//! This is a Rust implementation of [timespec](https://github.com/fenhl/timespec), a mini-language for specifying dates and times, intended to be used in command-line tools.
//!
//! For documentation of the timespec syntax, see [the timespec repository](https://github.com/fenhl/timespec).
//!
//! This crate implements timespec directions and predicates as iterator adaptors.

#![deny(missing_docs, rust_2018_idioms, unused, unused_import_braces, unused_lifetimes, unused_qualifications, warnings)]
#![forbid(unsafe_code)]

use {
    std::{
        collections::HashMap,
        fmt,
        str::FromStr,
    },
    chrono::{
        TimeDelta,
        prelude::*,
    },
    lazy_regex::{
        regex_captures,
        regex_is_match,
    },
};

mod plugins;

/// An error that occurred while parsing a timespec predicate.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A predicate tried to use a timespec plugin which has not been defined. The plugin name is included in the error data.
    #[error("no timespec plugin named “{0}” has been defined")]
    NoSuchPlugin(String),
    /// An error occurred while parsing a number.
    #[error(transparent)] ParseInt(#[from] std::num::ParseIntError),
    /// An error occurred in a plugin.
    #[error("error in timespec plugin: {0}")]
    Plugin(String),
    /// A POSIX timestamp predicate was out of the range of timestamps supported by this implementation.
    #[error("POSIX timestamp out of range")]
    Timestamp,
    /// While parsing a modulus or relative-plugin predicate, an unknown unit letter was encountered.
    #[error("unknown time unit: {0}")]
    Unit(String),
    /// The following predicate could not be parsed.
    #[error("unknown timespec predicate: {0:?}")]
    UnknownPredicate(String),
}

/// An iterator yielding datetimes for every second from the given start time.
#[derive(Debug, Clone)]
pub enum CountSeconds<Tz: TimeZone> {
    /// Start with the start datetime and continue into the future.
    Chronological(DateTime<Tz>),
    /// Start with the start datetime and continue into the past.
    Reverse(DateTime<Tz>),
}

impl<Tz: TimeZone> Iterator for CountSeconds<Tz> {
    type Item = DateTime<Tz>;

    fn next(&mut self) -> Option<DateTime<Tz>> {
        let (result, next_state) = match *self {
            CountSeconds::Chronological(ref start_date) => (start_date.clone(), CountSeconds::Chronological(start_date.clone() + TimeDelta::seconds(1))),
            CountSeconds::Reverse(ref start_date) => (start_date.clone(), CountSeconds::Reverse(start_date.clone() - TimeDelta::seconds(1))),
        };
        *self = next_state;
        Some(result)
    }
}

/// Units used for modulus predicates and in the `r` plugin.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Unit {
    /// Seconds of the minute.
    Seconds,
    /// Minutes of the hour.
    Minutes,
    /// Hours of the day, from 0 to 23.
    Hours,
    /// Days of the month, starting with 1.
    Days,
}

impl FromStr for Unit {
    type Err = Error;

    fn from_str(s: &str) -> Result<Unit, Error> {
        match s {
            "s" => Ok(Unit::Seconds),
            "m" => Ok(Unit::Minutes),
            "h" => Ok(Unit::Hours),
            "d" => Ok(Unit::Days),
            _ => Err(Error::Unit(s.into())),
        }
    }
}

impl From<Unit> for TimeDelta {
    fn from(unit: Unit) -> TimeDelta {
        match unit {
            Unit::Seconds => TimeDelta::seconds(1),
            Unit::Minutes => TimeDelta::minutes(1),
            Unit::Hours => TimeDelta::hours(1),
            Unit::Days => TimeDelta::days(1),
        }
    }
}

/// This trait can be implemented to parse custom predicates.
pub trait Plugin {
    /// Will be called at parse time with the custom predicate (plugin prefix removed) and the start time of the iteration.
    fn parse(&self, param_str: &str, start: DateTime<Utc>) -> Result<Predicate, Error>;
}

/// A `Plugin` must parse to this type.
pub enum Predicate {
    /// Use this to implement a predicate that can't be represented using the other variants. Note that the datetime to check will be converted to UTC before being passed. This is a limitation of the current API.
    Custom(Box<dyn Fn(DateTime<Utc>) -> bool>),
    /// Matches any datetime whose date matches the given year, month, and day. Omitted values are ignored, e.g. `Predicate::Date(Some(2012), None, None)` matches any datetime in 2012.
    Date(Option<i32>, Option<u8>, Option<u8>),
    /// Matches any datetime which is equal to the given datetime, ignoring subsecond nanoseconds on both datetimes.
    ExactSecond(DateTime<Utc>),
    /// Matches any datetime where the remainder of the given unit divided by the given number is zero.
    Modulus(u8, Unit),
    /// Matches any datetime whose time matches the given hour, minute, and second. Omitted values are ignored, e.g. `Predicate::Time(None, Some(0), Some(0))` matches any datetime on the hour.
    Time(Option<u8>, Option<u8>, Option<u8>),
    /// Matches any datetime on the given weekday.
    Weekday(Weekday),
    /// Matches any datetime where the last two digits of the year match the given number.
    YearMod(u8),
}

impl Predicate {
    fn from_str_with_plugins<Tz: TimeZone>(plugins: &HashMap<String, Box<dyn Plugin>>, start: &DateTime<Tz>, s: &str) -> Result<Predicate, Error> {
        match Predicate::from_str(s) {
            Err(Error::NoSuchPlugin(plugin_name)) => {
                if let Some(plugin) = plugins.get(&plugin_name) {
                    plugin.parse(&s[plugin_name.len() + 1..], start.with_timezone(&Utc))
                } else {
                    Err(Error::NoSuchPlugin(plugin_name))
                }
            }
            r => r,
        }
    }

    fn matches<Tz: TimeZone>(&self, date_time: DateTime<Tz>) -> bool {
        match self {
            Predicate::Custom(f) => f(date_time.with_timezone(&Utc)),
            Predicate::Date(year, month, day) => {
                year.map_or(true, |year| date_time.year() == year)
                && month.map_or(true, |month| date_time.month() as u8 == month)
                && day.map_or(true, |day| date_time.day() as u8 == day)
            }
            Predicate::ExactSecond(stamp) => date_time.with_timezone(&Utc).with_nanosecond(0) == stamp.with_nanosecond(0),
            Predicate::Modulus(interval, Unit::Seconds) => date_time.second() as u8 % interval == 0,
            Predicate::Modulus(interval, Unit::Minutes) => date_time.minute() as u8 % interval == 0,
            Predicate::Modulus(interval, Unit::Hours) => date_time.hour() as u8 % interval == 0,
            Predicate::Modulus(interval, Unit::Days) => date_time.day() as u8 % interval == 0,
            Predicate::Time(hour, minute, second) => {
                hour.map_or(true, |hour| date_time.hour() as u8 == hour)
                && minute.map_or(true, |minute| date_time.minute() as u8 == minute)
                && second.map_or(true, |second| date_time.second() as u8 == second)
            }
            Predicate::Weekday(weekday) => date_time.weekday() == *weekday,
            Predicate::YearMod(year_mod) => (date_time.year() % 100) as u8 == *year_mod,
        }
    }
}

impl FromStr for Predicate {
    type Err = Error;

    fn from_str(s: &str) -> Result<Predicate, Error> {
        if let Some((_, plugin)) = regex_captures!("^([a-z]+):.*$", s) {
            // must be caught by caller
            return Err(Error::NoSuchPlugin(plugin.to_owned()))
        }
        if let Ok(weekday) = s.parse() {
            return Ok(Predicate::Weekday(weekday))
        }
        if let Some((_, interval, unit)) = regex_captures!("^([0-9]{1,2})([smhd])$", s) {
            return Ok(Predicate::Modulus(interval.parse()?, unit.parse()?))
        }
        if let Some((_, year, month, day)) = regex_captures!("^([0-9]{1,9})?-([0-9]{1,9})?(?:-([0-9]{1,9})?)$", s) {
            return Ok(Predicate::Date(
                (!year.is_empty()).then(|| year.parse()).transpose()?,
                (!month.is_empty()).then(|| month.parse()).transpose()?,
                (!day.is_empty()).then(|| day.parse()).transpose()?,
            ))
        }
        if let Some((_, hour, minute, second)) = regex_captures!("^([0-9]{1,9})?:([0-9]{1,9})?(?:(?::([0-9]{1,9})?)?)$", s) {
            return Ok(Predicate::Time(
                (!hour.is_empty()).then(|| hour.parse()).transpose()?,
                (!minute.is_empty()).then(|| minute.parse()).transpose()?,
                (!second.is_empty()).then(|| second.parse()).transpose()?,
            ))
        }
        if regex_is_match!("^[0-9]{10,}$", s) {
            // exact POSIX timestamp
            return Ok(Predicate::ExactSecond(Utc.timestamp_opt(s.parse()?, 0).single().ok_or(Error::Timestamp)?))
        }
        if regex_is_match!("^[0-9]{4,9}$", s) {
            // absolute year
            return Ok(Predicate::Date(Some(s.parse()?), None, None))
        }
        if regex_is_match!("^[0-9]{1,2}$", s) {
            // year mod 100
            return Ok(Predicate::YearMod(s.parse()?))
        }
        Err(Error::UnknownPredicate(s.into()))
    }
}

impl fmt::Debug for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Predicate::Custom(_) => write!(f, "Predicate::Custom(_)"),
            Predicate::Date(year, month, day) => f.debug_tuple("Predicate::Date")
                .field(year)
                .field(month)
                .field(day)
                .finish(),
            Predicate::ExactSecond(stamp) => f.debug_tuple("Predicate::ExactSecond").field(stamp).finish(),
            Predicate::Modulus(interval, unit) => f.debug_tuple("Predicate::Modulus")
                .field(interval)
                .field(unit)
                .finish(),
            Predicate::Time(hour, minute, second) => f.debug_tuple("Predicate::Time")
                .field(hour)
                .field(minute)
                .field(second)
                .finish(),
            Predicate::Weekday(weekday) => f.debug_tuple("Predicate::Weekday").field(weekday).finish(),
            Predicate::YearMod(year_mod) => f.debug_tuple("Predicate::YearMod").field(year_mod).finish(),
        }
    }
}

/// This type represents a parsed timespec.
#[derive(Debug)]
pub struct TimeSpec {
    predicates: Vec<Predicate>,
}

impl TimeSpec {
    /// Parses a list of predicates into a timespec.
    ///
    /// This uses only the built-in plugins. To use your own plugins, use `parse_with_plugins`.
    pub fn parse<Tz: TimeZone, S: ToString, I: IntoIterator<Item = S>>(start: &DateTime<Tz>, predicates: I) -> Result<TimeSpec, Error> {
        TimeSpec::parse_with_plugins(default_plugins(), start, predicates)
    }

    /// Parses a list of predicates into a timespec using the given plugins.
    ///
    /// If the built-in plugins are not included in `plugins`, they are disabled.
    pub fn parse_with_plugins<Tz: TimeZone, S: ToString, I: IntoIterator<Item = S>>(plugins: HashMap<String, Box<dyn Plugin>>, start: &DateTime<Tz>, predicates: I) -> Result<TimeSpec, Error> {
        let mut parsed_predicates = Vec::default();
        for predicate in predicates {
            parsed_predicates.push(Predicate::from_str_with_plugins(&plugins, start, &predicate.to_string())?);
        }
        Ok(TimeSpec { predicates: parsed_predicates })
    }

    /// Filters the iterable `search_space` by discarding all datetimes that don't match this timespec.
    pub fn filter<Tz: TimeZone, I: IntoIterator<Item = DateTime<Tz>>>(self, search_space: I) -> TimeSpecFilter<Tz, I::IntoIter> {
        TimeSpecFilter {
            inner: search_space.into_iter(),
            spec: self,
        }
    }

    /// Checks whether the given datetime matches this timespec.
    pub fn matches<Tz: TimeZone>(&self, date_time: DateTime<Tz>) -> bool {
        self.predicates.iter().all(|pred| pred.matches(date_time.clone()))
    }
}

impl IntoIterator for TimeSpec {
    type IntoIter = TimeSpecFilter<Utc, CountSeconds<Utc>>;
    type Item = DateTime<Utc>;

    fn into_iter(self) -> Self::IntoIter {
        TimeSpecFilter {
            inner: CountSeconds::Chronological(Utc::now()),
            spec: self,
        }
    }
}

/// An iterator that filters the elements of an inner iterator with a timespec. Created using `TimeSpec::filter`.
pub struct TimeSpecFilter<Tz: TimeZone, I: Iterator<Item = DateTime<Tz>>> {
    inner: I,
    spec: TimeSpec,
}

impl<Tz: TimeZone, I: Iterator<Item = DateTime<Tz>>> Iterator for TimeSpecFilter<Tz, I> {
    type Item = DateTime<Tz>;

    fn next(&mut self) -> Option<DateTime<Tz>> {
        for x in &mut self.inner {
            if self.spec.matches(x.clone()) {
                return Some(x)
            }
        }
        None
    }
}

/// Returns the default set of plugins, currently only including `r`.
pub fn default_plugins() -> HashMap<String, Box<dyn Plugin>> {
    let mut ret = HashMap::default();
    ret.insert("r".into(), Box::new(plugins::Relative) as Box<dyn Plugin>);
    ret
}

/// This function is provided as a shortcut to get the next datetime from a set of predicates, starting with the current system time in UTC and continuing into the future.
///
/// # Returns
///
/// * `Ok(Some(date_time))` if a date was found
/// * `Ok(None)` if the predicates parse to a valid timespec but no date was found
/// * `Err(...)` if the predicates are not valid timespec syntax
pub fn next<S: ToString, I: IntoIterator<Item = S>>(predicates: I) -> Result<Option<DateTime<Utc>>, Error> {
    Ok(TimeSpec::parse(&Utc::now(), predicates)?.filter(CountSeconds::Chronological(Utc::now().with_nanosecond(0).expect("could not truncate subsecond portion of now"))).next())
}
