//! This is a Rust implementation of [timespec](https://github.com/fenhl/timespec), a mini-language for specifying dates and times, intended to be used in command-line tools.
//!
//! For documentation of the timespec syntax, see [the timespec repository](https://github.com/fenhl/timespec).
//!
//! This crate implements timespec directions and predicates as iterator adaptors.

#![deny(missing_docs, rust_2018_idioms, unused, unused_import_braces, unused_lifetimes, unused_qualifications, warnings)]
#![forbid(unsafe_code)]

use {
    std::{
        cmp::Ordering::*,
        collections::HashMap,
        fmt,
        str::FromStr,
    },
    chrono::{
        LocalResult,
        Months,
        TimeDelta,
        prelude::*,
    },
    chrono_tz::{
        Etc,
        Tz,
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
pub enum CountSeconds<Z: TimeZone> {
    /// Start with the start datetime and continue into the future.
    Chronological(DateTime<Z>),
    /// Start with the start datetime and continue into the past.
    Reverse(DateTime<Z>),
}

impl<Z: TimeZone> Iterator for CountSeconds<Z> {
    type Item = DateTime<Z>;

    fn next(&mut self) -> Option<DateTime<Z>> {
        let (result, next_state) = match *self {
            CountSeconds::Chronological(ref start_date) => (start_date.clone(), CountSeconds::Chronological(start_date.clone() + TimeDelta::try_seconds(1).unwrap())),
            CountSeconds::Reverse(ref start_date) => (start_date.clone(), CountSeconds::Reverse(start_date.clone() - TimeDelta::try_seconds(1).unwrap())),
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
            Unit::Seconds => TimeDelta::try_seconds(1).unwrap(),
            Unit::Minutes => TimeDelta::try_minutes(1).unwrap(),
            Unit::Hours => TimeDelta::try_hours(1).unwrap(),
            Unit::Days => TimeDelta::try_days(1).unwrap(),
        }
    }
}

/// This trait can be implemented to parse custom predicates.
pub trait Plugin {
    /// Will be called at parse time with the custom predicate (plugin prefix removed) and the start time of the iteration.
    fn parse(&self, plugins: &HashMap<String, Box<dyn Plugin>>, zone: Tz, start: DateTime<Utc>, param_str: &str) -> Result<Predicate, Error>;
}

/// A `Plugin` must parse to this type.
pub enum Predicate {
    /// Use this to implement a predicate that can't be represented using the other variants. Note that the datetime to check will be converted to UTC before being passed. This is a limitation of the current API.
    Custom(Box<dyn Fn(DateTime<Utc>) -> bool>),
    /// Matches any datetime whose date matches the given year, month, and day. Omitted values are ignored, e.g. `Predicate::Date(Some(2012), None, None)` matches any datetime in 2012.
    Date(Tz, Option<i32>, Option<u8>, Option<u8>),
    /// Matches any datetime which is equal to the given datetime, ignoring subsecond nanoseconds on both datetimes.
    ExactSecond(DateTime<Utc>),
    /// Matches any datetime where the remainder of the given unit divided by the given number is zero.
    Modulus(Tz, u8, Unit),
    /// Matches any datetime whose time matches the given hour, minute, and second. Omitted values are ignored, e.g. `Predicate::Time(None, Some(0), Some(0))` matches any datetime on the hour.
    Time(Tz, Option<u8>, Option<u8>, Option<u8>),
    /// Matches any datetime on the given weekday.
    Weekday(Tz, Weekday),
    /// Matches any datetime where the last two digits of the year match the given number.
    YearMod(Tz, u8),
}

impl Predicate {
    fn from_str_without_plugins(zone: Tz, s: &str) -> Result<Self, Error> {
        if let Some((_, plugin)) = regex_captures!("^([a-z]+):.*$", s) {
            // must be caught by caller
            return Err(Error::NoSuchPlugin(plugin.to_owned()))
        }
        if let Ok(weekday) = s.parse() {
            return Ok(Self::Weekday(zone, weekday))
        }
        if let Some((_, interval, unit)) = regex_captures!("^([0-9]{1,2})([smhd])$", s) {
            return Ok(Predicate::Modulus(zone, interval.parse()?, unit.parse()?))
        }
        if let Some((_, year, month, day)) = regex_captures!("^([0-9]{1,9})?-([0-9]{1,9})?(?:-([0-9]{1,9})?)$", s) {
            return Ok(Predicate::Date(
                zone,
                (!year.is_empty()).then(|| year.parse()).transpose()?,
                (!month.is_empty()).then(|| month.parse()).transpose()?,
                (!day.is_empty()).then(|| day.parse()).transpose()?,
            ))
        }
        if let Some((_, hour, minute, second)) = regex_captures!("^([0-9]{1,9})?:([0-9]{1,9})?(?:(?::([0-9]{1,9})?)?)$", s) {
            return Ok(Predicate::Time(
                zone,
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
            return Ok(Predicate::Date(zone, Some(s.parse()?), None, None))
        }
        if regex_is_match!("^[0-9]{1,2}$", s) {
            // year mod 100
            return Ok(Predicate::YearMod(zone, s.parse()?))
        }
        Err(Error::UnknownPredicate(s.into()))
    }

    fn from_str_with_plugins<Z: TimeZone>(plugins: &HashMap<String, Box<dyn Plugin>>, zone: Tz, start: &DateTime<Z>, s: &str) -> Result<Self, Error> {
        match Self::from_str_without_plugins(zone, s) {
            Err(Error::NoSuchPlugin(plugin_name)) => {
                if let Some(plugin) = plugins.get(&plugin_name) {
                    plugin.parse(plugins, zone, start.with_timezone(&Utc), &s[plugin_name.len() + 1..])
                } else {
                    Err(Error::NoSuchPlugin(plugin_name))
                }
            }
            r => r,
        }
    }

    /// Returns the first datetime that matches `self` and is not before the given `date_time`.
    fn next_match(&self, date_time: DateTime<Utc>) -> Option<DateTime<Utc>> {
        match self {
            Predicate::Custom(f) => CountSeconds::Chronological(date_time).filter(|&candidate| f(candidate)).next(),
            Predicate::Date(zone, year, month, day) => {
                let date_time = date_time.with_timezone(zone);
                let mut candidate = date_time.date_naive();
                Some(loop {
                    let mut all_match = true;
                    if let Some(year) = *year {
                        match candidate.year().cmp(&year) {
                            Less => {
                                candidate = NaiveDate::from_ymd_opt(year, 1, 1)?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => return None,
                        }
                    }
                    if let Some(month) = *month {
                        match candidate.month().cmp(&month.into()) {
                            Less => {
                                candidate = NaiveDate::from_ymd_opt(candidate.year(), month.into(), 1)?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = NaiveDate::from_ymd_opt(candidate.year().checked_add(1)?, month.into(), 1)?;
                                all_match = false;
                            }
                        }
                    }
                    if let Some(day) = *day {
                        match candidate.day().cmp(&day.into()) {
                            Less => {
                                candidate = NaiveDate::from_ymd_opt(candidate.year(), candidate.month(), day.into())
                                    .or_else(|| NaiveDate::from_ymd_opt(candidate.year(), candidate.month().checked_add(1)?, day.into()))?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = NaiveDate::from_ymd_opt(candidate.year(), candidate.month(), day.into())?.checked_add_months(Months::new(1))?;
                                all_match = false;
                            }
                        }
                    }
                    if all_match {
                        if candidate == date_time.date_naive() {
                            break date_time.with_timezone(&Utc)
                        } else if let LocalResult::Single(date_time) = candidate.and_hms_opt(0, 0, 0)?.and_local_timezone(*zone) {
                            break date_time.with_timezone(&Utc)
                        }
                    }
                })
            }
            Predicate::ExactSecond(stamp) => {
                let stamp = stamp.with_nanosecond(0)?;
                match date_time.with_nanosecond(0)?.cmp(&stamp) {
                    Less => Some(stamp), // return start of the second
                    Equal => Some(date_time), // return original subsecond time
                    Greater => None,
                }
            }
            Predicate::Modulus(zone, interval, Unit::Seconds) => {
                let date_time = date_time.with_timezone(zone);
                if date_time.second() as u8 % interval == 0 {
                    Some(date_time.with_timezone(&Utc))
                } else {
                    (date_time.second() as u8 - date_time.second() as u8 % interval).checked_add(*interval)
                        .and_then(|next_second| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), date_time.day(), date_time.hour(), date_time.minute(), next_second.into()).single())
                        .or_else(|| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), date_time.day(), date_time.hour(), date_time.minute(), 0).single()?.checked_add_signed(TimeDelta::try_minutes(1)?))
                }
            }
            Predicate::Modulus(zone, interval, Unit::Minutes) => {
                let date_time = date_time.with_timezone(zone);
                if date_time.minute() as u8 % interval == 0 {
                    Some(date_time.with_timezone(&Utc))
                } else {
                    (date_time.minute() as u8 - date_time.minute() as u8 % interval).checked_add(*interval)
                        .and_then(|next_minute| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), date_time.day(), date_time.hour(), next_minute.into(), 0).single())
                        .or_else(|| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), date_time.day(), date_time.hour(), 0, 0).single()?.checked_add_signed(TimeDelta::try_hours(1)?))
                }
            }
            Predicate::Modulus(zone, interval, Unit::Hours) => {
                let date_time = date_time.with_timezone(zone);
                if date_time.hour() as u8 % interval == 0 {
                    Some(date_time.with_timezone(&Utc))
                } else {
                    (date_time.hour() as u8 - date_time.hour() as u8 % interval).checked_add(*interval)
                        .and_then(|next_hour| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), date_time.day(), next_hour.into(), 0, 0).single())
                        .or_else(|| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), date_time.day(), 0, 0, 0).single()?.checked_add_signed(TimeDelta::try_days(1)?))
                }
            }
            Predicate::Modulus(zone, interval, Unit::Days) => {
                let date_time = date_time.with_timezone(zone);
                if date_time.day() as u8 % interval == 0 {
                    Some(date_time.with_timezone(&Utc))
                } else {
                    (date_time.day() as u8 - date_time.day() as u8 % interval).checked_add(*interval)
                        .and_then(|next_day| Utc.with_ymd_and_hms(date_time.year(), date_time.month(), next_day.into(), 0, 0, 0).single())
                        .or_else(|| Some(NaiveDate::from_ymd_opt(date_time.year(), date_time.month(), (*interval).into())?.checked_add_months(Months::new(1))?.and_hms_opt(0, 0, 0)?.and_utc()))
                }
            }
            Predicate::Time(zone, hour, minute, second) => {
                let mut candidate = date_time.with_timezone(zone);
                loop {
                    let mut all_match = true;
                    if let Some(hour) = *hour {
                        match candidate.hour().cmp(&hour.into()) {
                            Less => {
                                candidate = zone.with_ymd_and_hms(candidate.year(), candidate.month(), candidate.day(), hour.into(), 0, 0).single()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = NaiveDate::from_ymd_opt(candidate.year(), candidate.month(), candidate.day())?.succ_opt()?.and_hms_opt(hour.into(), 0, 0)?.and_local_timezone(*zone).single()?;
                                all_match = false;
                            }
                        }
                    }
                    if let Some(minute) = *minute {
                        match candidate.minute().cmp(&minute.into()) {
                            Less => {
                                candidate = zone.with_ymd_and_hms(candidate.year(), candidate.month(), candidate.day(), candidate.hour(), minute.into(), 0).single()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = zone.with_ymd_and_hms(candidate.year(), candidate.month(), candidate.day(), candidate.hour(), minute.into(), 0).single()?.checked_add_signed(TimeDelta::try_hours(1)?)?;
                                all_match = false;
                            }
                        }
                    }
                    if let Some(second) = *second {
                        match candidate.second().cmp(&second.into()) {
                            Less => {
                                candidate = zone.with_ymd_and_hms(candidate.year(), candidate.month(), candidate.day(), candidate.hour(), candidate.minute(), second.into()).single()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = zone.with_ymd_and_hms(candidate.year(), candidate.month(), candidate.day(), candidate.hour(), candidate.minute(), second.into()).single()?.checked_add_signed(TimeDelta::try_minutes(1)?)?;
                                all_match = false;
                            }
                        }
                    }
                    if all_match { break }
                }
                Some(candidate.with_timezone(&Utc))
            }
            Predicate::Weekday(zone, weekday) => {
                let date_time = date_time.with_timezone(zone);
                Some(if date_time.weekday() == *weekday {
                    date_time.with_timezone(&Utc)
                } else {
                    let mut date = date_time.date_naive().succ_opt()?;
                    while date.weekday() != *weekday {
                        date = date.succ_opt()?;
                    }
                    date.and_hms_opt(0, 0, 0)?.and_utc()
                })
            }
            Predicate::YearMod(zone, year_mod) => {
                let date_time = date_time.with_timezone(zone);
                Some(if (date_time.year() % 100) as u8 == *year_mod {
                    date_time.with_timezone(&Utc)
                } else {
                    let mut year = date_time.year() - date_time.year() % 100 + i32::from(*year_mod);
                    if year < date_time.year() { year += 100 }
                    NaiveDate::from_ymd_opt(year, 1, 1)?.and_hms_opt(0, 0, 0)?.and_utc()
                })
            }
        }
    }

    fn matches<Z: TimeZone>(&self, date_time: DateTime<Z>) -> bool {
        match self {
            Predicate::Custom(f) => f(date_time.with_timezone(&Utc)),
            Predicate::Date(zone, year, month, day) => {
                let date_time = date_time.with_timezone(zone);
                year.map_or(true, |year| date_time.year() == year)
                && month.map_or(true, |month| date_time.month() as u8 == month)
                && day.map_or(true, |day| date_time.day() as u8 == day)
            }
            Predicate::ExactSecond(stamp) => date_time.with_timezone(&Utc).with_nanosecond(0) == stamp.with_nanosecond(0),
            Predicate::Modulus(zone, interval, Unit::Seconds) => date_time.with_timezone(zone).second() as u8 % interval == 0,
            Predicate::Modulus(zone, interval, Unit::Minutes) => date_time.with_timezone(zone).minute() as u8 % interval == 0,
            Predicate::Modulus(zone, interval, Unit::Hours) => date_time.with_timezone(zone).hour() as u8 % interval == 0,
            Predicate::Modulus(zone, interval, Unit::Days) => date_time.with_timezone(zone).day() as u8 % interval == 0,
            Predicate::Time(zone, hour, minute, second) => {
                let date_time = date_time.with_timezone(zone);
                hour.map_or(true, |hour| date_time.hour() as u8 == hour)
                && minute.map_or(true, |minute| date_time.minute() as u8 == minute)
                && second.map_or(true, |second| date_time.second() as u8 == second)
            }
            Predicate::Weekday(zone, weekday) => date_time.with_timezone(zone).weekday() == *weekday,
            Predicate::YearMod(zone, year_mod) => (date_time.with_timezone(zone).year() % 100) as u8 == *year_mod,
        }
    }
}

impl fmt::Debug for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Predicate::Custom(_) => write!(f, "Predicate::Custom(_)"),
            Predicate::Date(zone, year, month, day) => f.debug_tuple("Predicate::Date")
                .field(zone)
                .field(year)
                .field(month)
                .field(day)
                .finish(),
            Predicate::ExactSecond(stamp) => f.debug_tuple("Predicate::ExactSecond").field(stamp).finish(),
            Predicate::Modulus(zone, interval, unit) => f.debug_tuple("Predicate::Modulus")
                .field(zone)
                .field(interval)
                .field(unit)
                .finish(),
            Predicate::Time(zone, hour, minute, second) => f.debug_tuple("Predicate::Time")
                .field(zone)
                .field(hour)
                .field(minute)
                .field(second)
                .finish(),
            Predicate::Weekday(zone, weekday) => f.debug_tuple("Predicate::Weekday").field(zone).field(weekday).finish(),
            Predicate::YearMod(zone, year_mod) => f.debug_tuple("Predicate::YearMod").field(zone).field(year_mod).finish(),
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
    pub fn parse<Z: TimeZone, S: ToString, I: IntoIterator<Item = S>>(start: &DateTime<Z>, predicates: I) -> Result<TimeSpec, Error> {
        TimeSpec::parse_with_plugins(default_plugins(), start, predicates)
    }

    /// Parses a list of predicates into a timespec using the given plugins.
    ///
    /// If the built-in plugins are not included in `plugins`, they are disabled.
    pub fn parse_with_plugins<Z: TimeZone, S: ToString, I: IntoIterator<Item = S>>(plugins: HashMap<String, Box<dyn Plugin>>, start: &DateTime<Z>, predicates: I) -> Result<TimeSpec, Error> {
        let mut parsed_predicates = Vec::default();
        for predicate in predicates {
            parsed_predicates.push(Predicate::from_str_with_plugins(&plugins, Etc::UTC, start, &predicate.to_string())?);
        }
        Ok(TimeSpec { predicates: parsed_predicates })
    }

    /// Returns the earliest UTC date matching this timespec that's not earlier than the current system time.
    pub fn next(&self) -> Option<DateTime<Utc>> {
        self.next_after(&Utc::now())
    }

    /// Returns the earliest UTC date matching this timespec that's not earlier than the given reference time.
    pub fn next_after<Z: TimeZone>(&self, start: &DateTime<Z>) -> Option<DateTime<Z>> {
        let mut candidate = start.to_utc();
        loop {
            let mut all_match = true;
            for predicate in &self.predicates {
                let next_match = predicate.next_match(candidate)?;
                if next_match != candidate {
                    candidate = next_match;
                    all_match = false;
                }
            }
            if all_match { break }
        }
        Some(candidate.with_timezone(&start.timezone()))
    }

    /// Filters the iterable `search_space` by discarding all datetimes that don't match this timespec.
    pub fn filter<Z: TimeZone, I: IntoIterator<Item = DateTime<Z>>>(self, search_space: I) -> TimeSpecFilter<Z, I::IntoIter> {
        TimeSpecFilter {
            inner: search_space.into_iter(),
            spec: self,
        }
    }

    /// Checks whether the given datetime matches this timespec.
    pub fn matches<Z: TimeZone>(&self, date_time: DateTime<Z>) -> bool {
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
pub struct TimeSpecFilter<Z: TimeZone, I: Iterator<Item = DateTime<Z>>> {
    inner: I,
    spec: TimeSpec,
}

impl<Z: TimeZone, I: Iterator<Item = DateTime<Z>>> Iterator for TimeSpecFilter<Z, I> {
    type Item = DateTime<Z>;

    fn next(&mut self) -> Option<DateTime<Z>> {
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
    ret.insert("z".into(), Box::new(plugins::WithTimeZone) as Box<dyn Plugin>);
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
    Ok(TimeSpec::parse(&Utc::now(), predicates)?.next())
}

/// This function is provided as a shortcut to get the next datetime from a set of predicates, starting with a given date and continuing into the future.
///
/// # Returns
///
/// * `Ok(Some(date_time))` if a date was found
/// * `Ok(None)` if the predicates parse to a valid timespec but no date was found
/// * `Err(...)` if the predicates are not valid timespec syntax
pub fn next_after<Z: TimeZone, S: ToString, I: IntoIterator<Item = S>>(start: &DateTime<Z>, predicates: I) -> Result<Option<DateTime<Z>>, Error> {
    Ok(TimeSpec::parse(start, predicates)?.next_after(start))
}
