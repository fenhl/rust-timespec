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
        time::Duration,
    },
    jiff::{
        SignedDuration,
        Span,
        Timestamp,
        civil,
        tz::TimeZone,
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
    /// An error occurred while constructing/parsing/formatting a date/time/timezone.
    #[error(transparent)] Jiff(#[from] jiff::Error),
    /// A predicate tried to use a timespec plugin which has not been defined. The plugin name is included in the error data.
    #[error("no timespec plugin named “{0}” has been defined")]
    NoSuchPlugin(String),
    /// An error occurred while parsing a number.
    #[error(transparent)] ParseInt(#[from] std::num::ParseIntError),
    /// An error occurred in a plugin.
    #[error("error in timespec plugin: {0}")]
    Plugin(String),
    /// While parsing a modulus or relative-plugin predicate, an unknown unit letter was encountered.
    #[error("unknown time unit: {0}")]
    Unit(String),
    /// The following predicate could not be parsed.
    #[error("unknown timespec predicate: {0:?}")]
    UnknownPredicate(String),
}

/// An iterator yielding datetimes for every second from the given start time.
#[derive(Debug, Clone)]
pub enum CountSeconds {
    /// Start with the start datetime and continue into the future.
    Chronological(Timestamp),
    /// Start with the start datetime and continue into the past.
    Reverse(Timestamp),
}

impl Iterator for CountSeconds {
    type Item = Timestamp;

    fn next(&mut self) -> Option<Timestamp> {
        let (result, next_state) = match *self {
            CountSeconds::Chronological(ref start_date) => (start_date.clone(), CountSeconds::Chronological(start_date.clone() + Duration::from_secs(1))),
            CountSeconds::Reverse(ref start_date) => (start_date.clone(), CountSeconds::Reverse(start_date.clone() - Duration::from_secs(1))),
        };
        *self = next_state;
        Some(result)
    }
}

/// Units used for modulus predicates.
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

    fn from_str(s: &str) -> Result<Self, Error> {
        match s {
            "s" => Ok(Self::Seconds),
            "m" => Ok(Self::Minutes),
            "h" => Ok(Self::Hours),
            "d" => Ok(Self::Days),
            _ => Err(Error::Unit(s.into())),
        }
    }
}

impl From<Unit> for SignedDuration {
    fn from(unit: Unit) -> Self {
        match unit {
            Unit::Seconds => Self::from_secs(1),
            Unit::Minutes => Self::from_mins(1),
            Unit::Hours => Self::from_hours(1),
            Unit::Days => Self::from_hours(24),
        }
    }
}

/// This trait can be implemented to parse custom predicates.
pub trait Plugin {
    /// Will be called at parse time with the custom predicate (plugin prefix removed) and the start time of the iteration.
    fn parse(&self, plugins: &HashMap<String, Box<dyn Plugin>>, zone: TimeZone, start: Timestamp, param_str: &str) -> Result<Predicate, Error>;
}

/// A `Plugin` must parse to this type.
pub enum Predicate {
    /// A list of predicates, all of which must match.
    All(Vec<Self>),
    /// Use this to implement a predicate that can't be represented using the other variants. Note that the datetime to check will be converted to UTC before being passed. This is a limitation of the current API.
    Custom(Box<dyn Fn(Timestamp) -> bool>),
    /// Matches any datetime whose date matches the given year, month, and day. Omitted values are ignored, e.g. `Predicate::Date(Some(2012), None, None)` matches any datetime in 2012.
    Date(TimeZone, Option<i16>, Option<i8>, Option<i8>),
    /// Matches any datetime which is equal to the given datetime, ignoring subsecond nanoseconds on both datetimes.
    ExactSecond(Timestamp),
    /// Matches any datetime where the remainder of the given unit divided by the given number is zero.
    Modulus(TimeZone, i8, Unit),
    /// Matches any datetime whose time matches the given hour, minute, and second. Omitted values are ignored, e.g. `Predicate::Time(None, Some(0), Some(0))` matches any datetime on the hour.
    Time(TimeZone, Option<i8>, Option<i8>, Option<i8>),
    /// Matches any datetime on the given weekday.
    Weekday(TimeZone, civil::Weekday),
    /// Matches any datetime where the last two digits of the year match the given number.
    YearMod(TimeZone, u8),
}

impl Predicate {
    fn from_str_without_plugins(zone: TimeZone, s: &str) -> Result<Self, Error> {
        if let Some((_, plugin)) = regex_captures!("^([a-z]+):.*$", s) {
            // must be caught by caller
            return Err(Error::NoSuchPlugin(plugin.to_owned()))
        }
        if s.eq_ignore_ascii_case("mon") || s.eq_ignore_ascii_case("monday") { return Ok(Self::Weekday(zone, civil::Weekday::Monday)) }
        if s.eq_ignore_ascii_case("tue") || s.eq_ignore_ascii_case("tueday") { return Ok(Self::Weekday(zone, civil::Weekday::Tuesday)) }
        if s.eq_ignore_ascii_case("wed") || s.eq_ignore_ascii_case("wednesday") { return Ok(Self::Weekday(zone, civil::Weekday::Wednesday)) }
        if s.eq_ignore_ascii_case("thu") || s.eq_ignore_ascii_case("thursday") { return Ok(Self::Weekday(zone, civil::Weekday::Thursday)) }
        if s.eq_ignore_ascii_case("fri") || s.eq_ignore_ascii_case("friday") { return Ok(Self::Weekday(zone, civil::Weekday::Friday)) }
        if s.eq_ignore_ascii_case("sat") || s.eq_ignore_ascii_case("saturday") { return Ok(Self::Weekday(zone, civil::Weekday::Saturday)) }
        if s.eq_ignore_ascii_case("sun") || s.eq_ignore_ascii_case("sunday") { return Ok(Self::Weekday(zone, civil::Weekday::Sunday)) }
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
            return Ok(Predicate::ExactSecond(Timestamp::from_second(s.parse()?)?))
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

    fn from_str_with_plugins(plugins: &HashMap<String, Box<dyn Plugin>>, zone: TimeZone, start: Timestamp, s: &str) -> Result<Self, Error> {
        match Self::from_str_without_plugins(zone.clone(), s) {
            Err(Error::NoSuchPlugin(plugin_name)) => {
                if let Some(plugin) = plugins.get(&plugin_name) {
                    plugin.parse(plugins, zone, start, &s[plugin_name.len() + 1..])
                } else {
                    Err(Error::NoSuchPlugin(plugin_name))
                }
            }
            r => r,
        }
    }

    /// Returns the first datetime that matches `self` and is not before the given `date_time`.
    fn next_match(&self, date_time: Timestamp) -> Option<Timestamp> {
        match self {
            Self::All(predicates) => {
                let mut candidate = date_time;
                loop {
                    let prev_candidate = candidate;
                    for predicate in predicates {
                        candidate = predicate.next_match(candidate)?;
                    }
                    if candidate == prev_candidate { break }
                }
                Some(candidate)
            }
            Self::Custom(f) => CountSeconds::Chronological(date_time).filter(|&candidate| f(candidate)).next(),
            Self::Date(zone, year, month, day) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                let mut candidate = date_time.date();
                Some(loop {
                    let mut all_match = true;
                    if let Some(year) = *year {
                        match candidate.year().cmp(&year) {
                            Less => {
                                candidate = civil::Date::new(year, 1, 1).ok()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => return None,
                        }
                    }
                    if let Some(month) = *month {
                        match candidate.month().cmp(&month) {
                            Less => {
                                candidate = civil::Date::new(candidate.year(), month, 1).ok()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = civil::Date::new(candidate.year().checked_add(1)?, month, 1).ok()?;
                                all_match = false;
                            }
                        }
                    }
                    if let Some(day) = *day {
                        match candidate.day().cmp(&day) {
                            Less => {
                                candidate = civil::Date::new(candidate.year(), candidate.month(), day).ok()
                                    .or_else(|| civil::Date::new(candidate.year(), candidate.month().checked_add(1)?, day).ok())?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = civil::Date::new(candidate.year(), candidate.month() % 12 + 1, day).or_else(|_| civil::Date::new(candidate.year(), (candidate.month() + 1) % 12 + 1, day)).ok()?;
                                all_match = false;
                            }
                        }
                    }
                    if all_match {
                        break if candidate == date_time.date() {
                            date_time
                        } else {
                            candidate.at(0, 0, 0, 0).to_zoned_datetime(zone.clone()).ok()?
                        }.timestamp()
                    }
                })
            }
            Predicate::ExactSecond(stamp) => {
                let stamp = Timestamp::from_second(stamp.as_second()).ok()?;
                match Timestamp::from_second(date_time.as_second()).ok()?.cmp(&stamp) {
                    Less => Some(stamp), // return start of the second
                    Equal => Some(date_time), // return original subsecond time
                    Greater => None,
                }
            }
            Predicate::Modulus(zone, interval, Unit::Seconds) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                if date_time.second() % *interval == 0 {
                    Some(date_time.timestamp())
                } else {
                    (date_time.second() - date_time.second() % interval).checked_add(*interval) //TODO(https://github.com/rust-lang/rust/issues/88581) date_time.second().checked_next_multiple_of(*interval)
                        .and_then(|next_second| date_time.with().second(next_second).subsec_nanosecond(0).build().ok())
                        .or_else(|| date_time.with().second(0).subsec_nanosecond(0).build().ok()?.checked_add(Span::new().minutes(1)).ok())
                        .map(|date_time| date_time.timestamp())
                }
            }
            Predicate::Modulus(zone, interval, Unit::Minutes) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                if date_time.minute() % interval == 0 {
                    Some(date_time.timestamp())
                } else {
                    (date_time.minute() - date_time.minute() % interval).checked_add(*interval) //TODO(https://github.com/rust-lang/rust/issues/88581) date_time.minute().checked_next_multiple_of(*interval)
                        .and_then(|next_minute| date_time.with().minute(next_minute).second(0).subsec_nanosecond(0).build().ok())
                        .or_else(|| date_time.with().minute(0).second(0).subsec_nanosecond(0).build().ok()?.checked_add(Span::new().hours(1)).ok())
                        .map(|date_time| date_time.timestamp())
                }
            }
            Predicate::Modulus(zone, interval, Unit::Hours) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                if date_time.hour() % interval == 0 {
                    Some(date_time.timestamp())
                } else {
                    (date_time.hour() - date_time.hour() % interval).checked_add(*interval) //TODO(https://github.com/rust-lang/rust/issues/88581) date_time.hour().checked_next_multiple_of(*interval)
                        .and_then(|next_hour| date_time.with().hour(next_hour).minute(0).second(0).subsec_nanosecond(0).build().ok())
                        .or_else(|| date_time.date().tomorrow().ok()?.at(0, 0, 0, 0).to_zoned_datetime(zone.clone()).ok())
                        .map(|date_time| date_time.timestamp())
                }
            }
            Predicate::Modulus(zone, interval, Unit::Days) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                if date_time.day() % interval == 0 {
                    Some(date_time.timestamp())
                } else {
                    (date_time.day() - date_time.day() % interval).checked_add(*interval) //TODO(https://github.com/rust-lang/rust/issues/88581) date_time.day().checked_next_multiple_of(*interval)
                        .and_then(|next_day| date_time.with().day(next_day).hour(0).minute(0).second(0).subsec_nanosecond(0).build().ok())
                        .or_else(|| date_time.date().last_of_month().tomorrow().ok()?.with().day(*interval).build().ok()?.at(0, 0, 0, 0).to_zoned_datetime(zone.clone()).ok())
                        .map(|date_time| date_time.timestamp())
                }
            }
            Predicate::Time(zone, hour, minute, second) => {
                let mut candidate = date_time.to_zoned_datetime(zone.clone());
                Some(loop {
                    let mut all_match = true;
                    if let Some(hour) = *hour {
                        match candidate.hour().cmp(&hour) {
                            Less => {
                                candidate = candidate.with().hour(hour).minute(0).second(0).subsec_nanosecond(0).build().ok()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = candidate.date().tomorrow().ok()?.at(hour, 0, 0, 0).to_zoned_datetime(zone.clone()).ok()?;
                                all_match = false;
                            }
                        }
                    }
                    if let Some(minute) = *minute {
                        match candidate.minute().cmp(&minute.into()) {
                            Less => {
                                candidate = candidate.with().minute(minute).second(0).subsec_nanosecond(0).build().ok()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = candidate.checked_add(Span::new().hours(1)).ok()?.with().minute(minute).second(0).subsec_nanosecond(0).build().ok()?;
                                all_match = false;
                            }
                        }
                    }
                    if let Some(second) = *second {
                        match candidate.second().cmp(&second.into()) {
                            Less => {
                                candidate = candidate.with().second(second).subsec_nanosecond(0).build().ok()?;
                                all_match = false;
                            }
                            Equal => {}
                            Greater => {
                                candidate = candidate.checked_add(Span::new().minutes(1)).ok()?.with().second(second).subsec_nanosecond(0).build().ok()?;
                                all_match = false;
                            }
                        }
                    }
                    if all_match {
                        break candidate.timestamp()
                    }
                })
            }
            Predicate::Weekday(zone, weekday) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                Some(if date_time.weekday() == *weekday {
                    date_time
                } else {
                    let mut date = date_time.date().tomorrow().ok()?;
                    while date.weekday() != *weekday {
                        date = date.tomorrow().ok()?;
                    }
                    date.at(0, 0, 0, 0).to_zoned_datetime(zone.clone()).ok()?
                }.timestamp())
            }
            Predicate::YearMod(zone, year_mod) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                Some(if (date_time.year() % 100) == (*year_mod).into() {
                    date_time
                } else {
                    let year = (date_time.year() - date_time.year() % 100).checked_add(100)?; //TODO(https://github.com/rust-lang/rust/issues/88581) date_time.year().next_multiple_of(100) + *year_mod
                    civil::date(year, 1, 1).at(0, 0, 0, 0).to_zoned_datetime(zone.clone()).ok()?
                }.timestamp())
            }
        }
    }

    fn matches(&self, date_time: impl Into<Timestamp>) -> bool {
        let date_time = date_time.into();
        match self {
            Self::All(predicates) => predicates.iter().all(|predicate| predicate.matches(date_time)),
            Self::Custom(f) => f(date_time),
            Predicate::Date(zone, year, month, day) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                year.is_none_or(|year| date_time.year() == year)
                && month.is_none_or(|month| date_time.month() == month)
                && day.is_none_or(|day| date_time.day() == day)
            }
            Predicate::ExactSecond(stamp) => date_time.as_second() == stamp.as_second(),
            Predicate::Modulus(zone, interval, Unit::Seconds) => date_time.to_zoned_datetime(zone.clone()).second() % interval == 0,
            Predicate::Modulus(zone, interval, Unit::Minutes) => date_time.to_zoned_datetime(zone.clone()).minute() % interval == 0,
            Predicate::Modulus(zone, interval, Unit::Hours) => date_time.to_zoned_datetime(zone.clone()).hour() % interval == 0,
            Predicate::Modulus(zone, interval, Unit::Days) => date_time.to_zoned_datetime(zone.clone()).day() % interval == 0,
            Predicate::Time(zone, hour, minute, second) => {
                let date_time = date_time.to_zoned_datetime(zone.clone());
                hour.is_none_or(|hour| date_time.hour() == hour)
                && minute.is_none_or(|minute| date_time.minute() == minute)
                && second.is_none_or(|second| date_time.second() == second)
            }
            Predicate::Weekday(zone, weekday) => date_time.to_zoned_datetime(zone.clone()).weekday() == *weekday,
            Predicate::YearMod(zone, year_mod) => date_time.to_zoned_datetime(zone.clone()).year() % 100 == (*year_mod).into(),
        }
    }
}

impl fmt::Debug for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::All(preds) => f.debug_tuple("Predicate::All")
                .field(preds)
                .finish(),
            Self::Custom(_) => write!(f, "Predicate::Custom(_)"),
            Self::Date(zone, year, month, day) => f.debug_tuple("Predicate::Date")
                .field(zone)
                .field(year)
                .field(month)
                .field(day)
                .finish(),
            Self::ExactSecond(stamp) => f.debug_tuple("Predicate::ExactSecond").field(stamp).finish(),
            Self::Modulus(zone, interval, unit) => f.debug_tuple("Predicate::Modulus")
                .field(zone)
                .field(interval)
                .field(unit)
                .finish(),
            Self::Time(zone, hour, minute, second) => f.debug_tuple("Predicate::Time")
                .field(zone)
                .field(hour)
                .field(minute)
                .field(second)
                .finish(),
            Self::Weekday(zone, weekday) => f.debug_tuple("Predicate::Weekday").field(zone).field(weekday).finish(),
            Self::YearMod(zone, year_mod) => f.debug_tuple("Predicate::YearMod").field(zone).field(year_mod).finish(),
        }
    }
}

/// This type represents a parsed timespec.
#[derive(Debug)]
pub struct TimeSpec {
    predicates: Vec<Predicate>,
}

impl TimeSpec {
    /// Parses a list of predicates into a timespec using the default plugins and UTC.
    ///
    /// This uses only the built-in plugins. To use your own plugins, use `parse_with_plugins`.
    pub fn parse<S: ToString, I: IntoIterator<Item = S>>(start: impl Into<Timestamp>, predicates: I) -> Result<TimeSpec, Error> {
        TimeSpec::parse_with_plugins_and_timezone(default_plugins(), TimeZone::UTC, start.into(), predicates)
    }

    /// Parses a list of predicates into a timespec using the default plugins and the given time zone.
    ///
    /// This uses only the built-in plugins. To use your own plugins, use `parse_with_plugins_and_timezone`.
    pub fn parse_with_timezone<S: ToString, I: IntoIterator<Item = S>>(timezone: TimeZone, start: impl Into<Timestamp>, predicates: I) -> Result<TimeSpec, Error> {
        TimeSpec::parse_with_plugins_and_timezone(default_plugins(), timezone, start.into(), predicates)
    }

    /// Parses a list of predicates into a timespec using the given plugins and UTC.
    ///
    /// If the built-in plugins are not included in `plugins`, they are disabled.
    pub fn parse_with_plugins<S: ToString, I: IntoIterator<Item = S>>(plugins: HashMap<String, Box<dyn Plugin>>, start: impl Into<Timestamp>, predicates: I) -> Result<TimeSpec, Error> {
        Self::parse_with_plugins_and_timezone(plugins, TimeZone::UTC, start.into(), predicates)
    }

    /// Parses a list of predicates into a timespec using the given plugins and time zone.
    ///
    /// If the built-in plugins are not included in `plugins`, they are disabled.
    pub fn parse_with_plugins_and_timezone<S: ToString, I: IntoIterator<Item = S>>(plugins: HashMap<String, Box<dyn Plugin>>, timezone: TimeZone, start: impl Into<Timestamp>, predicates: I) -> Result<TimeSpec, Error> {
        let start = start.into();
        let mut parsed_predicates = Vec::default();
        for predicate in predicates {
            parsed_predicates.push(Predicate::from_str_with_plugins(&plugins, timezone.clone(), start, &predicate.to_string())?);
        }
        Ok(TimeSpec { predicates: parsed_predicates })
    }

    /// Returns the earliest UTC date matching this timespec that's not earlier than the current system time.
    pub fn next(&self) -> Option<Timestamp> {
        self.next_after(Timestamp::now())
    }

    /// Returns the earliest UTC date matching this timespec that's not earlier than the given reference time.
    pub fn next_after(&self, start: impl Into<Timestamp>) -> Option<Timestamp> {
        let mut candidate = start.into();
        loop {
            let prev_candidate = candidate;
            for predicate in &self.predicates {
                candidate = predicate.next_match(candidate)?;
            }
            if candidate == prev_candidate { break }
        }
        Some(candidate)
    }

    /// Filters the iterable `search_space` by discarding all datetimes that don't match this timespec.
    pub fn filter<I: IntoIterator<Item = Timestamp>>(self, search_space: I) -> TimeSpecFilter<I::IntoIter> {
        TimeSpecFilter {
            inner: search_space.into_iter(),
            spec: self,
        }
    }

    /// Checks whether the given datetime matches this timespec.
    pub fn matches(&self, date_time: impl Into<Timestamp>) -> bool {
        let date_time = date_time.into();
        self.predicates.iter().all(|pred| pred.matches(date_time))
    }
}

impl IntoIterator for TimeSpec {
    type IntoIter = TimeSpecFilter<CountSeconds>;
    type Item = Timestamp;

    fn into_iter(self) -> Self::IntoIter {
        TimeSpecFilter {
            inner: CountSeconds::Chronological(Timestamp::now()),
            spec: self,
        }
    }
}

/// An iterator that filters the elements of an inner iterator with a timespec. Created using `TimeSpec::filter`.
pub struct TimeSpecFilter<I: Iterator<Item = Timestamp>> {
    inner: I,
    spec: TimeSpec,
}

impl<I: Iterator<Item = Timestamp>> Iterator for TimeSpecFilter<I> {
    type Item = Timestamp;

    fn next(&mut self) -> Option<Timestamp> {
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
pub fn next<S: ToString, I: IntoIterator<Item = S>>(predicates: I) -> Result<Option<Timestamp>, Error> {
    Ok(TimeSpec::parse(Timestamp::now(), predicates)?.next())
}

/// This function is provided as a shortcut to get the next datetime from a set of predicates, starting with a given date and continuing into the future.
///
/// # Returns
///
/// * `Ok(Some(date_time))` if a date was found
/// * `Ok(None)` if the predicates parse to a valid timespec but no date was found
/// * `Err(...)` if the predicates are not valid timespec syntax
pub fn next_after<S: ToString, I: IntoIterator<Item = S>>(start: Timestamp, predicates: I) -> Result<Option<Timestamp>, Error> {
    Ok(TimeSpec::parse(start, predicates)?.next_after(start))
}
