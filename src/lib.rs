//! This is a Rust implementation of [timespec](https://github.com/fenhl/timespec), a mini-language for specifying dates and times, intended to be used in command-line tools.
//!
//! For documentation of the timespec syntax, see [the timespec repository](https://github.com/fenhl/timespec).
//!
//! This crate implements timespec directions and predicates as iterator adaptors.

#![cfg_attr(test, deny(warnings))]
#![warn(trivial_casts)]
#![deny(unused, missing_docs, unused_import_braces, unused_qualifications)]
#![deny(rust_2018_idioms)] // this badly-named lint actually produces errors when Rust 2015 idioms are used

use std::{
    collections::HashSet,
    num::ParseIntError,
    str::FromStr
};
use chrono::{
    Duration,
    prelude::*
};
use regex::Regex;

/// An error that occurred while parsing a timespec predicate.
#[derive(Debug)]
pub enum Error {
    /// A predicate tried to use a timespec plugin which has not been defined. The plugin name is included in the error data.
    NoSuchPlugin(String),
    /// An error occurred while parsing a number.
    ParseInt(ParseIntError),
    /// While parsing a modulus or relative-plugin predicate, an unknown unit letter was encountered.
    Unit(String),
    /// The following predicate could not be parsed.
    UnknownPredicate(String)
}

impl From<ParseIntError> for Error {
    fn from(e: ParseIntError) -> Error {
        Error::ParseInt(e)
    }
}

/// An iterator yielding datetimes for every second from the given start time.
#[derive(Debug, Clone)]
pub enum CountSeconds<O: Offset, Tz: TimeZone<Offset = O>> {
    /// Start with the start datetime and continue into the future.
    Chronological(DateTime<Tz>),
    /// Start with the start datetime and continue into the past.
    Reverse(DateTime<Tz>)
}

impl<O: Offset, Tz: TimeZone<Offset = O>> Iterator for CountSeconds<O, Tz> {
    type Item = DateTime<Tz>;

    fn next(&mut self) -> Option<DateTime<Tz>> {
        let (result, next_state) = match *self {
            CountSeconds::Chronological(ref start_date) => (start_date.clone(), CountSeconds::Chronological(start_date.clone() + Duration::seconds(1))),
            CountSeconds::Reverse(ref start_date) => (start_date.clone(), CountSeconds::Reverse(start_date.clone() - Duration::seconds(1)))
        };
        *self = next_state;
        Some(result)
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Unit {
    Seconds,
    Minutes,
    Hours,
    Days
}

impl FromStr for Unit {
    type Err = Error;

    fn from_str(s: &str) -> Result<Unit, Error> {
        match s {
            "s" => Ok(Unit::Seconds),
            "m" => Ok(Unit::Minutes),
            "h" => Ok(Unit::Hours),
            "d" => Ok(Unit::Days),
            _ => Err(Error::Unit(s.into()))
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Predicate {
    Date(Option<i32>, Option<u8>, Option<u8>),
    ExactSecond(DateTime<Utc>),
    Modulus(u8, Unit),
    Time(Option<u8>, Option<u8>, Option<u8>),
    Weekday(Weekday),
    YearMod(u8)
}

impl Predicate {
    fn matches<O: Offset, Tz: TimeZone<Offset = O>>(&self, date_time: DateTime<Tz>) -> bool {
        match *self {
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
            Predicate::Weekday(weekday) => date_time.weekday() == weekday,
            Predicate::YearMod(year_mod) => (date_time.year() % 100) as u8 == year_mod
        }
    }
}

impl FromStr for Predicate {
    type Err = Error;

    fn from_str(s: &str) -> Result<Predicate, Error> {
        if let Some(captures) = Regex::new("^([a-z]+):(.*)$").unwrap().captures(s) {
            return Err(Error::NoSuchPlugin(captures[1].into())); //TODO plugin support
        }
        if let Ok(weekday) = s.parse() {
            return Ok(Predicate::Weekday(weekday));
        }
        if let Some(captures) = Regex::new("^([0-9]{1,2})([smhd])$").unwrap().captures(s) {
            return Ok(Predicate::Modulus(captures[0].parse()?, captures[1].parse()?));
        }
        if let Some(captures) = Regex::new("^([0-9]{1,9})?-([0-9]{1,9})?(?:-([0-9]{1,9})?)$").unwrap().captures(s) {
            return Ok(Predicate::Date(
                captures.get(1).map(|cap| cap.as_str().parse()).transpose()?,
                captures.get(2).map(|cap| cap.as_str().parse()).transpose()?,
                captures.get(3).map(|cap| cap.as_str().parse()).transpose()?
            ));
        }
        if let Some(captures) = Regex::new("^([0-9]{1,9})?:([0-9]{1,9})?(?::([0-9]{1,9})?)$").unwrap().captures(s) {
            return Ok(Predicate::Time(
                captures.get(1).map(|cap| cap.as_str().parse()).transpose()?,
                captures.get(2).map(|cap| cap.as_str().parse()).transpose()?,
                captures.get(3).map(|cap| cap.as_str().parse()).transpose()?
            ));
        }
        if Regex::new("^[0-9]{10,}$").unwrap().is_match(s) {
            // exact POSIX timestamp
            return Ok(Predicate::ExactSecond(Utc.timestamp(s.parse()?, 0)));
        }
        if Regex::new("^[0-9]{4,9}$").unwrap().is_match(s) {
            // absolute year
            return Ok(Predicate::Date(Some(s.parse()?), None, None));
        }
        if Regex::new("^[0-9]{1,2}$").unwrap().is_match(s) {
            // year mod 100
            return Ok(Predicate::YearMod(s.parse()?));
        }
        Err(Error::UnknownPredicate(s.into()))
    }
}

/// This type represents a parsed timespec.
#[derive(Debug)]
pub struct TimeSpec {
    predicates: HashSet<Predicate>
}

impl TimeSpec {
    /// Parses a list of predicates into a timespec.
    pub fn parse<S: ToString, I: IntoIterator<Item = S>>(predicates: I) -> Result<TimeSpec, Error> {
        let mut parsed_predicates = HashSet::default();
        for predicate in predicates {
            parsed_predicates.insert(predicate.to_string().parse()?);
        }
        Ok(TimeSpec { predicates: parsed_predicates })
    }

    /// Filters the iterable `search_space` by discarding all datetimes that don't match this timespec.
    pub fn filter<O: Offset, Tz: TimeZone<Offset = O>, I: IntoIterator<Item = DateTime<Tz>>>(self, search_space: I) -> TimeSpecFilter<O, Tz, I::IntoIter> {
        TimeSpecFilter {
            inner: search_space.into_iter(),
            spec: self
        }
    }

    /// Checks whether the given datetime matches this timespec.
    pub fn matches<O: Offset, Tz: TimeZone<Offset = O>>(&self, date_time: DateTime<Tz>) -> bool {
        self.predicates.iter().all(|pred| pred.matches(date_time.clone()))
    }
}

impl IntoIterator for TimeSpec {
    type IntoIter = TimeSpecFilter<Utc, Utc, CountSeconds<Utc, Utc>>;
    type Item = DateTime<Utc>;

    fn into_iter(self) -> Self::IntoIter {
        TimeSpecFilter {
            inner: CountSeconds::Chronological(Utc::now()),
            spec: self
        }
    }
}

/// An iterator that filters the elements of an inner iterator with a timespec. Created using `TimeSpec::filter`.
pub struct TimeSpecFilter<O: Offset, Tz: TimeZone<Offset = O>, I: Iterator<Item = DateTime<Tz>>> {
    inner: I,
    spec: TimeSpec
}

impl<O: Offset, Tz: TimeZone<Offset = O>, I: Iterator<Item = DateTime<Tz>>> Iterator for TimeSpecFilter<O, Tz, I> {
    type Item = DateTime<Tz>;

    fn next(&mut self) -> Option<DateTime<Tz>> {
        for x in &mut self.inner {
            if self.spec.matches(x.clone()) {
                return Some(x);
            }
        }
        None
    }
}

/// This function is provided as a shortcut to get the next datetime from a set of predicates, starting with the current system time in UTC and continuing into the future.
///
/// # Returns
///
/// * `Ok(Some(date_time))` if a date was found
/// * `Ok(None)` if the predicates parse to a valid timespec but no date was found
/// * `Err(...)` if the predicates are not valid timespec syntax
pub fn next<S: ToString, I: IntoIterator<Item = S>>(predicates: I) -> Result<Option<DateTime<Utc>>, Error> {
    Ok(TimeSpec::parse(predicates)?.filter(CountSeconds::Chronological(Utc::now())).next())
}
