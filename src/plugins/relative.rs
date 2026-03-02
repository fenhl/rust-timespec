use {
    std::{
        collections::HashMap,
        str::FromStr,
    },
    chrono::{
        Duration,
        TimeDelta,
        prelude::*,
    },
    chrono_tz::Tz,
    lazy_regex::regex_captures,
    crate::{
        Error,
        Plugin,
        Predicate,
    },
};

enum Unit {
    Seconds,
    Minutes,
    Hours,
    Days,
    Weeks,
}

impl FromStr for Unit {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        match s {
            "s" => Ok(Self::Seconds),
            "m" => Ok(Self::Minutes),
            "h" => Ok(Self::Hours),
            "d" => Ok(Self::Days),
            "w" => Ok(Self::Weeks),
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
            Unit::Weeks => TimeDelta::try_weeks(1).unwrap(),
        }
    }
}

pub(crate) struct Relative;

impl Plugin for Relative {
    fn parse(&self, _: &HashMap<String, Box<dyn Plugin>>, _: Tz, start: DateTime<Utc>, mut param_str: &str) -> Result<Predicate, Error> {
        let mut duration = Duration::zero();
        while let Some((full_match, interval, unit)) = regex_captures!("^([0-9]+)([smhdw])", param_str) {
            duration += Duration::from(unit.parse::<Unit>()?) * interval.parse()?;
            param_str = &param_str[full_match.len()..];
        }
        if !param_str.is_empty() {
            duration += Duration::try_seconds(param_str.parse()?).unwrap();
        }
        Ok(Predicate::ExactSecond(start + duration))
    }
}
