use {
    chrono::{
        Duration,
        prelude::*,
    },
    lazy_regex::regex_captures,
    crate::{
        Error,
        Plugin,
        Predicate,
        Unit,
    },
};

pub(crate) struct Relative;

impl Plugin for Relative {
    fn parse(&self, mut param_str: &str, start: DateTime<Utc>) -> Result<Predicate, Error> {
        let mut duration = Duration::zero();
        while let Some((full_match, interval, unit)) = regex_captures!("^([0-9]+)([smhd])", param_str) {
            duration = duration + Duration::from(unit.parse::<Unit>()?) * interval.parse()?;
            param_str = &param_str[full_match.len()..];
        }
        if !param_str.is_empty() {
            duration = duration + Duration::seconds(param_str.parse()?);
        }
        Ok(Predicate::ExactSecond(start + duration))
    }
}
