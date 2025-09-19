use {
    std::collections::HashMap,
    chrono::{
        Duration,
        prelude::*,
    },
    chrono_tz::Tz,
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
    fn parse(&self, _: &HashMap<String, Box<dyn Plugin>>, _: Tz, start: DateTime<Utc>, mut param_str: &str) -> Result<Predicate, Error> {
        let mut duration = Duration::zero();
        while let Some((full_match, interval, unit)) = regex_captures!("^([0-9]+)([smhd])", param_str) {
            duration += Duration::from(unit.parse::<Unit>()?) * interval.parse()?;
            param_str = &param_str[full_match.len()..];
        }
        if !param_str.is_empty() {
            duration += Duration::try_seconds(param_str.parse()?).unwrap();
        }
        Ok(Predicate::ExactSecond(start + duration))
    }
}
