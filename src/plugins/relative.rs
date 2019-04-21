use chrono::{
    Duration,
    prelude::*
};
use regex::Regex;
use crate::{
    Error,
    Plugin,
    Predicate,
    Unit
};

pub(crate) struct Relative;

impl Plugin for Relative {
    fn parse(&self, mut param_str: &str, start: DateTime<Utc>) -> Result<Predicate, Error> {
        let re = Regex::new("^([0-9]{1,2})([smhd])").unwrap();
        let mut duration = Duration::zero();
        while let Some(captures) = re.captures(param_str) {
            let interval = captures[1].parse()?;
            let unit = captures[2].parse::<Unit>()?;
            duration = duration + Duration::from(unit) * interval;
            param_str = &param_str[captures.len()..];
        }
        if !param_str.is_empty() {
            duration = duration + Duration::seconds(param_str.parse()?);
        }
        Ok(Predicate::ExactSecond(start + duration))
    }
}
