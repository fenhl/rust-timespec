use {
    std::collections::HashMap,
    jiff::{
        Span,
        Timestamp,
        tz::TimeZone,
    },
    crate::{
        Error,
        Plugin,
        Predicate,
    },
};

pub(crate) struct Relative;

impl Plugin for Relative {
    fn parse(&self, _: &HashMap<String, Box<dyn Plugin>>, _: TimeZone, start: Timestamp, param_str: &str) -> Result<Predicate, Error> {
        Ok(Predicate::ExactSecond(start + param_str.parse::<Span>()?))
    }
}
