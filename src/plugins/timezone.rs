use {
    std::collections::HashMap,
    jiff::{
        Timestamp,
        tz::TimeZone,
    },
    crate::{
        Error,
        Plugin,
        Predicate,
    },
};

pub(crate) struct WithTimeZone;

impl Plugin for WithTimeZone {
    fn parse(&self, plugins: &HashMap<String, Box<dyn Plugin>>, _: TimeZone, start: Timestamp, param_str: &str) -> Result<Predicate, Error> {
        let (zone, spec) = param_str.split_once(':').ok_or_else(|| Error::Plugin(format!("z plugin requires IANA timezone identifier followed by : followed by timespec")))?;
        let zone = TimeZone::get(zone)?;
        shlex::split(spec).ok_or_else(|| Error::Plugin(format!("failed to split zoned timespec")))?.into_iter().map(|pred| Predicate::from_str_with_plugins(plugins, zone.clone(), start, &pred)).collect::<Result<_, _>>().map(Predicate::All)
    }
}
