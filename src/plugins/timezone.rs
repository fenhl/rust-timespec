use {
    std::collections::HashMap,
    chrono::prelude::*,
    chrono_tz::Tz,
    crate::{
        Error,
        Plugin,
        Predicate,
    },
};

pub(crate) struct WithTimeZone;

impl Plugin for WithTimeZone {
    fn parse(&self, plugins: &HashMap<String, Box<dyn Plugin>>, _: Tz, start: DateTime<Utc>, param_str: &str) -> Result<Predicate, Error> {
        let (zone, spec) = param_str.split_once(':').ok_or_else(|| Error::Plugin(format!("z plugin requires IANA timezone identifier followed by : followed by timespec")))?;
        let zone = zone.parse().map_err(|e| Error::Plugin(format!("failed to parse timezone: {e:?}")))?;
        Predicate::from_str_with_plugins(plugins, zone, &start, spec)
    }
}
