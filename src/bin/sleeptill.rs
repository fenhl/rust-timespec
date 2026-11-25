#![deny(rust_2018_idioms, unused, unused_import_braces, unused_lifetimes, unused_qualifications, warnings)]
#![forbid(unsafe_code)]

use {
    std::{
        io::{
            self,
            prelude::*,
            stdout,
        },
        num::ParseIntError,
        thread::sleep,
        time::Duration,
    },
    jiff::{
        Timestamp,
        ZonedDateTime,
        tz::TimeZone,
    },
    timespec::CountSeconds,
};

#[derive(clap::Parser)]
struct Args {
    timespec: Vec<String>,
    #[clap(short, long)]
    /// Sleep for the sum of the specified intervals. Default unit is seconds, but s/m/h/d can be used to specify seconds/minutes/hours/days.
    relative: bool,
    #[clap(short = 'z', long, value_parser = TimeZone::get)]
    /// Use the specified timezone instead of the system timezone.
    timezone: Option<TimeZone>,
    #[clap(short, long)]
    /// Show an info line while sleeping.
    verbose: bool,
}

#[derive(Debug, thiserror::Error)]
enum Error {
    #[error(transparent)] Io(#[from] io::Error),
    #[error(transparent)] Jiff(#[from] jiff::Error),
    #[error(transparent)] ParseInt(#[from] ParseIntError),
    #[error(transparent)] TimeSpec(#[from] timespec::Error),
    #[error("no matches found")]
    NoMatches,
}

fn parse_duration(s: &str) -> Result<Duration, Error> {
    Ok(match s.chars().next_back() {
        Some('s') => Duration::from_secs(s[..s.len() - 1].parse()?),
        Some('m') => Duration::from_secs(60 * s[..s.len() - 1].parse::<u64>()?),
        Some('h') => Duration::from_secs(60 * 60 * s[..s.len() - 1].parse::<u64>()?),
        Some('d') => Duration::from_secs(24 * 60 * 60 * s[..s.len() - 1].parse::<u64>()?),
        _ => Duration::from_secs(s.parse()?),
    })
}

fn fmt_duration(duration: &Duration) -> String {
    let secs = duration.as_secs();
    let mins = secs / 60;
    let secs = secs % 60;
    let hours = mins / 60;
    let mins = mins % 60;
    let days = hours / 24;
    let hours = hours % 24;
    if days > 0 {
        format!("{days}d {hours:02}h {mins:02}m {secs:02}s")
    } else if hours > 0 {
        format!("{hours}h {mins:02}m {secs:02}s")
    } else if mins > 0 {
        format!("{mins}m {secs:02}s")
    } else {
        format!("{secs}s")
    }
}

fn sleeptill_main_inner(relative: bool, timespec: Vec<String>, verbose: bool, timezone: TimeZone, now: Timestamp) -> Result<(), Error> {
    let (end_date, duration) = if relative {
        let mut duration = Duration::default();
        for part in timespec {
            duration += parse_duration(&part)?;
        }
        let end_date = now.clone() + duration;
        (end_date, duration)
    } else {
        let spec = timespec::TimeSpec::parse_with_timezone(timezone, now, timespec)?;
        let end_date = spec.filter(CountSeconds::Chronological(now)).next().ok_or(Error::NoMatches)?;
        let duration = (end_date.clone() - now.clone()).try_into()?;
        (end_date, duration)
    };
    if verbose {
        let mut stdout = stdout();
        while Timestamp::now() < end_date {
            print!("   \rsleeping until {} ({} total, {} remaining)", end_date.strftime("%F %T"), fmt_duration(&duration), fmt_duration(&(end_date.clone() - Timestamp::now()).try_into()?));
            stdout.flush()?;
            sleep(Duration::from_secs(1));
        }
        println!("");
    } else {
        sleep(duration);
    }
    Ok(())
}

#[wheel::main]
fn main(args: Args) -> Result<(), Error> {
    let now = ZonedDateTime::now().with().subsec_nanosecond(0).build().expect("could not truncate subsecond portion of now");
    sleeptill_main_inner(args.relative, args.timespec, args.verbose, args.timezone.unwrap_or_else(|| TimeZone::system()), now.timestamp())
}
