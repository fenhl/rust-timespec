#![deny(rust_2018_idioms, unused, unused_import_braces, unused_lifetimes, unused_qualifications, warnings)]
#![forbid(unsafe_code)]

use {
    std::{
        fmt,
        io::{
            self,
            prelude::*,
            stdout,
        },
        num::ParseIntError,
        thread::sleep,
        time::Duration,
    },
    chrono::prelude::*,
    chrono_tz::Tz,
    structopt::StructOpt,
    timespec::CountSeconds,
};

#[derive(StructOpt)]
struct Args {
    timespec: Vec<String>,
    #[structopt(short, long)]
    /// Sleep for the sum of the specified intervals. Default unit is seconds, but s/m/h/d can be used to specify seconds/minutes/hours/days.
    relative: bool,
    #[structopt(short = "z", long)]
    /// Use the specified timezone instead of the system timezone.
    timezone: Option<Tz>,
    #[structopt(short, long)]
    /// Show an info line while sleeping.
    verbose: bool,
}

#[derive(Debug, thiserror::Error)]
enum Error {
    #[error(transparent)] DurationOutOfRange(#[from] time::OutOfRangeError),
    #[error(transparent)] Io(#[from] io::Error),
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
    let hours = hours % 60;
    if days > 0 {
        format!("{}d {:02}h {:02}m {:02}s", days, hours, mins, secs)
    } else if hours > 0 {
        format!("{}h {:02}m {:02}s", hours, mins, secs)
    } else if mins > 0 {
        format!("{}m {:02}s", mins, secs)
    } else {
        format!("{}s", secs)
    }
}

fn sleeptill_main_inner<Z: TimeZone>(relative: bool, timespec: Vec<String>, verbose: bool, now: DateTime<Z>) -> Result<(), Error>
where Z::Offset: fmt::Display {
    let (end_date, duration) = if relative {
        let mut duration = Duration::default();
        for part in timespec {
            duration += parse_duration(&part)?;
        }
        let end_date = now.clone() + chrono::Duration::from_std(duration)?;
        (end_date, duration)
    } else {
        let spec = timespec::TimeSpec::parse(&now, timespec)?;
        let end_date = spec.filter(CountSeconds::Chronological(now.clone())).next().ok_or(Error::NoMatches)?;
        let duration = (end_date.clone() - now.clone()).to_std()?;
        (end_date, duration)
    };
    if verbose {
        let mut stdout = stdout();
        while Local::now().with_timezone(&now.timezone()) < end_date {
            print!("   \rsleeping until {} ({} total, {} remaining)", end_date.format("%Y-%m-%d %H:%M:%S"), fmt_duration(&duration), fmt_duration(&(end_date.clone() - Local::now().with_timezone(&now.timezone())).to_std()?));
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
    let now = Local::now().with_nanosecond(0).expect("could not truncate subsecond portion of now");
    if let Some(tz) = args.timezone {
        sleeptill_main_inner(args.relative, args.timespec, args.verbose, now.with_timezone(&tz))
    } else {
        sleeptill_main_inner(args.relative, args.timespec, args.verbose, now)
    }
}
