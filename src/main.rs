use {
    std::{
        env,
        process::exit,
    },
    timespec::Error,
};

fn main() -> Result<(), Error> {
    let mut args = env::args();
    let _ = args.next(); // ignore executable name
    if let Some(date_time) = timespec::next(args)? {
        println!("{}", date_time);
        Ok(())
    } else {
        eprintln!("no matches found");
        exit(1)
    }
}
