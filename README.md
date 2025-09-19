This is a [Rust](https://www.rust-lang.org/) implementation of [timespec](https://github.com/fenhl/timespec), a mini-language for specifying dates and times, intended to be used in command-line tools.

This implementation currently has the capabilities specified in timespec 1.4.0 and includes the `r` plugin, as well as a new `z` plugin which allows modifying the timezone in which a predicate is evaluated. For example, `z:Europe/Berlin:mon` evaluates to a timespec which matches all datetimes whose local date in Berlin is a Monday.
