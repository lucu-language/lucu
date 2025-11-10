use core::fmt;

use crate::Mark;

impl Mark for anstyle::Style {
    fn fmt_before(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.render())
    }
    fn fmt_after(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.render_reset())
    }
}

impl Mark for anstyle::Color {
    fn fmt_before(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render())
    }
    fn fmt_after(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render_reset())
    }
}

impl Mark for anstyle::AnsiColor {
    fn fmt_before(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render())
    }
    fn fmt_after(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render_reset())
    }
}

impl Mark for anstyle::Ansi256Color {
    fn fmt_before(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render())
    }
    fn fmt_after(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render_reset())
    }
}

impl Mark for anstyle::RgbColor {
    fn fmt_before(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render())
    }
    fn fmt_after(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.on_default().render_reset())
    }
}
