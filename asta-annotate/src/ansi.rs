use core::fmt;

use crate::Mark;

#[derive(Default, Clone, Copy)]
pub struct MarkStyle {
    pub before: Option<anstyle::Style>,
    pub content: Option<anstyle::Style>,
    pub after: Option<anstyle::Style>,
}

impl MarkStyle {
    pub fn before(value: anstyle::Style) -> Self {
        Self {
            before: Some(value),
            ..Default::default()
        }
    }
    pub fn content(value: anstyle::Style) -> Self {
        Self {
            content: Some(value),
            ..Default::default()
        }
    }
    pub fn after(value: anstyle::Style) -> Self {
        Self {
            after: Some(value),
            ..Default::default()
        }
    }
}

pub fn apply(
    new: anstyle::Style,
    style: &mut anstyle::Style,
    f: &mut fmt::Formatter<'_>,
) -> Result<(), fmt::Error> {
    if new != *style {
        let old = core::mem::replace(style, new);
        write!(f, "{old:#}{new}")
    } else {
        Ok(())
    }
}

impl From<anstyle::Style> for MarkStyle {
    fn from(value: anstyle::Style) -> Self {
        Self {
            before: Some(value),
            content: Some(value),
            after: Some(value),
        }
    }
}

impl Mark for anstyle::Style {
    fn style(&self) -> MarkStyle {
        (*self).into()
    }
}

impl Mark for anstyle::Color {
    fn style(&self) -> MarkStyle {
        self.on_default().into()
    }
}

impl Mark for anstyle::AnsiColor {
    fn style(&self) -> MarkStyle {
        self.on_default().into()
    }
}

impl Mark for anstyle::Ansi256Color {
    fn style(&self) -> MarkStyle {
        self.on_default().into()
    }
}

impl Mark for anstyle::RgbColor {
    fn style(&self) -> MarkStyle {
        self.on_default().into()
    }
}
