use std::fmt;

use semver::Version;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VersionReq {
    inner: semver::VersionReq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VersionReqErrorCode {
    V0001,
    V0002,
    V0003,
}

impl fmt::Display for VersionReqErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VersionReqErrorCode::V0001 => write!(f, "V0001"),
            VersionReqErrorCode::V0002 => write!(f, "V0002"),
            VersionReqErrorCode::V0003 => write!(f, "V0003"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VersionReqError {
    pub code: VersionReqErrorCode,
    pub input: String,
    pub message: String,
}

impl VersionReqError {
    fn new(
        code: VersionReqErrorCode,
        input: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code,
            input: input.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for VersionReqError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.code, self.message)
    }
}

impl std::error::Error for VersionReqError {}

impl VersionReq {
    pub fn parse(s: &str) -> Result<Self, VersionReqError> {
        let trimmed = s.trim();
        if trimmed.is_empty() {
            return Err(VersionReqError::new(
                VersionReqErrorCode::V0001,
                s,
                "version requirement must not be empty",
            ));
        }

        if looks_like_bare_version(trimmed) {
            if let Err(msg) = validate_bare_version(trimmed) {
                return Err(VersionReqError::new(
                    VersionReqErrorCode::V0002,
                    s,
                    format!(
                        "invalid bare version '{s}': {msg}; bare versions must be of the form \
                         'major.minor.patch' (e.g. '1.2.3')"
                    ),
                ));
            }
        }

        match semver::VersionReq::parse(trimmed) {
            Ok(inner) => Ok(VersionReq { inner }),
            Err(e) => Err(VersionReqError::new(
                VersionReqErrorCode::V0003,
                s,
                format!("invalid version requirement '{s}': {e}"),
            )),
        }
    }

    pub fn matches(&self, v: &Version) -> bool {
        self.inner.matches(v)
    }
}

impl fmt::Display for VersionReq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.inner, f)
    }
}

fn looks_like_bare_version(trimmed: &str) -> bool {
    matches!(trimmed.chars().next(), Some(c) if c.is_ascii_digit()) && !trimmed.contains(',')
}

fn validate_bare_version(s: &str) -> Result<(), String> {
    let core_end = s.find(['-', '+']).unwrap_or(s.len());
    let core = &s[..core_end];
    let parts: Vec<&str> = core.split('.').collect();
    if parts.len() != 3 {
        return Err(format!(
            "expected 3 numeric components separated by '.', found {}",
            parts.len()
        ));
    }
    for p in &parts {
        if p.is_empty() || !p.bytes().all(|b| b.is_ascii_digit()) {
            return Err(format!(
                "component '{p}' is not a non-empty sequence of ASCII digits"
            ));
        }
    }
    Ok(())
}
