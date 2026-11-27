//! Search core for Finder: fuzzy matching, typo tolerance, MRU and frecency.
//!
//! This is the ranking half of instantMENU's menu pipeline, adapted to rwm's
//! in-process app corpus. Candidates are prepared once by `Finder`; each query
//! compiles one `frizbee` matcher and reuses it for every label and hidden
//! search term. Selection history is persisted in the same state directory as
//! the existing Finder recency file, so a launch is immediately reflected when
//! Finder opens with an empty query.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use frizbee::{CaseMatching, Config, Matcher, SortStrategy};

/// One prepared search candidate. `id` is the stable identity (the desktop
/// file path), `label` is what the UI draws, and `search_text` carries hidden
/// terms such as the Exec line and desktop file name.
#[derive(Clone, Debug)]
pub struct Candidate {
    pub id: String,
    pub label: String,
    pub search_text: String,
}

/// A fuzzy hit with a composite order key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Scored {
    index: usize,
    score: u32,
}

/// Label hits must outrank hits found only in Exec/path text, just as the old
/// substring ranking did.
const LABEL_HIT: u32 = 1 << 31;
/// Four priority bits are enough for exact/prefix/substring/fuzzy tiers.
const PRIORITY_SHIFT: u32 = 24;

/// instantMENU's half-life: selections halve in weight over four days.
const HALF_LIFE: Duration = Duration::from_secs(4 * 24 * 60 * 60);
/// Faded entries below this threshold are pruned on write.
const PRUNE_MIN: f64 = 0.1;
/// Same chunk size instantMENU uses before yielding to its worker.
const MATCH_CHUNK: usize = 64;

/// Decayed score of an entry last used `age` ago.
fn decayed(score: f64, age: Duration) -> f64 {
    score * 2f64.powf(-age.as_secs_f64() / HALF_LIFE.as_secs_f64())
}

/// A selection decays the old score, then counts as one new use.
fn touched(score: f64, age: Duration) -> f64 {
    decayed(score, age) + 1.0
}

/// Clock skew must not make an entry look ancient.
fn age_of(last_used: u64, now: SystemTime) -> Duration {
    now.duration_since(UNIX_EPOCH + Duration::from_secs(last_used))
        .unwrap_or(Duration::ZERO)
}

/// Escape the two characters that can occur in a desktop file path and would
/// otherwise break the line format.
fn render_entry(score: f64, last_used: u64, text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '\\' => escaped.push_str("\\\\"),
            '\t' => escaped.push_str("\\t"),
            _ => escaped.push(c),
        }
    }
    format!("{score:.6} {last_used} {escaped}")
}

fn parse_line(line: &str) -> Option<(String, Entry)> {
    let (score, rest) = line.split_once(' ')?;
    let (last_used, text) = rest.split_once(' ')?;
    let score: f64 = score.parse().ok()?;
    if !score.is_finite() || score < 0.0 {
        return None;
    }
    let last_used: u64 = last_used.parse().ok()?;

    let mut unescaped = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next() {
                Some('t') => unescaped.push('\t'),
                Some('\\') => unescaped.push('\\'),
                _ => return None,
            },
            _ => unescaped.push(c),
        }
    }
    if unescaped.is_empty() {
        return None;
    }
    Some((unescaped, Entry { score, last_used }))
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Entry {
    score: f64,
    last_used: u64,
}

/// Decaying use counts, persisted as `<score> <unix-secs> <id>` lines.
struct Frecency {
    path: Option<PathBuf>,
    entries: HashMap<String, Entry>,
}

impl Frecency {
    fn open(path: Option<PathBuf>) -> Self {
        let mut entries = HashMap::new();
        if let Some(path) = &path {
            match fs::read_to_string(path) {
                Ok(contents) => {
                    let mut bad = 0usize;
                    for line in contents.lines().filter(|line| !line.is_empty()) {
                        match parse_line(line) {
                            Some((id, entry)) => {
                                entries.insert(id, entry);
                            }
                            None => bad += 1,
                        }
                    }
                    if bad > 0 {
                        eprintln!("rwm: skipping {bad} malformed Finder frecency lines");
                    }
                }
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
                Err(err) => eprintln!("rwm: cannot read Finder frecency cache: {err}"),
            }
        }
        Frecency { path, entries }
    }

    fn score_of(&self, id: &str, now: SystemTime) -> f64 {
        self.entries.get(id).map_or(0.0, |entry| {
            decayed(entry.score, age_of(entry.last_used, now))
        })
    }

    fn record(&mut self, id: &str, now: SystemTime) {
        if id.is_empty() {
            return;
        }
        let old = self.entries.get(id).copied();
        let score = touched(
            old.map_or(0.0, |entry| entry.score),
            old.map_or(Duration::ZERO, |entry| age_of(entry.last_used, now)),
        );
        let last_used = now
            .duration_since(UNIX_EPOCH)
            .map(|duration| duration.as_secs())
            .unwrap_or(0);
        self.entries
            .insert(id.to_string(), Entry { score, last_used });
        self.entries
            .retain(|_, entry| decayed(entry.score, age_of(entry.last_used, now)) >= PRUNE_MIN);
        self.write();
    }

    fn write(&self) {
        let Some(path) = &self.path else {
            return;
        };
        let mut keys: Vec<&String> = self.entries.keys().collect();
        keys.sort();
        let mut contents = String::new();
        for key in keys {
            let entry = &self.entries[key];
            contents.push_str(&render_entry(entry.score, entry.last_used, key));
            contents.push('\n');
        }
        if let Some(parent) = path.parent()
            && let Err(err) = fs::create_dir_all(parent)
        {
            eprintln!("rwm: cannot create Finder state directory: {err}");
            return;
        }
        let mut tmp = path.clone().into_os_string();
        tmp.push(".tmp");
        if let Err(err) = fs::write(&tmp, contents).and_then(|()| fs::rename(&tmp, path)) {
            eprintln!("rwm: cannot write Finder frecency cache: {err}");
        }
    }
}

fn state_dir() -> Option<PathBuf> {
    if let Some(dir) = std::env::var_os("XDG_STATE_HOME") {
        let path = PathBuf::from(dir);
        if path.is_absolute() {
            return Some(path.join("dwm"));
        }
    }
    std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/state/dwm"))
}

fn recent_path() -> Option<PathBuf> {
    state_dir().map(|dir| dir.join("finder-recent"))
}

fn frecency_path() -> Option<PathBuf> {
    state_dir().map(|dir| dir.join("finder-frecency"))
}

fn load_recent() -> Vec<String> {
    let Some(path) = recent_path() else {
        return Vec::new();
    };
    fs::read_to_string(path)
        .unwrap_or_default()
        .lines()
        .take(10)
        .map(|line| line.trim_end_matches(['\r', '\n']).to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

/// Compiled query plus scores collected so far. The same query can be ranked
/// again (or extended with new candidates) without recompiling or rescanning;
/// a changed query gets a fresh matcher, as in instantMENU.
#[derive(Clone)]
struct FuzzyCache {
    query: String,
    matcher: Matcher,
    scores: Vec<Scored>,
    scanned: usize,
}

impl FuzzyCache {
    fn new(query: &str) -> Self {
        // instantMENU allows one typo per four query characters; short queries
        // stay exact enough not to flood the list with unrelated apps.
        let max_typos = (query.chars().count() / 4).min(u16::MAX as usize) as u16;
        let config = Config::default()
            .max_typos(Some(max_typos))
            .casing(CaseMatching::Ignore)
            .sort(SortStrategy::IndexAsc);
        FuzzyCache {
            query: query.to_string(),
            matcher: Matcher::new(query, &config),
            scores: Vec::new(),
            scanned: 0,
        }
    }

    /// Score the next chunk of candidates. Label hits carry a high bit so they
    /// always sort above Exec/path-only hits; exact/prefix/substring hits get
    /// priority bits above plain fuzzy hits.
    fn score_chunk(&mut self, candidates: &[Candidate], query: &str) {
        let end = (self.scanned + MATCH_CHUNK).min(candidates.len());
        if end <= self.scanned {
            return;
        }
        let chunk = &candidates[self.scanned..end];

        let labels: Vec<&str> = chunk
            .iter()
            .map(|candidate| candidate.label.as_str())
            .collect();
        let mut label_hit = vec![false; chunk.len()];
        for hit in self.matcher.match_list(&labels) {
            let offset = hit.index as usize;
            if offset >= label_hit.len() {
                continue;
            }
            label_hit[offset] = true;
            let index = self.scanned + offset;
            let priority = label_priority(&chunk[offset].label, query);
            self.scores.push(Scored {
                index,
                score: LABEL_HIT | ((priority as u32) << PRIORITY_SHIFT) | hit.score as u32,
            });
        }

        let hidden: Vec<(usize, &str)> = chunk
            .iter()
            .enumerate()
            .filter(|(offset, _)| !label_hit[*offset])
            .map(|(offset, candidate)| (offset, candidate.search_text.as_str()))
            .collect();
        if !hidden.is_empty() {
            let haystacks: Vec<&str> = hidden.iter().map(|(_, text)| *text).collect();
            for hit in self.matcher.match_list(&haystacks) {
                let Some(&(offset, _)) = hidden.get(hit.index as usize) else {
                    continue;
                };
                let index = self.scanned + offset;
                let priority = label_priority(&chunk[offset].label, query);
                self.scores.push(Scored {
                    index,
                    score: ((priority as u32) << PRIORITY_SHIFT) | hit.score as u32,
                });
            }
        }
        self.scanned = end;
    }

    fn finish(&mut self, candidates: &[Candidate], query: &str) -> Vec<Scored> {
        while self.scanned < candidates.len() {
            self.score_chunk(candidates, query);
        }
        self.scores.clone()
    }
}

/// Exact/prefix/substring tiers mirror the old substring ranking's intent
/// while leaving the remaining order to frizbee's similarity score.
fn label_priority(label: &str, query: &str) -> u8 {
    let label_lower = label.to_lowercase();
    let query_lower = query.to_lowercase();
    if query_lower.is_empty() {
        return 0;
    }
    if label_lower == query_lower {
        return 4;
    }
    if label_lower.starts_with(&query_lower) {
        return 3;
    }
    let Some(pos) = label_lower.find(&query_lower) else {
        return 0;
    };
    if pos > 0 && !label_lower.as_bytes()[pos - 1].is_ascii_alphanumeric() {
        2
    } else {
        1
    }
}

/// Token fallback for multi-word queries whose whole string does not align.
/// Every whitespace-separated token must appear somewhere in the search text.
fn token_matches(candidates: &[Candidate], query: &str) -> Vec<Scored> {
    let tokens: Vec<String> = query
        .split_whitespace()
        .map(|token| token.to_lowercase())
        .collect();
    if tokens.is_empty() {
        return Vec::new();
    }
    candidates
        .iter()
        .enumerate()
        .filter_map(|(index, candidate)| {
            let search_lower = candidate.search_text.to_lowercase();
            if !tokens.iter().all(|token| search_lower.contains(token)) {
                return None;
            }
            let label_lower = candidate.label.to_lowercase();
            let source = if tokens.iter().all(|token| label_lower.contains(token)) {
                LABEL_HIT
            } else {
                0
            };
            Some(Scored {
                index,
                score: source | (1u32 << PRIORITY_SHIFT),
            })
        })
        .collect()
}

/// Finder's search state. Stored on `Finder` so rendering and WM code keep
/// using `apps`, `order` and `visible` unchanged.
pub struct SearchEngine {
    mru: Vec<String>,
    frecency: Frecency,
    cache: Option<FuzzyCache>,
}

impl SearchEngine {
    pub fn new() -> Self {
        SearchEngine {
            mru: load_recent(),
            frecency: Frecency::open(frecency_path()),
            cache: None,
        }
    }

    /// Discard cached scores after the candidate corpus is rebuilt.
    pub fn invalidate(&mut self) {
        self.cache = None;
    }

    fn mru_rank(&self, id: &str) -> usize {
        self.mru
            .iter()
            .position(|recent| recent == id)
            .unwrap_or(usize::MAX)
    }

    fn sort_by_history(&self, indices: &mut [usize], candidates: &[Candidate], now: SystemTime) {
        indices.sort_by(|&a, &b| {
            let a = &candidates[a];
            let b = &candidates[b];
            self.mru_rank(&a.id)
                .cmp(&self.mru_rank(&b.id))
                .then_with(|| {
                    self.frecency
                        .score_of(&b.id, now)
                        .total_cmp(&self.frecency.score_of(&a.id, now))
                })
                .then_with(|| a.label.to_lowercase().cmp(&b.label.to_lowercase()))
        });
    }

    /// Empty query: last launch first, then decaying frecency, then label.
    fn rank_empty(&self, candidates: &[Candidate]) -> Vec<usize> {
        let mut indices: Vec<usize> = (0..candidates.len()).collect();
        self.sort_by_history(&mut indices, candidates, SystemTime::now());
        indices
    }

    /// Full ranking for a query. rwm's corpus is bounded by `MAX_APPS`, so the
    /// inline path is enough; no worker or event-loop change is needed.
    pub fn rank(&mut self, candidates: &[Candidate], query: &str) -> Vec<usize> {
        if query.trim().is_empty() {
            self.cache = None;
            return self.rank_empty(candidates);
        }
        if self
            .cache
            .as_ref()
            .is_none_or(|cache| cache.query != query || cache.scanned > candidates.len())
        {
            self.cache = Some(FuzzyCache::new(query));
        }
        let mut scored = {
            let cache = self.cache.as_mut().unwrap();
            cache.finish(candidates, query)
        };
        if scored.is_empty() {
            scored = token_matches(candidates, query);
        }

        let now = SystemTime::now();
        scored.sort_by(|a, b| {
            b.score
                .cmp(&a.score)
                .then_with(|| {
                    self.mru_rank(&candidates[a.index].id)
                        .cmp(&self.mru_rank(&candidates[b.index].id))
                })
                .then_with(|| {
                    self.frecency
                        .score_of(&candidates[b.index].id, now)
                        .total_cmp(&self.frecency.score_of(&candidates[a.index].id, now))
                })
                .then_with(|| a.index.cmp(&b.index))
        });
        scored.into_iter().map(|hit| hit.index).collect()
    }

    /// Record a launch in both the MRU list and the decaying frecency cache.
    pub fn record(&mut self, id: &str) {
        if id.is_empty() {
            return;
        }
        if let Some(pos) = self.mru.iter().position(|recent| recent == id) {
            self.mru.remove(pos);
        }
        self.mru.insert(0, id.to_string());
        self.mru.truncate(10);
        self.save_recent();
        self.frecency.record(id, SystemTime::now());
    }

    fn save_recent(&self) {
        let Some(path) = recent_path() else {
            return;
        };
        let mut text = String::new();
        for id in &self.mru {
            text.push_str(id);
            text.push('\n');
        }
        if let Some(parent) = path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        let tmp = path.with_extension("tmp");
        if fs::write(&tmp, text).is_ok() {
            let _ = fs::rename(&tmp, path);
        }
    }
}

impl Default for SearchEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// A search engine that never reads or writes the user's state files.
#[cfg(test)]
pub(crate) fn empty_for_tests() -> SearchEngine {
    SearchEngine {
        mru: Vec::new(),
        frecency: Frecency {
            path: None,
            entries: HashMap::new(),
        },
        cache: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn engine() -> SearchEngine {
        empty_for_tests()
    }

    fn candidate(label: &str) -> Candidate {
        Candidate {
            id: label.to_string(),
            label: label.to_string(),
            search_text: label.to_string(),
        }
    }

    fn labels<'a>(candidates: &'a [Candidate], order: &[usize]) -> Vec<&'a str> {
        order
            .iter()
            .map(|&index| candidates[index].label.as_str())
            .collect()
    }

    #[test]
    fn fuzzy_order_prefers_exact_then_prefix() {
        let candidates: Vec<Candidate> = ["Chromium", "Mozilla Firefox", "Firefox", "Fire"]
            .iter()
            .map(|label| candidate(label))
            .collect();
        let mut engine = engine();
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "fire")),
            vec!["Fire", "Firefox", "Mozilla Firefox"]
        );
    }

    #[test]
    fn typo_tolerance_finds_missing_character() {
        let candidates: Vec<Candidate> = ["Firefox", "Chromium"]
            .iter()
            .map(|label| candidate(label))
            .collect();
        let mut engine = engine();
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "firefx")),
            vec!["Firefox"]
        );
    }

    #[test]
    fn hidden_terms_never_outrank_label_hits() {
        let mut hidden = candidate("Terminal Emulator");
        hidden.id = "/usr/share/applications/terminal.desktop".to_string();
        hidden.search_text = "exec /usr/bin/firefox --new-window".to_string();
        let candidates = vec![candidate("Firefox"), hidden];
        let mut engine = engine();
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "fire")),
            vec!["Firefox", "Terminal Emulator"]
        );
    }

    #[test]
    fn repeated_query_is_stable() {
        let candidates: Vec<Candidate> = ["Firefox", "Fire", "Chromium"]
            .iter()
            .map(|label| candidate(label))
            .collect();
        let mut engine = engine();
        let first = engine.rank(&candidates, "fire");
        let second = engine.rank(&candidates, "fire");
        assert_eq!(first, second);
    }

    #[test]
    fn empty_query_puts_last_click_first() {
        let candidates: Vec<Candidate> = ["Firefox", "Chromium", "Terminal"]
            .iter()
            .map(|label| candidate(label))
            .collect();
        let mut engine = engine();
        engine.mru = vec!["Chromium".to_string(), "Firefox".to_string()];
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "")),
            vec!["Chromium", "Firefox", "Terminal"]
        );
    }

    #[test]
    fn scores_candidates_beyond_the_first_chunk() {
        let candidates: Vec<Candidate> = (0..140)
            .map(|index| candidate(&format!("App {index:03}")))
            .collect();
        let mut engine = engine();
        let first = engine.rank(&candidates, "App 139");
        assert_eq!(first.first().copied(), Some(139));
        assert_eq!(engine.cache.as_ref().unwrap().scanned, candidates.len());
        assert_eq!(engine.rank(&candidates, "App 139"), first);
    }

    #[test]
    fn record_makes_last_click_first_without_a_query() {
        let candidates: Vec<Candidate> = ["Firefox", "Chromium", "Terminal"]
            .iter()
            .map(|label| candidate(label))
            .collect();
        let mut engine = engine();
        engine.record("Chromium");
        assert_eq!(engine.mru, vec!["Chromium"]);
        assert!(engine.frecency.score_of("Chromium", SystemTime::now()) > 0.99);
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "")),
            vec!["Chromium", "Firefox", "Terminal"]
        );
    }

    #[test]
    fn frecency_breaks_ties_between_unseen_candidates() {
        let candidates: Vec<Candidate> = ["Firefox", "Chromium", "Terminal"]
            .iter()
            .map(|label| candidate(label))
            .collect();
        let mut engine = engine();
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        engine.frecency.entries.insert(
            "Firefox".to_string(),
            Entry {
                score: 3.0,
                last_used: now,
            },
        );
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "")),
            vec!["Firefox", "Chromium", "Terminal"]
        );
    }

    #[test]
    fn token_fallback_matches_reordered_words() {
        let mut hidden = candidate("Browser");
        hidden.search_text = "firefox browser stable".to_string();
        let candidates = vec![candidate("Chromium"), hidden];
        let mut engine = engine();
        assert_eq!(
            labels(&candidates, &engine.rank(&candidates, "browser firefox")),
            vec!["Browser"]
        );
    }

    #[test]
    fn frecency_decays_with_a_four_day_half_life() {
        assert_eq!(decayed(8.0, Duration::ZERO), 8.0);
        assert!((decayed(8.0, HALF_LIFE) - 4.0).abs() < 1e-9);
        assert_eq!(touched(0.0, Duration::ZERO), 1.0);
        assert!((touched(1.0, HALF_LIFE) - 1.5).abs() < 1e-9);
    }

    #[test]
    fn frecency_line_format_roundtrips() {
        for id in [
            "firefox",
            "sh -c 'echo hi'",
            "tab\there",
            "back\\slash",
            "/usr/share/applications/org.mozilla.firefox.desktop",
        ] {
            let line = render_entry(1.5, 1234, id);
            let (parsed, entry) = parse_line(&line).unwrap();
            assert_eq!(parsed, id);
            assert_eq!(
                entry,
                Entry {
                    score: 1.5,
                    last_used: 1234
                }
            );
        }
    }

    #[test]
    fn malformed_frecency_lines_are_rejected() {
        for line in [
            "onlytext",
            "1.0 2",
            "1.0 2 ",
            "abc 2 x",
            "1.0 abc x",
            "-1.0 2 x",
            "NaN 2 x",
            "1.0 2 lone\\",
            "1.0 2 bad\\q",
        ] {
            assert_eq!(parse_line(line), None, "{line:?}");
        }
    }

    #[test]
    fn recording_counts_and_prunes() {
        let now = UNIX_EPOCH + Duration::from_secs(100 * 24 * 60 * 60);
        let mut frecency = Frecency {
            path: None,
            entries: HashMap::from([(
                "ghost".to_string(),
                Entry {
                    score: 1.0,
                    last_used: 0,
                },
            )]),
        };
        frecency.record("alpha", now);
        assert_eq!(
            frecency.entries.get("alpha"),
            Some(&Entry {
                score: 1.0,
                last_used: 100 * 24 * 60 * 60
            })
        );
        assert!(!frecency.entries.contains_key("ghost"));
    }

    #[test]
    fn future_timestamps_count_as_just_used() {
        assert_eq!(
            age_of(10_000_000, UNIX_EPOCH + Duration::from_secs(1)),
            Duration::ZERO
        );
    }
}
