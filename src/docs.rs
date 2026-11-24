//! `click docs NAME`: the "Using Click" part of the AI reference, compiled
//! into the binary so that an installed Click documents its own version.
//!
//! A name is a tactic, answered from the tactic reference with every form of
//! that tactic and its class, or a page, named by its file name (an
//! `index.md` by its directory). A page name two pages share is answered by
//! its qualified names, `concepts/audit` and `cli/audit`.

include!(concat!(env!("OUT_DIR"), "/docs_pages.rs"));

const TACTIC_REFERENCE: &str = "reference/tactics/index.md";

struct Page {
    path: &'static str,
    name: String,
    qualified: String,
    text: &'static str,
}

fn pages() -> Vec<Page> {
    PAGES
        .iter()
        .map(|&(path, text)| {
            let parts = path.trim_end_matches(".md").split('/').collect::<Vec<_>>();
            let name = match parts.as_slice() {
                ["index"] => "start".to_owned(),
                [.., directory, "index"] => (*directory).to_owned(),
                [.., stem] => (*stem).to_owned(),
                [] => String::new(),
            };
            let qualified = match parts.as_slice() {
                [.., directory, "index"] => (*directory).to_owned(),
                [.., directory, stem] => format!("{directory}/{stem}"),
                _ => name.clone(),
            };
            Page {
                path,
                name,
                qualified,
                text,
            }
        })
        .collect()
}

/// A tactic's class, as the tactic reference's table gives it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TacticClass {
    Simple,
    Smart,
    Control,
}

impl TacticClass {
    fn parse(cell: &str) -> Option<Self> {
        match cell {
            "simple" => Some(Self::Simple),
            "smart" => Some(Self::Smart),
            "control" => Some(Self::Control),
            _ => None,
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            Self::Simple => "simple",
            Self::Smart => "smart",
            Self::Control => "control",
        }
    }

    /// What a refusal by a tactic of this class means.
    pub fn refusal_meaning(self) -> &'static str {
        match self {
            Self::Simple => "a refusal within its documented behavior is a bug",
            Self::Smart => "it may miss; if the goal holds, prove it through smaller steps",
            Self::Control => "the refusal is in the tactics it contains",
        }
    }
}

/// What a refusal by an elided form means: a smart form whose argument a
/// search fills, beside a simple form that takes the argument written. The
/// fourth refusal meaning, after the three classes'.
pub const SEARCH_MISS_MEANING: &str = "a search fills its elided argument; if the search finds nothing, that is a search miss: write the argument";

/// The simple form that writes the argument `form` elides: the `using` form
/// the reference lists beside a smart form, such as `apply(fact) using
/// { P; ... }`. `None` for a form that elides
/// nothing, including `close()`, whose `using` form is smart too.
fn explicit_form<'a>(forms: &'a [(String, TacticClass)], form: &str) -> Option<&'a str> {
    let elided = format!("{} using ", form.trim_matches('`'));
    forms
        .iter()
        .find(|(other, class)| {
            *class == TacticClass::Simple && other.trim_matches('`').starts_with(&elided)
        })
        .map(|(other, _)| other.as_str())
}

struct TacticEntry {
    name: String,
    forms: Vec<(String, TacticClass)>,
    sections: Vec<String>,
}

/// The tactic named by a written tactic or a reference form: its leading
/// identifier, or for `let { ... } = step()` the tactic after `=`.
fn tactic_identifier(text: &str) -> Option<&str> {
    let text = text.trim_start().trim_start_matches('`');
    let text = match text.strip_prefix("let ") {
        Some(rest) => rest.split_once('=')?.1.trim_start(),
        None => text,
    };
    let end = text
        .find(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .unwrap_or(text.len());
    let identifier = &text[..end];
    (!identifier.is_empty()).then_some(identifier)
}

fn heading_level(line: &str) -> Option<usize> {
    let level = line.bytes().take_while(|&byte| byte == b'#').count();
    (level > 0 && line.as_bytes().get(level) == Some(&b' ')).then_some(level)
}

/// The section starting at heading line `start`, up to the next heading at
/// its level or above.
fn section(lines: &[&str], start: usize) -> String {
    let level = heading_level(lines[start]).unwrap_or(1);
    let end = lines[start + 1..]
        .iter()
        .position(|line| heading_level(line).is_some_and(|other| other <= level))
        .map_or(lines.len(), |offset| start + 1 + offset);
    lines[start..end].join("\n").trim_end().to_owned()
}

fn tactic_entries() -> Vec<TacticEntry> {
    let Some(&(_, reference)) = PAGES.iter().find(|(path, _)| *path == TACTIC_REFERENCE) else {
        return Vec::new();
    };
    let lines = reference.lines().collect::<Vec<_>>();
    let mut entries: Vec<TacticEntry> = Vec::new();
    fn entry(entries: &mut Vec<TacticEntry>, name: &str) -> usize {
        match entries.iter().position(|entry| entry.name == name) {
            Some(index) => index,
            None => {
                entries.push(TacticEntry {
                    name: name.to_owned(),
                    forms: Vec::new(),
                    sections: Vec::new(),
                });
                entries.len() - 1
            }
        }
    }
    // The summary table: `| form | class | audience | purpose | details |`.
    for line in &lines {
        if !line.starts_with("| `") || line.matches('|').count() < 6 {
            continue;
        }
        let mut cells = line.split('|').map(str::trim).skip(1);
        let (Some(form), Some(class)) = (cells.next(), cells.next()) else {
            continue;
        };
        let (Some(name), Some(class)) = (tactic_identifier(form), TacticClass::parse(class)) else {
            continue;
        };
        // `name(args, ...)` is the row for user-defined tactics.
        if name == "name" {
            continue;
        }
        let index = entry(&mut entries, name);
        let forms = &mut entries[index].forms;
        if !forms.iter().any(|(existing, _)| existing == form) {
            forms.push((form.to_owned(), class));
        }
    }
    // Each `**Form:**` belongs to the section of the heading above it.
    let mut heading = None;
    for (number, line) in lines.iter().enumerate() {
        if heading_level(line).is_some() {
            heading = Some(number);
        }
        let Some(form) = line.strip_prefix("**Form:** ") else {
            continue;
        };
        let (Some(name), Some(start)) = (tactic_identifier(form), heading) else {
            continue;
        };
        if name == "name" {
            continue;
        }
        let index = entry(&mut entries, name);
        let text = section(&lines, start);
        if !entries[index].sections.contains(&text) {
            entries[index].sections.push(text);
        }
    }
    // The implicit tail ends every script and is written as nothing, so it
    // is not a form in the table; its reference is the automation section.
    if let Some(start) = lines
        .iter()
        .position(|line| *line == "## Automation and search")
    {
        let index = entry(&mut entries, "implicit");
        entries[index].forms.push((
            "the implicit tail, written as nothing at the end of a script".to_owned(),
            TacticClass::Smart,
        ));
        entries[index].sections.push(section(&lines, start));
    }
    entries
}

/// The class of a written tactic, when its text selects one form class.
pub fn written_tactic_class(written: &str) -> Option<(String, TacticClass)> {
    let name = tactic_identifier(written)?;
    let entries = tactic_entries();
    let entry = entries.iter().find(|entry| entry.name == name)?;
    let written_has = |marker: &str| written.contains(marker);
    let matching = entry
        .forms
        .iter()
        .filter(|(form, _)| {
            form.contains(" using ") == written_has(" using ")
                && (form.contains(" by ") || form.contains("{ requires"))
                    == (written_has(" by ") || written_has("{ requires"))
        })
        .map(|&(_, class)| class)
        .collect::<Vec<_>>();
    let class = *matching.first()?;
    matching
        .iter()
        .all(|&other| other == class)
        .then(|| (name.to_owned(), class))
}

/// Whether a written tactic is a smart form that elides an argument a
/// simple form of the same tactic takes written, such as `transport(P, Q)`
/// beside its `using` form. Its refusal is a search miss ([`SEARCH_MISS_MEANING`]).
pub fn written_tactic_elides_argument(written: &str) -> bool {
    let Some((name, TacticClass::Smart)) = written_tactic_class(written) else {
        return false;
    };
    tactic_entries()
        .iter()
        .find(|entry| entry.name == name)
        .is_some_and(|entry| {
            entry.forms.iter().any(|(form, class)| {
                *class == TacticClass::Smart && explicit_form(&entry.forms, form).is_some()
            })
        })
}

/// Every name `click docs` answers: tactics first, then pages.
pub fn index() -> String {
    let mut text = String::from(
        "usage: click docs [<NAME>]\n\nPrint the documentation for a tactic or a topic.\n\ntactics:\n",
    );
    for entry in tactic_entries() {
        let mut classes = Vec::new();
        for (_, class) in &entry.forms {
            if !classes.contains(&class.label()) {
                classes.push(class.label());
            }
        }
        text.push_str(&format!("  {:<22} {}\n", entry.name, classes.join(", ")));
    }
    text.push_str("\ntopics:\n");
    let pages = pages();
    for page in &pages {
        let shared = pages.iter().filter(|other| other.name == page.name).count() > 1;
        let name = if shared { &page.qualified } else { &page.name };
        let title = page
            .text
            .lines()
            .find_map(|line| line.strip_prefix("# "))
            .unwrap_or_default();
        text.push_str(&format!("  {name:<26} {title}\n"));
    }
    text
}

/// The documentation for `name`, or a message naming close matches.
pub fn lookup(name: &str) -> Result<String, String> {
    // The parser refuses these older spellings; their docs are the
    // replacement's.
    let name = match name {
        "assumption" | "arithmetic" | "known" | "solve" => "close",
        "execute_until" => "step_until",
        "auto" | "execute" => "implicit",
        name => name,
    };
    let pages = pages();
    if let Some(entry) = tactic_entries()
        .into_iter()
        .find(|entry| entry.name == name)
    {
        return Ok(render_tactic(&entry, &pages));
    }
    let matches = pages
        .iter()
        .filter(|page| {
            page.name == name || page.qualified == name || page.path.trim_end_matches(".md") == name
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [page] => Ok(render_page(page, &pages)),
        [] => Err(unknown(name, &pages)),
        several => Err(format!(
            "`{name}` names several pages: {}",
            several
                .iter()
                .map(|page| format!("`click docs {}`", page.qualified))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

fn render_tactic(entry: &TacticEntry, pages: &[Page]) -> String {
    let mut text = format!("# `{}`\n\nForms:\n\n", entry.name);
    for (form, class) in &entry.forms {
        match explicit_form(&entry.forms, form).filter(|_| *class == TacticClass::Smart) {
            Some(explicit) => text.push_str(&format!(
                "- {form}: {}; {SEARCH_MISS_MEANING}, as {explicit} does.\n",
                class.label(),
            )),
            None => text.push_str(&format!(
                "- {form}: {}; {}.\n",
                class.label(),
                class.refusal_meaning()
            )),
        }
    }
    let directory = TACTIC_REFERENCE.rsplit_once('/').map_or("", |(dir, _)| dir);
    for section in &entry.sections {
        text.push('\n');
        text.push_str(&rendered_markdown(section, directory, pages));
        text.push('\n');
    }
    text
}

fn render_page(page: &Page, pages: &[Page]) -> String {
    let directory = page.path.rsplit_once('/').map_or("", |(dir, _)| dir);
    rendered_markdown(page.text, directory, pages)
}

/// Markdown for a terminal: fixture markers dropped, and each link to an
/// embedded page rewritten to the `click docs` command that prints it.
fn rendered_markdown(text: &str, directory: &str, pages: &[Page]) -> String {
    let mut out = String::with_capacity(text.len());
    for line in text.lines() {
        if line.starts_with("<!-- verified-example:") {
            continue;
        }
        out.push_str(&rewrite_links(line, directory, pages));
        out.push('\n');
    }
    out
}

fn rewrite_links(line: &str, directory: &str, pages: &[Page]) -> String {
    let mut out = String::new();
    let mut rest = line;
    while let Some(open) = rest.find('[') {
        let Some(middle) = rest[open..].find("](").map(|offset| open + offset) else {
            break;
        };
        let Some(close) = rest[middle + 2..]
            .find(')')
            .map(|offset| middle + 2 + offset)
        else {
            break;
        };
        let label = &rest[open + 1..middle];
        let target = &rest[middle + 2..close];
        let path = target.split('#').next().unwrap_or_default();
        match path
            .ends_with(".md")
            .then(|| resolve(directory, path))
            .and_then(|resolved| pages.iter().find(|page| page.path == resolved))
        {
            Some(page) => {
                let shared = pages.iter().filter(|other| other.name == page.name).count() > 1;
                let name = if shared { &page.qualified } else { &page.name };
                out.push_str(&rest[..open]);
                out.push_str(&format!("{label} (`click docs {name}`)"));
            }
            None => out.push_str(&rest[..=close]),
        }
        rest = &rest[close + 1..];
    }
    out.push_str(rest);
    out
}

/// `path` relative to `directory`, with `.` and `..` resolved.
fn resolve(directory: &str, path: &str) -> String {
    let mut parts = directory
        .split('/')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
    for part in path.split('/') {
        match part {
            "." | "" => {}
            ".." => {
                parts.pop();
            }
            part => parts.push(part),
        }
    }
    parts.join("/")
}

fn unknown(name: &str, pages: &[Page]) -> String {
    let mut candidates = tactic_entries()
        .into_iter()
        .map(|entry| entry.name)
        .chain(pages.iter().map(|page| page.name.clone()))
        .filter(|candidate| {
            edit_distance(candidate, name) <= 2 || (name.len() >= 3 && candidate.contains(name))
        })
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    let mut message = format!("no docs for `{name}`");
    if !candidates.is_empty() {
        message.push_str(&format!(
            "; did you mean {}?",
            candidates
                .iter()
                .map(|candidate| format!("`{candidate}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    message.push_str("\nrun `click docs` to list every name");
    message
}

fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.chars().collect::<Vec<_>>();
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    for (row, left) in left.chars().enumerate() {
        let mut current = vec![row + 1];
        for (column, &right) in right.iter().enumerate() {
            let substitution = previous[column] + usize::from(left != right);
            current.push(
                substitution
                    .min(previous[column + 1] + 1)
                    .min(current[column] + 1),
            );
        }
        previous = current;
    }
    previous[right.len()]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_using_click_page_is_embedded_under_a_name() {
        assert!(PAGES.iter().any(|(path, _)| *path == "concepts/tracing.md"));
        assert!(PAGES.iter().any(|(path, _)| *path == TACTIC_REFERENCE));
        assert!(
            lookup("tracing")
                .unwrap()
                .starts_with("# Repairing a failed proof")
        );
        assert!(lookup("start").is_ok());
        assert!(lookup("concepts/tracing").is_ok());
    }

    /// A tactic and a page never share a name, so `click docs NAME` is never
    /// ambiguous between them.
    #[test]
    fn tactic_names_and_page_names_are_disjoint() {
        let pages = pages();
        for entry in tactic_entries() {
            assert!(
                pages.iter().all(|page| page.name != entry.name),
                "`{}` names both a tactic and a page",
                entry.name
            );
        }
    }

    #[test]
    fn a_tactic_entry_lists_every_form_with_its_class() {
        let normalize = lookup("normalize").unwrap();
        assert!(
            normalize.contains("- `normalize()`: simple;"),
            "{normalize}"
        );
        assert!(
            normalize.contains("- `normalize() using { P; ... }`: simple;"),
            "{normalize}"
        );
        assert!(
            normalize.contains("### Context-free normalization"),
            "{normalize}"
        );
        assert!(normalize.contains("### Normalization with selected premises"));
        let apply = lookup("apply").unwrap();
        assert!(
            apply.contains("- `apply(theorem(args))`: simple;"),
            "{apply}"
        );
        let step = lookup("step").unwrap();
        assert!(
            step.contains("- `let { result: name } = step()`: simple;"),
            "{step}"
        );
        assert!(lookup("auto").unwrap().contains("## Automation and search"));
        assert!(!normalize.contains("verified-example"), "{normalize}");
    }

    #[test]
    fn links_to_embedded_pages_become_commands() {
        let pages = pages();
        assert_eq!(
            rewrite_links(
                "see [Repairing a failed proof](tracing.md#outcomes) and [x](https://x.org)",
                "concepts",
                &pages
            ),
            "see Repairing a failed proof (`click docs tracing`) and [x](https://x.org)"
        );
        assert_eq!(
            rewrite_links("[verify](../reference/cli/verify.md)", "concepts", &pages),
            "verify (`click docs verify`)"
        );
    }

    #[test]
    fn a_shared_page_name_lists_its_qualified_names() {
        let error = lookup("audit").unwrap_err();
        assert!(error.contains("`click docs concepts/audit`"), "{error}");
        assert!(error.contains("`click docs cli/audit`"), "{error}");
        assert!(lookup("cli/audit").is_ok());
    }

    #[test]
    fn an_unknown_name_suggests_close_ones() {
        let error = lookup("normalise").unwrap_err();
        assert!(
            error.starts_with("no docs for `normalise`; did you mean"),
            "{error}"
        );
        assert!(error.contains("`normalize`"), "{error}");
    }

    #[test]
    fn a_written_tactic_selects_its_class() {
        let class = |written| written_tactic_class(written).map(|(_, class)| class);
        assert_eq!(class("normalize();"), Some(TacticClass::Simple));
        assert_eq!(class("close();"), Some(TacticClass::Smart));
        assert_eq!(class("apply(t(x));"), Some(TacticClass::Simple));
        assert_eq!(
            class("apply(a == b implies c == d);"),
            Some(TacticClass::Simple)
        );
        assert_eq!(class("step();"), Some(TacticClass::Simple));
        assert_eq!(class("step() by { close(); }"), Some(TacticClass::Control));
        assert_eq!(
            class("have x == 1 by { close(); }"),
            Some(TacticClass::Control)
        );
        assert_eq!(class("frobnicate();"), None);
    }

    #[test]
    fn an_elided_form_has_the_search_miss_meaning() {
        assert!(!written_tactic_elides_argument("apply(t(x));"));
        assert!(!written_tactic_elides_argument("apply(fact);"));
        assert!(written_tactic_elides_argument("transport(p, q);"));
        assert!(!written_tactic_elides_argument(
            "apply(a == b implies c == d) using { a == b; };"
        ));
        assert!(!written_tactic_elides_argument("close();"));
        assert!(!written_tactic_elides_argument("close();"));
        assert!(!written_tactic_elides_argument(
            "close() using { a == b; };"
        ));
        let apply = lookup("apply").unwrap();
        assert!(apply.contains("- `apply(fact)`: simple;"), "{apply}");
        let close = lookup("close").unwrap();
        assert!(
            close.contains("- `close() using { P; ... }`: smart;"),
            "{close}"
        );
        assert!(!close.contains(SEARCH_MISS_MEANING), "{close}");
    }

    #[test]
    fn the_index_lists_tactics_then_topics() {
        let index = index();
        let tactics = index.find("tactics:").unwrap();
        let topics = index.find("topics:").unwrap();
        assert!(tactics < topics);
        assert!(index[tactics..topics].contains("  normalize "), "{index}");
        assert!(index[topics..].contains("  tracing "), "{index}");
        assert!(index[topics..].contains("  cli/audit "), "{index}");
    }
}
