//! Validation and source mapping for compiler-preprocessed C output.

use std::{collections::BTreeMap, sync::Arc};

use crate::source::SourcePosition;

#[derive(Clone, Debug)]
struct Segment {
    physical_line: usize,
    source_line: usize,
    filename: Arc<str>,
}

/// A compact mapping from physical preprocessed lines to compiler locations.
#[derive(Clone, Debug, Default)]
pub struct CSourceMap {
    segments: Vec<Segment>,
}

impl CSourceMap {
    /// Decode GCC/Clang line markers, returning the marker-free artifact.
    ///
    /// Recognized markers are replaced by blank lines, so physical line
    /// numbers in diagnostics remain those of the compiler artifact.
    pub fn decode(source: &str) -> Result<(String, Self), String> {
        Self::decode_internal(source, None)
    }

    #[cfg(test)]
    fn decode_with_stats(source: &str, stats: &mut DecodeStats) -> Result<(String, Self), String> {
        Self::decode_internal(source, Some(stats))
    }

    fn decode_internal(
        source: &str,
        #[cfg(test)] mut stats: Option<&mut DecodeStats>,
        #[cfg(not(test))] _stats: Option<()>,
    ) -> Result<(String, Self), String> {
        let mut output = String::with_capacity(source.len());
        let mut segments = Vec::new();
        let mut names = BTreeMap::<String, Arc<str>>::new();
        let mut current: Option<(Arc<str>, usize)> = None;

        for (index, raw_line) in source.split_inclusive('\n').enumerate() {
            #[cfg(test)]
            if let Some(stats) = stats.as_deref_mut() {
                stats.lines += 1;
            }
            let physical_line = index + 1;
            let line = raw_line.strip_suffix('\n').unwrap_or(raw_line);
            let line = line.strip_suffix('\r').unwrap_or(line);
            if line.trim_start().starts_with('#') {
                match parse_marker(line, physical_line)? {
                    Some(marker) => {
                        #[cfg(test)]
                        if let Some(stats) = stats.as_deref_mut() {
                            stats.markers += 1;
                            stats.filename_bytes += marker.filename.len();
                        }
                        let filename = names
                            .entry(marker.filename.clone())
                            .or_insert_with(|| Arc::<str>::from(marker.filename))
                            .clone();
                        if marker.flags_enter && marker.flags_return {
                            return Err(format!(
                                "line marker cannot enter and return simultaneously at physical line {physical_line}"
                            ));
                        }
                        let next_line = physical_line.checked_add(1).ok_or_else(|| {
                            format!("physical line overflow at line {physical_line}")
                        })?;
                        segments.push(Segment {
                            physical_line: next_line,
                            source_line: marker.line,
                            filename: filename.clone(),
                        });
                        current = Some((filename, marker.line));
                        if raw_line.ends_with('\n') {
                            output.push('\n');
                        }
                    }
                    None => {
                        return Err(format!(
                            "unsupported preprocessor directive at physical line {physical_line}: {}",
                            bounded_directive(line)
                        ));
                    }
                }
                continue;
            }

            if let Some((_filename, source_line)) = &mut current {
                *source_line = source_line.checked_add(1).ok_or_else(|| {
                    format!("logical line overflow at physical line {physical_line}")
                })?;
            }
            output.push_str(raw_line);
        }

        Ok((output, Self { segments }))
    }

    /// Map a physical source position to its compiler source location.
    pub fn lookup(&self, position: SourcePosition) -> SourcePosition {
        self.lookup_counted(position, || {})
    }

    #[cfg(test)]
    fn lookup_with_comparisons(
        &self,
        position: SourcePosition,
        comparisons: &mut usize,
    ) -> SourcePosition {
        self.lookup_counted(position, || *comparisons += 1)
    }

    fn lookup_counted(
        &self,
        position: SourcePosition,
        mut comparison: impl FnMut(),
    ) -> SourcePosition {
        let index = self.segments.partition_point(|segment| {
            comparison();
            segment.physical_line <= position.line
        });
        let Some(segment) = index.checked_sub(1).and_then(|i| self.segments.get(i)) else {
            return position;
        };
        let line = segment
            .source_line
            .checked_add(position.line.saturating_sub(segment.physical_line))
            .unwrap_or(segment.source_line);
        SourcePosition::with_origin(
            position.line,
            position.column,
            segment.filename.clone(),
            line,
        )
    }
}

fn bounded_directive(line: &str) -> String {
    const LIMIT: usize = 120;
    if line.chars().count() <= LIMIT {
        return line.to_owned();
    }
    let mut prefix = line.chars().take(LIMIT).collect::<String>();
    prefix.push('…');
    prefix
}

#[cfg(test)]
#[derive(Default)]
struct DecodeStats {
    lines: usize,
    markers: usize,
    filename_bytes: usize,
}

#[derive(Debug)]
struct Marker {
    line: usize,
    filename: String,
    flags_enter: bool,
    flags_return: bool,
}

fn parse_marker(line: &str, physical_line: usize) -> Result<Option<Marker>, String> {
    let mut rest = line.trim_start();
    if !rest.starts_with('#') {
        return Ok(None);
    }
    rest = rest[1..].trim_start();
    let digits_len = rest.bytes().take_while(u8::is_ascii_digit).count();
    if digits_len == 0 {
        return Ok(None);
    }
    let number = rest[..digits_len]
        .parse::<usize>()
        .map_err(|_| format!("invalid line marker number at physical line {physical_line}"))?;
    rest = rest[digits_len..].trim_start();
    if !rest.starts_with('"') {
        return Err(format!(
            "line marker at physical line {physical_line} has no quoted filename"
        ));
    }
    let (filename, consumed) = parse_quoted_filename(&rest[1..], physical_line)?;
    rest = rest[1 + consumed..].trim_start();
    let mut flags = [false; 5];
    while !rest.is_empty() {
        let count = rest.bytes().take_while(u8::is_ascii_digit).count();
        if count == 0 {
            return Err(format!(
                "invalid trailing text in line marker at physical line {physical_line}"
            ));
        }
        let flag = rest[..count].parse::<usize>().unwrap_or(usize::MAX);
        if !(1..=4).contains(&flag) || flags[flag] {
            return Err(format!(
                "invalid or duplicate line marker flag at physical line {physical_line}"
            ));
        }
        flags[flag] = true;
        rest = rest[count..].trim_start();
    }
    if filename.is_empty() {
        return Err(format!(
            "empty filename in line marker at physical line {physical_line}"
        ));
    }
    Ok(Some(Marker {
        line: number,
        filename,
        flags_enter: flags[1],
        flags_return: flags[2],
    }))
}

fn parse_quoted_filename(input: &str, physical_line: usize) -> Result<(String, usize), String> {
    let chars: Vec<char> = input.chars().collect();
    let mut result = String::new();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            '"' => {
                let consumed = input
                    .char_indices()
                    .nth(i)
                    .map_or(input.len(), |(byte, _)| byte + 1);
                return Ok((result, consumed));
            }
            '\\' => {
                i += 1;
                if i == chars.len() {
                    break;
                }
                match chars[i] {
                    'a' => result.push('\x07'),
                    'b' => result.push('\x08'),
                    'f' => result.push('\x0c'),
                    'n' => result.push('\n'),
                    'r' => result.push('\r'),
                    't' => result.push('\t'),
                    'v' => result.push('\x0b'),
                    '\\' | '"' | '?' => result.push(chars[i]),
                    'x' => {
                        i += 1;
                        let start = i;
                        while i < chars.len() && chars[i].is_ascii_hexdigit() {
                            i += 1;
                        }
                        if start == i {
                            return Err(format!(
                                "empty hex escape in filename at physical line {physical_line}"
                            ));
                        }
                        let value = chars[start..i].iter().collect::<String>();
                        let byte = u8::from_str_radix(&value, 16).map_err(|_| {
                            format!(
                                "invalid hex escape in filename at physical line {physical_line}"
                            )
                        })?;
                        if byte >= 0x80 {
                            return Err(format!(
                                "non-UTF-8 escaped byte in filename at physical line {physical_line}"
                            ));
                        }
                        result.push(byte as char);
                        continue;
                    }
                    c if ('0'..='7').contains(&c) => {
                        let start = i;
                        while i + 1 < chars.len()
                            && i - start < 2
                            && ('0'..='7').contains(&chars[i + 1])
                        {
                            i += 1;
                        }
                        let value = chars[start..=i].iter().collect::<String>();
                        let byte = u8::from_str_radix(&value, 8).map_err(|_| {
                            format!(
                                "invalid octal escape in filename at physical line {physical_line}"
                            )
                        })?;
                        if byte >= 0x80 {
                            return Err(format!(
                                "non-UTF-8 escaped byte in filename at physical line {physical_line}"
                            ));
                        }
                        result.push(byte as char);
                    }
                    _ => {
                        return Err(format!(
                            "invalid escape in filename at physical line {physical_line}"
                        ));
                    }
                }
            }
            c => result.push(c),
        }
        i += 1;
    }
    Err(format!(
        "unterminated filename in line marker at physical line {physical_line}"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_nested_markers_and_escapes() {
        let (clean, map) =
            CSourceMap::decode("# 1 \"main\\\\file.c\"\nint a;\n# 8 \"h\\\".h\" 1 3\nint b;\n")
                .unwrap();
        assert_eq!(clean, "\nint a;\n\nint b;\n");
        assert_eq!(
            map.lookup(SourcePosition::new(2, 1)).to_string(),
            "main\\file.c:1"
        );
        assert_eq!(map.lookup(SourcePosition::new(4, 1)).to_string(), "h\".h:8");
        let (_, unicode_map) = CSourceMap::decode("# 1 \"h☃.h\"\nint x;\n").unwrap();
        assert_eq!(
            unicode_map.lookup(SourcePosition::new(2, 1)).to_string(),
            "h☃.h:1"
        );
    }

    #[test]
    fn rejects_residual_directives_and_bad_flags() {
        for input in [
            "#pragma once\n",
            "# 1 \"x\" 9\n",
            "# 1 x\n",
            "# 1 \"x\" 1 2\n",
            "# 1 \"x\\303\\251\"\n",
        ] {
            assert!(CSourceMap::decode(input).is_err(), "{input:?}");
        }
    }

    #[test]
    fn accepts_real_file_zero_marker_and_rejects_logical_overflow() {
        let (clean, map) = CSourceMap::decode("# 0 \"main.c\"\nint32 x;\n").unwrap();
        assert_eq!(clean, "\nint32 x;\n");
        assert_eq!(
            map.lookup(SourcePosition::new(2, 1)).origin.unwrap().line,
            0
        );
        let overflow = format!("# {} \"x\"\nline\n", usize::MAX);
        assert!(CSourceMap::decode(&overflow).is_err());
        let huge = format!("#pragma {}\n", "x".repeat(32 * 1024 * 1024));
        let error = CSourceMap::decode(&huge).unwrap_err();
        assert!(error.len() < 512);
    }

    #[test]
    fn decode_and_lookup_scale_across_four_input_sizes() {
        let mut previous_lines = 0;
        let mut previous_comparisons = 0;
        for size in [16usize, 32, 64, 128] {
            let mut input = String::new();
            for marker in 0..size {
                input.push_str(&format!("# 1 \"header{marker}.h\" 1\nint32 value;\n"));
            }
            let mut stats = DecodeStats::default();
            let (clean, map) = CSourceMap::decode_with_stats(&input, &mut stats).unwrap();
            assert_eq!(clean.lines().count(), size * 2);
            assert_eq!(stats.lines, size * 2);
            assert_eq!(stats.markers, size);
            assert!(stats.filename_bytes >= size * "header".len());
            assert_eq!(map.segments.len(), size);
            let mut comparisons = 0;
            for line in 1..=clean.lines().count() {
                let _ = map.lookup_with_comparisons(SourcePosition::new(line, 1), &mut comparisons);
            }
            assert!(comparisons <= clean.lines().count() * (size.ilog2() as usize + 2));
            assert!(stats.lines >= previous_lines * 2 || previous_lines == 0);
            assert!(comparisons >= previous_comparisons);
            previous_lines = stats.lines;
            previous_comparisons = comparisons;
        }
    }
}
