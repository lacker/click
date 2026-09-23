//! Opt-in, bounded observations of checked proof steps for CLI diagnostics.
//! The trace is diagnostic only; no recorded text participates in checking.

use std::cell::RefCell;
use std::collections::HashMap;

const MAX_STEPS: usize = 2048;
const MAX_RENDER_BYTES: usize = 64 * 1024;

struct Capture {
    function: String,
    steps: HashMap<usize, String>,
    limit_reached: bool,
}

thread_local! {
    static CAPTURE: RefCell<Option<Capture>> = const { RefCell::new(None) };
}

/// Scope tracing to one named function on the verification thread.
pub fn with_proof_trace<R>(function: &str, verify: impl FnOnce() -> R) -> R {
    struct Restore(Option<Capture>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CAPTURE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let prior = CAPTURE.with(|slot| {
        slot.replace(Some(Capture {
            function: function.to_owned(),
            steps: HashMap::new(),
            limit_reached: false,
        }))
    });
    let _restore = Restore(prior);
    verify()
}

pub(super) fn enabled_for(claim: &str) -> bool {
    CAPTURE.with(|slot| {
        slot.borrow().as_ref().is_some_and(|capture| {
            claim
                .strip_prefix(&capture.function)
                .is_some_and(|tail| tail.starts_with('.') || tail.is_empty())
        })
    })
}

pub(super) fn record(node: usize, description: String) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.steps.len() < MAX_STEPS {
            capture.steps.insert(node, description);
        } else {
            capture.limit_reached = true;
        }
    });
}

/// Render only nodes on the failing proof's lineage. Discarded smart-search
/// candidates may have been checked but never appear on this path.
pub(super) fn render(claim: &str, lineage: &[usize]) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        if !enabled_for(claim) {
            return None;
        }
        let mut output = String::from("  proof trace (checked steps on the failing path):");
        let mut shown = 0;
        for node in lineage {
            let Some(step) = capture.steps.get(node) else {
                continue;
            };
            if output.len() + step.len() > MAX_RENDER_BYTES {
                output.push_str("\n    … <trace output limit reached>");
                break;
            }
            output.push_str(step);
            shown += 1;
        }
        if shown == 0 {
            output.push_str("\n    <no checked simple steps recorded on this path>");
        }
        if capture.limit_reached {
            output.push_str("\n    … <trace step limit reached; later steps omitted>");
        }
        Some(output)
    })
}
