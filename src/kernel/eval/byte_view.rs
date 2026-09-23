//! The byte view of integer cells.
//!
//! Memory keeps typed cells, not bytes. A one-byte C access that lands inside
//! a wider integer cell, rather than on a cell of its own, still has a defined
//! meaning once the target's byte order is known: under little-endian order,
//! byte `k` of an integer object holds bits `8k .. 8k + 8` of its value. This
//! module is the only place that meaning is written down.
//!
//! The view is deliberately narrow:
//!
//! - only a C execution access of width one, at a constant offset, inside an
//!   integer cell at a constant offset of the same block;
//! - only under [`ByteOrder::Little`] installed from the execution
//!   environment; with no installed order, or under `Big`, there is no view;
//! - never for a pointer, float, or `_Bool` cell. A pointer's bytes are
//!   opaque, which is what keeps a pointer rebuilt from bytes refused.
//!
//! The containing cell is found with a bounded range query over the at most
//! seven constant offsets below the access in its own block, so the lookup
//! does work independent of every other cell in memory.

use super::*;

/// The widest integer cell, in bytes. A containing cell starts at most this
/// many bytes minus one below the accessed byte.
const WIDEST_INTEGER_CELL_BYTES: i64 = 8;

/// An integer cell that contains a one-byte access without starting at it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ContainingIntegerCell {
    /// The cell's own address, `(block, const o')`.
    pub(in crate::kernel) pointer: Pointer,
    /// The cell's value, an integer variant wider than one byte.
    pub(in crate::kernel) value: CValue,
    /// Which byte of the cell's representation the access names, `o - o'`.
    pub(in crate::kernel) byte: u32,
}

/// The byte width of an integer cell, or `None` for a cell with no byte view.
fn integer_cell_width(value: &CValue) -> Option<u32> {
    match value {
        CValue::Int8(_) | CValue::UInt8(_) => Some(1),
        CValue::Int16(_) | CValue::UInt16(_) => Some(2),
        CValue::Int32(_) | CValue::UInt32(_) => Some(4),
        CValue::Int64(_) | CValue::UInt64(_) => Some(8),
        CValue::Void
        | CValue::Bool(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

/// The integer cell that contains the byte at `pointer`, when the byte order
/// gives it a byte view.
///
/// The containing cell starts at `(block, const o')` with
/// `o' <= o < o' + w` and `w > 1`. Returns `None` for any order other than an
/// installed little-endian one, a symbolic offset, a one-byte cell at
/// `pointer` (that cell, not a byte view, is what the access names), no
/// overlapping cell, or an overlapping cell with no byte view (pointer,
/// float, `_Bool`).
pub(in crate::kernel) fn containing_integer_cell(
    memory: &CMemory,
    pointer: &Pointer,
    byte_order: Option<ByteOrder>,
) -> Option<ContainingIntegerCell> {
    if byte_order != Some(ByteOrder::Little) {
        return None;
    }
    let PointerOffsetTerm::Constant(offset) = pointer.offset else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(1);
    // A cell at the access's own address is the containing cell when it is
    // a wider integer (byte 0). A one-byte cell there is the access's own
    // cell, which the exact rules read and write; a cell with no byte view
    // is refused.
    if let Some(value) = memory.cells.get(pointer) {
        return (integer_cell_width(value)? > 1).then(|| ContainingIntegerCell {
            pointer: pointer.clone(),
            value: value.clone(),
            byte: 0,
        });
    }
    let lowest = offset.checked_sub(WIDEST_INTEGER_CELL_BYTES - 1)?;
    let start = Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::Constant(lowest),
    };
    // Constant offsets order before every other offset form and among
    // themselves by value, so this range is exactly the cells of this block
    // at constant offsets `lowest .. offset`: at most seven entries.
    for (cell_pointer, value) in memory.cells.range(start..pointer.clone()).rev() {
        crate::instrumentation::record_deterministic_work(1);
        let PointerOffsetTerm::Constant(cell_offset) = cell_pointer.offset else {
            continue;
        };
        let reach = match integer_cell_width(value) {
            Some(width) => i64::from(width),
            None => i64::from(crate::kernel::reasoning::cell_access_byte_width(value)),
        };
        if cell_offset + reach <= offset {
            continue;
        }
        // The nearest overlapping cell decides. A cell without a byte view
        // refuses the access rather than letting a farther cell answer.
        integer_cell_width(value)?;
        return Some(ContainingIntegerCell {
            pointer: cell_pointer.clone(),
            value: value.clone(),
            byte: u32::try_from(offset - cell_offset).ok()?,
        });
    }
    None
}

/// Byte `byte` of an integer cell's little-endian representation, as the
/// zero-extended 32-bit term of an `unsigned char`: `(v >> 8k) & 0xFF`.
pub(in crate::kernel) fn integer_cell_byte(value: &CValue, byte: u32) -> Option<Bitvector32Term> {
    let width = integer_cell_width(value)?;
    if byte >= width {
        return None;
    }
    let shift = 8 * byte;
    Some(match value {
        CValue::Int16(term) | CValue::UInt16(term) | CValue::Int32(term) | CValue::UInt32(term) => {
            // A 16-bit value's 32-bit term is its sign or zero extension, so
            // its low sixteen bits are its representation either way.
            Bitvector32Term::bitwise_and(
                Bitvector32Term::logical_shift_right(
                    term.clone(),
                    Bitvector32Term::Constant(shift),
                ),
                Bitvector32Term::Constant(0xFF),
            )
        }
        CValue::Int64(term) | CValue::UInt64(term) => {
            let bits = match value {
                CValue::Int64(_) => Bitvector32Term::uint64_from_int64(term.clone()),
                _ => term.clone(),
            };
            Bitvector32Term::uint32_from_64(Bitvector32Term::uint64_bitwise_and(
                Bitvector32Term::uint64_logical_shift_right(
                    bits,
                    Bitvector32Term::UInt64Constant(u64::from(shift)),
                ),
                Bitvector32Term::UInt64Constant(0xFF),
            ))
        }
        _ => return None,
    })
}

/// The value a one-byte load of `value_type` reads from byte `byte` of an
/// integer cell. An `unsigned char` reads the byte; a `signed char` reads its
/// sign extension, which is decided here only for a constant byte. A
/// symbolic signed byte has no sign-extension term to use, so it is refused.
pub(in crate::kernel) fn byte_view_load_value(
    cell: &ContainingIntegerCell,
    value_type: CType,
) -> Option<CValue> {
    let byte = integer_cell_byte(&cell.value, cell.byte)?;
    match value_type {
        CType::UInt8 => Some(CValue::UInt8(byte)),
        CType::Int8 => byte
            .as_const()
            .map(|byte| CValue::Int8(Bitvector32Term::Constant(byte as u8 as i8 as i32 as u32))),
        _ => None,
    }
}

/// The integer cell `cell` after a one-byte store of `stored` at its byte
/// `cell.byte`, under little-endian order:
/// `(v & !(0xFF << 8k)) | (zext(b) << 8k)`, in the cell's own variant.
///
/// An `int16_t` or `int64_t` cell is updated only when both the cell and the
/// byte are constants: its term would otherwise need a sign extension (16-bit)
/// or a signed shift into the sign bit (64-bit) that no term operation states.
/// `None` leaves the store to forget the cell, as it did before this view.
pub(in crate::kernel) fn integer_cell_with_byte(
    cell: &ContainingIntegerCell,
    stored: &CValue,
) -> Option<CValue> {
    let width = integer_cell_width(&cell.value)?;
    if width <= 1 || cell.byte >= width {
        return None;
    }
    let byte = match stored {
        CValue::UInt8(term) => term.clone(),
        CValue::Int8(term) => {
            Bitvector32Term::bitwise_and(term.clone(), Bitvector32Term::Constant(0xFF))
        }
        _ => return None,
    };
    let shift = 8 * cell.byte;
    // `byte < width <= 8`, so the 64-bit shift is in range; the 32-bit mask
    // is only used by cells of at most four bytes, where it is too.
    let mask32 = !0xFFu32.checked_shl(shift).unwrap_or(0);
    let mask64 = !(0xFFu64 << shift);
    let update32 = |term: &Bitvector32Term| {
        Bitvector32Term::bitwise_or(
            Bitvector32Term::bitwise_and(term.clone(), Bitvector32Term::Constant(mask32)),
            Bitvector32Term::unsigned_shift_left(byte.clone(), Bitvector32Term::Constant(shift)),
        )
    };
    Some(match &cell.value {
        CValue::UInt16(term) => CValue::UInt16(update32(term)),
        CValue::Int32(term) => CValue::Int32(update32(term)),
        CValue::UInt32(term) => CValue::UInt32(update32(term)),
        CValue::UInt64(term) => CValue::UInt64(Bitvector32Term::uint64_bitwise_or(
            Bitvector32Term::uint64_bitwise_and(
                term.clone(),
                Bitvector32Term::UInt64Constant(mask64),
            ),
            Bitvector32Term::uint64_shift_left(
                Bitvector32Term::uint64_from_32(byte),
                Bitvector32Term::UInt64Constant(u64::from(shift)),
            ),
        )),
        CValue::Int16(term) => {
            let (value, byte) = (term.as_const()?, byte.as_const()?);
            let bits = (value & 0xFFFF & mask32) | ((byte & 0xFF) << shift);
            CValue::Int16(Bitvector32Term::Constant(bits as u16 as i16 as i32 as u32))
        }
        CValue::Int64(term) => {
            let (value, byte) = (term.int64_as_const()?, byte.as_const()?);
            let bits = (value as u64 & mask64) | (u64::from(byte & 0xFF) << shift);
            CValue::Int64(Bitvector32Term::Int64Constant(bits as i64))
        }
        _ => return None,
    })
}
