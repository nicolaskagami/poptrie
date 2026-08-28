/// An index into the value and prefix tables.
///
/// The inner value is never `u32::MAX`, which [`LeafSlot`] reserves as its
/// empty sentinel.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct EntryIndex(u32);

impl EntryIndex {
    pub(crate) fn new(index: usize) -> Self {
        debug_assert!(index < u32::MAX as usize);
        Self(index as u32)
    }

    #[inline(always)]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) fn decrement_if_above(&mut self, removed: EntryIndex) {
        if *self > removed {
            self.0 -= 1;
        }
    }
}

/// A possibly empty slot for an `EntryIndex` in the leaves table.
/// This is a self-rolled option type to signal a missing value without extra space.
/// We use the highest representable value to signal `None` so we don't have to subtract.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LeafSlot(u32);

impl LeafSlot {
    pub(crate) const EMPTY: Self = Self(u32::MAX);

    #[inline(always)]
    pub(crate) fn occupied(entry: EntryIndex) -> Self {
        Self(entry.0)
    }

    #[inline(always)]
    pub(crate) fn get(self) -> Option<EntryIndex> {
        (self != Self::EMPTY).then_some(EntryIndex(self.0))
    }

    pub(crate) fn decrement_if_above(&mut self, removed: EntryIndex) {
        if self.0 != u32::MAX && self.0 > removed.0 {
            self.0 -= 1;
        }
    }
}
