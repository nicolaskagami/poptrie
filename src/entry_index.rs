/// Represents an index into the value and prefix tables.
///
/// This is a self-rolled option type to signal a missing value without extra space.
/// We use the highest representable value to signal `None` so we don't have to subtract.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub(crate) struct EntryIndex(u32);

impl EntryIndex {
    pub(crate) const NONE: Self = Self(u32::MAX);

    pub(crate) fn new(index: usize) -> Self {
        debug_assert!(index < u32::MAX as usize);
        Self(index as u32)
    }

    pub(crate) fn is_some(self) -> bool {
        self != Self::NONE
    }

    pub(crate) fn get(self) -> Option<usize> {
        (self.is_some()).then_some(self.0 as usize)
    }

    pub(crate) fn decrement(&mut self) {
        if self.is_some() {
            self.0 -= 1;
        }
    }
}
