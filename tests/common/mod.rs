pub mod reference_model;

pub const STRIDE: u32 = 6;

#[macro_export]
macro_rules! u32_strides {
    ($first:expr $(, $rest:expr)* $(,)?) => {{
        const STRIDE: u32 = $crate::common::STRIDE;

        #[allow(unused_mut)]
        {
            let mut shift: u32 = 32u32 - STRIDE;
            let mut value: u32 = ($first as u32) << shift;

            $(
                shift = shift.saturating_sub(STRIDE);
                value |= ($rest as u32) << shift;
            )*

            value
        }
    }};
}

#[cfg(test)]
#[allow(clippy::unusual_byte_groupings)] // Grouped 6 by 6 because that's the current STRIDE
mod tests {
    #[test]
    fn u32_macro_simple() {
        assert_eq!(u32_strides!(1), u32_strides!(1));
        assert_eq!(u32_strides!(2), 0b000010_000000_000000_000000_000000_00u32);
        assert_eq!(
            u32_strides!(63),
            0b111111_000000_000000_000000_000000_00u32
        );
    }
    #[test]
    fn u32_macro_steps() {
        assert_eq!(
            u32_strides!(1, 2),
            0b000001_000010_000000_000000_000000_00u32
        );
        assert_eq!(
            u32_strides!(1, 2, 3),
            0b000001_000010_000011_000000_000000_00u32
        );
        assert_eq!(
            u32_strides!(0, 1, 0),
            0b000000_000001_000000_000000_000000_00u32
        );
        assert_eq!(u32_strides!(1, 0, 0, 0), u32_strides!(1));
        assert_eq!(
            u32_strides!(63, 63),
            0b111111_111111_000000_000000_000000_00u32
        );
    }

    #[test]
    fn u32_macro_encoding() {
        assert_eq!(
            u32_strides!(0b000010, 2),
            0b000010_000010_000000_000000_000000_00u32
        );

        assert_eq!(
            u32_strides!(0b100000, 2),
            0b100000_000010_000000_000000_000000_00u32
        );
    }

    #[test]
    fn u32_macro_full_stride() {
        assert_eq!(
            u32_strides!(1, 1, 1, 1, 1, 3),
            0b000001_000001_000001_000001_000001_11u32
        );
        assert_eq!(u32_strides!(0, 0, 0, 0, 0, 3), 0b11u32);
    }
}
