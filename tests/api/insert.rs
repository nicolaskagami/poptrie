use crate::u32_strides;
use poptrie::Poptrie;

#[test]
fn insert_returns_old_value() {
    let mut trie = Poptrie::new();
    assert_eq!(trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 1u32), None);
    assert_eq!(
        trie.insert((u32::from_be_bytes([10, 0, 0, 0]), 8), 2u32),
        Some(1)
    );
    assert_eq!(trie.lookup(u32::from_be_bytes([10, 0, 1, 1])), Some(&2));
}

#[test]
fn insert_order_does_not_affect_lpm() {
    let mut forward = Poptrie::new();
    forward.insert((u32_strides!(1), 6), 6);
    forward.insert((u32_strides!(1, 1), 12), 12);
    forward.insert((u32_strides!(1, 1, 1), 18), 18);

    let mut reverse = Poptrie::new();
    reverse.insert((u32_strides!(1, 1, 1), 18), 18);
    reverse.insert((u32_strides!(1, 1), 12), 12);
    reverse.insert((u32_strides!(1), 6), 6);

    let lookups = [
        u32_strides!(1, 1),
        u32_strides!(1, 0),
        u32_strides!(0, 1),
        u32_strides!(1, 1, 1),
        0,
    ];

    for addr in lookups {
        assert_eq!(forward.lookup(addr), reverse.lookup(addr),);
    }
}
