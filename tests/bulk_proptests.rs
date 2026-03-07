use poptrie::Poptrie;
use proptest::prelude::*;

proptest! {
    #[test]
    fn bulk_insertion_matches_manual_insertion(
        entries in prop::collection::vec(
            ((any::<u32>(), 0u8..=32u8), any::<u32>()),
            0..100,
        )
    ) {
        let entries: Vec<((u32, u8), u32)> = entries
            .into_iter()
            .collect();

        let mut manually_inserted = Poptrie::new();
        for (prefix, value) in entries.iter().cloned() {
            manually_inserted.insert(prefix, value);
        }

        let bulk_inserted: Poptrie<_,_> = entries.iter().cloned().collect();

        // Manual and bulk insertion should yield the same
        for ((key, _), _) in &entries {
            for probe_len in 0u8..=32 {
                let mask = if probe_len == 0 { 0u32 } else { u32::MAX << (32 - probe_len) };
                let probe = key & mask;
                prop_assert_eq!(
                    manually_inserted.lookup(probe),
                    bulk_inserted.lookup(probe),
                    "mismatch for probe {:?}/{}", u32::to_be_bytes(probe), probe_len
                );
            }
        }
    }
}
