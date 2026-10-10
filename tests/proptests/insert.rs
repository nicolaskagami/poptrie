//! Proptests for insertions
//!
//! Property:
//! - Bulk insertion matches manual insertion

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
        for ((key, len), value) in entries.iter().cloned() {
            manually_inserted.insert((key, len), value);
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

    #[test]
    fn bulk_insert_into_existing_matches_manual_insert(
        seed in prop::collection::vec(((any::<u32>(), 0u8..=32u8), any::<u32>()), 0..50),
        batch in prop::collection::vec(((any::<u32>(), 0u8..=32u8), any::<u32>()), 0..50),
    ) {
        let seed: Vec<((u32, u8), u32)> = seed;
        let batch: Vec<((u32, u8), u32)> = batch;

        let mut manually_inserted = Poptrie::new();
        let mut bulk_inserted = Poptrie::new();

        for ((key, len), value) in seed.iter().cloned() {
            manually_inserted.insert((key, len), value);
            bulk_inserted.insert((key, len), value);
        }
        for ((key, len), value) in batch.iter().cloned() {
            manually_inserted.insert((key, len), value);
        }
        bulk_inserted.extend(batch.iter().cloned());

        prop_assert_eq!(bulk_inserted.len(), manually_inserted.len());

        for ((key, len), _) in seed.iter().chain(batch.iter()) {
            prop_assert_eq!(
                bulk_inserted.get((*key, *len)),
                manually_inserted.get((*key, *len)),
            );
        }
    }
}
