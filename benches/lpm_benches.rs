use std::hint::black_box;

use criterion::{
    BenchmarkId, Criterion, Throughput, criterion_group, criterion_main,
};

use poptrie::Poptrie;
use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha8Rng;

/// Generate realistic prefixes and random associated values
fn generate_prefixes(count: usize, seed: u64) -> Vec<((u32, u8), u32)> {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut prefixes = Vec::with_capacity(count);

    for _ in 0..count {
        let a = rng.random::<u8>();
        let b = rng.random::<u8>();
        let c = rng.random::<u8>();
        let d = rng.random::<u8>();

        // Realistic prefix length distribution (matching real BGP tables)
        // Based on https://bgp.potaroo.net/as2.0/bgp-active.html
        // ~60% /24, ~10% /23, ~10% /22, rest between 16 and 21
        let length = match rng.random_range(0..100) {
            0..60 => 24,
            60..70 => 23,
            70..80 => 22,
            _ => rng.random_range(16..=21),
        };

        let prefix = u32::from_be_bytes([a, b, c, d]);
        let val = rng.random::<u32>();
        prefixes.push(((prefix, length), val));
    }

    prefixes
}

fn generate_lookups(size: usize, seed: u64) -> Vec<u32> {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut lookups = Vec::with_capacity(size);

    for _ in 0..size {
        let a = rng.random::<u8>();
        let b = rng.random::<u8>();
        let c = rng.random::<u8>();
        let d = rng.random::<u8>();

        let prefix = u32::from_be_bytes([a, b, c, d]);
        lookups.push(prefix);
    }

    lookups
}

fn bench_lookup(c: &mut Criterion) {
    let mut group = c.benchmark_group("lookup");

    for size in [1_000, 10_000, 100_000].iter() {
        let prefixes = generate_prefixes(*size, 24);
        let lookups = generate_lookups(*size, 42);

        let poptrie: Poptrie<_, _> = prefixes.into_iter().collect();

        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(
            BenchmarkId::new("poptrie", size),
            &size,
            |b, _| {
                b.iter(|| {
                    for lookup in &lookups {
                        black_box(poptrie.lookup(black_box(*lookup)));
                    }
                })
            },
        );
    }

    group.finish();
}

fn bench_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert");
    for size in [1_000, 10_000, 100_000].iter() {
        let prefixes = generate_prefixes(*size, 99);

        group.throughput(Throughput::Elements(*size as u64));

        // Baseline insertion
        group.bench_with_input(
            BenchmarkId::new("manual", size),
            &prefixes,
            |b, prefixes| {
                b.iter(|| {
                    let mut poptrie = Poptrie::new();
                    for &((prefix, length), val) in prefixes {
                        poptrie.insert(
                            black_box((prefix, length)),
                            black_box(val),
                        );
                    }
                    black_box(poptrie)
                })
            },
        );

        // Bulk insertion
        group.bench_with_input(
            BenchmarkId::new("from_iter", size),
            &prefixes,
            |b, prefixes| {
                b.iter(|| {
                    let poptrie: Poptrie<_, _> =
                        black_box(prefixes.iter().copied().collect());
                    black_box(poptrie)
                })
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_insert, bench_lookup);

criterion_main!(benches);
