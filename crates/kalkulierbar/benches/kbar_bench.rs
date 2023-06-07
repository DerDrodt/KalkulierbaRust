use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use kalkulierbar::{logic::transform::fo_cnf::fo_cnf, parse::fo::parse_fo_formula, session};

pub fn fo_parser(c: &mut Criterion) {
    let small = r"\all X: (P(X) | Q(X)) -> \all X: P(X) | \all X: Q(X)";
    let medium = r"\all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt)";
    let large = r"\all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) -> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) -> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) <-> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) | \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) <-> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) & \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) -> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt)";
    let mut g = c.benchmark_group("FO Parser");
    g.bench_with_input(BenchmarkId::new("FO Parser", "small"), &small, |b, &f| {
        b.iter(|| {
            session(|| {
                let n = parse_fo_formula(f).unwrap();
                black_box(n)
            })
        })
    });
    g.bench_with_input(BenchmarkId::new("FO Parser", "medium"), &medium, |b, &f| {
        b.iter(|| {
            session(|| {
                let n = parse_fo_formula(f).unwrap();
                black_box(n)
            })
        })
    });

    g.bench_with_input(BenchmarkId::new("FO Parser", "large"), &large, |b, &f| {
        b.iter(|| {
            session(|| {
                let n = parse_fo_formula(f).unwrap();
                black_box(n)
            })
        })
    });
    g.finish();
}

pub fn b_fo_cnf(c: &mut Criterion) {
    let small = r"\all X: (P(X) | Q(X)) -> \all X: P(X) | \all X: Q(X)";
    let medium = r"\all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt)";
    let large = r"\all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) -> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) -> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt) <-> \all Here: \all There: ((Reachable(Here) & Connected(Here, There)) -> Reachable(There)) &
\all A: \all B: (Connected(A, B) -> Connected(B, A)) &
Connected(shanghai, hongkong) & Connected(hongkong, singapore) & Connected(frankfurt, hongkong) & Connected(frankfurt, darmstadt) &
Reachable(shanghai) &
!Reachable(darmstadt)";

    let mut g = c.benchmark_group("FO CNF");
    g.bench_with_input(BenchmarkId::new("FO CNF", "small"), &small, |b, &f| {
        session(|| {
            let n = parse_fo_formula(f).unwrap();
            b.iter(|| {
                let cs = fo_cnf(n.clone()).unwrap();
                black_box(cs)
            })
        })
    });
    g.bench_with_input(BenchmarkId::new("FO CNF", "medium"), &medium, |b, &f| {
        session(|| {
            let n = parse_fo_formula(f).unwrap();
            b.iter(|| {
                let cs = fo_cnf(n.clone()).unwrap();
                black_box(cs)
            })
        })
    });

    g.bench_with_input(BenchmarkId::new("FO CNF", "large"), &large, |b, &f| {
        session(|| {
            let n = parse_fo_formula(f).unwrap();
            b.iter(|| {
                let cs = fo_cnf(n.clone()).unwrap();
                black_box(cs)
            })
        })
    });
}

criterion_group!(benches, fo_parser, b_fo_cnf);
criterion_main!(benches);
