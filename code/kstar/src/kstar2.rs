// the accompanying code  SECOND, independent exact engine for Theorem K*.
// Independent of kstar.rs: ML is decided by exact ARC-COVER tests (no candidate-time enumeration):
//   ML(V) <= c  <=>  the CLOSED arcs {t : ||v t|| <= c}, v in V, cover R/Z
//   ML(V) >= c  <=>  the OPEN   arcs {t : ||v t|| <  c}, v in V, do NOT cover R/Z
// L = ML(B) is found by binary search over {a/d : d <= 2 max B}; equality times = points not covered by the open arcs at c = L.
// L2, and a cross-check of L and of the equality times, come from a second route: local maxima at t = k/(u+v).
// All arithmetic exact (i128 fractions).  No floating point.  Memory O(arcs) < 5 MB.
use std::cmp::Ordering;
use std::collections::BTreeSet;
type I = i128;
fn gcd(a: I, b: I) -> I { if b == 0 { a.abs() } else { gcd(b, a % b) } }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Fr { n: I, d: I } // reduced, d > 0
impl Fr {
    fn new(n: I, d: I) -> Fr { let g = gcd(n, d).max(1); let s = if d < 0 { -1 } else { 1 }; Fr { n: s * n / g, d: s * d / g } }
    fn zero() -> Fr { Fr { n: 0, d: 1 } }
}
impl PartialOrd for Fr { fn partial_cmp(&self, o: &Fr) -> Option<Ordering> { Some(self.cmp(o)) } }
impl Ord for Fr { fn cmp(&self, o: &Fr) -> Ordering { (self.n * o.d).cmp(&(o.n * self.d)) } }
// raw (unreduced) fractions for arcs
type R = (I, I);
fn rlt(a: R, b: R) -> bool { a.0 * b.1 < b.0 * a.1 }
fn rle(a: R, b: R) -> bool { a.0 * b.1 <= b.0 * a.1 }
fn arcs(vs: &[I], c: Fr) -> Vec<(R, R)> {
    let mut a = Vec::new();
    for &v in vs { for j in 0..=v { a.push(((j * c.d - c.n, v * c.d), (j * c.d + c.n, v * c.d))); } }
    a.sort_by(|x, y| (x.0 .0 * y.0 .1).cmp(&(y.0 .0 * x.0 .1)));
    a
}
// do the OPEN arcs {||vt|| < c} cover the circle?
fn open_cover(vs: &[I], c: Fr) -> bool {
    let a = arcs(vs, c);
    let mut x: R = (0, 1); let mut i = 0; let mut best: Option<R> = None;
    loop {
        while i < a.len() && rlt(a[i].0, x) { if best.map_or(true, |b| rlt(b, a[i].1)) { best = Some(a[i].1); } i += 1; }
        match best { None => return false, Some(b) => { if !rlt(x, b) { return false; } x = b; if !rlt(x, (1, 1)) { return true; } } }
    }
}
// do the CLOSED arcs {||vt|| <= c} cover the circle?
fn closed_cover(vs: &[I], c: Fr) -> bool {
    let a = arcs(vs, c);
    let mut r: R = (0, 1); let mut i = 0; let mut best: Option<R> = None;
    loop {
        while i < a.len() && rle(a[i].0, r) { if best.map_or(true, |b| rlt(b, a[i].1)) { best = Some(a[i].1); } i += 1; }
        match best { None => return false, Some(b) => { if !rlt(r, b) { return !rlt(r, (1, 1)); } r = b; if !rlt(r, (1, 1)) { return true; } } }
    }
}
fn ml_ge(vs: &[I], c: Fr) -> bool { !open_cover(vs, c) }
fn ml_le(vs: &[I], c: Fr) -> bool { closed_cover(vs, c) }
// exact ML by binary search over candidate values a/d, d <= 2 max
fn ml_cover(vs: &[I]) -> Fr {
    let mx = *vs.iter().max().unwrap();
    let mut cand: BTreeSet<Fr> = BTreeSet::new();
    for d in 1..=2 * mx { for a in 1..=d / 2 { cand.insert(Fr::new(a, d)); } }
    let cv: Vec<Fr> = cand.into_iter().collect();
    let (mut lo, mut hi) = (0usize, cv.len() - 1);
    assert!(ml_ge(vs, cv[0]));
    while lo < hi { let mid = (lo + hi + 1) / 2; if ml_ge(vs, cv[mid]) { lo = mid; } else { hi = mid - 1; } }
    let l = cv[lo];
    assert!(ml_le(vs, l), "cover-route ML inconsistent");
    l
}
// points of R/Z not covered by the open arcs at c  (= {t : f(t) >= c})
fn uncovered(vs: &[I], c: Fr) -> (Vec<Fr>, bool) {
    let a = arcs(vs, c);
    let mut pts = Vec::new(); let mut gap = false;
    let mut x: R = (0, 1); let mut i = 0; let mut best: Option<R> = None;
    loop {
        while i < a.len() && rlt(a[i].0, x) { if best.map_or(true, |b| rlt(b, a[i].1)) { best = Some(a[i].1); } i += 1; }
        let covered = match best { Some(b) => rlt(x, b), None => false };
        if covered { x = best.unwrap(); if !rlt(x, (1, 1)) { break; } continue; }
        if !rlt(x, (1, 1)) { break; }
        pts.push(Fr::new(x.0, x.1));
        while i < a.len() && rle(a[i].0, x) { if best.map_or(true, |b| rlt(b, a[i].1)) { best = Some(a[i].1); } i += 1; }
        match best {
            Some(b) if rlt(x, b) => { x = b; if !rlt(x, (1, 1)) { break; } }
            _ => { gap = true; if i < a.len() { x = a[i].0; } else { break; } }
        }
    }
    (pts, gap)
}
// second route: local maxima of f_V at t = k/(u+v) (u != v in V).  returns set of (time, value)
fn local_max(vs: &[I]) -> BTreeSet<(Fr, Fr)> {
    let mut out = BTreeSet::new();
    let u: Vec<I> = { let s: BTreeSet<I> = vs.iter().cloned().collect(); s.into_iter().collect() };
    for i in 0..u.len() { for j in i + 1..u.len() {
        let d = u[i] + u[j];
        for k in 1..d {
            let (mut m, mut inc, mut dec) = (I::MAX, false, false);
            let mut zero = false;
            for &x in &u {
                let r = (x * k) % d; let s = if 2 * r > d { r - d } else { r }; let a = s.abs();
                if a == 0 { zero = true; break; }
                if a < m { m = a; inc = s > 0; dec = s < 0; } else if a == m { if s > 0 { inc = true; } else { dec = true; } }
            }
            if zero || 2 * m == d { continue; }
            if inc && dec { out.insert((Fr::new(k, d), Fr::new(m, d))); }
        }
    } }
    out
}
struct Prof { l: Fr, l2: Fr, eq: Vec<Fr>, dd: I, vmu: I, dstar: I, rho_lam: Vec<(Fr, I, I)> }
// profile of base B via the cover route (L, eq times, D, v_mu) cross-checked against the local-max route (L, eq times, L2)
fn profile(b: &[I]) -> Result<Prof, String> {
    let l = ml_cover(b);
    if 2 * l.n >= l.d { return Err("L=1/2".into()); }
    let (eq, gap) = uncovered(b, l);
    if gap || eq.is_empty() { return Err(format!("eq-times enumeration failed gap={} n={}", gap, eq.len())); }
    let lm = local_max(b);
    let l_lm = lm.iter().map(|x| x.1).max().unwrap();
    if l_lm != l { return Err(format!("TENSION L cover={}/{} lm={}/{}", l.n, l.d, l_lm.n, l_lm.d)); }
    let eq_lm: BTreeSet<Fr> = lm.iter().filter(|x| x.1 == l).map(|x| x.0).collect();
    let eq_c: BTreeSet<Fr> = eq.iter().cloned().collect();
    if eq_lm != eq_c { return Err("TENSION equality times differ between routes".into()); }
    let l2 = lm.iter().map(|x| x.1).filter(|v| *v < l).max().unwrap_or(Fr::zero());
    let mut dd: I = 1; let mut vmu = I::MAX; let mut dstar: I = 0; let mut rl = Vec::new();
    for t in &eq {
        dd = dd / gcd(dd, t.d) * t.d;
        let (mut rho, mut lam) = (0, 0); let mut fmin = I::MAX;
        for &x in b {
            let r = (x * t.n) % t.d; let s = if 2 * r > t.d { r - t.d } else { r };
            fmin = fmin.min(s.abs());
            if s * l.d == l.n * t.d { rho = rho.max(x); }
            if -s * l.d == l.n * t.d { lam = lam.max(x); }
        }
        if Fr::new(fmin, t.d) != l { return Err("f(t_j) != L".into()); }
        if rho == 0 || lam == 0 { return Err("missing increasing/decreasing runner at eq time".into()); }
        let mn = rho.min(lam); if mn < vmu || (mn == vmu && t.d < dstar) { vmu = mn; dstar = t.d; } rl.push((*t, rho, lam));
    }
    Ok(Prof { l, l2, eq, dd, vmu, dstar, rho_lam: rl })
}
fn ceil_div(a: I, b: I) -> I { if a <= 0 { 0 } else { (a + b - 1) / b } }
#[derive(Default)]
struct St {
    bases: u64, skipped_half: u64, skipped_other: u64, nomult: u64, evals: u64,
    u_cases: u64, u_viol: u64, l_cases_cond: u64, l_viol: u64, nc_cases: u64, nc_hold: u64, nc_fail: u64,
    e_cases: u64, e_viol: u64, k_ge_l2: u64, k_lt_l2: u64, ml_eq_k_all: u64, ml_eq_k_without: u64,
    c1_cases: u64, c1_fail: u64, c1_kl2_viol: u64, c2_cases: u64, c2_fail: u64, c2_cond_viol: u64,
    xr_cases: u64, xr_viol: u64,
    ncv_cases: u64, ncv_detect: u64, ncw_cases: u64, ncw_detect: u64,
    weak_cases: u64, weak_viol: u64, belowl2_cases: u64, tension: u64,
    d_gt_cap_bases: u64,
    c2c_cases: u64, c2c_viol: u64, c2c_only: u64, c2c_false_hold: u64, c2c_false_fail: u64, c1_cond2_viol: u64, c2w_cases: u64, c2w_viol: u64, kl2_gt_k: u64, kl2_eq_l2: u64,
}
fn push_w(b: &[I], w: I) -> Vec<I> { let mut v = b.to_vec(); v.push(w); v }
fn run_base(b: &[I], mmax: I, wcap: I, claims: bool, xr: bool, st: &mut St, tag: &str, verbose: bool) {
    let mut bs: Vec<I> = b.to_vec(); bs.sort(); bs.dedup();
    let p = match profile(&bs) {
        Ok(p) => p,
        Err(e) => { if e == "L=1/2" { st.skipped_half += 1; } else { st.skipped_other += 1; if e.starts_with("TENSION") { st.tension += 1; } println!("SKIP {} {:?}: {}", tag, bs, e); } return; }
    };
    st.bases += 1;
    let mx = *bs.iter().max().unwrap(); let ld = p.l.n * p.dd / p.l.d; assert!(ld * p.l.d == p.l.n * p.dd, "L*D not integer");
    if p.dd > wcap { st.d_gt_cap_bases += 1; st.nomult += 1; return; }
    // multiples to test
    let mut ms: BTreeSet<I> = (1..=mmax).collect();
    let m_cond = ceil_div(ld * mx - p.vmu, p.dd).max(1);
    // smallest w with K>=L2 : w >= vmu*L2/(L-L2)
    let m_k = if p.l2.n == 0 { 1 } else { let num = p.vmu * p.l2.n * p.l.d; let den = p.l2.d * p.l.n - p.l2.n * p.l.d; ceil_div(num * 1, den * p.dd + 0).max(1) };
    // (w >= vmu*L2/(L-L2) with L,L2 as fractions: vmu*(L2.n/L2.d)/(L.n/L.d - L2.n/L2.d) = vmu*L2.n*L.d/(L2.d*L.n - L2.n*L.d))
    let m2 = ceil_div(2 * mx * mx * mx, p.dd).max(1); let mc2 = ceil_div(mx * p.dd, 2 * p.dd).max(1);
    for base in [m_cond, m_k, m2, mc2] { for dm in -1..=1 { let m = base + dm; if m >= 1 { ms.insert(m); } } }
    if claims { ms.insert(m2 + 2); ms.insert(m2.max(mc2)); ms.insert(m2.max(mc2) + 1); }
    if verbose { println!("{} base={:?} L={}/{} L2={}/{} D={} vmu={} #eq={} LD={} m_cond={} m_K={} m_2max3={}", tag, bs, p.l.n, p.l.d, p.l2.n, p.l2.d, p.dd, p.vmu, p.eq.len(), ld, m_cond, m_k, m2); }
    let mut cnt = 0u64;
    for m in ms {
        let w = m * p.dd; if w > wcap { continue; } if bs.contains(&w) { println!("IMPOSSIBLE w in B {:?} {}", bs, w); continue; }
        st.evals += 1; cnt += 1;
        let bw = push_w(&bs, w);
        let k = Fr::new(w * p.l.n, p.l.d * (w + p.vmu));
        let c = if k >= p.l2 { k } else { p.l2 };
        let cond = w + p.vmu >= ld * mx;
        // (U)
        let u_ok = ml_le(&bw, c); st.u_cases += 1; if !u_ok { st.u_viol += 1; println!("U-VIOLATION {} B={:?} w={} K={}/{} L2={}/{}", tag, bs, w, k.n, k.d, p.l2.n, p.l2.d); }
        // (L)
        let l_ok = ml_ge(&bw, k);
        if cond { st.l_cases_cond += 1; if !l_ok { st.l_viol += 1; println!("L-VIOLATION {} B={:?} w={} K={}/{}", tag, bs, w, k.n, k.d); } }
        else { st.nc_cases += 1; if l_ok { st.nc_hold += 1; } else { st.nc_fail += 1; } }
        // (L') refined closed bound with d* = denominator of the equality time attaining v_mu:  w+vmu >= L d* max(B)
        let ld2 = p.l.n * p.dstar / p.l.d; assert!(ld2 * p.l.d == p.l.n * p.dstar);
        let cond2 = w + p.vmu >= ld2 * mx;
        if cond2 { st.c2c_cases += 1; if !l_ok { st.c2c_viol += 1; println!("Lprime-VIOLATION {} B={:?} w={} d*={}", tag, bs, w, p.dstar); } if !cond { st.c2c_only += 1; } }
        else { if l_ok { st.c2c_false_hold += 1; } else { st.c2c_false_fail += 1; } }
        if !cond2 && 8 * (w + p.vmu) >= ld2 * mx { st.c2w_cases += 1; if !l_ok { st.c2w_viol += 1; } }
        if w >= 2 * mx * mx * mx && !cond2 { st.c1_cond2_viol += 1; }
        // (E)
        let kge = k >= p.l2; if kge { st.k_ge_l2 += 1; } else { st.k_lt_l2 += 1; if !ml_le(&bw, k) { st.kl2_gt_k += 1; } if ml_le(&bw, p.l2) && ml_ge(&bw, p.l2) { st.kl2_eq_l2 += 1; } }
        let eq_k = ml_le(&bw, k) && l_ok;  // ML == K
        if eq_k { st.ml_eq_k_all += 1; if !(kge && cond) { st.ml_eq_k_without += 1; } }
        if kge && cond { st.e_cases += 1; if !eq_k { st.e_viol += 1; println!("E-VIOLATION {} B={:?} w={}", tag, bs, w); } }
        // ML strictly below max(K,L2) (shows 'ML = max(K,L2)' false in general)
        if !ml_ge(&bw, c) { st.belowl2_cases += 1; }
        // weakened condition (planted negative for the closed bound): w+vmu >= (L D max)/8
        if !(w + p.vmu >= ld * mx) { /* only count where weak cond holds but true cond fails */
            if 8 * (w + p.vmu) >= ld * mx { st.weak_cases += 1; if !l_ok { st.weak_viol += 1; } } }
        // claim w >= 2 max^3 (multiple of D)
        if claims || w >= 2 * mx * mx * mx {
            if w >= 2 * mx * mx * mx {
                st.c1_cases += 1; if !kge { st.c1_kl2_viol += 1; }
                if !eq_k { st.c1_fail += 1; println!("CLAIM2max3-FAIL {} B={:?} D={} w={} cond={} K>=L2={} LD*max={}", tag, bs, p.dd, w, cond, kge, ld * mx); }
            }
            // corrected claim: w >= max(2max^3, D*max/2)
            if w >= 2 * mx * mx * mx && 2 * w >= p.dd * mx {
                st.c2_cases += 1; if !eq_k { st.c2_fail += 1; } if !cond { st.c2_cond_viol += 1; }
            }
        }
        // negative controls: wrong v_mu
        if kge && cond && eq_k {
            for vw in [p.vmu + 1, mx.max(p.vmu + 1), (p.vmu - 1).max(1)] {
                if vw == p.vmu { continue; }
                let k2 = Fr::new(w * p.l.n, p.l.d * (w + vw));
                st.ncv_cases += 1; let claim_ok = ml_le(&bw, k2) && ml_ge(&bw, k2); if !claim_ok { st.ncv_detect += 1; }
            }
        }
        // negative control: w not a multiple of D (only informative if D >= 2)
        if p.dd >= 2 && w > 2 {
            for w2 in [w + 1, w - 1] {
                if bs.contains(&w2) { continue; }
                let bw2 = push_w(&bs, w2); let k2 = Fr::new(w2 * p.l.n, p.l.d * (w2 + p.vmu)); let c2 = if k2 >= p.l2 { k2 } else { p.l2 };
                st.ncw_cases += 1; if !ml_le(&bw2, c2) { st.ncw_detect += 1; }
            }
        }
        // cross-route check of exact ML(B u {w}) on a subset (local-max route vs cover route)
        if xr && w <= 1200 && (st.evals % 5 == 0) {
            let lm = local_max(&bw); let mlm = lm.iter().map(|x| x.1).max().unwrap();
            st.xr_cases += 1; if !(ml_le(&bw, mlm) && ml_ge(&bw, mlm)) { st.xr_viol += 1; println!("XROUTE-TENSION {} B={:?} w={} lm={}/{}", tag, bs, w, mlm.n, mlm.d); }
        }
    }
    let _ = cnt;
}
fn pr(name: &str, s: &St) {
    println!("SUMMARY {}: bases={} skipped(L=1/2)={} skipped(other)={} tension={} D>cap(no multiples)={} evals={}", name, s.bases, s.skipped_half, s.skipped_other, s.tension, s.d_gt_cap_bases, s.evals);
    println!("  (U) ML<=max(K,L2): cases={} VIOLATIONS={}  | K>=L2 cases={} K<L2 cases={} (of which ML>K: {}, ML==L2: {}) | ML<max(K,L2) cases={}", s.u_cases, s.u_viol, s.k_ge_l2, s.k_lt_l2, s.kl2_gt_k, s.kl2_eq_l2, s.belowl2_cases);
    println!("  (L) cond true => ML>=K: cases={} VIOLATIONS={}  | cond false: cases={} ML>=K holds={} fails={}", s.l_cases_cond, s.l_viol, s.nc_cases, s.nc_hold, s.nc_fail);
    println!("  (L') w+vmu >= L d* max => ML>=K: cases={} VIOLATIONS={} (cases where D-version cond false but L' true: {}) | L' false: ML>=K holds={} fails={} | weakened L'(8x) only: cases={} violated={} | w>=2max^3 but L' false: {}", s.c2c_cases, s.c2c_viol, s.c2c_only, s.c2c_false_hold, s.c2c_false_fail, s.c2w_cases, s.c2w_viol, s.c1_cond2_viol);
    println!("  (E) K>=L2 & cond => ML==K: cases={} VIOLATIONS={}  | ML==K total={} of which outside (K>=L2&cond)={}", s.e_cases, s.e_viol, s.ml_eq_k_all, s.ml_eq_k_without);
    println!("  claim w>=2max^3 (D|w): cases={} FAIL(ML!=K)={} K<L2 viol={} | corrected claim w>=max(2max^3,D*max/2): cases={} FAIL={} cond-viol={}", s.c1_cases, s.c1_fail, s.c1_kl2_viol, s.c2_cases, s.c2_fail, s.c2_cond_viol);
    println!("  cross-route ML (cover vs local-max): cases={} tensions={}", s.xr_cases, s.xr_viol);
    println!("  NEG wrong v_mu: claims={} detected(false)={} | NEG w not mult of D: claims={} detected(false)={} | NEG weakened cond (8x): cases={} violated={}", s.ncv_cases, s.ncv_detect, s.ncw_cases, s.ncw_detect, s.weak_cases, s.weak_viol);
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("controls");
    let a = |i: usize, d: I| -> I { args.get(i).map(|s| s.parse().unwrap()).unwrap_or(d) };
    match mode {
        "controls" => {
            // engine negative controls: known ML values, both routes, and perturbation of the tested value
            let cs: Vec<(Vec<I>, (I, I))> = vec![(vec![1, 2, 3, 4, 5, 6], (1, 7)), (vec![1, 5, 6, 11, 16, 17], (5, 33)), (vec![1, 3, 4, 7], (1, 5)),
                (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 36], (3, 41)), (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 24], (1, 14)), (vec![1, 3, 4, 5, 7, 13, 18], (0, 0))];
            for (v, e) in cs {
                let l = ml_cover(&v); let lm = local_max(&v).iter().map(|x| x.1).max().unwrap();
                let up = Fr::new(l.n * 1000 + 1, l.d * 1000); let dn = Fr::new(l.n * 1000 - 1, l.d * 1000);
                println!("CONTROL {:?}: ML cover={}/{} lm={}/{} want={}/{} | closed(L)={} open(L)={} closed(L-eps)={} (want false) open(L+eps)={} (want true)", v, l.n, l.d, lm.n, lm.d, e.0, e.1, ml_le(&v, l), open_cover(&v, l), ml_le(&v, dn), open_cover(&v, up));
            }
        }
        "L2" => {
            // Lemma L2: L2([N]) <= 1/(N+2); structure of [N]\{r}
            let nmax = a(2, 40); let nmax2 = a(3, 40);
            let (mut bad, mut eq) = (0, 0);
            for n in 3..=nmax {
                let b: Vec<I> = (1..=n).collect(); let lm = local_max(&b);
                let l = lm.iter().map(|x| x.1).max().unwrap(); let l2 = lm.iter().map(|x| x.1).filter(|v| *v < l).max().unwrap_or(Fr::zero());
                let ok = l == Fr::new(1, n + 1) && l2 <= Fr::new(1, n + 2); if !ok { bad += 1; println!("L2-VIOLATION [N] N={} L={}/{} L2={}/{}", n, l.n, l.d, l2.n, l2.d); }
                if l2 == Fr::new(1, n + 2) { eq += 1; } else if n <= 12 { println!("note [N] N={} L2={}/{} (1/(N+2)={}/{})", n, l2.n, l2.d, 1, n + 2); }
            }
            println!("SUMMARY L2([N]) <= 1/(N+2), N=3..{}: violations={} (L2==1/(N+2) at {} of {} values)", nmax, bad, eq, nmax - 2);
            let (mut cases, mut viol, mut l2eq, mut l2eq_lt, mut cnt_lt, mut rn_cnt, mut rn_eq) = (0, 0, 0, 0, 0, 0, 0);
            for n in 3..=nmax2 { for r in (n / 2 + 1)..=n {
                if r < 3 { continue; }
                let b: Vec<I> = (1..=n).filter(|&x| x != r).collect();
                let p = match profile(&b) { Ok(p) => p, Err(e) => { println!("L2b skip N={} r={} {}", n, r, e); continue; } };
                cases += 1;
                let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
                let units: BTreeSet<Fr> = (1..r).filter(|&c| gcd(c, r) == 1).map(|c| Fr::new(c, r)).collect();
                let eqs: BTreeSet<Fr> = p.eq.iter().cloned().collect();
                if !(p.l == Fr::new(1, r) && p.dd == r && p.vmu == beta && eqs == units) { viol += 1; println!("STRUCT-VIOLATION N={} r={} L={}/{} D={} vmu={} beta={}", n, r, p.l.n, p.l.d, p.dd, p.vmu, beta); }
                if p.l2 > Fr::new(1, n + 1) { viol += 1; println!("L2a-VIOLATION N={} r={} L2={}/{}", n, r, p.l2.n, p.l2.d); }
                if p.l2 == Fr::new(1, n + 1) { l2eq += 1; if r < n { l2eq_lt += 1; } }
                if r < n { cnt_lt += 1; } else { rn_cnt += 1; if p.l2 == Fr::new(1, n + 1) { rn_eq += 1; } else if n <= 20 { println!("note r=N N={} L2={}/{} (1/(N+1)={}/{})", n, p.l2.n, p.l2.d, 1, n + 1); } }
            } }
            println!("SUMMARY [N]\\{{r}}, N/2<r<=N, r>=3, N=3..{}: cases={} violations(struct or L2<=1/(N+1))={} | L2==1/(N+1) in {} cases; r<N: {} of {} ; r=N: {} of {}", nmax2, cases, viol, l2eq, l2eq_lt, cnt_lt, rn_eq, rn_cnt);
        }
        "kravitz51" => {
            // B=[N], w=(N+1)s : ML = s/((N+1)s+1)
            let nmax = a(2, 30); let smax = a(3, 20); let (mut cases, mut viol) = (0, 0);
            for n in 2..=nmax {
                let b: Vec<I> = (1..=n).collect();
                let p = profile(&b).unwrap();
                assert!(p.l == Fr::new(1, n + 1) && p.dd == n + 1 && p.vmu == 1);
                for s in 1..=smax {
                    let w = (n + 1) * s; let bw = push_w(&b, w); let want = Fr::new(s, (n + 1) * s + 1);
                    cases += 1; if !(ml_le(&bw, want) && ml_ge(&bw, want)) { viol += 1; println!("K51-VIOLATION N={} s={}", n, s); }
                } }
            println!("SUMMARY Kravitz 5.1 ML(1..N,(N+1)s)=s/((N+1)s+1), N=2..{} s=1..{}: cases={} violations={}", nmax, smax, cases, viol);
        }
        "thmv" => {
            // BD Theorem V: ML([N]\{r} u {mr}) = max(1/(N+1), m/(mr+beta)), N/2<r<=N, r>=3
            let nmax = a(2, 30); let mmax = a(3, 45); let (mut cases, mut viol) = (0, 0);
            for n in 3..=nmax { for r in (n / 2 + 1)..=n { if r < 3 { continue; }
                let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
                let base: Vec<I> = (1..=n).filter(|&x| x != r).collect();
                for m in 2..=mmax {
                    let bw = push_w(&base, m * r); let k = Fr::new(m, m * r + beta); let want = if k >= Fr::new(1, n + 1) { k } else { Fr::new(1, n + 1) };
                    cases += 1; if !(ml_le(&bw, want) && ml_ge(&bw, want)) { viol += 1; println!("THMV-VIOLATION N={} r={} m={}", n, r, m); }
                } } }
            println!("SUMMARY Theorem V (BD) by cover engine, N=3..{} r>N/2 r>=3 m=2..{}: cases={} violations={}", nmax, mmax, cases, viol);
        }
        "fam" => {
            // [N]\{r}, all r (incl. r<=N/2), N<=nmax ; and [N] itself
            let nmax = a(2, 30); let mmax = a(3, 45); let wcap = a(4, 20000); let claims = a(5, 0) == 1;
            let mut st = St::default();
            for n in 3..=nmax { for r in 1..=n { let b: Vec<I> = (1..=n).filter(|&x| x != r).collect(); run_base(&b, mmax, wcap, claims, n <= 14, &mut st, "fam", n <= 6); } }
            pr(&format!("fam [N]\\{{r}} all r, N=3..{}", nmax), &st);
        }
        "gw" => {
            // Goddyn-Wong tight sets V=[N]\{r} u {mr} (beta >= m s) and non-tight siblings, used as bases
            let nmax = a(2, 22); let mut st = St::default();
            for n in 3..=nmax { for r in (n / 2 + 1)..=n { if r < 3 { continue; }
                let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
                for m in 2..=6 { let mut b: Vec<I> = (1..=n).filter(|&x| x != r).collect(); b.push(m * r);
                    let tight = beta >= m * s; if tight || m == 2 { run_base(&b, 14, 6000, false, false, &mut st, if tight { "gw-tight" } else { "gw-nontight" }, false); } } } }
            pr(&format!("GW family bases V=[N]\\{{r}} u {{mr}} N<={}", nmax), &st);
        }
        "spor" => {
            let mut st = St::default();
            let sets: Vec<Vec<I>> = vec![vec![1, 5, 6, 11, 16, 17], vec![1, 3, 4, 5, 7, 13, 18], vec![1, 3, 4, 7], vec![1, 3, 4, 5, 9], vec![1, 2, 3, 4, 5, 7, 12], vec![1, 4, 5, 6, 7, 11, 13], vec![1, 2, 3, 5, 8], vec![2, 3, 7], vec![1, 4, 7, 9]];
            for s in &sets { run_base(s, 16, 20000, false, true, &mut st, "spor", true);
                // all subsets obtained by deleting one element (as bases)
                for i in 0..s.len() { let mut t = s.clone(); t.remove(i); if t.len() >= 2 { run_base(&t, 16, 20000, false, true, &mut st, "spor-del", false); } } }
            pr("sporadic sets and their one-deletions", &st);
        }
        "random" => {
            let nb = a(2, 10000); let maxsp = a(3, 60); let wcap = a(4, 3000); let mmax = a(5, 10); let claims = a(6, 0) == 1; let seed = a(7, 88172645463325252) as u64;
            let mut st = St::default(); let mut x: u64 = seed;
            let mut nx = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
            let (mut cnt, mut g1, mut gn) = (0, 0, 0);
            while cnt < nb {
                let sz = 2 + (nx() % 5) as usize; let mut s: BTreeSet<I> = BTreeSet::new();
                while s.len() < sz { s.insert(1 + (nx() % (maxsp as u64)) as I); }
                let b: Vec<I> = s.into_iter().collect(); let g = b.iter().fold(0, |a, &v| gcd(a, v)); if g == 1 { g1 += 1; } else { gn += 1; }
                cnt += 1; run_base(&b, mmax, wcap, claims, cnt % 20 == 0, &mut st, "rnd", false);
                if cnt % 2000 == 0 { println!("progress {} / {} bases, evals {}", cnt, nb, st.evals); }
            }
            println!("random bases drawn={} (gcd 1: {}, gcd>1: {}), speeds<={}, seed={}", nb, g1, gn, maxsp, seed);
            pr(&format!("random bases 2..6 speeds<={} wcap={} mmax={} claims={}", maxsp, wcap, mmax, claims), &st);
        }
        _ => println!("modes: controls | L2 Nmax Nmax2 | kravitz51 | thmv | fam | gw | spor | random"),
    }
}
