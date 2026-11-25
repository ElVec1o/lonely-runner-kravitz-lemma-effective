// the accompanying code  Exact integer test of
//   (A) beta = v_mu : for B = [N]\{r}, N/2 < r <= N: ML(B) = 1/r, equality times are exactly a/r (gcd(a,r)=1),
//       Kravitz's v_mu (Lemma 9.4) equals beta = least b >= N+1-r coprime to r.
//   (B) Theorem K* (candidate): for ANY base B with L = ML(B) < 1/2, D = lcm of equality-time denominators,
//       w = mD not in B:   [ (i) K(w) >= L2(B)  and  (ii) crossing inside the first linear piece ]  =>  ML(B u {w}) = K(w),
//       K(w) = wL/(w+v_mu),  L2(B) = largest local-maximum value of e_B below L.
// All arithmetic exact (i128 fractions). Memory O(#candidate times) (< 10 MB). No floating point.
use std::cmp::Ordering;
use std::collections::BTreeSet;
type I = i128;
fn gcd(a: I, b: I) -> I { if b == 0 { a.abs() } else { gcd(b, a % b) } }
#[derive(Clone, Copy, Debug)]
struct Q { n: I, d: I }
impl Q {
    fn new(n: I, d: I) -> Q { let g = gcd(n, d).max(1); Q { n: n / g, d: d / g } }
    fn cmp(&self, o: &Q) -> Ordering { (self.n * o.d).cmp(&(o.n * self.d)) }
    fn eq(&self, o: &Q) -> bool { self.cmp(o) == Ordering::Equal }
}
// distance to nearest integer of v*p/q, as numerator over q
fn dist(v: I, p: I, q: I) -> I { let x = ((v % q) * (p % q)).rem_euclid(q); x.min(q - x) }
fn e_at(b: &[I], p: I, q: I) -> Q { let m = b.iter().map(|&v| dist(v, p, q)).min().unwrap(); Q::new(m, q) }
fn ml(b: &[I]) -> Q {
    let mut best = Q { n: 0, d: 1 };
    for i in 0..b.len() { for j in i..b.len() {
        let d = b[i] + b[j];
        for k in 1..=d / 2 {
            let mut m = I::MAX;
            for &v in b { let x = dist(v, k, d); if x < m { m = x; if m * best.d <= best.n * d { break; } } }
            if m * best.d > best.n * d { best = Q::new(m, d); }
        }
    } }
    best
}
struct Prof { l: Q, l2: Q, eq: Vec<(I, I)>, dd: I, vmu: I, sides: Vec<(I, I, I, i32)> } // sides: (k,d,v,sign)
fn profile(b: &[I]) -> Prof {
    // candidate times k/d, d = v_i+v_j ; local max iff the min is attained by an increasing and a decreasing runner
    let mut seen: BTreeSet<(I, I)> = BTreeSet::new();
    let mut lm: Vec<(Q, I, I)> = Vec::new();
    for i in 0..b.len() { for j in i..b.len() {
        let d0 = b[i] + b[j];
        for k0 in 1..d0 {
            let g = gcd(k0, d0); let (k, d) = (k0 / g, d0 / g);
            if !seen.insert((k, d)) { continue; }
            let m = b.iter().map(|&v| dist(v, k, d)).min().unwrap();
            if m == 0 { continue; }
            let (mut up, mut dn) = (false, false);
            for &v in b { let x = ((v % d) * k).rem_euclid(d); if x == m { up = true; } if x == d - m { dn = true; } }
            if up && dn { lm.push((Q::new(m, d), k, d)); }
        }
    } }
    let mut l = Q { n: 0, d: 1 };
    for x in &lm { if x.0.cmp(&l) == Ordering::Greater { l = x.0; } }
    let mut l2 = Q { n: 0, d: 1 };
    let mut eq = Vec::new(); let mut dd: I = 1; let mut vmu = I::MAX; let mut sides = Vec::new();
    for x in &lm {
        if x.0.eq(&l) {
            let (k, d) = (x.1, x.2); eq.push((k, d)); dd = dd / gcd(dd, d) * d;
            let m = l.n * d / l.d; // numerator of L over d (exact since value == L)
            let mut rho = 0; let mut lam = 0;
            for &v in b { let xx = ((v % d) * k).rem_euclid(d); if xx == m && v > rho { rho = v; } if xx == d - m && v > lam { lam = v; } }
            sides.push((k, d, rho, -1)); sides.push((k, d, lam, 1));
            vmu = vmu.min(rho).min(lam);
        } else if x.0.cmp(&l2) == Ordering::Greater { l2 = x.0; }
    }
    Prof { l, l2, eq, dd, vmu, sides }
}
struct Stat { bases: u64, cases: u64, cond: u64, viol: u64, holds: u64, holds_nocond: u64, fail_i: u64, fail_ii: u64, thr_eq: u64, thr_gap_max: I, below_l2: u64, eq_max_kl2: u64 }
fn run_base(b: &[I], wmax: I, st: &mut Stat, verbose: bool, tag: &str) {
    let p = profile(b);
    if p.l.n * 2 >= p.l.d || p.eq.is_empty() { return; }
    st.bases += 1;
    let mmax = (wmax / p.dd).min(600);
    let (mut last_bad_true, mut last_bad_pred) = (0, 0);
    for m in 1..=mmax {
        let w = m * p.dd; if b.contains(&w) { continue; }
        st.cases += 1;
        let kq = Q::new(w * p.l.n, p.l.d * (w + p.vmu));
        let ci = kq.cmp(&p.l2) != Ordering::Less;
        // (ii): some side with v == vmu whose crossing point t_j + sign*L/(w+v) has e_B == K
        let mut cii = false;
        for &(k, d, v, sg) in &p.sides { if v != p.vmu { continue; }
            // t = k/d + sg * l.n/(l.d*(w+v))
            let q = d * p.l.d * (w + v); let pn = k * p.l.d * (w + v) + (sg as I) * l_mul(p.l.n, d);
            if e_at(b, pn.rem_euclid(q), q).eq(&kq) { cii = true; break; }
        }
        let mut v2 = b.to_vec(); v2.push(w); let act = ml(&v2);
        let ok = act.eq(&kq);
        if ci && cii { st.cond += 1; if !ok { st.viol += 1; println!("VIOLATION {} base={:?} w={} K={}/{} ML={}/{}", tag, b, w, kq.n, kq.d, act.n, act.d); } }
        if !ci { st.fail_i += 1; } if !cii { st.fail_ii += 1; }
        if ok { st.holds += 1; if !(ci && cii) { st.holds_nocond += 1; } } else { last_bad_true = m; }
        if !(ci && cii) { last_bad_pred = m; }
        if act.cmp(&p.l2) == Ordering::Less && act.cmp(&kq) == Ordering::Less { st.below_l2 += 1; }
        let mx = if kq.cmp(&p.l2) == Ordering::Less { p.l2 } else { kq };
        if act.eq(&mx) { st.eq_max_kl2 += 1; }
    }
    if last_bad_true == last_bad_pred { st.thr_eq += 1; }
    st.thr_gap_max = st.thr_gap_max.max(last_bad_pred - last_bad_true);
    if verbose {
        let vmax = *b.iter().max().unwrap(); let vmin = *b.iter().min().unwrap();
        println!("{} base={:?} L={}/{} L2={}/{} D={} vmu={} #eq={} m0_true={} m0_pred={} m_kravitz>{} (mmax={})", tag, b, p.l.n, p.l.d, p.l2.n, p.l2.d, p.dd, p.vmu, p.eq.len(), last_bad_true + 1, last_bad_pred + 1, 4 * vmax * vmax * vmax * vmin / p.dd, mmax);
    }
}
fn l_mul(a: I, b: I) -> I { a * b }
fn pr(name: &str, s: &Stat) {
    println!("SUMMARY {}: bases={} cases={} cond_true={} VIOLATIONS={} formula_holds={} holds_without_cond={} fail(i)={} fail(ii)={} bases_threshold_exact={} max_threshold_gap_m={} ML_below_L2={} ML_eq_max(K,L2)={}", name, s.bases, s.cases, s.cond, s.viol, s.holds, s.holds_nocond, s.fail_i, s.fail_ii, s.thr_eq, s.thr_gap_max, s.below_l2, s.eq_max_kl2);
}
fn new() -> Stat { Stat { bases: 0, cases: 0, cond: 0, viol: 0, holds: 0, holds_nocond: 0, fail_i: 0, fail_ii: 0, thr_eq: 0, thr_gap_max: 0, below_l2: 0, eq_max_kl2: 0 } }
fn main() {
    let nmax: I = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(16);
    let wmax: I = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(1500);
    let nrand: u64 = std::env::args().nth(3).map(|s| s.parse().unwrap()).unwrap_or(1500);
    // negative control of ml(): known values
    let c1 = ml(&[1, 2, 3, 4, 5, 6]); let c2 = ml(&[1, 5, 6, 11, 16, 17]); let c3 = ml(&[1, 3, 4, 7]); let c4 = ml(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 36, 13]);
    println!("CONTROL ML(1..6)={}/{} (want 1/7)  ML(1,5,6,11,16,17)={}/{} (want 5/33)  ML(1,3,4,7)={}/{} (want 1/5)  ML([13]_12->36)={}/{} (want 3/41)", c1.n, c1.d, c2.n, c2.d, c3.n, c3.d, c4.n, c4.d);
    // (A) beta = v_mu
    let (mut a_cases, mut a_bad) = (0u64, 0u64);
    for n in 3..=nmax.max(40).min(60) { for r in (n / 2 + 1)..=n {
        let b: Vec<I> = (1..=n).filter(|&x| x != r).collect();
        let p = profile(&b);
        let s = n + 1 - r; let mut beta = s; while gcd(beta, r) != 1 { beta += 1; }
        let phi = (1..r).filter(|&a| gcd(a, r) == 1).count();
        let okl = p.l.eq(&Q::new(1, r));
        let okt = p.eq.len() == phi && p.eq.iter().all(|&(k, d)| d == r && gcd(k, r) == 1);
        a_cases += 1;
        if !(okl && okt && p.vmu == beta && p.dd == r) { a_bad += 1; if a_bad <= 10 { println!("A-MISMATCH N={} r={} L={}/{} #eq={} phi={} D={} vmu={} beta={}", n, r, p.l.n, p.l.d, p.eq.len(), phi, p.dd, p.vmu, beta); } }
    } }
    println!("SUMMARY A (beta = v_mu, equality times = units/r, L = 1/r), N=3..{}: cases={} mismatches={}", nmax.max(40).min(60), a_cases, a_bad);
    // (B) K*
    let mut sa = new();
    for n in 3..=nmax { for r in (n / 2 + 1)..=n { let b: Vec<I> = (1..=n).filter(|&x| x != r).collect(); run_base(&b, wmax, &mut sa, n <= 9 || n == 13, "a"); } }
    pr("a: [N]\\{r}, r>N/2", &sa);
    let mut sl = new();
    for n in 4..=nmax { for r in 1..=(n / 2) { let b: Vec<I> = (1..=n).filter(|&x| x != r).collect(); run_base(&b, wmax, &mut sl, n <= 7, "a'"); } }
    pr("a': [N]\\{r}, r<=N/2", &sl);
    let mut sc = new();
    let spor: Vec<Vec<I>> = vec![vec![1, 3, 4, 7], vec![1, 3, 4, 5, 9], vec![1, 2, 3, 4, 5, 7, 12], vec![1, 5, 6, 11, 16, 17], vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 24], vec![1, 4, 5, 6, 7, 11, 13], vec![1, 2, 3, 5, 8], vec![2, 3, 7], vec![1, 4, 7, 9]];
    for b in &spor { run_base(b, wmax * 2, &mut sc, true, "c"); }
    pr("c: sporadic / GW-accelerated bases", &sc);
    let mut sr = new(); let mut x: u64 = 0x9E3779B97F4A7C15;
    let mut nx = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let mut cnt = 0;
    while cnt < nrand {
        let sz = 2 + (nx() % 5) as usize; let mut s: BTreeSet<I> = BTreeSet::new();
        while s.len() < sz { s.insert(1 + (nx() % 30) as I); }
        let b: Vec<I> = s.into_iter().collect(); let g = b.iter().fold(0, |a, &v| gcd(a, v)); if g != 1 { continue; }
        cnt += 1; run_base(&b, wmax, &mut sr, cnt <= 12, "d");
    }
    pr("d: random bases (2..6 speeds <= 30, gcd 1)", &sr);
}
