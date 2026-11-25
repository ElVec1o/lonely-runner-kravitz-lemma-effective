// ins.rs : independent exact engine for the INS theorem review.
// Own design. Exact integers/fractions only (i64 inner loops, i128 rationals). No floats.
// ML route B: candidate times t=k/(u+v), u<=v in V.  ML route A: exact arc cover certificate at x=ML
//   (closed arcs cover  <=> ML<=x ;  open arcs leave a point  <=> ML>=x).
// Peaks: route P1 (k/(u+v), u<=v in B), route P2 (Farey fractions of order 2M, and 4M as Lemma-1(c) check).
// H_p(w): closed form, and an independent brute force (crossings + breakpoints, exact evaluation).
use std::collections::BTreeSet;
use std::env;

type I = i128;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q { n: I, d: I }
fn gcd(a: I, b: I) -> I { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
fn qn(n: I, d: I) -> Q { let (mut n, mut d) = (n, d); if d < 0 { n = -n; d = -d; } let g = gcd(n, d); if g > 1 { n /= g; d /= g; } if n == 0 { d = 1; } Q { n, d } }
fn qi(n: I) -> Q { Q { n, d: 1 } }
fn add(a: Q, b: Q) -> Q { qn(a.n * b.d + b.n * a.d, a.d * b.d) }
fn sub(a: Q, b: Q) -> Q { qn(a.n * b.d - b.n * a.d, a.d * b.d) }
fn mul(a: Q, b: Q) -> Q { qn(a.n * b.n, a.d * b.d) }
fn div(a: Q, b: Q) -> Q { qn(a.n * b.d, a.d * b.n) }
fn lt(a: Q, b: Q) -> bool { a.n * b.d < b.n * a.d }
fn le(a: Q, b: Q) -> bool { a.n * b.d <= b.n * a.d }
fn qmax(a: Q, b: Q) -> Q { if lt(a, b) { b } else { a } }
fn qmin(a: Q, b: Q) -> Q { if lt(a, b) { a } else { b } }
fn nid(x: Q) -> Q { let r = x.n.rem_euclid(x.d); qn(r.min(x.d - r), x.d) }
fn fmt(a: Q) -> String { format!("{}/{}", a.n, a.d) }

// ---------------- ML route B ----------------
fn ml_b(v: &[i64]) -> Q {
    let (mut bn, mut bd) = (0i64, 1i64);
    let n = v.len();
    for i in 0..n { for j in i..n {
        let qq = v[i] + v[j];
        'k: for k in 1..qq {
            let mut m = i64::MAX;
            for &x in v {
                let r = (x * k) % qq;
                let dd = if 2 * r < qq { r } else { qq - r };
                if dd < m { m = dd; if m * bd <= bn * qq { continue 'k; } }
            }
            bn = m; bd = qq;
        }
    }}
    qn(bn as I, bd as I)
}
// exists t with f_V(t) >= c (strict=false) or > c (strict=true), over candidate times
fn exists_cmp(v: &[i64], c: Q, strict: bool) -> bool {
    let (cn, cd) = (c.n as i64, c.d as i64);
    let n = v.len();
    for i in 0..n { for j in i..n {
        let qq = v[i] + v[j];
        'k: for k in 1..qq {
            let mut m = i64::MAX;
            for &x in v {
                let r = (x * k) % qq;
                let dd = if 2 * r < qq { r } else { qq - r };
                if dd < m { m = dd; let a = m * cd; let b = cn * qq; if (strict && a <= b) || (!strict && a < b) { continue 'k; } }
            }
            return true;
        }
    }}
    false
}
// ---------------- ML route A (arc cover) ----------------
fn arcs(v: &[i64], c: Q) -> Vec<(I, I, I)> {
    let (a, b) = (c.n, c.d);
    let mut out = Vec::new();
    for &x in v { let den = (x as I) * b; for j in 0..=x { let jb = (j as I) * b; out.push((jb - a, jb + a, den)); } }
    out.sort_by(|p, q| (p.0 * q.2).cmp(&(q.0 * p.2)));
    out
}
fn closed_cover(ar: &[(I, I, I)]) -> bool {
    let mut cur = (0 as I, 1 as I); let mut reach = cur; let mut idx = 0;
    loop {
        while idx < ar.len() && ar[idx].0 * cur.1 <= cur.0 * ar[idx].2 {
            let r = (ar[idx].1, ar[idx].2);
            if r.0 * reach.1 > reach.0 * r.1 { reach = r; }
            idx += 1;
        }
        if reach.0 * cur.1 <= cur.0 * reach.1 { return false; }
        cur = reach;
        if cur.0 >= cur.1 { return true; }
    }
}
fn open_uncovered(ar: &[(I, I, I)]) -> bool {
    let mut cur = (0 as I, 1 as I); let mut reach = cur; let mut idx = 0;
    loop {
        while idx < ar.len() && ar[idx].0 * cur.1 < cur.0 * ar[idx].2 {
            let r = (ar[idx].1, ar[idx].2);
            if r.0 * reach.1 > reach.0 * r.1 { reach = r; }
            idx += 1;
        }
        if reach.0 * cur.1 <= cur.0 * reach.1 { return true; }
        cur = reach;
        if cur.0 > cur.1 { return false; }
    }
}
fn cert(v: &[i64], x: Q) -> bool { let ar = arcs(v, x); closed_cover(&ar) && open_uncovered(&ar) }
fn cert_ctrl(v: &[i64], x: Q) -> bool {
    // controls: x*(1-1/1000): closed cover must FAIL ; x*(1+1/1000): open arcs must cover (uncovered=false)
    let lo = mul(x, qn(999, 1000)); let hi = mul(x, qn(1001, 1000));
    let c1 = !closed_cover(&arcs(v, lo));
    let c2 = !open_uncovered(&arcs(v, hi));
    c1 && c2
}
// ---------------- peaks ----------------
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Peak { d: i64, k: i64, m: i64, rho: i64, lam: i64 }
fn local_max(b: &[i64], k: i64, d: i64) -> Option<Peak> {
    let mut m = i64::MAX;
    for &v in b { let r = (v * k) % d; let dd = r.min(d - r); if dd < m { m = dd; } }
    if m == 0 { return None; }
    let (mut rho, mut lam) = (0i64, 0i64);
    for &v in b {
        let r = (v * k) % d; let dd = r.min(d - r);
        if dd == m {
            if 2 * r < d { rho = rho.max(v); }
            else if 2 * r > d { lam = lam.max(v); }
            else { rho = rho.max(v); lam = lam.max(v); }
        }
    }
    if rho > 0 && lam > 0 { Some(Peak { d, k, m, rho, lam }) } else { None }
}
fn peaks_p1(b: &[i64]) -> Vec<Peak> {
    let mut set = BTreeSet::new();
    let n = b.len();
    for i in 0..n { for j in i..n { let qq = b[i] + b[j]; for k in 1..qq { let g = gcd(k as I, qq as I) as i64; set.insert((qq / g, k / g)); } } }
    let mut out = Vec::new();
    for (d, k) in set { if let Some(p) = local_max(b, k, d) { out.push(p); } }
    out.sort(); out
}
fn peaks_p2(b: &[i64], order: i64) -> Vec<Peak> {
    let mut out = Vec::new();
    for d in 2..=order { for k in 1..d { if gcd(k as I, d as I) == 1 { if let Some(p) = local_max(b, k, d) { out.push(p); } } } }
    out.sort(); out
}
fn theta_of(p: &Peak, w: i64) -> Q { let r = ((w as I) * (p.k as I)) % (p.d as I); let d = p.d as I; if 2 * r <= d { qn(r, d) } else { qn(r - d, d) } }
fn mu_of(p: &Peak) -> Q { qn(p.m as I, p.d as I) }
// ---------------- H closed form ----------------
fn hform(mu: Q, th: Q, rho: I, lam: I, w: I) -> Q {
    let ath = if th.n < 0 { qn(-th.n, th.d) } else { th };
    if le(mu, ath) { return mu; }
    let (wq, rq, lq) = (qi(w), qi(rho), qi(lam));
    if th.n >= 0 {
        let right = div(add(mul(wq, mu), mul(lq, th)), add(wq, lq));
        let left = div(sub(mul(wq, mu), mul(rq, th)), add(wq, rq));
        qmax(left, right)
    } else {
        let left = div(add(mul(wq, mu), mul(rq, ath)), add(wq, rq));
        let right = div(sub(mul(wq, mu), mul(lq, ath)), add(wq, lq));
        qmax(left, right)
    }
}
fn hone(mu: Q, th: Q, rho: I, lam: I, w: I) -> Q {
    let ath = if th.n < 0 { qn(-th.n, th.d) } else { th };
    if le(mu, ath) { return mu; }
    let (wq, rq, lq) = (qi(w), qi(rho), qi(lam));
    if th.n >= 0 { div(add(mul(wq, mu), mul(lq, th)), add(wq, lq)) } else { div(add(mul(wq, mu), mul(rq, ath)), add(wq, rq)) }
}
// independent brute force: max over h of min(T(h), ||th + w h||), candidates = h=0, T/g crossings, g breakpoints
fn h_brute(mu: Q, th: Q, rho: I, lam: I, w: I) -> Q {
    let tent = |h: Q| -> Q { if h.n >= 0 { sub(mu, mul(qi(lam), h)) } else { add(mu, mul(qi(rho), h)) } };
    let ev = |h: Q| -> Q { qmin(tent(h), nid(add(th, mul(qi(w), h)))) };
    let mut best = ev(qi(0));
    let sl = rho.min(lam);
    // radius where tent is >= 0
    let rad = div(mu, qi(sl)); // |h| <= mu/min slope covers both sides (conservative)
    let rr = ((w * mu.n) / (mu.d * sl)) + 4;
    for e in [1i128, -1i128] {
        for n in -(rr + 2)..=(rr + 2) {
            // right: mu - lam h = e (th + w h - n)  =>  h (lam + e w) = mu - e (th - n)
            let den = lam + e * w;
            if den != 0 {
                let h = div(sub(mu, mul(qi(e), sub(th, qi(n)))), qi(den));
                if h.n >= 0 && le(h, rad) { best = qmax(best, ev(h)); }
            }
            // left: h=-s, mu - rho s = e (th - w s - n) => s (rho - e w) = mu - e (th - n)
            let den2 = rho - e * w;
            if den2 != 0 {
                let s = div(sub(mu, mul(qi(e), sub(th, qi(n)))), qi(den2));
                if s.n >= 0 && le(s, rad) { best = qmax(best, ev(qn(-s.n, s.d))); }
            }
        }
    }
    // g breakpoints th + w h = j/2
    for j in -(2 * rr + 8)..=(2 * rr + 8) {
        let h = div(sub(qn(j, 2), th), qi(w));
        let ah = if h.n < 0 { qn(-h.n, h.d) } else { h };
        if le(ah, rad) { best = qmax(best, ev(h)); }
    }
    best
}
// ---------------- PRNG ----------------
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
}
// ---------------- statistics ----------------
#[derive(Default)]
struct St {
    bases: u64, cases: u64, tension: u64, cert_fail: u64, ctrl_fail: u64,
    s1_viol: u64, s2_cases: u64, s2_viol: u64, s3_cases: u64, s3_viol: u64, s4_viol: u64, s4neg_viol: u64,
    brute_checked: u64, brute_mismatch: u64, l1c_viol: u64, peak_route_mismatch: u64,
    n_swap_s1: u64, n_swap_eq: u64, n_swap_eqcases: u64, n_low_s1: u64, n_sign_s1: u64, n_sign_eq: u64,
    n_range_eq: u64, n_range_cases: u64, half_bases: u64, n_one_s1: u64, n_one_eq: u64, n_mslope_s1: u64,
    maxratio_m2: f64, maxratio_2mm: f64, argm2: String, arg2mm: String, lastfail_gt_2mm: u64,
}
fn wlist(m: i64, stride: i64) -> Vec<i64> {
    let mut out = Vec::new();
    let top = 6 * m * m;
    for w in (m + 1)..=top {
        let near = (w - m * m).abs() <= 2 * m || (w - 2 * m * (m - 1)).abs() <= 3 * m;
        if w <= 3 * m * m || w % stride == 0 || near { out.push(w); }
    }
    out
}
fn run_base(name: &str, b0: &[i64], ws: Option<Vec<i64>>, stride: i64, st: &mut St, brute_every: u64, quiet: bool) {
    let mut b = b0.to_vec(); b.sort(); b.dedup();
    if b.len() < 2 { return; }
    let m = *b.last().unwrap();
    let l = ml_b(&b);
    let half = l == qn(1, 2);
    if half { st.half_bases += 1; }
    st.bases += 1;
    let p1 = peaks_p1(&b);
    let p2 = peaks_p2(&b, 2 * m);
    if p1 != p2 { st.peak_route_mismatch += 1; st.tension += 1; println!("TENSION peaks P1!=P2 base {}", name); }
    let p4 = peaks_p2(&b, 4 * m);
    if p4.iter().any(|p| p.d > 2 * m - if half { 0 } else { 1 }) { st.l1c_viol += 1; println!("L1C VIOL base {}", name); }
    let pmax = p1.iter().map(|p| mu_of(p)).fold(qi(0), qmax);
    if pmax != l { st.tension += 1; println!("TENSION max peak != L base {} L={} pmax={}", name, fmt(l), fmt(pmax)); }
    let ws = ws.unwrap_or_else(|| wlist(m, stride));
    let mut eqv: Vec<(i64, bool)> = Vec::new();
    let mut counter = 0u64;
    let thr2 = 2 * m * (m - 1);
    for &w in &ws {
        if b.contains(&w) { continue; }
        counter += 1; st.cases += 1;
        let mut v = b.clone(); v.push(w);
        let ml = ml_b(&v);
        if !cert(&v, ml) { st.cert_fail += 1; st.tension += 1; println!("CERT FAIL base {} w={} ml={}", name, w, fmt(ml)); }
        if !cert_ctrl(&v, ml) { st.ctrl_fail += 1; }
        let mut u = qi(0); let mut u_sw = qi(0); let mut u_low = qi(0); let mut u_sg = qi(0); let mut u_one = qi(0); let mut u_ms = qi(0);
        for p in &p1 {
            let mu = mu_of(p); let th = theta_of(p, w);
            let h = hform(mu, th, p.rho as I, p.lam as I, w as I);
            u = qmax(u, h);
            u_sw = qmax(u_sw, hform(mu, th, p.lam as I, p.rho as I, w as I));
            u_sg = qmax(u_sg, hform(mu, qn(-th.n, th.d), p.rho as I, p.lam as I, w as I));
            if mu == l { u_low = qmax(u_low, h); }
            u_one = qmax(u_one, hone(mu, th, p.rho as I, p.lam as I, w as I));
            u_ms = qmax(u_ms, hform(mu, th, m as I, m as I, w as I));
        }
        if brute_every > 0 && counter % brute_every == 0 {
            let mut idx = 0usize;
            for p in p1.iter() { idx += 1; if idx % (1 + p1.len() / 6) != 0 { continue; }
                let mu = mu_of(p); let th = theta_of(p, w);
                let hf = hform(mu, th, p.rho as I, p.lam as I, w as I);
                let hb = h_brute(mu, th, p.rho as I, p.lam as I, w as I);
                st.brute_checked += 1;
                if hf != hb { st.brute_mismatch += 1; println!("BRUTE MISMATCH base {} w={} peak {:?} closed={} brute={}", name, w, p, fmt(hf), fmt(hb)); }
            }
        }
        // S1
        if lt(u, ml) { st.s1_viol += 1; println!("S1 VIOL base {} w={} ml={} U={}", name, w, fmt(ml), fmt(u)); }
        let eq = ml == u;
        eqv.push((w, eq));
        if w >= thr2 { st.s2_cases += 1; if !eq { st.s2_viol += 1; println!("S2 VIOL base {} w={} ml={} U={}", name, w, fmt(ml), fmt(u)); } }
        if w >= m * m { st.s3_cases += 1; if !eq { st.s3_viol += 1; } }
        // S4 LIP
        let lip = div(mul(l, qi(w as I)), qi((w + m) as I));
        if lt(ml, lip) { st.s4_viol += 1; println!("S4 VIOL base {} w={}", name, w); }
        let lip_bad = div(mul(l, qi(w as I)), qi((w + m - 1) as I));
        if lt(ml, lip_bad) { st.s4neg_viol += 1; }
        // negatives
        if lt(u_sw, ml) { st.n_swap_s1 += 1; }
        if lt(u_low, ml) { st.n_low_s1 += 1; }
        if lt(u_sg, ml) { st.n_sign_s1 += 1; }
        if lt(u_one, ml) { st.n_one_s1 += 1; }
        if lt(u_ms, ml) { st.n_mslope_s1 += 1; }
        if w >= thr2 && u_one != ml { st.n_one_eq += 1; }
        if w >= thr2 { st.n_swap_eqcases += 1; if u_sw != ml { st.n_swap_eq += 1; } if u_sg != ml { st.n_sign_eq += 1; } }
        if w < thr2 { st.n_range_cases += 1; if !eq { st.n_range_eq += 1; } }
    }
    // last failure of equality
    let lastfail = eqv.iter().filter(|(_, e)| !*e).map(|(w, _)| *w).max().unwrap_or(0);
    let lastfail_m2 = eqv.iter().filter(|(w, e)| !*e && *w >= m * m).map(|(w, _)| *w).max().unwrap_or(0);
    let r = lastfail as f64 / (m * m) as f64;
    if r > st.maxratio_m2 { st.maxratio_m2 = r; st.argm2 = format!("{} w={} M={}", name, lastfail, m); }
    let r2 = lastfail as f64 / (2 * m * (m - 1)).max(1) as f64;
    if r2 > st.maxratio_2mm { st.maxratio_2mm = r2; st.arg2mm = format!("{} w={} M={}", name, lastfail, m); }
    if lastfail >= thr2 { st.lastfail_gt_2mm += 1; }
    if !quiet || lastfail_m2 > 0 {
        println!("BASE {} B={:?} L={}{} M={} peaks={} ncases={} lastfail_eq={} (=/M^2: {:.3}, /2M(M-1): {:.3}) lastfail_ge_M2={}",
            name, b, fmt(l), if half { "(half)" } else { "" }, m, p1.len(), eqv.len(), lastfail, r, r2, lastfail_m2);
    }
}
fn print_st(st: &St) {
    println!("SUMMARY bases={} (half-class {}) cases={} tension={} cert_fail={} ctrl_fail={} peakroute_mismatch={} lemma1c_viol={}",
        st.bases, st.half_bases, st.cases, st.tension, st.cert_fail, st.ctrl_fail, st.peak_route_mismatch, st.l1c_viol);
    println!("S1 (U) viol={} | S2 eq(w>=2M(M-1)) cases={} viol={} | S3 eq(w>=M^2) cases={} viol={} | S4 LIP viol={} (planted M-1 form violated {} times)",
        st.s1_viol, st.s2_cases, st.s2_viol, st.s3_cases, st.s3_viol, st.s4_viol, st.s4neg_viol);
    println!("H brute-force check: checked={} mismatch={}", st.brute_checked, st.brute_mismatch);
    println!("planted negatives: swap(rho,lam): U<ML in {} cases, U!=ML at w>=2M(M-1) in {} of {}; low-peaks-only: U<ML in {} cases; theta-sign: U<ML in {} cases, U!=ML at w>=2M(M-1) in {}; range(equality claimed for M<w<2M(M-1)) false in {} of {}; one-sided H: U<ML in {} cases, U!=ML at w>=2M(M-1) in {}; all slopes:=M: U<ML in {} cases",
        st.n_swap_s1, st.n_swap_eq, st.n_swap_eqcases, st.n_low_s1, st.n_sign_s1, st.n_sign_eq, st.n_range_eq, st.n_range_cases, st.n_one_s1, st.n_one_eq, st.n_mslope_s1);
    println!("max over bases of lastfail/M^2 = {:.4} at {} ; max lastfail/(2M(M-1)) = {:.4} at {} ; bases with a failure at w>=2M(M-1): {}",
        st.maxratio_m2, st.argm2, st.maxratio_2mm, st.arg2mm, st.lastfail_gt_2mm);
}
fn parse(a: &Vec<String>, i: usize, d: i64) -> i64 { a.get(i).map(|s| s.parse().unwrap()).unwrap_or(d) }

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a.get(1).map(|s| s.as_str()).unwrap_or("");
    match mode {
        "ctrl" => {
            // known values
            let mut ok = true;
            for n in 2..=30i64 { let v: Vec<i64> = (1..=n).collect(); let x = ml_b(&v); if x != qn(1, (n + 1) as I) { ok = false; println!("CTRL FAIL [{}] {}", n, fmt(x)); } if !cert(&v, x) || !cert_ctrl(&v, x) { ok = false; println!("CERT CTRL FAIL [{}]", n); } }
            let known: Vec<(Vec<i64>, Q)> = vec![
                (vec![1, 5, 6, 11, 16, 17], qn(5, 33)), (vec![1, 3, 4, 7], qn(1, 5)),
                (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 36], qn(3, 41)),
                (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 24], qn(1, 14))];
            for (v, x) in known { let y = ml_b(&v); if y != x { ok = false; println!("CTRL FAIL {:?} got {} want {}", v, fmt(y), fmt(x)); } if !cert(&v, y) || !cert_ctrl(&v, y) { ok = false; println!("CERT CTRL FAIL {:?}", v); } }
            // two-speed formula: ML{a,b}=s/(2s+1)?? check only equality of the two routes on all coprime pairs <= 40
            for x in 1..=40i64 { for y in (x + 1)..=40 { let v = vec![x, y]; let r = ml_b(&v); if !cert(&v, r) { ok = false; println!("CERT FAIL pair {:?}", v); } } }
            // false cert must be rejected
            let v = vec![1i64, 2, 3, 4, 5, 6]; if cert(&v, qn(1, 6)) || cert(&v, qn(1, 8)) { ok = false; println!("false value accepted"); }
            println!("CTRL {}", if ok { "ALL PASS" } else { "FAIL" });
        }
        "hform" => {
            // exhaustive local test of the closed form against brute force (no base involved)
            let (mut cnt, mut bad) = (0u64, 0u64);
            for d in 3..=10i128 { for am in 1..=(d / 2) { let mu = qn(am, d);
                for rho in 1..=6i128 { for lam in 1..=6i128 { for w in 1..=40i128 {
                    for r in (-(d / 2) + if d % 2 == 0 { 1 } else { 0 })..=(d / 2) {
                        let th = qn(r, d);
                        let hf = hform(mu, th, rho, lam, w); let hb = h_brute(mu, th, rho, lam, w);
                        cnt += 1; if hf != hb { bad += 1; if bad <= 10 { println!("HFORM MISMATCH mu={} th={} rho={} lam={} w={} closed={} brute={}", fmt(mu), fmt(th), rho, lam, w, fmt(hf), fmt(hb)); } }
                    }
                }}}
            }}
            println!("HFORM cases={} mismatches={}", cnt, bad);
        }
        "fam" => {
            let (nmin, nmax, stride) = (parse(&a, 2, 3), parse(&a, 3, 20), parse(&a, 4, 1));
            let mut st = St::default();
            for n in nmin..=nmax { for r in 1..=n {
                let b: Vec<i64> = (1..=n).filter(|&x| x != r).collect();
                if b.len() < 2 { continue; }
                run_base(&format!("[{}]\\{{{}}}", n, r), &b, None, stride, &mut st, 61, true);
            }}
            print_st(&st);
        }
        "rnd" => {
            let (seed, count, maxs, minsz, maxsz, stride) = (parse(&a, 2, 1) as u64, parse(&a, 3, 200), parse(&a, 4, 50), parse(&a, 5, 2), parse(&a, 6, 7), parse(&a, 7, 7));
            let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
            let mut st = St::default();
            let mut gcd_gt1 = 0;
            for it in 0..count {
                let sz = minsz + rng.below((maxsz - minsz + 1) as u64) as i64;
                let g = if rng.below(100) < 18 { 2 + rng.below(3) as i64 } else { 1 };
                if g > 1 { gcd_gt1 += 1; }
                let mut set = BTreeSet::new();
                let top = maxs / g;
                let mut tries = 0;
                while (set.len() as i64) < sz && tries < 1000 { set.insert(g * (1 + rng.below(top as u64) as i64)); tries += 1; }
                let b: Vec<i64> = set.into_iter().collect();
                if b.len() < 2 { continue; }
                run_base(&format!("rnd{}", it), &b, None, stride, &mut st, 53, true);
            }
            println!("random bases generated={} with gcd-forced>1: {}", count, gcd_gt1);
            print_st(&st);
        }
        "gw" => {
            let nmax = parse(&a, 2, 18); let stride = parse(&a, 3, 3);
            let mut st = St::default();
            for np in 3..=nmax { for r in 1..=np { for m in 2..=6i64 {
                if m * r <= np { continue; }
                let mut b: Vec<i64> = (1..=np).filter(|&x| x != r).collect(); b.push(m * r);
                run_base(&format!("GW[{}]\\{{{}}}+{}", np, r, m * r), &b, None, stride, &mut st, 41, true);
            }}}
            print_st(&st);
        }
        "spor" => {
            let sets: Vec<Vec<i64>> = vec![vec![1, 5, 6, 11, 16, 17], vec![1, 3, 4, 5, 7, 13, 18], vec![1, 3, 4, 7], vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 36],
                vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 24], vec![1, 3, 4, 5, 6, 7, 9, 12, 17], vec![2, 3, 5, 7, 11, 13], vec![1, 4, 6, 7, 9, 10]];
            let mut st = St::default();
            for s in sets {
                run_base(&format!("{:?}", s), &s, None, 3, &mut st, 31, true);
                for i in 0..s.len() { let mut t = s.clone(); t.remove(i); if t.len() >= 2 { run_base(&format!("{:?}-del{}", s, i), &t, None, 3, &mut st, 31, true); } }
            }
            print_st(&st);
        }
        "m1" => {
            // B={1,M}: last failing w of equality; compare with M(M-4)
            let mmax = parse(&a, 2, 60);
            let mut st = St::default();
            for m in 2..=mmax {
                run_base(&format!("{{1,{}}}", m), &[1, m], Some(((m + 1)..=(6 * m * m)).collect()), 1, &mut st, 0, false);
            }
            print_st(&st);
        }
        "d1" => d1(&a),
        "d3" => d3(),
        "d5" => d5(&a),
        "d2" => d2(&a),
        "pp" => pp(&a),
        _ => println!("modes: ctrl hform fam nmin nmax stride | rnd seed count maxs minsz maxsz stride | gw nmax stride | spor | m1 mmax | d1 seed count | d3 | d5 N"),
    }
}

// ---------------- D1: descent test ----------------
fn d1(a: &Vec<String>) {
    let (seed, count) = (parse(a, 2, 1) as u64, parse(a, 3, 300));
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    let (mut inst, mut viol_hi, mut viol_2m2, mut nfail_any) = (0u64, 0u64, 0u64, 0u64);
    let mut maxratio = 0f64; let mut arg = String::new();
    let mut maxratio_half = 0f64;
    let mut neg_hi = 0u64;
    let mut done = 0;
    while done < count {
        let sz = 2 + rng.below(6) as i64; // |B| = N-1 in 2..7, N = 3..8
        let n = sz + 1;
        let maxs = 14 + rng.below(30) as i64;
        let g = if rng.below(100) < 15 { 2 + rng.below(2) as i64 } else { 1 };
        let mut set = BTreeSet::new(); let mut tries = 0;
        while (set.len() as i64) < sz && tries < 500 { set.insert(g * (1 + rng.below((maxs / g) as u64) as i64)); tries += 1; }
        let b: Vec<i64> = set.into_iter().collect(); if b.len() as i64 != sz { continue; }
        let m = *b.last().unwrap();
        let l = ml_b(&b);
        // claim concerns bases with L > 1/N  (L >= 1/N by LRC(N-1), known for sz <= 12)
        if !lt(qn(1, n as I), l) { continue; }
        done += 1;
        let c = qn(1, n as I);
        let w_hi = (2 * m - 1) * m; let w_2 = 2 * m * m;
        // least failing: scan all w in (M, 2*w_2]
        let mut lastfail = 0i64; let mut nf = 0;
        for w in (m + 1)..=(w_2 + 2 * m) {
            if b.contains(&w) { continue; }
            let mut v = b.clone(); v.push(w);
            let lt_c = !exists_cmp(&v, c, false); // ML(V) < 1/N
            if lt_c { lastfail = w; nf += 1; if w >= w_hi { viol_hi += 1; println!("D1 VIOL (w>=(2M-1)M) B={:?} N={} w={}", b, n, w); } if w >= w_2 { viol_2m2 += 1; } }
            // planted negative: claim descent already for w >= M(M-1)... count failures there
            if w >= m * (m - 1) && w < w_hi && lt_c { neg_hi += 1; }
        }
        inst += 1; if nf > 0 { nfail_any += 1; }
        let r = lastfail as f64 / (m * m) as f64;
        if r > maxratio { maxratio = r; arg = format!("B={:?} N={} lastfail={} M={}", b, n, lastfail, m); }
        if m > 0 && lastfail as f64 / ((2 * m - 1) * m) as f64 > maxratio_half { maxratio_half = lastfail as f64 / ((2 * m - 1) * m) as f64; }
    }
    println!("D1 instances (B, L>1/N)={} ; with some failing w (ML(V)<1/N): {} ; violations at w>=(2M-1)M: {} ; at w>=2M^2: {}", inst, nfail_any, viol_hi, viol_2m2);
    println!("D1 least constant c with no failure beyond c*M^2 (sup over instances of lastfail/M^2) = {:.4} at {} ; sup lastfail/((2M-1)M) = {:.4} ; planted-negative claim 'descent for w>=M(M-1)' false in {} (w,B) cases", maxratio, arg, maxratio_half, neg_hi);
}
// ---------------- D3: tight N-sets, max <= N * second largest ----------------
fn d3() {
    let plan: Vec<(usize, i64)> = vec![(3, 120), (4, 60), (5, 40), (6, 30), (7, 26), (8, 22)];
    for (n, mx) in plan {
        let thr = qn(1, (n + 1) as I);
        let mut idx: Vec<i64> = (1..=(n as i64)).collect();
        let (mut tight, mut viol, mut lrc_viol) = (0u64, 0u64, 0u64);
        let mut sup = 0f64; let mut sarg = String::new(); let mut viol_neg = 0u64; let mut total = 0u64;
        loop {
            total += 1;
            if !exists_cmp(&idx, thr, true) {
                tight += 1;
                let x = ml_b(&idx); if x != thr { lrc_viol += 1; println!("D3 LRC-or-engine anomaly {:?} ML={}", idx, fmt(x)); }
                let w = idx[n - 1]; let m = idx[n - 2];
                let r = w as f64 / m as f64;
                if r > sup { sup = r; sarg = format!("{:?}", idx); }
                if w > (n as i64) * m { viol += 1; println!("D3 VIOL {:?}", idx); }
                if w > (n as i64 - 1) * m { viol_neg += 1; }
            }
            // next combination
            let mut i = n as i64 - 1;
            while i >= 0 && idx[i as usize] == mx - (n as i64 - 1 - i) { i -= 1; }
            if i < 0 { break; }
            idx[i as usize] += 1; for j in (i as usize + 1)..n { idx[j] = idx[j - 1] + 1; }
        }
        println!("D3 N={} sets<= {} : {} enumerated, tight={} ; violations of max<=N*second: {} ; sup w/second = {:.4} at {} ; planted claim max<=(N-1)*second false for {} ; anomalies {}", n, mx, total, tight, viol, sup, sarg, viol_neg, lrc_viol);
    }
}
// ---------------- D5: GW tight base + N sigma ----------------
fn d5(a: &Vec<String>) {
    let n = parse(a, 2, 20);
    let mrcap = parse(a, 3, 100);
    let (mut inst, mut ok, mut bad) = (0u64, 0u64, 0u64);
    for r in 1..n { for m in 2..=12i64 {
        let mr = m * r; if mr <= n - 1 || mr > mrcap { continue; }
        let mut b: Vec<i64> = (1..n).filter(|&x| x != r).collect(); b.push(mr); b.sort();
        let l = ml_b(&b);
        if l != qn(1, n as I) { continue; }
        inst += 1;
        let mm = *b.last().unwrap();
        let s0 = (2 * mm * mm + n - 1) / n;
        let peaks = peaks_p1(&b);
        let mut res = String::new();
        let mut allok = true;
        for sg in [s0, s0 + 1, s0 + 2, s0 + 7, 2 * s0] {
            let w = n * sg; let mut v = b.clone(); v.push(w);
            let x = ml_b(&v);
            let want = qn(sg as I, (n * sg + 1) as I);
            let mut u = qi(0);
            for p in &peaks { u = qmax(u, hform(mu_of(p), theta_of(p, w), p.rho as I, p.lam as I, w as I)); }
            let c = cert(&v, x);
            let good = x == want && u == x && c;
            if !good { allok = false; res.push_str(&format!(" FAIL(sigma={} ml={} want={} U={} cert={})", sg, fmt(x), fmt(want), fmt(u), c)); }
        }
        // threshold scan below: smallest sigma0' such that equality holds for all sigma in [sigma0', s0] (full scan if cheap)
        let mut lastfail = 0i64;
        let scan_max = s0;
        let step = if n * scan_max <= 60000 { 1 } else { (scan_max / 400).max(1) };
        let mut sg = 1; while sg <= scan_max { let w = n * sg; let mut v = b.clone(); v.push(w); let x = ml_b(&v); if x != qn(sg as I, (n * sg + 1) as I) { lastfail = sg; } sg += step; }
        if allok { ok += 1; } else { bad += 1; }
        println!("D5 N={} r={} m={} B-max={} 2M^2={} sigma0={} {} ; last failing sigma (scan step {}) = {} (w/2M^2 = {:.3}){}", n, r, m, mm, 2 * mm * mm, s0, if allok { "OK" } else { "BAD" }, step, lastfail, (n * lastfail) as f64 / (2 * mm * mm) as f64, res);
    }}
    println!("D5 N={} tight GW bases tested={} ok={} bad={}", n, inst, ok, bad);
}

// ---------------- D2: ML(V)<1/N  <=>  ML(B)<=1/N and ||w p||<1/N at every p with f_B(p)=1/N, for w >= (2M-1)M ----------------
fn d2(a: &Vec<String>) {
    let nmax = parse(a, 2, 14);
    let (mut cases, mut mism, mut lhs_true, mut neg_mism) = (0u64, 0u64, 0u64, 0u64);
    for n in 4..=nmax {
        let c = qn(1, n as I);
        let mut bases: Vec<Vec<i64>> = vec![(1..n).collect()];
        for r in 1..n { for m in 2..=8i64 { let mr = m * r; if mr <= n - 1 { continue; } let mut b: Vec<i64> = (1..n).filter(|&x| x != r).collect(); b.push(mr); b.sort(); bases.push(b); } }
        for b in bases {
            if ml_b(&b) != c { continue; }
            let m = *b.last().unwrap();
            let peaks: Vec<Peak> = peaks_p1(&b).into_iter().filter(|p| mu_of(p) == c).collect();
            let w0 = (2 * m - 1) * m;
            for w in w0..(w0 + 2 * n + 3) {
                if b.contains(&w) { continue; }
                let mut v = b.clone(); v.push(w);
                let lhs = !exists_cmp(&v, c, false);
                let rhs = peaks.iter().all(|p| lt(nid(add(qi(0), mul(qi(w as I), qn(p.k as I, p.d as I)))), c));
                // planted negative: weaker condition "||wp||<=1/N" (non-strict) must be wrong sometimes
                let rhs_neg = peaks.iter().all(|p| le(nid(mul(qi(w as I), qn(p.k as I, p.d as I))), c));
                cases += 1; if lhs { lhs_true += 1; }
                if lhs != rhs { mism += 1; println!("D2 MISMATCH B={:?} N={} w={} lhs={} rhs={}", b, n, w, lhs, rhs); }
                if lhs != rhs_neg { neg_mism += 1; }
            }
        }
    }
    println!("D2 cases={} (lhs ML(V)<1/N true in {}) mismatches={} ; planted non-strict variant mismatches={}", cases, lhs_true, mism, neg_mism);
}

// ---------------- PP: per-peak lower bound  ML(B u {w}) >= H_p(w) whenever w >= (d_p - 1) M ----------------
fn pp_base(b0: &[i64], st: &mut [u64; 6], stride: i64, worst: &mut (f64, String)) {
    let mut b = b0.to_vec(); b.sort(); b.dedup();
    if b.len() < 2 { return; }
    let m = *b.last().unwrap();
    let peaks = peaks_p1(&b);
    for w in wlist(m, stride) {
        if b.contains(&w) { continue; }
        let mut v = b.clone(); v.push(w);
        let ml = ml_b(&v);
        for p in &peaks {
            let h = hform(mu_of(p), theta_of(p, w), p.rho as I, p.lam as I, w as I);
            if w >= (p.d - 1) * m { st[0] += 1; if lt(ml, h) { st[1] += 1; println!("PP VIOL B={:?} w={} peak={:?} ml={} H={}", b, w, p, fmt(ml), fmt(h)); } }
            // planted negative: threshold divided by 6
            if w >= (p.d - 1) * m / 6 && w < (p.d - 1) * m { st[2] += 1; if lt(ml, h) { st[3] += 1;
                let r = w as f64 / ((p.d - 1) * m) as f64; // how far below the threshold a failure occurs
                if worst.0 == 0.0 || r < worst.0 { *worst = (r, format!("B={:?} w={} d={} M={}", b, w, p.d, m)); } } }
            // tighter claimed threshold for the maximizing peaks only is not tested here
            if p.d <= 2 * m { st[4] += 1; }
        }
    }
    st[5] += 1;
}
fn pp(a: &Vec<String>) {
    let nmax = parse(a, 2, 16); let nrnd = parse(a, 3, 400);
    let mut st = [0u64; 6]; let mut worst = (0f64, String::new());
    for n in 3..=nmax { for r in 1..=n { let b: Vec<i64> = (1..=n).filter(|&x| x != r).collect(); pp_base(&b, &mut st, 1, &mut worst); } }
    let mut rng = Rng(424242);
    for _ in 0..nrnd {
        let sz = 2 + rng.below(6) as i64; let g = if rng.below(100) < 18 { 2 + rng.below(3) as i64 } else { 1 };
        let mut set = BTreeSet::new(); let mut tries = 0;
        while (set.len() as i64) < sz && tries < 500 { set.insert(g * (1 + rng.below((40 / g) as u64) as i64)); tries += 1; }
        let b: Vec<i64> = set.into_iter().collect(); pp_base(&b, &mut st, 1, &mut worst);
    }
    println!("PP bases={} (peak,w) pairs with w>=(d-1)M: {} violations: {} ; planted threshold/6 pairs: {} violated: {} (smallest w/((d-1)M) at a violation: {:.3} at {}) ", st[5], st[0], st[1], st[2], st[3], worst.0, worst.1);
}
