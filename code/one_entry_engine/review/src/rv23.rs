// rv23: own exact-integer review engine. Independent of pf.rs/pf2.rs/bq23.rs (never read).
// ML(V) = max over t=k/(u+v), u<v in V, of exact integer min_x ||x t||  (local maxima of value<1/2 have this form).
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::env;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn gcd128(a: i128, b: i128) -> i128 { if b == 0 { a } else { gcd128(b, a % b) } }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Fr { n: u64, d: u64 }
fn fr(n: u64, d: u64) -> Fr { let g = gcd(n, d).max(1); Fr { n: n / g, d: d / g } }
fn fcmp(a: Fr, b: Fr) -> Ordering { ((a.n as u128) * (b.d as u128)).cmp(&((b.n as u128) * (a.d as u128))) }
fn fgt(a: Fr, b: Fr) -> bool { fcmp(a, b) == Ordering::Greater }
fn fge(a: Fr, b: Fr) -> bool { fcmp(a, b) != Ordering::Less }
fn feq(a: Fr, b: Fr) -> bool { fcmp(a, b) == Ordering::Equal }
fn flt(a: Fr, b: Fr) -> bool { fcmp(a, b) == Ordering::Less }

fn qset(v: &[u64]) -> Vec<u64> {
    let mut q = Vec::new();
    for i in 0..v.len() { for j in i + 1..v.len() { q.push(v[i] + v[j]); } }
    q.sort(); q.dedup(); q
}
// min distance numerator at t=k/q, early exit if value < thr (strictly). returns None if rejected.
#[inline]
fn minm(v: &[u64], k: u64, q: u64, thr: Option<Fr>) -> Option<u64> {
    let mut mm = q;
    for &x in v {
        let r = (x * k) % q;
        let m = r.min(q - r);
        if m < mm {
            mm = m;
            if let Some(b) = thr {
                if (mm as u128) * (b.d as u128) < (b.n as u128) * (q as u128) { return None; }
            }
        }
    }
    Some(mm)
}
fn ml_exact(v: &[u64]) -> Fr {
    let qs = qset(v);
    let mut best: Option<Fr> = None;
    for &q in &qs {
        for k in 1..=(q / 2) {
            if let Some(m) = minm(v, k, q, best) {
                let c = fr(m, q);
                if best.map_or(true, |b| fgt(c, b)) { best = Some(c); }
            }
        }
    }
    best.unwrap()
}
// visit all candidates with value >= thr: (k,q,m)
fn scan<F: FnMut(u64, u64, u64)>(v: &[u64], thr: Fr, mut f: F) {
    let qs = qset(v);
    for &q in &qs {
        for k in 1..=(q / 2) {
            if let Some(m) = minm(v, k, q, Some(thr)) { f(k, q, m); }
        }
    }
}
fn is_local_max(v: &[u64], k: u64, q: u64, m: u64) -> bool {
    if 2 * m >= q || m == 0 { return false; }
    let (mut p, mut mi) = (false, false);
    for &x in v {
        let r = (x * k) % q;
        if r == m { p = true; }
        if q - r == m { mi = true; }
    }
    p && mi
}
fn modinv(a: u64, m: u64) -> u64 { // a coprime m, m>=1
    if m == 1 { return 0; }
    let (mut t, mut nt, mut r, mut nr) = (0i128, 1i128, m as i128, (a % m) as i128);
    while nr != 0 { let qq = r / nr; let tt = t - qq * nt; t = nt; nt = tt; let rr = r - qq * nr; r = nr; nr = rr; }
    ((t % m as i128 + m as i128) % m as i128) as u64
}
fn base(n: u64, r: u64) -> Vec<u64> { (1..=n).filter(|&x| x != r).collect() }
fn d0d1(n: u64, r: u64) -> (u64, u64) {
    let mut d = n + 1 + r; while gcd(d, r) != 1 { d += 1; }
    let d0 = d; d += 1; while gcd(d, r) != 1 { d += 1; }
    (d0, d)
}
fn with_w(b: &[u64], ws: &[u64]) -> Vec<u64> {
    let mut v = b.to_vec(); for &w in ws { v.push(w); } v.sort(); v.dedup(); v
}

// ---- controls ----
fn ctl() {
    for n in 3..=22u64 { let v: Vec<u64> = (1..=n).collect(); assert!(feq(ml_exact(&v), fr(1, n + 1)), "ML[N] {}", n); }
    assert!(feq(ml_exact(&[1, 3, 4, 7]), fr(1, 5)));
    assert!(feq(ml_exact(&[1, 5, 6, 11, 16, 17]), fr(5, 33)));
    // Zhang Example 5.2: (73;70,72;140,144) -> 1/74 : set = [73]\{70,72} u {140,144}
    let v = with_w(&(1..=73u64).filter(|&x| x != 70 && x != 72).collect::<Vec<_>>(), &[140, 144]);
    assert!(feq(ml_exact(&v), fr(1, 74)), "zhang52 {:?}", ml_exact(&v));
    // float grid cross check on random sets
    let mut s: u64 = 88172645463325252;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
    let mut bad = 0; let mut tot = 0;
    for _ in 0..300 {
        let n = 3 + (rnd() % 6) as usize;
        let mut v: Vec<u64> = (0..n).map(|_| 1 + rnd() % 40).collect();
        if rnd() % 3 == 0 { v.push(200 + rnd() % 800); }
        v.sort(); v.dedup();
        if v.len() < 2 { continue; }
        let ex = ml_exact(&v);
        let exf = ex.n as f64 / ex.d as f64;
        if exf >= 0.5 - 1e-12 { continue; } // engine assumes < 1/2
        let steps = 4_000_000u64; let mut gm = 0f64;
        for i in 0..=steps / 2 { let t = i as f64 / steps as f64; let mut m = 1f64; for &x in &v { let y = (x as f64 * t) % 1.0; let d = y.min(1.0 - y); if d < m { m = d; } } if m > gm { gm = m; } }
        tot += 1;
        if gm > exf + 1e-9 || exf > gm + 1e-5 { bad += 1; println!("GRIDDIFF {:?} exact {} grid {}", v, exf, gm); }
    }
    println!("ctl: all asserts passed; grid cross-check {} sets, {} disagreements", tot, bad);
    assert!(bad == 0);
}

// ---- Plan 3 structure (a)-(e) ----
fn p3(n0: u64, n1: u64) {
    let (mut cases, mut fail) = (0u64, 0u64);
    let mut pl = [0u64; 12]; let mut pl_tot = [0u64; 12];
    let mut r1_cnt = 0; let mut d1_big = 0; let mut half_cnt = 0;
    for n in n0..=n1 {
        let a = n + 1;
        for r in 1..=n / 2 {
            cases += 1;
            let b = base(n, r);
            let (d0, d1) = d0d1(n, r);
            let mut ok = true;
            let mut note = String::new();
            // (a)
            if !(d0 >= n + 1 + r && d0 <= n + 2 * r && gcd(d0, r) == 1 && d0 <= 2 * n - 1 && 2 * d0 > 4) { ok = false; note += " a"; }
            let l = fr(2, d0);
            // (b)
            let ml = ml_exact(&b);
            if !feq(ml, l) { ok = false; note += " b"; }
            // (c) equality times
            let mut eq: BTreeSet<(u64, u64)> = BTreeSet::new();
            scan(&b, l, |k, q, m| { if fcmp(fr(m, q), l) == Ordering::Equal { let g = gcd(k, q); eq.insert((k / g, q / g)); } });
            let kk = modinv(r, d0);
            let want: BTreeSet<(u64, u64)> = { let mut s = BTreeSet::new(); let k2 = kk.min(d0 - kk); s.insert((k2, d0)); s };
            if eq != want { ok = false; note += " c"; }
            // (d) slopes at both t0=kk/D0 and -t0
            let mut vmu = u64::MAX; let mut slope_ok = true;
            for &(kq, sgn) in &[(kk, 0), (d0 - kk, 1)] {
                let mut rho = 0; let mut lam = 0;
                for &x in &b { let rr = (x * kq) % d0; if rr == 2 { rho = rho.max(x); } if d0 - rr == 2 { lam = lam.max(x); } }
                let (er, el) = if sgn == 0 { (2 * r, d0 - 2 * r) } else { (d0 - 2 * r, 2 * r) };
                if rho != er || lam != el { slope_ok = false; }
                vmu = vmu.min(rho.min(lam));
            }
            if !slope_ok { ok = false; note += " d1"; }
            let vclaim = (2 * r).min(d0 - 2 * r);
            if vmu != vclaim { ok = false; note += " d2"; }
            // planted negatives on vmu
            for (i, cand) in [vclaim + 1, vclaim.saturating_sub(1), (2 * r).max(d0 - 2 * r), r].iter().enumerate() {
                pl_tot[i] += 1; if *cand != vmu { pl[i] += 1; }
            }
            // (e) local maxima values >= 1/(N+1)
            let thr = fr(1, a);
            let mut vals: BTreeSet<(u64, u64)> = BTreeSet::new();
            scan(&b, thr, |k, q, m| { if is_local_max(&b, k, q, m) { let f = fr(m, q); vals.insert((f.n, f.d)); } });
            let mut want_hi: BTreeSet<(u64, u64)> = BTreeSet::new();
            for d in (n + r + 1)..=(n + 2 * r) { if gcd(d, r) == 1 { let f = fr(2, d); want_hi.insert((f.n, f.d)); } }
            let have_hi: BTreeSet<(u64, u64)> = vals.iter().cloned().filter(|&(x, y)| fgt(Fr { n: x, d: y }, thr)).collect();
            if have_hi != want_hi { ok = false; note += " e1"; }
            let have_thr = vals.contains(&(1, a));
            if !have_thr { ok = false; note += " e2(1/(N+1) not local max)"; }
            // L2 from data
            let mut l2 = Fr { n: 0, d: 1 };
            for &(x, y) in &vals { let f = Fr { n: x, d: y }; if flt(f, l) && fgt(f, l2) { l2 = f; } }
            let l2claim = if d1 <= n + 2 * r { fr(2, d1) } else { fr(1, a) };
            if !feq(l2, l2claim) { ok = false; note += " e3"; }
            // planted negatives on L2
            let plant = [fr(2, d0 + 1), fr(1, a), fr(2, d1)];
            let tr = [d1 != d0 + 1, d1 <= n + 2 * r, d1 > n + 2 * r]; // is the plant genuinely different from the claim?
            for (i, p) in plant.iter().enumerate() {
                if !feq(*p, l2claim) { pl_tot[4 + i] += 1; if !feq(*p, l2) { pl[4 + i] += 1; } }
                let _ = tr[i];
            }
            if r == 1 { r1_cnt += 1; }
            if d1 > n + 2 * r { d1_big += 1; }
            if 2 * r == n { half_cnt += 1; }
            if !ok { fail += 1; println!("FAIL N={} r={} D0={} D1={}{}", n, r, d0, d1, note); }
        }
    }
    println!("p3 N={}..{}: cases {} fail {} (r=1: {}, D1>N+2r: {}, r=N/2: {})", n0, n1, cases, fail, r1_cnt, d1_big, half_cnt);
    println!("planted vmu(+1,-1,max,r) detected/total: {}/{} {}/{} {}/{} {}/{}", pl[0], pl_tot[0], pl[1], pl_tot[1], pl[2], pl_tot[2], pl[3], pl_tot[3]);
    println!("planted L2 (2/(D0+1), 1/(N+1)always, 2/D1always) detected/total (only where plant differs from claim): {}/{} {}/{} {}/{}", pl[4], pl_tot[4], pl[5], pl_tot[5], pl[6], pl_tot[6]);
}

// Lemma A on grid: f_B(t) for t=(c+eta)/r, eta=j/(6A)
fn lemma_a(n0: u64, n1: u64) {
    let (mut tot, mut fail, mut pl, mut pl_tot) = (0u64, 0u64, 0u64, 0u64);
    for n in n0..=n1 {
        let a = n + 1;
        for r in 1..=n / 2 {
            let b = base(n, r);
            for c in 0..r.max(1) {
                if r >= 2 && (c == 0 || gcd(c, r) != 1) { continue; }
                let cc = if r == 1 { 0 } else { c };
                // X
                let x = if r == 1 { n } else {
                    let u = (1..r).find(|&u| (u * cc) % r == r - 1).unwrap();
                    let mut x = n; while x % r != u % r { x -= 1; } x };
                for j in 0..=6u64 {
                    let q = 6 * a * r; let p = cc * 6 * a + j; // t = p/q
                    let mut m = q; for &v in &b { let rr = (v * p) % q; m = m.min(rr.min(q - rr)); }
                    let form = (2 * j * r).min(6 * a - x * j); // both over q (6 a r): 2 eta*q=2j r ; (1-X eta)/r *q = (6a - X j)
                    tot += 1; if m != form { fail += 1; if fail < 5 { println!("LEMMA A FAIL n={} r={} c={} j={} m={} form={}", n, r, cc, j, m, form); } }
                    if r >= 2 && x > r { pl_tot += 1; let form2 = (2 * j * r).min(6 * a - (x - r) * j); if m != form2 { pl += 1; } }
                }
            }
        }
    }
    println!("lemmaA N={}..{} grid: {} points fail {}; planted X-r detected {}/{}", n0, n1, tot, fail, pl, pl_tot);
}

// ---- V1 ----
fn v1(n0: u64, n1: u64) {
    let (mut tot_e, mut f_e, mut tot_u, mut f_u, mut tot_l, mut f_l) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut below, mut below_ne) = (0u64, 0u64); let (mut pl, mut pl_tot) = ([0u64; 3], [0u64; 3]);
    let mut thr_leq = 0u64; let mut pairs = 0u64; let mut r12 = 0u64;
    for n in n0..=n1 {
        let a = n + 1;
        for r in 1..=n / 2 {
            pairs += 1; if r <= 2 { r12 += 1; }
            let b = base(n, r);
            let (d0, d1) = d0d1(n, r);
            let x0 = d0 - 2 * r; let v = (2 * r).min(x0);
            let delta = if d1 <= n + 2 * r { d1 - d0 } else { 2 * n + 2 - d0 };
            let wthr = (2 * n - v.min(2 * n)).max((v * d0 + delta - 1) / delta); // max(2N - v, ceil(v D0/Delta))
            if wthr <= 2 * n * n { thr_leq += 1; } else { println!("THR>2N^2 N={} r={} wthr={}", n, r, wthr); }
            let l2 = if d1 <= n + 2 * r { fr(2, d1) } else { fr(1, a) };
            let mthr = (wthr + d0 - 1) / d0;
            let mut ms: Vec<u64> = vec![1, 2, mthr.saturating_sub(1).max(1), mthr, mthr + 1, mthr + 2, (mthr + 1) / 2 + 1];
            if n <= 40 { ms.push((2 * n * n * n + d0 - 1) / d0); }
            ms.sort(); ms.dedup();
            for m in ms {
                let w = m * d0;
                let vs = with_w(&b, &[w]);
                let ml = ml_exact(&vs);
                let k = fr(2 * w, d0 * (w + v));
                // (U)
                let mx = if fgt(k, l2) { k } else { l2 };
                tot_u += 1; if fgt(ml, mx) { f_u += 1; println!("U FAIL N={} r={} w={}", n, r, w); }
                // (L) cond w+v >= 2N
                if w + v >= 2 * n { tot_l += 1; if flt(ml, k) { f_l += 1; println!("L FAIL N={} r={} w={}", n, r, w); } }
                if w >= wthr {
                    tot_e += 1; if !feq(ml, k) { f_e += 1; println!("E FAIL N={} r={} w={} ml={:?} k={:?}", n, r, w, ml, k); }
                    for (i, vv) in [v + 1, v - 1, (2 * r).max(x0)].iter().enumerate() {
                        let kp = fr(2 * w, d0 * (w + vv)); if !feq(kp, k) { pl_tot[i] += 1; if !feq(ml, kp) { pl[i] += 1; } }
                    }
                } else { below += 1; if !feq(ml, k) { below_ne += 1; } }
            }
        }
    }
    println!("v1 N={}..{}: pairs {} (r<=2: {}), wthr<=2N^2 in {}; (U) {} fail {}; (L) {} fail {}; (E, w>=wthr) {} fail {}", n0, n1, pairs, r12, thr_leq, tot_u, f_u, tot_l, f_l, tot_e, f_e);
    println!("below threshold: {} multiples tested, ML != K in {}; planted v+1,v-1,max detected/total {}/{} {}/{} {}/{}", below, below_ne, pl[0], pl_tot[0], pl[1], pl_tot[1], pl[2], pl_tot[2]);
}

// ---- Proposition G ----
fn pg(n0: u64, n1: u64, mult: u64) {
    let mut s: u64 = 0x9E3779B97F4A7C15;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
    let (mut tot, mut fl, mut fu, mut below, mut below_f, mut wr_cases, mut wr_f) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut maxg = 0f64; let mut gle3n = 0u64; let mut pairs = 0u64; let mut pl = (0u64, 0u64);
    for n in n0..=n1 {
        let a = n + 1;
        for r in 1..=n / 2 {
            pairs += 1;
            let b = base(n, r);
            let (d0, _) = d0d1(n, r);
            let x0 = d0 - 2 * r;
            // w_G = ceil( 4r(2rA - X0(D0-A)) / (D0 (D0-A)) )
            let num = 4 * (r as i128) * (2 * (r as i128) * (a as i128) - (x0 as i128) * ((d0 - a) as i128));
            let den = (d0 as i128) * ((d0 - a) as i128);
            let wg = if num <= 0 { 1i128 } else { (num + den - 1) / den };
            let wg = wg.max(1) as u64;
            if (wg as f64) / (n as f64) > maxg { maxg = wg as f64 / n as f64; }
            if wg <= 3 * n { gle3n += 1; } else { println!("wG>3N N={} r={} wG={}", n, r, wg); }
            let l = fr(2, d0);
            let mut ws: Vec<u64> = (1..=mult * n).collect();
            for _ in 0..12 { ws.push(mult * n + 1 + rnd() % (40 * n)); }
            for w in ws {
                let vs = with_w(&b, &[w]);
                let ml = ml_exact(&vs);
                // tau = 2w/(w D0 + 4 r X0)
                let tau = fr(2 * w, w * d0 + 4 * r * x0);
                let in_scope = w >= wg;
                if w == r { wr_cases += 1; if in_scope && flt(ml, tau) { wr_f += 1; println!("w=r VIOLATION N={} r={} wG={}", n, r, wg); } }
                if in_scope {
                    tot += 1;
                    if flt(ml, tau) { fl += 1; println!("G LOWER FAIL N={} r={} w={} ml={:?} tau={:?}", n, r, w, ml, tau); }
                    if fgt(ml, l) { fu += 1; println!("G UPPER FAIL N={} r={} w={}", n, r, w); }
                    // planted: claim ML >= L (strict improvement) is false when w not multiple... count refutations
                    pl.1 += 1; if flt(ml, l) { pl.0 += 1; }
                } else { below += 1; if flt(ml, tau) { below_f += 1; } }
            }
        }
    }
    println!("pg N={}..{} pairs {} w in [1,{}N]+12 random: in-scope(w>=wG) {} lowerfail {} upperfail {}; w<wG {} of which lower bound fails {}; w=r cases {} violations {}; wG<=3N in {}/{} pairs, max wG/N {:.3}; planted 'ML>=L' refuted {}/{}", n0, n1, pairs, mult, tot, fl, fu, below, below_f, wr_cases, wr_f, gle3n, pairs, maxg, pl.0, pl.1);
}

// ---- Plan 2 ----
#[derive(Clone, Copy, Debug)]
struct R { n: i128, d: i128 }
fn rr(n: i128, d: i128) -> R { let (mut n, mut d) = (n, d); if d < 0 { n = -n; d = -d; } let g = gcd128(n.abs(), d).max(1); R { n: n / g, d: d / g } }
impl R {
    fn add(self, o: R) -> R { rr(self.n * o.d + o.n * self.d, self.d * o.d) }
    fn sub(self, o: R) -> R { rr(self.n * o.d - o.n * self.d, self.d * o.d) }
    fn mul(self, o: R) -> R { rr(self.n * o.n, self.d * o.d) }
    fn div(self, o: R) -> R { rr(self.n * o.d, self.d * o.n) }
    fn cmp(self, o: R) -> Ordering { (self.n * o.d).cmp(&(o.n * self.d)) }
    fn lt(self, o: R) -> bool { self.cmp(o) == Ordering::Less }
    fn gt(self, o: R) -> bool { self.cmp(o) == Ordering::Greater }
    fn eq(self, o: R) -> bool { self.cmp(o) == Ordering::Equal }
    fn zero(self) -> bool { self.n == 0 }
}
fn rmin(a: R, b: R) -> R { if a.lt(b) { a } else { b } }
fn rmax(a: R, b: R) -> R { if a.gt(b) { a } else { b } }
fn saw(w: i128, c: i128, r: i128, eta: R) -> R {
    // || w (c+eta)/r ||, eta = p/q
    let nn = w * (c * eta.d + eta.n); let dd = r * eta.d;
    let rem = ((nn % dd) + dd) % dd; rr(rem.min(dd - rem), dd)
}
// X for entry i, unit c: variants: mode 0 normal (largest in [N] in class), 1: X-r (planted), 3: largest retained (exclude removed set)
fn xclass(n: u64, r: u64, c: u64, excl: &[u64], mode: u8) -> Option<u64> {
    let u = (1..r).find(|&u| (u * c) % r == r - 1).unwrap();
    let mut x = n; while x % r != u % r { x -= 1; }
    if mode == 1 { return if x > r { Some(x - r) } else { None }; }
    if mode == 3 { while x >= 1 && excl.contains(&x) { if x <= r { return None; } x -= r; } if x < 1 { return None; } }
    Some(x)
}
fn e_arc(a: u64, r: u64, c: u64, x: u64, ws: &[u64; 2], pairs_excl: bool) -> R {
    let _ = pairs_excl;
    let (a_, r_, c_, x_) = (a as i128, r as i128, c as i128, x as i128);
    let top = rr(1, a_);
    let mut pts = vec![rr(0, 1), top];
    for &w in ws {
        let w = w as i128;
        // y = w(c+eta)/r in (1/2)Z, eta=(m r - 2 w c)/(2 w), need 0<eta<1/A
        let lo = (2 * w * c_) / r_ + 1; // m > 2wc/r
        let hi = (2 * w * (c_ * a_ + 1) + r_ * a_ - 1) / (r_ * a_) + 1;
        for m in lo..=hi { let eta = rr(m * r_ - 2 * w * c_, 2 * w); if eta.n > 0 && eta.lt(top) { pts.push(eta); } }
    }
    pts.sort_by(|p, q| p.cmp(*q)); pts.dedup_by(|p, q| p.eq(*q));
    let tent = |e: R| rr(1, r_).mul(rr(1, 1).sub(rr(x_, 1).mul(e)));
    let funcs = |e: R| [tent(e), saw(ws[0] as i128, c_, r_, e), saw(ws[1] as i128, c_, r_, e)];
    let pmin = |v: [R; 3]| rmin(v[0], rmin(v[1], v[2]));
    let mut best = rr(0, 1);
    for i in 0..pts.len() {
        let e = pts[i]; best = rmax(best, pmin(funcs(e)));
        if i + 1 < pts.len() {
            let (aa, bb) = (pts[i], pts[i + 1]);
            let (fa, fb) = (funcs(aa), funcs(bb));
            for s in 0..3 { for t in s + 1..3 {
                let den = fb[s].sub(fa[s]).sub(fb[t].sub(fa[t]));
                if den.zero() { continue; }
                let x_ = fa[t].sub(fa[s]).div(den);
                if x_.n > 0 && x_.lt(rr(1, 1)) {
                    let v: Vec<R> = (0..3).map(|j| fa[j].add(fb[j].sub(fa[j]).mul(x_))).collect();
                    best = rmax(best, rmin(v[0], rmin(v[1], v[2])));
                }
            } }
        }
    }
    best
}
fn e_value(n: u64, r1: u64, r2: u64, w1: u64, w2: u64, mode: u8) -> Option<R> {
    let a = n + 1; let ws = [w1, w2]; let mut best = rr(0, 1);
    for &r in &[r1, r2] {
        for c in 1..r {
            if gcd(c, r) != 1 { continue; }
            match xclass(n, r, c, &[r1, r2], mode) { Some(x) => { best = rmax(best, e_arc(a, r, c, x, &ws, false)); } None => { return None; } }
        }
    }
    Some(best)
}
fn rfr(f: Fr) -> R { rr(f.n as i128, f.d as i128) }
fn p2_sets(n: u64, r1: u64, r2: u64, rng: &mut dyn FnMut() -> u64, wmul: u64) -> Vec<(u64, u64)> {
    let a = n + 1;
    let mut ws: Vec<u64> = Vec::new();
    for m in 2..=7u64 { ws.push(m * r1); ws.push(m * r2); }
    for m in 1..=3u64 { for d in [0i64, 1, -1, 2, -2] { let x = (m * a) as i64 + d; if x > n as i64 { ws.push(x as u64); } } }
    let l = r1 / gcd(r1, r2) * r2; let mut m = 1; while m * l <= wmul * n && m <= 5 { if m * l > n { ws.push(m * l); } m += 1; }
    // multiples of r_i +-1, 2A*k multiples, near multiples of r_i*A
    for m in 2..=6u64 { ws.push(m * r1 + 1); ws.push(m * r2 - 1); ws.push(m * r1 * 2 + 1); }
    for _ in 0..14 { ws.push(n + 1 + rng() % (wmul * n)); }
    // CRT-style: w = c-class chosen so that w*c/r_i ~ integer for some c: w = x*r_j' such that w ≡ -1 mod r1, w ≡ 1 mod r2
    for t in 0..2u64 { let mut w = n + 1 + rng() % (3 * n); let tr1 = if t == 0 { r1 - 1 } else { 1 }; let tr2 = if t == 0 { 1 } else { r2 - 1 };
        for _ in 0..(r1 * r2) { if w % r1 == tr1 % r1 && w % r2 == tr2 % r2 { ws.push(w); break; } w += 1; } }
    ws.retain(|&w| w > n && w <= wmul * n + 10 * a); ws.sort(); ws.dedup();
    let mut out = Vec::new();
    for i in 0..ws.len() { for j in i + 1..ws.len() { out.push((ws[i], ws[j])); } }
    if out.len() > 120 { let mut o2 = Vec::new(); for _ in 0..120 { o2.push(out[(rng() as usize) % out.len()]); } o2.sort(); o2.dedup(); out = o2; }
    out
}
fn p2(n0: u64, n1: u64, seed: u64, wmul: u64, abl: bool) {
    let mut s = seed | 1;
    let mut rng = move || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
    let (mut tot, mut sand_f, mut eq_tot, mut eq_f, mut aw, mut aw_lrc_f, mut aw_eq_ok, mut aw_eq_no) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut exc, mut exc_f, mut conv_f, mut pairs) = (0u64, 0u64, 0u64, 0u64);
    let (mut pl, mut pl_t, mut plx, mut plx_t) = (0u64, 0u64, 0u64, 0u64);
    let (mut eltA, mut aw_E_lt) = (0u64, 0u64);
    let mut ab = [[0u64; 3]; 3]; // ablation: [variant][tot, sand-viol, eq-viol]
    for n in n0..=n1 {
        let a = n + 1; let afr = fr(1, a);
        for r1 in (n / 2 + 1)..=n { for r2 in r1 + 1..=n {
            let g = gcd(r1, r2);
            if g == 1 && !abl { continue; }
            if g > 1 { pairs += 1; }
            let b0: Vec<u64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
            for (w1, w2) in p2_sets(n, r1, r2, &mut rng, wmul) {
                let vs = with_w(&b0, &[w1, w2]);
                let ml = ml_exact(&vs);
                if g == 1 {
                    // ablation: formula E (mode 0) and corrected-retained E (mode 3) on coprime pairs
                    for (vi, mode) in [0u8, 3u8].iter().enumerate() {
                        if let Some(e) = e_value(n, r1, r2, w1, w2, *mode) {
                            let mx = rmax(rfr(afr), e); let mlr = rfr(ml);
                            ab[vi][0] += 1; if mlr.gt(mx) || e.gt(mlr) { ab[vi][1] += 1; }
                            if w1 % a != 0 && w2 % a != 0 { ab[vi][2] += 1; }
                        }
                    }
                    continue;
                }
                let e = e_value(n, r1, r2, w1, w2, 0).unwrap();
                let mlr = rfr(ml);
                let mx = rmax(rfr(afr), e);
                tot += 1;
                if e.gt(mlr) || mlr.gt(mx) { sand_f += 1; println!("SANDWICH FAIL N={} r=({},{}) w=({},{}) E={:?} ML={:?}", n, r1, r2, w1, w2, e, ml); }
                let a_div = w1 % a == 0 || w2 % a == 0;
                if !a_div {
                    eq_tot += 1; if !mlr.eq(mx) { eq_f += 1; println!("EQ FAIL N={} r=({},{}) w=({},{})", n, r1, r2, w1, w2); }
                    // planted claims
                    for dd in [1i128, -1] { pl_t += 1; let claim = mx.add(rr(dd, 100000)); if !mlr.eq(claim) { pl += 1; } }
                    if let Some(ex) = e_value(n, r1, r2, w1, w2, 1) { plx_t += 1; let mx2 = rmax(rfr(afr), ex); if !mlr.eq(mx2) { plx += 1; } }
                    // exception: ML<1/N iff E<1/N
                    let invn = rr(1, n as i128);
                    let ml_lt = mlr.lt(invn); let e_lt = e.lt(invn);
                    if ml_lt { exc += 1; }
                    if ml_lt != e_lt { conv_f += 1; println!("EXC IFF FAIL N={} r=({},{}) w=({},{})", n, r1, r2, w1, w2); }
                    if e.lt(rfr(afr)) { eltA += 1; }
                } else {
                    aw += 1;
                    if flt(ml, afr) { aw_lrc_f += 1; println!("LRC VIOLATION?? N={} r=({},{}) w=({},{})", n, r1, r2, w1, w2); }
                    if e.lt(rfr(afr)) { aw_E_lt += 1; }
                    if mlr.eq(mx) { aw_eq_ok += 1; } else { aw_eq_no += 1; }
                }
            }
        } }
    }
    let _ = exc_f;
    println!("p2 N={}..{} seed {} wmul {}: gcd>1 pairs {}, sets {}; sandwich fail {}; A-divides-neither: {} sets, ML=max(1/A,E) fail {}; planted +-1/1e5 refuted {}/{}; planted X-r refuted {}/{}; ML<1/N sets {} , iff-failures {} ; E<1/A (tight) sets {}", n0, n1, seed, wmul, pairs, tot, sand_f, eq_tot, eq_f, pl, pl_t, plx, plx_t, exc, conv_f, eltA);
    println!("A|w sets: {}; ML>=1/A violated {}; E<1/A among them {}; equality ML=max in {} ; equality FAILS in {}", aw, aw_lrc_f, aw_E_lt, aw_eq_ok, aw_eq_no);
    if abl { println!("ablation gcd=1 pairs (r_i>N/2): formula E (X=largest in class incl removed): sets {} sandwich-violations {} (A-dividing-neither sets {}); retained-largest X variant: sets {} sandwich-violations {}", ab[0][0], ab[0][1], ab[0][2], ab[1][0], ab[1][1]); }
}

fn exc(path: &str) {
    let txt = std::fs::read_to_string(path).unwrap();
    let (mut tot, mut mism, mut g1, mut small_r, mut adiv, mut inscope, mut e_ok, mut e_bad) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut lt1a = 0u64;
    for line in txt.lines() {
        if line.starts_with('#') || line.trim().is_empty() { continue; }
        let f: Vec<&str> = line.split('\t').collect();
        let n: u64 = f[0].parse().unwrap(); let r1: u64 = f[1].parse().unwrap(); let r2: u64 = f[2].parse().unwrap();
        let w1: u64 = f[3].parse().unwrap(); let w2: u64 = f[4].parse().unwrap();
        let mlp: Vec<&str> = f[5].split('/').collect(); let want = fr(mlp[0].parse().unwrap(), mlp[1].parse().unwrap());
        let b0: Vec<u64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
        let vs = with_w(&b0, &[w1, w2]); let ml = ml_exact(&vs);
        tot += 1; if !feq(ml, want) { mism += 1; println!("EXC MISMATCH {:?} got {:?}", line, ml); }
        let a = n + 1;
        if flt(ml, fr(1, a)) { lt1a += 1; }
        if gcd(r1, r2) == 1 { g1 += 1; }
        if 2 * r1 <= n { small_r += 1; }
        if w1 % a == 0 || w2 % a == 0 { adiv += 1; }
        if gcd(r1, r2) > 1 && 2 * r1 > n && w1 % a != 0 && w2 % a != 0 {
            inscope += 1;
            let e = e_value(n, r1, r2, w1, w2, 0).unwrap();
            if e.lt(rr(1, n as i128)) && rfr(ml).eq(rmax(rfr(fr(1, a)), e)) { e_ok += 1; } else { e_bad += 1; println!("EXC IN SCOPE BAD {}", line); }
        }
    }
    println!("exceptions file: {} lines, ML mismatches {}; gcd=1: {}; r1<=N/2: {}; A|w: {}; ML<1/A: {}; in scope of Plan2 theorem (gcd>1, r1>N/2, A not|w): {} of which E<1/N and ML=max(1/A,E): {} bad {}", tot, mism, g1, small_r, adiv, lt1a, inscope, e_ok, e_bad);
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let p = |i: usize| -> u64 { a[i].parse().unwrap() };
    match a[1].as_str() {
        "ctl" => ctl(),
        "p3" => p3(p(2), p(3)),
        "lemA" => lemma_a(p(2), p(3)),
        "v1" => v1(p(2), p(3)),
        "pg" => pg(p(2), p(3), p(4)),
        "p2" => p2(p(2), p(3), p(4), p(5), p(6) == 1),
        "exc" => exc(&a[2]),
        _ => println!("modes: ctl p3 lemA v1 pg p2 exc"),
    }
}
