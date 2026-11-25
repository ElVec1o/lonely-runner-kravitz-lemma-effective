// pf.rs : own exact engine for PLAN3_PROOF / PLAN2_E_PROOF.
// Exact i128 rationals, no floats.  Own design (not bq23.rs, not ins.rs, not kstar2.rs, not w2.rs).
// Decision engine: ge(V,c) = "exists t with ||v t|| >= c for all v" (closed gaps of the open bands, then the inserted speeds on each gap);
//                  le(V,c) = "closed bands {||vt||<=c} cover the circle".  ML(V)=c  iff  ge && le.
// Candidate engine (route 2, only for sets of speeds <= ~200): ML = max over t=k/q, q<=2M-1 (Lemma 1(c) of BP: local maxima have denominators dividing u+v).
use std::cmp::Ordering;
use std::env;

type I = i128;
#[derive(Clone, Copy, Debug)]
struct Q { n: I, d: I }
fn gcd(a: I, b: I) -> I { let (mut a, mut b) = (a.abs(), b.abs()); while b != 0 { let t = a % b; a = b; b = t; } a }
fn q(n: I, d: I) -> Q { let (mut n, mut d) = (n, d); if d < 0 { n = -n; d = -d; } let g = gcd(n, d); if g > 1 { n /= g; d /= g; } if n == 0 { d = 1; } Q { n, d } }
fn qi(n: I) -> Q { Q { n, d: 1 } }
fn add(a: Q, b: Q) -> Q { q(a.n * b.d + b.n * a.d, a.d * b.d) }
fn sub(a: Q, b: Q) -> Q { q(a.n * b.d - b.n * a.d, a.d * b.d) }
fn mul(a: Q, b: Q) -> Q { q(a.n * b.n, a.d * b.d) }
fn dv(a: Q, b: Q) -> Q { q(a.n * b.d, a.d * b.n) }
fn cmpq(a: Q, b: Q) -> Ordering { (a.n * b.d).cmp(&(b.n * a.d)) }
fn lt(a: Q, b: Q) -> bool { cmpq(a, b) == Ordering::Less }
fn le_(a: Q, b: Q) -> bool { cmpq(a, b) != Ordering::Greater }
fn eq(a: Q, b: Q) -> bool { cmpq(a, b) == Ordering::Equal }
fn qmax(a: Q, b: Q) -> Q { if lt(a, b) { b } else { a } }
fn qmin(a: Q, b: Q) -> Q { if lt(a, b) { a } else { b } }
fn floor_q(a: Q) -> I { a.n.div_euclid(a.d) }
fn ceil_q(a: Q) -> I { -((-a.n).div_euclid(a.d)) }
fn nid(x: Q) -> Q { let r = x.n.rem_euclid(x.d); q(r.min(x.d - r), x.d) }
fn fmt(a: Q) -> String { format!("{}/{}", a.n, a.d) }

fn gcdu(a: i64, b: i64) -> i64 { gcd(a as I, b as I) as i64 }

// ---------- gaps of the retained set at level c ----------
// closed=false: open bands (kq-p)/(vq) .. (kq+p)/(vq); returns CLOSED gaps [a,b] (a<=b) between merged components.
// closed=true : closed bands; returns OPEN gaps (a,b), a<b.
fn gaps(v: &[i64], c: Q, closed: bool) -> Vec<(Q, Q)> {
    let mut iv: Vec<(Q, Q)> = Vec::new();
    for &x in v {
        let x = x as I;
        for k in 0..=x {
            let lo = q(k * c.d - c.n, x * c.d);
            let hi = q(k * c.d + c.n, x * c.d);
            iv.push((lo, hi));
        }
    }
    iv.sort_by(|a, b| cmpq(a.0, b.0).then(cmpq(a.1, b.1)));
    let mut out = Vec::new();
    let mut cur = iv[0].1;
    for &(lo, hi) in iv.iter().skip(1) {
        let gap = if closed { lt(cur, lo) } else { le_(cur, lo) };
        if gap { out.push((cur, lo)); }
        if lt(cur, hi) { cur = hi; }
    }
    out
}

// exists a point of [a,b] (closed) outside the union of the OPEN intervals ivs ?
fn uncovered_closed(a: Q, b: Q, ivs: &mut Vec<(Q, Q)>) -> bool {
    ivs.sort_by(|x, y| cmpq(x.0, y.0));
    let mut cur = a;
    let mut i = 0;
    let mut best = cur;
    loop {
        // best = max hi over intervals with lo < cur
        while i < ivs.len() && lt(ivs[i].0, cur) { if lt(best, ivs[i].1) { best = ivs[i].1; } i += 1; }
        // best >= every hi among lo<cur seen so far
        if !lt(cur, best) { return true; } // cur not inside any open interval (lo<cur<hi fails)
        // need the max over ALL lo<cur, which is best (monotone); cur point covered iff best>cur
        cur = best;
        if lt(b, cur) { return false; }
    }
}
// exists a point of the OPEN interval (a,b) outside the union of the CLOSED intervals ivs ?
fn uncovered_open(a: Q, b: Q, ivs: &mut Vec<(Q, Q)>) -> bool {
    ivs.sort_by(|x, y| cmpq(x.0, y.0));
    let mut reach = a;
    let mut i = 0;
    let mut best = reach;
    loop {
        if le_(b, reach) { return false; }
        while i < ivs.len() && le_(ivs[i].0, reach) { if lt(best, ivs[i].1) { best = ivs[i].1; } i += 1; }
        if !lt(reach, best) { return true; }
        reach = best;
    }
}
fn bad_intervals(w: i64, a: Q, b: Q, c: Q, out: &mut Vec<(Q, Q)>) {
    // intervals ((k-c)/w, (k+c)/w) that can meet [a,b]
    let w = w as I;
    let k0 = floor_q(mul(qi(w), a)) - 1;
    let k1 = ceil_q(mul(qi(w), b)) + 1;
    for k in k0..=k1 {
        let lo = q(k * c.d - c.n, w * c.d);
        let hi = q(k * c.d + c.n, w * c.d);
        if lt(lo, b) || (le_(lo, b)) { if lt(a, hi) || le_(a, hi) { out.push((lo, hi)); } }
    }
}
fn ge_set(base: &[i64], ins: &[i64], c: Q) -> bool {
    for (a, b) in gaps(base, c, false) {
        let mut ivs = Vec::new();
        for &w in ins { bad_intervals(w, a, b, c, &mut ivs); }
        if uncovered_closed(a, b, &mut ivs) { return true; }
    }
    false
}
fn le_set(base: &[i64], ins: &[i64], c: Q) -> bool {
    for (a, b) in gaps(base, c, true) {
        let mut ivs = Vec::new();
        for &w in ins { bad_intervals(w, a, b, c, &mut ivs); }
        if uncovered_open(a, b, &mut ivs) { return false; }
    }
    true
}
fn is_ml(base: &[i64], ins: &[i64], c: Q) -> bool { ge_set(base, ins, c) && le_set(base, ins, c) }

// ---------- direct evaluation ----------
fn f_at(v: &[i64], t: Q) -> Q {
    let mut m = qi(1);
    for &x in v { let d = nid(mul(qi(x as I), t)); if lt(d, m) { m = d; } }
    m
}
// route 2: ML of a (small) set by candidate times k/q, q<=2M-1
fn ml_cand(v: &[i64]) -> Q {
    let mx = *v.iter().max().unwrap() as I;
    let mut best = qi(0);
    for qq in 3..=(2 * mx - 1) {
        for k in 1..=(qq / 2) {
            if gcd(k, qq) != 1 { continue; }
            // f(k/qq) = min_v min(vk mod qq, qq - vk mod qq)/qq
            let mut m = qq;
            for &x in v { let r = (x as I * k).rem_euclid(qq); let d = r.min(qq - r); if d < m { m = d; if m == 0 { break; } } }
            let val = q(m, qq);
            if lt(best, val) { best = val; }
        }
    }
    best
}
// local maximum values of f_V (route: candidate times k/q, q<=2M-1; local-max test at t +- h, h = 1/(16 M^2); integer arithmetic)
fn local_max_values(v: &[i64]) -> Vec<Q> {
    let mx = *v.iter().max().unwrap() as I;
    let hh: I = 16 * mx * mx;
    let mut vals: Vec<Q> = Vec::new();
    for qq in 3..=(2 * mx - 1) {
        for k in 1..=(qq / 2) {
            if gcd(k, qq) != 1 { continue; }
            let mut m = qq;
            for &x in v { let r = (x as I * k).rem_euclid(qq); let d = r.min(qq - r); if d < m { m = d; if m == 0 { break; } } }
            if m == 0 { continue; }
            // f(t)=m/qq.  f(t+-h): t+h=(k hh + qq)/(qq hh), t-h=(k hh - qq)/(qq hh); dist/(qq hh) <= m/qq  <=> dist <= m hh
            let den = qq * hh;
            let mut ok = true;
            for sgn in [1i128, -1] {
                let num = k * hh + sgn * qq;
                let mut mn = den;
                for &x in v { let r = (x as I * num).rem_euclid(den); let d = r.min(den - r); if d < mn { mn = d; } }
                if mn > m * hh { ok = false; break; }
            }
            if ok { let val = q(m, qq); if !vals.iter().any(|x| eq(*x, val)) { vals.push(val); } }
        }
    }
    vals.sort_by(|a, b| cmpq(*a, *b));
    vals
}

fn d0_of(n: i64, r: i64) -> i64 { let mut d = n + 1 + r; while gcdu(d, r) != 1 { d += 1; } d }
fn next_cop(d: i64, r: i64) -> i64 { let mut x = d + 1; while gcdu(x, r) != 1 { x += 1; } x }
fn inv_mod(a: i64, m: i64) -> i64 { // a^{-1} mod m, gcd=1
    let (mut t, mut nt, mut r, mut nr) = (0i128, 1i128, m as I, (a as I).rem_euclid(m as I));
    while nr != 0 { let qq = r / nr; let tt = t - qq * nt; t = nt; nt = tt; let rr = r - qq * nr; r = nr; nr = rr; }
    t.rem_euclid(m as I) as i64
}

struct Cnt { name: &'static str, tot: u64, fail: u64, neg_tot: u64, neg_det: u64 }
impl Cnt { fn new(n: &'static str) -> Cnt { Cnt { name: n, tot: 0, fail: 0, neg_tot: 0, neg_det: 0 } }
    fn rep(&self) { println!("  {:<46} cases {:>8}  FAIL {:>4}   planted-negatives {:>7} detected {:>7}", self.name, self.tot, self.fail, self.neg_tot, self.neg_det); } }

fn bset(n: i64, rem: &[i64]) -> Vec<i64> { (1..=n).filter(|x| !rem.contains(x)).collect() }

// ====================================== plan 3 ======================================
// lemma checks for B=[N]\{r}, 1<=r<=N/2.
fn p3(n0: i64, n1: i64, kmode: i64) {
    let mut c_l1 = Cnt::new("L1  ML(B)=2/D0 (ge&le) and route-2 value");
    let mut c_d0 = Cnt::new("L0  D0<=N+2r, D0>=N+1+r, coprime");
    let mut c_eq = Cnt::new("L2  equality times = {+-k/D0}, rk=1 mod D0, only 2");
    let mut c_rl = Cnt::new("L3  rho=2r, lambda=D0-2r at t0 (swap at -t0), vmu");
    let mut c_lm = Cnt::new("L4  local maxima >1/(N+1) are exactly 2/D (D coprime in window)");
    let mut c_l2 = Cnt::new("L5  L2 = 2/D1 if D1<=N+2r else 1/(N+1)");
    let mut c_ar = Cnt::new("L6  arc formula f=min((1-X eta)/r,2 eta) on grid (r>=2)");
    let mut c_u = Cnt::new("K1  (U) ML(B+w)<=max(K,L2), D0|w");
    let mut c_l = Cnt::new("K2  (L) ML>=K when w+vmu>=2N, D0|w");
    let mut c_e = Cnt::new("K3  (E) ML=K when w>=thr(N,r), D0|w");
    let mut c_t = Cnt::new("K4  explicit threshold only (planted: w<thr => some fail)");
    let mut min_ratio = 1e9f64; let mut max_ratio = 0f64; let mut nn = 0u64;
    for n in n0..=n1 {
        let mut worst_thr: f64 = 0.0;
        for r in 1..=(n / 2) {
            let b = bset(n, &[r]);
            let d0 = d0_of(n, r);
            let d1 = next_cop(d0, r);
            // L0
            c_d0.tot += 1;
            if !(d0 >= n + 1 + r && d0 <= n + 2 * r && gcdu(d0, r) == 1) { c_d0.fail += 1; println!("FAIL L0 N={} r={}", n, r); }
            let l = q(2, d0 as I);
            // L1: decision engine and route 2
            c_l1.tot += 1;
            let ok1 = is_ml(&b, &[], l);
            let ok1b = eq(ml_cand(&b), l);
            if !(ok1 && ok1b) { c_l1.fail += 1; println!("FAIL L1 N={} r={} ge/le={} cand={}", n, r, ok1, ok1b); }
            // planted negatives for L1: 2/D1, 2/(D0-1 if coprime-or-not), D0 replaced by N+1+r when not coprime
            for dd in [d1, d0 - 1, d0 + 0 + 1] {
                if dd == d0 { continue; }
                c_l1.neg_tot += 1;
                if !is_ml(&b, &[], q(2, dd as I)) { c_l1.neg_det += 1; }
            }
            if gcdu(n + 1 + r, r) != 1 { // naive claim D=N+1+r not coprime: must be refuted
                c_l1.neg_tot += 1; if !is_ml(&b, &[], q(2, (n + 1 + r) as I)) { c_l1.neg_det += 1; }
            }
            // L2: equality times = points of closed gaps at level L (degenerate gaps)
            let gp = gaps(&b, l, false);
            let k0 = inv_mod(r, d0) as I; // r k = 1 mod D0
            let t0 = q(k0, d0 as I);
            let tm = q(d0 as I - k0, d0 as I);
            c_eq.tot += 1;
            let mut ok2 = gp.len() == 2;
            if ok2 { for (a, bb) in &gp { if !eq(*a, *bb) { ok2 = false; } } }
            if ok2 {
                let mut pts: Vec<Q> = gp.iter().map(|x| x.0).collect();
                pts.sort_by(|a, b| cmpq(*a, *b));
                let mut want = vec![t0, tm]; want.sort_by(|a, b| cmpq(*a, *b));
                if !(eq(pts[0], want[0]) && eq(pts[1], want[1])) { ok2 = false; }
            }
            if !ok2 { c_eq.fail += 1; println!("FAIL L2 N={} r={} gaps={}", n, r, gp.len()); }
            // planted: wrong inverse (k=r mod D0, or k0+1)
            for kk in [k0 + 1, (r as I) % d0 as I] {
                if kk == k0 || kk == d0 as I - k0 { continue; }
                c_eq.neg_tot += 1;
                let tt = q(kk, d0 as I);
                if !(gp.iter().any(|x| eq(x.0, tt))) { c_eq.neg_det += 1; }
            }
            // L3: rho, lambda from the definition (exact residues) at t0 and at -t0
            c_rl.tot += 1;
            let lq = l;
            let mut rho = 0; let mut lam = 0; let mut rho2 = 0; let mut lam2 = 0;
            for &v in &b {
                let x = mul(qi(v as I), t0);
                let fr = sub(x, qi(floor_q(x)));
                if eq(fr, lq) { rho = rho.max(v); }
                if eq(fr, sub(qi(1), lq)) { lam = lam.max(v); }
                let x2 = mul(qi(v as I), tm);
                let fr2 = sub(x2, qi(floor_q(x2)));
                if eq(fr2, lq) { rho2 = rho2.max(v); }
                if eq(fr2, sub(qi(1), lq)) { lam2 = lam2.max(v); }
            }
            let vmu = (rho.min(lam)).min(rho2.min(lam2));
            let want_vmu = (2 * r).min(d0 - 2 * r);
            let ok3 = rho == 2 * r && lam == d0 - 2 * r && rho2 == d0 - 2 * r && lam2 == 2 * r && vmu == want_vmu;
            if !ok3 { c_rl.fail += 1; println!("FAIL L3 N={} r={} rho={} lam={} rho2={} lam2={} vmu={} want={}", n, r, rho, lam, rho2, lam2, vmu, want_vmu); }
            for bad in [want_vmu + 1, want_vmu - 1, (2 * r).max(d0 - 2 * r), r] {
                if bad == want_vmu { continue; }
                c_rl.neg_tot += 1; if vmu != bad { c_rl.neg_det += 1; }
            }
            // L4/L5: local maxima
            let lm = local_max_values(&b);
            // expected values > 1/(N+1): 2/D for D in [N+r+1, N+2r], gcd(D,r)=1
            let mut want: Vec<Q> = Vec::new();
            for dd in (n + r + 1)..=(n + 2 * r) { if gcdu(dd, r) == 1 { want.push(q(2, dd as I)); } }
            want.sort_by(|a, b| cmpq(*a, *b));
            let thr = q(1, (n + 1) as I);
            let mut got: Vec<Q> = lm.iter().cloned().filter(|x| lt(thr, *x)).collect();
            got.sort_by(|a, b| cmpq(*a, *b));
            c_lm.tot += 1;
            let mut ok4 = got.len() == want.len();
            if ok4 { for i in 0..got.len() { if !eq(got[i], want[i]) { ok4 = false; } } }
            if !ok4 { c_lm.fail += 1; println!("FAIL L4 N={} r={}", n, r); }
            // L5
            c_l2.tot += 1;
            let l2_comp = lm.iter().cloned().filter(|x| lt(*x, l)).fold(qi(0), |a, b| qmax(a, b));
            let l2_claim = if d1 <= n + 2 * r { q(2, d1 as I) } else { q(1, (n + 1) as I) };
            if !eq(l2_comp, l2_claim) { c_l2.fail += 1; println!("FAIL L5 N={} r={} comp={} claim={}", n, r, fmt(l2_comp), fmt(l2_claim)); }
            // planted: D1' = D0+1 whenever not coprime; and always-1/(N+1)
            if gcdu(d0 + 1, r) != 1 && d0 + 1 <= n + 2 * r { c_l2.neg_tot += 1; if !eq(l2_comp, q(2, (d0 + 1) as I)) { c_l2.neg_det += 1; } }
            if d1 <= n + 2 * r { c_l2.neg_tot += 1; if !eq(l2_comp, q(1, (n + 1) as I)) { c_l2.neg_det += 1; } }
            // L6: arc formula (r>=2)
            if r >= 2 {
                for c in 1..r {
                    if gcdu(c, r) != 1 { continue; }
                    let u = (-(inv_mod(c, r) as i64)).rem_euclid(r); // class of -c^{-1}
                    let u = if u == 0 { r } else { u };
                    let mut x = u; while x + r <= n { x += r; }
                    for j in 0..=6i128 {
                        let eta = q(j, 6 * (n as I + 1));
                        let t = q(c as I * 1, r as I); let t = add(t, mul(eta, q(1, r as I)));
                        let want = qmin(q(1, r as I), qi(1)); let _ = want;
                        let tent = mul(sub(qi(1), mul(qi(x as I), eta)), q(1, r as I));
                        let saw = mul(qi(2), eta);
                        let fm = qmin(tent, saw);
                        c_ar.tot += 1;
                        if !eq(f_at(&b, t), fm) { c_ar.fail += 1; println!("FAIL L6 N={} r={} c={} j={}", n, r, c, j); }
                        if j > 0 { // planted: wrong X (X-r)
                            let tent2 = mul(sub(qi(1), mul(qi((x - r) as I), eta)), q(1, r as I));
                            let fm2 = qmin(tent2, saw);
                            if !eq(fm2, fm) { c_ar.neg_tot += 1; if !eq(f_at(&b, t), fm2) { c_ar.neg_det += 1; } }
                        }
                    }
                }
            }
            // K*: multiples of D0
            let vm = want_vmu as I;
            let delta = if d1 <= n + 2 * r { (d1 - d0) as I } else { (2 * n + 2 - d0) as I };
            // thr = max(2N - vmu, ceil(vmu*D0/delta))
            let t1 = 2 * n as I - vm;
            let t2 = (vm * d0 as I + delta - 1) / delta;
            let thr_w = t1.max(t2).max(1);
            let lk = q(2, d0 as I);
            let l2c = l2_claim;
            // window of multiples: j from 1 .. jmax where jmax covers up to 3*thr
            let jt = (thr_w / d0 as I) + 1;
            let mut js: Vec<I> = (1..=(jt + 6)).collect();
            js.push(2 * jt + 1); js.push(3 * jt + 2);
            let mut last_bad = 0;
            for &j in &js {
                let w = j * d0 as I;
                let kw = mul(mul(qi(w), lk), q(1, w + vm)); // w L/(w+vmu)
                let ins = [w as i64];
                // (U)
                let mx = qmax(kw, l2c);
                c_u.tot += 1;
                if !le_set(&b, &ins, mx) { c_u.fail += 1; println!("FAIL K1 N={} r={} w={}", n, r, w); }
                let geok = ge_set(&b, &ins, kw);
                if w + vm >= 2 * n as I {
                    c_l.tot += 1;
                    if !geok { c_l.fail += 1; println!("FAIL K2 N={} r={} w={}", n, r, w); }
                }
                let eq_val = geok && le_set(&b, &ins, kw);
                if w >= thr_w {
                    c_e.tot += 1;
                    if !eq_val { c_e.fail += 1; println!("FAIL K3 N={} r={} w={} thr={}", n, r, w, thr_w); }
                    for bad in [vm + 1, vm - 1] {
                        let kb = mul(mul(qi(w), lk), q(1, w + bad));
                        c_e.neg_tot += 1;
                        if !(ge_set(&b, &ins, kb) && le_set(&b, &ins, kb)) { c_e.neg_det += 1; }
                    }
                } else if !eq_val { last_bad = w; }
                if j <= 3 {
                    for dw in [-1i128, 1] {
                        let w2 = w + dw; if w2 <= n as I { continue; }
                        let k2 = mul(mul(qi(w2), lk), q(1, w2 + vm));
                        let mx2 = qmax(k2, l2c);
                        c_u.neg_tot += 1;
                        if !le_set(&b, &[w2 as i64], mx2) { c_u.neg_det += 1; }
                    }
                }
            }
            // threshold sharpness: last multiple below thr where equality fails
            c_t.tot += 1;
            if last_bad > 0 { let ratio = last_bad as f64 / thr_w as f64; if ratio < min_ratio { min_ratio = ratio; } if ratio > max_ratio { max_ratio = ratio; } nn += 1; }
            let rr = thr_w as f64 / (2.0 * (n as f64).powi(3)); if rr > worst_thr { worst_thr = rr; }
            if kmode > 0 {
                // K* at w>=2N^3 (the BP statement) : three least multiples
                let mut j = (2 * n as I * n as I * n as I + d0 as I - 1) / d0 as I;
                for _ in 0..3 {
                    let w = j * d0 as I;
                    let kw = mul(mul(qi(w), lk), q(1, w + vm));
                    c_e.tot += 1;
                    if !(ge_set(&b, &[w as i64], kw) && le_set(&b, &[w as i64], kw)) { c_e.fail += 1; println!("FAIL K3' N={} r={} w={}", n, r, w); }
                    j += 1;
                }
            }
        }
        let _ = worst_thr;
    }
    println!("RESULTS p3 N={}..{}", n0, n1);
    for c in [&c_d0, &c_l1, &c_eq, &c_rl, &c_lm, &c_l2, &c_ar, &c_u, &c_l, &c_e] { c.rep(); }
    println!("  threshold sharpness: for {} (N,r) the last failing multiple below thr has w_fail/thr in [{:.3},{:.3}] (thr = max(2N-vmu, ceil(vmu D0/Delta)))", nn, min_ratio, max_ratio);
    let _ = c_t;
}

// ====================================== plan 2 ======================================
fn xclass(n: i64, r: i64, c: i64) -> i64 {
    let u = (-(inv_mod(c, r))).rem_euclid(r); let u = if u == 0 { r } else { u };
    let mut x = u; while x + r <= n { x += r; } x
}
fn e_value(n: i64, rs: [i64; 2], ws: [i64; 2]) -> Q {
    let a_ = q(1, (n + 1) as I);
    let mut best = qi(0);
    for &r in &rs {
        for c in 1..r {
            if gcdu(c, r) != 1 { continue; }
            let x = xclass(n, r, c) as I;
            let rr = r as I;
            let eval = |eta: Q| -> Q {
                let tent = mul(sub(qi(1), mul(qi(x), eta)), q(1, rr));
                let t = mul(add(qi(c as I), eta), q(1, rr));
                let s1 = nid(mul(qi(ws[0] as I), t));
                let s2 = nid(mul(qi(ws[1] as I), t));
                qmin(qmin(tent, s1), s2)
            };
            let mut cands: Vec<Q> = vec![qi(0), a_];
            let mut alph = [qi(0); 2]; let mut bet = [qi(0); 2];
            for j in 0..2 { alph[j] = q(ws[j] as I * c as I, rr); bet[j] = q(ws[j] as I, rr); }
            for j in 0..2 {
                // kinks: alpha + beta eta in (1/2)Z
                let s_lo = alph[j]; let s_hi = add(alph[j], mul(bet[j], a_));
                let m0 = floor_q(mul(qi(2), s_lo)) ; let m1 = ceil_q(mul(qi(2), s_hi));
                for m in m0..=m1 { let eta = dv(sub(q(m, 2), alph[j]), bet[j]); cands.push(eta);
                    // tent crossing with piece centred at m'=floor, sigma = +-1
                }
                let mlo = floor_q(s_lo) - 1; let mhi = ceil_q(s_hi) + 1;
                for mp in mlo..=mhi {
                    for sg in [-1i128, 1] {
                        let den = add(mul(qi(sg), bet[j]), q(x, rr));
                        if den.n == 0 { continue; }
                        let num = sub(q(1, rr), mul(qi(sg), sub(alph[j], qi(mp))));
                        cands.push(dv(num, den));
                    }
                }
            }
            // saw1 ~ saw2
            let (s1lo, s1hi) = (alph[0], add(alph[0], mul(bet[0], a_)));
            let (s2lo, s2hi) = (alph[1], add(alph[1], mul(bet[1], a_)));
            for m1 in (floor_q(s1lo) - 1)..=(ceil_q(s1hi) + 1) {
                for m2 in (floor_q(s2lo) - 1)..=(ceil_q(s2hi) + 1) {
                    for g1 in [-1i128, 1] { for g2 in [-1i128, 1] {
                        let den = sub(mul(qi(g1), bet[0]), mul(qi(g2), bet[1]));
                        if den.n == 0 { continue; }
                        let num = sub(mul(qi(g2), sub(alph[1], qi(m2))), mul(qi(g1), sub(alph[0], qi(m1))));
                        cands.push(dv(num, den));
                    } }
                }
            }
            for eta in cands { if lt(eta, qi(0)) || lt(a_, eta) { continue; } let v = eval(eta); if lt(best, v) { best = v; } }
        }
    }
    best
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } fn range(&mut self, a: i64, b: i64) -> i64 { a + (self.next() % ((b - a + 1) as u64)) as i64 } }

fn p2(n0: i64, n1: i64, nrand: i64, seed: u64, wmaxmul: i64) {
    let mut rng = Rng(seed);
    let (mut tot, mut ok_sandwich, mut tot_a, mut eq_a, mut tot_div, mut lrc_fail, mut exc, mut exc_ok) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let (mut plant_tot, mut plant_det) = (0u64, 0u64);
    let mut e_ge_ml_when_e_small = 0u64;
    for n in n0..=n1 {
        let a = n + 1;
        for r1 in (n / 2 + 1)..=n { for r2 in (r1 + 1)..=n {
            if gcdu(r1, r2) == 1 { continue; }
            let b = bset(n, &[r1, r2]);
            // structured w candidates
            let mut ws: Vec<i64> = Vec::new();
            for m in 2..=7 { ws.push(m * r1); ws.push(m * r2); }
            for m in 1..=3 { ws.push(m * a); ws.push(m * a + 1); ws.push(m * a - 1); }
            for _ in 0..nrand { ws.push(rng.range(n + 1, wmaxmul * n)); }
            // a few huge multiples of r1,r2 and of lcm
            let lcm = r1 * r2 / gcdu(r1, r2);
            ws.push(lcm); ws.push(2 * lcm); ws.push(lcm * (rng.range(2, 6)));
            ws.retain(|&w| w > n); ws.sort(); ws.dedup();
            // all pairs but thinned for big lists
            let mut pairs: Vec<(i64, i64)> = Vec::new();
            for i in 0..ws.len() { for j in (i + 1)..ws.len() { pairs.push((ws[i], ws[j])); } }
            // thin: keep every pair when small else random 120
            let keep: Vec<(i64, i64)> = if pairs.len() <= 160 { pairs } else { let mut v = Vec::new(); for _ in 0..160 { let k = rng.range(0, pairs.len() as i64 - 1) as usize; v.push(pairs[k]); } v };
            for (w1, w2) in keep {
                let e = e_value(n, [r1, r2], [w1, w2]);
                let a_q = q(1, a as I);
                let theta = qmax(a_q, e);
                tot += 1;
                let ge_e = if eq(e, qi(0)) { true } else { ge_set(&b, &[w1, w2], e) };
                let le_t = le_set(&b, &[w1, w2], theta);
                if ge_e && le_t { ok_sandwich += 1; } else { println!("FAIL sandwich N={} R=({},{}) W=({},{}) E={} theta={} ge_e={} le_t={}", n, r1, r2, w1, w2, fmt(e), fmt(theta), ge_e, le_t); }
                let adiv = w1 % a == 0 || w2 % a == 0;
                if !adiv {
                    tot_a += 1;
                    if is_ml(&b, &[w1, w2], theta) { eq_a += 1; } else { println!("FAIL equality(A not dividing) N={} R=({},{}) W=({},{}) E={} theta={}", n, r1, r2, w1, w2, fmt(e), fmt(theta)); }
                    // planted negatives: wrong value
                    for bad in [add(theta, q(1, 100000)), sub(theta, q(1, 100000))] { plant_tot += 1; if !is_ml(&b, &[w1, w2], bad) { plant_det += 1; } }
                    // exceptions
                    if lt(e, q(1, n as I)) {
                        exc += 1;
                        // ML<1/N iff E<1/N (A not dividing): verify ML<1/N decided independently
                        if !ge_set(&b, &[w1, w2], q(1, n as I)) { exc_ok += 1; } else { println!("FAIL exception-equivalence N={} R=({},{}) W=({},{})", n, r1, r2, w1, w2); }
                    } else if !ge_set(&b, &[w1, w2], q(1, n as I)) { println!("FAIL exception-equivalence(2) N={} R=({},{}) W=({},{}) E={}", n, r1, r2, w1, w2, fmt(e)); }
                } else {
                    tot_div += 1;
                    // A | w : LRC check ML>=1/A (must hold if LRC holds), and equality iff
                    if !ge_set(&b, &[w1, w2], a_q) { lrc_fail += 1; println!("LRC-VIOLATION? N={} R=({},{}) W=({},{})", n, r1, r2, w1, w2); }
                    if lt(e, a_q) { e_ge_ml_when_e_small += 1; }
                }
            }
        } }
    }
    println!("RESULTS p2 N={}..{} seed={}", n0, n1, seed);
    println!("  sets {}; sandwich E<=ML<=max(1/A,E) holds {} ; A-not-dividing sets {}: ML=max(1/A,E) exactly {} ; planted wrong-value claims {} detected {}", tot, ok_sandwich, tot_a, eq_a, plant_tot, plant_det);
    println!("  exceptions (E<1/N, A not dividing) {}, all confirmed ML<1/N by independent ge: {} ; sets with A|w {} (LRC ML>=1/A violated: {}; of which E<1/A: {})", exc, exc_ok, tot_div, lrc_fail, e_ge_ml_when_e_small);
}

fn ctl() {
    println!("CONTROLS");
    // ML([N]) = 1/(N+1)
    for n in 3..=20 { let b = bset(n, &[]); assert!(is_ml(&b, &[], q(1, n as I + 1))); assert!(eq(ml_cand(&b), q(1, n as I + 1))); }
    println!("  ML([N])=1/(N+1) N=3..20 ok (both routes)");
    // known values
    assert!(is_ml(&[1, 3, 4, 7], &[], q(1, 5)));
    assert!(is_ml(&[1, 5, 6, 11, 16, 17], &[], q(5, 33)));
    println!("  ML(1,3,4,7)=1/5, ML(1,5,6,11,16,17)=5/33 ok");
    // planted false claims must fail
    assert!(!is_ml(&[1, 3, 4, 7], &[], q(1, 6)));
    assert!(!is_ml(&[1, 3, 4, 7], &[], q(2, 9)));
    // Zhang Example 5.2: N=73, remove 70,72, insert 140,144: tight ML=1/74
    let b = bset(73, &[70, 72]);
    assert!(is_ml(&b, &[140, 144], q(1, 74)));
    println!("  (73;70,72;140,144) ML=1/74 ok (Zhang Example 5.2)");
    assert!(!is_ml(&b, &[140, 144], q(1, 73)));
    // N=14 (10,14;20,98): ML=7/99 (bq23 control); we only check E and ML here with our own engine
    let b = bset(14, &[10, 14]);
    let e = e_value(14, [10, 14], [20, 98]);
    println!("  N=14 R=(10,14) W=(20,98): E={} ML=7/99? {}", fmt(e), is_ml(&b, &[20, 98], q(7, 99)));
    // two-speed gap formula s/(2s+1)
    println!("  CTL TOTAL OK");
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a[1].as_str() {
        "ctl" => ctl(),
        "p3" => p3(a[2].parse().unwrap(), a[3].parse().unwrap(), a.get(4).map(|s| s.parse().unwrap()).unwrap_or(0)),
        "p2" => p2(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), a[5].parse().unwrap(), a[6].parse().unwrap()),
        _ => println!("usage"),
    }
}
