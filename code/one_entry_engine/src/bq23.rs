// bq23: the accompanying code plan 2 / plan 3 instrument. Own code, exact i128 integers/fractions.
// Engine core (good_pieces / sub_speed / has_good / ml_exact) is the same algorithm as the accompanying code, re-typed here.
// Notation: N = number of speeds of [N]; A = N+1; ML(V) = max_t min_{v in V} ||vt||; tau = 1/N.
// Subcommands:
//  ctl                       negative controls (planted values; TSV rows of EXCEPTIONS_N14_120.tsv via `tsv`)
//  tsv FILE                  recompute F (closed form) and E (arc formula) on every row of the TSV and compare with its ML
//  cert2 N0 N1 [mode]        certified-complete pair engine, ALL pairs (r1<r2<=N), ALL inserted w1<w2 (no cap), exceptions ML<1/N,
//                            each exception analysed: ML (method B), F, E, T4 class.   mode: all | coprime | gcd
//  grid N0 N1                unpruned grid w2 <= 3N^2, witness prefilter + sweep, exceptions ML<1/N (control for cert2)
//  fscan N0 N1               all sets with F defined (r1,r2 > N/2, each r_i | some w) and w2 <= 3N^2: is F<1/N <=> exception?
//  t1 N0 N1 S                random sets (gcd>1, r_i>N/2), S per N: ML == max(1/A,E) ?  (decision engine)
//  one N0 N1                 plan 3 table: L=ML([N]\{r}) for r<=N/2, equality times, v_mu, L2, guess L=2/D0
//  kstar N0 N1               plan 3 K*: ML([N]\{r} u {w}) for multiples w of D, w>=2N^3 vs w L/(w+v_mu)
use std::cmp::Ordering;
use std::collections::HashSet;
use std::env;
type I = i128;

#[derive(Clone, Copy, Debug)]
struct Fr { n: I, d: I }
fn fr(n: I, d: I) -> Fr { Fr { n, d } }
fn gcd(a: I, b: I) -> I { if b == 0 { a.abs() } else { gcd(b, a % b) } }
fn red(a: Fr) -> Fr { let g = gcd(a.n, a.d).max(1); let mut r = fr(a.n / g, a.d / g); if r.d < 0 { r = fr(-r.n, -r.d); } r }
fn cmpf(a: Fr, b: Fr) -> Ordering { (a.n * b.d).cmp(&(b.n * a.d)) }
fn fadd(a: Fr, b: Fr) -> Fr { red(fr(a.n * b.d + b.n * a.d, a.d * b.d)) }
fn fsub(a: Fr, b: Fr) -> Fr { red(fr(a.n * b.d - b.n * a.d, a.d * b.d)) }
fn fmul(a: Fr, b: Fr) -> Fr { red(fr(a.n * b.n, a.d * b.d)) }
fn fdiv(a: Fr, b: Fr) -> Fr { red(fr(a.n * b.d, a.d * b.n)) }
fn fmin(a: Fr, b: Fr) -> Fr { if cmpf(a, b) == Ordering::Greater { b } else { a } }
fn fmax(a: Fr, b: Fr) -> Fr { if cmpf(a, b) == Ordering::Less { b } else { a } }
fn feq(a: Fr, b: Fr) -> bool { cmpf(a, b) == Ordering::Equal }
fn show(f: Fr) -> String { let g = red(f); format!("{}/{}", g.n, g.d) }
fn ceil_div(a: I, b: I) -> I { -((-a).div_euclid(b)) }
fn inv_mod(a: I, m: I) -> I { // a coprime to m
    let (mut r0, mut r1, mut s0, mut s1) = (m, a.rem_euclid(m), 0 as I, 1 as I);
    while r1 != 0 { let q = r0 / r1; let t = r0 - q * r1; r0 = r1; r1 = t; let u = s0 - q * s1; s0 = s1; s1 = u; }
    s0.rem_euclid(m)
}
fn len(a: Fr, b: Fr) -> Fr { red(fr(b.n * a.d - a.n * b.d, a.d * b.d)) }

fn good_pieces(vs: &[i64], p: I, q: I) -> Vec<(Fr, Fr)> {
    let mut bands: Vec<(Fr, Fr)> = Vec::new();
    for &v in vs {
        let v = v as I;
        let mut k: I = 0;
        loop {
            if 2 * (k * q - p) >= v * q { break; }
            bands.push((fr(k * q - p, v * q), fr(k * q + p, v * q)));
            k += 1;
        }
    }
    bands.sort_by(|a, b| cmpf(a.0, b.0));
    let half = fr(1, 2);
    let mut out = Vec::new();
    if bands.is_empty() { out.push((fr(0, 1), half)); return out; }
    let mut h = bands[0].1;
    for b in bands.iter().skip(1) {
        if cmpf(b.0, h) == Ordering::Less { if cmpf(b.1, h) == Ordering::Greater { h = b.1; } }
        else {
            if cmpf(h, half) != Ordering::Greater {
                let r = if cmpf(b.0, half) == Ordering::Greater { half } else { b.0 };
                out.push((h, r));
            }
            h = b.1;
        }
    }
    if cmpf(h, half) != Ordering::Greater { out.push((h, half)); }
    out
}
fn sub_speed(pc: &[(Fr, Fr)], w: I, p: I, q: I) -> Vec<(Fr, Fr)> {
    let mut out = Vec::new();
    for &(a, b) in pc {
        let j0 = ceil_div(a.n * w * q + p * a.d - q * a.d, a.d * q);
        let mut j = j0;
        loop {
            let lo = fr(j * q + p, w * q);
            if cmpf(lo, b) == Ordering::Greater { break; }
            let hi = fr((j + 1) * q - p, w * q);
            let l2 = if cmpf(lo, a) == Ordering::Less { a } else { lo };
            let h2 = if cmpf(hi, b) == Ordering::Greater { b } else { hi };
            if cmpf(l2, h2) != Ordering::Greater { out.push((l2, h2)); }
            j += 1;
        }
    }
    out
}
fn has_good(pc: &[(Fr, Fr)], w: I, p: I, q: I) -> bool {
    for &(a, b) in pc {
        let j0 = ceil_div(a.n * w * q + p * a.d - q * a.d, a.d * q);
        if (j0 * q + p) * b.d <= b.n * w * q { return true; }
    }
    false
}
fn ml_exact(vs: &[i64]) -> Fr {
    let mut best = fr(0, 1);
    let mut seen = HashSet::new();
    for i in 0..vs.len() {
        for j in i..vs.len() {
            let d = (vs[i] + vs[j]) as I;
            if !seen.insert(d) { continue; }
            let mut k: I = 1;
            while 2 * k <= d {
                let mut m = d;
                for &v in vs {
                    let r = (k * v as I) % d;
                    let x = if r < d - r { r } else { d - r };
                    if x < m { m = x; if m * best.d <= best.n * d { break; } }
                }
                if m * best.d > best.n * d { best = fr(m, d); }
                k += 1;
            }
        }
    }
    red(best)
}
fn ge(vs: &[i64], val: Fr) -> bool { !good_pieces(vs, val.n, val.d).is_empty() }
// ML == val exactly (decision engine, eps = 1/(1000003 q); valid while eps < gap between distinct ML values)
fn ml_is(vs: &[i64], val: Fr) -> bool { ge(vs, val) && !good_pieces(vs, val.n * 1000003 + 1, val.d * 1000003).is_empty() == false }
fn set_of(n: i64, r1: i64, r2: i64, w1: i64, w2: i64) -> Vec<i64> {
    let mut v: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
    v.push(w1); v.push(w2); v
}
fn witnessed(n: I, r: I, w1: I, w2: I) -> bool {
    let mut d = n + 1 + r;
    while d <= 2 * n {
        if gcd(d, r) == 1 {
            let a = w1 % d; let b = w2 % d;
            let ok = |x: I| x != 0 && x != r % d && x != (d - r % d) % d;
            if ok(a) && ok(b) { return true; }
        }
        d += 1;
    }
    false
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
    fn below(&mut self, m: u64) -> u64 { self.next() % m } }

// ---------------- closed form F (witness lower bounds), BH M2 ----------------
fn beta_of(n: I, r: I) -> (I, I) { let s = n + 1 - r; let mut b = s; while gcd(b, r) != 1 { b += 1; } (s, b) }
// L_r(m) for w = m r, other inserted speed wo
fn lower_l(n: I, r: I, w: I, wo: I) -> Fr {
    let (_s, beta) = beta_of(n, r);
    let m = w / r; let d = m * r + beta;
    let inv = inv_mod(r % d, d);
    let a = (d - inv) % d; // a r = -1 mod d
    let y = (a * (wo % d)) % d; let dist = y.min(d - y);
    fmin(fr(m, d), fr(dist, d))
}
// F = max(1/A [if A divides neither w], max over (i,j) with r_i | w_j of L_{r_i}(w_j/r_i)); None if r1 or r2 divides neither w, or r_i <= N/2
fn formula_f(n: I, r1: I, r2: I, w1: I, w2: I) -> Option<Fr> {
    if 2 * r1 <= n || 2 * r2 <= n { return None; }
    let mut best = fr(0, 1);
    for &r in &[r1, r2] {
        let mut has = false;
        for &(w, wo) in &[(w1, w2), (w2, w1)] {
            if w % r == 0 { has = true; best = fmax(best, lower_l(n, r, w, wo)); }
        }
        if !has { return None; }
    }
    let a = n + 1;
    if w1 % a != 0 && w2 % a != 0 { best = fmax(best, fr(1, a)); }
    Some(best)
}
// ---------------- arc formula E (tent and two sawtooths over unit arcs) ----------------
fn saw(w: I, c: I, r: I, eta: Fr) -> Fr {
    let num = w * c * eta.d + w * eta.n; let den = r * eta.d;
    let m = num.rem_euclid(den); let mm = if m < den - m { m } else { den - m }; red(fr(mm, den))
}
fn tent(x: I, r: I, eta: Fr) -> Fr { fdiv(fsub(fr(1, 1), fmul(fr(x, 1), eta)), fr(r, 1)) }
fn arc_max(n: I, r: I, c: I, x: I, ws: [I; 2]) -> Fr {
    let a1 = n + 1; let end = fr(1, a1);
    let mut pts: Vec<Fr> = vec![fr(0, 1), end];
    for &w in &ws {
        let mut j = (2 * w * c).div_euclid(r);
        loop {
            let e = fr(j * r - 2 * w * c, 2 * w);
            if cmpf(e, end) != Ordering::Less { break; }
            if e.n > 0 { pts.push(red(e)); }
            j += 1;
        }
    }
    pts.sort_by(|a, b| cmpf(*a, *b));
    pts.dedup_by(|a, b| feq(*a, *b));
    let f3 = |eta: Fr| -> [Fr; 3] { [tent(x, r, eta), saw(ws[0], c, r, eta), saw(ws[1], c, r, eta)] };
    let mn = |v: [Fr; 3]| fmin(v[0], fmin(v[1], v[2]));
    let mut best = fr(0, 1);
    for wdw in pts.windows(2) {
        let (a, b) = (wdw[0], wdw[1]);
        let va = f3(a); let vb = f3(b);
        best = fmax(best, mn(va)); best = fmax(best, mn(vb));
        let h = fsub(b, a);
        let sl: Vec<Fr> = (0..3).map(|i| fdiv(fsub(vb[i], va[i]), h)).collect();
        for i in 0..3 { for j in (i + 1)..3 {
            if feq(sl[i], sl[j]) { continue; }
            let e = fadd(a, fdiv(fsub(va[j], va[i]), fsub(sl[i], sl[j])));
            if cmpf(e, a) != Ordering::Less && cmpf(e, b) != Ordering::Greater { best = fmax(best, mn(f3(e))); }
        } }
    }
    best
}
// E for gcd>1, both r_i > N/2. Returns None if not applicable (a free class occurs).
fn arc_e(n: I, rs: [I; 2], ws: [I; 2]) -> Option<Fr> {
    let mut best = fr(0, 1);
    for &r in &rs {
        for c in 1..r {
            if gcd(c, r) != 1 { continue; }
            let u = (r - inv_mod(c, r)) % r;
            let x = if u + r <= n { u + r } else { u };
            if x == rs[0] || x == rs[1] { return None; }
            best = fmax(best, arc_max(n, r, c, x, ws));
        }
    }
    Some(best)
}

// ---------------- certified-complete pair engine ----------------
struct Fam { w1: I, kind: String, l: I, res: Vec<I> }
fn certpair(n: i64, r1: i64, r2: i64, excs: &mut Vec<(i64, i64)>, fams: &mut Vec<Fam>, flags: &mut Vec<String>) {
    let nn = n as I;
    if n < 5 { flags.push("N<5".into()); return; }
    let ret: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
    let g0 = good_pieces(&ret, 1, nn);
    if g0.is_empty() { flags.push("G0EMPTY(all w fail)".into()); return; }
    let mut l = fr(0, 1);
    for &(a, b) in &g0 { let x = len(a, b); if cmpf(x, l) == Ordering::Greater { l = x; } }
    if l.n == 0 { flags.push("G0POINTS".into()); return; }
    let w0 = 4 * (nn + 2) * l.d / (nn * (nn - 4) * l.n) + 1;
    if w0 > 400000 { flags.push(format!("W0cap={}", w0)); return; }
    let mut w1 = nn + 1;
    while w1 < w0 {
        let g1 = sub_speed(&g0, w1, 1, nn);
        if g1.is_empty() { fams.push(Fam { w1: w1 as I, kind: "ALL".into(), l: 0, res: vec![] }); w1 += 1; continue; }
        let mut l2 = fr(0, 1);
        for &(a, b) in &g1 { let x = len(a, b); if cmpf(x, l2) == Ordering::Greater { l2 = x; } }
        if l2.n == 0 {
            // points only: failing w2 are residue classes mod L
            let mut ll: I = 1; let mut pts = Vec::new();
            for &(a, _b) in &g1 { let a = red(a); ll = ll / gcd(ll, a.d) * a.d; pts.push(a); }
            if ll > 3_000_000 { flags.push(format!("POINT-L{}-w1={}", ll, w1)); w1 += 1; continue; }
            let mut res = Vec::new();
            for c in 0..ll {
                let mut all = true;
                for p in &pts { let x = (c * p.n).rem_euclid(p.d); let dist = x.min(p.d - x); if dist * nn >= p.d { all = false; break; } }
                if all { res.push(c); }
            }
            if !res.is_empty() { fams.push(Fam { w1: w1 as I, kind: "POINT".into(), l: ll, res }); }
            w1 += 1; continue;
        }
        let wb = ceil_div(2 * l2.d, nn * l2.n);
        if wb > 20_000_000 { flags.push(format!("WBcap w1={}", w1)); w1 += 1; continue; }
        let mut w2 = w1 + 1;
        while w2 < wb { if !has_good(&g1, w2, 1, nn) { excs.push((w1 as i64, w2 as i64)); } w2 += 1; }
        w1 += 1;
    }
}

fn famlist(f: &Fam, cap_members: usize, lo: I) -> Vec<i64> {
    // members w2 > max(w1, lo) of a family, smallest first
    let mut out = Vec::new();
    let lo = lo.max(f.w1);
    if f.kind == "ALL" { for j in 1..=(cap_members as I) { out.push((lo + j) as i64); } return out; }
    let mut j: I = lo / f.l;
    while out.len() < cap_members * f.res.len().max(1) && j < lo / f.l + 1000 {
        for &c in &f.res { let w = c + j * f.l; if w > lo { out.push(w as i64); } }
        j += 1;
    }
    out.sort(); out.truncate(cap_members); out
}

fn fam_count(f: &Fam, wmax: I) -> u64 {
    if f.kind == "ALL" { return if wmax > f.w1 { (wmax - f.w1) as u64 } else { 0 }; }
    let mut c = 0u64;
    for &r in &f.res {
        let first = if r > f.w1 { r } else { r + ((f.w1 - r) / f.l + 1) * f.l };
        if first <= wmax { c += ((wmax - first) / f.l + 1) as u64; }
    }
    c
}
struct Tally { n: u64, f_def: u64, f_eq: u64, e_def: u64, e_eq: u64, lt_n2: u64, first_f_cex: Option<String>, first_e_cex: Option<String> }

fn analyse(n: i64, r1: i64, r2: i64, w1: i64, w2: i64, tag: &str, t: &mut Tally) {
    let nn = n as I;
    let v = set_of(n, r1, r2, w1, w2);
    let ml = ml_exact(&v);
    let lt = cmpf(ml, fr(1, nn)) == Ordering::Less;
    let f = formula_f(nn, r1 as I, r2 as I, w1 as I, w2 as I);
    let e = if gcd(r1 as I, r2 as I) > 1 && 2 * r1 > n { arc_e(nn, [r1 as I, r2 as I], [w1 as I, w2 as I]) } else { None };
    t.n += 1;
    let mut fs = String::from("-"); let mut es = String::from("-");
    if let Some(ff) = f { t.f_def += 1; fs = show(ff); if feq(ff, ml) { t.f_eq += 1; } else if t.first_f_cex.is_none() { t.first_f_cex = Some(format!("N={} R=({},{}) W=({},{}) ML={} F={}", n, r1, r2, w1, w2, show(ml), fs)); } }
    else if t.first_f_cex.is_none() && lt { t.first_f_cex = Some(format!("N={} R=({},{}) W=({},{}) ML={} F=undefined", n, r1, r2, w1, w2, show(ml))); }
    if let Some(ee) = e { t.e_def += 1; let m = fmax(fr(1, nn + 1), ee); es = show(ee); if feq(m, ml) { t.e_eq += 1; } else if t.first_e_cex.is_none() { t.first_e_cex = Some(format!("N={} R=({},{}) W=({},{}) ML={} E={} max(1/A,E)={}", n, r1, r2, w1, w2, show(ml), es, show(m))); } }
    if lt { t.lt_n2 += 1; }
    println!("EXC {} N={} R=({},{}) W=({},{}) ML={} {} F={} E={} g={}", tag, n, r1, r2, w1, w2, show(ml), if lt { "<1/N" } else { ">=1/N!!" }, fs, es, gcd(r1 as I, r2 as I));
}

fn cert2(n0: i64, n1: i64, mode: &str, rwin: i64) {
    for n in n0..=n1 {
        let nn = n as I;
        let mut t = Tally { n: 0, f_def: 0, f_eq: 0, e_def: 0, e_eq: 0, lt_n2: 0, first_f_cex: None, first_e_cex: None };
        let (mut pairs, mut nfin, mut nfam, mut nflag) = (0u64, 0u64, 0u64, 0u64);
        let mut low_exc = 0u64; let mut famlines: Vec<String> = Vec::new(); let mut cnt2000 = 0u64; let mut cnt_by_r: std::collections::BTreeMap<(i64, i64), u64> = std::collections::BTreeMap::new();
        let mut t4 = (0u64, 0u64, 0u64); // (dominant exceptions, matching T4 shape, not matching)
        let mut t4bad: Vec<String> = Vec::new();
        for r1 in 1..n { for r2 in (r1 + 1)..=n {
            if rwin > 0 && r1 < n - rwin { continue; }
            let cop = gcd(r1 as I, r2 as I) == 1;
            if mode == "coprime" && !cop { continue; }
            if mode == "gcd" && cop { continue; }
            pairs += 1;
            let mut excs = Vec::new(); let mut fams = Vec::new(); let mut flags = Vec::new();
            certpair(n, r1, r2, &mut excs, &mut fams, &mut flags);
            for fl in &flags { nflag += 1; println!("FLAG N={} R=({},{}) {}", n, r1, r2, fl); }
            if 2 * r1 <= n { low_exc += excs.len() as u64 + fams.len() as u64; }
            nfin += excs.len() as u64; nfam += fams.len() as u64;
            let wcap: I = if n <= 40 { 2000 } else { 600 };
            for &(_w1, w2) in &excs { if (w2 as I) <= wcap { cnt2000 += 1; *cnt_by_r.entry((r1, r2)).or_insert(0) += 1; } }
            for f in &fams { let c = fam_count(f, wcap); cnt2000 += c; if c > 0 { *cnt_by_r.entry((r1, r2)).or_insert(0) += c; } }
            for &(w1, w2) in &excs {
                analyse(n, r1, r2, w1, w2, "fin", &mut t);
                t4_check(n, r1, r2, w1, w2, &mut t4, &mut t4bad);
            }
            for f in &fams {
                let mut mem = famlist(f, 4, 0); let mem2 = famlist(f, 4, 2 * f.w1 * f.w1 - 1); for x in mem2 { if !mem.contains(&x) { mem.push(x); } }
                famlines.push(format!("FAM N={} R=({},{}) w1={} kind={} L={} nres={} res<=8: {:?} members {:?}", n, r1, r2, f.w1, f.kind, f.l, f.res.len(), f.res.iter().take(8).collect::<Vec<_>>(), mem));
                for &w2 in &mem { analyse(n, r1, r2, f.w1 as i64, w2, "fam", &mut t); t4_check(n, r1, r2, f.w1 as i64, w2, &mut t4, &mut t4bad); }
            }
        } }
        for l in &famlines { println!("{}", l); }
        println!("CNTLE N={} wcap={} exceptions (finite + family members) with w2<=wcap: {} ; per pair: {:?}", n, if n <= 40 { 2000 } else { 600 }, cnt2000, cnt_by_r.iter().map(|(k, v)| format!("({},{}):{}", k.0, k.1, v)).collect::<Vec<_>>());
        println!("CERT2 N={} mode={} pairs={} finite-exceptions={} families={} flags={} | exceptions with r1<=N/2: {} | analysed={} (<1/N: {}) F defined {} F==ML {} | E defined {} max(1/A,E)==ML {} | T4 dominant(w2>=2w1^2) {} match {} nomatch {} | first F cex: {:?} | first E cex: {:?}",
            n, mode, pairs, nfin, nfam, nflag, low_exc, t.n, t.lt_n2, t.f_def, t.f_eq, t.e_def, t.e_eq, t4.0, t4.1, t4.2, t.first_f_cex, t.first_e_cex);
        for b in t4bad.iter().take(10) { println!("  T4NOMATCH {}", b); }
        let _ = nn;
    }
}
// T4: dominant regime w2 >= 2 w1^2: claim r2=N, w1 = m r1 with [N]_{r1->w1} tight (beta>=m s), N | w2, ML = sigma/(N sigma+1)
fn t4_check(n: i64, r1: i64, r2: i64, w1: i64, w2: i64, t4: &mut (u64, u64, u64), bad: &mut Vec<String>) {
    if (w2 as I) < 2 * (w1 as I) * (w1 as I) { return; }
    t4.0 += 1;
    let nn = n as I;
    let mut ok = r2 == n && w1 % r1 == 0 && w2 % n == 0;
    let mut why = String::new();
    if ok {
        // B = [N-1]_{r1 -> m r1}: Goddyn-Wong criterion for N' = N-1 speeds (s' = N - r1, beta' = least b >= s' coprime to r1)
        let (s, b) = beta_of(nn - 1, r1 as I); let m = (w1 / r1) as I;
        let tight = 2 * r1 > n - 1 && b >= m * s;
        let sigma = (w2 / n) as I;
        let ml = ml_exact(&set_of(n, r1, r2, w1, w2));
        let pred = fr(sigma, nn * sigma + 1);
        if !tight { ok = false; why.push_str("onE-not-tight "); }
        if !feq(ml, pred) { ok = false; why.push_str(&format!("ML={} pred={} ", show(ml), show(pred))); }
    } else { why = format!("shape r2==N:{} r1|w1:{} N|w2:{}", r2 == n, w1 % r1 == 0, w2 % n == 0); }
    if ok { t4.1 += 1; } else { t4.2 += 1; if bad.len() < 20 { bad.push(format!("N={} R=({},{}) W=({},{}) {}", n, r1, r2, w1, w2, why)); } }
}

// unpruned grid, w2 <= 3N^2
fn grid(n0: i64, n1: i64) {
    for n in n0..=n1 {
        let nn = n as I; let wmax = 3 * n * n;
        let mut exc: Vec<(i64, i64, i64, i64)> = Vec::new();
        let mut sweep = 0u64;
        for r1 in 1..n {
            let nr2 = (n - r1) as usize;
            let g0s: Vec<Vec<(Fr, Fr)>> = ((r1 + 1)..=n).map(|r2| { let ret: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect(); good_pieces(&ret, 1, nn) }).collect();
            for w1 in (n + 1)..wmax {
                let mut g1s: Vec<Option<Vec<(Fr, Fr)>>> = vec![None; nr2];
                for w2 in (w1 + 1)..=wmax {
                    if witnessed(nn, r1 as I, w1 as I, w2 as I) { continue; }
                    for (k, r2) in ((r1 + 1)..=n).enumerate() {
                        if witnessed(nn, r2 as I, w1 as I, w2 as I) { continue; }
                        if g1s[k].is_none() { g1s[k] = Some(sub_speed(&g0s[k], w1 as I, 1, nn)); }
                        sweep += 1;
                        if !has_good(g1s[k].as_ref().unwrap(), w2 as I, 1, nn) { exc.push((r1, r2, w1, w2)); }
                    }
                }
            }
        }
        let mut t = Tally { n: 0, f_def: 0, f_eq: 0, e_def: 0, e_eq: 0, lt_n2: 0, first_f_cex: None, first_e_cex: None };
        for &(r1, r2, w1, w2) in &exc { analyse(n, r1, r2, w1, w2, "grid", &mut t); }
        println!("GRID N={} wmax={} swept={} exceptions={} | F defined {} F==ML {} | E defined {} max(1/A,E)==ML {} | first F cex {:?} | first E cex {:?}", n, wmax, sweep, exc.len(), t.f_def, t.f_eq, t.e_def, t.e_eq, t.first_f_cex, t.first_e_cex);
    }
}

// F-scan: every set with F defined and w2 <= 3N^2; check (F < 1/N) <=> (ML < 1/N), and ML == F when F < 1/N
fn fscan(n0: i64, n1: i64) {
    for n in n0..=n1 {
        let nn = n as I; let wmax = 3 * n * n;
        let (mut tot, mut fl, mut exc_ok, mut f_lt_not_exc, mut ml_ne_f, mut f_ge_but_exc) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let mut firsts: Vec<String> = Vec::new();
        for r1 in (n / 2 + 1)..n { for r2 in (r1 + 1)..=n {
            let mut list: Vec<(i64, i64)> = Vec::new();
            let lcm = (r1 as I / gcd(r1 as I, r2 as I) * r2 as I) as i64;
            for w1 in (n + 1)..=wmax {
                let a1 = w1 % r1 == 0; let b1 = w1 % r2 == 0;
                if a1 || b1 { for w2 in (w1 + 1)..=wmax { if (a1 || w2 % r1 == 0) && (b1 || w2 % r2 == 0) { list.push((w1, w2)); } } }
                else { let mut w2 = (w1 / lcm + 1) * lcm; while w2 <= wmax { list.push((w1, w2)); w2 += lcm; } }
            }
            for (w1, w2) in list {
                if let Some(f) = formula_f(nn, r1 as I, r2 as I, w1 as I, w2 as I) {
                    tot += 1;
                    let flt = cmpf(f, fr(1, nn)) == Ordering::Less;
                    if flt {
                        fl += 1;
                        let v = set_of(n, r1, r2, w1, w2);
                        let ml = ml_exact(&v);
                        let exc = cmpf(ml, fr(1, nn)) == Ordering::Less;
                        if !exc { f_lt_not_exc += 1; if gcd(r1 as I, r2 as I) > 1 { f_ge_but_exc += 1; } if firsts.len() < 5 { firsts.push(format!("F<1/N but ML>=1/N: N={} R=({},{}) W=({},{}) F={} ML={}", n, r1, r2, w1, w2, show(f), show(ml))); } }
                        else if feq(ml, f) { exc_ok += 1; } else { ml_ne_f += 1; if firsts.len() < 5 { firsts.push(format!("exception with ML!=F: N={} R=({},{}) W=({},{}) F={} ML={}", n, r1, r2, w1, w2, show(f), show(ml))); } }
                    }
                }
            }
        } }
                println!("FSCAN N={} wmax={} sets-with-F-defined={} F<1/N: {} -> exception with ML==F: {} | F<1/N but ML>=1/N: {} (of which gcd>1: {}) | exception with ML!=F: {} | {:?}", n, wmax, tot, fl, exc_ok, f_lt_not_exc, f_ge_but_exc, ml_ne_f, firsts);
    }
}

// T1: random sets, gcd>1, r_i > N/2: ML == max(1/A, E) ? via decision engine at the predicted value
fn t1(n0: i64, n1: i64, s: u64) {
    let mut rng = Rng(0x2545F4914F6CDD1D);
    for n in n0..=n1 {
        let nn = n as I; let wmax = (3 * n * n) as u64;
        let (mut tot, mut ok, mut atlow, mut bad) = (0u64, 0u64, 0u64, 0u64); let mut firsts: Vec<String> = Vec::new();
        let mut tries = 0u64;
        while tot < s && tries < s * 400 {
            tries += 1;
            let r1 = n / 2 + 1 + rng.below((n - n / 2 - 1) as u64) as i64; let r2 = n / 2 + 1 + rng.below((n - n / 2 - 1) as u64) as i64;
            if r1 >= r2 || gcd(r1 as I, r2 as I) == 1 { continue; }
            let mode = rng.below(3);
            let mut w1 = n + 1 + rng.below(wmax) as i64; let mut w2 = n + 1 + rng.below(wmax) as i64;
            if mode == 0 { w1 = r1 * (2 + rng.below((wmax as i64 / r1 - 1).max(1) as u64) as i64); }
            if mode == 1 { w1 = r1 * (2 + rng.below(6) as i64); w2 = r2 * (2 + rng.below(6) as i64); }
            if w1 == w2 || w1 <= n || w2 <= n { continue; }
            let e = match arc_e(nn, [r1 as I, r2 as I], [w1 as I, w2 as I]) { Some(e) => e, None => continue };
            let val = fmax(fr(1, nn + 1), e);
            let v = set_of(n, r1, r2, w1, w2);
            tot += 1;
            let up = !good_pieces(&v, val.n * 1000003 + 1, val.d * 1000003).is_empty();
            let dn = ge(&v, val);
            if dn && !up { ok += 1; } else { bad += 1; if firsts.len() < 5 { firsts.push(format!("N={} R=({},{}) W=({},{}) E={} val={} ge(val)={} ge(val+eps)={} A|w:{}", n, r1, r2, w1, w2, show(e), show(val), dn, up, (w1 as I % (nn + 1) == 0) || (w2 as I % (nn + 1) == 0))); } }
            if cmpf(e, fr(1, nn + 1)) != Ordering::Greater { atlow += 1; }
        }
        println!("T1 N={} sets={} ML==max(1/A,E): {} failures: {} (of which E<=1/A: {}) {:?}", n, tot, ok, bad, atlow, firsts);
    }
}

// ---------------- control ----------------
fn ctl() {
    let mut fails = 0;
    // planted: Zhang Example 5.2, N=73 R=(70,72) W=(140,144): ML = 1/74 tight
    let v = set_of(73, 70, 72, 140, 144);
    let m = ml_exact(&v); let f = formula_f(73, 70, 72, 140, 144).unwrap(); let e = arc_e(73, [70, 72], [140, 144]).unwrap();
    println!("ctl N=73 (70,72;140,144): ML={} F={} E={} max(1/A,E)={}", show(m), show(f), show(e), show(fmax(fr(1, 74), e)));
    if !(feq(m, fr(1, 74)) && feq(f, fr(1, 74)) && feq(fmax(fr(1, 74), e), fr(1, 74))) { fails += 1; }
    let v = set_of(73, 70, 72, 140, 216);
    let m = ml_exact(&v); let f = formula_f(73, 70, 72, 140, 216).unwrap(); let e = arc_e(73, [70, 72], [140, 216]).unwrap();
    println!("ctl N=73 (70,72;140,216): ML={} F={} E={} (G(73)=3/221 expected)", show(m), show(f), show(e));
    if !feq(m, fr(3, 221)) { fails += 1; }
    // N=14 planted (10,14;20,98) ML 7/99
    let m = ml_exact(&set_of(14, 10, 14, 20, 98)); let f = formula_f(14, 10, 14, 20, 98).unwrap(); let e = arc_e(14, [10, 14], [20, 98]).unwrap();
    println!("ctl N=14 (10,14;20,98): ML={} F={} E={} (7/99 expected)", show(m), show(f), show(e));
    if !feq(m, fr(7, 99)) || !feq(f, m) { fails += 1; }
    // negative control for the decision engine: ml_is at value and at value +/- one step
    let v = set_of(14, 10, 14, 20, 98);
    let a = ml_is(&v, fr(7, 99)); let b = ml_is(&v, fr(8, 99)); let c = ml_is(&v, fr(6, 99));
    println!("ctl ml_is(7/99)={} ml_is(8/99)={} ml_is(6/99)={} (expect true,false,false)", a, b, c);
    if !(a && !b && !c) { fails += 1; }
    // planted E/ML on random sets
    let mut rng = Rng(88172645463325252); let mut mism = 0; let mut tot = 0;
    for _ in 0..300 {
        let n = 14 + rng.below(12) as i64; let r1 = n / 2 + 1 + rng.below((n - n / 2 - 1) as u64) as i64; let r2 = n / 2 + 1 + rng.below((n - n / 2 - 1) as u64) as i64;
        if r1 >= r2 || gcd(r1 as I, r2 as I) == 1 { continue; }
        let w1 = n + 1 + rng.below(200) as i64; let w2 = n + 1 + rng.below(400) as i64; if w1 == w2 { continue; }
        let nn = n as I;
        let e = match arc_e(nn, [r1 as I, r2 as I], [w1 as I, w2 as I]) { Some(e) => e, None => continue };
        let ml = ml_exact(&set_of(n, r1, r2, w1, w2)); tot += 1;
        // E <= ML always (E is attained); ML <= max(1/A,E)
        if cmpf(e, ml) == Ordering::Greater || cmpf(ml, fmax(fr(1, nn + 1), e)) == Ordering::Greater { mism += 1; }
    }
    println!("ctl random: sets={} violations of E<=ML<=max(1/A,E): {}", tot, mism);
    if mism > 0 { fails += 1; }
    println!("CTL TOTAL FAILS = {}", fails);
}
fn tsv(path: &str) {
    let txt = std::fs::read_to_string(path).unwrap();
    let (mut tot, mut fok, mut eok, mut edef, mut fdef, mut first) = (0, 0, 0, 0, 0, String::new());
    for line in txt.lines() {
        if line.starts_with('#') || line.trim().is_empty() { continue; }
        let f: Vec<&str> = line.split('\t').collect();
        let n: i64 = f[0].parse().unwrap(); let r1: i64 = f[1].parse().unwrap(); let r2: i64 = f[2].parse().unwrap(); let w1: i64 = f[3].parse().unwrap(); let w2: i64 = f[4].parse().unwrap();
        let mv: Vec<&str> = f[5].split('/').collect(); let ml = fr(mv[0].parse().unwrap(), mv[1].parse().unwrap());
        tot += 1;
        if let Some(ff) = formula_f(n as I, r1 as I, r2 as I, w1 as I, w2 as I) { fdef += 1; if feq(ff, ml) { fok += 1; } else if first.is_empty() { first = format!("F!=ML at {}", line); } }
        if gcd(r1 as I, r2 as I) > 1 && 2 * r1 > n {
            if let Some(e) = arc_e(n as I, [r1 as I, r2 as I], [w1 as I, w2 as I]) { edef += 1; if feq(fmax(fr(1, n as I + 1), e), ml) { eok += 1; } else if first.is_empty() { first = format!("max(1/A,E)!=ML at {} E={}", line, show(e)); } }
        }
    }
    println!("TSV rows={} F defined {} F==ML {} | E defined {} max(1/A,E)==ML {} | first mismatch: {}", tot, fdef, fok, edef, eok, first);
}

// ---------------- plan 3 ----------------
struct One { l: Fr, eq: Vec<(I, I)>, vmu: I, dstar: I, dlcm: I, l2: Fr, neq: usize }
fn one_scan(vs: &[i64]) -> One {
    let m = *vs.iter().max().unwrap() as I;
    let mut best = fr(0, 1);
    for s in 3..=(2 * m - 1) {
        for k in 1..=(s / 2) {
            if gcd(k, s) != 1 { continue; }
            let mut mn = s; let mut ok = true;
            for &v in vs {
                let r = (k * v as I) % s; let x = r.min(s - r);
                if x < mn { mn = x; if mn * best.d < best.n * s { ok = false; break; } }
            }
            if ok && mn * best.d > best.n * s { best = fr(mn, s); }
        }
    }
    best = red(best);
    let mut best2 = fr(0, 1);
    let mut eq: Vec<(I, I)> = Vec::new(); let mut vmu: I = I::MAX; let mut dstar: I = 0; let mut dlcm: I = 1;
    for s in 3..=(2 * m - 1) {
        for k in 1..=(s / 2) {
            if gcd(k, s) != 1 { continue; }
            let mut mn = s; let mut ok = true;
            for &v in vs {
                let r = (k * v as I) % s; let x = r.min(s - r);
                if x < mn { mn = x; if mn * best2.d <= best2.n * s { ok = false; break; } }
            }
            if !ok { continue; }
            let val = fr(mn, s);
            if mn == 0 { continue; }
            // sign structure
            let (mut rho, mut lam) = (0 as I, 0 as I);
            for &v in vs { let r = (k * v as I) % s; if r == mn { rho = rho.max(v as I); } if r == s - mn { lam = lam.max(v as I); } }
            if 2 * mn == s { continue; }
            if rho == 0 || lam == 0 { continue; } // not a local maximum
            if feq(val, best) {
                eq.push((k, s));
                let mu = rho.min(lam);
                if mu < vmu || (mu == vmu && s < dstar) { vmu = mu; dstar = s; }
                dlcm = dlcm / gcd(dlcm, s) * s;
            } else if cmpf(val, best) == Ordering::Less && cmpf(val, best2) == Ordering::Greater { best2 = val; }
        }
    }
    One { l: best, eq, vmu, dstar, dlcm, l2: red(best2), neq: 0 }
}
fn d0_of(n: I, r: I) -> I { let mut d = n + 1 + r; while gcd(d, r) != 1 { d += 1; } d }
fn one(n0: i64, n1: i64) {
    let (mut tot, mut guess_ok) = (0u64, 0u64);
    for n in n0..=n1 {
        for r in 1..=(n / 2) {
            let vs: Vec<i64> = (1..=n).filter(|&x| x != r).collect();
            let o = one_scan(&vs);
            let d0 = d0_of(n as I, r as I);
            let g = feq(o.l, fr(2, d0));
            tot += 1; if g { guess_ok += 1; }
            let _ = o.neq;
            println!("ONE N={} r={} L={} D0={} guess={} neq={} D={} dstar={} vmu={} L2={} eqk={:?}", n, r, show(o.l), d0, if g { "OK" } else { "FAIL" }, o.eq.len(), o.dlcm, o.dstar, o.vmu, show(o.l2), o.eq.iter().take(3).collect::<Vec<_>>());
        }
    }
    println!("ONE-SUMMARY N={}..{} rows={} guess L=2/D0 holds in {}", n0, n1, tot, guess_ok);
}
// K*: ML([N]\{r} u {w}) = wL/(w+vmu) for w multiple of D, w >= 2N^3 (decision engine, exact)
fn kstar(n0: i64, n1: i64) {
    for n in n0..=n1 {
        let (mut tot, mut ok) = (0u64, 0u64); let mut firsts: Vec<String> = Vec::new();
        for r in 1..=(n / 2) {
            let vs: Vec<i64> = (1..=n).filter(|&x| x != r).collect();
            let o = one_scan(&vs);
            let thr = 2 * (n as I).pow(3);
            let j0 = ceil_div(thr, o.dlcm);
            for j in [j0, j0 + 1, j0 + 2] {
                let w = j * o.dlcm;
                let pred = red(fr(w * o.l.n, o.l.d * (w + o.vmu)));
                let mut v = vs.clone(); v.push(w as i64);
                tot += 1;
                let t = 4 * w;
                let ge_v = ge(&v, pred);
                let up = !good_pieces(&v, pred.n * t + 1, pred.d * t).is_empty();
                if ge_v && !up { ok += 1; } else if firsts.len() < 4 { firsts.push(format!("N={} r={} w={} pred={} ge={} ge(+eps)={}", n, r, w, show(pred), ge_v, up)); }
            }
        }
        println!("KSTAR N={} cases={} ML==wL/(w+vmu): {} {:?}", n, tot, ok, firsts);
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let cmd = a.get(1).map(|s| s.as_str()).unwrap_or("");
    let p = |i: usize| -> i64 { a[i].parse().unwrap() };
    match cmd {
        "ctl" => ctl(),
        "tsv" => tsv(&a[2]),
        "cert2" => cert2(p(2), p(3), a.get(4).map(|s| s.as_str()).unwrap_or("all"), a.get(5).map(|s| s.parse().unwrap()).unwrap_or(0)),
        "grid" => grid(p(2), p(3)),
        "fscan" => fscan(p(2), p(3)),
        "t1" => t1(p(2), p(3), p(4) as u64),
        "one" => one(p(2), p(3)),
        "kstar" => kstar(p(2), p(3)),
        "t4conv" => t4conv(p(2), p(3)),
        "freearc" => freearc(p(2), p(3)),
        _ => eprintln!("usage"),
    }
}

// T4 converse: B = [N-1]_{r1 -> m r1} Goddyn-Wong tight (N'=N-1, beta' >= m s'), w2 = sigma N >= 2 w1^2: ML(V) == sigma/(N sigma+1) ?
fn t4conv(n0: i64, n1: i64) {
    for n in n0..=n1 {
        let nn = n as I;
        let (mut cases, mut ok) = (0u64, 0u64); let mut firsts: Vec<String> = Vec::new(); let mut npairs = 0u64;
        for r1 in 1..n {
            if 2 * r1 <= n - 1 { continue; }
            let (s, b) = beta_of(nn - 1, r1 as I);
            let mut m: I = 2;
            while m * s <= b {
                npairs += 1;
                let w1 = m * r1 as I;
                let sig0 = ceil_div(2 * w1 * w1, nn);
                for sg in [sig0, sig0 + 1, sig0 + 2] {
                    let w2 = sg * nn; if w2 <= w1 { continue; }
                    let v = set_of(n, r1, n, w1 as i64, w2 as i64);
                    let pred = fr(sg, nn * sg + 1);
                    cases += 1;
                    let a = ge(&v, pred); let up = !good_pieces(&v, pred.n * 1000003 + 1, pred.d * 1000003).is_empty();
                    if a && !up { ok += 1; } else if firsts.len() < 4 { firsts.push(format!("N={} r1={} w1={} w2={} pred={} ge={} ge(+eps)={}", n, r1, w1, w2, show(pred), a, up)); }
                }
                m += 1;
            }
        }
        println!("T4CONV N={} (r1,m) tight pairs={} cases={} ML==sigma/(N sigma+1): {} {:?}", n, npairs, cases, ok, firsts);
    }
}

// free arc lemma check: coprime r1<r2 in (N/2,N]; for each entry r (other speed o) the class c with c*o = -1 mod r (u = o mod r) is free
// (largest class element removed); on t=(c+eta)/r, 0<=eta<=1/A every retained speed has ||vt|| >= 1/N.  Exact test via good_pieces of Ret at tau=1/N.
fn freearc(n0: i64, n1: i64) {
    for n in n0..=n1 {
        let nn = n as I; let (mut tot, mut ok) = (0u64, 0u64); let mut firsts: Vec<String> = Vec::new();
        for r1 in (n / 2 + 1)..n { for r2 in (r1 + 1)..=n {
            if gcd(r1 as I, r2 as I) != 1 { continue; }
            let ret: Vec<i64> = (1..=n).filter(|&x| x != r1 && x != r2).collect();
            let g0 = good_pieces(&ret, 1, nn);
            for &(r, o) in &[(r2, r1), (r1, r2)] {
                let rr = r as I; let u = (o as I) % rr; // class of o
                let c = (rr - inv_mod(u, rr)) % rr; // c*u = -1 mod r
                let ta = fr(c, rr); let tb = fr(c * (nn + 1) + 1, rr * (nn + 1)); // t=(c+eta)/r, eta in [0,1/A]
                // fold into [0,1/2]
                let half = fr(1, 2);
                let mut segs: Vec<(Fr, Fr)> = Vec::new();
                if cmpf(tb, half) != Ordering::Greater { segs.push((ta, tb)); }
                else if cmpf(ta, half) != Ordering::Less { segs.push((fsub(fr(1, 1), tb), fsub(fr(1, 1), ta))); }
                else { segs.push((ta, half)); segs.push((fsub(fr(1, 1), tb), half)); }
                tot += 1;
                let covered = segs.iter().all(|&(a, b)| g0.iter().any(|&(pa, pb)| cmpf(pa, a) != Ordering::Greater && cmpf(b, pb) != Ordering::Greater));
                if covered { ok += 1; } else if firsts.len() < 3 { firsts.push(format!("N={} R=({},{}) entry r={} c={}", n, r1, r2, r, c)); }
            }
        } }
        println!("FREEARC N={} free arcs={} retained speeds >= 1/N on whole arc: {} {:?}", n, tot, ok, firsts);
    }
}
