// the accompanying code instrument. Exact integer arithmetic only.
// mode ins  : test the insertion formula  ML(B u {w}) <= max_p H_p(w) (all w) and = (w large)
// mode stab : enumerate primitive N-subsets of [1,H] with ML < 1/N and classify them
// mode ctl  : negative controls on known values
use std::env;

fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }

/// ML(V) >= a/b ?  (0 < a/b <= 1/2). Closed allowed set nonempty iff some t=(j+a/b)/u, u in V, is allowed.
fn ge(v: &[u64], a: u128, b: u128) -> bool {
    for &u in v {
        let u = u as u128;
        let ub = u * b;
        let lo = u * a;
        let hi = ub - lo;
        'j: for j in 0..u {
            let num = j * b + a;
            for &x in v {
                let r = (x as u128 * num) % ub;
                if r < lo || r > hi { continue 'j; }
            }
            return true;
        }
    }
    false
}

/// exact ML(V) as (num, den) (not reduced), via candidate peaks k/d, d in {u+v, 2u}.
fn ml_exact(v: &[u64]) -> (u64, u64) {
    let mut ds: Vec<u64> = Vec::new();
    for i in 0..v.len() { ds.push(2 * v[i]); for j in i + 1..v.len() { ds.push(v[i] + v[j]); } }
    ds.sort(); ds.dedup();
    let (mut bn, mut bd) = (0u64, 1u64);
    for &d in &ds {
        for k in 1..=d / 2 {
            let mut m = d;
            for &x in v { let r = (x * k) % d; let q = r.min(d - r); if q < m { m = q; if (m as u128) * (bd as u128) <= (bn as u128) * (d as u128) { break; } } }
            if (m as u128) * (bd as u128) > (bn as u128) * (d as u128) { bn = m; bd = d; }
        }
    }
    let g = gcd(bn as u128, bd as u128) as u64; (bn / g, bd / g)
}

#[derive(Clone, Debug)]
struct Peak { k: u64, d: u64, a: u64, rho: u64, lam: u64 }

/// all local maxima of f_B on (0,1): p=k/d reduced, d<=2M-1, value a/d, slopes rho (left), lam (right)
fn peaks(b: &[u64]) -> Vec<Peak> {
    let m = *b.iter().max().unwrap();
    let mut out = Vec::new();
    for d in 2..=(2 * m - 1) {
        for k in 1..d {
            if gcd(k as u128, d as u128) != 1 { continue; }
            let mut a = d;
            for &x in b { let r = (x * k) % d; a = a.min(r.min(d - r)); }
            if a == 0 { continue; }
            let (mut rho, mut lam) = (0u64, 0u64);
            for &x in b { let r = (x * k) % d; if r == a { rho = rho.max(x); } if r == d - a { lam = lam.max(x); } }
            if rho > 0 && lam > 0 { out.push(Peak { k, d, a, rho, lam }); }
        }
    }
    out
}

/// H_p(w) as a fraction (num, den)
fn hp(p: &Peak, w: u64) -> (u128, u128) {
    let (d, a) = (p.d as u128, p.a as u128);
    let e = ((w as u128) * (p.k as u128)) % d;
    let th = e.min(d - e);
    if th >= a { return (a, d); }
    let w = w as u128; let (rho, lam) = (p.rho as u128, p.lam as u128);
    let pos = 2 * e <= d; // theta >= 0
    let (ln, ld, rn, rd);
    if pos { rn = w * a + lam * th; rd = d * (w + lam); ln = (w * a).saturating_sub(rho * th); ld = d * (w + rho); }
    else { ln = w * a + rho * th; ld = d * (w + rho); rn = (w * a).saturating_sub(lam * th); rd = d * (w + lam); }
    if ln * rd >= rn * ld { (ln, ld) } else { (rn, rd) }
}

fn hmax(ps: &[Peak], w: u64) -> (u128, u128) {
    let (mut n, mut d) = (0u128, 1u128);
    for p in ps { let (a, b) = hp(p, w); if a * d > n * b { n = a; d = b; } }
    let g = gcd(n, d); (n / g, d / g)
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } }

struct InsStat { cases: u64, uviol: u64, eqfail: u64, eqfail_2m2: u64, eqfail_m2: u64, worst: f64, worst_s: String, lipviol: u64 }

fn ins_base(b: &[u64], wfac: u64, st: &mut InsStat, verbose: bool) {
    let m = *b.iter().max().unwrap();
    let (ln, ld) = ml_exact(b);
    if 2 * ln == ld { return; }
    let ps = peaks(b);
    // sanity: top peak value equals ML(B)
    let top = ps.iter().map(|p| (p.a as u128, p.d as u128)).fold((0u128, 1u128), |acc, x| if x.0 * acc.1 > acc.0 * x.1 { x } else { acc });
    assert!(top.0 * ld as u128 == ln as u128 * top.1, "peak/ML mismatch {:?}", b);
    let mut lastfail = 0u64;
    for w in (m + 1)..=(wfac * m * m) {
        if b.contains(&w) { continue; }
        let mut v = b.to_vec(); v.push(w);
        let (hn, hd) = hmax(&ps, w);
        st.cases += 1;
        // (U): ML > H ?  ML has denominator <= 2w, so ML > H iff ML >= H + 1/(2w*hd)
        let tw = 2 * w as u128;
        if ge(&v, tw * hn + 1, tw * hd) { st.uviol += 1; if verbose || st.uviol < 6 { println!("UVIOL B={:?} w={} H={}/{}", b, w, hn, hd); } }
        let eq = ge(&v, hn, hd);
        if !eq {
            st.eqfail += 1; lastfail = w;
            if w >= 2 * m * m { st.eqfail_2m2 += 1; if st.eqfail_2m2 < 6 { println!("EQFAIL>=2M^2 B={:?} w={} H={}/{}", b, w, hn, hd); } }
            if w >= m * m { st.eqfail_m2 += 1; }
        }
        // Lipschitz inheritance: ML(V) >= w L/(w+M)
        if !ge(&v, w as u128 * ln as u128, ld as u128 * (w + m) as u128) { st.lipviol += 1; }
    }
    let ratio = lastfail as f64 / (m * m) as f64;
    if ratio > st.worst { st.worst = ratio; st.worst_s = format!("B={:?} last eq-fail w={} M={} w/M^2={:.3}", b, lastfail, m, ratio); }
}

fn mode_ins(args: &[String]) {
    let nb: u64 = args[0].parse().unwrap(); let maxs: u64 = args[1].parse().unwrap(); let wfac: u64 = args[2].parse().unwrap();
    let mut st = InsStat { cases: 0, uviol: 0, eqfail: 0, eqfail_2m2: 0, eqfail_m2: 0, worst: 0.0, worst_s: String::new(), lipviol: 0 };
    let mut nbases = 0;
    // structured
    let mut structured: Vec<Vec<u64>> = vec![vec![1, 3, 4, 7], vec![1, 3, 4, 5, 9], vec![1, 2, 3, 4, 5, 7, 12], vec![1, 5, 6, 11], vec![2, 4, 6, 8], vec![2, 3, 5, 7, 11]];
    for n in 2..=11u64 { structured.push((1..=n).collect()); for r in 1..=n { let b: Vec<u64> = (1..=n).filter(|&x| x != r).collect(); if b.len() >= 2 { structured.push(b); } } }
    for b in &structured { if *b.iter().max().unwrap() <= maxs.max(12) { ins_base(b, wfac, &mut st, false); nbases += 1; } }
    println!("structured done: bases={} cases={} Uviol={} eqfail={} eqfail(w>=M^2)={} eqfail(w>=2M^2)={} lipviol={} worst: {}", nbases, st.cases, st.uviol, st.eqfail, st.eqfail_m2, st.eqfail_2m2, st.lipviol, st.worst_s);
    let mut rng = Rng(0x9E3779B97F4A7C15);
    for i in 0..nb {
        let sz = 2 + (rng.next() % 5) as usize;
        let mut b: Vec<u64> = Vec::new();
        while b.len() < sz { let x = 1 + rng.next() % maxs; if !b.contains(&x) { b.push(x); } }
        b.sort();
        ins_base(&b, wfac, &mut st, false); nbases += 1;
        if i % 50 == 49 { println!("progress {}/{} cases={} Uviol={} eqfail={} (>=M^2: {}, >=2M^2: {}) lipviol={}", i + 1, nb, st.cases, st.uviol, st.eqfail, st.eqfail_m2, st.eqfail_2m2, st.lipviol); }
    }
    println!("FINAL ins: bases={} cases={} Uviol={} eqfail={} eqfail(w>=M^2)={} eqfail(w>=2M^2)={} lipviol={}", nbases, st.cases, st.uviol, st.eqfail, st.eqfail_m2, st.eqfail_2m2, st.lipviol);
    println!("worst last-failure ratio: {}", st.worst_s);
}

struct StabStat { n: usize, h: u64, sets: u64, exc: u64, hist: Vec<u64>, top_nondescent: u64, no_tight_sub: u64, kbig: u64, maxratio: f64, maxratio_s: String, tight: u64, tight_maxw_nm: f64, tight_s: String, far: Vec<String>, nts: Vec<String>, lacun_exc: u64, lacun_bad: u64 }

fn stab_leaf(v: &[u64], st: &mut StabStat) {
    st.sets += 1;
    let n = st.n as u64;
    if ge(v, 1, n as u128) { return; }
    st.exc += 1;
    let (a, b) = ml_exact(v);
    assert!(a * n < b);
    let dist = v.iter().filter(|&&x| x > n).count();
    st.hist[dist] += 1;
    let k = b - a * n;
    if 2 * k > n { st.kbig += 1; }
    let w = v[v.len() - 1]; let m = v[v.len() - 2];
    let base = &v[..v.len() - 1];
    let (ba, bb) = ml_exact(base);
    let top_tight_or_less = ba * n <= bb;
    if !top_tight_or_less {
        st.top_nondescent += 1;
        let r = w as f64 / (m * m) as f64;
        if r > st.maxratio { st.maxratio = r; st.maxratio_s = format!("{:?} ML={}/{} ML(B)={}/{} w/M^2={:.4}", v, a, b, ba, bb, r); }
    }
    if w >= 2 * m * m { st.lacun_exc += 1; if !top_tight_or_less { st.lacun_bad += 1; } }
    let mut any = false;
    for i in 0..v.len() { let mut s = v.to_vec(); s.remove(i); let (sa, sb) = ml_exact(&s); if sa * n == sb { any = true; break; } }
    if !any { st.no_tight_sub += 1; if st.nts.len() < 25 { st.nts.push(format!("{:?} ML={}/{} k={} dist={}", v, a, b, k, dist)); } }
    if a * (n + 1) == b { st.tight += 1; let r = w as f64 / (n * m) as f64; if r > st.tight_maxw_nm { st.tight_maxw_nm = r; st.tight_s = format!("{:?} w/(N*M)={:.3}", v, r); } }
    if dist >= 3 && st.far.len() < 25 { st.far.push(format!("{:?} ML={}/{} k={} dist={} tightsub={}", v, a, b, k, dist, any)); }
}

fn stab_rec(v: &mut Vec<u64>, start: u64, g: u64, st: &mut StabStat) {
    if v.len() == st.n { if g == 1 { stab_leaf(v, st); } return; }
    let need = (st.n - v.len()) as u64;
    for x in start..=(st.h - need + 1) {
        v.push(x);
        stab_rec(v, x + 1, gcd(g as u128, x as u128) as u64, st);
        v.pop();
    }
}

fn mode_stab(args: &[String]) {
    let n: usize = args[0].parse().unwrap(); let h: u64 = args[1].parse().unwrap();
    let mut st = StabStat { n, h, sets: 0, exc: 0, hist: vec![0; n + 1], top_nondescent: 0, no_tight_sub: 0, kbig: 0, maxratio: 0.0, maxratio_s: String::new(), tight: 0, tight_maxw_nm: 0.0, tight_s: String::new(), far: vec![], nts: vec![], lacun_exc: 0, lacun_bad: 0 };
    let mut v = Vec::new();
    stab_rec(&mut v, 1, 0, &mut st);
    println!("STAB N={} H={} primitive sets={} exceptions(ML<1/N)={} tight={}", n, h, st.sets, st.exc, st.tight);
    println!("  hist by |V minus [N]|: {:?}", st.hist);
    println!("  k=b-aN > N/2 (Fan-Sun shape violated): {}", st.kbig);
    println!("  top-removal base has ML > 1/N: {} ; max w/M^2 among them: {}", st.top_nondescent, st.maxratio_s);
    println!("  exceptions with w>=2M^2: {} of which ML(B)>1/N: {}", st.lacun_exc, st.lacun_bad);
    println!("  no tight (N-1)-subset: {}", st.no_tight_sub);
    for s in &st.nts { println!("    NTS {}", s); }
    println!("  tight sets: max w/(N*M): {}", st.tight_s);
    for s in &st.far { println!("    FAR {}", s); }
}

fn mode_ctl() {
    let chk = |v: &[u64], a: u64, b: u64| { let r = ml_exact(v); let ok = r == (a, b) && ge(v, a as u128, b as u128) && !ge(v, (a * 1000 + 1) as u128, (b * 1000) as u128); println!("ctl {:?} expect {}/{} got {}/{} {}", v, a, b, r.0, r.1, if ok { "OK" } else { "FAIL" }); };
    chk(&[1, 2, 3, 4, 5, 6], 1, 7); chk(&[1, 5, 6, 11, 16, 17], 5, 33); chk(&[1, 3, 4, 7], 1, 5);
    chk(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 36], 3, 41); chk(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 24], 1, 14);
    chk(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 29, 31], 2, 41);
    // planted wrong value must FAIL
    let r = ml_exact(&[1, 2, 3, 4, 5, 6]); println!("ctl planted wrong (1/6 for [6]): {}", if r == (1, 6) { "FAIL(control broken)" } else { "correctly rejected" });
    // insertion formula on Kravitz 5.1: B=[5], w=12 -> 2/13
    let ps = peaks(&[1, 2, 3, 4, 5]); let h = hmax(&ps, 12); println!("ctl H([5],12) = {}/{} expect 2/13; H([5],13) = {:?} expect 1/6", h.0, h.1, hmax(&ps, 13));
}

fn mode_pt(args: &[String]) {
    let b: Vec<u64> = args[0].split(',').map(|x| x.parse().unwrap()).collect();
    let (ln, ld) = ml_exact(&b); let ps = peaks(&b); let m = *b.iter().max().unwrap();
    let tops: Vec<String> = ps.iter().filter(|p| p.a * ld == ln * p.d).map(|p| format!("{}/{}(rho{},lam{})", p.k, p.d, p.rho, p.lam)).collect();
    println!("B={:?} ML={}/{} M={} peaks={} top peaks: {}", b, ln, ld, m, ps.len(), tops.join(" "));
    for a in &args[1..] { let w: u64 = a.parse().unwrap(); let mut v = b.clone(); v.push(w); let (hn, hd) = hmax(&ps, w); let tw = 2 * w as u128;
        println!("  w={} (w/M^2={:.2}) H={}/{} ML>=H:{} ML>H:{}", w, w as f64 / (m * m) as f64, hn, hd, ge(&v, hn, hd), ge(&v, tw * hn + 1, tw * hd)); }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match args[1].as_str() { "ins" => mode_ins(&args[2..]), "stab" => mode_stab(&args[2..]), "ctl" => mode_ctl(), "pt" => mode_pt(&args[2..]), _ => panic!("mode") }
}
