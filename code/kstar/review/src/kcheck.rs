// Reviewer's own engine. Exact integer arithmetic, no floats except the grid sanity mode.
// ML(V) = max over t = k/(u+v), u<=v in V, of min_x ||x t||  (local maxima of a min of tents are tent peaks k/(2v) or rise/fall crossings k/(u+v)).
use std::cmp::Ordering;
use std::cmp::Ordering::*;
use std::collections::BTreeSet;
use std::env;
type Fr = (u64, u64);
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn fcmp(a: Fr, b: Fr) -> Ordering { (a.0 as u128 * b.1 as u128).cmp(&(b.0 as u128 * a.1 as u128)) }
fn fred(a: Fr) -> Fr { let g = gcd(a.0, a.1); if g == 0 { a } else { (a.0 / g, a.1 / g) } }
#[inline] fn dist(x: u64, q: u64) -> u64 { let r = x % q; if r < q - r { r } else { q - r } }
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
  fn below(&mut self, n: u64) -> u64 { self.next() % n } }

struct Info { l: Fr, m: u64, eqs: Vec<(u64, u64)>, cands: Vec<(u64, u64, u64)>, dl: Option<u128>, vmu: u64, dstar: u64, l2: Fr, l1viol: u32, nlm: usize }

fn analyse(b: &[u64]) -> Option<Info> {
    let m = *b.iter().max().unwrap();
    let mut set = BTreeSet::new();
    for i in 0..b.len() { for j in i..b.len() { let q = b[i] + b[j]; for k in 0..q { let g = gcd(k, q); set.insert((k / g, q / g)); } } }
    let mut cands = Vec::new(); let mut best: Fr = (0, 1);
    for &(k, d) in &set { let f = b.iter().map(|&v| dist(v * k, d)).min().unwrap(); cands.push((k, d, f)); if fcmp((f, d), best) == Greater { best = (f, d); } }
    let l = fred(best);
    let half_only = env::var("HALFONLY").is_ok(); if half_only { if 2 * l.0 != l.1 { return None; } } else if 2 * l.0 >= l.1 { return None; }
    let eqs: Vec<(u64, u64)> = cands.iter().filter(|c| fcmp((c.2, c.1), l) == Equal).map(|c| (c.0, c.1)).collect();
    let p = 8 * m * m; let mut lm: Vec<Fr> = vec![]; let mut l1viol = 0u32;
    for &(k, d, f) in &cands {
        if f == 0 || k == 0 { continue; }
        let mm = d * p; let nr = k * p + 1; let nl = k * p - 1;
        let fr = b.iter().map(|&v| dist(v * nr, mm)).min().unwrap();
        let fl = b.iter().map(|&v| dist(v * nl, mm)).min().unwrap();
        let ft = (f, d);
        if fcmp((fr, mm), ft) != Greater && fcmp((fl, mm), ft) != Greater {
            let val = fred(ft); lm.push(val);
            if d > 2 * m - 1 || 2 * val.0 >= val.1 { l1viol += 1; }
        }
    }
    let mut l2: Fr = (0, 1);
    for &v in &lm { if fcmp(v, l) == Less && fcmp(v, l2) == Greater { l2 = v; } }
    let lm2: BTreeSet<Fr> = lm.iter().cloned().collect(); let lv: Vec<Fr> = lm2.into_iter().collect();
    let mm1 = (2 * m - 1) as u128;
    for i in 0..lv.len() { for j in 0..i {
        let (a, c) = (lv[i], lv[j]);
        let num = (a.0 as u128 * c.1 as u128).abs_diff(c.0 as u128 * a.1 as u128);
        if num * mm1 * mm1 < a.1 as u128 * c.1 as u128 { l1viol += 1; } } }
    let (a, bb) = l;
    let mut vmu = u64::MAX; let mut per: Vec<(u64, u64)> = vec![];
    for &(k, d) in &eqs {
        let mut rho = 0; let mut lam = 0;
        for &v in b { let r = (v * k) % d; if r * bb == a * d { rho = rho.max(v); } if r * bb == (bb - a) * d { lam = lam.max(v); } }
        if rho == 0 || lam == 0 { l1viol += 1; continue; }
        vmu = vmu.min(rho.min(lam)); per.push((d, rho.min(lam)));
    }
    let dstar = per.iter().filter(|x| x.1 == vmu).map(|x| x.0).min().unwrap_or(0);
    let mut dl: Option<u128> = Some(1);
    for &(_, d) in &eqs { if let Some(x) = dl { let g = { let (mut aa, mut bb2) = (x, d as u128); while bb2 != 0 { let t = aa % bb2; aa = bb2; bb2 = t; } aa };
        let n = x / g * d as u128; dl = if n > 1_000_000_000_000_000_000u128 { None } else { Some(n) }; } }
    Some(Info { l, m, eqs, cands, dl, vmu, dstar, l2, l1viol, nlm: lv.len() })
}

fn ml_add(b: &[u64], info: &Info, w: u64) -> Fr {
    let mut best: Fr = (0, 1);
    for &(k, d, f) in &info.cands { let v = f.min(dist(w * k, d)); if fcmp((v, d), best) == Greater { best = (v, d); } }
    let us: Vec<u64> = b.iter().cloned().chain(std::iter::once(w)).collect();
    for &u in &us {
        let q = u + w;
        for k in 0..q {
            let mut dn = dist(w * k, q);
            if dn * best.1 <= best.0 * q { continue; }
            let mut ok = true;
            for &v in b { let x = dist(v * k, q); if x < dn { dn = x; if dn * best.1 <= best.0 * q { ok = false; break; } } }
            if ok { best = (dn, q); }
        }
    }
    fred(best)
}
// plain ML of a set (no analyse restrictions)
fn ml_plain(v: &[u64]) -> Fr {
    let mut best: Fr = (0, 1);
    for i in 0..v.len() { for j in i..v.len() { let q = v[i] + v[j]; for k in 0..q {
        let f = v.iter().map(|&x| dist(x * k, q)).min().unwrap(); if fcmp((f, q), best) == Greater { best = (f, q); } } } }
    fred(best)
}
fn bpush(b: &[u64], w: u64) -> Vec<u64> { let mut v = b.to_vec(); v.push(w); v.sort(); v }

#[derive(Default)]
struct St { bases: u64, half: u64, dcap: u64, cases: u64, win_b: u64, u_viol: u64, l_cases: u64, l_viol: u64, e_cases: u64, e_viol: u64,
  t_cases: u64, t_viol: u64, l6a: u64, l6b: u64, l1v: u64, dstar_bad: u64, nm_cases: u64, nm_uviol: u64, wv_cases: u64, wv_u_detect: u64, wv_eq_detect: u64,
  k_lt_l2: u64, k_lt_l2_ml_gt_k: u64, maxeq_false: u64, l_fail_without_cond: u64, no_cond_cases: u64, examples: u32 }
fn show(st: &mut St, tag: &str, b: &[u64], w: u64, ml: Fr) { if st.examples < 12 { st.examples += 1; println!("VIOL {} B={:?} w={} ML={}/{}", tag, b, w, ml.0, ml.1); } }

fn test_base(b: &[u64], st: &mut St, wcap: u64) {
    let info = match analyse(b) { None => { st.half += 1; return; } Some(i) => i };
    let d = match info.dl { Some(d) if d * 1 <= wcap as u128 => d as u64, _ => { st.dcap += 1; return; } };
    st.bases += 1; st.l1v += info.l1viol as u64;
    let (a, bb) = info.l; let m = info.m; let vmu = info.vmu;
    if info.dstar > 2 * m - 1 || d % info.dstar != 0 { st.dstar_bad += 1; }
    let kf = |w: u64| -> Fr { (w * a, bb * (w + vmu)) };
    let cond = |w: u64| -> bool { ((w + vmu) as u128) * bb as u128 >= a as u128 * info.dstar as u128 * m as u128 };
    let m3 = 2 * m * m * m;
    // multiples
    let mut ms: BTreeSet<u64> = (1..=40u64).collect();
    let thr = |x: u128| -> u64 { ((x + d as u128 - 1) / d as u128) as u64 };
    let t1 = thr(((a as u128 * info.dstar as u128 * m as u128 + bb as u128 - 1) / bb as u128).saturating_sub(vmu as u128).max(1));
    let t3 = thr(m3 as u128);
    let t2 = if info.l2.0 == 0 { 1 } else { let den = a as u128 * info.l2.1 as u128 - info.l2.0 as u128 * bb as u128; let num = info.l2.0 as u128 * vmu as u128 * bb as u128; thr((num + den - 1) / den) };
    for t in [t1, t2, t3] { for x in t.saturating_sub(1)..=t + 1 { if x >= 1 { ms.insert(x); } } }
    for &mm in &ms {
        let w = mm * d; if w > wcap { continue; }
        if b.contains(&w) { st.win_b += 1; continue; }
        st.cases += 1;
        let ml = ml_add(b, &info, w);
        let k = kf(w);
        let mx = if fcmp(k, info.l2) == Greater { k } else { info.l2 };
        if fcmp(ml, mx) == Greater { st.u_viol += 1; show(st, "U", b, w, ml); }
        if fcmp(k, info.l2) == Less { st.k_lt_l2 += 1; if fcmp(ml, k) == Greater { st.k_lt_l2_ml_gt_k += 1; } }
        if fcmp(ml, mx) != Equal { st.maxeq_false += 1; }
        let c = cond(w);
        if c { st.l_cases += 1; if fcmp(ml, k) == Less { st.l_viol += 1; show(st, "L", b, w, ml); }
               if fcmp(k, info.l2) != Less { st.e_cases += 1; if fcmp(ml, k) != Equal { st.e_viol += 1; show(st, "E", b, w, ml); } } }
        else { st.no_cond_cases += 1; if fcmp(ml, k) == Less { st.l_fail_without_cond += 1; } }
        if w >= m3 { st.t_cases += 1; if fcmp(ml, k) != Equal { st.t_viol += 1; show(st, "2M3", b, w, ml); } }
        // Lemma 6 arithmetic, checked directly
        if w >= m3 { if !(w as u128 >= a as u128 * info.dstar as u128 * m as u128 / bb as u128) || !cond(w) { st.l6a += 1; } if fcmp(k, info.l2) == Less { st.l6b += 1; } }
        // negative control: wrong v_mu (v_mu-1) must make (U) fail when ML==K and K>=L2 and vmu>1
        if w >= m3 && vmu > 1 { st.wv_cases += 1; let k2: Fr = (w * a, bb * (w + vmu - 1)); // K' > K actually: smaller denominator => larger; claim ML == K' must be false
            if fcmp(ml, k2) != Equal { st.wv_eq_detect += 1; }
            let k3: Fr = (w * a, bb * (w + vmu + 1)); // K'' < K: (U) with K'' must fail
            let mx3 = if fcmp(k3, info.l2) == Greater { k3 } else { info.l2 }; if fcmp(ml, mx3) == Greater { st.wv_u_detect += 1; } }
    }
    // negative control: non-multiples of D
    if d > 1 { for mm in 1..=6u64 { for dw in [1i64, -1] { let w = (mm * d) as i64 + dw; if w < 1 { continue; } let w = w as u64; if w > wcap || w % d == 0 || b.contains(&w) { continue; }
        st.nm_cases += 1; let ml = ml_add(b, &info, w); let k = kf(w); let mx = if fcmp(k, info.l2) == Greater { k } else { info.l2 };
        if fcmp(ml, mx) == Greater { st.nm_uviol += 1; } } } }
}
fn report(tag: &str, st: &St) {
    println!("== {} bases={} skipped_L=1/2:{} skipped_D>cap:{} | cases(D|w)={} w_in_B={} | U viol {} | L cases {} viol {} | E cases {} viol {} | 2M^3 cases {} viol {} | Lemma6a viol {} 6b viol {} | Lemma1/gap viol {} | d* bad {}",
        tag, st.bases, st.half, st.dcap, st.cases, st.win_b, st.u_viol, st.l_cases, st.l_viol, st.e_cases, st.e_viol, st.t_cases, st.t_viol, st.l6a, st.l6b, st.l1v, st.dstar_bad);
    println!("   info: K<L2 cases {} (ML>K in {}); ML!=max(K,L2) in {}; no-size-cond cases {} with ML<K in {}", st.k_lt_l2, st.k_lt_l2_ml_gt_k, st.maxeq_false, st.no_cond_cases, st.l_fail_without_cond);
    println!("   NEGCTRL: non-multiples {} -> (U) violated {} | wrong v_mu (+1): (U) violated {} of {}; claim ML==K(v_mu-1) false in {} of {}", st.nm_cases, st.nm_uviol, st.wv_u_detect, st.wv_cases, st.wv_eq_detect, st.wv_cases);
}
fn rand_base(r: &mut Rng, nmin: u64, nmax: u64, maxv: u64) -> Vec<u64> {
    let n = nmin + r.below(nmax - nmin + 1); let mut s = BTreeSet::new(); while (s.len() as u64) < n { s.insert(1 + r.below(maxv)); } s.into_iter().collect()
}
fn comb(n: u64, k: usize, f: &mut dyn FnMut(&[u64])) { fn rec(s: u64, n: u64, k: usize, cur: &mut Vec<u64>, f: &mut dyn FnMut(&[u64])) { if cur.len() == k { f(cur); return; } for x in s..=n { cur.push(x); rec(x + 1, n, k, cur, f); cur.pop(); } } rec(1, n, k, &mut vec![], f); }

fn main() {
    let a: Vec<String> = env::args().collect();
    let mode = a[1].as_str();
    match mode {
        "controls" => {
            let mut bad = 0;
            for n in 2..=30u64 { let v: Vec<u64> = (1..=n).collect(); if ml_plain(&v) != (1, n + 1) { bad += 1; println!("BAD [N] N={}", n); } }
            let known: Vec<(Vec<u64>, Fr)> = vec![(vec![1, 3, 4, 7], (1, 5)), (vec![1, 5, 6, 11, 16, 17], (5, 33)), (vec![1, 2], (1, 3)), (vec![2, 3], (1, 5).max((2, 5))), (vec![3, 5], (3, 8).max((3, 8)))];
            for (v, e) in &known { let r = ml_plain(v); println!("ML{:?}={}/{} expected {}/{} {}", v, r.0, r.1, e.0, e.1, if r == fred(*e) { "ok" } else { "MISMATCH(check expected)" }); }
            // two coprime speeds, opposite parity: ML = s/(2s+1), 2s+1=a+b ; both odd: 1/2
            for x in 1..=40u64 { for y in x + 1..=40 { if gcd(x, y) == 1 { let r = ml_plain(&[x, y]); let e = if (x + y) % 2 == 0 { (1, 2) } else { fred(((x + y - 1) / 2, x + y)) }; if r != e { bad += 1; println!("BAD two-speed {} {} got {:?} exp {:?}", x, y, r, e); } } } }
            println!("controls bad={}", bad);
        }
        "grid" => { // grid sanity of candidate completeness
            let mut r = Rng(88172645463325252); let mut bad = 0; let ng: u64 = 2_000_000;
            for it in 0..120 { let mut b = rand_base(&mut r, 2, 6, 30);
                if it % 2 == 1 { let w = 1 + r.below(2000); if !b.contains(&w) { b.push(w); } }
                let mx = *b.iter().max().unwrap(); let ml = ml_plain(&b); let mlf = ml.0 as f64 / ml.1 as f64;
                let mut gm = 0f64; for i in 0..ng { let t = i as f64 / ng as f64; let mut f = 1.0f64; for &v in &b { let x = (v as f64 * t).fract(); let dd = x.min(1.0 - x); if dd < f { f = dd; } } if f > gm { gm = f; } }
                if gm > mlf + 1e-9 || mlf > gm + mx as f64 / ng as f64 + 1e-9 { bad += 1; println!("GRIDBAD {:?} ml={} grid={}", b, mlf, gm); } }
            println!("grid bad={} of 120", bad);
        }
        "fam" => { let n0: u64 = a[2].parse().unwrap(); let n1: u64 = a[3].parse().unwrap(); let wcap: u64 = a[4].parse().unwrap(); let mut st = St::default();
            for n in n0..=n1 { for r in 1..=n { let b: Vec<u64> = (1..=n).filter(|&x| x != r).collect(); if b.is_empty() { continue; } test_base(&b, &mut st, wcap); } }
            report(&format!("fam [N]\\{{r}} N={}..{} wcap={}", n0, n1, wcap), &st); }
        "rand" => { let seed: u64 = a[2].parse().unwrap(); let cnt: u64 = a[3].parse().unwrap(); let nmin: u64 = a[4].parse().unwrap(); let nmax: u64 = a[5].parse().unwrap(); let maxv: u64 = a[6].parse().unwrap(); let wcap: u64 = a[7].parse().unwrap();
            let mut r = Rng(seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407) | 1); let mut st = St::default(); let mut g1 = 0; let t0 = std::time::Instant::now();
            for i in 0..cnt { let b = rand_base(&mut r, nmin, nmax, maxv); let g = b.iter().fold(0, |x, &y| gcd(x, y)); if g > 1 { g1 += 1; } test_base(&b, &mut st, wcap); if i % 500 == 499 { println!("progress {}/{} {:.0}s", i + 1, cnt, t0.elapsed().as_secs_f64()); } }
            println!("gcd>1 bases: {}", g1); report(&format!("rand seed={} n={}..{} speeds<={} wcap={}", seed, nmin, nmax, maxv, wcap), &st); }
        "near" => { let seed: u64 = a[2].parse().unwrap(); let cnt: u64 = a[3].parse().unwrap(); let wcap: u64 = a[4].parse().unwrap();
            let mut r = Rng(seed | 1); let mut st = St::default(); let mut got = 0u64; let mut tries = 0u64; let mut minl = 1.0f64;
            while got < cnt && tries < 50_000_000 { tries += 1; let b = rand_base(&mut r, 2, 4, 60); let ml = ml_plain(&b); let lf = ml.0 as f64 / ml.1 as f64; if lf > 0.40 && 2 * ml.0 < ml.1 { got += 1; if lf < minl { minl = lf; } test_base(&b, &mut st, wcap); } }
            println!("near-half bases got {} (L in (0.4,0.5)), tries {}", got, tries); report("near-1/2", &st); }
        "tight" => { let wcap: u64 = a[2].parse().unwrap(); let mut st = St::default(); let mut cnt = 0;
            for (n, mx) in [(3usize, 30u64), (4, 22), (5, 14)] { let mut f = |b: &[u64]| { let ml = ml_plain(b); if ml == (1, n as u64 + 1) { cnt += 1; test_base(b, &mut st, wcap); } }; comb(mx, n, &mut f); }
            // GW family V=[N]\{r} u {m r}, tight when beta >= m s, as bases
            let mut gw = 0;
            for n in 3..=22u64 { for r in 3..=n { if 2 * r <= n { continue; } for mm in 2..=6u64 { if mm * r > 90 { continue; } let mut b: Vec<u64> = (1..=n).filter(|&x| x != r).collect(); b.push(mm * r); b.sort(); let ml = ml_plain(&b);
                if ml == (1, n + 1) { gw += 1; test_base(&b, &mut st, wcap); } } } }
            println!("tight sets (n=3..5 enumerated) {} ; GW-family tight bases {}", cnt, gw); report("tight", &st); }
        "props" => {
            let mut bad = 0u64; let mut l2ex: Vec<String> = vec![];
            // L2([N]) and Lemma L2b, N=2..60
            for n in 2..=60u64 { let b: Vec<u64> = (1..=n).collect(); let i = analyse(&b).unwrap();
                let units: BTreeSet<(u64, u64)> = (1..=n).filter(|&k| gcd(k, n + 1) == 1).map(|k| (k, n + 1)).collect(); let eqs: BTreeSet<(u64, u64)> = i.eqs.iter().cloned().collect();
                if i.l != (1, n + 1) || eqs != units || i.dl != Some((n + 1) as u128) || i.vmu != 1 || i.dstar != n + 1 || fcmp(i.l2, (1, n + 2)) == Greater || i.l1viol > 0 { bad += 1; println!("BAD L2b N={}", n); }
                if i.l2 != (1, n + 2) { l2ex.push(format!("N={}: L2={}/{}", n, i.l2.0, i.l2.1)); } }
            println!("L2b N=2..60 bad={}; L2 != 1/(N+2) at: {:?}", bad, l2ex);
            // Cor B
            let mut cb = 0u64; let mut cbn = 0u64;
            for n in 2..=40u64 { let b: Vec<u64> = (1..=n).collect(); let info = analyse(&b).unwrap(); for s in 1..=30u64 { let w = (n + 1) * s; if w > 1500 && n > 24 { continue; } cbn += 1; let ml = ml_add(&b, &info, w); if ml != fred((s, (n + 1) * s + 1)) { cb += 1; println!("BAD CorB n={} s={} ml={:?}", n + 1, s, ml); } } }
            println!("Cor B (Kravitz 5.1, runners n=N+1=3..41): cases {} bad {}", cbn, cb);
            // Prop S + C1 + C2
            let (mut ps, mut psn, mut c1, mut c1n, mut c2, mut c2n, mut tight_n) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64); let mut l2s: Vec<String> = vec![]; let mut l2lt = 0;
            for n in 3..=40u64 { for r in 3..=n { if 2 * r <= n { continue; } let b: Vec<u64> = (1..=n).filter(|&x| x != r).collect(); let info = analyse(&b).unwrap(); psn += 1;
                let s = n + 1 - r; let beta = (s..).find(|&x| gcd(x, r) == 1).unwrap();
                let units: BTreeSet<(u64, u64)> = (1..r).filter(|&c| gcd(c, r) == 1).map(|c| (c, r)).collect(); let eqs: BTreeSet<(u64, u64)> = info.eqs.iter().cloned().collect();
                if info.l != (1, r) || eqs != units || info.dl != Some(r as u128) || info.dstar != r || info.vmu != beta || fcmp(info.l2, (1, n + 1)) == Greater || info.l1viol > 0 { ps += 1; println!("BAD PropS N={} r={} L={:?} vmu={} beta={} l2={:?}", n, r, info.l, info.vmu, beta, info.l2); }
                if info.l2 != (1, n + 1) { l2s.push(format!("N={},r={}:L2={}/{}", n, r, info.l2.0, info.l2.1)); if fcmp(info.l2, (1, n + 1)) == Less { l2lt += 1; } }
                if n <= 24 || mm_ok(n) { for mm in 2..=40u64 { let w = mm * r; if w > 4000 { continue; } c1n += 1; let ml = ml_add(&b, &info, w);
                    let k1: Fr = (1, n + 1); let k2: Fr = (mm, mm * r + beta); let e = if fcmp(k1, k2) == Greater { k1 } else { k2 };
                    if ml != fred(e) { c1 += 1; println!("BAD C1 N={} r={} m={} ml={:?} exp={:?}", n, r, mm, ml, fred(e)); }
                    let tight = ml == (1, n + 1); if tight { tight_n += 1; } c2n += 1; if tight != (beta >= mm * s) { c2 += 1; println!("BAD C2 N={} r={} m={}", n, r, mm); } } } } }
            println!("PropS bases {} bad {}; L2 != 1/(N+1) in {} bases (strictly smaller in {}): {:?}", psn, ps, l2s.len(), l2lt, l2s);
            println!("C1 cases {} bad {}; C2 (tight <=> beta>=ms) cases {} bad {} (tight cases {})", c1n, c1, c2n, c2, tight_n);
        }
        "lemma3" => { let mut r = Rng(0x9E3779B97F4A7C15); let (mut bad, mut n) = (0u64, 0u64); let (mut badhalf, mut nhalf) = (0u64, 0u64); let (mut n2, mut bad2) = (0u64, 0u64);
            for pass in 0..2 { for _ in 0..3_000_000 { let b = 5 + r.below(60); let aa = if pass == 0 { 1 + r.below((b - 1) / 2) } else { b / 2 + 1 + r.below(b / 4 + 1) }; if aa >= b { continue; } // L=aa/b; pass0 L<1/2 ; pass1 L>1/2
                let v = 1 + r.below(50); let w = 1 + r.below(200); let mut q = 1 + r.below(2000); let mut p = r.below(q); if pass == 1 && r.below(2) == 0 { q = 2 * w; p = 1; } // x = p/q >= 0 (symmetric)
                // e = L - v x ; exact over denominator b*q
                let e_num = aa as i128 * q as i128 - (v * p) as i128 * b as i128;
                let wx = dist(w * p, q) as i128; // ||w x|| = wx/q  => over b*q: wx*b
                let m_num = if e_num < wx * b as i128 { e_num } else { wx * b as i128 }; // min over denominator b*q
                // compare m_num/(b q) <= w a /(b (w+v))  <=> m_num (w+v) <= w a q
                let ok = m_num * (w + v) as i128 <= (w * aa * q) as i128;
                if pass == 0 { n += 1; if !ok { bad += 1; } let ok2 = m_num * (w + 2 * v) as i128 <= (w * aa * q) as i128; if !ok2 { badhalf += 1; } nhalf += 1; } else { n2 += 1; if !ok { bad2 += 1; } } } }
            println!("Lemma3: L<1/2: tested {} (e at equality), violations {} | L>1/2: tested {}, violations {} (hypothesis L<=1/2 not needed?) | NEG CONTROL (bound with 2v instead of v): {} of {} violated", n, bad, n2, bad2, badhalf, nhalf); }
        "conc" => { let mut r = Rng(12345678911); let ng: usize = 400_000; let mut res = [(0u64, 0u64); 4]; let mut bases = 0;
            for _ in 0..600 { let b = rand_base(&mut r, 2, 6, 25); let info = match analyse(&b) { None => continue, Some(i) => i }; bases += 1;
                let lf = info.l.0 as f64 / info.l.1 as f64; let l2f = info.l2.0 as f64 / info.l2.1 as f64;
                let f: Vec<f64> = (0..ng).map(|i| { let t = i as f64 / ng as f64; let mut z = 1.0f64; for &v in &b { let x = (v as f64 * t).fract(); let dd = x.min(1.0 - x); if dd < z { z = dd; } } z }).collect();
                let cs = [if l2f >= 1e-3 { l2f } else { 2.0 }, (l2f + lf) / 2.0, if l2f * 0.5 >= 1e-3 { l2f * 0.5 } else { 2.0 }, lf * 0.5];
                for (ci, &c) in cs.iter().enumerate() { if c > 1.0 { continue; } let mut i = 0; while i < ng { if f[i] > c { let s = i; while i < ng && f[i] > c { i += 1; } let e = i; // component [s,e)
                    let mut nonconc = false; for j in s + 1..e.saturating_sub(1) { if f[j - 1] + f[j + 1] - 2.0 * f[j] > 1e-9 { nonconc = true; break; } }
                    res[ci].0 += 1; if nonconc { res[ci].1 += 1; } } else { i += 1; } } } }
            println!("Concavity of f on components of {{f>c}} (grid {}), {} bases: c=L2: {} comps, {} nonconcave | c=(L2+L)/2: {} / {} | c=L2/2: {} / {} | c=L/2: {} / {}", ng, bases, res[0].0, res[0].1, res[1].0, res[1].1, res[2].0, res[2].1, res[3].0, res[3].1); }
        _ => println!("unknown mode"),
    }
}
fn mm_ok(n: u64) -> bool { n <= 40 }
