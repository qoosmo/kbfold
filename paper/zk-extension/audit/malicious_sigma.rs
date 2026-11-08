// Chapter 11 algebra/probability regression tests.
// INSECURE educational group: order 11 in F_23^*, never deploy.
// Exhaustive enumeration validates fixed-bit HVZK, malicious-verifier
// one-step rejection-sampling with abort correction, and forking.
use std::collections::HashMap;
const P: i64=11;
const MOD: i64=23;
const G: i64=2;
const H: i64=8; // 2^3 modulo 23
fn norm(x:i64)->i64{x.rem_euclid(P)}
fn mul(a:i64,b:i64)->i64{(a*b).rem_euclid(MOD)}
fn exp(mut a:i64,mut k:i64)->i64{
    k=norm(k);let mut z=1;
    while k>0 {if k&1==1{z=mul(z,a);}a=mul(a,a);k>>=1;}
    z
}
fn inv(x:i64)->i64{exp(x,P-1)}
fn pinv(x:i64)->i64{(1..P).find(|u|norm(x* *u)==1).unwrap()}
fn com(bit:i64,r:i64)->i64{mul(exp(G,bit),exp(H,r))}
fn ys(c:i64)->[i64;2]{[c,mul(c,inv(G))]}
#[derive(Clone,Copy,Debug,Hash,PartialEq,Eq)]
struct Tr {t:[i64;2], e:[i64;2], z:[i64;2]}
fn honest(c:i64,branch:usize,r:i64,fa:i64,fb:i64,u:i64,e:i64)->Tr{
    let y=ys(c);
    let other=1-branch;
    let mut ee=[0;2];let mut zz=[0;2];let mut tt=[0;2];
    ee[other]=fa;zz[other]=fb;
    tt[other]=mul(exp(H,fb),inv(exp(y[other],fa)));
    ee[branch]=norm(e-fa);
    zz[branch]=norm(u+ee[branch]*r);
    tt[branch]=exp(H,u);
    assert_eq!(norm(ee.iter().sum()),e);
    for j in 0..2{assert_eq!(exp(H,zz[j]),mul(tt[j],exp(y[j],ee[j])));}
    Tr{t:tt,e:ee,z:zz}
}
fn simulated(c:i64,e0:i64,z0:i64,z1:i64,e:i64)->Tr{
    let ee=[e0,norm(e-e0)];
    let zz=[z0,z1];
    let y=ys(c);
    let tt=[mul(exp(H,z0),inv(exp(y[0],ee[0]))),
            mul(exp(H,z1),inv(exp(y[1],ee[1])))];
    Tr{t:tt,e:ee,z:zz}
}
#[test]
fn fixed_bit_or_exact_law_and_first_message_uniformity(){
    assert_eq!(exp(G,P),1);
    assert_eq!(exp(H,P),1);
    for branch in 0..2{
        let r=4;
        let c=com(branch as i64,r);
        for e in 0..2{
            let mut real=HashMap::new();
            let mut sim=HashMap::new();
            let mut tm=HashMap::new();
            for ef in 0..P{for zf in 0..P{for u in 0..P{
                let h=honest(c,branch,r,ef,zf,u,e);
                *real.entry(h).or_insert(0usize)+=1;
                *tm.entry(h.t).or_insert(0usize)+=1;
                let s=simulated(c,ef,zf,u,e);
                *sim.entry(s).or_insert(0usize)+=1;
            }}}
            assert_eq!(real,sim,"exact fixed-bit law, branch={branch}, e={e}");
            assert_eq!(tm.len(),(P*P) as usize);
            assert!(tm.values().all(|count|*count==P as usize));
        }
    }
    println!("Chapter 11 fixed-bit OR: exact transcript laws and uniform T");
}
fn malicious_reply(t:[i64;2])->i64{
    // -1 means abort; otherwise the verifier chooses a bit adaptively.
    if (t[0]+t[1])%4==0{-1}
    else{(t[0]*t[1]+t[1])&1}
}
#[derive(Clone,Copy,Debug,Hash,PartialEq,Eq)]
struct View{t:[i64;2],reply:i64,e:[i64;2],z:[i64;2]}
fn view(t:Tr,reply:i64)->View{
    if reply<0{View{t:t.t,reply,e:[-1,-1],z:[-1,-1]}}
    else{View{t:t.t,reply,e:t.e,z:t.z}}
}
#[test]
fn malicious_adaptive_verifier_with_abort_balanced(){
    let c=com(1,3);
    let mut real=HashMap::<View,usize>::new();
    let mut selected=HashMap::<View,usize>::new();
    // Count REAL honest transcripts with an extra independent dummy coin
    // so that both sample spaces have the same total number of trials.
    for fa in 0..P{for fb in 0..P{for u in 0..P{
        let first=honest(c,1,3,fa,fb,u,0);
        let e=malicious_reply(first.t);
        let h=if e<0{first}else{honest(c,1,3,fa,fb,u,e)};
        *real.entry(view(h,e)).or_insert(0)+=2;
    }}}
    // Guess one bit; use fixed-bit simulated distribution. On abort,
    // accept exactly one of the two extra selection-coin outcomes.
    for guess in 0..2{for e0 in 0..P{for z0 in 0..P{for z1 in 0..P{
        let s=simulated(c,e0,z0,z1,guess);
        let e=malicious_reply(s.t);
        for coin in 0..2{
            let accept=if e<0{coin==1}else{guess==e};
            if accept{*selected.entry(view(s,e)).or_insert(0)+=1;}
        }
    }}}}
    assert_eq!(real,selected,"exact selected-trial and honest full laws incl abort");
    assert_eq!(real.values().sum::<usize>(),(2*P*P*P) as usize);
    // If abort is always selected, the probabilities of public abort
    // histories are biased relative to their honest real frequencies.
    let real_abort=real.iter().filter(|(k,_)|k.reply<0).map(|(_,v)|*v).sum::<usize>();
    assert!(real_abort>0&&real_abort<real.values().sum::<usize>());
    println!("Chapter 11 malicious verifier: exact selected/real view law incl abort");
}
fn special_extracted(c:i64,a:Tr,b:Tr)->(i64,i64){
    assert_eq!(a.t,b.t);
    assert_ne!(norm(a.e.iter().sum()),norm(b.e.iter().sum()));
    let j=(0..2).find(|&j|a.e[j]!=b.e[j]).unwrap();
    let r=norm((a.z[j]-b.z[j])*pinv(a.e[j]-b.e[j]));
    assert_eq!(c,com(j as i64,r));
    (j as i64,r)
}
#[test]
fn forking_first_difference_and_exact_probability(){
    const K:usize=4;
    let c=com(1,6);
    let mut accepting=Vec::new();
    for challenge in 0..(1<<K){accepting.push(challenge);}
    for aa in 0..(1<<K){for bb in 0..(1<<K){
        if aa==bb{continue;}
        let i=(0..K).find(|i|(aa>>i)&1!=(bb>>i)&1).unwrap();
        let a=honest(c,1,6,(2+i) as i64,3,7,((aa>>i)&1) as i64);
        let b=honest(c,1,6,(2+i) as i64,3,7,((bb>>i)&1) as i64);
        assert_eq!(a.t,b.t);
        let (t,r)=special_extracted(c,a,b);
        assert_eq!(t,1);assert_eq!(r,6);
    }}
    // For any accepting set of m distinct k-bit strings, two
    // independently uniform challenge strings fork with exact count m(m-1).
    let denominator=(1<<K)*(1<<K);
    for m in 0usize..=(1usize<<K){
        let numerator=m*m.saturating_sub(1);
        let p=m as f64/((1<<K) as f64);
        let expected=p*(p-1.0/((1<<K) as f64));
        let actual=numerator as f64/denominator as f64;
        assert!((expected-actual).abs()<1e-10);
    }
    println!("Chapter 11: all distinct 4-bit forks, exact probability and extraction");
}
