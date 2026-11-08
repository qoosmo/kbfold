// Chapter 13 deterministic regression tests, not a cryptographic deployment.
// Reuse the independently audited odd-field polynomial folding implementation.
include!("fold_masks.rs");

const HALF: i64 = 49; // 2^{-1} in F_97

fn eq_weight(index:usize, z:&[i64])->i64{
    let mut w=1;
    for (i,&v) in z.iter().enumerate() {
        w=mul(w,if ((index>>i)&1)==1{v}else{m(1-v)});
    }
    w
}
fn round_poly(f:&[i64], chi:&[i64])->[i64;3]{
    assert_eq!(f.len(),chi.len());
    let mut out=[0,0,0];
    for i in 0..f.len()/2{
        let (f0,f1)=(f[2*i],f[2*i+1]);
        let (h0,h1)=(chi[2*i],chi[2*i+1]);
        let df=m(f1-f0);let dh=m(h1-h0);
        out[0]=add(out[0],mul(f0,h0));
        out[1]=add(out[1],add(mul(df,h0),mul(f0,dh)));
        out[2]=add(out[2],mul(df,dh));
    }
    out
}
#[test]
fn hidden_masked_sumcheck_and_degree_aware_closure(){
    let mut st=0xC013_2026_4F51u64;
    let mut count=0;
    for bits in 1usize..=5 {
        let n=1usize<<bits;
        for b in [1usize,2usize,n/2,n] {
            for _ in 0..55 {
                let mut f=(0..n).map(|_|rand(&mut st)).collect::<Vec<_>>();
                let z=(0..bits).map(|_|rand(&mut st)).collect::<Vec<_>>();
                let mut chi=(0..n).map(|i|eq_weight(i,&z)).collect::<Vec<_>>();
                let v=f.iter().zip(chi.iter()).fold(0i64,|v,(a,h)|add(v,mul(*a,*h)));
                let rmask=(0..b).map(|_|rand(&mut st)).collect::<Vec<_>>();
                let mut q=sum(&encode(&f,bits),&{
                    let mut shifted=vec![0i64;n];shifted.extend(rmask);shifted
                });
                let mut claim=v;let mut offset=0i64;
                let mut challenges=Vec::new();
                let mut final_round=[0i64;3];
                for j in 1..=bits{
                    let nj=1usize<<(bits-j+1);
                    let true_sum=f.iter().zip(chi.iter()).fold(0,|v,(a,h)|add(v,mul(*a,*h)));
                    let s=round_poly(&f,&chi);
                    assert_eq!(add(eval(&s,0),eval(&s,1)),true_sum);
                    assert_eq!(add(true_sum,offset),claim);

                    let c=rand(&mut st);
                    let h0=add(mul(offset,HALF),m(-c));
                    let h1=mul(2,c);
                    let masked=[add(s[0],h0),add(s[1],h1),s[2]];
                    // Publishing the quadratic coefficient would reveal the
                    // unmasked quadratic coefficient exactly.
                    assert_eq!(masked[2],s[2]);
                    assert_eq!(add(eval(&masked,0),eval(&masked,1)),claim);
                    let r=rand(&mut st);
                    challenges.push(r);
                    let new_offset=add(mul(offset,HALF),mul(c,m(2*r-1)));
                    let next_f=restrict(&f,r);
                    let next_chi=restrict(&chi,r);
                    let next_sigma=next_f.iter().zip(next_chi.iter()).fold(0,|v,(a,h)|add(v,mul(*a,*h)));
                    assert_eq!(eval(&s,r),next_sigma);
                    assert_eq!(eval(&masked,r),add(next_sigma,new_offset));
                    final_round=masked;
                    claim=eval(&masked,r);
                    offset=new_offset;f=next_f;chi=next_chi;
                    q=fold(&q,r);
                    let D=(nj/2)+(b+(1usize<<j)-1)/(1usize<<j);
                    assert!(q.len()<=D,"masked code degree bound");
                }
                assert_eq!(f.len(),1);assert_eq!(chi.len(),1);
                assert!(q.len()<=2,"final polynomial linear");
                assert_eq!(q[0],f[0],"final constant equals restricted f");
                let prod_chi=challenges.iter().zip(z.iter()).fold(1i64,|w,(&r,&zi)|{
                    let term=add(mul(m(1-r),m(1-zi)),mul(r,zi));
                    mul(w,term)
                });
                assert_eq!(prod_chi,chi[0]);
                assert_eq!(claim,add(mul(chi[0],q[0]),offset));
                assert_eq!(eval(&final_round,*challenges.last().unwrap()),claim);
                count+=1;
            }
        }
    }
    println!("Chapter 13: {count} end-to-end hidden Sumcheck/fold/linear closure traces over F_97");
}

#[test]
fn hiding_bit_commitments_are_exactly_uniform_in_toy_group(){
    // Toy group of prime order 11 in F_23^*, not secure.
    let mut counts=[[0usize;23];2];
    let g=2i64;let h=8i64;
    fn gpow(mut a:i64,mut p:i64)->i64 {
        let mut ret=1i64;
        while p>0{if p&1==1{ret=ret*a%23;}a=a*a%23;p>>=1;}
        ret
    }
    for b in 0..2{
        for r in 0..11{
            let c=gpow(g,b as i64)*gpow(h,r)%23;
            counts[b][c as usize]+=1;
        }
    }
    assert_eq!(counts[0],counts[1]);
    assert_eq!(counts[0].iter().sum::<usize>(),11);
    assert_eq!(counts[0].iter().filter(|n|**n==1).count(),11);
    println!("Chapter 13: two bit values yield identical full toy Pedersen distributions");
}

#[test]
fn confidential_local_fold_and_two_point_closure(){
    let root=(2..MOD).find(|&x|pow(x,32)==1&&pow(x,16)!=1).unwrap();
    let dom=(0..32).map(|i|pow(root,i)).collect::<Vec<_>>();
    let mut st=0x1013_4F1D_2026u64;
    for _ in 0..220{
        let p=(0..12).map(|_|rand(&mut st)).collect::<Vec<_>>();
        let r=rand(&mut st);let q=fold(&p,r);
        for x in dom.iter().take(16){
            let x=*x;
            let y=mul(x,x);
            let invx=pow(x,95);
            let pos=eval(&p,x);let neg=eval(&p,m(-x));
            let even=mul(add(pos,neg),HALF);
            let odd=mul(m(pos-neg),mul(HALF,invx));
            let folded=add(mul(m(2*r-1),even),mul(m(1-r),odd));
            assert_eq!(folded,eval(&q,y));
        }
        let a=rand(&mut st);let b=rand(&mut st);
        let x0=dom[0];let x1=dom[1];
        let u0=add(a,mul(x0,b));let u1=add(a,mul(x1,b));
        assert_eq!(m(mul(x1,u0)-mul(x0,u1)),mul(m(x1-x0),a));
    }
    println!("Chapter 13: hidden fold triple and final two-leaf closure verified");
}
