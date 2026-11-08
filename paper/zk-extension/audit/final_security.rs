// Chapter 14 reproducible algebraic security checks.
// This is NOT a cryptographic implementation nor a quantum simulator.
// Covers exact trapdoor equivocation and the sparse-fold counterexample.
include!("fold_masks.rs");

fn inv_mod(mut a:i64, modulus:i64)->i64 {
    a=a.rem_euclid(modulus);
    assert_ne!(a,0);
    (1..modulus).find(|x|(a* *x).rem_euclid(modulus)==1).unwrap()
}
fn pow_mod(mut a:i64,mut exponent:i64,modulus:i64)->i64{
    let mut out=1;
    while exponent>0{
        if exponent&1==1{out=out*a%modulus;}
        exponent>>=1;
        if exponent>0{a=a*a%modulus;}
    }
    out
}
#[test]
fn all_nonzero_trapdoors_exactly_equivocate_all_bits(){
    let prime=11i64;
    let base=2i64; let modulus=23i64;
    assert_eq!(pow_mod(base,prime,modulus),1);
    let mut checks=0usize;
    for alpha in 1..prime{
        let h=pow_mod(base,alpha,modulus);
        let inv_alpha=inv_mod(alpha,prime);
        let mut dist0=[0usize;23];
        let mut dist1=[0usize;23];
        for rho in 0..prime{
            let c=pow_mod(h,rho,modulus);
            for b in 0..=1i64{
                let equiv_r=(rho-b*inv_alpha).rem_euclid(prime);
                let opened=pow_mod(base,b,modulus)*pow_mod(h,equiv_r,modulus)%modulus;
                assert_eq!(opened,c);
                if b==0{dist0[c as usize]+=1;}else{dist1[c as usize]+=1;}
                checks+=1;
            }
        }
        assert_eq!(dist0,dist1);
        assert_eq!(dist0.iter().filter(|v|**v==1).count(),11);
    }
    println!("Chapter 14: {checks} exact equivocation/binding-break identities checked");
}

#[test]
fn sparse_local_checks_and_final_line_fail_to_certify_rs_membership(){
    // F_97 has multiplicative roots of unity of all orders 4,8,16,32.
    let mut count=0usize;
    for bits in 1..=4usize{
        let n=1usize<<bits;
        let length=2*n;
        let root=(2..MOD).find(|&x|pow(x,length)==1 && pow(x,length/2)!=1).unwrap();
        let domain=(0..length).map(|i|pow(root,i)).collect::<Vec<_>>();
        for b in 1..n{
            let d=n+b;
            let mut source=vec![0i64;d+1];
            source[d]=1;
            // Character orthogonality recovers the unique interpolation
            // coefficient of X^d from all domain evaluations.
            let inverse_length=pow((length as i64).rem_euclid(MOD),95);
            let coeff_d=mul(inverse_length,domain.iter().map(|&x|{
                mul(eval(&source,x),pow(pow(x,95),d))
            }).fold(0,add));
            assert_eq!(coeff_d,1);
            // Therefore this word is NOT in RS(domain, d).
            // Yet EVERY local pair relation passes at all rounds,
            // even for every listed challenge sequence.
            for seed in 0..12usize{
                let mut current=source.clone();
                let mut current_domain=domain.clone();
                for j in 0..bits{
                    let r=m((seed*17+j*13) as i64);
                    let next=fold(&current,r);
                    assert!(next.len()<=((current.len()+1)/2));
                    for &x in &current_domain{
                        let y=mul(x,x);
                        let pplus=eval(&current,x);
                        let pminus=eval(&current,m(-x));
                        let even=mul(add(pplus,pminus),49);
                        let odd=mul(m(pplus-pminus),mul(49,pow(x,95)));
                        let from_word=add(mul(m(2*r-1),even),mul(m(1-r),odd));
                        assert_eq!(from_word,eval(&next,y));
                    }
                    current=next;
                    current_domain=(0..(length>>(j+1))).map(|i|pow(root,i<< (j+1))).collect();
                }
                assert!(current.len()<=2,"final polynomial is linear");
                count+=1;
            }
        }
    }
    println!("Chapter 14: {count} complete non-codeword fold chains passed all local checks");
}

#[test]
fn rate_and_distance_bound_for_all_small_levels(){
    let mut checked=0usize;
    for bits in 1..=6usize{
        let n=1usize<<bits;
        for blowup in 1..=4usize{
            for b in 1..=n{
                for j in 0..=bits{
                    let nj=n>>j;
                    let bj=(b+(1usize<<j)-1)/(1usize<<j);
                    let dj=nj+bj;
                    let mj=(1usize<<blowup)*nj;
                    assert!(dj<=mj);
                    if blowup>=2 {assert!(2*dj<=mj);}
                    let min_dist=mj-dj+1;
                    assert!(min_dist>=1);
                    if blowup==1 && b==n {assert_eq!(dj,mj);}
                    checked+=1;
                }
            }
        }
    }
    println!("Chapter 14: {checked} enlarged RS rate/distance constraints checked");
}
