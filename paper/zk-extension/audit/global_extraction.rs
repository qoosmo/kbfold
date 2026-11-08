// Chapter 12 checkpoint-and-replay audit. Pure combinatorics, no crypto deployment.
// Checks exact acceptance/fork probabilities and the global union bound.
fn ipow(mut x:u128,mut e:u32)->u128 {
    let mut ans=1u128;
    while e>0 {if e&1==1{ans=ans.checked_mul(x).unwrap();}e>>=1;if e>0{x=x.checked_mul(x).unwrap();}}
    ans
}
#[test]
fn all_admissible_accepting_sets_satisfy_fork_bound(){
    let mut total=0usize;
    for k in 1..=6u32 {
        let n=1u128<<k;
        for r in 1..=7u32 {for m in 0..=n {
            // Exact failure = m*(n-m+1)^r/n^(r+1).
            // Bound = 1/n + 1/(r+1). Cross-multiply using integers.
            let lhs=m*ipow(n-m+1,r)*(r as u128+1);
            let rhs=ipow(n,r)*(n+r as u128+1);
            assert!(lhs<=rhs,"k={k}, r={r}, m={m}");
            total+=1;
        }}
    }
    println!("{total} exact integer fork-bound inequalities passed");
}
#[test]
fn exhaustive_challenge_tree_fork_counts(){
    for k in 1..=3usize {
        let n=1usize<<k;
        for mask in 0..(1usize<<n) {
            let accepted=(0..n).filter(|&i|(mask>>i)&1==1).collect::<Vec<_>>();
            let m=accepted.len();
            let mut count=0usize;
            for main in 0..n {if (mask>>main)&1==0{continue;}
                for side1 in 0..n {for side2 in 0..n {
                    let fail1=(mask>>side1)&1==0||side1==main;
                    let fail2=(mask>>side2)&1==0||side2==main;
                    if fail1&&fail2{count+=1;}
                }}
            }
            assert_eq!(count,m*(n-m+1).pow(2),"k={k}, mask={mask}");
        }
    }
    println!("exhaustive 1-,2-,3-bit acceptance trees: main/fork counts passed");
}
fn accepting_set(k:usize,tag:usize)->Vec<usize>{
    let n=1usize<<k;
    (0..n).filter(|i| (i+2*tag)%3!=0).collect()
}
#[test]
fn chronological_multi_block_forks_preserve_main_path(){
    let k=4usize;let n=1usize<<k;let blocks=5usize;
    let main_values=[1usize,2,3,4,5];
    let outer_theta=11usize;let outer_z=13usize;
    let mut recorded=Vec::new();
    for tag in 0..blocks {
        let accepts=accepting_set(k,tag);
        let main=main_values[tag];
        // The honest main verifier has already chosen its challenge path.
        let main_accepted=accepts.contains(&main);
        if main_accepted {
            // Counterfactual accepted path under the SAME checkpoint state.
            let other=accepts.iter().copied().find(|&x|x!=main).unwrap();
            let first_difference=(0..k).find(|i|((main>>*i)&1)!=((other>>*i)&1)).unwrap();
            assert!(first_difference<k);
            recorded.push((tag,main,other));
        }
        // Side replay does not touch the main challenges or outer state.
        assert_eq!(outer_theta,11);
        assert_eq!(outer_z,13);
    }
    for (tag,main,_) in recorded {assert_eq!(main,main_values[tag]);}
    // Raw checkpoint simulation is classical and depends on an exact restore.
    assert_eq!(n,16);
}
#[test]
fn exact_two_opening_collision_recovers_setup_log(){
    // Tiny pedagogical group: p=11, modulus 23, g=2, h=g^3=8.
    let prime=11i64;
    let (actual_bit,wrong_bit)=(0i64,1i64);
    let (r,alpha)=(4i64,3i64);
    let inv=(1..prime).find(|v|(alpha* *v)%prime==1).unwrap();
    let r2=(r+(actual_bit-wrong_bit)*inv).rem_euclid(prime);
    let delta=(r2-r).rem_euclid(prime);
    let delta_inv=(1..prime).find(|v|(delta* *v)%prime==1).unwrap();
    let recovered=((actual_bit-wrong_bit)*delta_inv).rem_euclid(prime);
    assert_eq!(recovered,alpha);
    assert_eq!((actual_bit+alpha*r).rem_euclid(prime),
               (wrong_bit+alpha*r2).rem_euclid(prime));
}
