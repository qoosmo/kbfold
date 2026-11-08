// Chapter 10: educational algebra-only audit, NOT cryptographic deployment.
// A tiny prime-order group (order 11, subgroup of F_23^*) is deliberately
// insecure. It verifies formulas and exact distribution identities only.
use std::collections::HashMap;
const P:i64=11;
const MOD:i64=23;
const G:i64=2;
const ALPHA:i64=3; // witness to the insecure test setup
fn m(x:i64)->i64{x.rem_euclid(P)}
fn mul(a:i64,b:i64)->i64{(a*b).rem_euclid(MOD)}
fn pow(mut a:i64,mut k:i64)->i64{
 let mut x=1;
 while k>0{if k&1==1{x=mul(x,a);}a=mul(a,a);k>>=1;}
 x
}
fn inv_p(x:i64)->i64{assert_ne!(m(x),0);(1..P).find(|y|m(x* *y)==1).unwrap()}
fn inv_g(x:i64)->i64{pow(x,P-1)}
fn h()->i64{pow(G,ALPHA)}
fn com(b:i64,r:i64)->i64{mul(pow(G,m(b)),pow(h(),m(r)))}
fn or_y(c:i64,t:i64)->i64{mul(c,inv_g(pow(G,m(t))))}
fn verify(c:i64,branches:&[i64],a:&[i64],e:&[i64],z:&[i64],challenge:i64)->bool{
 if a.len()!=branches.len()||e.len()!=branches.len()||z.len()!=branches.len(){return false;}
 if m(e.iter().sum::<i64>())!=m(challenge){return false;}
 (0..branches.len()).all(|i|{
  pow(h(),z[i])==mul(a[i],pow(or_y(c,branches[i]),e[i]))
 })
}
fn simulate(c:i64,branches:&[i64],e:&[i64],z:&[i64])->(Vec<i64>,i64){
 let a=(0..branches.len()).map(|i|mul(pow(h(),m(z[i])),inv_g(pow(or_y(c,branches[i]),m(e[i]))))).collect::<Vec<_>>();
 let challenge=m(e.iter().sum());
 assert!(verify(c,branches,&a,e,z,challenge));
 (a,challenge)
}
fn actual(c:i64,branches:&[i64],j:usize,r:i64,
       fake_e:&[i64],fake_z:&[i64],nonce:i64,challenge:i64)->(Vec<i64>,Vec<i64>,Vec<i64>){
 assert_eq!(branches.len(),fake_e.len());
 assert_eq!(branches.len(),fake_z.len());
 assert_eq!(c,com(branches[j],r));
 let n=branches.len();
 let mut e=fake_e.to_vec();let mut z=fake_z.to_vec();let mut a=vec![0;n];
 for i in 0..n{
  if i!=j{a[i]=mul(pow(h(),m(z[i])),inv_g(pow(or_y(c,branches[i]),m(e[i]))));}
  else{a[i]=pow(h(),m(nonce));}
 }
 e[j]=m(challenge-e.iter().enumerate().filter(|(i,_)|*i!=j).map(|(_,x)|*x).sum::<i64>());
 z[j]=m(nonce+e[j]*r);
 assert!(verify(c,branches,&a,&e,&z,challenge));
 (a,e,z)
}
fn extract(c:i64,branches:&[i64],a:&[i64],first:&(Vec<i64>,Vec<i64>),second:&(Vec<i64>,Vec<i64>))->(i64,i64){
 let (e,z)=first;let(ep,zp)=second;
 let j=(0..branches.len()).find(|&i|m(e[i]-ep[i])!=0).expect("different global challenges");
 let r=m((z[j]-zp[j])*inv_p(e[j]-ep[j]));
 assert_eq!(c,com(branches[j],r));
 assert_eq!(a.len(),branches.len());
 (branches[j],r)
}
#[test]
fn group_and_binding(){
 assert_eq!(pow(G,P),1);
 assert_eq!(pow(h(),P),1);
 for b in 0..=1{
  let mut seen=Vec::new();
  for r in 0..P{seen.push(com(b,r));}
  seen.sort();seen.dedup();
  assert_eq!(seen.len(),P as usize,"Pedersen hiding uniform over group");
 }
 for bits in [vec![0,0,0],vec![1,0,1],vec![1,1,1]]{
  let rs=[1,4,7];let sum=bits.iter().sum::<i64>();
  let rsum=m(rs.iter().sum());
  let c=bits.iter().zip(rs).fold(1,|acc,(b,r)|mul(acc,com(*b,r)));
  assert_eq!(c,com(sum,rsum));
  let branches=(0..=3).filter(|v|v%2==sum%2).collect::<Vec<_>>();
  let j=branches.iter().position(|v|*v==sum).unwrap();
  let fake_e=vec![2;branches.len()];let fake_z=vec![5;branches.len()];
  let (a,e,z)=actual(c,&branches,j,rsum,&fake_e,&fake_z,7,4);
  assert!(verify(c,&branches,&a,&e,&z,4));
  let (_,ep,zp)=actual(c,&branches,j,rsum,&fake_e,&fake_z,7,9);
  let (t,r)=extract(c,&branches,&a,&(e,z),&(ep,zp));
  assert_eq!(t,sum);
  assert_eq!(com(t,r),c);
 }
 // A different integer opening must reveal the known small DL α.
 let sum=0;let claimed=1;let rsum=4;
 let wrong_r=m(rsum+(sum-claimed)*inv_p(ALPHA));
 assert_eq!(com(sum,rsum),com(claimed,wrong_r));
 let recovered=m((sum-claimed)*inv_p(wrong_r-rsum));
 assert_eq!(recovered,ALPHA);
}
#[test]
fn exact_or_hvzk_histograms(){
 let c=com(1,5);let branches=[0,1];
 let mut honest=HashMap::<[i64;7],usize>::new();
 let mut simulated=HashMap::<[i64;7],usize>::new();
 for e in 0..P {for nonce in 0..P {for ef in 0..P {for zf in 0..P {
  let (a,ev,zv)=actual(c,&branches,1,5,&[ef,ef],&[zf,zf],nonce,e);
  let key=[a[0],a[1],ev[0],ev[1],zv[0],zv[1],e];
  *honest.entry(key).or_insert(0)+=1;
  let (as_,c_)=simulate(c,&branches,&[e,nonce],&[ef,zf]);
  let key2=[as_[0],as_[1],e,nonce,ef,zf,c_];
  *simulated.entry(key2).or_insert(0)+=1;
 }}}}
 assert_eq!(honest,simulated,"perfect HVZK transcript distribution");
 println!("OR sigma: exact distribution equality across {} transcripts",honest.len());
}
fn f16_mul(mut a:u8,mut b:u8)->u8{
 let mut x=0u8;
 while b!=0{
  if b&1!=0{x^=a;}
  b>>=1;
  let carry=(a&8)!=0;
  a<<=1;a&=15;
  if carry{a^=3;}
 }
 x
}
#[test]
fn field_affine_to_parity_exhaustive_f16(){
 let mut cases=0;
 for x in 0u8..16{for y in 0u8..16{
  for a in 0u8..16{for b in 0u8..16{
   let rhs=f16_mul(a,x)^f16_mul(b,y);
   // γ_i = X^i in F_2[X]/(X^4+X+1); coordinates are 4 binary digits.
   for target in [rhs,rhs^1,rhs^2]{
    let mut parity_ok=true;
    for k in 0..4{
     let mut side=0u8;
     for i in 0..4{
      let ax=f16_mul(a,1<<i);let by=f16_mul(b,1<<i);
      side^=((ax>>k)&1)&((x>>i)&1);
      side^=((by>>k)&1)&((y>>i)&1);
     }
     if side!=((target>>k)&1){parity_ok=false;}
    }
    assert_eq!(parity_ok,rhs==target);
    cases+=1;
   }
  }}
 }}
 println!("Affine field-to-binary parity: {cases} GF(16) cases checked");
}
