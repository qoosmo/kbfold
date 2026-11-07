// Reproducible integer-prime-field regression checks for Chapter 5.
// This is a test, not a substitute for proofs or cryptographic validation.
const MOD: i64 = 97;
fn m(x: i64) -> i64 { x.rem_euclid(MOD) }
fn add(a:i64,b:i64)->i64{m(a+b)}
fn mul(a:i64,b:i64)->i64{m(a*b)}
fn trim(mut p:Vec<i64>)->Vec<i64>{
 while p.last()==Some(&0)&&p.len()>1 {p.pop();}
 if p.is_empty(){p.push(0)} p
}
fn scale(p:&[i64],c:i64)->Vec<i64>{trim(p.iter().map(|v|mul(*v,c)).collect())}
fn sum(a:&[i64],b:&[i64])->Vec<i64>{
 let mut o=vec![0;a.len().max(b.len())];
 for (i,v) in a.iter().enumerate(){o[i]=add(o[i],*v);}
 for (i,v) in b.iter().enumerate(){o[i]=add(o[i],*v);}
 trim(o)
}
fn poly_mul(a:&[i64],b:&[i64])->Vec<i64>{
 let mut o=vec![0;a.len()+b.len()-1];
 for(i,x)in a.iter().enumerate(){for(j,y)in b.iter().enumerate(){o[i+j]=add(o[i+j],mul(*x,*y));}} trim(o)
}
fn kernel(b:usize,m_bits:usize)->Vec<i64>{
 let mut out=vec![1];
 for i in 0..m_bits {
  let mut f=vec![0; (1<<i)+1]; f[0]=((b>>i)&1)as i64; f[1<<i]=1;
  out=poly_mul(&out,&f);
 }
 trim(out)
}
fn encode(f:&[i64],m_bits:usize)->Vec<i64>{
 let mut out=vec![0];
 for(b,c)in f.iter().enumerate(){out=sum(&out,&scale(&kernel(b,m_bits),*c));}
 out
}
fn fold(p:&[i64],r:i64)->Vec<i64>{
 let mut out=vec![0;(p.len()+1)/2];
 for(i,c)in p.iter().enumerate(){
  let s=if i%2==0 {m(2*r-1)} else {m(1-r)};
  out[i/2]=add(out[i/2],mul(s,*c));
 }
 trim(out)
}
fn restrict(f:&[i64],r:i64)->Vec<i64>{
 (0..f.len()/2).map(|i|add(mul(m(1-r),f[2*i]),mul(r,f[2*i+1]))).collect()
}
fn eval(p:&[i64],x:i64)->i64{p.iter().rev().fold(0,|acc,c|add(mul(acc,x),*c))}
fn pow(mut x:i64,mut n:usize)->i64{let mut y=1;while n>0{if n&1==1{y=mul(y,x)}x=mul(x,x);n>>=1;}y}
fn rand(st:&mut u64)->i64{*st=st.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);(*st>>32) as i64%MOD}
fn degree_lt(p:&[i64],n:usize)->bool{trim(p.to_vec()).len()<=n}
fn run_case(bits:usize,b:usize,st:&mut u64){
 let n=1usize<<bits;
 let f:(Vec<i64>)=(0..n).map(|_|rand(st)).collect();
 let mut rs:(Vec<i64>)=(0..b).map(|_|rand(st)).collect();
 if rs.last()==Some(&0){*rs.last_mut().unwrap()=1;}
 let mut q=sum(&encode(&f,bits),&{
  let mut t=vec![0;n];t.extend_from_slice(&rs);trim(t)
 });
 let mut ff=f.clone(); let mut rpoly=rs;
 assert_eq!(q.len()<=n+b,true);
 for j in 0..=bits{
  let nj=1usize<<(bits-j);
  let bj=(b+(1usize<<j)-1)/(1usize<<j);
  let mut predicted=encode(&ff,bits-j);
  let mut masked=vec![0;nj];masked.extend_from_slice(&rpoly);
  predicted=sum(&predicted,&masked);
  assert_eq!(q,predicted,"level {j}, bits={bits}, B={b}");
  assert!(degree_lt(&q,nj+bj),"bad degree bound: level {j}");
  if j==bits {
   assert!(q.len()<=2,"linear final polynomial");
   assert_eq!(q[0],ff[0],"final constant must be MLE at challenges");
   assert_eq!(q.get(1).copied().unwrap_or(0),rpoly[0],"final slope");
  } else{
   let r=rand(st);
   q=fold(&q,r);
   rpoly=fold(&rpoly,r);
   ff=restrict(&ff,r);
  }
 }
}
#[test]
fn masked_folds_closure_all_levels(){
 let mut state=0x517A_07D3_5EC0_2026u64;
 let mut count=0;
 for bits in 1..=6{
  for t in 0..=bits{
   let b=1usize<<t;
   for _ in 0..120{run_case(bits,b,&mut state);count+=1;}
  }
 }
 println!("Chapter 5: {count} complete masked fold chains checked modulo {MOD}");
}
#[test]
fn folded_word_and_two_point_closure(){
 // 97 has subgroup of order 32; 28^3 is 1, 28 is not used.
 // Find a primitive 32nd root and use a domain of size 32.
 let omega=(2..MOD).find(|&x|pow(x,32)==1&&pow(x,16)!=1).unwrap();
 let domain:Vec<i64>=(0..32).map(|i|pow(omega,i)).collect();
 let mut st=0xA55E_2026_5EEDu64;
 for _ in 0..400 {
  let p:Vec<i64>=(0..12).map(|_|rand(&mut st)).collect();
  let r=rand(&mut st);let folded=fold(&p,r);
  for &x in domain.iter().take(12){
   let y=mul(x,x);
   let inv_two=49;let inv_x=pow(x,95);
   let pe=mul(add(eval(&p,x),eval(&p,m(-x))),inv_two);
   let po=mul(m(eval(&p,x)-eval(&p,m(-x))),mul(inv_two,inv_x));
   let wd=add(mul(m(2*r-1),pe),mul(m(1-r),po));
   assert_eq!(wd,eval(&folded,y));
  }
  let a=rand(&mut st);let b=rand(&mut st);
  let x=domain[0];let y=domain[1];
  let qx=add(a,mul(b,x));let qy=add(a,mul(b,y));
  let inv=pow(m(y-x),95);
  assert_eq!(mul(m(mul(y,qx)-mul(x,qy)),inv),a);
 }
 println!("Chapter 5: 4800 local word fold cases and 400 two-point closure checks");
}

#[test]
fn exact_degree_zero_mask_joint_leakage() {
 // Theorem 5.7: each marginal is uniform but (opening, slope) distinguishes.
 let mut first_opening=[0usize; MOD as usize];
 let mut first_slope=[0usize; MOD as usize];
 let mut second_opening=[0usize; MOD as usize];
 let mut second_slope=[0usize; MOD as usize];
 for c in 0..MOD {
  let slope=m(-c);
  let f0_open=c;
  let f1_open=add(2,c);
  first_opening[f0_open as usize]+=1;
  second_opening[f1_open as usize]+=1;
  first_slope[slope as usize]+=1;
  second_slope[slope as usize]+=1;
  assert_eq!(add(f0_open,slope),0);
  assert_eq!(add(f1_open,slope),2);
 }
 assert!(first_opening.iter().all(|n|*n==1));
 assert!(second_opening.iter().all(|n|*n==1));
 assert!(first_slope.iter().all(|n|*n==1));
 assert!(second_slope.iter().all(|n|*n==1));
 println!("Chapter 5: exact uniform-marginal/perfect-joint-leakage attack verified");
}
