// Chapter 6: deterministic regression checks for binary-field kernel algebra.
// No external crates. Rust tests supplement, but do not replace, paper proofs.
#[derive(Clone, Copy)]
struct GF { degree: usize, irreducible: u16 }
impl GF {
    fn q(self) -> usize { 1usize << self.degree }
    fn mul(self, a: u16, b: u16) -> u16 {
        let mut x: u16 = 0;
        for i in 0..self.degree { if (b >> i) & 1 == 1 { x ^= a << i; } }
        for i in (self.degree..=(2*self.degree-2)).rev() {
            if (x >> i) & 1 == 1 { x ^= self.irreducible << (i-self.degree); }
        }
        assert!((x as usize) < self.q()); x
    }
    fn pow(self, mut a: u16, mut e: usize) -> u16 {
        let mut r=1u16;
        while e>0 {if e&1==1 {r=self.mul(r,a)} a=self.mul(a,a);e>>=1;}
        r
    }
    fn square(self,a:u16)->u16 {self.mul(a,a)}
    fn trace(self, a:u16)->u16 {
        let mut x=a;let mut s=0;
        for _ in 0..self.degree {s^=x;x=self.square(x);}
        assert!(s<=1,"trace is binary");
        s
    }
    fn kernel(self, b:usize, z:u16, ell:usize)->u16 {
        let mut v=1;
        for i in 0..ell {
            let term=self.pow(z,1usize<<i) ^ (((b>>i)&1)as u16);
            v=self.mul(v,term);
        }
        v
    }
    fn lambda(self, b:usize, theta:&[u16])->u16 {
        let mut v=1;
        for (i,t) in theta.iter().enumerate(){
            v=self.mul(v,1 ^ *t ^ (((b>>i)&1)as u16));
        }
        v
    }
}
fn next(seed:&mut u64,q:usize)->u16 {
    *seed=seed.wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    ((*seed>>32)as usize%q)as u16
}
fn basis_and_coords(f:GF, ell:usize)->(Vec<u16>,Vec<usize>,Vec<u16>){
    let n=f.degree;assert_eq!(1usize<<ell,n);
    let beta:Vec<u16>=(0..n).map(|i|f.kernel(i,2,ell)).collect();
    let mut lut=vec![usize::MAX;f.q()];
    for mask in 0..f.q() {
        let mut x=0u16;
        for u in 0..n {if mask>>u&1==1{x^=beta[u];}}
        assert_eq!(lut[x as usize],usize::MAX,"kernel values must be a basis");
        lut[x as usize]=mask;
    }
    assert!(lut.iter().all(|u|*u!=usize::MAX));
    let mut eta=Vec::new();
    for k in 0..n {
        let possible:Vec<u16>=(0..f.q() as u16).filter(|a|
            (0..n).all(|v|
                f.trace(f.mul(*a,beta[v])) == u16::from(k==v)
            )
        ).collect();
        assert_eq!(possible.len(),1,"trace dual unique");
        eta.push(possible[0]);
    }
    (beta,lut,eta)
}
fn run_binary_case(f:GF,ell:usize,seed:&mut u64){
    let n=f.degree;let q=f.q();let (beta,coord,eta)=basis_and_coords(f,ell);
    assert_eq!(beta.len(),n);
    for _trial in 0..110 {
        let p:Vec<u16>=(0..n).map(|_|next(seed,q)).collect();
        let mut c=vec![0u16;n];
        for u in 0..n {
            for v in 0..n {
                if coord[p[v] as usize]>>u&1==1 {c[u]^=beta[v];}
            }
        }
        let theta:Vec<u16>=(0..ell).map(|_|next(seed,q)).collect();
        let lambda:Vec<u16>=(0..n).map(|u|f.lambda(u,&theta)).collect();
        let mut d=0u16;
        for u in 0..n {d^=f.mul(lambda[u],c[u]);}
        let t:Vec<u16>=(0..n).map(|_|next(seed,q)).collect();
        let mut v_all=vec![0u16;n];let mut u_all=vec![0u16;n];
        for k in 0..n {
            let mut v=f.mul(eta[k],d);
            for row in 0..n {
                let mut h=0u16;
                for u in 0..n {
                    let z=f.mul(beta[row],lambda[u]);
                    if coord[z as usize]>>k&1==1 {h^=eta[u];}
                }
                v^=f.mul(h,p[row]);
            }
            assert_eq!(f.trace(v),0,"trace-coordinate verification");
            v_all[k]=v;
            u_all[k]=v^f.square(t[k])^t[k];
            assert_eq!(f.trace(u_all[k]),0,"Artin-Schreier mask");
        }
        let r=next(seed,q);let s=f.square(r);let z=next(seed,q);
        let mut a=r;
        let mut w=vec![0u16;n];
        for k in 0..n {
            w[k]=f.kernel(k,z,ell);
            if k==0 {w[k]^=f.pow(z,n);}
            assert_eq!(f.square(w[k]),
                      f.kernel(k,f.square(z),ell)^
                      if k==0 {f.pow(f.square(z),n)} else {0});
            a^=f.mul(w[k],t[k]);
        }
        let mut second=f.square(a)^s;
        for k in 0..n {
            second^=f.mul(f.square(w[k]),u_all[k]^v_all[k]^t[k]);
        }
        assert_eq!(second,0,"honest affine second check");

        let mut delta=next(seed,q);
        let mut errors:Vec<u16>=(0..n).map(|_|next(seed,q)).collect();
        if delta==0&&errors.iter().all(|e|*e==0){delta=1;errors[0]=1;}
        let mut roots=0usize;
        for z in 0..q {
            let mut value=delta;
            for k in 0..n {
                let mut wk=f.kernel(k,z as u16,ell);
                if k==0 {wk^=f.pow(z as u16,n);}
                value^=f.mul(errors[k],f.square(wk));
            }
            if value==0 {roots+=1;}
        }
        assert!(roots<=n,"anchored degree-n root bound");
    }
    println!("GF(2^{n}): 110 masks, trace coordinates, anchored roots passed");
}
#[test]
fn characteristic_two_kernel_gf16_gf256(){
    let mut seed=0xC6A1_2026_7777_5EEDu64;
    run_binary_case(GF{degree:4,irreducible:0x13},2,&mut seed);
    run_binary_case(GF{degree:8,irreducible:0x11b},3,&mut seed);
}


// Chapter 7: exact packed Ring Switching regressions over GF(16)/GF(256).
fn transposed(f:GF,beta:&[u16],coord:&[usize],x:&[u16])->Vec<u16>{
 let n=f.degree;
 assert_eq!(x.len(),n);
 let mut out=vec![0u16;n];
 for u in 0..n {
  for v in 0..n {
   if (coord[x[v] as usize]>>u)&1 == 1 {out[u]^=beta[v];}
  }
 }
 out
}
fn ring_switch_case(f:GF,ell:usize,seed:&mut u64){
 let n=f.degree;let q=f.q();
 let (beta,coord,_eta)=basis_and_coords(f,ell);
 let high=2usize;let cols=1usize<<high;
 for _trial in 0..130 {
  let mut w=vec![vec![0u16;cols];n];
  for v in 0..n {for j in 0..cols {
   w[v][j]=next(seed,q)&1;
  }}
  let mut packed=vec![0u16;cols];
  for j in 0..cols {
   for v in 0..n {if w[v][j]==1 {packed[j]^=beta[v];}}
   for v in 0..n {
    assert_eq!(((coord[packed[j] as usize]>>v)&1) as u16,w[v][j]);
   }
  }
  let r_hi:Vec<u16>=(0..high).map(|_|next(seed,q)).collect();
  let r_lo:Vec<u16>=(0..ell).map(|_|next(seed,q)).collect();
  let theta:Vec<u16>=(0..ell).map(|_|next(seed,q)).collect();
  let hh:Vec<u16>=(0..cols).map(|j|f.lambda(j,&r_hi)).collect();
  let qq:Vec<u16>=(0..n).map(|v|f.lambda(v,&r_lo)).collect();
  let ll:Vec<u16>=(0..n).map(|u|f.lambda(u,&theta)).collect();
  let mut partial=vec![0u16;n];
  for v in 0..n {for j in 0..cols {
   if w[v][j]==1{partial[v]^=hh[j];}
  }}
  let ts=transposed(f,&beta,&coord,&partial);
  let again=transposed(f,&beta,&coord,&ts);
  assert_eq!(again,partial,"transpose involution");
  for u in 0..n {
   for v in 0..n {
    assert_eq!((coord[ts[u] as usize]>>v)&1,
               (coord[partial[v] as usize]>>u)&1);
   }
  }
  for u in 0..n {
   let mut expected=0u16;
   for j in 0..cols {
    if ((coord[hh[j] as usize]>>u)&1)==1 {expected^=packed[j];}
   }
   assert_eq!(ts[u],expected,"packed transpose identity");
  }
  let mut aa=vec![0u16;cols];
  for j in 0..cols {
   for u in 0..n {
    if ((coord[hh[j] as usize]>>u)&1)==1 {aa[j]^=ll[u];}
   }
  }
  let mut rhs=0u16;
  for j in 0..cols {rhs^=f.mul(aa[j],packed[j]);}
  let mut bs=0u16;
  for u in 0..n {bs^=f.mul(ll[u],ts[u]);}
  assert_eq!(bs,rhs,"correct unmasked batched relation");
  let mut y=0u16;
  for v in 0..n {y^=f.mul(qq[v],partial[v]);}
  let mut y_direct=0u16;
  for v in 0..n {for j in 0..cols {
   if w[v][j]==1{y_direct^=f.mul(qq[v],hh[j]);}
  }}
  assert_eq!(y,y_direct,"two-axis multilinear evaluation");
  let p:Vec<u16>=(0..n).map(|_|next(seed,q)).collect();
  let m:Vec<u16>=(0..n).map(|v|partial[v]^p[v]).collect();
  let cp=transposed(f,&beta,&coord,&p);
  assert_eq!(transposed(f,&beta,&coord,&cp),p,"pad transpose inverse");
  let tm=transposed(f,&beta,&coord,&m);
  let mut bm=0u16;let mut dc=0u16;
  for u in 0..n {
   bm^=f.mul(ll[u],tm[u]);
   dc^=f.mul(ll[u],cp[u]);
  }
  assert_eq!(bm^dc,rhs,"masked outgoing equation");
  let pin=next(seed,q);let yprime=y^pin;
  let mut incoming_lhs=yprime;let mut incoming_rhs=pin;
  for v in 0..n {
   incoming_lhs^=f.mul(qq[v],m[v]);
   incoming_rhs^=f.mul(qq[v],p[v]);
  }
  assert_eq!(incoming_lhs,incoming_rhs,"incoming affine equation");
  let mut c_bad=cp.clone();c_bad[0]^=1;
  let mut dc_bad=0u16;
  for u in 0..n {dc_bad^=f.mul(ll[u],c_bad[u]);}
  assert_eq!(bm^dc_bad^rhs,ll[0],"outgoing residual split");
 }
 println!("GF(2^{n}): 130 packed witness, transposition and mask cases passed");
}
#[test]
fn chapter7_packed_ring_switching(){
 let mut seed=0xC7A7_2026_ABC1_DE55u64;
 ring_switch_case(GF{degree:4,irreducible:0x13},2,&mut seed);
 ring_switch_case(GF{degree:8,irreducible:0x11b},3,&mut seed);
}
