use std::cmp::{min,max};
use std::collections::{BTreeSet,BTreeMap};

fn gcd(mut a:u128,mut b:u128)->u128{while b!=0{let r=a%b;a=b;b=r;}a}
fn lcm(a:u128,b:u128)->u128{a/gcd(a,b)*b}
fn gcd_all(v:&[u128])->u128{v.iter().copied().reduce(gcd).unwrap()}
fn antichain(v:&[u128])->bool{for i in 0..v.len(){for j in i+1..v.len(){if v[j]%v[i]==0{return false}}}true}
fn self_bad(d:&[u128],i:usize)->bool{(0..d.len()).filter(|&j|j!=i).map(|j|gcd(d[i],d[j])).sum::<u128>()>=d[i]}
fn compact(d:&[u128])->bool{
 if d.len()!=5||!antichain(d)||gcd_all(d)!=1{return false}
 let nb=(0..5).filter(|&i|self_bad(d,i)).count(); if nb<3{return false}
 if 7*d.iter().sum::<u128>()>1135*d[0]||d[4]>=7*d[0]{return false}
 let sg:u128=(0..5).flat_map(|i|(i+1..5).map(move|j|(i,j))).map(|(i,j)|gcd(d[i],d[j])).sum();
 2*(d.iter().sum::<u128>()-2*sg)<=7*d[0]
}
fn edge_count_bad(d:&[u128])->(usize,usize){let b:Vec<_>=(0..5).filter(|&i|self_bad(d,i)).collect();let mut e=0;for x in 0..b.len(){for y in x+1..b.len(){if 4*gcd(d[b[x]],d[b[y]])>=min(d[b[x]],d[b[y]]){e+=1}}}(b.len(),e)}
fn tower(d:&[u128])->Option<(u128,i128)>{
 let ell=d.iter().copied().reduce(lcm).unwrap(); let mut p:Vec<u128>=d.iter().map(|x|ell/x).collect();p.sort();
 let prod=p.iter().product::<u128>();let nsum=p.iter().map(|x|prod/x).sum::<u128>();let cap=1135*prod/(7*nsum)-1;
 let mut b=0u128;for m in 1..=cap{if p.iter().any(|x|m%x==0){b+=1}if m>=p[4]{let z=2*b*prod-(m+1)*nsum;if z==0{return Some((m,0))}/* positive terms fit */ if 2*b*prod<(m+1)*nsum{return Some((m,-1))}}}None
}
fn norm(mut v:Vec<u128>)->Vec<u128>{v.sort();let g=gcd_all(&v);for x in &mut v{*x/=g}v}
fn bank1()->BTreeSet<Vec<u128>>{let mut out=BTreeSet::new();for a in 2u128..=27{for ap in 2u128..=27{if gcd(a,ap)!=1||min(a,ap)>4||max(a,ap)>=7*min(a,ap){continue}for c1 in 2u128..=3{for c2 in c1..=10{if 5*(c1+c2)<3*c1*c2{continue}let ll=lcm(c1,c2);for k1 in 2..7*c1{if gcd(k1,c1)!=1{continue}for k2 in 2..7*c2{if gcd(k2,c2)!=1||k1*c2==k2*c1{continue}assert_eq!((ll*k1)%c1,0);assert_eq!((ll*k2)%c2,0);let s=ll+ll*k1/c1+ll*k2/c2;let am=max(a,ap);for u in 1..=s*am/(am-1){let amin=min(a,ap);let mut vm=7*u*amin/ll;let den=c1*c2-c1-c2;if c1*c2>c1+c2{vm=min(vm,(a+ap)*c1*c2/den)}for v in 1..=vm{let d=norm(vec![u*a,u*ap,v*ll,v*ll*k1/c1,v*ll*k2/c2]);if d.len()==5&&d.windows(2).all(|x|x[0]!=x[1])&&compact(&d)&&edge_count_bad(&d)==(3,1){out.insert(d);}}}}}}}}}out}

#[derive(Clone,Copy,Eq,PartialEq,Ord,PartialOrd)]struct Q{n:u128,d:u128}
fn q(n:u128,d:u128)->Q{let g=gcd(n,d);Q{n:n/g,d:d/g}}
fn bank0()->BTreeSet<Vec<u128>>{let mut groups:BTreeMap<Q,BTreeSet<Q>>=BTreeMap::new();for c1 in 2u128..=10{for c2 in 2u128..=10{if 5*(c1+c2)<3*c1*c2{continue}for k1 in 2..7*c1{if gcd(k1,c1)!=1||c1>=7*k1{continue}for k2 in 2..7*c2{if gcd(k2,c2)!=1||c2>=7*k2{continue}let t=q(c1*k2,k1*c2);if t.n==t.d{continue}groups.entry(t).or_default().insert(q(c1,k1));}}}}let mut out=BTreeSet::new();for (t,rs) in groups{let r:Vec<_>=rs.into_iter().collect();for i in 0..r.len(){for j in i+1..r.len(){for k in j+1..r.len(){let qs=[q(1,1),t,r[i],r[j],r[k]];let den=qs.iter().fold(1,|z,x|lcm(z,x.d));let d=norm(qs.iter().map(|x|x.n*(den/x.d)).collect());if d.windows(2).all(|x|x[0]!=x[1])&&compact(&d)&&edge_count_bad(&d)==(3,0){out.insert(d);}}}}}out}

fn shape_ok(w:&[u128;4])->bool{if gcd_all(w)!=1||!antichain(w)||w[3]>=7*w[0]{return false}for i in 0..4{let others:Vec<_>=(0..4).filter(|&j|j!=i).collect();let rhs=others.iter().map(|&j|w[j]).product::<u128>();let mut lhs=0;for &j in &others{let z: u128=others.iter().filter(|&&l|l!=j).map(|&l|w[l]).product();lhs+=gcd(w[i],w[j])*z*2}if lhs<rhs{return false}}true}
fn shapes()->BTreeSet<Vec<u128>>{let mut out=BTreeSet::new();for a in 1u128..=300{let hi=7*a;let xs:Vec<u128>=(a+1..hi).filter(|&x|x%a!=0).collect();for ii in 0..xs.len(){let b=xs[ii];for jj in ii+1..xs.len(){let c=xs[jj];if c%b==0{continue}/* prune first vertex using maximum possible last contribution */let partial_num=(gcd(a,b)*c+gcd(a,c)*b)*2;for kk in jj+1..xs.len(){let d=xs[kk];if d%b==0||d%c==0{continue}let w=[a,b,c,d];if shape_ok(&w){out.insert(w.to_vec());}}}}}out}
fn print_bank(name:&str,s:&BTreeSet<Vec<u128>>){println!("{} count={}",name,s.len());let mut fails=Vec::new();for d in s{println!("{:?}",d);if let Some(x)=tower(d){fails.push((d,x))}}println!("{} tower_failures={:?}",name,fails)}
fn main(){let b1=bank1();print_bank("B1",&b1);let b2=bank0();print_bank("B2",&b2);return;let s=shapes();println!("B3 count={} largest_w1={}",s.len(),s.iter().map(|x|x[0]).max().unwrap_or(0));for w in s{println!("{:?}",w)}}
