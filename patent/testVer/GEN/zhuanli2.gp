a;q;D;x;b;E;G;order;du;Qu;dca;Qca;Bu;Bux;

panding(a,b,D,q)=
{ 
  if(lift((a^2-D*b^2-1)*Mod(1,q))==0,print(a);print(b);1,0);
}

{
  a=10^12;
  while(1,q=nextprime(random(a));if(lift((q-1)*Mod(1,3))==0,break;););
  print("q"); 
  print(q);
  flag=0;flag2=0;
  while(1,b1=random(q);while(27*b1^2==0,b1=random(q););b=[0,0,0,0,b1];E=ellinit(b*Mod(1,q));E1ap=ellap(E);orderForE=q+1-E1ap;if(isprime(orderForE)==1,break););
  order=orderForE; 
  print(isprime(order));
  print(order);G=random(E);
  print(ellpow(E,G,order)); 
  /*U*/
  du=random(order-2)+1;Qu=ellpow(E,G,du);  
  /*CA*/
print("print");
print(0);print(0);print(0);print(0);print(b1);print(q);print(order);
print(lift(G[1]));print(lift(G[2]));print(lift(Qu[1]));print(lift(Qu[2]));
print(20);print(44444);


r=lift(polrootsmod(x^3-1,q)[2]);
print(r);
lambda=lift(polrootsmod(x^2+x+1,order)[1]);
print(lambda);
print("test");
G1=random(E);
G2=G1;G2[1]=G2[1]*r;
print(G2);
print(ellpow(E,G1,lambda));
print(du);
print(isprime(order));
G1=random(E);G2=random(E);G3=random(E);
print(ellpow(E,G1,order)); 
print(ellpow(E,G2,order)); 
print(ellpow(E,G2,order));
print(ellpow(E,G,du)==Qu);  


  tim=0; 
  
  while(1,dca=random(order-2)+1;Qca=ellpow(E,G,dca);Bu=elladd(E,Qu,Qca);Bux=Bu[1];if(panding(polcoeff(Bux.pol,0),polcoeff(Bux.pol,1),D,q)==1,break,tim=tim+1;if(lift(tim*Mod(1,1000))==0,print(tim);););); 
  print("possible");
  print(Bu);
/*
 a11=a22.pol;
 print(type(a11));
 a1a=polcoeff(a11,0)*Mod(1,q); 
 a1b=polcoeff(a11,1)*Mod(1,q);
 print(a1a);print(a1b);
 cx=(1+a1a)/a1b;
 a11a=((cx^2+D*Mod(1,q))/(cx^2-D*Mod(1,q)));
 a11b=(2*cx)/(cx^2-D*Mod(1,q));
 print(a11a);
 print(a11b);
*/
}
