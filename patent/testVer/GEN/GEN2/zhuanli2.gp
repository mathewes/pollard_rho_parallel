a;q;D;x;b;E;G;order;du;Qu;dca;Qca;Bu;Bux;

panding(a,b,D,q)=
{ 
  if(lift((a^2-D*b^2-1)*Mod(1,q))==0,print(a);print(b);1,0);
}

{
  a=10^15;
  tim=0;
  while(tim!=100,tim=tim+1;print("tim");print(tim);while(1,q=nextprime(random(a));if(lift((q-1)*Mod(1,3))==0,break;););
  print("q"); print(q);
  flag=0;flag2=0;
  mx=10000000;
  while(mx!=0,mx=mx-1;b1=random(q);while(27*b1^2==0,b1=random(q););b=[0,0,0,0,b1];E=ellinit(b*Mod(1,q));E1ap=ellap(E);orderForE=q+1-E1ap;if(isprime(orderForE)==1,break););
  order=orderForE; 
  print("testPrime");
  print(isprime(order));
  print(order);
  if(isprime(order),G=random(E);print(ellpow(E,G,order));du=random(order-2)+1;Qu=ellpow(E,G,du);print("print");
print(0);print(0);print(0);print(0);print(b1);print(q);print(order);
print(lift(G[1]));print(lift(G[2]));print(lift(Qu[1]));print(lift(Qu[2]));
print(20);print(44444);
r=lift(polrootsmod(x^3-1,q)[2]);
print(r);
lambda=lift(polrootsmod(x^2+x+1,order)[1]);
print(lambda);
print("end"););
);
}
