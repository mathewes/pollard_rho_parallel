a;q;D;x;b;E;G;order;du;Qu;dca;Qca;Bu;Bux;

panding(a,b,D,q)=
{ 
  if(lift((a^2-D*b^2-1)*Mod(1,q))==0,print(a);print(b);1,0);
}

{
  a=10^6;
  q=nextprime(random(a));
  print("q"); 
  print(q);
  D=-q+2;y=(x^2+D)*Mod(1,q);x=ffgen(y,'x);
  flag=0;flag2=0;
/*
  a1=random(x);b1=random(x);
*/
  a1=random(q);b1=random(q);
  while(4*a1^3+27*b1^2==0,a1=random(x);b1=random(x););
  b=[0,0,0,a1,b1];E=ellinit(b*x^0);
  G=random(E);
  E1=ellinit(b*Mod(1,q));
  E1ap=ellap(E1);
  V0=2;V1=E1ap;V2=V1*V1-q*V0;
  orderForE=q*q+1-V2;
  print("orderForE");
  print(orderForE);
  print("testOrderForE");
  print(ellpow(E1,G,orderForE));
  print("G");
  print(G);
  fct=[orderForE,factor(orderForE)];
  print("order, testOrder");
  order=ellorder(E1,G,fct);
  print(order);
  print(ellpow(E1,G,order)); 
  /*U*/
  du=random(order-2)+1;Qu=ellpow(E,G,du); 
  /*CA*/
  r1=random(q);
  
 


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
