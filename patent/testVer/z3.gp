a;q;D;x;b;E;G;order;du;Qu;dca;Qca;Bu;Bux;

panding(a,b,D,q)=
{ 
  if(lift((a^2-D*b^2-1)*Mod(1,q))==0,1,0);
}

fl(i)=
{
  a1111=lift(i*Mod(1,1000000000));
  if(a1111==0,0,1);
}

{
  a=10^8;
  q=nextprime(random(a));
  print(q);D=-q+2;y=(x^2+D)*Mod(1,q);x=ffgen(y,'x);
  flag=0;flag2=0;
  a1=random(x);b1=random(x);
  while(4*a1^3+27*b1^2==0,a1=random(x);b1=random(x););
  print(a1);print(b1);  
  b=[0,0,0,a1,b1];E=ellinit(b*x^0);
  G=random(E);
  print(G);
  p=q^4+1;
 tim=0;
  for(i=2,p,if(fl(i)==0,print(tim);tim=tim+1);if(ellpow(E,G,i)==G,order=i-1;break;););
  print(ellpow(E,G,order));
  /*U*/
  du=random(order-2)+1;Qu=ellpow(E,G,du);  
  /*CA*/
  tim=0; 
  while(1,dca=random(order-2)+1;Qca=ellpow(E,G,dca);Bu=elladd(E,Qu,Qca);Bux=Bu[1];if(panding(polcoeff(Bux.pol,0),polcoeff(Bux.pol,1),D,q)==1,break,tim=tim+1;if(lift(tim*Mod(1,1000))==0,print(tim);););); 
  print("dca,Dca");
  print(dca);
  print(Qca);
  print("BU");
  print(Bu);
  a11=Bux.pol;
  a1a=polcoeff(a11,0)*Mod(1,q);
  a1b=polcoeff(a11,1)*Mod(1,q);
  cx=(1+a1a)/a1b;
  a11a=((cx^2+D*Mod(1,q))/(cx^2-D*Mod(1,q)));
  a11b=(2*cx)/(cx^2-D*Mod(1,q));
  print(a11a);
  print(a11b);
}
