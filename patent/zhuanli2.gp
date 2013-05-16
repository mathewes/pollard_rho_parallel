a;q;w;x;b;E;G;order;du;Qu;dca;Qca;Bu;Bux;

panding(a,b,D,q)=
{ 
  if(lift((a^2-D*b^2-1)*Mod(1,q))==0,print(a^2);print(b^2);print(a^2-D*b^2);print(q);1,0);
}

{
  /*basic information*/

  a=10^50;
  q=nextprime(random(a));
  print(q);
  w=-61182963833226648365600490867908823022138748065726;
  y=(x^2-w)*Mod(1,q);
  x=ffgen(y,'x);
  b=[random(x),random(x),random(x),random(x),random(x)];
  E=ellinit(b*x^0);
  print(1);
  G=random(E);
  print(2);
  order=1;
  for(i=2,q^2,if(ellpow(E,G,i)==G,order=i-1;break;););
  print(3);
  /*U*/
  du=random(order-2)+1;Qu=ellpow(E,G,du);
  
  /*CA*/ 
  while(1,dca=random(order-2)+1;Qca=ellpow(E,G,dca);Bu=elladd(E,Qu,Qca);Bux=Bu[1];if(panding(polcoeff(Bux.pol,0),polcoeff(Bux.pol,1),w,q)==1,break;);); 
  print(dca);
  print(Qca);
  print("BU");
  print(Bu);
  a11=Bux.pol;
  a1a=polcoeff(a11,0)*Mod(1,q);
  a1b=polcoeff(a11,1)*Mod(1,q);
  cx=(1+a1a/a1b);
  print(cx);
  a11a=((cx^2+w*Mod(1,q))/(cx^2-w*Mod(1,q)));
  print(a11a);
}
