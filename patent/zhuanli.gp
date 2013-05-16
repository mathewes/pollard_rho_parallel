p=7;

b=(x^2+5)*Mod(1,p);
a=ffgen(b,'a);
/*
a4=(a+3)*Mod(1,7);
a6=5*Mod(1,7);
*/
a4=random(a);
a6=random(a);
ellA=[0,0,0,a4,a6];
print(ellA);
E=ellinit(ellA*a^0);
P=random(E);
print(P);

