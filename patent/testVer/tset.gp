p=9;
q=p^2;
i;j=1;flag=0;
for(i=1,q,for(j=p,q-1,k=j/i;r=lift(j*Mod(1,i));if(k>=p||r>=p,flag=1;break;););if(flag==1,flag=0,print(i);););
