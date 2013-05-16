from random import randint
from math import sqrt
from math import ceil
from math import floor

#D=-8135911281212236577396499
#q=8135911281212236577396501
q=2503
D=-2501
a=1
b=1
tim=0
while 1:
	b=randint(1,q)
	v=(1+D*b*b)%q
	c1=sqrt(v)
	c1=int(c1)
	flag=0#should less
        d=c1*c1
	tim=tim+1
	if tim%100==0:
		print tim/100
	if d==v:
		print(str(b)+'*x+'+str(c1))
		break
	elif d>v:
		flag=0
	else:
		flag=1
	if flag==0:
		i=-1
		while 1:
			e=(c1+i)*(c1+i)
			if e==v:
				print(str(b)+'*x+'+str(c1-i))
				flag=-1
				break
	
			elif e<v:
				break
			else:
				i=i-1
		if flag==-1:
			break
	else:
		i=1 
                while 1:  
                        e=(c1+i)*(c1+i)
                        if e==v:
                                print(str(b)+'*x+'+str(c1-i))
                                flag=-1
                                break
                            
                        elif e>v:
                                break
                        else:
                                i=i+1
                if flag==-1:
                        break
		
