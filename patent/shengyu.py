from math import sqrt
def fun(q):
	i=0 
	while i<q:
		b=i-q+1
		c=sqrt(b+q)
		if c==int(c):
			return b
		i=i+1
	return -1

print(fun(61182963833226648365600490867908823022138748065727))

#fun(7)
