from math import sqrt
import sys
def fun(q):
	i=0 
	while i<q:
		b=i-q+1
		c=sqrt(b+q)
		if c!=int(c):
			return b
		i=i+1
	return -1

print fun(int(sys.argv[1]))
#fun(7)
