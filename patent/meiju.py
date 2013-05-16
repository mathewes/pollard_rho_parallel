q=7
D=-2

for a in range(q):
	for b in range(q):
		if (a*a-D*b*b-1)%q==0:
			print(str(a)+':'+str(b))
