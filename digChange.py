b=416363315556156604917983573

b=bin(b)
bLen=len(b)
if bLen>66:
	hi=b[0:bLen-64]
	low='0b'+b[bLen-64:]
else:
	hi=0
	low=b
print int(hi,2)
print int(low,2)