from math import comb
from fractions import Fraction as Fr

def delta(m, n, i, j):  # delta(a_i < b_j)
    total = comb(m+n, m); cnt = 0
    for t in range(j, m+n):
        a_before = t - j
        if a_before < i+1 or a_before > m: continue
        rem_a = m - a_before; rem = m+n-t-1
        if 0 <= rem_a <= rem: cnt += comb(t, j) * comb(rem, rem_a)
    return Fr(cnt, total)

# Step bounds along the two paths
maxstep_row = Fr(0); maxstep_col = Fr(0)
for m in range(1,31):
    for n in range(1,31):
        for j in range(n-1):
            s = abs(delta(m,n,0,j+1)-delta(m,n,0,j))
            if s>maxstep_row: maxstep_row=s; row_at=(m,n,j,float(s))
        for i in range(m-1):
            s = abs(delta(m,n,i+1,n-1)-delta(m,n,i,n-1))
            if s>maxstep_col: maxstep_col=s; col_at=(m,n,i,float(s))
print("max step on i=0 row:", float(maxstep_row), "at", row_at if maxstep_row>0 else None)
print("max step on j=top col:", float(maxstep_col), "at", col_at if maxstep_col>0 else None)
print("1/3 =", float(Fr(1,3)))

# Endpoint sanity: d_row(0)=m/(m+n); d_col(last)=n/(m+n)
ok=True
for m in range(1,31):
    for n in range(1,31):
        assert delta(m,n,0,0)==Fr(m,m+n)
        assert delta(m,n,m-1,n-1)==Fr(n,m+n)
print("endpoints d(a0,b0)=m/(m+n), d(a_{m-1},b_{n-1})=n/(m+n): verified")

# Is there a closed-form single witness? Check candidate: i=0, j = number of b's just past threshold.
# Specifically smallest j with delta(a0,bj) >= 1/3; is it always <= 2/3?
import statistics
overshoot=[]
for m in range(1,31):
    for n in range(1,31):
        d0=Fr(m,m+n)
        if d0>Fr(2,3):  # use column instead
            # smallest i with delta(a_i,b_{n-1}) <= 2/3; check >=1/3
            found=None
            for i in range(m):
                d=delta(m,n,i,n-1)
                if d<=Fr(2,3):
                    found=d; break
            if found is None or not (Fr(1,3)<=found<=Fr(2,3)): overshoot.append(('col',m,n))
        else:
            found=None
            for j in range(n):
                d=delta(m,n,0,j)
                if d>=Fr(1,3):
                    found=d; break
            if found is None or not (Fr(1,3)<=found<=Fr(2,3)): overshoot.append(('row',m,n))
print("closed witness (first-crossing on chosen path) fails:", overshoot[:10], "count", len(overshoot))
