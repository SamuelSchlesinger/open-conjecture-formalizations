import itertools
from fractions import Fraction as Fr

def linexts(n, rel):
    # rel: set of (i,j) meaning i < j. count/enumerate linear extensions (perms) respecting rel
    below = [set() for _ in range(n)]
    for (i,j) in rel:
        below[j].add(i)
    res=[]
    def rec(placed, order):
        if len(order)==n:
            res.append(tuple(order)); return
        for x in range(n):
            if x not in placed and below[x] <= placed:
                rec(placed|{x}, order+[x])
    rec(set(), [])
    return res

def closure(n, edges):
    # transitive closure of edges (i<j)
    less=[[False]*n for _ in range(n)]
    for (i,j) in edges: less[i][j]=True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if less[i][k] and less[k][j]: less[i][j]=True
    return less

def is_poset(n, less):
    for i in range(n):
        if less[i][i]: return False
        for j in range(n):
            if less[i][j] and less[j][i]: return False
    return True

def width(n, less):
    # max antichain
    best=1
    for r in range(2, n+1):
        for s in itertools.combinations(range(n), r):
            if all(not less[a][b] and not less[b][a] for a,b in itertools.combinations(s,2)):
                best=max(best,r)
    return best

def is_connected(n, less):
    # comparability graph connected
    adj=[set() for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if less[i][j] or less[j][i]: adj[i].add(j); adj[j].add(i)
    seen={0}; stack=[0]
    while stack:
        u=stack.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); stack.append(v)
    return len(seen)==n

def series_decomp(n, less):
    # exists nonempty proper down-set D with everything in D below everything not in D
    elems=set(range(n))
    for r in range(1,n):
        for D in itertools.combinations(range(n), r):
            Ds=set(D); U=elems-Ds
            # D is a down-set? and all D < all U?
            if all(less[d][u] for d in Ds for u in U):
                return True
    return False

# enumerate posets on n elements (small), width 2, connected, series-indecomposable, parallel-indecomposable(=connected)
def analyze(n):
    pairs=list(itertools.combinations(range(n),2))
    cores=[]
    seen_iso=set()
    cnt=0
    for mask in range(1<<len(pairs)):
        edges=[pairs[k] for k in range(len(pairs)) if mask&(1<<k)]
        less=closure(n,edges)
        if not is_poset(n,less): continue
        if width(n,less)!=2: continue
        if not is_connected(n,less): continue  # parallel-indecomposable
        if series_decomp(n,less): continue     # series-indecomposable
        # canonical form to dedup isomorphism
        canon=None
        for perm in itertools.permutations(range(n)):
            t=tuple(sorted((perm[i],perm[j]) for i in range(n) for j in range(n) if less[i][j]))
            if canon is None or t<canon: canon=t
        if canon in seen_iso: continue
        seen_iso.add(canon)
        cnt+=1
        # compute balanced pairs
        LE=linexts(n,set(edges))
        E=len(LE)
        minima=[i for i in range(n) if not any(less[j][i] for j in range(n))]
        maxima=[i for i in range(n) if not any(less[i][j] for j in range(n))]
        bal_pairs=[]
        for i,j in pairs:
            if less[i][j] or less[j][i]: continue
            before=sum(1 for L in LE if L.index(i)<L.index(j))
            d=Fr(before,E)
            if Fr(1,3)<=d<=Fr(2,3): bal_pairs.append((i,j,float(d)))
        min_bal = len(minima)==2 and any({minima[0],minima[1]}=={i,j} for i,j,_ in bal_pairs)
        max_bal = len(maxima)==2 and any({maxima[0],maxima[1]}=={i,j} for i,j,_ in bal_pairs)
        cores.append((canon, E, len(minima), len(maxima), min_bal, max_bal, len(bal_pairs)))
    return cores

for n in range(2,7):
    cores=analyze(n)
    nb_min=sum(1 for c in cores if c[4])
    nb_max=sum(1 for c in cores if c[5])
    nb_either=sum(1 for c in cores if c[4] or c[5])
    no_bal=[c for c in cores if c[6]==0]
    print(f"n={n}: {len(cores)} prime width-2 cores; minima-balanced {nb_min}, maxima-balanced {nb_max}, either {nb_either}/{len(cores)}; cores with NO balanced pair: {len(no_bal)}")

# Characterize the n=6 cores where neither minima nor maxima is balanced
print("\n=== n=6 cores where neither minima nor maxima balanced ===")
def detail(n):
    pairs=list(itertools.combinations(range(n),2)); seen=set()
    for mask in range(1<<len(pairs)):
        edges=[pairs[k] for k in range(len(pairs)) if mask&(1<<k)]
        less=closure(n,edges)
        if not is_poset(n,less) or width(n,less)!=2 or not is_connected(n,less) or series_decomp(n,less): continue
        canon=min(tuple(sorted((p[i],p[j]) for i in range(n) for j in range(n) if less[i][j])) for p in itertools.permutations(range(n)))
        if canon in seen: continue
        seen.add(canon)
        LE=linexts(n,set(edges)); E=len(LE)
        minima=[i for i in range(n) if not any(less[j][i] for j in range(n))]
        maxima=[i for i in range(n) if not any(less[i][j] for j in range(n))]
        balp=[]
        for i,j in pairs:
            if less[i][j] or less[j][i]: continue
            b=sum(1 for L in LE if L.index(i)<L.index(j)); d=Fr(b,E)
            if Fr(1,3)<=d<=Fr(2,3): balp.append((i,j,f"{float(d):.2f}"))
        mb={minima[0],minima[1]} if len(minima)==2 else None
        Mb={maxima[0],maxima[1]} if len(maxima)==2 else None
        minbal = mb and any({i,j}==mb for i,j,_ in balp)
        maxbal = Mb and any({i,j}==Mb for i,j,_ in balp)
        if not minbal and not maxbal:
            print(f"  edges(transitive-reduced rel as <): {sorted(edges)}, E={E}, minima={minima}, maxima={maxima}")
            print(f"    balanced pairs: {balp}")
detail(6)
