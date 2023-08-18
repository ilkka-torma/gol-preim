vrs = [0]
NUM_THREADS = 2


from pysat.solvers import Glucose4
import time, datetime
import random
import multiprocessing as mp
import functools
import copy
import math

from enum import Enum

class Status(Enum):
    SOLE = 0
    OTHER = 1
    DEAD = 2
    DEADEND = 3


"""
vrs is a list of python objects, and their indices represent
what number is used for each in the minisat
our functions operate on cnfs, i.e. they take a cnf in the variables,
and return a cnf in the variables

as a side-effect, they may introduce new variables and introduce global
constraints
"""

# is s1 a subset of s2? both are assumed sorted and duplicate-free
def subset_sorted(s1, s2):
    if s1:
        if s2:
            if s1[0] == s2[0]:
                return subset_sorted(s1[1:], s2[1:])
            elif s1[0] < s2[0]:
                return False
            else:
                return subset_sorted(s1, s2[1:])
        else:
            return False
    else:
        return True

# binary words, potentially with nonempty forbidden subwords
def all_words(n, forbidden=None):
    if forbidden is None:
        forbidden = [set()]*n
    if n == 0:
        yield tuple()
    else:
        for w in all_words(n-1, forbidden[1:]):
            for b in range(2):
                v = (b,) + w
                if not any(v[:i] in forbidden[0] for i in range(2, len(v))):
                    yield v

def cart_prod(xss):
    if not xss:
        yield []
    else:
        for xs in cart_prod(xss[1:]):
            for x in xss[0]:
                yield [x]+xs

# this is just for naming our basic variables
def name_basic(vec, layer=0):
    global vrs
    vr = vec+(layer,)
    if vr not in vrs:
        vrs.append(vr)
    return vrs.index(vr)

# nbhd is a list of basic variables
def generate_gol_one(nbhd):
    center = nbhd[4]
    others = nbhd[:4] + nbhd[5:]
    return AND(OR([[center]], generate_s(others, 3)),
               OR(generate_s(others, 2), generate_s(others, 3)))

def generate_gol_ker(nbhd):
    center = nbhd[4]
    others = nbhd[:4] + nbhd[5:]
    #print (generate_not_s(others, 3))
    return AND(generate_not_s(others, 3), OR([[-center]], generate_not_s(others, 2)))

# exactly n
def generate_s(V, n):
    if n == 0:
        return list([-v] for v in V)
    if len(V) < n:
        return [[]]
    if len(V) == n:
        return list([v] for v in V)
    left = V[:len(V)//2]
    right = V[len(V)//2:]
    inst = [[]]
    for i in range(0, n+1):
        inst = OR(inst, AND(generate_s(left, i), generate_s(right, n-i)))
    return inst

# at least n
def generate_geq_s(V, n):
    #print (V, n)
    if n == 0:
        #print (V, n, [])
        return []
    if len(V) < n:
        #print (V, n, [[]])
        return [[]]
    if len(V) == n:
        #print (V, n, list([v] for v in V))
        return list([v] for v in V)
    left = V[:len(V)//2]
    right = V[len(V)//2:]
    inst = [[]]
    for i in range(0, n+1):
        inst = OR(inst, AND(generate_geq_s(left, i), generate_geq_s(right, n-i)))
    #print (V, n, inst)
    return inst

# any number but n
def generate_not_s(V, n):
    if n == 0:
        return [V]
    if len(V) < n:
        return []
    if len(V) == n:
        return [list(-v for v in V)]
    inst = [[]]
    for i in range(0, n):
        #print (i)
        #print ( generate_s(V, i))
        #print ( "ij", inst, OR(inst, generate_s(V, i)))
        inst = OR(inst, generate_s(V, i))
    #print ("jyg", generate_geq_s(V, n+1))
    inst = OR(inst, generate_geq_s(V, n+1))
    return inst

def simplify(L):
    L = list(map(list, set(map(frozenset, L)))) # absolute lol
    LL = []
    for a in L:
        if len(set(map(abs, a))) != len(a): # automatically true then...
            continue
        LL.append(a)
    LLL = []
    for a in LL:
        for b in LL:
            if a == b:
                continue
            if set(b).issubset(set(a)):
                break
        else:
            LLL.append(a)
    return LLL



# and of two cnfs...
def AND(a, b):
    return simplify(a + b)

def OR(a, b):
    r = []
    for ai in a:
        for bi in b:
            r.append(ai + bi)
    return simplify(r)




# 1,2,... replaced by names
def substi(cnf, names):
    newcnf = []
    for l in cnf:
        newcnf.append([])
        for i in l:
            if i > 0:
                newcnf[-1].append(names[i-1])
            else:
                newcnf[-1].append(-names[-i-1])
    return newcnf

one = generate_gol_one([1,2,3,4,5,6,7,8,9])
ker = generate_gol_ker([1,2,3,4,5,6,7,8,9])
either = OR(one, ker)


def model_to_pat(model):
    global vrs
    pat = {}
    for var in model:
        x,y,l = vrs[abs(var)]
        if l == 0:
            pat[x,y] = 1*(var>0)
    return pat

def bimodel_to_pat(model):
    global vrs
    pat0 = dict()
    pat1 = dict()
    for var in model:
        x,y,l = vrs[abs(var)]
        if l==0:
            pat0[x,y] = 1*(var>0)
        else:
            pat1[x,y] = 1*(var>0)
    for vec in pat0:
        if vec in pat1:
            if pat0[vec] != pat1[vec]:
                if pat0[vec]:
                    pat0[vec] = "I"
                else:
                    pat0[vec] = "O"
            elif pat0[vec]:
                pat0[vec] = "i"
            else:
                pat0[vec] = "o"
    return pat0

def str_to_pat(s, offset=(0,0)):
    x,y = offset
    pat = {}
    for (j,r) in enumerate(s.splitlines()):
        for (i,c) in enumerate(r):
            if c == '0':
                pat[x+i,y+j] = 0
            elif c == '1':
                pat[x+i,y+j] = 1
    return pat

def gol_pre_dict(pat, layer=0, period=None):
    inst = []
    if period is None:
        small = pat
    else:
        ys = set(y for (_,y) in pat)
        small = set((i,y) for y in ys for i in range(period[0])) | set(pat)
    for (x,y) in small:
        v00 = name_basic((x-1, y-1), layer=layer)
        v01 = name_basic((x-1, y), layer=layer)
        v02 = name_basic((x-1, y+1), layer=layer)
        v10 = name_basic((x, y-1), layer=layer)
        v11 = name_basic((x, y), layer=layer)
        v12 = name_basic((x, y+1), layer=layer)
        v20 = name_basic((x+1, y-1), layer=layer)
        v21 = name_basic((x+1, y), layer=layer)
        v22 = name_basic((x+1, y+1), layer=layer)
        nbhd = [v00, v01, v02, v10, v11, v12, v20, v21, v22]
        if (x,y) not in pat:
            inst.extend(substi(either, nbhd))
        elif pat[x,y] == 0:
            inst.extend(substi(ker, nbhd))
        else:
            inst.extend(substi(one, nbhd))
    if period is not None:
        (p,q) = period
        big = set(nbr for vec in pat for nbr in nbors(vec))
        for (x,y) in big:
            if (x+p,y+q) in big:
                var0 = name_basic((x,y), layer=layer)
                var1 = name_basic((x+p,y+q), layer=layer)
                inst.extend([[-var0,var1],[var0,-var1]])
    return inst


def nbors(vec):
    x,y = vec
    yield (x-1,y-1)
    yield (x-1,y)
    yield (x-1,y+1)
    yield (x,y-1)
    yield (x,y+1)
    yield (x+1,y-1)
    yield (x+1,y)
    yield (x+1,y+1)

def adjs(vec):
    x,y = vec
    yield (x-1,y)
    yield (x,y-1)
    yield (x,y+1)
    yield (x+1,y)

# default is east, then ccw
# positive y is south
def nbor_at(vec, rot=0):
    x,y = vec
    ring = [(x+1,y),(x+1,y-1),(x,y-1),(x-1,y-1),(x-1,y),(x-1,y+1),(x,y+1),(x+1,y+1)]
    return ring[rot%8]

def to_vars(pat, layer=0):
    for vec in pat:
        yield (1 if pat[vec] else -1)*name_basic(vec, layer)

def func_to_vars(f, domain, layer=0):
    for vec in domain:
        val = f(vec)
        if val is not None:
            yield (1 if val else -1)*name_basic(vec, layer)

def func_to_pat(f, domain):
    pat = {}
    for vec in domain:
        val = f(vec)
        if val is not None:
            pat[vec] = val
    return pat

# status of computation
def status(pat, forced, allowed_func_or_set, allow_diamonds=False, period=None, existential=False):
    if not hasattr(allowed_func_or_set, "__call__"):
        allowed = lambda vec: vec in allowed_func_or_set
    else:
        allowed = allowed_func_or_set

    
    layer0 = gol_pre_dict(pat)
    if period is not None:
        layer0_per = gol_pre_dict(pat, period=period)
    else:
        layer0_per = layer0
    
    with Glucose4(bootstrap_with=layer0_per) as solver:
        # can all forced patterns be produced, or the assumption if none are given?
        # if not, we're dead
        # preimages must be periodic here
        # in existential case, one forced pattern is enough
        for (assum_preim, preims) in forced:
            assum = list(to_vars(assum_preim))
            if preims:
                for preim in preims:
                    if solver.solve(assumptions=assum+list(to_vars(preim))):
                        if existential:
                            break
                    elif not existential:
                        return Status.DEAD
                else:
                    if existential:
                        return Status.DEAD
            elif not solver.solve(assumptions=assum):
                return Status.DEAD

    # can another preimage be produced?
    # if not, we're done
    # here preimages don't need to be periodic
    for (assum_preim, preims) in forced:
        if preims:
            assum = list(to_vars(assum_preim))
            with Glucose4(bootstrap_with=layer0) as solver:
                for preim in preims:
                    solver.add_clause([-var for var in to_vars(preim)])
                if solver.solve(assumptions=assum):
                    break
    else:
        return Status.SOLE

    # is there a diamond?
    # if yes, we're at a dead end
    # here preimages are periodic
    if not allow_diamonds:
        layer1_per = gol_pre_dict(pat, layer=1, period=period)
        border = set()
        for vec in pat:
            for nbr in nbors(vec):
                if nbr not in pat and allowed(nbr):
                    border.add(vec)
                    border.add(nbr)
        eq_border = [[name_basic(v, layer=b), -name_basic(v, layer=1-b)]
                     for v in border for b in [0,1]]
    
        with Glucose4(bootstrap_with=layer0_per+layer1_per+eq_border) as bisolver:
            for (assum_preim, preims) in forced:
                assum = list(to_vars(assum_preim, layer=0))+list(to_vars(assum_preim, layer=1))
                for preim in preims:
                    p_assum = list(to_vars(preim, layer=0))
                    for var in to_vars({vec:preim[vec] for vec in preim
                                        if all(nbr in pat or not allowed(nbr)
                                               for nbr in nbors(vec))},
                                       layer=1):
                        if bisolver.solve(assumptions=assum+p_assum+[-var]):
                            return Status.DEADEND

    # otherwise we're still computing
    return Status.OTHER

# find relevant preimage patterns for given chunk
# assumes chunk is within forceds' domain
# takes a while unless there are only a few, in that case it's faster than trying all
# we don't use period here
def find_relevants(pat, preim_func, forced, chunk):
    layer = gol_pre_dict(pat)
    nhood = set(nbr for vec in pat for nbr in nbors(vec))
    assum = [[var] for var in func_to_vars(preim_func, nhood)]
    restr = [{vec:preim[vec] for vec in chunk} for preim in forced]
    not_forced = [[-var for var in to_vars(preim)] for preim in restr]

    res = []
    with Glucose4(bootstrap_with=layer+assum+not_forced) as solver:
        while solver.solve():
            md = solver.get_model()
            new = []
            rel = 0
            for vec in reversed(chunk):
                rel *= 2
                nm = name_basic(vec)
                if nm in md:
                    new.append(-nm)
                    rel += 1
                else:
                    new.append(nm)
            solver.add_clause(new)
            res.append(rel)
            if len(res)%1000 == 0:
                print("Found", len(res), "so far")
    res.sort()
    return res

class Score:

    def __init__(self, nums):
        self.the_max = max(nums)
        self.the_sum = sum(nums) - max(nums)
        self.same = max(nums) == min(nums)

    def __lt__(self, other):
        if self.the_max < other.the_max:
            return True
        elif self.the_sum < other.the_sum:
            return True
        return False

    def __min__(self, other):
        if self.the_max < other.the_max:
            return self
        elif self.the_max > other.the_max:
            return other
        elif self.the_sum <= other.the_sum:
            return self
        return other

    def much_less(self, other):
        if self.the_max < other.the_max:
            return True
        elif self.the_max == other.the_max and self.same < other.same:
            return True
        return False

    def __str__(self):
        return "({:0.4f}|{:0.4f})".format(self.the_max, self.the_sum)


# score, based on number of other preims
# assume that status is OTHER
# old score is computed as follows:
# - loop through pairs p=(P,Qs)
# - loop though chunks C
# - loop through killable patterns R not yet killed
# - let M(p,R,C) = 1+max number of shared bits with a Q restricted to C
# - score is (sum_p sum_C (sum_R M(p,R,C)^2)^2)^0.25
# new score: sum_p sum_C log(1+sum_R M(p,R,C)/|C|)/|C|
# we don't use periods here
def compute_score(pat, forced, chunks, relevants):
    #print(pat, forced, chunks)
    with Glucose4(bootstrap_with=gol_pre_dict(pat)) as solver:
        scores = []
        new_relevs = []
        for ((preim_assum, forced_pats), relevs) in zip(forced, relevants):
            if forced_pats:
                new_relevants = []
                for (chunk, relvs) in zip(chunks, relevs):
                    new_relvs = []
                    chunk_score = 0
                    for num in relvs:
                        assum = [(1 if preim_assum[vec] else -1)*name_basic(vec)
                                 for vec in preim_assum]
                        sim_forced = [0]*len(forced_pats)
                        not_forced = [False]*len(forced_pats)
                        num_stored = num
                        for vec in chunk:
                            assum.append((1 if num%2 else -1)*name_basic(vec))
                            for (i, preim) in enumerate(forced_pats):
                                if preim[vec] == num%2:
                                    sim_forced[i] += 1
                                else:
                                    not_forced[i] = True
                            num = num//2
                        if all(not_forced) and solver.solve(assumptions=assum):
                            new_relvs.append(num_stored)
                            chunk_score += max(sim_forced)
                    new_relevants.append(new_relvs)
                    scores.append(math.log(1+chunk_score/len(chunk))/len(chunk))
                new_relevs.append(new_relevants)
            else:
                new_relevs.append([[] for _ in range(len(chunks))])
        #print(new_relevs)
        return Score(scores), new_relevs

def avg(a,b):
    if a is None:
        return (2*b, True)
    if b is None:
        return (2*a, True)
    return (a+b, False)

def dist(v1,v2):
    if v1 is None or v2 is None:
        return None
    x,y = v1
    i,j = v2
    dx = abs(x-i)
    dy = abs(y-j)
    return 2*max(dx,dy) + min(dx,dy)

def linesort_orig(line, start):
    line.sort()
    cur = min(line, key=lambda vec: dist(vec, start))
    while nbor_at(cur, 0) in line:
        cur = nbor_at(cur, 0)
    rot = 4
    new = [cur]
    # build skeleton
    while True:
        for i in range(1,9):
            if nbor_at(cur, rot+i) in line:
                rot += i
                break
        for i in range(1,9):
            if nbor_at(cur, rot-i) not in line:
                rot -= i
                break
        cur = nbor_at(cur, rot)
        if cur not in line or cur in new:
            break
        new.append(cur)
        print(new)
        rot = rot-3
    new = [None] + new + [None]
    for vec in line:
        if vec not in new:
            min_i = min((i for i in range(1,len(new)-1)),
                        key=lambda i: avg(dist(vec, new[i]), dist(vec, new[i+1])))
            new = new[:min_i+1] + [vec] + new[min_i+1:]
    return new[1:-1]

def linesort(line, start):
    line = line[:]
    line.sort(key=lambda v: (sum(1 for w in line if w in nbors(v)), v))
    cur = old =  line.pop()
    new = [cur]
    while line:
        nbrs = list(v for v in line if v in nbors(cur))
        if nbrs:
            vec = min(nbrs, key=lambda v: (dist(v,cur), dist(v,old)))
            old, cur = cur, vec
        else:
            vec = min(line, key=lambda v: sum(1 for w in line if w in nbors(v)))
            old = cur = vec
        line.remove(vec)
        new.append(vec)
    return new


# worker process for finding scores
def finder_poolworker(pat, forced, chunks, period, line, blen, relv, score, seen, forbs, allowed_domain, allow_diamonds, existential, require_drop, prune_subsets, fill_states, ix):
    valids = []
    new_forbs = set()
    pruned = 0
    forb_fill = {nbor2 : fill_states[nbor2]
                 for i in range(blen)
                 for nbor in nbors(line[(ix+i)%len(line)])
                 for nbor2 in adjs(nbor)
                 if nbor2 in fill_states and fill_states[nbor2] is not None}
    if period is None:
        inside = True
    else:
        (p,_) = period
        inside = all(0 <= line[(ix+i)%len(line)][0] < p for i in range(blen))
    pat.update(forb_fill)
    for wd in all_words(blen, forbidden=forbs[ix:]+forbs[:ix]):
        for (i, b) in enumerate(wd):
            pat[line[(ix+i)%len(line)]] = b
        if prune_subsets:
            items = tuple(sorted(pat.items()))
            if any(subset_sorted(items, the_seen) for the_seen in seen):
                pruned += 1
                continue
        elif tuple(sorted(pat.items())) in seen:
            pruned += 1
            continue
        if status(pat, forced, allowed_domain, allow_diamonds, period, existential) not in [Status.OTHER, Status.SOLE]:
            new_forbs.add(wd)
            continue
        sc, rv = compute_score(pat, forced, chunks, relv)
        new_pat = {line[(ix+i)%len(line)] : wd[i] for i in range(blen)}
        new_pat.update(forb_fill)
        valids.append(Extension(new_pat, sc, chunks, rv))
    forced = False
    if not valids or (inside and len(valids) == 1):
        scores = valids
        forced = True
    elif require_drop:
        scores = [ext for ext in valids if ext.score.much_less(score)]
    else:
        scores = valids
    return (ix, scores, forced, new_forbs, pruned)

def encode_relevants(pats, chunk):
    "Encode patterns over chunk into integers"
    ret = []
    for pat in pats:
        n = 0
        for vec in chunk:
            n *= 2
            n += pat[vec]
        ret.append(n)
    return ret


# Pattern builder history snapshot
class Snapshot:
    def __init__(self, line, extensions):
        self.line = line
        self.extensions = extensions

# Pattern builder extension
class Extension:
    def __init__(self, pat, score, chunks, relvs):
        self.pat = pat
        self.score = score
        self.chunks = chunks
        self.relvs = relvs


# Backtracking pattern builder
# forced is a nonempty list of pairs (P,Qs)
# each P is a function (int,int) -> {0,1,None} representing a potentially infinite pattern
# each Q is a 2D pattern represented as dict[int, int] : int
# the Qs should all have equal domains
# the semantics for (P,Qs) is that P is in preimage, and if it occurs then exactly Qs are allowed
# chunks is a list of lists of points representing (ordered) subsets of Z^2
# relv is a list of lists of ints encoding patterns, same length as chunks
# allowed is a boolean function on 2D points that tells where we can extend
# History is a list of tuples (line, [(pattern, score, relv)])
# Each tuple represents a border line and an ordering of extension choices
# The first element in the ordering is the chosen one
# blen can be set when a halted computation is resumed
# use_corners controls if pattern border uses Moore of von Neumann nhood
# merge_bound controls when chunks should be merged (higher value => merge sooner)
# forbidden cells are filled with fill_state if not None
# period, if not None, is enforced on the forced preimages, but not on killable ones
class Finder:

    # initialize everything
    def __init__(self, forced, chunks=None, allowed=lambda _: True, pat=None, line=None, relv=None, allow_diamonds=False, blen=1, use_corners=True, merge_bound=10000, fill_state=lambda _: None, period=None, prune_subsets=False, existential=False):
        self.forced = forced
        self.domain = list(forced[0][1][0])
        self.allowed = allowed
        if chunks is None:
            chunks = [self.domain]
        if relv is None:
            if (not pat) or max(len(c) for c in chunks) < 16:
                relv = [[list(range(2**len(chunk))) if preims else []
                         for chunk in chunks]
                        for (_, preims) in forced]
            else:
                relv = [[find_relevants(pat, preim_assum, preims, chunk)
                         for chunk in chunks]
                        for (preim_assum, preims) in forced]
        if pat is None:
            self.pat = {}
            self.line = linesort([p for p in self.domain if allowed(p)], min(self.domain))
        else:
            self.pat = pat
            if pat:
                self.line = list(set(nbor for vec in pat for nbor in nbors(vec) if nbor not in pat and allowed(nbor)))
            else:
                self.line = list(vec for vec in self.domain if allowed(vec))
        if line is not None:
            self.line = line
        self.allow_diamonds = allow_diamonds
        score, relv = compute_score(self.pat, self.concrete_forced(), chunks, relv)
        self.history = [Snapshot([], [Extension({}, score, chunks, relv)])]
        self.seen = set()
        self.pruned = 0
        self.blen=blen
        self.use_corners = use_corners
        self.merge_bound = merge_bound
        self.fill_state = fill_state
        self.period = period
        self.prune_subsets = prune_subsets
        self.existential = existential
        self.start_time = time.perf_counter()

    def score(self):
        return self.history[-1].extensions[0].score

    def relv(self):
        return self.history[-1].extensions[0].relvs

    def chunks(self):
        return self.history[-1].extensions[0].chunks

    def concrete_forced(self):
        nhood = set(self.pat)|set(self.domain)
        for _ in range(2):
            nhood = set(nbr for vec in nhood for nbr in nbors(vec))
        return [(func_to_pat(preim_assum, nhood), preims) for (preim_assum, preims) in self.forced]

    # extend continuously until there are no more killable patterns
    # return True/False for success/failure to kill all patterns
    def extend_until_null(self):
        while self.history and sum(len(y) for x in self.relv() for y in x):
            print("Score {} relevants {} size {} depth {} seen {} pruned {} in {}".format(
                self.score(),
                [[len(y) for y in x] for x in self.relv()] if any(len(y)>10 for x in self.relv() for y in x) else self.relv(),
                len(self.pat),
                len(self.history),
                len(self.seen),
                self.pruned,
                str(datetime.timedelta(seconds=time.perf_counter() - self.start_time))))
            prettyprint(self.pat, preim=self.domain, border=self.line)
            if len(self.chunks()) > 1:
                relevants = self.relv()
                sizes = [(sum(len(relvs[i]) for relvs in relevants), i)
                         for i in range(len(self.chunks()))]
                sizes.sort()
                (len1, i1), (len2, i2) = sizes[:2]
                if (len1+1)*(len2+1) < self.merge_bound:
                    print("Merging chunks {} and {}".format(i1,i2))
                    self.merge_chunks(i1, i2)
                    continue
            upper = 2
            maxlen = max(len(x) for r in self.relv() for x in r)
            if maxlen < 400:
                upper = 3
            if maxlen < 200:
                upper = 4
            if maxlen < 100:
                upper = 5
            #if maxlen < 50:
            #    upper = 6
            print("Using", maxlen, upper)
            forbs = None
            for blen in range(self.blen,upper):
                res, forbs, req_drop = self.extend(blen, forbs)
                if res:
                    break
            else:
                if maxlen < 15 and req_drop:
                    print("Extending randomly")
                    rnd = self.extend_random(limit=10000)
                    if rnd is None:
                        self.backtrack()
                    else:
                        ext, score, relv = rnd
                        self.extend_by(ext)
                        self.history.append(Snapshot(line=self.line,
                                                     extensions=[Extension(ext, score, self.chunks(), relv)]))
                else:
                    self.backtrack()
            self.blen = 1
        return self.history != []

    # backtrack to previous valid state
    # return True/False for success
    def backtrack(self):
        if not self.history:
            return False
        snapshot = self.history[-1]
        extension = snapshot.extensions[0]
        for vec in extension.pat:
            del self.pat[vec]
        self.line = snapshot.line
        del snapshot.extensions[0]
        if snapshot.extensions:
            self.extend_by(snapshot.extensions[0].pat)
        else:
            del self.history[-1]
            return self.backtrack()
        return True
            
    # extend by block of given length
    # return forbidden blocks, True/False for success/failure, and True/False for score drop
    # update mode if needed
    def extend(self, blen, forbs=None):
        if forbs is None:
            forbs = [set()]*len(self.line)
        require_drop = True
        if self.period is None:
            for (ix, vec) in enumerate(self.line):
                if sum(nbr in self.line for nbr in nbors(vec)) <= 2 and sum(nbr in self.pat or not self.allowed(nbr) for nbr in nbors(vec)) >= 6:
                    ixes = [ix]
                    require_drop = False
                    break
            else:
                ixes = list(range(len(self.line)))
        else:
            ixes = list(range(len(self.line)))
        if len(ixes) < blen:
            return False, [], require_drop
        minx = min(min(p[0] for p in self.pat or self.domain), min(p[0] for p in self.domain))
        maxx = max(max(p[0] for p in self.pat or self.domain), max(p[0] for p in self.domain))
        miny = min(min(p[1] for p in self.pat or self.domain), min(p[1] for p in self.domain))
        maxy = max(max(p[1] for p in self.pat or self.domain), max(p[1] for p in self.domain))
        allowed_domain = set((x,y)
                             for x in range(minx-2, maxx+3)
                             for y in range(miny-2, maxy+3)
                             if self.allowed((x,y)))
        fill_states = {(x,y) : self.fill_state((x,y))
                       for x in range(minx-2, maxx+3)
                       for y in range(miny-2, maxy+3)
                       if not self.allowed((x,y))
                       and (x,y) not in self.pat}
        conc_forced = self.concrete_forced()
        with mp.Pool(NUM_THREADS) as pool:
            worked = list(pool.imap_unordered(functools.partial(finder_poolworker,
                                                                self.pat.copy(),
                                                                conc_forced,
                                                                self.chunks(),
                                                                self.period,
                                                                self.line,
                                                                blen,
                                                                self.relv(),
                                                                self.score(),
                                                                self.seen,
                                                                forbs,
                                                                allowed_domain,
                                                                self.allow_diamonds,
                                                                self.existential,
                                                                require_drop,
                                                                self.prune_subsets,
                                                                fill_states),
                                              ixes))
        forced = False
        scores = []
        for (ix, the_scores, is_forced, forb, pruned) in worked:
            self.pruned += pruned
            if is_forced:
                scores = the_scores
                forced = True
                break
            else:
                scores.extend(the_scores)
                forbs[ix] = forb
        scores.sort(key=lambda ext: ext.score)
        if scores:
            if forced:
                msg = "Forced"
            else:
                msg = "Choice"
        else:
            msg = "Not found for block length {} in {}".format(
                blen,
                str(datetime.timedelta(seconds=time.perf_counter() - self.start_time)))
        print(msg, ", ".join("{}".format(ext.score) for ext in scores))
        if scores:
            self.history.append(Snapshot(self.line, scores))
            new_pat = scores[0].pat
            self.extend_by(new_pat)
            return True, None, require_drop
        return False, forbs, require_drop

    # extend by random blobs until score decreases
    # return extending pattern, score and relevants
    # if not found after limit, return None
    # todo: remove unnecessary bits
    def extend_random(self, limit=None):
        num = 0
        rej = 0
        thickline = set(self.line)
        for _ in range(2):
            thickline = set(nbr for vec in thickline for nbr in nbors(vec)
                            if self.allowed(nbr)
                            and nbr not in self.pat)
        while (limit is None or num < limit):
            x,y = random.choice(self.line)
            new_set = [(i,j) for i in range(x-3,x+4) for j in range(y-3,y+4)
                       if (i,j) in thickline]
            for vec in new_set:
                self.pat[vec] = random.randint(0,1)
            sts = status(self.pat, self.concrete_forced(), self.allowed, period=self.period, existential=self.existential)
            if sts == Status.SOLE:
                score = 0
                relv = []
                break
            elif sts == Status.OTHER:
                score, relv = compute_score(self.pat, self.concrete_forced(), self.chunks(), self.relv())
                if score < self.score():
                    break
            else:
                rej += 1
            for vec in new_set:
                del self.pat[vec]
            num += 1
            if num%1000 == 0:
                print("{} rejected out of {}".format(rej, num))
        else:
            return None
        for vec in list(new_set):
            b = self.pat[vec]
            del self.pat[vec]
            new_set.remove(vec)
            sc, _ = compute_score(self.pat, self.concrete_forced(), self.chunks(), self.relv())
            if sc > score:
                self.pat[vec] = b
                new_set.append(vec)
        ext = {vec:self.pat[vec] for vec in new_set}
        for vec in ext:
            del self.pat[vec]
        return ext, score, relv

    # extend pattern by given disjoint pattern
    # update line as well
    # do not update history
    def extend_by(self, pattern):
        self.pat.update(pattern)
        newline = set(self.line)
        for vec in pattern:
            for nbr in (nbors(vec) if self.use_corners else adjs(vec)):
                newline.add(nbr)
        self.line = linesort([vec for vec in newline if vec not in self.pat and self.allowed(vec)],
                             min(self.domain))
        self.seen.add(tuple(sorted(self.pat.items())))


    # merge two chunks (given by indices)
    def merge_chunks(self, ix1, ix2):
        ix1, ix2 = max(ix1, ix2), min(ix1, ix2)
        chunks = self.chunks().copy()
        chunk1 = chunks[ix1]
        #width = len(chunk1)
        chunk2 = chunks[ix2]
        new_chunk = chunk1 + [vec for vec in chunk2 if vec not in chunk1]
        relevants = copy.deepcopy(self.relv())
        #for ((_, preims), relv_pats) in zip(self.forced, relevants):
        #    preims1 = [sum(preim[vec]*2**i for (i, vec) in enumerate(chunk1))
        #               for preim in preims]
        #    preims2 = [sum(preim[vec]*2**i for (i, vec) in enumerate(chunk2))
        #               for preim in preims]
        #    new_pats = []
        #    rel_pre = [(relv1, pre2) for relv1 in relv_pats[ix1] for pre2 in preims2]
        #    pre_rel = [(pre1, relv2) for pre1 in preims1 for relv2 in relv_pats[ix2]]
        #    rel_rel = [(relv1, relv2) for relv1 in relv_pats[ix1] for relv2 in relv_pats[ix2]]
        #    for (relv1, relv2) in rel_pre + pre_rel + rel_rel:
        #        num = relv1
        #        extra = 0
        #        for vec in chunk2:
        #            if vec not in chunk1:
        #                num += (relv2%2)*2**(width+extra)
        #                extra += 1
        #            elif (relv1//(2**chunk1.index(vec)))%2 != relv2%2:
        #                break
        #            relv2 = relv2 // 2
        #        else:
        #            new_pats.append(num)
        #
        #    del relv_pats[ix1]
        #    del relv_pats[ix2]
        #    new_pats.sort()
        #    relv_pats.append(new_pats)
        del chunks[ix1]
        del chunks[ix2]
        chunks.append(new_chunk)
        for ((preim_assum, forced), relvs) in zip(self.forced, relevants):
            del relvs[ix1]
            del relvs[ix2]
            if forced:
                relvs.append(find_relevants(self.pat, preim_assum, forced, new_chunk))
            else:
                relvs.append([])
        score, relv = compute_score(self.pat, self.concrete_forced(), chunks, relevants)

        self.history.append(Snapshot(self.line, [Extension({}, score, chunks, relv)]))


    # try to complete pattern to rectangle, then return it
    # use period
    def complete_to_rect(self, xborder, yborder):
        pat = self.pat.copy()
        xmin = min(vec[0] for vec in pat) - xborder
        xmax = max(vec[0] for vec in pat) + xborder
        ymin = min(vec[1] for vec in pat) - yborder
        ymax = max(vec[1] for vec in pat) + yborder
        remain = []
        for x in range(xmin,xmax+1):
            for y in range(ymin,ymax+1):
                  if (x,y) not in pat:
                      if self.allowed((x,y)):
                          remain.append((x,y))
                      elif self.fill_state((x,y)) is not None:
                          pat[x,y] = self.fill_state((x,y))
        remain.sort(key=lambda p: (min(abs(p[0] - v[0]) + abs(p[1] - v[1]) for v in pat),
                                   abs(p[0] - (xmax+xmin)/2) + abs(p[1] - (ymax+ymin)/2)))
        #remain.sort(key=lambda p: abs(p[0] - (xmax+xmin)/2) + abs(p[1] - (ymax+ymin)/2))
        #remain.sort(key=lambda p: abs(p[0] - (xmax+xmin)/2)**2 + abs(p[1] - (ymax+ymin)/2)**2)
        #remain.sort(key=lambda p: max(p[0], p[1]))
        vals = []
        ix = 0
        r = 0
        while len(vals) < len(remain):
            r += 1
            if r%50 == 0:
                prettyprint(pat)
                print()
            # Change to 0
            b = 0#random.randint(0,1)
            vals.append([b,1-b])
            pat[remain[ix]] = b
            st = status(pat, self.concrete_forced(), self.allowed, allow_diamonds=True, period=self.period, existential=self.existential)
            if st == Status.DEAD:
                while True:
                    vals[-1] = vals[-1][1:]
                    pat[remain[ix]] = vals[-1][0]
                    st = status(pat, self.concrete_forced(), self.allowed, allow_diamonds=True, period=self.period, existential=self.existential)
                    if st == Status.DEAD:
                        # dead end, backtrack
                        while not vals[-1][1:]:
                            del vals[-1]
                            del pat[remain[ix]]
                            ix -= 1
                    else:
                        #prettyprint(pat)
                        #print()
                        ix += 1
                        break
            else:
                #prettyprint(pat)
                ix += 1
                #print()
        return pat

    def store_pat(self, filename):
        with open(filename, 'w') as f:
            f.write(str(self.pat))

def prettyprint(pat, border=None, preim=None, order=False):
    pat = pat.copy()
    if border is not None:
        if order:
            for (vec, c) in zip(border, "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"+"-"*len(border)):
                if vec not in pat:
                    pat[vec] = c
        else:
            for vec in border:
                if vec not in pat:
                    pat[vec] = '-'
    if preim is not None:
        for vec in preim:
            if vec not in pat:
                if border is None or vec not in border:
                    pat[vec] = "P"
                else:
                    pat[vec] = "B"
    minx = min(p[0] for p in pat)
    maxx = max(p[0] for p in pat)
    miny = min(p[1] for p in pat)
    maxy = max(p[1] for p in pat)
    for y in range(miny, maxy+1):
        for x in range(minx, maxx+1):
            if (x,y) in pat:
                print(pat[x,y], end="")
            else:
                print(" ",end="")
        print()

def from_mat(m, origin=(0,0)):
    i,j = origin
    return {(x+i,y+j):b for (y,r) in enumerate(m) for (x,b) in enumerate(r)}

def pat_union(*pats):
    res = dict()
    for pat in pats:
        res.update(pat)
    return res




