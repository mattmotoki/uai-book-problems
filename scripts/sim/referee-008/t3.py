# Exact check of Theorem 3 for eta=0 and for a Bernoulli(q) background A, N = 16^j.
# State = (t, k ones). Under mu_N, the gap per step = 2*gamma*Pr(disagree, minus=0, plus=1) - 2*gamma*Pr(minus=1, plus=0).
import math
from fractions import Fraction
def run(N, eta, qA):
    g = 1/(32*math.sqrt(N)); a=0.5+g; b=0.5-g
    # log-probabilities via lgamma for counts
    gap=0.0; neg=0.0
    for t in range(N):            # history length t
        for k in range(t+1):
            lmu = k*math.log(a)+(t-k)*math.log(b)
            lnu = k*math.log(b)+(t-k)*math.log(a)
            lA  = k*math.log(qA)+(t-k)*math.log(1-qA)
            mu=math.exp(lmu); nu=math.exp(lnu); A=math.exp(lA)
            def score(wm):
                s1=(1-eta)*(wm*mu*a+(1-wm)*nu*b)+eta*A*qA
                s0=(1-eta)*(wm*mu*b+(1-wm)*nu*a)+eta*A*(1-qA)
                return s1-s0
            am = 1 if score(0.25)>=0 else 0
            ap = 1 if score(0.75)>=0 else 0
            w = math.comb(t,k)*mu
            if am==0 and ap==1: gap += w*2*g
            if am==1 and ap==0: neg += w*2*g
    return gap, neg
for N in [1,16,256,1024]:
    for eta,q in [(0,0.5),(2**-20,0.01),(2**-20,0.99)]:
        gap,neg=run(N,eta,q)
        print(N,eta,q,"gap=%.5f lb=%.5f ub=%.5f neg=%.2e"%(gap,math.sqrt(N)/32,math.sqrt(N)/16,neg))
