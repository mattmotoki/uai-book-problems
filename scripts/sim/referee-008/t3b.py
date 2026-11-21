import math
# A = mixture of point masses: half on 1^inf, half on 0^inf, plus adversarial "contrarian" A that predicts against minus core.
def run(N, eta):
    g=1/(32*math.sqrt(N)); a=.5+g; b=.5-g; gap=neg=0.0
    for t in range(N):
        for k in range(t+1):
            mu=math.exp(k*math.log(a)+(t-k)*math.log(b)); nu=math.exp(k*math.log(b)+(t-k)*math.log(a))
            A1 = 0.5 if k==t else 0.0; A0 = 0.5 if k==0 else 0.0
            def sc(wm):
                s1=(1-eta)*(wm*mu*a+(1-wm)*nu*b)+eta*A1
                s0=(1-eta)*(wm*mu*b+(1-wm)*nu*a)+eta*A0
                return s1-s0
            am=1 if sc(.25)>=0 else 0; ap=1 if sc(.75)>=0 else 0
            w=math.comb(t,k)*mu
            if am==0 and ap==1: gap+=w*2*g
            if am==1 and ap==0: neg+=w*2*g
    return gap,neg
for N in [256,1024,4096]:
    print(N, run(N,2**-20), math.sqrt(N)/32)
