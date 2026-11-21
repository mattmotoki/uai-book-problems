# Monte Carlo check of the Problem 3.3 counterexample (Pro query 001):
# mu(1)=1/2+d_t, nu(1)=1/2-d_t, d_t=1/(32t); xi- = 1/4 mu + 3/4 nu, xi+ = 3/4 mu + 1/4 nu; 0-1 loss under mu.
import numpy as np
rng = np.random.default_rng(0)
paths, n = 200_000, 4000
logR = np.zeros(paths)  # log nu/mu of history
gap = np.zeros(n)      # E_mu[loss(xi-) - loss(xi+)] at step t
for t in range(1, n + 1):
    d = 1 / (32 * t)
    R = np.exp(logR)
    pred_minus = R < 1/3   # xi- predicts 1
    pred_plus = R < 3      # xi+ predicts 1
    # expected loss under mu given prediction p: predict 1 -> 1/2-d, predict 0 -> 1/2+d
    lm = np.where(pred_minus, 0.5 - d, 0.5 + d)
    lp = np.where(pred_plus, 0.5 - d, 0.5 + d)
    gap[t-1] = (lm - lp).mean()
    x = rng.random(paths) < 0.5 + d
    logR += np.where(x, np.log((0.5 - d) / (0.5 + d)), np.log((0.5 + d) / (0.5 - d)))
cum = np.cumsum(gap)
H = np.cumsum(1 / (32 * np.arange(1, n + 1)))
for t in [10, 100, 1000, 4000]:
    print(f"n={t:5d}  L(xi-)-L(xi+)={cum[t-1]:.4f}  claimed lower bound sum d_t={H[t-1]:.4f}  ratio={cum[t-1]/H[t-1]:.2f}")
print("min per-step gap / d_t:", (gap / (1/(32*np.arange(1,n+1)))).min().round(3))
print("P(1/2<R_n<3/2) at end:", ((np.exp(logR) > 0.5) & (np.exp(logR) < 1.5)).mean().round(3))
