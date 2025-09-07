# τ-Crystal Physics Selector — Reference

This note makes “limits” physical: every tunable becomes a budgeted quantity with units, a predictor, and a gate checked by receipts.

## 1) Models (units; device-profiled)
Work \(W(n,k)=(w_1+w_2k)\,n\) items.  
Storage \(S(n,k)=s_0+(s_1+s_2k)\,n\) bytes.  
Compute time \(T=c_{\text{time}}\,W\) seconds.  
I/O time \(T_{\text{io}}=\dfrac{\mathrm{IO\_FRAC}\cdot S}{\beta}\) seconds (β = sustained B/s).  
Predictor \(\hat T=\max(T,T_{\text{io}})\) if IO\_FRAC>0, else \(\hat T=T\).  
Memory guard \(M_0+S\le M_{\max}\).  
Error \(\varepsilon(k)\le A e^{-\sigma k}\).

## 2) Feasibility polytope
Minimal error-feasible order:
\[
k_{\min}=\left\lceil -\frac{1}{\sigma}\ln\!\Big(\frac{\varepsilon_{\max}}{A}\Big)\right\rceil.
\]
Per-k caps on \(n\):
\[
n_{\text{time}}(k)=\frac{L_{\max}}{c_{\text{time}}(w_1+w_2k)},\quad
n_{\text{mem}}(k)=\frac{M_{\max}-M_0-s_0}{\,s_1+s_2k\,},
\]
\[
n_{\text{io}}(k)=\frac{\beta L_{\max}-\mathrm{IO\_FRAC}\,s_0}{\mathrm{IO\_FRAC}\,(s_1+s_2k)}\ (\text{if IO\_FRAC}>0 \land \beta L_{\max}>\mathrm{IO\_FRAC}\,s_0).
\]
\[
\mathcal P=\{(n,k)\in\mathbb N^2:\ k\ge k_{\min},\ 1\le n\le \lfloor\min(n_{\text{time}},n_{\text{mem}},n_{\text{io}})\rfloor\}.
\]

Quick loop cap for \(k\) (if denominators >0):
\[
k \le \left\lfloor\frac{L_{\max}/c_{\text{time}}-w_1}{w_2}\right\rfloor,\qquad
k \le \left\lfloor\frac{M_{\max}-M_0-s_0-s_1}{s_2}\right\rfloor.
\]

## 3) Selector (integer, monotone, \(O(k)\))
1. Compute \(k_{\min}\), a conservative \(k_{\max}\).
2. For \(k=k_{\min}\ldots k_{\max}\): compute \(n_{\text{cap}}(k)\). If \(\ge1\), choose \(n^\star\) (e.g., \(n_{\text{cap}}\)).
3. Score candidates by objective:
   - **Max precision**: maximize \(k\); break ties by \(n\).
   - **Max τ**: evaluate \(\tau(k,n)\) and take argmax.
4. Emit a **pre-run certificate** with \(\hat T,\hat M,\hat\varepsilon\).

## 4) Receipts (what to read)
Single line:  
`n=… k=…  L≤… E≤… M≤… ε≤…  T^=… M^=… ε^=…  T=… E=… τ=…  dT=… dE=…  ok=…`  
Goal: small residues (e.g., \(dT\le\) T\_TOL). If `ok=false`, check the prior `[select/debug]` line (c_time, IO_FRAC, β, W, S).

## 5) Linear calibrator (compute-dominant window)
Fit \(T(n)=a n + b\) over a window \([n_{\min},n_{\max}]\). Store slope, intercept, and residual metric
\(\eta=\max_i |T_i-(a n_i+b)|/T_i\).  
Stamp: `passport.coefficients.linear={a,b,eta,n_min,n_max}`.  
Use \(T^\wedge=\max(a n+b, T_{\text{io}})\) when IO is negligible.

## 6) Energy scaffold (Linux RAPL)
Measure Joules with RAPL, fit \(c_{\text{energy}}=E/W\), add gate \(\hat E\le E_{\max}\) and residue \(dE\). Start warn-only; enforce once stable.

## 7) Practical IO knobs
Estimate β by streaming a large buffer: \(\hat\beta=X/T\).  
Estimate IO share:
\[
\mathrm{IO\_FRAC}\approx
\begin{cases}
0,& T_{\text{comp}}=c_{\text{time}}W\ \ge T\\
\min\!\left(1,\ \dfrac{\beta T}{S}\right),& T_{\text{comp}}<T
\end{cases}
\]
Keep IO\_FRAC=0 until β is trusted.
