# Factor model transformations, out-of-sample risk evaluation, fundamental factor models & covariance estimation (Ledoit-Wolf, DCC, STVU, Newey-West/Cohen HAC, Cai clustering, causal log-MAD winsorization, multi-region linking, currency rebasing), and statistical factor models (PCA/SVD, subspace iteration, PPCA, RMT shrinkage, Bai-Ng, Procrustes alignment) with 41 proved structural symmetry, strict causality, no-lookahead, parallel-equivalence, and dimension-guard laws. Source: https://github.com/robinmarin/bend-quant/tree/main/risk
import ./subspace_svd.bend as SSVD
import ./cov.bend as C
import ./risk.bend as R
import ./io.bend as I
import ./LAWS.bend as Laws
import ./PROOF.bend as Proof
