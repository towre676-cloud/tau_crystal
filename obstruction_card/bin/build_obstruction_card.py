import json, csv, sys, math, cmath, numpy as np
from pathlib import Path
def read_csv_matrix(p):
    with open(p,'r',newline='') as f:
        rdr=csv.reader(f)
        rows=[[float(x) for x in row] for row in rdr if row]
    return np.array(rows,dtype=float)
def psd_inv_sqrt(H, eps=1e-18):
    # symmetric PSD inverse square root via eigendecomposition
    w, V = np.linalg.eigh(0.5*(H+H.T))
    w = np.clip(w, eps, None)
    Dm12 = np.diag(1.0/np.sqrt(w))
    return (V @ Dm12) @ V.T
def principal_angle_from_neutral(NA, NB, k=2):
    # NA, NB are orthonormal basis matrices for neutral subspaces
    # return the smallest principal angle defined by the two least nonzero singular values
    C = NA.T @ NB
    s = np.linalg.svd(C,compute_uv=False)
    s = np.sort(s)
    if s.size<2: return float('nan')
    s1, s2 = s[-2], s[-1]
    s1 = np.clip(s1,1e-18,1.0); s2 = np.clip(s2,1e-18,1.0)
    return math.atan2(math.sqrt(max(0.0,1.0-s1*s1)), s2)
def polar_unitary(X):
    U, s, Vt = np.linalg.svd(X, full_matrices=False)
    return U @ Vt
def save_csv(p, M):
    with open(p,'w',newline='') as f:
        w=csv.writer(f); [w.writerow([repr(float(x)) for x in row]) for row in np.atleast_2d(M)]
def main():
    in_dir  = Path('obstruction_card/in')
    out_dir = Path('obstruction_card/out'); out_dir.mkdir(parents=True, exist_ok=True)
    A = read_csv_matrix(in_dir/'A.csv')
    B = read_csv_matrix(in_dir/'B.csv')
    if A.shape[0]!=B.shape[1] or A.shape[1]!=B.shape[0]:
        raise SystemExit(f'shape mismatch A{A.shape} B{B.shape}: expected square obstruction window')
    H0 = A @ B
    H1 = B @ A
    H0m12 = psd_inv_sqrt(H0)
    H1m12 = psd_inv_sqrt(H1)
    M = H0m12 @ A @ H1m12
    # singular spectrum encodes masses (ratios)
    U, s, Vt = np.linalg.svd(M, full_matrices=False)
    detM = np.linalg.det(U) * np.prod(s) * np.linalg.det(Vt)
    # phase of det M is the strong-theta proxy on the finite window
    theta = math.atan2(detM.imag if isinstance(detM, complex) else 0.0, detM.real if isinstance(detM, complex) else detM)
    # block splits for CKM/PMNS: declare index cuts in obstruction_card/in/splits.json
    splits_path = in_dir/'splits.json'
    CKM=None; PMNS=None
    if splits_path.exists():
        sp = json.loads(splits_path.read_text())
        # each entry gives row/col slices for up, down, lepton, neutrino sectors inside A,B
        ru, cu = slice(*sp['up']['rows']), slice(*sp['up']['cols'])
        rd, cd = slice(*sp['down']['rows']), slice(*sp['down']['cols'])
        rl, cl = slice(*sp['lepton']['rows']), slice(*sp['lepton']['cols'])
        rn, cn = slice(*sp['neutrino']['rows']), slice(*sp['neutrino']['cols'])
        Au, Bu = A[ru,cu], B[cu,ru]
        Ad, Bd = A[rd,cd], B[cd,rd]
        Al, Bl = A[rl,cl], B[cl,rl]
        An, Bn = A[rn,cn], B[cn,rn]
        Hu0, Hu1 = Au@Bu, Bu@Au; Hd0, Hd1 = Ad@Bd, Bd@Ad
        Hl0, Hl1 = Al@Bl, Bl@Al; Hn0, Hn1 = An@Bn, Bn@An
        Mu = psd_inv_sqrt(Hu0) @ Au @ psd_inv_sqrt(Hu1)
        Md = psd_inv_sqrt(Hd0) @ Ad @ psd_inv_sqrt(Hd1)
        Ml = psd_inv_sqrt(Hl0) @ Al @ psd_inv_sqrt(Hl1)
        Mn = psd_inv_sqrt(Hn0) @ An @ psd_inv_sqrt(Hn1)
        Uu = polar_unitary(Mu); Ud = polar_unitary(Md)
        Ul = polar_unitary(Ml); Un = polar_unitary(Mn)
        CKM  = Uu.T.conj() @ Ud
        PMNS = Ul.T.conj() @ Un
    # electroweak principal angle: provide orthonormal bases NA, NB in obstruction_card/in/neutral_{A,B}.csv
    thetaW = float('nan')
    NA_p = in_dir/'neutral_A.csv'; NB_p = in_dir/'neutral_B.csv'
    if NA_p.exists() and NB_p.exists():
        NA = read_csv_matrix(NA_p); NB = read_csv_matrix(NB_p)
        thetaW = principal_angle_from_neutral(NA,NB)
    # outputs
    np.save(out_dir/'M.npy', M)
    save_csv(out_dir/'singular_values.csv', s.reshape(1,-1))
    save_csv(out_dir/'theta_detM.csv', np.array([[theta]]))
    save_csv(out_dir/'thetaW.csv', np.array([[thetaW]]))
    save_csv(out_dir/'U_left.csv', U)
    save_csv(out_dir/'V_right.csv', Vt.T)
    if CKM is not None: save_csv(out_dir/'CKM.csv', CKM)
    if PMNS is not None: save_csv(out_dir/'PMNS.csv', PMNS)
if __name__=='__main__': main()
