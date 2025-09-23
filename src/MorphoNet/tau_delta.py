import os, json, math, torch, numpy as np
def soft_argmax_2d(hm):
  N,C,H,W = hm.shape; hm = hm.reshape(N,C,-1); p = torch.softmax(hm, dim=-1);
  ys, xs = torch.meshgrid(torch.arange(H), torch.arange(W), indexing="ij")
  coords = torch.stack([xs.flatten(), ys.flatten()], dim=-1).float()
  out = torch.einsum("nck,kg->ncg", p, coords)  # (N,C,2)
  return out
def nme_bb(pred, gt, bb_sqrt):
  d = torch.linalg.vector_norm(pred-gt, dim=-1).mean()
  return (d / float(bb_sqrt)).item()
def residual_heatmaps(pred_hm, gt_pts, H, W, sigma=1.5):
  K = gt_pts.shape[0]; gt = torch.zeros((K,H,W), dtype=torch.float32)
  for k,(x,y) in enumerate(gt_pts):
    xi=int(round(max(0,min(W-1,x)))); yi=int(round(max(0,min(H-1,y))))
    for dy in range(-3,4):
      for dx in range(-3,4):
        xx=xi+dx; yy=yi+dy
        if 0<=xx<W and 0<=yy<H:
          gt[k,yy,xx]=max(gt[k,yy,xx], math.exp(-(dx*dx+dy*dy)/(2*sigma*sigma)))
  return pred_hm.squeeze(0)-gt
def tau_delta_record(pred_hm, gt_pts, bb_sqrt):
  N,C,H,W = pred_hm.shape; coords = soft_argmax_2d(pred_hm)[0]  # (C,2)
  gt = torch.from_numpy(gt_pts).float()
  score = nme_bb(coords, gt, bb_sqrt)
  res = residual_heatmaps(pred_hm, gt_pts, H, W)
  energy = float(torch.abs(res).sum().item())
  return {"nme_bb": score, "residual_energy": energy}
