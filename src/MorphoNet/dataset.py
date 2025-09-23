import os, math, glob
import torch
from torch.utils.data import Dataset
from PIL import Image
import numpy as np
class LS3DWTSV(Dataset):
  def __init__(self, index_tsv, root_images, out_res=128, sigma=1.5):
    self.rows=[r.strip().split("\t") for r in open(index_tsv,"r",encoding="utf-8").read().splitlines()][1:]
    self.root=root_images; self.res=out_res; self.sigma=sigma
  def __len__(self): return len(self.rows)
  def _read_landmarks(self, p):
    pts=[]
    for line in open(p,"r",encoding="utf-8"):
      s=line.strip().split("\t");
      if len(s)>=3 and s[0].isdigit(): pts.append((float(s[1]), float(s[2])))
    return np.array(pts, dtype=np.float32)
  def _heatmaps(self, pts):
    H=W=self.res; K=pts.shape[0]; HMs=np.zeros((K,H,W), dtype=np.float32);
    for k,(x,y) in enumerate(pts):
      xi=int(max(0,min(W-1,round(x)))); yi=int(max(0,min(H-1,round(y))))
      # small Gaussian stamp
      for dy in range(-3,4):
        for dx in range(-3,4):
          xx=xi+dx; yy=yi+dy
          if 0<=xx<W and 0<=yy<H:
            HMs[k,yy,xx]=max(HMs[k,yy,xx], math.exp(-(dx*dx+dy*dy)/(2*self.sigma*self.sigma)))
    return HMs
  def __getitem__(self,i):
    rel,_,w,h,_,_,_,_, lmp = self.rows[i]
    img = Image.open(os.path.join(self.root, rel)).convert("RGB").resize((self.res,self.res))
    pts = self._read_landmarks(lmp)
    # naive scale into res assuming landmarks already in pixel coords of this res
    x = torch.from_numpy(np.asarray(img)).permute(2,0,1).float()/255.0
    y = torch.from_numpy(self._heatmaps(pts))
    return x, y
