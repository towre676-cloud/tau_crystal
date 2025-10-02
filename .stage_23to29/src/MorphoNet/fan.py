import math
import torch
import torch.nn as nn
import torch.nn.functional as F
class HPM(nn.Module):
    def __init__(self, c):
        super().__init__(); self.b1=nn.Conv2d(c,c,3,1,1); self.b2=nn.Conv2d(c,c,3,1,2,dilation=2); self.b3=nn.Conv2d(c,c,3,1,3,dilation=3); self.bn=nn.BatchNorm2d(c)
    def forward(self,x): return F.relu(self.bn(self.b1(x)+self.b2(x)+self.b3(x)))
class HourGlass(nn.Module):
    def __init__(self,c,depth=2):
        super().__init__(); self.depth=depth; self.down=nn.ModuleList(); self.up=nn.ModuleList();
        for _ in range(depth): self.down.append(nn.Sequential(nn.MaxPool2d(2), HPM(c))); self.up.append(HPM(c))
        self.low=HPM(c)
    def forward(self,x):
        feats=[]; y=x
        for i in range(self.depth):
            feats.append(self.up[i](y)); y=self.down[i](y)
        y=self.low(y)
        for i in reversed(range(self.depth)):
            y=F.interpolate(y, scale_factor=2, mode="bilinear", align_corners=False); y=y+feats[i]
        return y
class TinyFANBase(nn.Module):
    def __init__(self, out_ch=68):
        super().__init__(); c=64
        self.stem=nn.Sequential(nn.Conv2d(3,c,7,2,3), nn.BatchNorm2d(c), nn.ReLU(), nn.Conv2d(c,c,3,1,1), nn.BatchNorm2d(c), nn.ReLU())
        self.hg1=HourGlass(c,2); self.hg2=HourGlass(c,2)
        self.head=nn.Conv2d(c,out_ch,1)
    def forward(self,x): y=self.stem(x); y=self.hg1(y); y=self.hg2(y); return self.head(y)
class TinyFAN2D(TinyFANBase): pass
class TinyFAN3D(TinyFANBase): pass
