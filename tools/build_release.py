#!/usr/bin/env python3
"""Rebuild tested Windows/Pi executables and complete offline-download site."""
from __future__ import annotations
import hashlib,json,os,subprocess,shutil,sys,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=Path(os.environ.get('MOTH_RELEASE_DIR',str(ROOT.parent)))
SITE=ROOT/'site'; BUILDS=ROOT/'build'
VERSION='0.1.1'
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def go_binary(dest,pkg,goos,goarch,gui=False):
 env=dict(os.environ,GOOS=goos,GOARCH=goarch,CGO_ENABLED='0')
 flags='-s -w -H=windowsgui' if gui else '-s -w'
 subprocess.run(['go','build','-trimpath','-ldflags='+flags,'-o',str(dest),pkg],cwd=ROOT,env=env,check=True)
def zipwrite(path,mapping):
 with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=8,strict_timestamps=False) as z:
  for dest,src in sorted(mapping.items()):
   z.write(src,arcname=dest)
 with zipfile.ZipFile(path) as z:
  bad=z.testzip()
  if bad:raise RuntimeError(f'Bad archive member: {bad}')
 print(path.name,path.stat().st_size,sha(path))
def files_under(base):
 return [p for p in base.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
def main():
 OUT.mkdir(parents=True,exist_ok=True);BUILDS.mkdir(exist_ok=True);(SITE/'downloads').mkdir(exist_ok=True)
 if os.environ.get('MOTH_SKIP_QA')!='1':
  subprocess.run(['go','test','-race','./...'],cwd=ROOT,check=True)
  subprocess.run(['go','vet','./...'],cwd=ROOT,check=True)
  subprocess.run(['node','--check','ui/app.js'],cwd=ROOT,check=True)
  subprocess.run(['bash','tests/pi_capture_fixture.sh'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
  print('QA core, vet, JS, and Pi fixture passed')
 go_binary(BUILDS/'MothCompanion.exe','./cmd/moth','windows','amd64',gui=True)
 go_binary(BUILDS/'moth-witness-linux-arm64','./cmd/witness','linux','arm64')
 shutil.copy2(BUILDS/'MothCompanion.exe',OUT/'MothCompanion.exe')
 shutil.copy2(BUILDS/'moth-witness-linux-arm64',OUT/'moth-witness-linux-arm64')
 source={}
 for folder in ['cmd','internal','ui','hardware','docs','tools','tests']:
  for p in files_under(ROOT/folder):
   if folder=='tests' and p.name=='Moth-Windows-QA.json':continue
   if folder=='tools' and p.name=='build_release.py':pass
   source['MothCompanion-Source/'+p.relative_to(ROOT).as_posix()]=p
 for file in ['README.md','go.mod']:
  source['MothCompanion-Source/'+file]=ROOT/file
 for p in files_under(SITE/'assets'):
  source['MothCompanion-Source/site/'+p.relative_to(SITE).as_posix()]=p
 source['MothCompanion-Source/site/index.html']=SITE/'index.html'
 zipwrite(OUT/'MothCompanion-Source.zip',source)
 window={
 'MothCompanion.exe':BUILDS/'MothCompanion.exe',
 'README.md':ROOT/'README.md',
 'docs/RESURRECTION_LEDGER.md':ROOT/'docs/RESURRECTION_LEDGER.md',
 'docs/HARDWARE_AND_WINDOWS_QA.md':ROOT/'docs/HARDWARE_AND_WINDOWS_QA.md',
 'hardware/pi/capture_and_witness.sh':ROOT/'hardware/pi/capture_and_witness.sh',
 'hardware/firmware/MothMotionController.ino':ROOT/'hardware/firmware/MothMotionController.ino',
 'tests/windows_selftest.ps1':ROOT/'tests/windows_selftest.ps1',
 }
 zipwrite(OUT/'MothCompanion-Windows.zip',window)
 # Site downloads are real bytes, not placeholder buttons.
 downloads={
  'MothCompanion.exe':OUT/'MothCompanion.exe',
  'MothCompanion-Windows.zip':OUT/'MothCompanion-Windows.zip',
  'MothCompanion-Source.zip':OUT/'MothCompanion-Source.zip',
  'moth-witness-linux-arm64':OUT/'moth-witness-linux-arm64',
  'capture_and_witness.sh':ROOT/'hardware/pi/capture_and_witness.sh',
  'RESURRECTION_LEDGER.md':ROOT/'docs/RESURRECTION_LEDGER.md',
  'HARDWARE_AND_WINDOWS_QA.md':ROOT/'docs/HARDWARE_AND_WINDOWS_QA.md',
 }
 for k,p in downloads.items():shutil.copy2(p,SITE/'downloads'/k)
 sums=''.join(f'{sha(SITE/"downloads"/k)}  {k}\n' for k in sorted(downloads))
 (SITE/'downloads/SHA256SUMS.txt').write_text(sums)
 (OUT/'MothCompanion-SHA256SUMS.txt').write_text(sums)
 manifest={
  'product':'Moth Companion', 'version':VERSION, 'windows_arch':'amd64',
  'developer_signature':'unsigned prototype; review source and checksums',
  'artifacts':{k:{'sha256':sha(SITE/'downloads'/k),'bytes':(SITE/'downloads'/k).stat().st_size} for k in sorted(downloads)},
  'verification':{'go_race':True,'go_vet':True,'pi_fixture':True,'physical_pi':False,'physical_servo':False,'windows11_native':False,'public_sites_deployed':False},
 }
 (SITE/'downloads/release-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 # Fail the package if any local Site link is broken.
 from html.parser import HTMLParser
 class Links(HTMLParser):
  def __init__(self):super().__init__();self.links=[]
  def handle_starttag(self,tag,attrs):
   for k,v in attrs:
    if k in ('src','href') and v and not v.startswith(('#','http:','https:','data:','mailto:')):self.links.append(v.split('#',1)[0])
 l=Links();l.feed((SITE/'index.html').read_text())
 missing=[v for v in l.links if not (SITE/v).is_file()]
 if missing:raise RuntimeError('Broken Site assets or download links: '+repr(missing))
 zipwrite(OUT/'MothCompanion-Site.zip',{p.relative_to(SITE).as_posix():p for p in files_under(SITE)})
 shutil.copy2(SITE/'index.html',OUT/'MothCompanion-Landing.html')
 print('RELEASE READY',VERSION)
if __name__=='__main__':main()
