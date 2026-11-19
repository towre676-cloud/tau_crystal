"""Layout smoke test without browser network. Requires: pip install playwright; Chromium installed."""
import asyncio, base64, os, pathlib, re
from playwright.async_api import async_playwright
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = pathlib.Path(os.environ.get('MOTH_QA_DIR', str(ROOT / 'build/qa')))
OUTPUT.mkdir(parents=True, exist_ok=True)
MOCK = '''<script>
const mockState={version:'0.1.1',companion_name:'Moth',user_name:'',mood:'curious',energy:82,bond:16,
 memories:[{id:'m1',text:'We love pine forests.',created:new Date().toISOString()}],tasks:[],
 turns:[{role:'user',text:'Hello Moth!',at:new Date().toISOString()},
 {role:'assistant',text:'Hello. Shall we continue our project?',at:new Date().toISOString()}],captures:[],
 settings:{model:'llama3.2',voice:false,ollama:false,low_motion:false}};
window.fetch=async function(path,opt={}){
 let data={ok:true},body={};try{body=JSON.parse(opt.body||'{}')}catch{}
 if(path==='/api/state')data=mockState;
 if(path==='/api/memory'&&opt.method==='POST'){mockState.memories.push({id:'m2',text:body.text,created:new Date().toISOString()});data={id:'m2',text:body.text}}
 if(path==='/api/chat'){mockState.turns.push({role:'user',text:body.message},{role:'assistant',text:'I remember that we love pine forests.'});data={reply:'I remember that we love pine forests.',engine:'offline'}}
 if(path==='/api/pet'){data={mood:'content',energy:81,bond:17}}
 return{ok:true,json:async()=>data};
};
</script>'''
async def main():
 async with async_playwright() as p:
  browser=await p.chromium.launch(executable_path=os.environ.get('MOTH_CHROMIUM','/usr/bin/chromium'),args=['--no-sandbox'])
  for width,height,label in [(1440,900,'desktop'),(390,844,'mobile')]:
   page=await browser.new_page(viewport={'width':width,'height':height})
   issues=[];page.on('pageerror',lambda err:issues.append(str(err)))
   site=(ROOT/'site/index.html').read_text()
   for img in (ROOT/'site/assets').glob('*.png'):
    site=site.replace('assets/'+img.name,'data:image/png;base64,'+base64.b64encode(img.read_bytes()).decode())
   await page.set_content(site,wait_until='load')
   site_overflow=await page.evaluate('document.documentElement.scrollWidth - innerWidth')
   await page.screenshot(path=str(OUTPUT/f'site-{label}.png'),full_page=True)
   markup=(ROOT/'ui/index.html').read_text()
   css=(ROOT/'ui/app.css').read_text();js=(ROOT/'ui/app.js').read_text()
   markup=re.sub(r'<link[^>]+href="/app.css"[^>]*>',f'<style>{css}</style>',markup)
   markup=markup.replace('<script src="/app.js" defer></script>',MOCK+f'<script>{js}</script>')
   await page.set_content(markup,wait_until='load')
   await page.wait_for_timeout(150)
   app_overflow=await page.evaluate('document.documentElement.scrollWidth - innerWidth')
   await page.screenshot(path=str(OUTPUT/f'app-{label}.png'),full_page=True)
   assert site_overflow==0 and app_overflow==0,(label,site_overflow,app_overflow)
   assert not issues,(label,issues)
   await page.locator('[data-view="memory"]').first.click()
   await page.locator('#memory-input').fill('We love the woods')
   await page.locator('#memory-form button[type=submit]').click()
   await page.wait_for_timeout(100)
   assert await page.get_by_text('We love the woods').count()==1
   await page.locator('[data-view="home"]').first.click()
   await page.locator('#chat-input').fill('What do you remember?')
   await page.locator('#send-button').click()
   await page.wait_for_timeout(100)
   assert await page.get_by_text('I remember that we love pine forests.').count()==1
   assert not issues,(label,issues)
   print(f'PASS {label}: site & app responsive, no page exceptions, memory and chat controls')
   await page.close()
  await browser.close()
if __name__=='__main__':asyncio.run(main())
