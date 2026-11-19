/*
 Moth Motion Controller v1 — Arduino UNO/Nano (Servo.h)
 Actual servo control for a physical companion. No network or AI required.

 Wiring: head signal D9, ear signal D10, both servo grounds connected to
 controller GND AND separate regulated servo power supply GND. Servo power
 goes to a separate current-rated ~5 V supply, NEVER to an Arduino I/O pin.

 USB protocol (115200 baud, one JSON command per line):
 {"v":1,"cmd":"move","axis":"head","deg":20}
 {"v":1,"cmd":"move","axis":"ear","deg":-15}
 {"v":1,"cmd":"stop"}
 Degree offsets are relative to physical neutral (90 deg). All commands
 are clamped to conservative bounds and smoothly stepped. STOP and the
 5-second serial watchdog return to the neutral pose. Disconnect servos and
 test with no mechanical linkage before mounting inside a companion.

 This is OPEN LOOP: no feedback encoder/position certificate. Mechanical
 slack and motor drift are not eliminated by this firmware. FactoryCal and
 a sensed feedback loop are separate, necessary hardware milestones.
*/
#include <Servo.h>
Servo headServo, earServo;
const byte HEAD_PIN=9, EAR_PIN=10;
const int HEAD_NEUTRAL=90, EAR_NEUTRAL=90;
const int HEAD_MIN=60, HEAD_MAX=120;
const int EAR_MIN=55, EAR_MAX=125;
int headCurrent=90, earCurrent=90, headTarget=90, earTarget=90;
char lineBuf[128]; size_t lineSize=0;
unsigned long lastMove=0,lastStep=0;

void report(const char* kind,const char* name){
 Serial.print("{\"kind\":\"");Serial.print(kind);Serial.print("\",\"message\":\"");Serial.print(name);Serial.println("\"}");
}
void neutral(){headTarget=HEAD_NEUTRAL;earTarget=EAR_NEUTRAL;}
int numberAfter(const char* src,const char* key,int fallback){
 const char* p=strstr(src,key);if(!p)return fallback;p=strchr(p,':');if(!p)return fallback;p++;
 while(*p==' ')p++;return atoi(p);
}
bool has(const char* src,const char* fragment){return strstr(src,fragment)!=NULL;}
void parse(const char* s){
 if(!has(s,"\"v\"")||numberAfter(s,"\"v\"",-1)!=1){report("error","protocol version must be 1");return;}
 if(has(s,"\"stop\"")){neutral();lastMove=millis();report("ack","stop to neutral");return;}
 if(!has(s,"\"move\"")){report("error","unknown command");return;}
 int delta=numberAfter(s,"\"deg\"",9999);if(delta==9999){report("error","missing degrees");return;}
 if(has(s,"\"head\"")){headTarget=constrain(HEAD_NEUTRAL+delta,HEAD_MIN,HEAD_MAX);lastMove=millis();report("ack","head moving");return;}
 if(has(s,"\"ear\"")){earTarget=constrain(EAR_NEUTRAL+delta,EAR_MIN,EAR_MAX);lastMove=millis();report("ack","ear moving");return;}
 report("error","unknown axis");
}
void setup(){
 headServo.attach(HEAD_PIN);earServo.attach(EAR_PIN);
 headServo.write(headCurrent);earServo.write(earCurrent);
 Serial.begin(115200);lastMove=millis();lastStep=millis();
 report("hello","moth-motion/v1 ready - open loop");
}
void loop(){
 while(Serial.available()){
  char c=char(Serial.read());
  if(c=='\n'){lineBuf[lineSize]='\0';if(lineSize>0)parse(lineBuf);lineSize=0;}
  else if(c!='\r'){
   if(lineSize+1>=sizeof(lineBuf)){lineSize=0;report("error","command too long");}
   else lineBuf[lineSize++]=c;
  }
 }
 unsigned long now=millis();
 if(now-lastMove>5000UL){if(headTarget!=HEAD_NEUTRAL||earTarget!=EAR_NEUTRAL){neutral();report("watchdog","neutral fallback");}}
 if(now-lastStep>=24UL){lastStep=now;
  if(headCurrent<headTarget)headCurrent+=min(2,headTarget-headCurrent);
  if(headCurrent>headTarget)headCurrent-=min(2,headCurrent-headTarget);
  if(earCurrent<earTarget)earCurrent+=min(2,earTarget-earCurrent);
  if(earCurrent>earTarget)earCurrent-=min(2,earCurrent-earTarget);
  headServo.write(headCurrent);earServo.write(earCurrent);
 }
}
