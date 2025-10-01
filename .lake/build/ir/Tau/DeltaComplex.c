// Lean compiler output
// Module: Tau.DeltaComplex
// Imports: Init Tau.LeafGroup
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Tau_unitOn(lean_object*, lean_object*);
static lean_object* l_Tau_unitOn___closed__1;
static lean_object* l_Tau_verifyObstruction___closed__1;
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_applyMorphism(lean_object*, lean_object*, lean_object*);
lean_object* l_Tau_leafGroupAdd(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_computeDelta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Tau_applyMorphism_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_tauDrift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Tau_verifyObstruction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Tau_verifyObstruction___closed__0;
lean_object* l_Tau_leafGroupNeg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_verifyObstruction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Tau_unitOn___closed__2;
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Tau_leafGroupL1Norm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Tau_applyMorphism_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Tau_unitOn___closed__0;
static lean_object* l_Tau_verifyObstruction___closed__2;
LEAN_EXPORT lean_object* l_Tau_applyMorphism___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Tau_unitOn___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Tau_unitOn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Tau_unitOn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Tau_unitOn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Tau_unitOn___closed__0;
x_4 = l_List_elem___redArg(x_3, x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Tau_unitOn___closed__1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Tau_unitOn___closed__2;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Tau_applyMorphism_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_6);
x_9 = lean_apply_1(x_8, x_6);
x_10 = lean_string_dec_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_6);
x_5 = x_7;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
x_12 = lean_apply_1(x_3, x_6);
x_13 = lean_int_add(x_4, x_12);
lean_dec(x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Tau_applyMorphism(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Tau_unitOn___closed__1;
x_6 = l_List_foldl___at___Tau_applyMorphism_spec__0(x_1, x_3, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Tau_applyMorphism_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___at___Tau_applyMorphism_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Tau_applyMorphism___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Tau_applyMorphism(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Tau_computeDelta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Tau_unitOn), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_alloc_closure((void*)(l_Tau_applyMorphism___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_Tau_unitOn), 2, 1);
lean_closure_set(x_7, 0, x_4);
x_8 = lean_alloc_closure((void*)(l_Tau_leafGroupNeg), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Tau_leafGroupAdd(x_6, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Tau_tauDrift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Tau_applyMorphism___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_int_sub(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
static lean_object* _init_l_Tau_verifyObstruction___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FAILED: |dTau| > lambda * L1", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Tau_verifyObstruction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("VERIFIED: |dTau| <= lambda * L1", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Tau_verifyObstruction___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("VERIFIED: DELTA=0, tau conserved", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Tau_verifyObstruction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_3);
x_7 = lean_alloc_closure((void*)(l_Tau_computeDelta), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = l_Tau_leafGroupL1Norm(x_7, x_6);
x_9 = l_Tau_tauDrift(x_3, x_2, x_4, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_nat_abs(x_9);
lean_dec(x_9);
x_24 = lean_nat_mul(x_1, x_8);
lean_dec(x_8);
x_25 = lean_nat_dec_le(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_12 = x_25;
goto block_22;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_8);
x_26 = l_Tau_unitOn___closed__1;
x_27 = lean_int_dec_eq(x_9, x_26);
lean_dec(x_9);
x_12 = x_27;
goto block_22;
}
block_22:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Tau_verifyObstruction___closed__0;
x_14 = lean_box(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
if (x_11 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Tau_verifyObstruction___closed__1;
x_17 = lean_box(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Tau_verifyObstruction___closed__2;
x_20 = lean_box(x_11);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Tau_verifyObstruction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Tau_verifyObstruction(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Tau_LeafGroup(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tau_DeltaComplex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Tau_LeafGroup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Tau_unitOn___closed__0 = _init_l_Tau_unitOn___closed__0();
lean_mark_persistent(l_Tau_unitOn___closed__0);
l_Tau_unitOn___closed__1 = _init_l_Tau_unitOn___closed__1();
lean_mark_persistent(l_Tau_unitOn___closed__1);
l_Tau_unitOn___closed__2 = _init_l_Tau_unitOn___closed__2();
lean_mark_persistent(l_Tau_unitOn___closed__2);
l_Tau_verifyObstruction___closed__0 = _init_l_Tau_verifyObstruction___closed__0();
lean_mark_persistent(l_Tau_verifyObstruction___closed__0);
l_Tau_verifyObstruction___closed__1 = _init_l_Tau_verifyObstruction___closed__1();
lean_mark_persistent(l_Tau_verifyObstruction___closed__1);
l_Tau_verifyObstruction___closed__2 = _init_l_Tau_verifyObstruction___closed__2();
lean_mark_persistent(l_Tau_verifyObstruction___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
