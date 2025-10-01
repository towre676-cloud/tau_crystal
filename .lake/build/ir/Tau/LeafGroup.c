// Lean compiler output
// Module: Tau.LeafGroup
// Imports: Init
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
LEAN_EXPORT lean_object* l_Tau_instNegLeafGroup;
static lean_object* l_Tau_leafGroupZero___closed__0;
LEAN_EXPORT lean_object* l_Tau_leafGroupAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Tau_leafGroupIsZero(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT uint8_t l_Tau_leafGroupIsZero___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_leafGroupNeg(lean_object*, lean_object*);
static lean_object* l_Tau_instNegLeafGroup___closed__0;
static lean_object* l_Tau_instAddLeafGroup___closed__0;
LEAN_EXPORT lean_object* l_List_foldl___at___Tau_leafGroupL1Norm_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_leafGroupIsZero___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Tau_instAddLeafGroup;
LEAN_EXPORT lean_object* l_Tau_instZeroLeafGroup;
LEAN_EXPORT lean_object* l_Tau_leafGroupIsZero___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_leafGroupL1Norm(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Tau_leafGroupZero(lean_object*);
LEAN_EXPORT lean_object* l_Tau_leafGroupZero___boxed(lean_object*);
static lean_object* _init_l_Tau_leafGroupZero___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupZero(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Tau_leafGroupZero___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupZero___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Tau_leafGroupZero(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = lean_int_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupNeg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Tau_leafGroupL1Norm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_nat_abs(x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupL1Norm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___at___Tau_leafGroupL1Norm_spec__0(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Tau_leafGroupIsZero___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = l_Tau_leafGroupZero___closed__0;
x_5 = lean_int_dec_eq(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Tau_leafGroupIsZero(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Tau_leafGroupIsZero___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_all___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupIsZero___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Tau_leafGroupIsZero___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Tau_leafGroupIsZero___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Tau_leafGroupIsZero(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Tau_instZeroLeafGroup() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Tau_leafGroupZero___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Tau_instAddLeafGroup___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Tau_leafGroupAdd), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Tau_instAddLeafGroup() {
_start:
{
lean_object* x_1; 
x_1 = l_Tau_instAddLeafGroup___closed__0;
return x_1;
}
}
static lean_object* _init_l_Tau_instNegLeafGroup___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Tau_leafGroupNeg), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Tau_instNegLeafGroup() {
_start:
{
lean_object* x_1; 
x_1 = l_Tau_instNegLeafGroup___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Tau_LeafGroup(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Tau_leafGroupZero___closed__0 = _init_l_Tau_leafGroupZero___closed__0();
lean_mark_persistent(l_Tau_leafGroupZero___closed__0);
l_Tau_instZeroLeafGroup = _init_l_Tau_instZeroLeafGroup();
lean_mark_persistent(l_Tau_instZeroLeafGroup);
l_Tau_instAddLeafGroup___closed__0 = _init_l_Tau_instAddLeafGroup___closed__0();
lean_mark_persistent(l_Tau_instAddLeafGroup___closed__0);
l_Tau_instAddLeafGroup = _init_l_Tau_instAddLeafGroup();
lean_mark_persistent(l_Tau_instAddLeafGroup);
l_Tau_instNegLeafGroup___closed__0 = _init_l_Tau_instNegLeafGroup___closed__0();
lean_mark_persistent(l_Tau_instNegLeafGroup___closed__0);
l_Tau_instNegLeafGroup = _init_l_Tau_instNegLeafGroup();
lean_mark_persistent(l_Tau_instNegLeafGroup);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
