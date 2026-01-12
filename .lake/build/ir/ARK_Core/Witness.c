// Lean compiler output
// Module: ARK_Core.Witness
// Imports: public import Init public import ARK_Core.Impossibility public import Mathlib.Analysis.InnerProductSpace.PiL2 public import Mathlib.Analysis.Calculus.ContDiff.Basic public import Mathlib.Tactic.NormNum public import Mathlib.Tactic.IntervalCases public import Mathlib.Tactic.Linarith public import Mathlib.Analysis.Complex.ExponentialBounds public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
lean_object* l_Rat_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__2;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__3;
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00lambda_spec__0(lean_object*);
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_lambda___closed__0;
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__0;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_f__val(lean_object*);
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0_spec__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_lambda;
lean_object* lp_mathlib_CauSeq_const___at___00CauSeq_Completion_ofRat___at___00Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8__spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0___boxed(lean_object*, lean_object*);
static lean_object* lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__1;
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2;
x_2 = lean_alloc_closure((void*)(lp_mathlib_CauSeq_const___at___00CauSeq_Completion_ofRat___at___00Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8__spec__3_spec__3___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00lambda_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2;
x_2 = lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_lambda___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4;
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(5u);
x_4 = l_Rat_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_lambda() {
_start:
{
lean_object* x_1; lean_object* x_2;
x_1 = lp_ARK_x2dP_x2dneq_x2dNP_lambda___closed__0;
x_2 = lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00lambda_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2;
x_2 = lp_ARK_x2dP_x2dneq_x2dNP_NNRat_cast___at___00NNRat_cast___at___00NNRat_cast___at___00lambda_spec__0_spec__0_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_object* x_5;
lean_dec(x_2);
x_5 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_inc(x_2);
x_8 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_7, x_2);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
return x_9;
}
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3;
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2;
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_2 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3;
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3;
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_f__val(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28;
x_2 = lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__0;
lean_inc(x_1);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unsigned_to_nat(2u);
lean_inc(x_3);
x_5 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_4, x_3);
x_6 = lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__1;
x_7 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_4, x_7);
x_9 = lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__2;
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
lean_inc(x_10);
x_11 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_4, x_10);
x_12 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_6);
x_13 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_4, x_12);
x_14 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
x_15 = lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__3;
x_16 = lean_apply_1(x_1, x_15);
lean_inc(x_16);
x_17 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_4, x_16);
x_18 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_6);
x_19 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_4, x_18);
x_20 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_19);
x_21 = lp_ARK_x2dP_x2dneq_x2dNP_lambda;
lean_inc(x_10);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_10);
lean_inc(x_16);
x_23 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_16);
x_24 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_25, 0, x_16);
lean_closure_set(x_25, 1, x_3);
x_26 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_27, 0, x_21);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_28, 0, x_20);
lean_closure_set(x_28, 1, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3;
x_3 = lp_ARK_x2dP_x2dneq_x2dNP_npowRec___at___00f__val_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Impossibility(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_PiL2(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_ContDiff_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_NormNum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_IntervalCases(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_Linarith(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Witness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Impossibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_PiL2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_ContDiff_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_NormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_IntervalCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_ExponentialBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_ARK_x2dP_x2dneq_x2dNP_lambda___closed__0 = _init_lp_ARK_x2dP_x2dneq_x2dNP_lambda___closed__0();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_lambda___closed__0);
lp_ARK_x2dP_x2dneq_x2dNP_lambda = _init_lp_ARK_x2dP_x2dneq_x2dNP_lambda();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_lambda);
lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__0 = _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__0();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__0);
lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__1 = _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__1();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__1);
lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__2 = _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__2();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__2);
lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__3 = _init_lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__3();
lean_mark_persistent(lp_ARK_x2dP_x2dneq_x2dNP_f__val___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
