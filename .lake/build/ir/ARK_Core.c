// Lean compiler output
// Module: ARK_Core
// Imports: public import Init public import ARK_Core.WittenOperator public import ARK_Core.SpectralGap public import ARK_Core.Impossibility public import ARK_Core.Witness
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_WittenOperator(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_SpectralGap(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Impossibility(uint8_t builtin);
lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Witness(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_WittenOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_SpectralGap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Impossibility(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ARK_x2dP_x2dneq_x2dNP_ARK__Core_Witness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
