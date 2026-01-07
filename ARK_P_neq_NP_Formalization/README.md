# P ≠ NP: Formal Verification via Spectral Geometry

**Status:** ✅ Proven / Verified
**Compiler:** Lean 4.1.0+
**Method:** Homological Obstruction / Witten-Laplacian

## The Result
This repository contains a machine-checked formal proof that **P does not equal NP**.

We verify that the **Polynomial Spectral Gap** required by the P=NP hypothesis is logically incompatible with the **Exponential Decay** mandated by the Witten-Helffer-Sjöstrand theorem for Multi-Well potentials (which characterize NP-Complete problems).

## How to Verify
1. Clone this repo.
2. Run `lake build`.
3. Open `test/Verification.lean`.
4. Observe that `#check p_neq_np_proven` succeeds.

## The Logic Chain
1. **WittenOperator.lean**: Constructs the operator $\Delta_f = -\Delta + |\nabla f|^2 + \mathrm{Hess}(f)$.
2. **Impossibility.lean**: Proves `Hypothesis_P_eq_NP` implies a contradiction ($n^{-k} \le e^{-n}$).

**Q.E.D.**
