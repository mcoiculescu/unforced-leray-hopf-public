import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# `PartIII-a:T16/1/1/4` : `FDerivApplyShiftBound` (generic calculus lemma)

Source `the November 2 reference manuscript` lines 3604-3610.
For `f : ℝ³ → ℝ` of class `C^∞`, the map `y' ↦ ∂_v f(y' - w)` (as a `ℂ`-valued map) has
`n`-th derivative bounded by `‖D^{n+1} f(y - w)‖ ‖v‖`.  Proof: translation invariance of
`iteratedFDeriv` (`iteratedFDeriv_comp_sub`), the identity `g = ofRealCLM ∘ (apply v) ∘ fderiv f`
with `iteratedFDeriv_comp_left`, and the norm identity `norm_iteratedFDeriv_fderiv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Pointwise bound at the point `x` for the map `g x' = ((∂_v f)(x') : ℂ)` (no shift). -/
lemma l4_bound_at (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (v x : Space) :
    ‖iteratedFDeriv ℝ n (fun x' => ((fderiv ℝ f x' v : ℝ) : ℂ)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f x‖ * ‖v‖ := by
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (by simp)
  have hn : ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ (n + 1) f x‖ :=
    norm_iteratedFDeriv_fderiv
  have h2 : iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x
      = (ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fderiv ℝ f) x) :=
    (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left (f := fderiv ℝ f)
      hd.contDiffAt le_rfl
  have h3 : ContDiff ℝ n (fun y => fderiv ℝ f y v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp hd
  have h4 : iteratedFDeriv ℝ n (fun y => ((fderiv ℝ f y v : ℝ) : ℂ)) x
      = Complex.ofRealCLM.compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left (f := fun y => fderiv ℝ f y v)
      h3.contDiffAt le_rfl
  have hA : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun φ => by
      rw [ContinuousLinearMap.apply_apply, mul_comm]
      exact φ.le_opNorm v)
  have hB : ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ = 1 := Complex.ofRealCLM_norm
  have c1 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le Complex.ofRealCLM
    (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x)
  have c2 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
    (ContinuousLinearMap.apply ℝ ℝ v) (iteratedFDeriv ℝ n (fderiv ℝ f) x)
  rw [h4]
  calc ‖Complex.ofRealCLM.compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x)‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x‖ := c1
    _ = ‖(ContinuousLinearMap.apply ℝ ℝ v).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fderiv ℝ f) x)‖ := by rw [hB, one_mul, h2]
    _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ v‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ := c2
    _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) f x‖ * ‖v‖ := by rw [hn, mul_comm]

/-- **`PartIII-a:T16/1/1/4`**: the shifted directional derivative `y' ↦ ∂_v f(y' - w)` has
`n`-th derivative bounded by `‖D^{n+1} f(y - w)‖ ‖v‖`. -/
theorem fDerivApplyShiftBound : UnforcedLeray.Short.IIIa.FDerivApplyShiftBound := by
  intro f hf n v w y
  have key := l4_bound_at f hf n v (y - w)
  have e := iteratedFDeriv_comp_sub (𝕜 := ℝ)
    (f := fun x' : Space => ((fderiv ℝ f x' v : ℝ) : ℂ)) n w y
  have e' : (fun y' : Space => ((fderiv ℝ f (y' - w) v : ℝ) : ℂ)) =
      (fun z : Space => ((fderiv ℝ f (z - w) v : ℝ) : ℂ)) := rfl
  rw [e']
  rw [e]
  exact key

end UnforcedLeray.Short.IIIa
