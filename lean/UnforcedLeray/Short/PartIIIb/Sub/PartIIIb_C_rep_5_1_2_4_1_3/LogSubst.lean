import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/10`: the substitution `λ = e^{(σ-τ)/2}`

Source `the November 2 reference manuscript` 3611-3621 (`σ = τ + 2 log λ`).
The map `φ σ = exp((σ-τ)/2)` sends `Iio τ` bijectively onto `Ioo 0 1` with derivative
`φ' σ = exp((σ-τ)/2)/2 > 0`; the one-dimensional change of variables gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- The substitution `λ = e^{(σ-τ)/2}`, `dλ = (λ/2) dσ`, of `(0,1)` by `(-∞, τ)`. -/
theorem logSubst : LogSubst := by
  intro τ f _hf
  -- the map `σ ↦ e^{(σ-τ)/2}` and its derivative
  have hderiv : ∀ x ∈ Iio τ,
      HasDerivWithinAt (fun σ : ℝ => Real.exp ((σ - τ) / 2))
        (Real.exp ((x - τ) / 2) * (1 / 2)) (Iio τ) x := by
    intro x _
    have h1 : HasDerivAt (fun σ : ℝ => (σ - τ) / 2) (1 / 2) x := by
      simpa using ((hasDerivAt_id x).sub_const τ).div_const 2
    exact h1.exp.hasDerivWithinAt
  -- injectivity on `Iio τ`
  have hinj : InjOn (fun σ : ℝ => Real.exp ((σ - τ) / 2)) (Iio τ) := by
    intro a _ b _ hab
    have h := Real.exp_eq_exp.1 hab
    linarith
  -- the image is `Ioo 0 1`
  have himage : (fun σ : ℝ => Real.exp ((σ - τ) / 2)) '' Iio τ = Ioo 0 1 := by
    ext l
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      have hσ' : σ < τ := hσ
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
    · rintro ⟨hl0, hl1⟩
      refine ⟨τ + 2 * Real.log l, ?_, ?_⟩
      · have := Real.log_neg hl0 hl1
        show τ + 2 * Real.log l < τ
        linarith
      · show Real.exp ((τ + 2 * Real.log l - τ) / 2) = l
        rw [show (τ + 2 * Real.log l - τ) / 2 = Real.log l by ring]
        exact Real.exp_log hl0
  rw [← himage,
    MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio hderiv hinj f]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Iio (fun σ _ => ?_)
  have hpos : 0 < Real.exp ((σ - τ) / 2) * (1 / 2) := by positivity
  rw [abs_of_pos hpos, mul_one_div]

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
