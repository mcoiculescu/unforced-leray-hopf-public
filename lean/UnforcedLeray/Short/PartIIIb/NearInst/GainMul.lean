import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Multiplication by a bounded measurable function on `Lp`

Generic tool for the gain multiplication `G T = g T` of `near/equation-comparison.tex`
(source lines 3875-3880): for `φ` measurable with `|φ| ≤ C`, `f ↦ φ f` is a continuous linear map
`Lp E 2 μ →L[ℝ] Lp E 2 μ` of norm `≤ C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem memLp_mulBdd {φ : α → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ a, |φ a| ≤ C)
    (f : Lp E 2 μ) : MemLp (φ • (f : α → E)) 2 μ := by
  have hφm : MemLp φ ∞ μ := memLp_top_of_bound hφ.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hC a)
  exact MemLp.smul (r := 2) (Lp.memLp f) hφm

/-- Multiplication by the bounded measurable function `φ`, as a continuous linear map on `Lp`. -/
def mulBdd (φ : α → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ a, |φ a| ≤ C) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mulBdd hφ hC f).toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add f g] with a ha
        change φ a • ((f + g : Lp E 2 μ) : α → E) a = φ a • (f : α → E) a + φ a • (g : α → E) a
        rw [ha, Pi.add_apply, smul_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul c f] with a ha
        change φ a • ((c • f : Lp E 2 μ) : α → E) a = c • (φ a • (f : α → E) a)
        rw [ha, Pi.smul_apply, smul_comm] }
    (max C 0) (by
      intro f
      have hCn : ∀ a, ‖φ a‖ ≤ max C 0 := fun a => by
        rw [Real.norm_eq_abs]; exact (hC a).trans (le_max_left _ _)
      rw [Lp.norm_def, Lp.norm_def]
      show (eLpNorm (((memLp_mulBdd hφ hC f).toLp _ : Lp E 2 μ) : α → E) 2 μ).toReal ≤ _
      have h1 : eLpNorm (((memLp_mulBdd hφ hC f).toLp _ : Lp E 2 μ) : α → E) 2 μ
          = eLpNorm (φ • (f : α → E)) 2 μ :=
        eLpNorm_congr_ae (MemLp.coeFn_toLp _)
      rw [h1]
      have h2 := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (μ := μ) 2
        (Lp.aestronglyMeasurable f) φ
      have h3 : eLpNorm φ ∞ μ ≤ ENNReal.ofReal (max C 0) :=
        eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hCn) |>.trans_eq (by simp)
      have h4 : eLpNorm (φ • (f : α → E)) 2 μ ≤ ENNReal.ofReal (max C 0) * eLpNorm f 2 μ :=
        h2.trans (by gcongr)
      have hfin : eLpNorm f 2 μ ≠ ⊤ := (Lp.memLp f).2.ne
      calc (eLpNorm (φ • (f : α → E)) 2 μ).toReal
          ≤ (ENNReal.ofReal (max C 0) * eLpNorm f 2 μ).toReal :=
            ENNReal.toReal_mono (by finiteness) h4
        _ = max C 0 * (eLpNorm f 2 μ).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right _ _)])

theorem mulBdd_apply_ae (φ : α → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ a, |φ a| ≤ C)
    (f : Lp E 2 μ) : (mulBdd φ hφ C hC f : α → E) =ᵐ[μ] φ • (f : α → E) :=
  MemLp.coeFn_toLp (memLp_mulBdd hφ hC f)

/-- Multiplication by `φ` followed by multiplication by `ψ` with `φψ = 1` is the identity. -/
theorem mulBdd_mulBdd (φ ψ : α → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) (C C' : ℝ)
    (hC : ∀ a, |φ a| ≤ C) (hC' : ∀ a, |ψ a| ≤ C') (h : ∀ a, ψ a * φ a = 1) (f : Lp E 2 μ) :
    mulBdd ψ hψ C' hC' (mulBdd φ hφ C hC f) = f := by
  apply Lp.ext
  have h1 := mulBdd_apply_ae ψ hψ C' hC' (mulBdd φ hφ C hC f)
  have h2 := mulBdd_apply_ae φ hφ C hC f
  filter_upwards [h1, h2] with a ha hb
  rw [ha]
  change ψ a • (mulBdd φ hφ C hC f : α → E) a = _
  rw [hb]
  change ψ a • (φ a • (f : α → E) a) = _
  rw [smul_smul, h a, one_smul]

/-- Multiplication by `φ` with a bounded inverse `ψ`, as a continuous linear equivalence. -/
def mulBddEquiv (φ ψ : α → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) (C C' : ℝ)
    (hC : ∀ a, |φ a| ≤ C) (hC' : ∀ a, |ψ a| ≤ C') (h : ∀ a, ψ a * φ a = 1) :
    Lp E 2 μ ≃L[ℝ] Lp E 2 μ :=
  ContinuousLinearEquiv.equivOfInverse (mulBdd φ hφ C hC) (mulBdd ψ hψ C' hC')
    (mulBdd_mulBdd φ ψ hφ hψ C C' hC hC' h)
    (mulBdd_mulBdd ψ φ hψ hφ C' C hC' hC (fun a => by rw [mul_comm]; exact h a))

theorem mulBddEquiv_apply (φ ψ : α → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) (C C' : ℝ)
    (hC : ∀ a, |φ a| ≤ C) (hC' : ∀ a, |ψ a| ≤ C') (h : ∀ a, ψ a * φ a = 1) (f : Lp E 2 μ) :
    mulBddEquiv φ ψ hφ hψ C C' hC hC' h f = mulBdd φ hφ C hC f := rfl

end UnforcedLeray.Short.PartIIIb.NearInst
