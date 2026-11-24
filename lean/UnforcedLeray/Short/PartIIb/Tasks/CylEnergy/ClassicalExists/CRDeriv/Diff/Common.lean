import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv.ParamCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatGrad
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds
import UnforcedLeray.Lib.BudgetsGronwall.SingularVolterra

/-!
# Shared helpers for `PartII-b:T22/1/10/1/2` (`dDiff`) and `PartII-b:T22/1/10/1/3` (`dCont`)

Measurability of the slices of the parametric integrands, the pointwise size bounds for the
heat semigroup and its derivative (from `heatWBounds`), the affine-kernel integrability, and the
operator-norm bound for a plane functional `α • fst + β • snd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace DiffC

/-- A function continuous on `[s, τ)` is strongly measurable on `(s, τ]` (the point `τ` is null). -/
lemma aesm_Ioc_of_contOn {f : ℝ → ℝ} {s τ : ℝ} (hf : ContinuousOn f (Ico s τ)) :
    AEStronglyMeasurable f (volume.restrict (Ioc s τ)) := by
  have h1 : ContinuousOn f (Ioo s τ) := hf.mono Ioo_subset_Ico_self
  have h2 : AEStronglyMeasurable f (volume.restrict (Ioo s τ)) :=
    h1.aestronglyMeasurable measurableSet_Ioo
  have h3 : volume.restrict (Ioo s τ) = volume.restrict (Ioc s τ) :=
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc' (by simp))
  rw [← h3]
  exact h2

/-- Slices `t ↦ Φ t x` of a parametric integrand continuous on `[s, τ) × Pl`. -/
lemma aesm_slice (Φ : ℝ → Pl → ℝ) {s τ : ℝ}
    (hΦ : ContinuousOn (fun z : ℝ × Pl => Φ z.1 z.2) (Ico s τ ×ˢ univ)) (x : Pl) :
    AEStronglyMeasurable (fun t => Φ t x) (volume.restrict (Ioc s τ)) := by
  apply aesm_Ioc_of_contOn
  have hmap : ContinuousOn (fun t : ℝ => (t, x)) (Ico s τ) :=
    continuousOn_id.prodMk continuousOn_const
  exact hΦ.comp hmap (fun t ht => ⟨ht, mem_univ _⟩)

/-- Each integrand `g t` of a `DHyp` family is continuous on the plane. -/
lemma cont_slice {s T : ℝ} {g : ℝ → Pl → ℝ}
    (hgc : ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ)) {t : ℝ}
    (ht : t ∈ Icc s T) : Continuous (g t) :=
  continuousOn_univ.1 (hgc.comp (continuousOn_const.prodMk continuousOn_id)
    (fun x _ => ⟨ht, mem_univ _⟩))

/-- The endpoint `τ` is `volume`-null, so almost every `t` satisfies `t ≠ τ`. -/
lemma ae_ne_point (τ : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ τ := by
  simp [ae_iff]

/-- Operator norm of `α • fst + β • snd` on `ℝ × ℝ`. -/
lemma norm_clm_le (α β : ℝ) :
    ‖α • ContinuousLinearMap.fst ℝ ℝ ℝ + β • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |α| + |β| := by
  have h1 : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have h2 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  calc ‖α • ContinuousLinearMap.fst ℝ ℝ ℝ + β • ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ ‖α • ContinuousLinearMap.fst ℝ ℝ ℝ‖ + ‖β • ContinuousLinearMap.snd ℝ ℝ ℝ‖ :=
        norm_add_le _ _
    _ = |α| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ + |β| * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |α| * 1 + |β| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg α))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg β))
    _ = |α| + |β| := by ring

/-- Strong measurability of `t ↦ α t • fst + β t • snd`. -/
lemma aesm_clm {μ : Measure ℝ} {α β : ℝ → ℝ} (hα : AEStronglyMeasurable α μ)
    (hβ : AEStronglyMeasurable β μ) :
    AEStronglyMeasurable (fun t => α t • ContinuousLinearMap.fst ℝ ℝ ℝ +
      β t • ContinuousLinearMap.snd ℝ ℝ ℝ) μ :=
  (hα.smul aestronglyMeasurable_const).add (hβ.smul aestronglyMeasurable_const)

/-- Uniform size of the semigroup: `|e^{ν(τ-t)Δ} g(x)| ≤ 2 e^{ν(T-s)} M` for `s ≤ t ≤ τ ≤ T`. -/
lemma heatSG_bound_aux {ν s T τ t : ℝ} (hν : 0 < ν) (hτT : τ ≤ T) (hst : s ≤ t) (htτ : t ≤ τ)
    {g : Pl → ℝ} {b M0 : ℝ} (hbM : b ≤ M0) (hb0 : 0 ≤ b) (hg : WB b g) (x : Pl) :
    |heatSG (ν * (τ - t)) g x| ≤ 2 * Real.exp (ν * (T - s)) * M0 := by
  have ha : 0 ≤ ν * (τ - t) := mul_nonneg hν.le (by linarith)
  have h := (heatWBounds b g hg).1 (ν * (τ - t)) ha x
  have hc := Real.one_le_cosh x.2
  have hexp : Real.exp (ν * (τ - t)) ≤ Real.exp (ν * (T - s)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hν.le)
  have h1 : 2 * Real.exp (ν * (τ - t)) ≤ 2 * Real.exp (ν * (T - s)) := by linarith
  have hB : 2 * Real.exp (ν * (τ - t)) * b ≤ 2 * Real.exp (ν * (T - s)) * M0 :=
    mul_le_mul h1 hbM hb0 (by positivity)
  have h0 : 0 ≤ |heatSG (ν * (τ - t)) g x| := abs_nonneg _
  linarith [le_mul_of_one_le_right h0 hc]

/-- Uniform size of the derivative kernel for `s ≤ t < τ ≤ T`. -/
lemma heatSGd_bound_aux {ν s T τ t : ℝ} (hν : 0 < ν) (hτT : τ ≤ T) (hst : s ≤ t) (htτ : t < τ)
    {g : Pl → ℝ} {b M0 : ℝ} (hbM : b ≤ M0) (hb0 : 0 ≤ b) (hg : WB b g) (i : Fin 2) (x : Pl) :
    |heatSGd i (ν * (τ - t)) g x| ≤
      2 * Real.exp (ν * (T - s)) * (1 + (ν * (τ - t)) ^ (-(1 / 2 : ℝ))) * M0 := by
  have ha : 0 < ν * (τ - t) := mul_pos hν (by linarith)
  have h := (heatWBounds b g hg).2 (ν * (τ - t)) ha i x
  have hc := Real.one_le_cosh x.2
  have hp : 0 ≤ (ν * (τ - t)) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  have hexp : Real.exp (ν * (τ - t)) ≤ Real.exp (ν * (T - s)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hν.le)
  have h1 : 2 * Real.exp (ν * (τ - t)) * (1 + (ν * (τ - t)) ^ (-(1 / 2 : ℝ))) ≤
      2 * Real.exp (ν * (T - s)) * (1 + (ν * (τ - t)) ^ (-(1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hB : 2 * Real.exp (ν * (τ - t)) * (1 + (ν * (τ - t)) ^ (-(1 / 2 : ℝ))) * b ≤
      2 * Real.exp (ν * (T - s)) * (1 + (ν * (τ - t)) ^ (-(1 / 2 : ℝ))) * M0 :=
    mul_le_mul h1 hbM hb0 (mul_nonneg (by positivity) (by linarith))
  have h0 : 0 ≤ |heatSGd i (ν * (τ - t)) g x| := abs_nonneg _
  linarith [le_mul_of_one_le_right h0 hc]

/-- The derivative bound with the kernel `(τ - t)^{-1/2}` made explicit. -/
lemma heatSGd_bound_int {ν s T τ t : ℝ} (hν : 0 < ν) (hτT : τ ≤ T) (hst : s ≤ t) (htτ : t < τ)
    {g : Pl → ℝ} {b M0 : ℝ} (hbM : b ≤ M0) (hb0 : 0 ≤ b) (hg : WB b g) (i : Fin 2) (x : Pl) :
    |heatSGd i (ν * (τ - t)) g x| ≤
      2 * Real.exp (ν * (T - s)) * M0 + 2 * Real.exp (ν * (T - s)) * M0 *
        ν ^ (-(1 / 2 : ℝ)) * (τ - t) ^ (-(1 / 2 : ℝ)) := by
  have h := heatSGd_bound_aux hν hτT hst htτ hbM hb0 hg i x
  have hp : (ν * (τ - t)) ^ (-(1 / 2 : ℝ)) = ν ^ (-(1 / 2 : ℝ)) * (τ - t) ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow hν.le (by linarith)
  rw [hp] at h
  linarith

/-- An affine function of the kernel `(τ - t)^{-1/2}` is interval integrable. -/
lemma affine_kernel_intInt (A C τ s : ℝ) :
    IntervalIntegrable (fun t : ℝ => A + C * (τ - t) ^ (-(1 / 2 : ℝ))) volume s τ :=
  intervalIntegrable_const.add ((UnforcedLeray.Gronwall.intervalIntegrable_kernel τ s τ).const_mul C)

/-- A real function on `(s, τ]` bounded by a constant is interval integrable. -/
lemma intInt_of_bdd {F : ℝ → ℝ} {s τ K : ℝ} (hsτ : s ≤ τ)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioc s τ)))
    (hb : ∀ t ∈ Ioc s τ, |F t| ≤ K) : IntervalIntegrable F volume s τ := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => K) intervalIntegrable_const ?_ ?_
  · rw [uIoc_of_le hsτ]
    exact hF
  · rw [uIoc_of_le hsτ]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => by
      show ‖F t‖ ≤ K
      rw [Real.norm_eq_abs]
      exact hb t ht)

end DiffC

end UnforcedLeray.Short.IIb.CylPDE
