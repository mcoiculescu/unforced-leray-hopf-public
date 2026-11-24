import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_2
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# `phaseIBPScalar` (task `PartIII-b:C/near/pins/3/3/2/4`)

Source `the November 2 reference manuscript`
1666, 1675-1677, 2666-2668, 2683.  Slice integration by parts on `ℝ³` for compactly supported smooth
functions, plus the axis `{hRad = 0}` being a null set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem axis_null : volume {y : Space | ¬ 0 < hRad y} = 0 := by
  let s : Submodule ℝ Space :=
    LinearMap.ker (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap ⊓
      LinearMap.ker (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hs : s ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ∈ s := by rw [h]; trivial
    simp [s] at this
  have hsub : {y : Space | ¬ 0 < hRad y} ⊆ (s : Set Space) := by
    intro y hy
    have h0 : hRad y = 0 := le_antisymm (not_lt.mp hy) (Real.sqrt_nonneg _)
    unfold hRad at h0
    rw [Real.sqrt_eq_zero (by positivity)] at h0
    have a : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have b : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    simp [s, a, b]
  exact measure_mono_null hsub (Measure.addHaar_submodule volume s hs)

private theorem slice_fderiv {G : ℝ × Space → ℂ} (hG : ContDiff ℝ ∞ G) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun y : Space => G (τ, y)) y v = fderiv ℝ G (τ, y) (0, v) := by
  have h1 : HasFDerivAt (fun y : Space => ((τ, y) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have h2 := (hG.differentiable (by simp) (τ, y)).hasFDerivAt.comp y h1
  change fderiv ℝ (G ∘ Prod.mk τ) y v = _
  rw [h2.fderiv]
  simp

private theorem integrable_of_vanish {k : Space → ℂ} (hk : Continuous k) (R : ℝ)
    (h : ∀ y, R < ‖y‖ → k y = 0) : Integrable k volume := by
  apply hk.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
  intro y hy
  exact h y (by simpa using hy)

private theorem slice_ibp {G H : ℝ × Space → ℂ} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {R : ℝ} (RG : ∀ τ y, R < ‖y‖ → G (τ, y) = 0) (RH : ∀ τ y, R < ‖y‖ → H (τ, y) = 0)
    (τ : ℝ) (v : Space) :
    ∫ y, H (τ, y) * fderiv ℝ G (τ, y) (0, v) = -∫ y, fderiv ℝ H (τ, y) (0, v) * G (τ, y) := by
  have hι : ContDiff ℝ ∞ (fun y : Space => ((τ, y) : ℝ × Space)) :=
    contDiff_const.prodMk contDiff_id
  have hGs : ContDiff ℝ ∞ (fun y : Space => G (τ, y)) := hG.comp hι
  have hHs : ContDiff ℝ ∞ (fun y : Space => H (τ, y)) := hH.comp hι
  have cG' : Continuous fun y : Space => fderiv ℝ G (τ, y) (0, v) :=
    ((hG.continuous_fderiv (by simp)).comp (hι.continuous)).clm_apply continuous_const
  have cH' : Continuous fun y : Space => fderiv ℝ H (τ, y) (0, v) :=
    ((hH.continuous_fderiv (by simp)).comp (hι.continuous)).clm_apply continuous_const
  have e1 : ∀ y, fderiv ℝ (fun y : Space => G (τ, y)) y v = fderiv ℝ G (τ, y) (0, v) :=
    fun y => slice_fderiv hG τ y v
  have e2 : ∀ y, fderiv ℝ (fun y : Space => H (τ, y)) y v = fderiv ℝ H (τ, y) (0, v) :=
    fun y => slice_fderiv hH τ y v
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y : Space => H (τ, y)) (g := fun y : Space => G (τ, y)) (v := v)
    (by simp only [e2]; exact integrable_of_vanish (cH'.mul hGs.continuous) R
          (fun y hy => by simp [RG τ y hy]))
    (by simp only [e1]; exact integrable_of_vanish (hHs.continuous.mul cG') R
          (fun y hy => by simp [RH τ y hy]))
    (integrable_of_vanish (hHs.continuous.mul hGs.continuous) R
          (fun y hy => by simp [RH τ y hy]))
    (fun x _ => (hHs.differentiable (by simp)) x)
    (fun x _ => (hGs.differentiable (by simp)) x)
  simpa only [e1, e2] using this

private theorem comp_fderiv {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (j : Fin 3)
    (x : ℝ × Space) (w : ℝ × Space) :
    fderiv ℝ (fun x => Φ x j) x w = fderiv ℝ Φ x w j := by
  have h := (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ |>.hasFDerivAt.comp x
    (hΦ.differentiable (by simp) x).hasFDerivAt
  have h' : fderiv ℝ (fun x => Φ x j) x =
      ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ Φ x) :=
    h.fderiv
  rw [h']; rfl

theorem phaseIBPScalar : PhaseIBPScalar := by
  intro P ψ hψ Φ hΦ F hF
  obtain ⟨Rψ, hRψ⟩ := hψ.bounded_support
  obtain ⟨RΦ, hRΦ⟩ := hΦ.bounded_support
  set R := max Rψ RΦ with hR
  have RG : ∀ τ y, R < ‖y‖ → ((ψ (τ, y) : ℝ) : ℂ) = 0 := fun τ y hy =>
    hRψ τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  have RH : ∀ j : Fin 3, ∀ τ y, R < ‖y‖ → Φ (τ, y) j = 0 := fun j τ y hy => by
    have := hRΦ τ y (lt_of_le_of_lt (le_max_right _ _) hy)
    simp [this]
  have hHj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x => Φ x j) := fun j =>
    ((EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hΦ.smooth
  have key : ∀ τ : ℝ, ∫ y, dotL (Φ (τ, y)) (F (τ, y)) =
      -∫ y, ((ψ (τ, y) : ℝ) : ℂ) * ∑ j : Fin 3, dy j Φ (τ, y) j := by
    intro τ
    have hae : ∀ᵐ y : Space ∂volume, 0 < hRad y := by
      rw [ae_iff]; exact axis_null
    have h1 : ∫ y, dotL (Φ (τ, y)) (F (τ, y)) =
        ∫ y, ∑ j : Fin 3, Φ (τ, y) j * dy j (fun x : ℝ × Space => ((ψ x : ℝ) : ℂ)) (τ, y) := by
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      rw [dotL_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [hF τ y hy j]
    rw [h1]
    have cψ' : ∀ j : Fin 3, Continuous fun y : Space =>
        fderiv ℝ (fun x : ℝ × Space => ((ψ x : ℝ) : ℂ)) (τ, y) (0, coordinateVector j) :=
      fun j => ((hψ.smooth.continuous_fderiv (by simp)).comp
        (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun y : Space => ((τ, y) : ℝ × Space))).continuous).clm_apply continuous_const
    have cH : ∀ j : Fin 3, Continuous fun y : Space => Φ (τ, y) j := fun j =>
      (hHj j).continuous.comp (continuous_const.prodMk continuous_id)
    have cH' : ∀ j : Fin 3, Continuous fun y : Space =>
        fderiv ℝ (fun x => Φ x j) (τ, y) (0, coordinateVector j) := fun j =>
      ((hHj j).continuous_fderiv (by simp)|>.comp
        (continuous_const.prodMk continuous_id)).clm_apply continuous_const
    have cψ : Continuous fun y : Space => ((ψ (τ, y) : ℝ) : ℂ) :=
      hψ.smooth.continuous.comp (continuous_const.prodMk continuous_id)
    have hI1 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun y : Space => Φ (τ, y) j *
        dy j (fun x : ℝ × Space => ((ψ x : ℝ) : ℂ)) (τ, y)) volume := fun j _ =>
      integrable_of_vanish ((cH j).mul (cψ' j)) R (fun y hy => by simp [RH j τ y hy])
    rw [integral_finsetSum _ hI1]
    have h2 : ∫ y, ((ψ (τ, y) : ℝ) : ℂ) * ∑ j : Fin 3, dy j Φ (τ, y) j =
        ∑ j : Fin 3, ∫ y, fderiv ℝ (fun x => Φ x j) (τ, y) (0, coordinateVector j) *
          ((ψ (τ, y) : ℝ) : ℂ) := by
      have hI2 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun y : Space =>
          fderiv ℝ (fun x => Φ x j) (τ, y) (0, coordinateVector j) *
          ((ψ (τ, y) : ℝ) : ℂ)) volume := fun j _ =>
        integrable_of_vanish ((cH' j).mul cψ) R (fun y hy => by simp [RG τ y hy])
      rw [← integral_finsetSum _ hI2]
      congr 1; funext y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [mul_comm, comp_fderiv hΦ.smooth]; rfl
    rw [h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact slice_ibp (G := fun x : ℝ × Space => ((ψ x : ℝ) : ℂ)) (H := fun x => Φ x j)
      hψ.smooth (hHj j) RG (RH j) τ (coordinateVector j)
  unfold pairF scalarPair phaseInt
  simp only [key, integral_neg, smul_neg]

end UnforcedLeray.Short.PartIIIb.NearInst
