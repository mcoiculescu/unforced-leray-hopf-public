import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2

/-!
# Calculus helpers for `InletWeak`

Slice derivatives, `dy` of continuous linear images, jet bounds from slice jets, and the weak
`y_j`-derivative of a smooth field (classical integration by parts in `y` for a phase test with
bounded `y`-support; the periodic `τ` integral is untouched).
Source `the November 2 reference manuscript`
lines 2385-2387, 2525-2531.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (phaseInt)
open scoped ContDiff

local notation "𝕊" => UnforcedLeray.Space

section Calc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem slice_fderiv {f : ℝ × 𝕊 → F} (hf : Differentiable ℝ f) (t : ℝ) (y v : 𝕊) :
    fderiv ℝ (fun y' => f (t, y')) y v = fderiv ℝ f (t, y) (0, v) := by
  have h1 : HasFDerivAt (fun y' : 𝕊 => ((t, y') : ℝ × 𝕊))
      ((0 : 𝕊 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ 𝕊)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h2 := (hf (t, y)).hasFDerivAt.comp y h1
  show fderiv ℝ (f ∘ Prod.mk t) y v = _
  rw [h2.fderiv]
  simp

theorem contDiff_dy' {f : ℝ × 𝕊 → F} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dy_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (c : F →L[ℝ] G)
    {f : ℝ × 𝕊 → F} (hf : Differentiable ℝ f) (j : Fin 3) :
    dy j (fun x => c (f x)) = fun x => c (dy j f x) := by
  funext x
  have h := c.hasFDerivAt.comp x (hf x).hasFDerivAt
  simp only [dy]
  rw [show (fun x => c (f x)) = c ∘ f from rfl, h.fderiv]
  rfl

theorem dy_add' {f g : ℝ × 𝕊 → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin 3) :
    dy j (fun x => f x + g x) = fun x => dy j f x + dy j g x := by
  funext x
  simp only [dy]
  have h : fderiv ℝ (fun x => f x + g x) x = fderiv ℝ f x + fderiv ℝ g x :=
    ((hf x).hasFDerivAt.add (hg x).hasFDerivAt).fderiv
  rw [h]
  rfl

theorem dy_smul' {f : ℝ × 𝕊 → F} (hf : Differentiable ℝ f) (c : ℝ) (j : Fin 3) :
    dy j (fun x => c • f x) = fun x => c • dy j f x := by
  funext x
  simp only [dy]
  have h : fderiv ℝ (fun x => c • f x) x = c • fderiv ℝ f x :=
    ((hf x).hasFDerivAt.const_smul c).fderiv
  rw [h]
  rfl

theorem norm_cv (j : Fin 3) : ‖UnforcedLeray.coordinateVector j‖ = 1 := by
  simp [UnforcedLeray.coordinateVector]

/-- Jet bounds of a smooth field from bounds on its slice jets of orders `0, 1, 2`. -/
theorem bdd_of_slice {G : ℝ × 𝕊 → F} (hG : ContDiff ℝ ∞ G) (C : ℝ)
    (hC : ∀ l ≤ 2, ∀ τ y, ‖iteratedFDeriv ℝ l (fun y' => G (τ, y')) y‖ ≤ C) (j k : Fin 3) :
    (∀ x, ‖G x‖ ≤ C) ∧ (∀ x, ‖dy j G x‖ ≤ C) ∧ ∀ x, ‖dy j (dy k G) x‖ ≤ C := by
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hs : ∀ τ : ℝ, ContDiff ℝ ∞ (fun y' : 𝕊 => G (τ, y')) := fun τ =>
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hsd : ∀ τ : ℝ, Differentiable ℝ (fun y' : 𝕊 => G (τ, y')) := fun τ =>
    (hs τ).differentiable (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨τ, y⟩
    have := hC 0 (by norm_num) τ y
    rwa [norm_iteratedFDeriv_zero] at this
  · rintro ⟨τ, y⟩
    have h1 := hC 1 (by norm_num) τ y
    rw [norm_iteratedFDeriv_one] at h1
    have : dy j G (τ, y) = fderiv ℝ (fun y' => G (τ, y')) y (UnforcedLeray.coordinateVector j) :=
      (slice_fderiv hGd τ y _).symm
    rw [this]
    calc _ ≤ ‖fderiv ℝ (fun y' => G (τ, y')) y‖ * ‖UnforcedLeray.coordinateVector j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by rw [norm_cv]; linarith
  · rintro ⟨τ, y⟩
    have h2 := hC 2 (by norm_num) τ y
    have hdk : Differentiable ℝ (dy k G) := (contDiff_dy' hG k).differentiable (by simp)
    have e1 : dy j (dy k G) (τ, y) =
        fderiv ℝ (fun y' => dy k G (τ, y')) y (UnforcedLeray.coordinateVector j) :=
      (slice_fderiv hdk τ y _).symm
    have e2 : (fun y' => dy k G (τ, y')) =
        fun y' => fderiv ℝ (fun y'' => G (τ, y'')) y' (UnforcedLeray.coordinateVector k) := by
      funext y'
      exact (slice_fderiv hGd τ y' _).symm
    have hd2 : Differentiable ℝ (fderiv ℝ (fun y' : 𝕊 => G (τ, y'))) :=
      ((hs τ).fderiv_right (m := ∞) (by simp)).differentiable (by simp)
    have e3 : fderiv ℝ (fun y' => fderiv ℝ (fun y'' => G (τ, y'')) y'
        (UnforcedLeray.coordinateVector k)) y (UnforcedLeray.coordinateVector j) =
        fderiv ℝ (fderiv ℝ (fun y'' => G (τ, y''))) y (UnforcedLeray.coordinateVector j)
          (UnforcedLeray.coordinateVector k) := by
      have hx : HasFDerivAt (fun y' => fderiv ℝ (fun y'' => G (τ, y'')) y'
          (UnforcedLeray.coordinateVector k))
          ((fderiv ℝ (fderiv ℝ (fun y'' => G (τ, y''))) y).flip
            (UnforcedLeray.coordinateVector k)) y := by
        simpa using (hd2 y).hasFDerivAt.clm_apply
          (hasFDerivAt_const (UnforcedLeray.coordinateVector k) y)
      rw [hx.fderiv]
      rfl
    rw [e1, e2, e3]
    have h3 := iteratedFDeriv_two_apply (𝕜 := ℝ) (fun y'' => G (τ, y'')) y
      ![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector k]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h3
    rw [← h3]
    calc _ ≤ ‖iteratedFDeriv ℝ 2 (fun y'' => G (τ, y'')) y‖ *
          ∏ i, ‖(![UnforcedLeray.coordinateVector j, UnforcedLeray.coordinateVector k] :
            Fin 2 → 𝕊) i‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C := by
        simp [Fin.prod_univ_two, norm_cv]
        linarith

/-- Products of a continuous function with one vanishing for `‖y‖ > R` are integrable. -/
theorem integrable_mul_of_vanish {G H : 𝕊 → ℂ} (hG : Continuous G) (hH : Continuous H) (R : ℝ)
    (hv : ∀ y, R < ‖y‖ → H y = 0) :
    Integrable (fun y => G y * H y) ∧ Integrable (fun y => H y * G y) := by
  have hc : HasCompactSupport H :=
    HasCompactSupport.intro (isCompact_closedBall (0 : 𝕊) R) (fun y hy => by
      apply hv
      simpa [Metric.mem_closedBall, dist_zero_right] using hy)
  exact ⟨(hG.mul hH).integrable_of_hasCompactSupport hc.mul_left,
    (hH.mul hG).integrable_of_hasCompactSupport hc.mul_right⟩

/-- **Weak `y_j`-derivative of a smooth field** (classical integration by parts in `y` against a
phase test, which has bounded `y`-support; source 2525-2531). -/
theorem weakDyS_of_smooth (P : ℝ) [Fact (0 < P)] (j : Fin 3) {f : ℝ × 𝕊 → ℂ}
    (hf : ContDiff ℝ ∞ f) : WeakDyS P j f (dy j f) := by
  intro φ hφ
  obtain ⟨R, hR⟩ := hφ.bounded_support
  obtain ⟨R', hR'⟩ := (hφ.dy j).bounded_support
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdf := contDiff_dy' hf j
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hdφ := contDiff_dy' hφ.smooth j
  unfold phaseInt
  rw [← smul_neg]
  congr 1
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ∫ y, dy j φ (t, y) * f (t, y) = -∫ y, φ (t, y) * dy j f (t, y)
  have hc : ∀ {g : ℝ × 𝕊 → ℂ}, Continuous g → Continuous fun y : 𝕊 => g (t, y) :=
    fun hg => hg.comp (continuous_const.prodMk continuous_id)
  have hfs : Differentiable ℝ (fun y : 𝕊 => f (t, y)) :=
    hfd.comp ((differentiable_const t).prodMk differentiable_id)
  have hφs : Differentiable ℝ (fun y : 𝕊 => φ (t, y)) :=
    hφd.comp ((differentiable_const t).prodMk differentiable_id)
  have e1 : ∀ y, fderiv ℝ (fun y' => f (t, y')) y (UnforcedLeray.coordinateVector j) =
      dy j f (t, y) := fun y => slice_fderiv hfd t y _
  have e2 : ∀ y, fderiv ℝ (fun y' => φ (t, y')) y (UnforcedLeray.coordinateVector j) =
      dy j φ (t, y) := fun y => slice_fderiv hφd t y _
  have I1 := integrable_mul_of_vanish (hc hdf.continuous) (hc hφ.smooth.continuous) R
    (fun y hy => hR t y hy)
  have I2 := integrable_mul_of_vanish (hc hf.continuous) (hc hdφ.continuous) R'
    (fun y hy => hR' t y hy)
  have I3 := integrable_mul_of_vanish (hc hf.continuous) (hc hφ.smooth.continuous) R
    (fun y hy => hR t y hy)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y : 𝕊 => f (t, y)) (g := fun y : 𝕊 => φ (t, y))
    (v := UnforcedLeray.coordinateVector j)
    (by simpa only [e1] using I1.1) (by simpa only [e2] using I2.1) I3.1
    (fun x _ => hfs x) (fun x _ => hφs x)
  simp only [e1, e2] at key
  have a1 : (fun y => dy j φ (t, y) * f (t, y)) = fun y => f (t, y) * dy j φ (t, y) := by
    funext y; ring
  have a2 : (fun y => φ (t, y) * dy j f (t, y)) = fun y => dy j f (t, y) * φ (t, y) := by
    funext y; ring
  rw [a1, a2]
  exact key

end Calc

end UnforcedLeray.Short.PartIIIb.Concrete
