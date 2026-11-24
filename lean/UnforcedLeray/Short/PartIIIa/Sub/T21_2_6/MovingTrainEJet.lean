import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# `PartIII-a:T21/2/6/2`: rescaling of the vorticity jets (`MovingTrainEJet`)

Source of record: `the November 2 reference manuscript` lines 2854-2873
(`E_mov(y) = a² E(√a y)`). Pure calculus: the vorticity `Ec tr r = Cyl.curl (tr.v r)` is `C^∞`
for `r ≥ 0` (the curl of a smooth field is smooth), so the chain rule applies to `y ↦ E(√a y)`
and the scalar `a²` is multiplied in.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Generic bound: the `j`-th derivative of `x ↦ Φ (h (l • x))` is at most `‖Φ‖ l^j` times that of
`h` at `l • y`. -/
theorem iter_clm_comp_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : E →L[ℝ] F) {h : ℝ × ℝ → E}
    (hh : ContDiff ℝ ∞ h) (l : ℝ) (hl : 0 ≤ l) (j : ℕ) (y : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (fun x => Φ (h (l • x))) y‖ ≤
      ‖Φ‖ * (l ^ j * ‖iteratedFDeriv ℝ j h (l • y)‖) := by
  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ := l • ContinuousLinearMap.id ℝ (ℝ × ℝ) with hLdef
  have hLy : ∀ x, L x = l • x := fun x => by simp [hLdef]
  have hLn : ‖L‖ = l := by
    rw [hLdef, norm_smul, ContinuousLinearMap.norm_id, Real.norm_of_nonneg hl, mul_one]
  have hsm : ContDiff ℝ ∞ (h ∘ L) := hh.comp L.contDiff
  have e1 : (fun x => Φ (h (l • x))) = Φ ∘ (h ∘ L) := by
    funext x
    simp [hLy]
  rw [e1, ContinuousLinearMap.iteratedFDeriv_comp_left Φ hsm.contDiffAt
      (by first | exact le_top | simp),
    ContinuousLinearMap.iteratedFDeriv_comp_right L hh y
      (by first | exact le_top | simp)]
  have hA := Φ.norm_compContinuousMultilinearMap_le
    ((iteratedFDeriv ℝ j h (L y)).compContinuousLinearMap fun _ => L)
  have hB := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j h (L y)) (fun _ : Fin j => L)
  rw [hLy] at hA hB ⊢
  simp only [hLn, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hB
  refine hA.trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [mul_comm]
  exact hB

/-- The curl of a smooth meridional field is smooth. -/
theorem curl_contDiff_of {u : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl u) := by
  have h1 : ContDiff ℝ 1 u := hu.of_le (by first | exact le_top | simp)
  have hc : UnforcedLeray.Cyl.curl u = fun z =>
      fderiv ℝ (fun w => u w 1) z (1, 0) - fderiv ℝ (fun w => u w 0) z (0, 1) :=
    funext (fun z => UnforcedLeray.B0238.curl_eq_fderiv h1 z)
  rw [hc]
  have g1 : ContDiff ℝ ∞ (fun w => u w 1) := UnforcedLeray.B0238.contDiff_comp_apply hu 1
  have g0 : ContDiff ℝ ∞ (fun w => u w 0) := UnforcedLeray.B0238.contDiff_comp_apply hu 0
  have d1 : ContDiff ℝ ∞ (fderiv ℝ (fun w => u w 1)) := (contDiff_infty_iff_fderiv.1 g1).2
  have d0 : ContDiff ℝ ∞ (fderiv ℝ (fun w => u w 0)) := (contDiff_infty_iff_fderiv.1 g0).2
  exact (d1.clm_apply contDiff_const).sub (d0.clm_apply contDiff_const)

/-- **Rescaling of the vorticity jets** (SP 2854-2873; `movingTrainE tr r y = a² E(r, √a y)`). -/
theorem movingTrainEJet : MovingTrainEJet := by
  intro ν c hν tr r hr j y
  have ha : 0 < clockA ν r := by
    unfold clockA
    nlinarith [mul_nonneg hν.le hr]
  have hl : 0 ≤ Real.sqrt (clockA ν r) := Real.sqrt_nonneg _
  have hpt : ∀ y : ℝ × ℝ, (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
      Real.sqrt (clockA ν r) • y := by
    intro y
    ext <;> simp [smul_eq_mul]
  have hfun : movingTrainE tr r =
      fun y => (clockA ν r ^ 2 • ContinuousLinearMap.id ℝ ℝ)
        (UnforcedLeray.B0238.Ec tr r (Real.sqrt (clockA ν r) • y)) := by
    funext y'
    simp [movingTrainE, hpt, smul_eq_mul]
  have hsm : ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr r) :=
    curl_contDiff_of (UnforcedLeray.B0238.contDiff_Vc tr hr)
  have hΦ : ‖clockA ν r ^ 2 • ContinuousLinearMap.id ℝ ℝ‖ ≤ clockA ν r ^ 2 := by
    rw [norm_smul, ContinuousLinearMap.norm_id, Real.norm_of_nonneg (sq_nonneg _), mul_one]
  have hb := iter_clm_comp_bound (clockA ν r ^ 2 • ContinuousLinearMap.id ℝ ℝ) hsm
    (Real.sqrt (clockA ν r)) hl j y
  rw [hfun, hpt y]
  calc _ ≤ ‖clockA ν r ^ 2 • ContinuousLinearMap.id ℝ ℝ‖ *
        (Real.sqrt (clockA ν r) ^ j * ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
          (Real.sqrt (clockA ν r) • y)‖) := hb
    _ ≤ clockA ν r ^ 2 *
        (Real.sqrt (clockA ν r) ^ j * ‖iteratedFDeriv ℝ j (UnforcedLeray.B0238.Ec tr r)
          (Real.sqrt (clockA ν r) • y)‖) :=
        mul_le_mul_of_nonneg_right hΦ (by positivity)
    _ = _ := by ring

end UnforcedLeray.Short.IIIa
