import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# `PartIII-a:T21/2/6/1`: rescaling of the velocity jets (`MovingTrainVJet`)

Source of record: `the November 2 reference manuscript` lines 2854-2873
(`V(y) = a^{3/2} v(√a y)`). Pure calculus: the coordinate map `EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)`
has norm at most one, `x ↦ h(√a x)` has `j`-th derivative bounded by `(√a)^j` times the
`j`-th derivative of `h`, and the scalar `a^{3/2}` is multiplied in.
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

/-- **Rescaling of the velocity jets** (SP 2854-2873; `movingTrainV tr r y = a^{3/2} v(r, √a y)`). -/
theorem movingTrainVJet : MovingTrainVJet := by
  intro ν c hν tr r hr j y
  have ha : 0 < clockA ν r := by
    unfold clockA
    nlinarith [mul_nonneg hν.le hr]
  have hl : 0 ≤ Real.sqrt (clockA ν r) := Real.sqrt_nonneg _
  have hpt : ∀ y : ℝ × ℝ, (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) =
      Real.sqrt (clockA ν r) • y := by
    intro y
    ext <;> simp [smul_eq_mul]
  let P : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap
  have hP : ∀ x : EuclideanSpace ℝ (Fin 2), P x = fun i => x i := fun x => rfl
  have hPn : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [one_mul, hP]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 (fun i => PiLp.norm_apply_le x i)
  have hfun : movingTrainV tr r =
      fun y => (clockA ν r ^ (3 / 2 : ℝ) • P) (tr.v r (Real.sqrt (clockA ν r) • y)) := by
    funext y'
    funext i
    simp [movingTrainV, hP, hpt, smul_eq_mul]
  have hsm : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hΦ : ‖clockA ν r ^ (3 / 2 : ℝ) • P‖ ≤ clockA ν r ^ (3 / 2 : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ha.le _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ha.le _) hPn
  have hb := iter_clm_comp_bound (clockA ν r ^ (3 / 2 : ℝ) • P) hsm
    (Real.sqrt (clockA ν r)) hl j y
  rw [hfun, hpt y]
  calc _ ≤ ‖clockA ν r ^ (3 / 2 : ℝ) • P‖ *
        (Real.sqrt (clockA ν r) ^ j * ‖iteratedFDeriv ℝ j (tr.v r)
          (Real.sqrt (clockA ν r) • y)‖) := hb
    _ ≤ clockA ν r ^ (3 / 2 : ℝ) *
        (Real.sqrt (clockA ν r) ^ j * ‖iteratedFDeriv ℝ j (tr.v r)
          (Real.sqrt (clockA ν r) • y)‖) :=
        mul_le_mul_of_nonneg_right hΦ (by positivity)
    _ = _ := by ring

end UnforcedLeray.Short.IIIa
