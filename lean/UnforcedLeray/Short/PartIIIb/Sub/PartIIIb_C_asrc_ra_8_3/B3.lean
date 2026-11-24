import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_1

/-!
# `DiffMagFromSup` (`PartIII-b:C/asrc/ra/8/3/1/3`): the nonnegative-bounds form

Source: `the November 2 reference manuscript` 2040-2051.

The target `DiffMagFromSup` quantifies over all real `X0 X1` with no sign condition.  For a
negative bound, `ENNReal.ofReal X0 = 0` forces `g ≡ 0`, and the conclusion `0 ≤ X0 + X1` can then
fail (take `X0 = X1 = -1`); so the target is not provable as stated.  This file proves the
statement with the sign conditions `0 ≤ X0`, `0 ≤ X1` added (`diffMagFromSup_nonneg_B3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A sup bound `‖D^j f‖_∞ ≤ M` (with `M ≥ 0`) gives the pointwise bound at every `x`. -/
theorem supNormD_pointwise_B3 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) (f : E → F) (M : ℝ) (hM : 0 ≤ M)
    (h : UnforcedLeray.B0277.supNormD j f ≤ ENNReal.ofReal M) (x : E) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ M := by
  have h1 : ‖iteratedFDeriv ℝ j f x‖ₑ ≤ ENNReal.ofReal M :=
    (le_iSup (fun y => ‖iteratedFDeriv ℝ j f y‖ₑ) x).trans h
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 h1

theorem diffMagFromSup_nonneg_B3 : ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ),
    (∀ y : ℝ × ℝ, vsum ν s y = (UnforcedLeray.Train.Vc ν c s y 0,
      UnforcedLeray.Train.Vc ν c s y 1)) →
    ContDiff ℝ 1 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z) → ∀ X0 X1 : ℝ,
    0 ≤ X0 → 0 ≤ X1 →
    UnforcedLeray.B0277.supNormD 0 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z) ≤
      ENNReal.ofReal X0 →
    UnforcedLeray.B0277.supNormD 1 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z) ≤
      ENNReal.ofReal X1 →
    ∀ x : ℝ × ℝ, trainDiffMag tr s x ≤ X0 + X1 := by
  intro ν c tr s hV hg X0 X1 hX0 hX1 S0 S1 x
  set g : ℝ × ℝ → UnforcedLeray.Train.Vec :=
    fun z => tr.v s z - UnforcedLeray.Train.Vc ν c s z with hgdef
  have hpt : ∀ y : ℝ × ℝ, trainPl tr s y - vsum ν s y = (g y 0, g y 1) := by
    intro y
    rw [hV y]
    simp [trainPl, hgdef]
  have hfun : (fun y => trainPl tr s y - vsum ν s y) = fun y => (g y 0, g y 1) :=
    funext hpt
  let L : UnforcedLeray.Train.Vec →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.prod (EuclideanSpace.proj (0 : Fin 2)) (EuclideanSpace.proj (1 : Fin 2))
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun v => ?_)
    have b0 : ‖v 0‖ ≤ ‖v‖ := PiLp.norm_apply_le v 0
    have b1 : ‖v 1‖ ≤ ‖v‖ := PiLp.norm_apply_le v 1
    rw [one_mul, Prod.norm_def]
    exact max_le b0 b1
  have hD : fderiv ℝ (fun y => (g y 0, g y 1)) x = L.comp (fderiv ℝ g x) := by
    have hdg : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiable one_ne_zero x).hasFDerivAt
    exact (L.hasFDerivAt.comp x hdg).fderiv
  have hDn : ‖fderiv ℝ (fun y => (g y 0, g y 1)) x‖ ≤ ‖fderiv ℝ g x‖ := by
    rw [hD]
    have hc := ContinuousLinearMap.opNorm_comp_le L (fderiv ℝ g x)
    exact le_trans hc (mul_le_of_le_one_left (norm_nonneg _) hLn)
  have hgx : ‖g x‖ ≤ X0 := by
    have := supNormD_pointwise_B3 0 g X0 hX0 S0 x
    rwa [norm_iteratedFDeriv_zero] at this
  have hDx : ‖fderiv ℝ g x‖ ≤ X1 := by
    have := supNormD_pointwise_B3 1 g X1 hX1 S1 x
    rwa [norm_iteratedFDeriv_one] at this
  have a0 : ‖g x 0‖ ≤ ‖g x‖ := PiLp.norm_apply_le (g x) 0
  have a1 : ‖g x 1‖ ≤ ‖g x‖ := PiLp.norm_apply_le (g x) 1
  have h1 : ‖(g x 0, g x 1)‖ ≤ ‖g x‖ := by
    rw [Prod.norm_def]
    exact max_le a0 a1
  unfold trainDiffMag
  rw [hfun, hpt x]
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem diffMagFromSup_proof : DiffMagFromSup := by
  intro ν c tr s hV hg X0 X1 hX0 hX1 S0 S1 x
  exact diffMagFromSup_nonneg_B3 ν c tr s hV hg X0 X1 hX0 hX1 S0 S1 x

end UnforcedLeray.Short.PartIIIb.Concrete
