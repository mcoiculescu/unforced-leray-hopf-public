import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_4
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.AdjChart
import UnforcedLeray.Short.PartIIa.Tasks.F03dWindowBackNorm

/-!
# Part II-a, task `PartII-a:F09/3/1/4/2`: the scalar bound of the reversed window component

Proves `AdjCompBound` of `Sub/«PartII-a_F09_3_1_4»`. Source of record:
`the November 2 reference manuscript`,
lines 1435-1436 (all Jacobians on the window are bounded), with the reversed chart
`θ = 1 - e^{-t}`, `x = e^{-t/2} y`, `t = τ₀ - τ` (lines 1431-1441).

Proof outline. (1) Shift `z ↦ (τ₀ - z.1, z.2)` (measure preserving, `lintegral_comp_emb`).
(2) On `|t| < 1` the integrand is `e^{-qt} ‖ν g(chart(t,y))‖^q`, and
`e^{-qt} ≤ e^{|5/2-q|} e^{-5t/2}` there, the density of `lintegral_adjChart`.
(3) `lintegral_adjChart` for the cut-off function `adjbG`, which vanishes on `θ ≥ 1`.
(4) Drop the cut-off and identify the lower integral with the `L^q` norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Parabolic

/-- The reversed time shift `z ↦ (τ₀ - z.1, z.2)` as a measurable equivalence. -/
def adjbShiftE (τ₀ : ℝ) : (ℝ × Space) ≃ᵐ (ℝ × Space) where
  toFun z := (τ₀ - z.1, z.2)
  invFun p := (τ₀ - p.1, p.2)
  left_inv z := by simp
  right_inv p := by simp
  measurable_toFun := Measurable.prodMk (measurable_const.sub measurable_fst) measurable_snd
  measurable_invFun := Measurable.prodMk (measurable_const.sub measurable_fst) measurable_snd

/-- The reversed time shift is measure preserving. -/
theorem adjb_shift_mp (τ₀ : ℝ) :
    MeasurePreserving (fun z : ℝ × Space => (τ₀ - z.1, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (Measure.measurePreserving_sub_left volume τ₀).prod (MeasurePreserving.id volume)

/-- The component `adjComp` at the shifted point `(τ₀ - t, y)` is the chart expression on `|t| < 1`. -/
theorem adjb_adjComp_shift (ν τ₀ : ℝ) (g : PS 3 → ℂ) (p : ℝ × Space) :
    adjComp ν τ₀ g (τ₀ - p.1, p.2) =
      if |p.1| < 1 then
        (ν : ℂ) * ((Real.exp (-p.1) : ℝ) : ℂ) * g (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)
      else 0 := by
  unfold adjComp
  have h1 : τ₀ - (τ₀ - p.1) = p.1 := sub_sub_cancel τ₀ p.1
  have h2 : τ₀ - p.1 - τ₀ = -p.1 := sub_sub_cancel_left τ₀ p.1
  simp only [h1, h2, abs_neg, neg_div]

/-- Scalar factors pull out of the `ℂ`-norm. -/
theorem adjb_enorm_scalar (r : ℝ) (hr : 0 ≤ r) (ν : ℝ) (w : ℂ) :
    ‖(ν : ℂ) * ((r : ℝ) : ℂ) * w‖ₑ = ENNReal.ofReal r * ‖(ν : ℂ) * w‖ₑ := by
  rw [show (ν : ℂ) * (r : ℂ) * w = (r : ℂ) * ((ν : ℂ) * w) by ring, enorm_mul,
    wd_enorm_real r hr]

/-- The real weight inequality on the window `|t| < 1`:
`e^{-tq} ≤ e^{|5/2 - q|} e^{-5t/2}`. -/
theorem adjb_real_weight (q t : ℝ) (ht : |t| < 1) :
    Real.exp (-t) ^ q ≤ Real.exp |5 / 2 - q| * Real.exp (-(5 * t / 2)) := by
  rw [← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (5 / 2 - q) * t ≤ |5 / 2 - q| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_of_le_one_right (abs_nonneg _) ht.le))
  have h2 : -t * q = -(5 * t / 2) + (5 / 2 - q) * t := by ring
  rw [h2]
  linarith

/-- The pointwise `ℝ≥0∞` bound on the window. -/
theorem adjb_pointwise (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : |t| < 1) (N : ℝ≥0∞) :
    (ENNReal.ofReal (Real.exp (-t)) * N) ^ q ≤
      ENNReal.ofReal (Real.exp |5 / 2 - q|) *
        (ENNReal.ofReal (Real.exp (-(5 * t / 2))) * N ^ q) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos (-t)).le hq.le]
  have key : ENNReal.ofReal (Real.exp (-t) ^ q) ≤
      ENNReal.ofReal (Real.exp |5 / 2 - q|) * ENNReal.ofReal (Real.exp (-(5 * t / 2))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos |5 / 2 - q|).le]
    exact ENNReal.ofReal_le_ofReal (adjb_real_weight q t ht)
  calc ENNReal.ofReal (Real.exp (-t) ^ q) * N ^ q
      ≤ (ENNReal.ofReal (Real.exp |5 / 2 - q|) * ENNReal.ofReal (Real.exp (-(5 * t / 2)))) *
          N ^ q := mul_le_mul_of_nonneg_right key zero_le
    _ = ENNReal.ofReal (Real.exp |5 / 2 - q|) *
          (ENNReal.ofReal (Real.exp (-(5 * t / 2))) * N ^ q) := by ring

/-- The cut-off reversed integrand: `G X = ‖ν g X‖_ₑ^q` for `X.1 < 1`, and `0` otherwise. -/
def adjbG (ν : ℝ) (g : PS 3 → ℂ) (q : ℝ) (X : PS 3) : ℝ≥0∞ :=
  if X.1 < 1 then ‖(ν : ℂ) * g X‖ₑ ^ q else 0

theorem adjbG_zero (ν : ℝ) (g : PS 3 → ℂ) (q : ℝ) :
    ∀ X : PS 3, 1 ≤ X.1 → adjbG ν g q X = 0 := by
  intro X hX
  unfold adjbG
  rw [if_neg (not_lt.2 hX)]

theorem adjbG_chart (ν : ℝ) (g : PS 3 → ℂ) (q : ℝ) (p : ℝ × Space) :
    adjbG ν g q (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) =
      ‖(ν : ℂ) * g (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)‖ₑ ^ q := by
  unfold adjbG
  dsimp only
  rw [if_pos (show 1 - Real.exp (-p.1) < 1 by linarith [Real.exp_pos (-p.1)])]

/-- The pointwise bound of the shifted component by the cut-off reversed integrand. -/
theorem adjb_pt (q : ℝ) (hq : 0 < q) (ν τ₀ : ℝ) (g : PS 3 → ℂ) (p : ℝ × Space) :
    ‖adjComp ν τ₀ g (τ₀ - p.1, p.2)‖ₑ ^ q ≤
      ENNReal.ofReal (Real.exp |5 / 2 - q|) *
        (ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
          adjbG ν g q (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)) := by
  rw [adjb_adjComp_shift, adjbG_chart]
  by_cases h : |p.1| < 1
  · rw [if_pos h, adjb_enorm_scalar (Real.exp (-p.1)) (Real.exp_pos (-p.1)).le]
    exact adjb_pointwise q hq p.1 h _
  · rw [if_neg h, enorm_zero, ENNReal.zero_rpow_of_pos hq]
    exact zero_le

/-- **`PartII-a:F09/3/1/4/2`: the scalar bound of the reversed window component.** -/
theorem adjCompBound : AdjCompBound := by
  intro q hq
  have hq0 : (0 : ℝ) < q := by linarith
  refine ⟨Real.exp |5 / 2 - q|, (Real.exp_pos _).le, ?_⟩
  intro ν τ₀ g _hg
  have h1 : ∫⁻ z : ℝ × Space, ‖adjComp ν τ₀ g z‖ₑ ^ q =
      ∫⁻ p : ℝ × Space, ‖adjComp ν τ₀ g (τ₀ - p.1, p.2)‖ₑ ^ q :=
    ((adjb_shift_mp τ₀).lintegral_comp_emb (adjbShiftE τ₀).measurableEmbedding
      (fun z => ‖adjComp ν τ₀ g z‖ₑ ^ q)).symm
  have h2 : ∫⁻ p : ℝ × Space, ‖adjComp ν τ₀ g (τ₀ - p.1, p.2)‖ₑ ^ q ≤
      ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp |5 / 2 - q|) *
        (ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
          adjbG ν g q (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)) :=
    lintegral_mono fun p => adjb_pt q hq0 ν τ₀ g p
  have h3 : ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
        adjbG ν g q (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) =
      ∫⁻ X : PS 3, adjbG ν g q X :=
    (lintegral_adjChart (adjbG ν g q) (adjbG_zero ν g q)).symm
  have h4 : ∫⁻ X : PS 3, adjbG ν g q X ≤ ∫⁻ X : PS 3, ‖(ν : ℂ) * g X‖ₑ ^ q :=
    lintegral_mono fun X => by
      unfold adjbG
      by_cases hX : X.1 < 1
      · rw [if_pos hX]
      · rw [if_neg hX]
        exact zero_le
  have h5 : ∫⁻ X : PS 3, ‖(ν : ℂ) * g X‖ₑ ^ q =
      eLpNorm (fun X => (ν : ℂ) * g X) (ENNReal.ofReal q) volume ^ q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, one_div, ENNReal.rpow_inv_rpow hq0.ne']
  calc ∫⁻ z : ℝ × Space, ‖adjComp ν τ₀ g z‖ₑ ^ q
      = ∫⁻ p : ℝ × Space, ‖adjComp ν τ₀ g (τ₀ - p.1, p.2)‖ₑ ^ q := h1
    _ ≤ ∫⁻ p : ℝ × Space, ENNReal.ofReal (Real.exp |5 / 2 - q|) *
        (ENNReal.ofReal (Real.exp (-(5 * p.1 / 2))) *
          adjbG ν g q (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2)) := h2
    _ = ENNReal.ofReal (Real.exp |5 / 2 - q|) * ∫⁻ X : PS 3, adjbG ν g q X := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3]
    _ ≤ ENNReal.ofReal (Real.exp |5 / 2 - q|) * ∫⁻ X : PS 3, ‖(ν : ℂ) * g X‖ₑ ^ q :=
        mul_le_mul_of_nonneg_left h4 zero_le
    _ = ENNReal.ofReal (Real.exp |5 / 2 - q|) *
        eLpNorm (fun X => (ν : ℂ) * g X) (ENNReal.ofReal q) volume ^ q := by rw [h5]

end UnforcedLeray.Short.PartIIa
