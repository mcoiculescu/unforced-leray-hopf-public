import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Pairing

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: bounding and integrating the drift

Source: SP 2962-2964, 2954-2956.

* `abs_integral_mul_le`: `|∫ w Res| ≤ Bnd ((2L)⁻¹ A + (L/2)|K|)` when `|Res| ≤ Bnd` on the square
  `K`, `Res = 0` off `K`, `∫_K w² ≤ A` (pointwise `|w| ≤ w²/(2L) + L/2`).
* `abs_sub_le_of_deriv_bound`: a right derivative bounded by `Λ a(τ)⁻²` gives
  `|I(t) - I(s)| ≤ Λ (z(t) - z(s))` (`z' = a⁻²`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem volume_real_closedBall_zero (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r) = (2 * r) ^ 2 := by
  have h0 : (0 : ℝ × ℝ) = ((0 : ℝ), (0 : ℝ)) := rfl
  rw [Measure.real, h0, ← closedBall_prod_same, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem setIntegral_abs_le {w : ℝ × ℝ → ℝ} (hw : Continuous w) (r : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, |w x| ≤
      (1 / (2 * L)) * (∫ x in Metric.closedBall (0 : ℝ × ℝ) r, w x ^ 2) +
        L / 2 * (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r) := by
  have hK := isCompact_closedBall (0 : ℝ × ℝ) r
  have i1 : IntegrableOn (fun x => |w x|) (Metric.closedBall (0 : ℝ × ℝ) r) :=
    hw.abs.continuousOn.integrableOn_compact hK
  have i2 : IntegrableOn (fun x => w x ^ 2) (Metric.closedBall (0 : ℝ × ℝ) r) :=
    (hw.pow 2).continuousOn.integrableOn_compact hK
  have i3 : IntegrableOn (fun _ : ℝ × ℝ => L / 2) (Metric.closedBall (0 : ℝ × ℝ) r) :=
    integrableOn_const hK.measure_lt_top.ne
  have hpt : ∀ x, |w x| ≤ (1 / (2 * L)) * w x ^ 2 + L / 2 := by
    intro x
    have h1 := sq_nonneg (|w x| - L)
    have h2 : w x ^ 2 = |w x| ^ 2 := (sq_abs (w x)).symm
    rw [h2]
    have hL2 : 0 < 2 * L := by linarith
    have key : 2 * L * |w x| ≤ |w x| ^ 2 + L ^ 2 := by nlinarith
    calc |w x| = (2 * L * |w x|) / (2 * L) := by field_simp
      _ ≤ (|w x| ^ 2 + L ^ 2) / (2 * L) := div_le_div_of_nonneg_right key hL2.le
      _ = (1 / (2 * L)) * |w x| ^ 2 + L / 2 := by field_simp
  have i4 : IntegrableOn (fun x => (1 / (2 * L)) * w x ^ 2 + L / 2)
      (Metric.closedBall (0 : ℝ × ℝ) r) := (i2.const_mul _).add i3
  calc ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, |w x|
      ≤ ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, ((1 / (2 * L)) * w x ^ 2 + L / 2) :=
        setIntegral_mono_on i1 i4 measurableSet_closedBall
          (fun x _ => hpt x)
    _ = (1 / (2 * L)) * (∫ x in Metric.closedBall (0 : ℝ × ℝ) r, w x ^ 2) +
          L / 2 * (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r) := by
        rw [integral_add (i2.const_mul _) i3, integral_const_mul, setIntegral_const, smul_eq_mul,
          mul_comm (L / 2)]

theorem abs_integral_mul_le {w Res : ℝ × ℝ → ℝ} (hw : Continuous w) {r Bnd A L : ℝ}
    (hBnd : 0 ≤ Bnd) (hL : 0 < L)
    (hin : ∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) r, |Res x| ≤ Bnd)
    (hout : ∀ x ∉ Metric.closedBall (0 : ℝ × ℝ) r, Res x = 0)
    (hA : ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, w x ^ 2 ≤ A) :
    |∫ x, w x * Res x| ≤ Bnd * ((1 / (2 * L)) * A +
      L / 2 * (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r)) := by
  have hK := isCompact_closedBall (0 : ℝ × ℝ) r
  have i1 : IntegrableOn (fun x => |w x|) (Metric.closedBall (0 : ℝ × ℝ) r) :=
    hw.abs.continuousOn.integrableOn_compact hK
  have i1' : IntegrableOn (fun x => Bnd * |w x|) (Metric.closedBall (0 : ℝ × ℝ) r) :=
    i1.const_mul Bnd
  have hg : Integrable ((Metric.closedBall (0 : ℝ × ℝ) r).indicator (fun x => Bnd * |w x|)) :=
    IntegrableOn.integrable_indicator i1' measurableSet_closedBall
  have hle : ∫ x, |w x * Res x| ≤
      ∫ x, (Metric.closedBall (0 : ℝ × ℝ) r).indicator (fun x => Bnd * |w x|) x := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hg
      (Eventually.of_forall fun x => ?_)
    show |w x * Res x| ≤ (Metric.closedBall (0 : ℝ × ℝ) r).indicator (fun x => Bnd * |w x|) x
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ × ℝ) r
    · rw [indicator_of_mem hx, abs_mul, mul_comm Bnd]
      exact mul_le_mul_of_nonneg_left (hin x hx) (abs_nonneg _)
    · rw [indicator_of_notMem hx, hout x hx, mul_zero, abs_zero]
  rw [integral_indicator measurableSet_closedBall, integral_const_mul] at hle
  have hab := setIntegral_abs_le hw r hL
  have hvol : 0 ≤ (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r) :=
    measureReal_nonneg
  calc |∫ x, w x * Res x| ≤ ∫ x, |w x * Res x| := abs_integral_le_integral_abs
    _ ≤ Bnd * ∫ x in Metric.closedBall (0 : ℝ × ℝ) r, |w x| := hle
    _ ≤ Bnd * ((1 / (2 * L)) * A +
          L / 2 * (volume : Measure (ℝ × ℝ)).real (Metric.closedBall (0 : ℝ × ℝ) r)) := by
        refine mul_le_mul_of_nonneg_left (hab.trans ?_) hBnd
        have : 0 ≤ 1 / (2 * L) := by positivity
        nlinarith

/-- A right derivative bounded by `Λ a(τ)⁻²` on `[s, t)` integrates to `Λ (z(t) - z(s))`. -/
theorem abs_sub_le_of_deriv_bound {I I' : ℝ → ℝ} {ν s t Λ : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hst : s ≤ t) (hc : ContinuousOn I (Icc s t))
    (hd : ∀ τ ∈ Ico s t, HasDerivWithinAt I (I' τ) (Ici τ) τ)
    (hb : ∀ τ ∈ Ico s t, |I' τ| ≤ Λ * (clockA ν τ)⁻¹ ^ 2) :
    |I t - I s| ≤ Λ * (movingZ ν t - movingZ ν s) := by
  have hzc : ContinuousOn (fun σ => movingZ ν σ) (Icc s t) := fun σ hσ =>
    (hasDerivAt_movingZ hν (hs.trans hσ.1)).continuousAt.continuousWithinAt
  have hzd : ∀ τ ∈ Ico s t, HasDerivWithinAt (fun σ => Λ * (movingZ ν σ - movingZ ν s))
      (Λ * (clockA ν τ)⁻¹ ^ 2) (Ici τ) τ := by
    intro τ hτ
    have := ((hasDerivAt_movingZ hν (hs.trans hτ.1)).sub_const (movingZ ν s)).const_mul Λ
    exact this.hasDerivWithinAt
  have hBc : ContinuousOn (fun σ => I s + Λ * (movingZ ν σ - movingZ ν s)) (Icc s t) :=
    continuousOn_const.add (continuousOn_const.mul (hzc.sub continuousOn_const))
  have hBc' : ContinuousOn (fun σ => -I s + Λ * (movingZ ν σ - movingZ ν s)) (Icc s t) :=
    continuousOn_const.add (continuousOn_const.mul (hzc.sub continuousOn_const))
  have h1 := image_le_of_deriv_right_le_deriv_boundary (f := I) (f' := I') hc hd
    (B := fun σ => I s + Λ * (movingZ ν σ - movingZ ν s)) (B' := fun τ => Λ * (clockA ν τ)⁻¹ ^ 2)
    (by simp) hBc (fun τ hτ => (hzd τ hτ).const_add (I s))
    (fun τ hτ => (le_abs_self _).trans (hb τ hτ))
  have h2 := image_le_of_deriv_right_le_deriv_boundary (f := fun σ => -I σ)
    (f' := fun τ => -I' τ) hc.neg (fun τ hτ => (hd τ hτ).neg)
    (B := fun σ => -I s + Λ * (movingZ ν σ - movingZ ν s))
    (B' := fun τ => Λ * (clockA ν τ)⁻¹ ^ 2)
    (by simp) hBc' (fun τ hτ => (hzd τ hτ).const_add (-I s))
    (fun τ hτ => (neg_le_abs _).trans (hb τ hτ))
  have ht : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have e1 := h1 ht
  have e2 := h2 ht
  rw [abs_le]
  constructor <;> linarith

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
