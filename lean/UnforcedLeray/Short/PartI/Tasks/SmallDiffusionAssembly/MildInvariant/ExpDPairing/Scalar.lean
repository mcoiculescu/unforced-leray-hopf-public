import UnforcedLeray.Short.PartI.Sub.PartI_C05_4
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeGenerator

/-!
# Helper for target `PartI:C05/4/2`: the scalar clock identity for a measurable clock

For measurable `β` with `0 ≤ β ≤ 1`, the clock `B(τ) = ∫_r^τ β` is Lipschitz and nonnegative
on `[r, t]`, so `τ ↦ exp(-n B(τ))` is Lipschitz there, hence absolutely continuous, and its
a.e. derivative is `-n β(τ) exp(-n B(τ))` (Lebesgue differentiation of `B`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartI.ExpDPairingHelp

theorem beta_intervalIntegrable {β : ℝ → ℝ} (hβm : Measurable β)
    (hβ01 : ∀ τ, 0 ≤ β τ ∧ β τ ≤ 1) (a b : ℝ) : IntervalIntegrable β volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hβm.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by
    show ‖β x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hβ01 x).1], (hβ01 x).2⟩

theorem exp_neg_lipschitz (n : ℕ) :
    LipschitzOnWith (n : NNReal) (fun x : ℝ => Real.exp (-(n : ℝ) * x)) (Ici 0) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-(n : ℝ) * y))
      (Real.exp (-(n : ℝ) * x) * (-(n : ℝ))) x := by
    intro x
    have h := ((hasDerivAt_id' x).const_mul (-(n : ℝ))).exp
    convert h using 1
    ring
  refine (Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := fun x : ℝ =>
    Real.exp (-(n : ℝ) * x) * (-(n : ℝ))) (convex_Ici 0) (fun x _ => (hd x).hasDerivWithinAt) ?_)
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have hexp : Real.exp (-(n : ℝ) * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx'
    linarith
  have hb : ‖Real.exp (-(n : ℝ) * x) * (-(n : ℝ))‖ ≤ (n : ℝ) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), abs_of_pos (Real.exp_pos _)]
    nlinarith [Real.exp_pos (-(n : ℝ) * x), Nat.cast_nonneg (α := ℝ) n]
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact hb

theorem scalar_exp_clock (n : ℕ) {r t : ℝ} (hrt : r ≤ t) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβ01 : ∀ τ, 0 ≤ β τ ∧ β τ ≤ 1) :
    Real.exp (-(n : ℝ) * ∫ u in r..t, β u) - 1 =
      ∫ τ in r..t, Real.exp (-(n : ℝ) * ∫ u in r..τ, β u) * (-(n : ℝ) * β τ) := by
  have hint : ∀ a b, IntervalIntegrable β volume a b := beta_intervalIntegrable hβm hβ01
  -- the clock is 1-Lipschitz
  have hBlip : LipschitzOnWith 1 (fun τ => ∫ u in r..τ, β u) (uIcc r t) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    have key : (∫ u in r..x, β u) - (∫ u in r..y, β u) = ∫ u in y..x, β u :=
      intervalIntegral.integral_interval_sub_left (hint r x) (hint r y)
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (f := β)
      (C := 1) (fun u _ => by
        show ‖β u‖ ≤ 1
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hβ01 u).1], (hβ01 u).2⟩)
    rw [Real.norm_eq_abs] at hn
    rw [Real.dist_eq, Real.dist_eq, key]
    simpa [abs_sub_comm] using hn
  -- the clock is nonnegative on `[r, t]`
  have hBnn : MapsTo (fun τ => ∫ u in r..τ, β u) (uIcc r t) (Ici 0) := by
    intro τ hτ
    rw [uIcc_of_le hrt] at hτ
    exact intervalIntegral.integral_nonneg hτ.1 (fun u _ => (hβ01 u).1)
  -- the composed function is Lipschitz on `[r, t]`
  have hF : LipschitzOnWith ((n : NNReal) * 1)
      (fun τ => Real.exp (-(n : ℝ) * ∫ u in r..τ, β u)) (uIcc r t) :=
    (exp_neg_lipschitz n).comp hBlip hBnn
  have hac := hF.absolutelyContinuousOnInterval
  have hftc := hac.integral_deriv_eq_sub
  have hae := (hint r t).ae_hasDerivAt_integral
  have hderiv : ∀ᵐ x ∂volume, x ∈ Set.uIoc r t →
      deriv (fun τ => Real.exp (-(n : ℝ) * ∫ u in r..τ, β u)) x =
        Real.exp (-(n : ℝ) * ∫ u in r..x, β u) * (-(n : ℝ) * β x) := by
    filter_upwards [hae] with x hx hxI
    have hxm : x ∈ uIcc r t := Set.uIoc_subset_uIcc hxI
    have hB : HasDerivAt (fun τ => ∫ u in r..τ, β u) (β x) x := hx hxm r (left_mem_uIcc)
    have h1 : HasDerivAt (fun τ => -(n : ℝ) * ∫ u in r..τ, β u) (-(n : ℝ) * β x) x :=
      hB.const_mul (-(n : ℝ))
    exact h1.exp.deriv
  have hcongr : (∫ x in r..t, deriv (fun τ => Real.exp (-(n : ℝ) * ∫ u in r..τ, β u)) x) =
      ∫ τ in r..t, Real.exp (-(n : ℝ) * ∫ u in r..τ, β u) * (-(n : ℝ) * β τ) :=
    intervalIntegral.integral_congr_ae hderiv
  rw [← hcongr, hftc, intervalIntegral.integral_same]
  simp

end UnforcedLeray.Short.PartI.ExpDPairingHelp
