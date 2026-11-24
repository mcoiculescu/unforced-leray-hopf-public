import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# From the integrated comoving identity to all comoving jets (helper of `PartII-b:S3/1/1/2/1/2`)

Source of record: `the November 2 reference manuscript`,
lines 2559-2562.

`hasComovingJetDeriv_of_integral_identity`: if `F, H` have smooth slices, all spatial jets of `H`
are jointly continuous, and `F(τ₀ + t, e^{-t/2}x) - F(τ₀, x) = ∫₀ᵗ H(τ₀ + r, e^{-r/2}x) dr` for all
`τ₀, t, x`, then `HasComovingJetDeriv F H`. The jets of the identity are taken under the integral
sign (`dirSpatialJet_intervalIntegral`, one-dimensional differentiation under the integral along
`s ↦ x + s • w`), the dilation chain rule (`JointSmoothSub.dirSpatialJet_comp_smul`) turns the
`ws`-jet of `x ↦ F(τ₀ + t, e^{-t/2}x)` into `e^{-|ws|t/2} ∂^{ws}F(τ₀ + t, e^{-t/2}x)`, and the
fundamental theorem of calculus at `t = 0` gives the comoving jet derivative
`∂^{ws}H + (|ws|/2) ∂^{ws}F`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.CorrComovingSub

/-- **Spatial jets commute with a parametric interval integral.** If the slices `K r` are
smooth, every spatial jet of `K` is jointly continuous, and `x ↦ ∫_a^b K r x dr` is smooth, then
`∂^{ws} ∫_a^b K r dr = ∫_a^b ∂^{ws} K r dr` pointwise. -/
theorem dirSpatialJet_intervalIntegral {K : ℝ → SpatialField}
    (hK : ∀ r, ContDiff ℝ ∞ (K r))
    (hKc : ∀ ws : List Space, Continuous (fun p : ℝ × Space => dirSpatialJet (K p.1) ws p.2))
    (a b : ℝ) (hI : ContDiff ℝ ∞ (fun x => ∫ r in a..b, K r x)) :
    ∀ (ws : List Space) (x : Space),
      dirSpatialJet (fun x => ∫ r in a..b, K r x) ws x = ∫ r in a..b, dirSpatialJet (K r) ws x
  | [], _ => rfl
  | w :: ws, x => by
      have ih := dirSpatialJet_intervalIntegral hK hKc a b hI ws
      have hfun : dirSpatialJet (fun x => ∫ r in a..b, K r x) ws =
          fun x => ∫ r in a..b, dirSpatialJet (K r) ws x := funext ih
      have hΦd : Differentiable ℝ (fun x => ∫ r in a..b, dirSpatialJet (K r) ws x) := by
        rw [← hfun]
        exact JointSmoothSub.differentiable_dirSpatialJet hI ws
      rw [dirSpatialJet_cons, hfun]
      have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • w) w s := fun s => by
        simpa using ((hasDerivAt_id s).smul_const w).const_add x
      have hd1 : HasDerivAt (fun s : ℝ => ∫ r in a..b, dirSpatialJet (K r) ws (x + s • w))
          (fderiv ℝ (fun x => ∫ r in a..b, dirSpatialJet (K r) ws x) x w) 0 := by
        have h := (hΦd (x + (0 : ℝ) • w)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
        rw [zero_smul, add_zero] at h
        exact h
      have hJd : ∀ r, Differentiable ℝ (dirSpatialJet (K r) ws) := fun r =>
        JointSmoothSub.differentiable_dirSpatialJet (hK r) ws
      obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall x ‖w‖)).exists_bound_of_continuousOn
        (hKc (w :: ws)).continuousOn
      have hcomp : ∀ (vs : List Space) (s : ℝ),
          Continuous fun r : ℝ => dirSpatialJet (K r) vs (x + s • w) := fun vs s =>
        (hKc vs).comp (continuous_id.prodMk continuous_const)
      have hmemB : ∀ s ∈ ball (0 : ℝ) 1, x + s • w ∈ closedBall x ‖w‖ := by
        intro s hs
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
        have hs' : ‖s‖ < 1 := by simpa [mem_ball, dist_zero_right] using hs
        nlinarith [norm_nonneg w, norm_nonneg s]
      have hd2 := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume) (a := a) (b := b)
        (F := fun s r => dirSpatialJet (K r) ws (x + s • w))
        (F' := fun s r => dirSpatialJet (K r) (w :: ws) (x + s • w))
        (x₀ := (0 : ℝ)) (bound := fun _ => C) (s := ball (0 : ℝ) 1)
        (ball_mem_nhds 0 one_pos)
        (Eventually.of_forall fun s => (hcomp ws s).aestronglyMeasurable)
        ((hcomp ws 0).intervalIntegrable a b)
        ((hcomp (w :: ws) 0).aestronglyMeasurable)
        (Eventually.of_forall fun r hr s hs =>
          hC (r, x + s • w) ⟨uIoc_subset_uIcc hr, hmemB s hs⟩)
        intervalIntegrable_const
        (Eventually.of_forall fun r _ s _ => by
          have h := (hJd r (x + s • w)).hasFDerivAt.comp_hasDerivAt s (hline s)
          exact h)
      have huniq := hd1.unique hd2.2
      rw [huniq]
      simp

/-- **All comoving jets from the integrated identity.** If `F, H` have smooth slices, every
spatial jet of `H` is jointly continuous, and
`F(τ₀ + t, e^{-t/2}x) - F(τ₀, x) = ∫₀ᵗ H(τ₀ + r, e^{-r/2}x) dr` for all `τ₀, t, x`, then
`HasComovingJetDeriv F H`. -/
theorem hasComovingJetDeriv_of_integral_identity {F H : ℝ → SpatialField}
    (hF : ∀ τ, ContDiff ℝ ∞ (F τ)) (hH : ∀ τ, ContDiff ℝ ∞ (H τ))
    (hHc : ∀ ws : List Space, Continuous (fun p : ℝ × Space => dirSpatialJet (H p.1) ws p.2))
    (hI : ∀ (τ₀ t : ℝ) (x : Space),
      F (τ₀ + t) (Real.exp (-t / 2) • x) - F τ₀ x =
        ∫ r in (0 : ℝ)..t, H (τ₀ + r) (Real.exp (-r / 2) • x)) :
    HasComovingJetDeriv F H := by
  intro ws τ₀ y
  set n : ℕ := ws.length with hn
  set c : ℝ → ℝ := fun t => Real.exp (-t / 2) with hc
  have hc_cont : Continuous c := Real.continuous_exp.comp (continuous_neg.div_const 2)
  set L : ℝ → Space := fun r => dirSpatialJet (H (τ₀ + r)) ws (c r • y) with hL
  have hLc : Continuous L :=
    (hHc ws).comp ((continuous_const.add continuous_id).prodMk (hc_cont.smul continuous_const))
  -- the `ws`-jet of the integrated identity
  have hjet : ∀ t : ℝ, (c t) ^ n • dirSpatialJet (F (τ₀ + t)) ws (c t • y) -
      dirSpatialJet (F τ₀) ws y = ∫ r in (0 : ℝ)..t, (c r) ^ n • L r := by
    intro t
    set K : ℝ → SpatialField := fun r x => H (τ₀ + r) (c r • x) with hK
    have hKs : ∀ r, ContDiff ℝ ∞ (K r) := fun r =>
      JointSmoothSub.contDiff_infty_comp_smul (hH (τ₀ + r)) (c r)
    have hKjet : ∀ (vs : List Space) (r : ℝ) (x : Space),
        dirSpatialJet (K r) vs x = (c r) ^ vs.length • dirSpatialJet (H (τ₀ + r)) vs (c r • x) :=
      fun vs r x => JointSmoothSub.dirSpatialJet_comp_smul (hH (τ₀ + r)) (c r) vs x
    have hKc : ∀ vs : List Space,
        Continuous (fun p : ℝ × Space => dirSpatialJet (K p.1) vs p.2) := by
      intro vs
      have hfun : (fun p : ℝ × Space => dirSpatialJet (K p.1) vs p.2) = fun p =>
          (c p.1) ^ vs.length • dirSpatialJet (H (τ₀ + p.1)) vs (c p.1 • p.2) :=
        funext fun p => hKjet vs p.1 p.2
      rw [hfun]
      exact ((hc_cont.comp continuous_fst).pow _).smul ((hHc vs).comp
        ((continuous_const.add continuous_fst).prodMk
          ((hc_cont.comp continuous_fst).smul continuous_snd)))
    have hFt : ContDiff ℝ ∞ (fun x => F (τ₀ + t) (c t • x)) :=
      JointSmoothSub.contDiff_infty_comp_smul (hF (τ₀ + t)) (c t)
    have hIfun : (fun x => ∫ r in (0 : ℝ)..t, K r x) =
        (fun x => F (τ₀ + t) (c t • x)) - F τ₀ := by
      funext x
      exact (hI τ₀ t x).symm
    have hIs : ContDiff ℝ ∞ (fun x => ∫ r in (0 : ℝ)..t, K r x) := by
      rw [hIfun]
      exact hFt.sub (hF τ₀)
    have h1 := dirSpatialJet_intervalIntegral hKs hKc 0 t hIs ws y
    rw [hIfun, HigherPhaseSub.dirSpatialJet_sub hFt (hF τ₀) ws, Pi.sub_apply,
      JointSmoothSub.dirSpatialJet_comp_smul (hF (τ₀ + t)) (c t) ws y] at h1
    rw [h1]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [hL]
    exact hKjet ws r y
  -- solve for the jet along the ray
  have hJ : ∀ t : ℝ, dirSpatialJet (F (τ₀ + t)) ws (c t • y) =
      Real.exp ((n : ℝ) * t / 2) •
        (dirSpatialJet (F τ₀) ws y + ∫ r in (0 : ℝ)..t, (c r) ^ n • L r) := by
    intro t
    have hinv : Real.exp ((n : ℝ) * t / 2) * (c t) ^ n = 1 := by
      simp only [hc]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have : (n : ℝ) * t / 2 + (n : ℝ) * (-t / 2) = 0 := by ring
      rw [this, Real.exp_zero]
    rw [← hjet t, add_sub_cancel, smul_smul, hinv, one_smul]
  have hE : HasDerivAt (fun t : ℝ => Real.exp ((n : ℝ) * t / 2)) ((n : ℝ) / 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (n : ℝ) * t / 2) ((n : ℝ) / 2) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (n : ℝ)).div_const 2
    have h2 := (Real.hasDerivAt_exp ((n : ℝ) * 0 / 2)).comp 0 h1
    simp only [mul_zero, zero_div, Real.exp_zero, one_mul] at h2
    exact h2
  have hcont : Continuous fun r => (c r) ^ n • L r := (hc_cont.pow n).smul hLc
  have hIntDeriv : HasDerivAt
      (fun t => dirSpatialJet (F τ₀) ws y + ∫ r in (0 : ℝ)..t, (c r) ^ n • L r)
      ((c 0) ^ n • L 0) 0 :=
    (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 0)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).const_add _
  have hprod := hE.smul hIntDeriv
  have hfun : (fun t : ℝ => dirSpatialJet (F (τ₀ + t)) ws (Real.exp (-t / 2) • y)) =
      fun t => Real.exp ((n : ℝ) * t / 2) •
        (dirSpatialJet (F τ₀) ws y + ∫ r in (0 : ℝ)..t, (c r) ^ n • L r) :=
    funext hJ
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp [hL, hc, hn]

end UnforcedLeray.Short.IIb.CorrComovingSub

end
