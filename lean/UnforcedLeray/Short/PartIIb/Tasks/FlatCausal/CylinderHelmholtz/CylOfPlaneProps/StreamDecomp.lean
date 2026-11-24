import UnforcedLeray.Short.PartIIb.Sub.T12_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.SmoothPrimEta
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.CylOfPlaneProps.FluxConst

/-!
# Part II-b, leaf `PartII-b:T12/1/5/7` (`CylStreamDecomp`): stream function of a periodic
solenoidal test

Source of record: `the November 2 reference manuscript` lines 1727-1731. The target
is `CylStreamDecomp` of `Sub/T12_1_5.lean`.

Proof. Let `m = ∫ Ψ(0,s)₀ ds` (the flux, constant in `q` by `cylFluxConst`), let `g = Ψ₀ - m χ(η)`,
and let `R` strictly exceed the support radii of `Ψ₀`, `Ψ₁`, `χ`. Put `Φ(z) = ∫_{-R}^{z₂} g(z₁, s) ds`
(`smoothPrimEta`). Then `∂_η Φ = g` and `∂_q Φ = ∫_{-R}^{η} ∂_q g = -Ψ₁` by `div_free` and FTC.
`Φ` vanishes for `|η| > R` because `∫_{-R}^{R} g(q, ·) = m - m·1 = 0`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- A whole-line integral of a function vanishing for `R ≤ |s|` is the integral over `(-R, R)`. -/
theorem csd_int_eq (f : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (hf : ∀ s : ℝ, R ≤ |s| → f s = 0) :
    ∫ s in (-R)..R, f s = ∫ s, f s := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply hf
  by_contra hc
  push_neg at hc
  exact hx (abs_le.mp hc.le)

/-- An interval integral of a function vanishing on the interval is zero. -/
theorem csd_int_zero (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ s ∈ Set.uIcc a b, f s = 0) :
    ∫ s in a..b, f s = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun s hs => hf s hs)]
  simp

theorem cylStreamDecomp : CylStreamDecomp := by
  intro c Ψ hΨ χ hχ hχint
  have h0 := hΨ.comp 0
  have h1 := hΨ.comp 1
  obtain ⟨L0, hL0⟩ := h0.bounded
  obtain ⟨L1, hL1⟩ := h1.bounded
  obtain ⟨Lχ, _, hLχ⟩ := UnforcedLeray.Cyl.OneD.Test.exists_bound hχ
  obtain ⟨R, hRL0, hRL1, hRχ, hR0⟩ : ∃ R : ℝ, L0 < R ∧ L1 < R ∧ Lχ < R ∧ 0 ≤ R :=
    ⟨|L0| + |L1| + |Lχ| + 1,
      by linarith [le_abs_self L0, abs_nonneg L1, abs_nonneg Lχ],
      by linarith [le_abs_self L1, abs_nonneg L0, abs_nonneg Lχ],
      by linarith [le_abs_self Lχ, abs_nonneg L0, abs_nonneg L1],
      by positivity⟩
  have hfl : CylFluxConst := cylFluxConst
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ s, Ψ (0, s) 0 := ⟨_, rfl⟩
  have hflux : ∀ q : ℝ, ∫ s, Ψ (q, s) 0 = m := fun q => by
    rw [hm]; exact hfl c Ψ hΨ q
  obtain ⟨g, hg⟩ : ∃ g : ℝ × ℝ → ℝ, ∀ z, g z = Ψ z 0 - m * χ z.2 :=
    ⟨fun z => Ψ z 0 - m * χ z.2, fun z => rfl⟩
  have hgsmooth : ContDiff ℝ ∞ g := by
    have e : g = fun z => Ψ z 0 - m * χ z.2 := funext hg
    rw [e]
    exact h0.smooth.sub (contDiff_const.mul (hχ.smooth.comp contDiff_snd))
  have hgbound : ∀ z : ℝ × ℝ, R ≤ |z.2| → g z = 0 := by
    intro z hz
    have a1 : Ψ z 0 = 0 := hL0 z (lt_of_lt_of_le hRL0 hz)
    have a2 : χ z.2 = 0 := hLχ z.2 (le_of_lt (lt_of_lt_of_le hRχ hz))
    rw [hg, a1, a2]; ring
  have hper : ∀ q s : ℝ, g (q + c, s) = g (q, s) := by
    intro q s
    rw [hg, hg]
    have a : Ψ (q + c, s) 0 = Ψ (q, s) 0 := h0.periodic (q, s)
    show Ψ (q + c, s) 0 - m * χ s = Ψ (q, s) 0 - m * χ s
    rw [a]
  obtain ⟨hΦsmooth, hΦη, hΦq⟩ := smoothPrimEta g R hgsmooth (fun z hz => hgbound z hz.le)
  -- the integral of `g(q, ·)` over `(-R, R)` vanishes
  have hgint : ∀ q : ℝ, ∫ s in (-R)..R, g (q, s) = 0 := by
    intro q
    have A : ∫ s in (-R)..R, Ψ (q, s) 0 = m :=
      (csd_int_eq (fun s => Ψ (q, s) 0) R hR0
        (fun s hs => hL0 (q, s) (lt_of_lt_of_le hRL0 hs))).trans (hflux q)
    have B : ∫ s in (-R)..R, χ s = 1 :=
      (csd_int_eq χ R hR0 (fun s hs => hLχ s (le_of_lt (lt_of_lt_of_le hRχ hs)))).trans hχint
    have c1 : Continuous fun s : ℝ => Ψ (q, s) 0 :=
      h0.smooth.continuous.comp (continuous_const.prodMk continuous_id)
    have c2 : Continuous fun s : ℝ => m * χ s :=
      continuous_const.mul hχ.smooth.continuous
    rw [intervalIntegral.integral_congr (g := fun s => Ψ (q, s) 0 - m * χ s)
      (fun s _ => hg (q, s)),
      intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, A, B]
    ring
  have hcont : ∀ q : ℝ, Continuous fun s : ℝ => g (q, s) := fun q =>
    hgsmooth.continuous.comp (continuous_const.prodMk continuous_id)
  -- the stream function is a cylinder test
  have hPeriodic : ∀ z : ℝ × ℝ,
      (fun y : ℝ × ℝ => ∫ s in (-R)..y.2, g (y.1, s)) (z.1 + c, z.2) =
        (fun y : ℝ × ℝ => ∫ s in (-R)..y.2, g (y.1, s)) z := by
    intro z
    show ∫ s in (-R)..z.2, g (z.1 + c, s) = ∫ s in (-R)..z.2, g (z.1, s)
    simp only [hper]
  -- pointwise identity for the `q`-derivative of `g`
  have hpt : ∀ p : ℝ × ℝ,
      fderiv ℝ g p (1, 0) = -fderiv ℝ (fun y => Ψ y 1) p (0, 1) := by
    intro p
    have hgfun : g = fun y => Ψ y 0 - m * χ y.2 := funext hg
    have d0 : HasFDerivAt (fun y => Ψ y 0) (fderiv ℝ (fun y => Ψ y 0) p) p :=
      ((h0.smooth.differentiable (by simp)) p).hasFDerivAt
    have dχ : HasFDerivAt (fun y : ℝ × ℝ => χ y.2)
        (deriv χ p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      HasDerivAt.comp_hasFDerivAt p ((hχ.smooth.differentiable (by simp) p.2).hasDerivAt)
        hasFDerivAt_snd
    have hgd : HasFDerivAt g
        (fderiv ℝ (fun y => Ψ y 0) p - m • (deriv χ p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
      rw [hgfun]; exact d0.sub (dχ.const_mul m)
    rw [hgd.fderiv]
    have hd := hΨ.div_free p
    simp
    linarith
  refine ⟨fun z => ∫ s in (-R)..z.2, g (z.1, s), m, ⟨hΦsmooth, hPeriodic, ?_⟩, ?_, ?_⟩
  · -- vanishing for large `|η|`
    refine ⟨R, fun z hz => ?_⟩
    show ∫ s in (-R)..z.2, g (z.1, s) = 0
    rcases lt_abs.mp hz with h | h
    · -- `z.2 > R`
      have hi1 : IntervalIntegrable (fun s => g (z.1, s)) volume (-R) R :=
        (hcont z.1).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun s => g (z.1, s)) volume R z.2 :=
        (hcont z.1).intervalIntegrable _ _
      have h2 : ∫ s in R..z.2, g (z.1, s) = 0 := by
        apply csd_int_zero
        intro s hs
        apply hgbound (z.1, s)
        show R ≤ |s|
        rw [Set.mem_uIcc] at hs
        rcases hs with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · rw [abs_of_nonneg (by linarith)]; linarith
        · exfalso; linarith
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hgint z.1, h2, add_zero]
    · -- `z.2 < -R`
      apply csd_int_zero
      intro s hs
      apply hgbound (z.1, s)
      show R ≤ |s|
      rw [Set.mem_uIcc] at hs
      rcases hs with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · exfalso; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
  · -- `Ψ₀ = ∂_η Φ + m χ`
    intro z
    rw [hΦη z, hg z]
    ring
  · -- `Ψ₁ = -∂_q Φ`
    intro z
    rw [hΦq z]
    have hint : ∫ s in (-R)..z.2, fderiv ℝ g (z.1, s) (1, 0) =
        ∫ s in (-R)..z.2, -fderiv ℝ (fun y => Ψ y 1) (z.1, s) (0, 1) :=
      intervalIntegral.integral_congr (fun s _ => hpt (z.1, s))
    have hb : Ψ (z.1, -R) 1 = 0 := by
      apply hL1 (z.1, -R)
      show L1 < |-R|
      rw [abs_neg, abs_of_nonneg hR0]; exact hRL1
    have hFTC : ∫ s in (-R)..z.2, fderiv ℝ (fun y => Ψ y 1) (z.1, s) (0, 1) =
        Ψ (z.1, z.2) 1 - Ψ (z.1, -R) 1 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Ψ (z.1, s) 1)
      · intro s _
        have hΨ1 : HasFDerivAt (fun y => Ψ y 1) (fderiv ℝ (fun y => Ψ y 1) (z.1, s)) (z.1, s) :=
          ((h1.smooth.differentiable (by simp)) (z.1, s)).hasFDerivAt
        have hl : HasDerivAt (fun t : ℝ => (z.1, t)) ((0 : ℝ), (1 : ℝ)) s :=
          (hasDerivAt_const s z.1).prodMk (hasDerivAt_id' s)
        exact hΨ1.comp_hasDerivAt s hl
      · have hcf : Continuous (fderiv ℝ (fun y => Ψ y 1)) :=
          h1.smooth.continuous_fderiv (by simp)
        exact ((hcf.comp (continuous_const.prodMk continuous_id)).clm_apply
          continuous_const).intervalIntegrable _ _
    rw [hint, intervalIntegral.integral_neg, hFTC, hb, Prod.mk.eta]
    ring
