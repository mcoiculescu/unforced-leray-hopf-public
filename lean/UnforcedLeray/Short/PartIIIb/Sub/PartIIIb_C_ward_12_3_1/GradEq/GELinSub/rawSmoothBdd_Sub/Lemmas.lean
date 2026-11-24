import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props

/-!
# `RawSmoothBdd` decomposed into source facts (task `PartIII-b:C/ward/12/3/1/2/6/1`)

Source `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Joint `C^∞` smoothness of `(τ,y) ↦ raw τ y` on `ℝ × ℝ³` in the background regime
(source 1214, 1305-1325, smoothness through the axis for positive time, with the exp-scaling
`t = e^{Rτ/…}` ring-lift change of variable). -/
def RawJointSmooth : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)

/-- Periodicity of `raw` in `τ` with period `p.period = 2c/R` on all of `ℝ³` (source 1215-1217:
discrete self-similarity; off the axis this is `raw_periodic_off`, and the axis is the closure
of its complement by continuity). -/
def RawPeriodicAll : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ τ y, p.raw (τ + p.period) y = p.raw τ y

/-- Globally bounded fixed spatial derivatives of `raw τ` of orders `k = 0, 1, 2` (`k : Fin 3`: the
orders used by `GELinField` and by the inlet source `inletFn`), below one threshold `ν₀`
(source 1217-1219, 1322-1325; the bounds `P_k` of `RingBoundedDerivs` at the order `2`). -/
def RawDerivBdd : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ k : Fin 3, ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space),
        ‖iteratedFDeriv ℝ (k : ℕ) (p.raw τ) y‖ ≤ C

theorem rawSmoothBdd_of (h1 : RawJointSmooth) (h2 : RawPeriodicAll) (h3 : RawDerivBdd) :
    RawSmoothBdd := by
  intro dm dp hdm
  obtain ⟨a, ha, H1⟩ := h1 dm dp hdm
  obtain ⟨b, hb, H2⟩ := h2 dm dp hdm
  obtain ⟨c, hc, H3⟩ := h3 dm dp hdm
  refine ⟨min a (min b c), lt_min ha (lt_min hb hc), fun p d hreg hν => ?_⟩
  exact ⟨H1 p d hreg (hν.trans (min_le_left _ _)),
    H2 p d hreg (hν.trans ((min_le_right _ _).trans (min_le_left _ _))),
    H3 p d hreg (hν.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩

end UnforcedLeray.Short.PartIIIb.Concrete
