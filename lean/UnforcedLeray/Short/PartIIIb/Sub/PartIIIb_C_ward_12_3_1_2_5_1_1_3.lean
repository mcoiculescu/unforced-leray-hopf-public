import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1

/-!
# `InletFnEnvelope` (decomposition into a far-field and a near-axis leaf)

Source `the November 2 reference manuscript`
lines 2542-2551 (large radius: unprojected derivatives bounded by
`C_{k,N} ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`; on `ϱ < R` the all-age heat expansion gives arbitrary axial
decay and the inlet cutoff vanishes near the axis; uniform in phase), 2563-2569, 1206-1222.

`inletFn = -∂_j(L₀E_i + (raw·∇)E_i + (E_i·∇)raw)` involves up to three `y`-derivatives of `E_i`
(with the weight `y` of `y·∇` in `L₀`) and up to two of `raw`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Far field** (2542-2548, `k = 0`, `N = 2`): for some `R₀ > 0` and `C`, uniformly in the phase
`τ ∈ (0,P]`, `‖F_n(τ,y)‖ ≤ C ϱ^{-3}(1+|y₃|/ϱ)^{-2}` for `ϱ = |y'| > R₀`. -/
def InletFnFarDecay : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) →
      ‖inletFn p i j (τ, y)‖ ≤ C * (Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ))

/-- **Near the axis** (2545-2549): for every `R₀ > 0` there is `C` with
`‖F_n(τ,y)‖ ≤ C (1+|y₃|)^{-2}` for `τ ∈ (0,P]` and `ϱ ≤ R₀` (smooth through the axis; all-age heat
expansion gives arbitrary axial decay; inlet cutoff vanishes near the axis). -/
def InletFnNearBound : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3) (R0 : ℝ), 0 < R0 → ∃ C : ℝ,
    ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0 →
      ‖inletFn p i j (τ, y)‖ ≤ C * (1 + |y 2|) ^ (-2 : ℝ)

theorem inletFnEnvelope_of (h1 : InletFnFarDecay) (h2 : InletFnNearBound) :
    InletFnEnvelope := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hreg hν hm z g hg i j => ?_⟩
  obtain ⟨Cf, R0, hR0, hf⟩ := H1 p d hreg (hν.trans (min_le_left _ _)) hm z g hg i j
  obtain ⟨Cn, hn⟩ := H2 p d hreg (hν.trans (min_le_right _ _)) hm z g hg i j R0 hR0
  refine ⟨max Cf Cn, R0, hR0, fun τ hτ y => ?_⟩
  unfold cylProfile
  by_cases hy : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R0
  · rw [if_pos hy]
    have hpos : 0 < (1 + |y 2|) ^ (-2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    exact (hn τ hτ y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le)
  · rw [if_neg hy]
    have hy' : R0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := not_le.mp hy
    have hρ : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := hR0.trans hy'
    have hpos : 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ (-3 : ℝ) *
        (1 + |y 2| / Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ (-2 : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos (by positivity) _)
    exact (hf τ hτ y hy').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)

end UnforcedLeray.Short.PartIIIb.Concrete
