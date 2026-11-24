import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_3

/-!
# `PartII-a:N01/9/1/2/4/3` (helper): vanishing of the heat integral before the support

The target `heatIntZero : HeatIntZero` is FALSE as stated: `HeatIntZero` quantifies over every
`s₁ : ℝ`, but for `s₁ ≤ 0` the hypothesis `F = 0` on `{s < s₁}` does not force `F(σ,·) = 0` for
`σ ∈ (p.1, 0]`, and the heat integral does not vanish there (planeHeat with `θ ≤ 0` is the identity).
Counterexample: `c = ν = 1`, `μ = 1`, `s₁ = -1`, `F p = if -1 ≤ p.1 then e₀ else 0`, `p = (-2, 0, 0)`;
the integral is `(1/2) e₀ ≠ 0`.

`HeatIntZero` now carries the extra hypothesis `0 < s₁` (which holds in
`IsSmoothForceFn`, where `0 < s₁` is part of the definition).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

theorem heatIntZero : UnforcedLeray.Short.PartIIa.N01.HeatIntZero := by
  intro c ν hc hν μ F s₁ hs₁ hz p hp
  have hzero : ∀ σ ∈ Set.uIcc (0 : ℝ) p.1,
      ((σ / p.1 : ℝ) : ℂ) ^ μ • UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
        (fun z => UnforcedLeray.B0220.periodize c
          (fun q : UnforcedLeray.B0220.Profile => (q.1)⁻¹ • F q) (σ, z)) p.2 = 0 := by
    intro σ hσ
    have hσs : σ < s₁ := by
      rcases Set.mem_uIcc.1 hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hF0 : (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c
          (fun q : UnforcedLeray.B0220.Profile => (q.1)⁻¹ • F q) (σ, z))
        = fun _ => (0 : UnforcedLeray.B0223.MeridC) := by
      funext z
      show (σ)⁻¹ • F (σ, UnforcedLeray.B0220.reduceIoc c z.1, z.2) = 0
      rw [hz _ hσs, smul_zero]
    rw [hF0, UnforcedLeray.B0225.planeHeat_zero]
    simp
  unfold smoothHeatInt
  calc (∫ σ in (0 : ℝ)..p.1, ((σ / p.1 : ℝ) : ℂ) ^ μ •
          UnforcedLeray.B0224.planeHeat (ν * (p.1 - σ))
            (fun z => UnforcedLeray.B0220.periodize c
              (fun q : UnforcedLeray.B0220.Profile => (q.1)⁻¹ • F q) (σ, z)) p.2)
      = ∫ σ in (0 : ℝ)..p.1, (0 : UnforcedLeray.B0223.MeridC) :=
        intervalIntegral.integral_congr (fun σ hσ => hzero σ hσ)
    _ = 0 := by simp

end UnforcedLeray.Short.PartIIa.N01
