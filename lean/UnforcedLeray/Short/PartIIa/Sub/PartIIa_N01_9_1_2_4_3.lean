import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4

/-!
# `PartII-a:N01/9/1/2/4/3` (decomposition): `HeatIntRegular`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  Continuity of the heat integral on all of
`ℝ × ℝ²` splits into vanishing for `s < s₁` and continuity on the open set `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)

/-- **(R1)** The heat integral vanishes for `s < s₁` when `F = 0` there (all integrands vanish:
`F(σ,·) = 0` for `σ` between `0` and `s`, `periodize` and `planeHeat` of `0` are `0`). -/
def HeatIntZero : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → UnforcedLeray.B0223.MeridC, ∀ s₁ : ℝ, 0 < s₁ →
    (∀ p : Profile, p.1 < s₁ → F p = 0) → ∀ p : Profile, p.1 < s₁ → smoothHeatInt c ν μ F p = 0

/-- **(R2)** The heat integral is continuous on `s > 0` (substitute `σ = s t`; the integrand is
jointly continuous in `(s,q,η)` for `t < 1`, bounded by `sup |F|`; dominated convergence). -/
def HeatIntContPos : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → UnforcedLeray.B0223.MeridC,
    IsSmoothForceFn c F → ContinuousOn (smoothHeatInt c ν μ F) (Ioi (0 : ℝ) ×ˢ univ)

/-- **(R3)** For `s > 0` each component is differentiable in `(q,η)` (differentiate `planeHeat`
under the integral; derivatives of `F` are bounded). -/
def HeatIntDiffPos : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → UnforcedLeray.B0223.MeridC,
    IsSmoothForceFn c F →
      ∀ s : ℝ, 0 < s → ∀ i : Fin 2,
        Differentiable ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i)

/-- **(R4)** The `(q,η)`-derivative is jointly continuous on `s > 0` (it is the heat integral of
the derivative of `F`; same argument as R2). -/
def HeatIntFderivCont : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → UnforcedLeray.B0223.MeridC,
    IsSmoothForceFn c F → ∀ i : Fin 2, ContinuousOn
      (fun p : Chart => fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (p.1, y) i) p.2)
      (Ioi (0 : ℝ) ×ˢ univ)

theorem heatIntRegular_of (h0 : HeatIntZero) (h1 : HeatIntContPos) (h2 : HeatIntDiffPos)
    (h3 : HeatIntFderivCont) : HeatIntRegular := by
  intro c ν hc hν μ F hF
  refine ⟨?_, h2 c ν hc hν μ F hF, h3 c ν hc hν μ F hF⟩
  obtain ⟨_, _, s₁, s₂, R, hs₁, hz⟩ := hF
  have hz0 : ∀ p : Profile, p.1 < s₁ → F p = 0 := fun p hp => hz p (Or.inl hp)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 < s₁
  · have hev : (smoothHeatInt c ν μ F) =ᶠ[𝓝 p] fun _ => (0 : UnforcedLeray.B0223.MeridC) := by
      have : {x : Profile | x.1 < s₁} ∈ 𝓝 p := (isOpen_lt continuous_fst continuous_const).mem_nhds hp
      filter_upwards [this] with x hx using h0 c ν hc hν μ F s₁ hs₁ hz0 x hx
    exact continuousAt_const.congr hev.symm
  · have hpos : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
      ⟨lt_of_lt_of_le hs₁ (not_lt.1 hp), trivial⟩
    exact (h1 c ν hc hν μ F ⟨‹_›, ‹_›, s₁, s₂, R, hs₁, hz⟩).continuousAt (hopen.mem_nhds hpos)

end UnforcedLeray.Short.PartIIa.N01
