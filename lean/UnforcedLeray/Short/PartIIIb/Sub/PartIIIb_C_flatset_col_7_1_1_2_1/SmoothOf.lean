import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# `DuhamelSmooth` from five analytic facts (decomposition of
`PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth`)

Source `the November 2 reference manuscript`
1650-1656, 1684-1689.  Strategy (no heat equation): since `G(σ,·) = 0` for `σ < s₀`, substitute
`σ = s - τ`, so for `0 < s < S`
`duhamel ν μ G (s,x) i = ∫₀^S ρ(s,τ) • planeHeat (ν τ) (G(s-τ,·) i) x dτ`
with `ρ(s,τ) = θ(s-τ) ((s-τ)/s)^μ` where `θ` is a smooth cutoff (=1 on `[s₀,∞)`, =0 on `(-∞,s₀/2]`),
so that `ρ` is smooth on `s > 0` and the integrand is unchanged.  Then the integral is smooth in
`(s,x)` by differentiation under the integral sign, the Gaussian average having derivatives bounded
uniformly in `τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Smooth cut-off kernel `ρ(s,τ) = θ(s-τ) ((s-τ)/s)^μ`, `θ = smoothTransition((· - s₀/2)/(s₀/2))`. -/
def rhoCut (s0 μ : ℝ) (s τ : ℝ) : ℂ :=
  ((Real.smoothTransition (((s - τ) - s0 / 2) / (s0 / 2)) : ℝ) : ℂ) *
    (((((s - τ) / s : ℝ)) : ℂ) ^ (μ : ℂ))

/-- The Gaussian-averaged shifted field `(s,x) ↦ planeHeat (ν τ) (G(s-τ,·) i) x`. -/
def heatH (ν : ℝ) (G : Chart → Fin 2 → ℝ) (i : Fin 2) (τ : ℝ) :
    ℝ × (ℝ × ℝ) → ℂ :=
  fun y => UnforcedLeray.B0224.planeHeat (ν * τ) (fun z => ((G (y.1 - τ, z) i : ℝ) : ℂ)) y.2

/-- **Shift** (source 1650-1656): for `G` supported in `s ≥ s₀`, `0 < s < S`. -/
def DuhamelShift : Prop :=
  ∀ (c ν μ : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → ∃ s0 : ℝ, 0 < s0 ∧
    ∀ (S s : ℝ), 0 < s → s < S → ∀ (x : ℝ × ℝ) (i : Fin 2),
      duhamel ν μ G (s, x) i = ∫ τ in (0 : ℝ)..S, rhoCut s0 μ s τ * heatH ν G i τ (s, x)

/-- `ρ` is smooth on `s > 0`. -/
def RhoCutSmooth : Prop :=
  ∀ (s0 μ : ℝ), 0 < s0 →
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => rhoCut s0 μ p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ)

/-- Each slice `heatH ν G i τ`, `τ ≥ 0`, is smooth in `(s,x)`. -/
def HeatSmooth : Prop :=
  ∀ (c ν : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ i : Fin 2,
    ∀ τ : ℝ, 0 ≤ τ → ContDiff ℝ ∞ (heatH ν G i τ)

/-- All derivatives of `heatH` are bounded uniformly in `τ ≥ 0` (Gaussian has mass one,
derivatives of `G` are bounded by `IsDriving`). -/
def HeatBound : Prop :=
  ∀ (c ν : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ i : Fin 2, ∀ n : ℕ,
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ y, ‖iteratedFDeriv ℝ n (heatH ν G i τ) y‖ ≤ C

/-- Joint continuity in `(τ,y)` of every `y`-derivative of `heatH`, `τ ≥ 0`. -/
def HeatCont : Prop :=
  ∀ (c ν : ℝ) (G : Chart → Fin 2 → ℝ), IsDriving c G → 0 < ν → ∀ i : Fin 2, ∀ n : ℕ,
    ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ n (heatH ν G i q.1) q.2)
      (Ici (0 : ℝ) ×ˢ univ)

/-- **Differentiation under the integral** (generic): `ρ` smooth on `s > 0`, `H τ` smooth with
derivatives bounded uniformly for `τ ∈ [0,S]` and jointly continuous in `(τ,y)`; then
`y ↦ ∫₀^S ρ(y.1,τ) H τ y dτ` is smooth on `0 < y.1 < S`. -/
def ParamIntegralSmooth : Prop :=
  ∀ (S : ℝ) (ρ : ℝ × ℝ → ℂ) (H : ℝ → ℝ × (ℝ × ℝ) → ℂ),
    ContDiffOn ℝ ∞ ρ (Ioi (0 : ℝ) ×ˢ univ) →
    (∀ τ, 0 ≤ τ → ContDiff ℝ ∞ (H τ)) →
    (∀ n : ℕ, ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ y, ‖iteratedFDeriv ℝ n (H τ) y‖ ≤ C) →
    (∀ n : ℕ, ContinuousOn (fun q : ℝ × (ℝ × (ℝ × ℝ)) => iteratedFDeriv ℝ n (H q.1) q.2)
      (Ici (0 : ℝ) ×ˢ univ)) →
    ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => ∫ τ in (0 : ℝ)..S, ρ (y.1, τ) * H τ y)
      (Ioo (0 : ℝ) S ×ˢ univ)

theorem duhamelSmooth_of (hSh : DuhamelShift) (hρ : RhoCutSmooth) (hS : HeatSmooth)
    (hB : HeatBound) (hC : HeatCont) (hP : ParamIntegralSmooth) : DuhamelSmooth := by
  intro c ν μ G hG hν i
  obtain ⟨s0, hs0, hsh⟩ := hSh c ν μ G hG
  have hloc : ∀ S : ℝ, 0 < S →
      ContDiffOn ℝ ∞ (fun p => duhamel ν μ G p i) (Ioo (0 : ℝ) S ×ˢ univ) := by
    intro S hSpos
    have h1 := hP S (fun p => rhoCut s0 μ p.1 p.2) (heatH ν G i) (hρ s0 μ hs0)
      (hS c ν G hG hν i) (hB c ν G hG hν i) (hC c ν G hG hν i)
    refine h1.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hsh S s hs.1 hs.2 x i
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨s, x⟩ ⟨hs, -⟩
  refine ⟨Ioo 0 (s + 1) ×ˢ univ, ?_, ⟨⟨hs, by linarith [show (0:ℝ) < s from hs]⟩, trivial⟩, ?_⟩
  · exact isOpen_Ioo.prod isOpen_univ
  · refine (hloc (s + 1) (by linarith [show (0:ℝ) < s from hs])).mono ?_
    intro p hp
    exact hp.2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
