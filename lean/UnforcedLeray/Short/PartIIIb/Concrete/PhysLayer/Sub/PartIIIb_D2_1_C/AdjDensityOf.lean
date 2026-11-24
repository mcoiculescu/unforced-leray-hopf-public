import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1

/-!
# `FWUAdjDensity`: decomposition into truncation, mollification, triangle inequality

Source: `the November 2 reference manuscript` lines 1351-1362
(`bg:common-body-graph` at `r = 2`, the adjoint graph domain) and 1556-1583.
Route: (a) solenoidal stream-potential cutoff `curl(χₙ ψ)` stays in `FWUAdjDom` and has
`y`-compact support; (b) mollification in `(τ, y)` (periodic in `τ`) of a `y`-compactly supported
element gives `IsSolTest` functions converging in the adjoint graph norm; (c) diagonal argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- `Φ` has `y`-compact support: it vanishes for `‖y‖ ≥ R`, for some `R`, at every phase `τ`. -/
def YCompactSupp (Φ : ℝ × Space → CVec3) : Prop :=
  ∃ R : ℝ, ∀ τ y, R ≤ ‖y‖ → Φ (τ, y) = 0

/-- **Truncation** (source 1351-1362, 1361; stream-potential solenoidal cutoff `curl(χₙ ψ)`,
reusing `Cons.C03.Concrete.isSolTest_projectedPotentialCurlCutoff`): an element `Φ` of the adjoint
graph domain with `(μ + L₀ᵗ)Φ = g` is approximated by `y`-compactly supported elements `Φ'` of the
adjoint graph domain, with `(μ + L₀ᵗ)Φ' = g'`, `‖g' - g‖_{Y_2} < ε`. -/
def FWUAdjTrunc : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → ∀ ε : ℝ, 0 < ε →
      ∃ Φ' g' : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ' g' ∧ YCompactSupp Φ' ∧
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => g' x - g x) < ENNReal.ofReal ε

/-- **Mollification** (source 1351-1362, 1556-1583; mollification in `y` and, periodically, in
`τ`; reusing PartIIb `SolTestMollIsSolTest`): a `y`-compactly supported element `Φ` of the adjoint
graph domain with `(μ + L₀ᵗ)Φ = g` is approximated in the adjoint graph norm by solenoidal phase
tests `Ψ` with `(μ + L₀ᵗ)Ψ ∈ Y_2`, `‖(μ + L₀ᵗ)Ψ - g‖_{Y_2} < ε`. -/
def FWUAdjMoll : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    ∀ Φ g : ℝ × Space → CVec3, FWUAdjDom P ν μ Φ g → YCompactSupp Φ → ∀ ε : ℝ, 0 < ε →
      ∃ Ψ : ℝ × Space → CVec3, IsSolTest P Ψ ∧
        UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x) ∧
        UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x - g x) < ENNReal.ofReal ε

/-- **Triangle inequality** for the `Y_2` norm `phaseLpNorm P 2` (Minkowski in `L²` of the cell
`(0,P] × ℝ³` with the normalised measure), for measurable fields. -/
def PhaseLpTri2 : Prop :=
  ∀ (P : ℝ) (a b c : ℝ × Space → CVec3), 0 < P →
    AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
    AEStronglyMeasurable c volume →
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => a x - c x) ≤
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => a x - b x) +
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => b x - c x)

theorem fwuAdjDensity_of (h1 : FWUAdjTrunc) (h2 : FWUAdjMoll) (h3 : PhaseLpTri2) :
    FWUAdjDensity := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ
  have key : ∀ n : ℕ, ∃ Ψ : ℝ × Space → CVec3, IsSolTest P Ψ ∧
      UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x) ∧
      UnforcedLeray.Short.IIb.phaseLpNorm P 2
        (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x - g x) <
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have he : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    obtain ⟨Φ', g', hΦ', hsupp, hg'⟩ := h1 P ν μ hP hP1 hν hμ Φ g hΦ _ he
    obtain ⟨Ψ, hΨ, hmem, hnorm⟩ := h2 P ν μ hP hP1 hν hμ Φ' g' hΦ' hsupp _ he
    refine ⟨Ψ, hΨ, hmem, ?_⟩
    have htri := h3 P (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x) g' g hP hmem.meas
      hΦ'.mem_g.meas hΦ.mem_g.meas
    calc UnforcedLeray.Short.IIb.phaseLpNorm P 2
          (fun x => L0T ν Ψ x + (μ : ℂ) • Ψ x - g x)
        ≤ _ := htri
      _ < ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1))) + ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1))) :=
          ENNReal.add_lt_add hnorm hg'
      _ = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
          rw [← ENNReal.ofReal_add he.le he.le]
          congr 1
          field_simp
          ring
  choose Φn hsol hmem hlt using key
  refine ⟨Φn, hsol, hmem, ?_⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) (fun n => (hlt n).le)

end UnforcedLeray.Short.PartIIIb.Concrete
