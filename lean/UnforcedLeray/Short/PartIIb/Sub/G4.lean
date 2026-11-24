import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Part II-b, task `PartII-b:G4`: the affine inlet columns (conditional)

Source of record: `the November 2 reference manuscript`, lines 2347-2383
(`Exact geometry and the nonlinear correction`, display `short-bg:affine` at 2383), and the
sentences after it: "The quadratic inlet source has the same bound with `|α|²`, and
`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`".


the three assertions of the source are given exact Lean statements:

* `AffineColumnComparison` (first display of `short-bg:affine`):
  `‖𝒞_ε - 𝒞_0‖_{ℝ²→H_p} ≤ ε 𝒫_ν`, `𝒞_ε - 𝒞_0 = ε s r_ε` (`r_ε` smooth at zero, compact in upper
  age, polynomial weighted bounds); the columns are the bounded operators `IsCop`, `IsC0op` of
  `StatementsMixed.lean`;
* `InletSourceBound` (second display, `inlet_source_bound`):
  `‖A_0 E_εα + 𝔓 B_{V_0} E_εα‖_{W^{1,Y_p}} ≤ 𝒫_ν R^{2/p}|α|` for the unit coordinates
  `α = e_i`: the functional `Φ ↦ ⟪L_0ᵗΦ + (∇V_0)ᵀΦ - (V_0·∇)Φ, E_i⟫` on solenoidal tests (the
  inlet part of `Params.OrdRel`) is represented by `g_i ∈ Y` with a weak spatial gradient in
  `Yq`, the `Y`-norms of `g_i` and of `∇ g_i` being `≤ 𝒫_ν R^{2/p}`, `p = 11/4`;
* `InletSupBound`: `‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|` (`E_εα = Σ α_i E_i`).

## Statement defect found upstream (author/organizer action)

`p.mode` (the planar eigenvorticity profile `h`, `q = h(r)e^{2iϑ}`) and `p.ageCut` (`Σ`, with
`H = Σ/ν`) are *free* fields of `Params`, and `BgRegime` does not constrain them. But the columns
`𝒞_ε, 𝒞_0` and the inlet `E_ε` are *linear in `p.mode`* (`frozenStream = 2Re P_c Δ⁻¹ q`) and
depend on `Σ`; so any bound `‖𝒞_ε - 𝒞_0‖ ≤ C ν^{-k} ε` with `C` chosen before `∀ p` is false for
`p.mode := M · q`, `M → ∞` (both columns scale by `M`). The quantifiers in `GlobalOperatorComparison`,
`StrongRegularity`, `BackgroundResult`, `BackgroundOutput`, ... (`StatementsNonlinear.lean`) have
the same flaw; they must be restated with a fixed `Σ > 0` and a fixed eigenpair
`IsGrowingEigenpair λ q` (`Blueprint/Construction/Planar.lean`), `p.ageCut = Σ`, `p.mode = q`,
the constants depending on `(Σ, q)`. The statements below are the corrected forms.

Proved here: `affineInletFacts_of` (the conjunction; no sorry). Leaves: `AffineColumnComparison`
(`PartII-b:G4/2`), `InletSourceBound` (`PartII-b:G4/3`), `InletSupBound` (`PartII-b:G4/4`);
shared ingredient `FrozenStreamBounds` (`PartII-b:G4/1`) with the cotangent-series identity
`SumInvSqShift` (`PartII-b:G4/1a`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Periodization of the harmonic part** (SP 2349-2352): for `c > 0` and `z ∈ ℂ` with
`z ∉ cℤ`, `Σ_{n∈ℤ} (z + nc)^{-2} = (π/c)² / sin²(π z/c)`. (Differentiate Mathlib's
`Complex.cot_series_rep`: `π cot(π x) = 1/x + Σ_{n≥1} (1/(x-n) + 1/(x+n))`.) -/
def SumInvSqShift : Prop :=
  ∀ (c : ℝ) (z : ℂ), 0 < c → (∀ n : ℤ, z + n * c ≠ 0) →
    HasSum (fun n : ℤ => ((z + n * c) ^ 2)⁻¹)
      (((Real.pi : ℂ) / c) ^ 2 * (Complex.sin (Real.pi * z / c) ^ 2)⁻¹)

/-- **The periodized eigenstream** (SP 2347-2358): for the growing eigenprofile `q`, the periodized
stream `P_c Δ⁻¹ q` (`periodicStream q c`, complex valued on `(q, η)`) is `C^∞` and all of its
fixed derivatives have exponential transverse decay with polynomial `c` costs:
`‖D^j periodicStream q c (ξ, η)‖ ≤ C c^N e^{-κ|η|/c}` for `c ≥ 1`. (Gaussian eigenstream = harmonic
quadrupole `(π/c)² csc²` plus a Gaussian remainder outside a fixed core; apparent poles replaced
by the smooth core.) -/
def FrozenStreamBounds : Prop :=
  ∀ (lam : ℂ) (q : Planar.Profile), Planar.IsGrowingEigenpair lam q → ∀ j : ℕ,
    ∃ (C κ : ℝ) (N : ℕ), 0 < C ∧ 0 < κ ∧ ∀ c : ℝ, 1 ≤ c →
      ContDiff ℝ ∞ (periodicStream q c) ∧
      ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (periodicStream q c) x‖ ≤
        C * c ^ N * Real.exp (-(κ * |x.2| / c))

/-- **`affine_column_comparison`** (SP 2383, first display; proof 2347-2382): at a fixed slow age
`Σ` and a fixed growing eigenpair `(λ, q)`, in the regime, for small `ν`: the unprojected complete
inlet column `𝒞_ε` exists as a bounded operator `ℝ² → H_p` (`IsCop`), and for every flat column
`𝒞_0` (`IsC0op`), `‖𝒞_ε - 𝒞_0‖ ≤ 𝒫_ν ε`. -/
def AffineColumnComparison : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      (∃ Ce : E2 →L[ℝ] HpR p.c, IsCop p Ce) ∧
      ∀ (Ce C0 : E2 →L[ℝ] HpR p.c), IsCop p Ce → IsC0op p C0 →
        ‖Ce - C0‖ ≤ C * (p.ν ^ k)⁻¹ * p.ε

/-- **`inlet_source_bound`** (SP 2383, second display): for each inlet `E_i`, the complete inlet
source (the `α = e_i` part of `Params.OrdRel`, tested against solenoidal phase tests) is
represented by `g ∈ Y` with a weak spatial gradient `∇g ∈ Yq` (tested against phase tests:
`⟪-∂_jΦ, g⟫ = ⟪Φ, ∂_j g⟫`), and `‖g‖_Y + Σ_j ‖∂_j g‖_Y ≤ 𝒫_ν R^{2/p}`, `p = 11/4`. -/
def InletSourceBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ i : Fin 2, ∃ (g : p.Y) (G : Fin 3 → Yq p.period q0E),
        (∀ Φ, IsSolTest p.period Φ →
          phasePair p.period q0E Φ (g : Yq p.period q0E) =
            pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x) (p.Efun i)) ∧
        (∀ j : Fin 3, HasPtwOp p.period (fun Φ x => -(dy j Φ x))
          (fun x => rep (g : Yq p.period q0E) x.1 x.2) (fun x => rep (G j) x.1 x.2)) ∧
        ‖g‖ + ∑ j : Fin 3, ‖G j‖ ≤ C * (p.ν ^ k)⁻¹ * p.R ^ (2 / bgp)

/-- **`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`** (SP after 2383): every fixed Cartesian derivative of the
affine inlet `E_εα = Σ α_i E_i` is bounded by `𝒫_{ν,j}|α|`, uniformly in the phase and the point. -/
def InletSupBound : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (α : E2) (τ : ℝ) (y : Space),
        ‖iteratedFDeriv ℝ j (fun z => ∑ i : Fin 2, α i • p.inlet i τ z) y‖ ≤
          C * (p.ν ^ k)⁻¹ * ‖α‖

/-- The three assertions of `short-bg:affine` and the sentence after it. -/
def AffineInletFacts : Prop :=
  AffineColumnComparison ∧ InletSourceBound ∧ InletSupBound

/-- **`PartII-b:G4`, conditional form.** -/
theorem affineInletFacts_of (hA : AffineColumnComparison) (hB : InletSourceBound)
    (hC : InletSupBound) : AffineInletFacts :=
  ⟨hA, hB, hC⟩

end UnforcedLeray.Short.IIb
