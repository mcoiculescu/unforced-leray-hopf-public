import UnforcedLeray.Blueprint.Construction.Steps
import UnforcedLeray.Cons.C01ReferenceChoice.Eigenpair
import UnforcedLeray.Cons.C01ReferenceChoice.Adjoint
import UnforcedLeray.Cons.C01ReferenceChoice.Oscillator
import UnforcedLeray.Cons.C01ReferenceChoice.Pairing
import UnforcedLeray.Cons.C01ReferenceChoice.Mellin
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Step C1: the reference choice (`StepReferenceChoice`)

`paper/main.tex`, Theorems G1–G4 (lines 691–785) and the choice of `μ₀` (lines 13197–13213,
`eq:st18-t00755`, with `eq:m2-signed-invariant` at line 13217); blueprint units B0085 (G1),
B0099 (G3a), B0125 (G3b), B0134 (G4), B0881–B0883 (the choice of `μ₀`, `𝒞 ≢ 0`, the signed
coefficient).

`StepReferenceChoice F` (`Blueprint/Construction/Steps.lean`) depends only on the fields
`F.planar` and `F.σ₀` of a `ConstructionData` (`stepReferenceChoice_iff`). Those fields are
data to be chosen, so C1 is proved as an existence theorem for the planar data and `σ₀`
(`exists_referenceChoice`), and transported to any record carrying them
(`exists_stepReferenceChoice`, `stepReferenceChoice_of_eq`).

## What is proved

For the whole-line Rayleigh mode `F` at speed `c` produced by the compiled O8
(`Rayleigh.Evans.exists_wholeLine_growing_mode`, through B0034), with vorticity
`h = kφ/(Ω - c)` and `λ = -2ic`:
* G1 (`IsGrowingEigenpair λ h`) and `-2 < ω < 0` (`Eigenpair.lean`, no hypothesis);
* G3a's domain of `D`: `Dh ∈ X_G` (`Oscillator.lean`, no hypothesis; line 1516, B0095), from
  the closed form `Dh = F(4κ' + 4sκ'' + sκ' + 2κ + κ²) + F'(4κ' + κ/2)` and Gaussian bounds;
* G3a's nondegenerate pairing `J_q = ∫ h²/k r dr ≠ 0` (line 1518, B0096; `Pairing.lean`), by
  the compiled index lemma for the transferred phase-speed eigenvector (bypass B2(c));
* G3a's adjoint eigenvector: the explicit `q† = Gū/J̄`, `u = φ/(Ω - c)` (`eq:st18-t00066`) is
  a normalized `X_G`-adjoint eigenvector, by the Green symmetry (`Adjoint.lean`);
* G4's `ℓ(H) = M_q/J_q ≠ 0` (`eq:st18-t00109`, `Adjoint.lean`);
* `𝓛(μ) ≠ 0` on `μ > -5/2` (`couplingL_ne_zero`, `eq:st18-t00112`);
* `𝔐` is bounded on `X_G` (`eq:st18-t00110`) and the moment clause (`Quadrupole.lean`);
* from the G3b clauses: `𝓙` converges and is holomorphic on `Re μ > -3/2`, is continuous at
  every real `μ > -3/2` (B0131), is not identically zero (B0132, by Mathlib's Mellin
  inversion and `M_q ≠ 0`), and has a real point `σ₀ ∈ (1/16, 1/8)` with `𝓙(σ₀) ≠ 0` (identity
  theorem; lines 2019–2022, 13197–13213); hence `C₀ = 𝒞(σ₀) ≠ 0` (`Mellin.lean`).

## The named hypothesis (what is missing)

One statement the manuscript proves, stated for the whole-line modes of O8 and the explicit
adjoint `q† = h_X/J̄`:
* `CanonicalBranchHyp` (G3b, B0125 with B0118, B0119, B0124; lines 735–760, 1809–1890): a
  canonical branch `V_can` with the clauses of `IsCanonicalBranch`, whose quadrupole
  `Q_can(θ) = 𝔐(V_can(θ))` is continuous on `(0, ∞)` (line 745 "smooth at every positive `θ`";
  line 2006).

Main declarations (namespace `UnforcedLeray.Cons.C01`): `ReferenceChoice`,
`stepReferenceChoice_iff`, `CanonicalBranchHyp`, `CanonicalBranchXGHyp`,
`canonicalBranchHyp_of_XG`, `modeData`, `couplingL_ne_zero`,
`signedCoeff_ne_zero`, **`exists_referenceChoice_of_mode`**, **`exists_referenceChoice`**,
**`exists_stepReferenceChoice`**, `stepReferenceChoice_of_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Cons.C01

open Blueprint Blueprint.Planar ComplexODEC

/-- **C1 as a property of the planar data and `σ₀`**: G1–G4 for `P` (`IsPlanarReference`),
`-2 < ω < 0` (`eq:st18-t00008`), `σ₀ ∈ (1/16, 1/8)` with `𝒞(σ₀) ≠ 0` (`eq:st18-t00755`,
`eq:m2-signed-invariant`), and `𝓙` continuous at `σ₀`. Units B0085, B0882. -/
def ReferenceChoice (P : PlanarData) (σ₀ : ℝ) : Prop :=
  IsPlanarReference P ∧ P.eigenvalue.im ∈ Ioo (-2 : ℝ) 0 ∧ σ₀ ∈ Ioo (1 / 16 : ℝ) (1 / 8) ∧
    P.signedCoeff σ₀ ≠ 0 ∧ ContinuousAt P.mellinJ σ₀

/-- `StepReferenceChoice F` is `ReferenceChoice F.planar F.σ₀`: C1 involves no other field. -/
theorem stepReferenceChoice_iff (F : ConstructionData) :
    StepReferenceChoice F ↔ ReferenceChoice F.planar F.σ₀ := Iff.rfl

/-! ## The named hypotheses -/

/-- **G3b, the canonical branch** (`thm:ref-canonical-branch`, lines 735–760, proof lines
1809–1890; units B0125, B0118, B0119, B0124): for the G1 eigenpair `(λ, q) = (-2ic, h)` of a
whole-line mode, its `X_G`-adjoint eigenvector `q† = h_X/J̄_q` (`eq:st18-t00066`, normalized as
in `eq:st18-t00012`; `adjointMode`) and `κ = ⟨Dq, q†⟩`, there is a solution `V_can` of
`-∂_θV = (L₀ + θ⁻¹D)V` on `θ > 0` with the clauses of `IsCanonicalBranch` (smooth, in `X_G`,
bounded near `0`, `V_can(θ) = e^{-λθ}θ^{-κ}(q + O_{X_G}(θ⁻¹))`), whose quadrupole
`Q_can(θ) = 𝔐(V_can(θ))` is continuous on `(0, ∞)` (line 745: "smooth at every positive `θ`";
continuity of `Q_can` is used at line 2006). The `X_G`-continuity of `V_can` implies this clause
(`continuousOn_quadCurve`). -/
def CanonicalBranchHyp : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ), WholeLineData c F →
    ∃ V : ℝ → Profile, IsCanonicalBranch (-2 * Complex.I * c)
      (gaussianPairing (oscillatorD (modeVort c F)) (adjointMode c F)) (modeVort c F) V ∧
      ContinuousOn (fun θ => quadrupole (V θ)) (Ioi 0)

/-- The literal reading of G3b's "smooth at every positive `θ`" (line 745): the canonical
branch is continuous into `X_G`. It implies `CanonicalBranchHyp`
(`canonicalBranchHyp_of_XG`). -/
def CanonicalBranchXGHyp : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ), WholeLineData c F →
    ∃ V : ℝ → Profile, IsCanonicalBranch (-2 * Complex.I * c)
      (gaussianPairing (oscillatorD (modeVort c F)) (adjointMode c F)) (modeVort c F) V ∧
      IsXGContinuous V

/-- `X_G`-continuity of the branch gives continuity of its quadrupole (`𝔐` is bounded on
`X_G`, `eq:st18-t00110`). -/
theorem canonicalBranchHyp_of_XG (h : CanonicalBranchXGHyp) : CanonicalBranchHyp := by
  intro c F hF
  obtain ⟨V, hV, hVc⟩ := h c F hF
  exact ⟨V, hV, continuousOn_quadCurve hV.memXG hVc⟩

/-! ## The planar data of a mode and the nonvanishing factors -/

/-- The planar data `(λ, q, q†, V_can) = (-2ic, h, Gū/J̄, V)` of a whole-line mode. -/
def modeData (c : ℂ) (F : ℝ → ℂ) (V : ℝ → Profile) : PlanarData :=
  ⟨-2 * Complex.I * c, modeVort c F, adjointMode c F, V⟩

/-- **`𝓛(μ) ≠ 0`** for `μ > -5/2` (`eq:st18-t00112`, lines 2009–2017, unit B0133): `ℓ(H) ≠ 0`,
`Γ` has no zeros, and `λ ≠ 0`. -/
theorem couplingL_ne_zero (P : PlanarData) (hH : P.strainCoupling ≠ 0)
    (hlam : P.eigenvalue ≠ 0) {μ : ℝ} (hμ : -(5 / 2) < μ) : P.couplingL μ ≠ 0 := by
  have hpole : ∀ m : ℕ, (μ : ℂ) + 5 / 2 ≠ -m := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h'
    have : (5 / 2 : ℂ).re = 5 / 2 := by norm_num
    rw [this] at h'
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hG : Complex.Gamma ((μ : ℂ) + 5 / 2) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hpow : P.eigenvalue ^ ((μ : ℂ) + 5 / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hlam h.1
  exact div_ne_zero (mul_ne_zero hH hG) hpow

/-- `𝒞(μ) = (63πi/128)𝓛(μ)𝓙(μ) ≠ 0` when `𝓛(μ) ≠ 0` and `𝓙(μ) ≠ 0`
(`eq:m2-signed-invariant`, unit B0883). -/
theorem signedCoeff_ne_zero (P : PlanarData) {μ : ℝ} (hL : P.couplingL μ ≠ 0)
    (hJ : P.mellinJ μ ≠ 0) : P.signedCoeff μ ≠ 0 := by
  have hk : (63 * (Real.pi : ℂ) * Complex.I / 128) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero)
      (by norm_num)
    exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero hk hL) hJ

/-! ## C1 for the data of a mode -/

/-- **C1 for the data of a whole-line mode** (lines 691–785, 13197–13213; B0085, B0099, B0125,
B0134, B0882): if `V` is a canonical branch for the explicit adjoint whose quadrupole is
continuous on `(0, ∞)`, then some `σ₀ ∈ (1/16, 1/8)` makes `(modeData c F V, σ₀)` a reference
choice. -/
theorem exists_referenceChoice_of_mode {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F)
    (hre0 : 0 < c.re) (hre1 : c.re < 1)
    {V : ℝ → Profile}
    (hV : IsCanonicalBranch (-2 * Complex.I * c)
      (gaussianPairing (oscillatorD (modeVort c F)) (adjointMode c F)) (modeVort c F) V)
    (hVc : ContinuousOn (fun θ => quadrupole (V θ)) (Ioi 0)) :
    ∃ σ₀ : ℝ, ReferenceChoice (modeData c F V) σ₀ := by
  have hJ := directAdjointPairing_ne_zero hF
  have heig := isGrowingEigenpair_modeVort hF
  have hadj := isAdjointEigenvector_adjointMode hF hJ
  have hD := Osc.memXG_oscillatorD_modeVort hF
  have hcurve : CurveFacts (modeData c F V).canonical (modeData c F V).eigenvalue
      (modeData c F V).kappa (modeData c F V).mode :=
    ⟨heig.re_pos, heig.memXG, hV.memXG, hVc, hV.bounded_near_zero, hV.asymptotic⟩
  have hJne := exists_mellinJC_ne_zero hcurve (modeQuadrupole_ne_zero hF)
  obtain ⟨σ₀, hσ₀, hJσ⟩ := exists_mem_Ioo_mellinJ_ne_zero hcurve hJne
    (by norm_num : (1 / 16 : ℝ) < 1 / 8) (by norm_num)
  have hlam : (modeData c F V).eigenvalue ≠ 0 := by
    intro h
    have h1 := heig.re_pos
    have h2 : (-2 * Complex.I * c).re = 0 := by
      have : (modeData c F V).eigenvalue = -2 * Complex.I * c := rfl
      rw [← this, h, Complex.zero_re]
    linarith
  have hH : (modeData c F V).strainCoupling ≠ 0 := strainCoupling_adjointMode_ne_zero hF hJ
  have hfreq := (Rayleigh.Evans.growthRate_bounds hF.mode.upper_half_plane hre0 hre1).2
  refine ⟨σ₀, ⟨heig, hadj, hD, hV, fun θ hθ => integrableOn_moment (hV.memXG θ hθ),
    fun μ hμ => integrableOn_mellinJ_integrand hcurve hμ⟩, ⟨hfreq.1, hfreq.2⟩, hσ₀, ?_, ?_⟩
  · exact signedCoeff_ne_zero _
      (couplingL_ne_zero _ hH hlam (by linarith [hσ₀.1])) hJσ
  · exact continuousAt_mellinJ hcurve (by linarith [hσ₀.1])

/-- **Step C1, existence form** (lines 691–785, 13197–13213; units B0085, B0099, B0125, B0134,
B0881–B0883): under the one named hypothesis (G3b's canonical branch), there are planar data
`P` and `σ₀` satisfying C1. -/
theorem exists_referenceChoice (hcan : CanonicalBranchHyp) :
    ∃ (P : PlanarData) (σ₀ : ℝ), ReferenceChoice P σ₀ := by
  obtain ⟨c, -, hre0, hre1, F, hF⟩ := exists_wholeLineData
  obtain ⟨V, hV, hVc⟩ := hcan c F hF
  obtain ⟨σ₀, h⟩ := exists_referenceChoice_of_mode hF hre0 hre1 hV hVc
  exact ⟨_, σ₀, h⟩

/-- C1 holds for every record carrying a reference choice. -/
theorem stepReferenceChoice_of_eq {F : ConstructionData} {P : PlanarData} {σ₀ : ℝ}
    (hP : F.planar = P) (hσ : F.σ₀ = σ₀) (h : ReferenceChoice P σ₀) : StepReferenceChoice F := by
  rw [stepReferenceChoice_iff, hP, hσ]
  exact h

/-- **Step C1 for a construction record** (`StepReferenceChoice`, lines 691–800, 13208, 13217,
13608–13617): under the one named hypothesis `CanonicalBranchHyp` (G3b), for every record `F`
some choice of its planar data and `σ₀` (all other fields unchanged) satisfies C1. -/
theorem exists_stepReferenceChoice (hcan : CanonicalBranchHyp) (F : ConstructionData) :
    ∃ (P : PlanarData) (σ₀ : ℝ), StepReferenceChoice { F with planar := P, σ₀ := σ₀ } := by
  obtain ⟨P, σ₀, h⟩ := exists_referenceChoice hcan
  exact ⟨P, σ₀, h⟩

end UnforcedLeray.Cons.C01
