import UnforcedLeray.Short.PartIIb.Sub.B1
import UnforcedLeray.Units.B0411.Operators
import UnforcedLeray.Lib.LerayLp.Cutoff
import NavierStokes.R3.ComparisonCutoffs

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/2` (organizer split): statements for `L0TSolApprox`

Source of record `the November 2 reference manuscript`:
lines 119-120 (the Cartesian Leray projection `𝔓 = ℙ`), 1356-1366 (`bg:common-body-graph`, the
projected inverse is the inverse applied to `ℙ f`), 1393-1400 and 1409-1412 (the kernel and
parabolic-annulus estimates), 1446-1455 (uniqueness by testing against radial cutoffs at radius
`N`: the drift cutoff is bounded, the diffusion cutoffs cost `N⁻¹, N⁻²`, all terms are tails) and
1464-1466 ("radial cutoffs approximate it in this graph, since their drift commutator is bounded on
an escaping annulus and their diffusion commutators tend to zero").

The target `L0TSolApprox` (`Sub/PartIII-b_C_ward_12_3_1_2_8_2_1.lean`) asks for solenoidal phase
tests `Ψₙ` with `⟪L₀ᵗΨₙ, d⟫ → ⟪L₀ᵗ(projSmooth Φ), d⟫` for every `d ∈ Y_{q₀}`.  The approximants are
the curl cutoffs of the Newton curl potentials of the real and imaginary parts,
`Ψₙ = curl(χ_{n+1} B₁) + i curl(χ_{n+1} B₂)`, `B_k = curl(N * φ_k)`
(`isSolTest_projectedTestNewtonVectorPotentialCurlCutoff`), and the limit is the smooth field
`curlRepC Φ = curl B₁ + i curl B₂`, which equals `projSmooth Φ` (both are smooth representatives
of `𝔓Φ`).  The cutoff error `E_R = curl((χ_R - 1) B)` vanishes for `|y| < R`, and for `|y| ≥ R` every
term of `L₀ᵗE_R` is `O((1+|y|)⁻²)`, given the derivative decay `|D^k_y B| ≲ (1+|y|)^{-(k+1)}`
(`k ≤ 3`) and `|D^k_y ∂_τB| ≲ (1+|y|)^{-(k+1)}` (`k ≤ 1`): the drift term `y·∇E_R` is controlled
because one more derivative gains one more power.  Since `(1+|y|)⁻² ∈ L^{11/7}` (`2 · 11/7 > 3`),
the tail over `|y| ≥ R` tends to zero; Hölder then gives convergence of the pairings.

Statements only (no proofs here); `Of.lean` proves the assemblies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

/-! ## Objects -/

/-- The smooth Newton-curl representative of `𝔓φ` for a real phase test `φ`:
`curl B` with `B = curl(N * φ)` (complexified). -/
def curlRepR (φ : ℝ × Space → Space) : ℝ × Space → CVec3 :=
  fun z => realC (spatialCurlST (projectedTestNewtonVectorPotentialCurl φ) z)

/-- The smooth Newton-curl representative of `𝔓Φ` for a complex phase test `Φ`, built from the real
and imaginary parts. -/
def curlRepC (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  curlRepR (fun z => reV (Φ z)) + Complex.I • curlRepR (fun z => imV (Φ z))

/-- The solenoidal approximants: curl cutoffs at radius `n + 1` of the Newton curl potentials of the
real and imaginary parts of `Φ`. -/
def curlCutoffSeq (Φ : ℝ × Space → CVec3) (n : ℕ) : ℝ × Space → CVec3 :=
  projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl (fun z => reV (Φ z))) +
    Complex.I • projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl (fun z => imV (Φ z)))

/-- The cutoff error field `realC (curl ((χ_R - 1) B))`. -/
def cutoffErr (R : ℝ) (B : ℝ × Space → Space) : ℝ × Space → CVec3 :=
  fun z => realC (spatialCurlST (fun w => (cutoff R w.2 - 1) • B w) z)

/-! ## Identification of the limit -/

/-- **(1) The Newton-curl representative is a representative of `𝔓Φ`.**  For every phase `τ`,
`curlRepC Φ (τ, ·) = projTest P Φ (τ, ·)` almost everywhere (source lines 119-120, 1356-1366).
Real case: `IIb.projTestIsNewtonCurl`; complex case: `IIb.projTest_add_smul_ae` with
`IIb.realC_reV_add_I_smul_imV`. -/
def NewtonCurlRepSliceAE : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ → ∀ τ : ℝ,
    (fun y => curlRepC Φ (τ, y)) =ᵐ[volume]
      fun y => UnforcedLeray.Short.IIb.projTest P Φ (τ, y)

/-! ## Decay of the Newton potentials (source lines 1393-1400, 1409-1412: Gaussian/kernel
differentiation, one power of decay per derivative) -/

/-- **(2a) Far-field derivatives of the scalar Newton potential** `N * f` of a compact smooth test
supported in `|x| ≤ ρ`: for `|y| ≥ 2ρ + 1`, `D^k(N * f)(y) = ∫ D^kN(y - x) f(x) dx` and
`|y - x| ≥ |y|/2` on the support, so `‖D^k(N * f)(y)‖ ≤ C_k ‖f‖_{L¹} |y|^{-(k+1)}`
(`Kernels.norm_iteratedFDeriv_newton_le`). -/
def NewtonConvFarDeriv : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Space → ℝ) (ρ : ℝ), IsSpatialTest f → 0 ≤ ρ →
    (∀ x : Space, ρ < ‖x‖ → f x = 0) → ∀ y : Space, 2 * ρ + 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ k (newtonConv f) y‖ ≤ C * (∫ x, |f x|) * ‖y‖ ^ (-((k : ℝ) + 1))

/-- **(2) Far-field derivative decay of the Newton vector potential** `A = N * φ`:
`‖D^k_y A(τ, y)‖ ≤ M |y|^{-(k+1)}` for `|y| ≥ ρ`, `k ≤ 4`, uniformly in `τ`. -/
def NewtonVectorPotentialFarDeriv : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∃ ρ M : ℝ, 1 ≤ ρ ∧ 0 ≤ M ∧ ∀ (τ : ℝ) (y : Space), ρ ≤ ‖y‖ → ∀ k : ℕ, k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotential φ (τ, x)) y‖ ≤
        M * ‖y‖ ^ (-((k : ℝ) + 1))

/-- **(3) Spatial derivatives of a slice curl** cost one derivative of the field:
`‖D^k_y (curl A)(τ, y)‖ ≤ 3 ‖D^{k+1}_y A(τ, y)‖`. -/
def SpatialCurlSliceDerivBound : Prop :=
  ∀ (A : ℝ × Space → Space), ContDiff ℝ ∞ A → ∀ (k : ℕ) (τ : ℝ) (y : Space),
    ‖iteratedFDeriv ℝ k (fun x => spatialCurlST A (τ, x)) y‖ ≤
      3 * ‖iteratedFDeriv ℝ (k + 1) (fun x => A (τ, x)) y‖

/-- **(4) Far-field derivative decay of the Newton curl potential** `B = curl(N * φ)`:
`‖D^k_y B(τ, y)‖ ≤ M |y|^{-(k+2)}` for `|y| ≥ ρ`, `k ≤ 3`. -/
def NewtonCurlSliceDecayFar : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∃ ρ M : ℝ, 1 ≤ ρ ∧ 0 ≤ M ∧ ∀ (τ : ℝ) (y : Space), ρ ≤ ‖y‖ → ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖ ≤
        M * ‖y‖ ^ (-((k : ℝ) + 2))

/-- **(5) Near-field bound of the Newton curl potential**: on `|y| ≤ ρ` the first three spatial
derivatives of `B` are bounded, uniformly in `τ`. -/
def NewtonCurlSliceBoundNear : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ → ∀ ρ : ℝ,
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ : ℝ) (y : Space), ‖y‖ ≤ ρ → ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖ ≤ M

/-- **(6) Global derivative decay of the Newton curl potential**:
`‖D^k_y B(τ, y)‖ ≤ M (1+|y|)^{-(k+1)}` for `k ≤ 3`, all `τ, y`. -/
def NewtonCurlSliceDecay : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ : ℝ) (y : Space) (k : ℕ), k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun x => projectedTestNewtonVectorPotentialCurl φ (τ, x)) y‖ ≤
        M * powWeight ((k : ℝ) + 1) y

/-- **(7) The phase derivative commutes with the Newton curl potential**:
`∂_τ curl(N * φ) = curl(N * ∂_τφ)`. -/
def NewtonCurlTimeComm : Prop :=
  ∀ (P : ℝ) (φ : ℝ × Space → Space), IsPhaseTest P φ →
    dτ (projectedTestNewtonVectorPotentialCurl φ) =
      projectedTestNewtonVectorPotentialCurl (dτ φ)

/-! ## The `L₀ᵗ` cutoff-error calculus (source lines 1446-1455, 1464-1466) -/

/-- **(8) Pointwise control of `L₀ᵗ` by slice derivatives**:
`|L₀ᵗF| ≤ |∂_τF| + 2|F| + 3|y| |D_yF| + 3ν |D²_yF|`. -/
def L0TSliceBound : Prop :=
  ∀ (F : ℝ × Space → CVec3), ContDiff ℝ ∞ F → ∀ ν : ℝ, 0 ≤ ν → ∀ (τ : ℝ) (y : Space),
    ‖L0T ν F (τ, y)‖ ≤ ‖dτ F (τ, y)‖ + 2 * ‖F (τ, y)‖ +
      3 * ‖y‖ * ‖iteratedFDeriv ℝ 1 (fun x => F (τ, x)) y‖ +
      3 * ν * ‖iteratedFDeriv ℝ 2 (fun x => F (τ, x)) y‖

/-- **(9) Spatial derivatives of a complexified slice curl**:
`‖D^k_y realC(curl G)(τ, y)‖ ≤ 3 ‖D^{k+1}_y G(τ, y)‖`. -/
def RealCCurlSliceDerivBound : Prop :=
  ∀ (G : ℝ × Space → Space), ContDiff ℝ ∞ G → ∀ (k : ℕ) (τ : ℝ) (y : Space),
    ‖iteratedFDeriv ℝ k (fun x => realC (spatialCurlST G (τ, x))) y‖ ≤
      3 * ‖iteratedFDeriv ℝ (k + 1) (fun x => G (τ, x)) y‖

/-- **(10) First derivative of a cut-off field** `(χ_R - 1) b`: if `|b| ≤ M(1+|y|)⁻¹` and
`|Db| ≤ M(1+|y|)⁻²`, then `|D((χ_R - 1) b)| ≤ C M (1 - χ_{R/2}) (1+|y|)⁻²` (it vanishes for
`|y| < R`, and `|∇χ_R| ≲ R⁻¹ ≲ (1+|y|)⁻¹` on the annulus `R ≤ |y| ≤ 2R`). -/
def CutoffSmulDeriv1 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Space → Space), ContDiff ℝ ∞ b → ∀ M : ℝ, 0 ≤ M →
    (∀ (y : Space) (k : ℕ), k ≤ 1 → ‖iteratedFDeriv ℝ k b y‖ ≤ M * powWeight ((k : ℝ) + 1) y) →
    ∀ R : ℝ, 1 ≤ R → ∀ y : Space,
      ‖iteratedFDeriv ℝ 1 (fun x => (cutoff R x - 1) • b x) y‖ ≤
        C * M * ((1 - cutoff (R / 2) y) * powWeight 2 y)

/-- **(11) Second and third derivatives of a cut-off field**: with
`|D^k b| ≤ M(1+|y|)^{-(k+1)}` for `k ≤ 3`,
`|y| |D²((χ_R - 1) b)| + |D³((χ_R - 1) b)| ≲ M (1 - χ_{R/2}) (1+|y|)⁻²` (the drift weight `|y|` is
paid by one power of decay, and `|y| / R ≤ 2` on the annulus). -/
def CutoffSmulDeriv23 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Space → Space), ContDiff ℝ ∞ b → ∀ M : ℝ, 0 ≤ M →
    (∀ (y : Space) (k : ℕ), k ≤ 3 → ‖iteratedFDeriv ℝ k b y‖ ≤ M * powWeight ((k : ℝ) + 1) y) →
    ∀ R : ℝ, 1 ≤ R → ∀ y : Space,
      ‖y‖ * ‖iteratedFDeriv ℝ 2 (fun x => (cutoff R x - 1) • b x) y‖ ≤
          C * M * ((1 - cutoff (R / 2) y) * powWeight 2 y) ∧
        ‖iteratedFDeriv ℝ 3 (fun x => (cutoff R x - 1) • b x) y‖ ≤
          C * M * ((1 - cutoff (R / 2) y) * powWeight 2 y)

/-- **(12) The phase derivative of the cutoff error** is the cutoff error of `∂_τB`
(symmetry of second derivatives; the cutoff depends on `y` only). -/
def CurlCutoffTimeComm : Prop :=
  ∀ (B : ℝ × Space → Space), ContDiff ℝ ∞ B → ∀ R : ℝ,
    dτ (cutoffErr R B) = cutoffErr R (dτ B)

/-- **(13) `L₀ᵗ` of the curl cutoff minus `L₀ᵗ` of the curl is `L₀ᵗ` of the cutoff error**
(`curl(χ_R B) - curl B = curl((χ_R - 1)B)` and linearity of `L₀ᵗ` on smooth fields). -/
def CurlCutoffL0TDiff : Prop :=
  ∀ (B : ℝ × Space → Space), ContDiff ℝ ∞ B → ∀ R ν : ℝ, 0 < R → ∀ z : ℝ × Space,
    L0T ν (projectedPotentialCurlCutoff R B) z - L0T ν (fun w => realC (spatialCurlST B w)) z =
      L0T ν (cutoffErr R B) z

/-- **(14) The `L₀ᵗ` cutoff-error bound for a general smooth potential** with the decay of (6)
and (7): `|L₀ᵗ curl(χ_R B) - L₀ᵗ curl B| ≤ K (1+ν) M (1 - χ_{R/2}) (1+|y|)⁻²`. -/
def CurlCutoffL0TCalc : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ × Space → Space), ContDiff ℝ ∞ B → ∀ M : ℝ, 0 ≤ M →
    (∀ (τ : ℝ) (y : Space) (k : ℕ), k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun x => B (τ, x)) y‖ ≤ M * powWeight ((k : ℝ) + 1) y) →
    (∀ (τ : ℝ) (y : Space) (k : ℕ), k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun x => dτ B (τ, x)) y‖ ≤ M * powWeight ((k : ℝ) + 1) y) →
    ∀ ν : ℝ, 0 ≤ ν → ∀ R : ℝ, 1 ≤ R → ∀ (τ : ℝ) (y : Space),
      ‖L0T ν (projectedPotentialCurlCutoff R B) (τ, y) -
          L0T ν (fun w => realC (spatialCurlST B w)) (τ, y)‖ ≤
        K * (1 + ν) * M * ((1 - cutoff (R / 2) y) * powWeight 2 y)

/-- **The `L₀ᵗ` cutoff-error bound for the Newton curl potential of a real phase test**
(assembled in `Of.lean` from (6), (7), (14)). -/
def CurlCutoffL0TErrorBound : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ν : ℝ, 0 ≤ ν → ∀ R : ℝ, 1 ≤ R → ∀ (τ : ℝ) (y : Space),
      ‖L0T ν (projectedPotentialCurlCutoff R (projectedTestNewtonVectorPotentialCurl φ)) (τ, y) -
          L0T ν (curlRepR φ) (τ, y)‖ ≤
        K * (1 + ν) * ((1 - cutoff (R / 2) y) * powWeight 2 y)

/-! ## Limits and Hölder pairing -/

/-- **(15) A limit of phase tests with a cut-off tail error is an `L^{q₀'}` slice test.**  If
`|Θₙ - Θ'| ≤ K (1 - χ_{(n+1)/2}) (1+|y|)⁻²`, then `Θ' = Θₙ` on `|y| ≤ (n+1)/2` (so `Θ'` is continuous
and `P`-periodic), `|Θ'| ≤ C (1+|y|)⁻²`, and `PartIIa.sliceContOfDecay` applies (`2 · 11/7 > 3`). -/
def UniformCutoffLimitSliceTest : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Θ : ℕ → ℝ × Space → CVec3) (Θ' : ℝ × Space → CVec3) (K : ℝ),
    (∀ n, IsPhaseTest P (Θ n)) →
    (∀ (n : ℕ) (τ : ℝ) (y : Space),
      ‖Θ n (τ, y) - Θ' (τ, y)‖ ≤ K * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y)) →
    IsSliceTest P (conjExp q0E) Θ'

/-- **(16) Hölder pairing of the cut-off tail error.**  Under the same bound, and `Θ'` a slice test,
`⟪Θₙ, d⟫ → ⟪Θ', d⟫` for every `d ∈ Y_{q₀}`: the slice errors are dominated by
`K ‖(1 - χ_{(n+1)/2}) (1+|y|)⁻²‖_{L^{11/7}} → 0` (`IIb.cutoffTailSmall`), then
`IIb.phasePairLimit_of IIb.testElemLimit`. -/
def UniformCutoffLimitPairing : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Θ : ℕ → ℝ × Space → CVec3) (Θ' : ℝ × Space → CVec3) (K : ℝ),
    (∀ n, IsPhaseTest P (Θ n)) → IsSliceTest P (conjExp q0E) Θ' →
    (∀ (n : ℕ) (τ : ℝ) (y : Space),
      ‖Θ n (τ, y) - Θ' (τ, y)‖ ≤ K * ((1 - cutoff (((n : ℝ) + 1) / 2) y) * powWeight 2 y)) →
    ∀ d : Yq P q0E,
      Tendsto (fun n => phasePair P q0E (Θ n) d) atTop (𝓝 (phasePair P q0E Θ' d))

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
