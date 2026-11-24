import UnforcedLeray.Units.B0220
import UnforcedLeray.Units.B0223
import UnforcedLeray.Units.B0225
import UnforcedLeray.Units.B0226

/-!
# Part II-a, module `near/free-comparison.tex`: statements

Source of record: `the November 2 reference manuscript`, lines 1634-1896.

Objects (all concrete, reusing the compiled drafts of the 162-page route):
* `H = L²(s^{-3/2} ds dq dη; ℂ²)` is `B0220.HSpace c B0223.MeridC` (cell measure; the source's
  normalisation `dq/c` multiplies the norms of `H` and `H_T` by the same constant, which
  does not change any operator norm between them).
  `H_T = L²(s^{-1/2} ds dq dη; Sym_3)` is `HTSpace c`, with the four independent components
  `(T_rr, T_rz, T_zz, T_φφ)` of an axisymmetric tensor without components having exactly one
  azimuthal index (lines 1642-1646).
* `T_ε = (μ - A_ε)^{-1} P_ε` is `Teps = B0223.RepsVec ∘ PepsC ε c`: `RepsVec` is the
  Laplace transform of the exact Cartesian free (Ornstein-Uhlenbeck) semigroup conjugated by
  the unitary lift `liftVec`, and `PepsC ε c` the orthogonal projection of `H` onto the
  exact solenoidal subspace `{Q-type divergence zero}`, which is the conjugated Cartesian
  Leray projection (B0226 `Peps_eq_starProjection`).
* `T_0 = R_0(μ) P_0` is `T0flat = B0225.R0 ∘ PepsC 0 c` (flat causal cylinder inverse, flat
  Leray projection).
* `S_ε = T_ε s div_ε` is the unique bounded extension from smooth tensors, expressed by the
  predicate `IsStressMap`: a bounded `S : H_T → H` with `S M = T (s div_ε M)` on smooth tensors.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### Tensor space `H_T` and the divergence `div_ε` (lines 1641-1672) -/

/-- Components `(T_rr, T_rz, T_zz, T_φφ)` of an axisymmetric tensor without swirl. -/
abbrev TensorVal := EuclideanSpace ℂ (Fin 4)

/-- `s^{-1/2} ds dq dη` on the cell (line 1642). -/
def measureHT (c : ℝ) : Measure Profile :=
  (cellMeasure c).withDensity fun p => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ)))

/-- The tensor Hilbert space `H_T = L²(s^{-1/2} ds dq dη; Sym_3)`. -/
abbrev HTSpace (c : ℝ) := Lp TensorVal 2 (measureHT c)

/-- Profile partial derivatives in the order `(s, q, η)`. -/
def pdS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Profile → E)
    (p : Profile) : E := fderiv ℝ f p (1, 0, 0)

def pdQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Profile → E)
    (p : Profile) : E := fderiv ℝ f p (0, 1, 0)

def pdEta {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Profile → E)
    (p : Profile) : E := fderiv ℝ f p (0, 0, 1)

/-- `S = s ∂_s` (line 1649). -/
def opS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Profile → E) :
    Profile → E := fun p => p.1 • pdS f p

/-- `K = 2S + η ∂_η` (line 1650). -/
def opK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Profile → E) :
    Profile → E := fun p => (2 : ℝ) • opS f p + p.2.2 • pdEta f p

/-- `Q_ε = ∂_q - ε (K + 1)` (line 1650). -/
def opQ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ε : ℝ) (f : Profile → E) :
    Profile → E := fun p => pdQ f p - ε • (opK f p + f p)

/-- The tensor divergence with the hoop traction (lines 1660-1665):
`(div_ε T)_r = Q_ε T_rr + ∂_η T_rz - ε T_φφ`, `(div_ε T)_z = Q_ε T_zr + ∂_η T_zz`. -/
def divEps (ε : ℝ) (M : Profile → TensorVal) : Profile → MeridC := fun p =>
  !₂[opQ ε (fun p => M p 0) p + pdEta (fun p => M p 1) p - (ε : ℂ) * M p 3,
    opQ ε (fun p => M p 1) p + pdEta (fun p => M p 2) p]

/-- Smooth tensor tests: smooth, `c`-periodic in `q`, supported in a band `s₀ ≤ s ≤ s₁`,
`|η| ≤ L`, `s₀ > 0`. -/
structure IsTensorTest (c : ℝ) (M : Profile → TensorVal) : Prop where
  smooth : ContDiff ℝ ∞ M
  periodic : QPeriodic c M
  band : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, M p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L

/-- Smooth meridional tests (same class, `ℂ²`-valued). -/
structure IsMeridTest (c : ℝ) (f : Profile → MeridC) : Prop where
  smooth : ContDiff ℝ ∞ f
  periodic : QPeriodic c f
  band : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L

/-! ### The operators `P_ε`, `T_ε`, `T_0` on `H` -/

/-- The complexified profile gradient `(D_εΦ, ∂_ηΦ)` of a real test `Φ` (line 1666 and B0226). -/
def cgrad (ε : ℝ) (Φ : Profile → ℝ) : Profile → MeridC := fun p =>
  !₂[((Deps ε Φ p : ℝ) : ℂ), ((Axi.dEta Φ p : ℝ) : ℂ)]

/-- The exact solenoidal subspace of the complex Hilbert space `H`:
`{b : b ⟂ (D_εΦ, ∂_ηΦ) for all profile tests Φ}` (weak form of `D_ε b_r + ∂_η b_z = 0`,
tex 3398-3400 of the old route, B0226 `solenoidalH` complexified). -/
def solenoidalHC (ε c : ℝ) : Submodule ℂ (HSpace c MeridC) :=
  (Submodule.span ℂ {g : HSpace c MeridC | ∃ Φ : ProfileTest c,
    ∃ _ : MemLp (cgrad ε Φ.1) 2 (measureH c), g = (‹MemLp (cgrad ε Φ.1) 2 (measureH c)›).toLp _})ᗮ

instance (ε c : ℝ) : CompleteSpace (solenoidalHC ε c) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

/-- `P_ε` on `H`: the orthogonal projection onto the exact solenoidal subspace, which is the
conjugated Cartesian Leray projection `J_ε⁻¹ P_{3D} J_ε` (`B0226.Peps_eq_starProjection`);
`P_0` is its `ε = 0` member, the flat cylinder projection (line 1676). -/
def PepsC (ε c : ℝ) : HSpace c MeridC →L[ℂ] HSpace c MeridC :=
  (solenoidalHC ε c).starProjection

/-- `T_ε = (μ - A_ε)^{-1} P_ε = R_ε^{vec}(μ) P_ε` (line 1677), `P = 2εc`. -/
def Teps {P ν ε c : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c)
    (hP : P = 2 * ε * c) (μ : ℂ) : HSpace c MeridC →L[ℂ] HSpace c MeridC :=
  RepsVec hν hε hc hP μ ∘L PepsC ε c

/-- `T_0 = R_0(μ) P_0` (lines 1655-1656, 1676): causal flat cylinder inverse after the flat
Leray projection. -/
def T0flat {c : ℝ} (hc : 0 < c) (ν : ℝ) (μ : ℂ) : HSpace c MeridC →L[ℂ] HSpace c MeridC :=
  B0225.R0 hc ν μ ∘L PepsC 0 c

/-- `S : H_T → H` is a stress map for the body operator `T` and parameter `ε`:
`S M = T (s div_ε M)` for every smooth tensor `M` (any representatives `F` of `M` in `H_T` and
`G` of `s div_ε M` in `H`). By density of smooth tensors this determines `S` ("completion from
smooth tensors", line 1678). -/
def IsStressMap (c ε : ℝ) (T : HSpace c MeridC →L[ℂ] HSpace c MeridC)
    (S : HTSpace c →L[ℂ] HSpace c MeridC) : Prop :=
  ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ (F : HTSpace c) (G : HSpace c MeridC),
    (F : Profile → TensorVal) =ᵐ[measureHT c] M →
    (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
      S F = T G

/-- A bounded measurable real multiplier maps `L²(μ; E)` into itself. -/
theorem memLp_chi_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Profile) (χ : Profile → ℝ) (hχ : Measurable χ) {B : ℝ}
    (hB : ∀ p, |χ p| ≤ B) {f : Profile → E} (hf : MemLp f 2 μ) :
    MemLp (fun p => χ p • f p) 2 μ :=
  hf.of_le_mul (c := B) (hχ.aestronglyMeasurable.smul hf.1) (Eventually.of_forall fun p => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB p) (norm_nonneg _))

/-- Multiplication by a bounded measurable real function, a bounded operator on `L²(μ; E)`. -/
def mulChi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (μ : Measure Profile) (χ : Profile → ℝ) (hχ : Measurable χ) {B : ℝ}
    (hB : ∀ p, |χ p| ≤ B) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_chi_smul μ χ hχ hB (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_chi_smul μ χ hχ hB (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_chi_smul μ χ hχ hB (Lp.memLp f)).coeFn_toLp,
          (memLp_chi_smul μ χ hχ hB (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_chi_smul μ χ hχ hB (Lp.memLp f)).toLp _)
            ((memLp_chi_smul μ χ hχ hB (Lp.memLp g)).toLp _),
          Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [(memLp_chi_smul μ χ hχ hB (Lp.memLp (a • f))).coeFn_toLp,
          (memLp_chi_smul μ χ hχ hB (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_chi_smul μ χ hχ hB (Lp.memLp f)).toLp _),
          Lp.coeFn_smul a f] with x h1 h2 h3 h4
        simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
        exact smul_comm _ _ _ }
    B fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_chi_smul μ χ hχ hB (Lp.memLp f)).coeFn_toLp] with x hx
      simp only [LinearMap.coe_mk, AddHom.coe_mk, hx, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

/-! ### Cutoffs, the constant `Γ`, and the statements (lines 1695-1722) -/

/-- The `C⁸` norm `Σ_{k ≤ 8} sup |D^k f|`. -/
def cNorm8 (f : Profile → ℝ) : ℝ := ∑ k ∈ Finset.range 9, ⨆ p, ‖iteratedFDeriv ℝ k f p‖

/-- `χ`: smooth, `c`-periodic in `q`, supported in `σ ≤ s ≤ H₁`, `|η| ≤ L₁` (line 1696). -/
structure IsNearCutoff (c σ H1 L1 : ℝ) (χ : Profile → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  periodic : QPeriodic c χ
  support : ∀ p : Profile, χ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1

/-- `χ₁`: smooth, periodic, band-supported, equal to one on a neighbourhood of `supp χ`
(line 1696, "equal one on a larger neighborhood"). -/
structure IsLargerCutoff (c : ℝ) (χ χ1 : Profile → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ1
  periodic : QPeriodic c χ1
  band : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, χ1 p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L
  one_near : ∃ U : Set Profile, IsOpen U ∧ tsupport χ ⊆ U ∧ ∀ p ∈ U, χ1 p = 1

/-- The window part of `Γ` (lines 1699-1702). -/
def GammaBox (ν c σ H1 L1 M γs : ℝ) : ℝ :=
  2 + ν + ν⁻¹ + c + c⁻¹ + σ⁻¹ + H1 + L1 + M + γs⁻¹

/-- `Γ = 2 + ν + ν⁻¹ + c + c⁻¹ + σ⁻¹ + H₁ + L₁ + sup|μ| + γ_*⁻¹ + ‖χ‖_{C⁸} + ‖χ₁‖_{C⁸}`. -/
def Gamma (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) : ℝ :=
  GammaBox ν c σ H1 L1 M γs + cNorm8 χ + cNorm8 χ1

/-- Seminorm `‖z‖_{H⁶}` of a smooth test on the cell (sum of the `L²(cell)` norms of all
derivatives of order `≤ 6`, in the plain Lebesgue measure `ds dq dη`). -/
def h6Norm (c : ℝ) (z : Profile → MeridC) : ℝ :=
  ∑ k ∈ Finset.range 7, (∫ p, ‖iteratedFDeriv ℝ k z p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)

/-- **Existence of the stress maps `S_ε` (`ε ∈ [0,1]`)** (line 1678-1690): a bounded `S_ε : H_T → H`
extending `T_ε s div_ε` from smooth tensors, `‖S_ε M‖_H ≤ C ν^{-1/2} ‖M‖_{H_T}`
(`near:free-energy`, `b`-part; the dissipation part `√ν ‖(Q_ε b, ∂_η b, ε b_r)‖_{H_T}`
is the same estimate on the gradient and is part of this task's proof). Uniform for
`0 ≤ ε ≤ 1` and `μ` in compact subsets of `Re μ > -1/4`. -/
def NearStressMapExists : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c M γs : ℝ) (hν : 0 < ν) (hc : 0 < c), 0 < γs →
    ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        (∃ S : HTSpace c →L[ℂ] HSpace c MeridC, IsStressMap c ε (Teps hν hε hc hP μ) S ∧
            ∀ F, ‖S F‖ ≤ C * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖) ∧
        (∃ S : HTSpace c →L[ℂ] HSpace c MeridC, IsStressMap c 0 (T0flat hc ν μ) S ∧
            ∀ F, ‖S F‖ ≤ C * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖)

/-- **Quantitative Leray comparison on smooth tests** (`near:leray-test`, lines 1737-1751): for
smooth tests `f`, `‖(P_ε - P_0) f‖_H ≤ p(1 + c + c⁻¹) √ε Σ_{a,j ∈ {0,1}} ‖η^j S^a f‖_H`,
`p` a polynomial. (The extension to the full stated domain by density, retaining the zero mode,
is part of the proof.) -/
def NearLerayComparison : Prop :=
  ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (c ε : ℝ), 0 < c → 0 < ε → ε ≤ 1 →
    ∀ (f : Profile → MeridC) (F : HSpace c MeridC), IsMeridTest c f →
      (F : Profile → MeridC) =ᵐ[measureH c] f →
        ‖(PepsC ε c - PepsC 0 c) F‖ ≤ C * (1 + c + c⁻¹) ^ d * Real.sqrt ε *
          ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
            (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] f) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ)

/-- **Smooth adjoint comparison** (`near:smooth-adjoint-comparison`, lines 1809-1816): for a smooth
test `z` in the observation box, `‖(T_ε* - T_0*) z‖_H ≤ C Γ^k √ε ‖z‖_{H⁶}` and
`‖(S_ε* - S_0*) z‖_{H_T} ≤ C Γ^k √ε ‖z‖_{H⁶}` (adjoints of bounded operators between the
Hilbert spaces; the source states the sum of the two, equivalent up to the factor 2). -/
def NearSmoothAdjointComparison : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (hν : 0 < ν) (hc : 0 < c), 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          ∀ (z : Profile → MeridC) (Z : HSpace c MeridC), IsMeridTest c z →
            (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
            (Z : Profile → MeridC) =ᵐ[measureH c] z →
              ‖(ContinuousLinearMap.adjoint (Teps hν hε hc hP μ) -
                  ContinuousLinearMap.adjoint (T0flat hc ν μ)) Z‖ ≤
                C * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z ∧
              ∀ Seps S0 : HTSpace c →L[ℂ] HSpace c MeridC,
                IsStressMap c ε (Teps hν hε hc hP μ) Seps → IsStressMap c 0 (T0flat hc ν μ) S0 →
                  ‖(ContinuousLinearMap.adjoint Seps - ContinuousLinearMap.adjoint S0) Z‖ ≤
                    C * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z

/-- **Local regularity + band-limited dual vectors** (lines 1766-1804 and 1817-1832): for every
`N ≥ 1` there is a (low-frequency) subspace `V ⊆ H` such that, after localisation by `χ`,
the outputs `T_ε b, T_0 b` are within `C Γ^k N^{-1}‖b‖` of `V` (local `H¹` bound) and the outputs
`S_ε M, S_0 M` within `C Γ^k N^{-1/4}‖M‖` of `V` (local `H^{1/4}` bound, `near:local-smoothing`),
while every `z ∈ V` has, after the adjoint localisation `χ*z`, a smooth observation-box
representative of `H⁶` norm at most `C Γ^k N⁶ ‖z‖`. -/
def NearBandLimited : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c), 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 → ∀ N : ℝ, 1 ≤ N →
          ∃ V : Submodule ℂ (HSpace c MeridC),
            (∀ b : HSpace c MeridC,
              (∃ v ∈ V, ‖mulChi (measureH c) χ hm hB (Teps hν hε hc hP μ b) - v‖ ≤
                  C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * N⁻¹ * ‖b‖) ∧
              (∃ v ∈ V, ‖mulChi (measureH c) χ hm hB (T0flat hc ν μ b) - v‖ ≤
                  C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * N⁻¹ * ‖b‖)) ∧
            (∀ Seps S0 : HTSpace c →L[ℂ] HSpace c MeridC,
              IsStressMap c ε (Teps hν hε hc hP μ) Seps → IsStressMap c 0 (T0flat hc ν μ) S0 →
              ∀ F : HTSpace c,
                (∃ v ∈ V, ‖mulChi (measureH c) χ hm hB (Seps F) - v‖ ≤
                    C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * N ^ (-(1 / 4 : ℝ)) * ‖F‖) ∧
                (∃ v ∈ V, ‖mulChi (measureH c) χ hm hB (S0 F) - v‖ ≤
                    C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * N ^ (-(1 / 4 : ℝ)) * ‖F‖)) ∧
            (∀ z ∈ V, ∃ ζ : Profile → MeridC, IsMeridTest c ζ ∧
              (∀ p, ζ p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) ∧
              ((ContinuousLinearMap.adjoint (mulChi (measureH c) χ hm hB) z : HSpace c MeridC) :
                Profile → MeridC) =ᵐ[measureH c] ζ ∧
              h6Norm c ζ ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * N ^ (6 : ℕ) * ‖z‖)

/-- **Proposition `near:compact-free-comparison`** (lines 1692-1722, eq. `near:compact-free-rates`):
there is a fixed integer `k` and constant `C` such that, uniformly for `0 < ε ≤ 1` (with
`P = 2εc ≤ 1`) and `μ` in a compact subset of `Re μ > -1/4`,
`‖χ(T_ε - T_0)‖_{H→H} ≤ C Γ^k ε^{1/14}` and `‖χ(S_ε - S_0)‖_{H_T→H} ≤ C Γ^k ε^{1/50}`. -/
def NearCompactFreeComparison : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c), 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          (∀ b : HSpace c MeridC,
            ‖mulChi (measureH c) χ hm hB ((Teps hν hε hc hP μ - T0flat hc ν μ) b)‖ ≤
              C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ε ^ (1 / 14 : ℝ) * ‖b‖) ∧
          (∀ Seps S0 : HTSpace c →L[ℂ] HSpace c MeridC,
            IsStressMap c ε (Teps hν hε hc hP μ) Seps → IsStressMap c 0 (T0flat hc ν μ) S0 →
            ∀ F : HTSpace c,
              ‖mulChi (measureH c) χ hm hB ((Seps - S0) F)‖ ≤
                C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ε ^ (1 / 50 : ℝ) * ‖F‖)

end UnforcedLeray.Short.PartIIa
