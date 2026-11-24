import UnforcedLeray.Units.B0094.Basis
import UnforcedLeray.Units.B0094.Planar
import UnforcedLeray.Units.B0094.SchwartzCore

/-!
# B0094 (`eq:st18-t00068`): `D` is selfadjoint and `≤ 0` on `X_G`, with spectrum `{0, -1, -2, …}`

Blueprint unit B0094, label `eq:st18-t00068`, `paper/main.tex` lines 1503--1515 (proof of G3a,
Section `sec:st18-1665`). Dependencies: B0093 (`eq:st18-t00067`, `Units/B0093.lean`: the operator
`D = Δ + ½ y·∇ + 2` of `eq:st18-t00011` as `B0093.gaussianOperator`) and B0010
(`eq:st18-t00005`, `Units/B0010.lean`: the space `X_G = XG` of angular-two profiles and its planar
realization `angularTwoField`).

## The manuscript's claim (tex lines 1503--1515)

After conjugating `D` to the oscillator `Δ - |y|²/16 + 3/2` (B0093), the Hermite realization has a
selfadjoint closure; the Hermite level of total degree `N` has eigenvalue `1 - N/2`; angular weight
two means `N = 2 + 2ℓ`; hence `D ≤ 0` on `X_G` with spectrum `0, -1, -2, …`, and
`𝒟(D) = {f = ∑_{ℓ≥0} f_ℓ : ∑ (1 + ℓ²) ‖f_ℓ‖² < ∞}` with `f_ℓ` the component of `f` in the
`ℓ`-th eigenspace.

## What is formalized

* `Dcore` (`Basis.lean`): `D` on the core of Gaussian-polynomial profiles
  `f₂(r) = r² p(r²) e^{-r²/4}` (`prof p`); `Dcore_eq_gaussianOperator` identifies it with the
  manuscript's planar operator `Δ + ½ y·∇ + 2` acting on `f₂(r) e^{2iϑ}` (B0093's
  `gaussianOperator`, B0010's `angularTwoField`). These planar functions are `U_G⁻¹` of
  polynomial-times-Gaussian (Schwartz) functions, i.e. finite combinations of the angular-two
  Hermite levels.
* `D := Dcore.closure`, the selfadjoint closure. `Dcore_isClosable`, `isSelfAdjoint_D`
  (`D† = D`), `D_nonpos` (`⟪f, D f⟫ ∈ ℝ`, `≤ 0`), `opSpectrum_D` (spectrum `{0, -1, -2, …}`,
  with the standard definition: `μ` is in the resolvent set iff `D - μ` maps `𝒟(D)` bijectively
  onto `X_G` with bounded inverse), `mem_D_domain_iff` (the domain `eq:st18-t00068`) and
  `hasSum_components` (`f = ∑ f_ℓ`).
* `oscBasis`: the orthonormal eigenbasis (`D_oscBasis`); each eigenspace is the line
  `span {oscBasis ℓ}` (`D_eigen_iff`), so `f_ℓ = ⟪oscBasis ℓ, f⟫ • oscBasis ℓ`; each eigenvector is
  a Gaussian-polynomial profile `prof q` with `lag q = -ℓ q` (`oscBasis_eigen`; `q` is the
  Laguerre polynomial `L_ℓ^{(2)}(s/4)` up to normalization, which is not needed).
* `oscBasis_level` (tex lines 1506--1510): `oscBasis ℓ = U_G⁻¹ (coreS q)` with `deg q = ℓ`, where
  `coreS q = √(4π) (y₁ + i y₂)² q(|y|²) e^{-|y|²/8}` is the angular-two Hermite function of total
  degree `N = 2 + 2ℓ`, and the oscillator acts on it by `1 - N/2 = -ℓ`.
* **Schwartz core** (tex line 1505): `schwartzCore` is the subspace of `X_G` of the functions
  `U_G⁻¹ φ = √G φ` with `φ ∈ 𝓢(ℝ², ℂ)` of angular weight two (`IsAngularTwo`,
  `φ(R_θ y) = e^{2iθ} φ(y)`), realized by the profiles `schProf φ r = √G(r) φ(r, 0)`
  (`angularTwoField_schProf`). `schwartz_mem_D`: each such function lies in `𝒟(D)` and
  `D (U_G⁻¹ φ) = U_G⁻¹ (osc φ)`, where `osc = Δ - |y|²/16 + 3/2` (`oscS`, B0093's
  `oscillator`); `angularTwoField_schProf_oscS`: this is the manuscript's planar operator
  `Δ + ½ y·∇ + 2` applied to `U_G⁻¹ φ`. `hasCore_schwartzCore`: `D.HasCore schwartzCore`
  (Mathlib's `LinearPMap.HasCore`: the closure of `D` restricted to the Schwartz class is `D`).
  `schwartz_iterate_mem_D`: the same holds for every power `osc^m φ` (the form consumer B0095
  uses: Schwartz `U_G q` gives `q` in every power domain).
* `closure_eq_D_of_symmetric`: every symmetric extension of `Dcore` has closure `D`.
* `D_graph_iff`: `f ∈ 𝒟(D)` with `D f = g` iff `⟪D φ, f⟫ = ⟪φ, g⟫` for every core vector `φ`.

## Route and deviations

Teschl's tensor-product Hermite realization (`teschl2009`, §8.3) is not formalized; instead,
following the unit's notes, `X_G` is diagonalized directly: the Gram–Schmidt orthonormalization of
`r^{2+2k} e^{-r²/4}` is a Hilbert basis (`Density.lean`: completeness, the missing analytic input
named in the notes, proved via an exponential-moment induction, Weierstrass and the fundamental
lemma of the calculus of variations), `D` is triangular on the monomials with diagonal `-ℓ` and
symmetric on the core (`Profiles.lean`, explicit Gaussian moments), hence diagonal in the
orthonormalized basis, and `Diagonal.lean` proves the operator facts for `diag(-ℓ)`.
For the Schwartz core, `GaussSchwartz.lean` shows that `U_G` of the core functions are Schwartz
(`coreS`), and `SchwartzCore.lean` proves that the oscillator is symmetric on Schwartz functions
(integration by parts, Mathlib's `integral_bilinear_lineDerivOp_right_eq_neg_left`) and preserves
angular weight two (the Laplacian commutes with rotations); `D_graph_iff` then gives
`schwartz_mem_D`.

Lean's inner product `⟪f, g⟫_ℂ` is conjugate-linear in `f`; the manuscript's pairing is
`pairing f g = ⟪g, f⟫_ℂ` (B0010.pairing_eq_inner). All statements used here are insensitive to
this convention.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial
open scoped InnerProductSpace ComplexConjugate SchwartzMap

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010

/-! ## The operator -/

/-- **The operator `D` on `X_G`** (tex lines 1503--1515): the closure of
`D = Δ + ½ y·∇ + 2` (`eq:st18-t00011`) from the core of angular-two Gaussian-polynomial profiles
`r² p(r²) e^{-r²/4}` (B0094). -/
def D : XG →ₗ.[ℂ] XG := Dcore.closure

/-- On the core, `D` is the manuscript's planar differential operator `Δ + ½ y·∇ + 2` (B0093)
acting on the angular-two realization `f₂(r) e^{2iϑ}` (B0010) of the profile
`f₂ = r² p(r²) e^{-r²/4}`: both send it to the profile of `lag p`. -/
theorem Dcore_eq_gaussianOperator (p : ℂ[X]) :
    Dcore ⟨prof p, mem_Dcore_domain p⟩ = prof (lag p) ∧
      B0093.gaussianOperator (angularTwoField (profFun p)) = angularTwoField (profFun (lag p)) :=
  ⟨Dcore_apply p _, gaussianOperator_angularTwoField_profFun p⟩

/-- The core operator is closable (tex line 1505). -/
theorem Dcore_isClosable : Dcore.IsClosable := Dcore_closure.1

theorem D_eq_diagOp : D = diagOp oscBasis := Dcore_closure.2

theorem Dcore_le_D : Dcore ≤ D := LinearPMap.le_closure _

/-- **`D` is selfadjoint** on `X_G` (tex lines 1505, 1509). -/
theorem isSelfAdjoint_D : IsSelfAdjoint D := by
  rw [D_eq_diagOp]
  exact isSelfAdjoint_diagOp oscBasis

/-- **`D ≤ 0`** on `X_G` (tex line 1509): `⟪f, D f⟫` is real and nonpositive. -/
theorem D_nonpos (f : D.domain) :
    (⟪(f : XG), D f⟫_ℂ).re ≤ 0 ∧ (⟪(f : XG), D f⟫_ℂ).im = 0 := by
  have h : ∀ T : XG →ₗ.[ℂ] XG, T = diagOp oscBasis → ∀ f : T.domain,
      (⟪(f : XG), T f⟫_ℂ).re ≤ 0 ∧ (⟪(f : XG), T f⟫_ℂ).im = 0 := by
    rintro T rfl f
    exact diagOp_nonpos oscBasis f
  exact h D D_eq_diagOp f

/-- **The spectrum of `D`** is `{0, -1, -2, …}` (tex line 1510). -/
theorem opSpectrum_D : opSpectrum D = Set.range fun n : ℕ => -(n : ℂ) := by
  rw [D_eq_diagOp]
  exact opSpectrum_diagOp oscBasis

/-- **The domain of `D`** (`eq:st18-t00068`, tex lines 1511--1514):
`f ∈ 𝒟(D)` iff `∑_ℓ (1 + ℓ²) ‖f_ℓ‖² < ∞`, where `f_ℓ = ⟪oscBasis ℓ, f⟫ • oscBasis ℓ` is the
component of `f` in the `ℓ`-th eigenspace (`D_eigen_iff`). -/
theorem mem_D_domain_iff (f : XG) :
    f ∈ D.domain ↔
      Summable fun ℓ : ℕ => (1 + (ℓ : ℝ) ^ 2) * ‖⟪oscBasis ℓ, f⟫_ℂ • oscBasis ℓ‖ ^ 2 := by
  rw [D_eq_diagOp, mem_diagOp_domain_iff_summable]
  have : ∀ ℓ, ‖⟪oscBasis ℓ, f⟫_ℂ • oscBasis ℓ‖ = ‖⟪oscBasis ℓ, f⟫_ℂ‖ := fun ℓ => by
    rw [norm_smul, oscBasis.orthonormal.1 ℓ, mul_one]
  simp only [this]

/-- `f = ∑_ℓ f_ℓ` (tex line 1512). -/
theorem hasSum_components (f : XG) :
    HasSum (fun ℓ : ℕ => ⟪oscBasis ℓ, f⟫_ℂ • oscBasis ℓ) f := by
  have := oscBasis.hasSum_repr f
  simpa only [oscBasis.repr_apply_apply] using this

/-- The vectors of `oscBasis` are eigenvectors: `D (oscBasis ℓ) = -ℓ oscBasis ℓ`
(tex lines 1506--1510). -/
theorem D_oscBasis (n : ℕ) :
    ∃ h : oscBasis n ∈ D.domain, D ⟨oscBasis n, h⟩ = -(n : ℂ) • oscBasis n := by
  rw [D_eq_diagOp]
  exact ⟨basis_mem_domain oscBasis n, diagOp_basis oscBasis n⟩

/-- Each eigenvalue `-ℓ` is simple: its eigenspace is the line spanned by `oscBasis ℓ`. -/
theorem D_eigen_iff (n : ℕ) (f : D.domain) :
    D f = -(n : ℂ) • (f : XG) ↔ (f : XG) ∈ Submodule.span ℂ {oscBasis n} := by
  have h : ∀ T : XG →ₗ.[ℂ] XG, T = diagOp oscBasis → ∀ f : T.domain,
      (T f = -(n : ℂ) • (f : XG) ↔ (f : XG) ∈ Submodule.span ℂ {oscBasis n}) := by
    rintro T rfl f
    exact diagOp_eigen_iff oscBasis n f
  exact h D D_eq_diagOp f

/-- The eigenvectors are Gaussian-polynomial profiles `r² q(r²) e^{-r²/4}` with
`lag q = -ℓ q` (the angular-two Hermite level `N = 2 + 2ℓ`, tex lines 1506--1508). -/
theorem oscBasis_eigen (n : ℕ) : ∃ q : ℂ[X], oscBasis n = prof q ∧ lag q = -(n : ℂ) • q := by
  obtain ⟨q, hq, hlag⟩ := osc_eigen n
  refine ⟨q, by rw [coe_oscBasis, hq], prof_injective ?_⟩
  rw [hlag, map_smul]

/-! ## Cores and the weak form of the graph -/

/-- **Core property** (tex line 1505): every symmetric operator extending `Dcore` is closable
with closure `D` (applied to the Schwartz class in `hasCore_schwartzCore`). -/
theorem closure_eq_D_of_symmetric {S : XG →ₗ.[ℂ] XG} (hle : Dcore ≤ S)
    (hsymm : ∀ x y : S.domain, ⟪S x, (y : XG)⟫_ℂ = ⟪(x : XG), S y⟫_ℂ) :
    S.IsClosable ∧ S.closure = D := by
  have hb : ∀ n, oscBasis n ∈ S.domain := fun n => hle.1 (oscBasis_mem_Dcore n)
  have heig : ∀ n, S ⟨oscBasis n, hb n⟩ = -(n : ℂ) • oscBasis n := by
    intro n
    rw [← hle.2 (x := ⟨oscBasis n, oscBasis_mem_Dcore n⟩) rfl, Dcore_oscBasis]
  rw [D_eq_diagOp]
  exact closure_eq_diagOp oscBasis hsymm hb heig

/-- **Weak form of the graph of `D`**: `f ∈ 𝒟(D)` and `D f = g` iff
`⟪D φ, f⟫ = ⟪φ, g⟫` for every core vector `φ = prof p`. -/
theorem D_graph_iff (f g : XG) :
    (∃ hf : f ∈ D.domain, D ⟨f, hf⟩ = g) ↔ ∀ p : ℂ[X], ⟪prof (lag p), f⟫_ℂ = ⟪prof p, g⟫_ℂ := by
  have hle : Dcore ≤ diagOp oscBasis :=
    le_diagOp_of_symm oscBasis Dcore_symm oscBasis_mem_Dcore Dcore_oscBasis
  rw [D_eq_diagOp]
  constructor
  · rintro ⟨hf, rfl⟩ p
    have hp : prof p ∈ (diagOp oscBasis).domain := hle.1 (mem_Dcore_domain p)
    have h1 : prof (lag p) = diagOp oscBasis ⟨prof p, hp⟩ := by
      rw [← Dcore_apply p (mem_Dcore_domain p)]
      exact hle.2 rfl
    rw [h1]
    exact diagOp_symm oscBasis ⟨prof p, hp⟩ ⟨f, hf⟩
  · intro h
    apply exists_diagOp_eq
    intro n
    obtain ⟨q, hq, hlag⟩ := oscBasis_eigen n
    have := h q
    rw [hlag, map_smul, ← hq, inner_smul_left, map_neg, Complex.conj_natCast] at this
    rw [← this]

/-! ## The Schwartz core (tex line 1505) -/

/-- `D` is symmetric: `⟪D f, g⟫ = ⟪f, D g⟫` on `𝒟(D)`. -/
theorem D_symm (f g : D.domain) : ⟪D f, (g : XG)⟫_ℂ = ⟪(f : XG), D g⟫_ℂ := by
  have h : ∀ T : XG →ₗ.[ℂ] XG, T = diagOp oscBasis → ∀ f g : T.domain,
      ⟪T f, (g : XG)⟫_ℂ = ⟪(f : XG), T g⟫_ℂ := by
    rintro T rfl f g
    exact diagOp_symm oscBasis f g
  exact h D D_eq_diagOp f g

/-- **Schwartz functions lie in `𝒟(D)`** (tex lines 1503--1505, 1517): for every Schwartz
function `φ` on `ℝ²` of angular weight two, `U_G⁻¹ φ = √G φ` (the element of `X_G` with profile
`schProf φ r = √G(r) φ(r, 0)`) lies in `𝒟(D)`, and `D (U_G⁻¹ φ) = U_G⁻¹ (osc φ)` with
`osc = Δ - |y|²/16 + 3/2` (`oscS`, `eq:st18-t00067`). -/
theorem schwartz_mem_D (φ : 𝓢(ℝ × ℝ, ℂ)) (hφ : IsAngularTwo φ) :
    ∃ h : (memLp_schProf φ).toLp (schProf φ) ∈ D.domain,
      D ⟨_, h⟩ = (memLp_schProf (oscS φ)).toLp (schProf (oscS φ)) :=
  (D_graph_iff _ _).2 fun p => inner_prof_lag_schProf p hφ

/-- On the Schwartz class `D` is the manuscript's differential operator `Δ + ½ y·∇ + 2`
(`eq:st18-t00011`, B0093's `gaussianOperator`): the planar function of the profile of
`D (U_G⁻¹ φ)` is `gaussianOperator` applied to the planar function `U_G⁻¹ φ` of `schProf φ`. -/
theorem angularTwoField_schProf_oscS (φ : 𝓢(ℝ × ℝ, ℂ)) (hφ : IsAngularTwo φ) :
    angularTwoField (schProf (oscS φ)) =
      B0093.gaussianOperator (angularTwoField (schProf φ)) := by
  rw [angularTwoField_schProf hφ.oscS, angularTwoField_schProf hφ, coe_oscS,
    ← B0093.conjG_gaussianOperator_conjGInv_schwartz, B0093.conjGInv_conjG]

theorem IsAngularTwo.iterate_oscS {φ : 𝓢(ℝ × ℝ, ℂ)} (h : IsAngularTwo φ) (m : ℕ) :
    IsAngularTwo ((B0094.oscS)^[m] φ) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.oscS

/-- **All powers** (tex lines 1517--1518, used by B0095): for every `m`,
`U_G⁻¹ (osc^m φ) ∈ 𝒟(D)` and `D (U_G⁻¹ (osc^m φ)) = U_G⁻¹ (osc^{m+1} φ)`; hence `U_G⁻¹ φ` lies
in every power domain `𝒟(D^m)` and `D^m (U_G⁻¹ φ) = U_G⁻¹ (osc^m φ)`. -/
theorem schwartz_iterate_mem_D (φ : 𝓢(ℝ × ℝ, ℂ)) (hφ : IsAngularTwo φ) (m : ℕ) :
    ∃ h : (memLp_schProf (oscS^[m] φ)).toLp (schProf (oscS^[m] φ)) ∈ D.domain,
      D ⟨_, h⟩ = (memLp_schProf (oscS^[m + 1] φ)).toLp (schProf (oscS^[m + 1] φ)) := by
  simpa only [Function.iterate_succ_apply'] using schwartz_mem_D _ (hφ.iterate_oscS m)

theorem IsAngularTwo.add {φ ψ : 𝓢(ℝ × ℝ, ℂ)} (hφ : IsAngularTwo φ) (hψ : IsAngularTwo ψ) :
    IsAngularTwo (φ + ψ) := by
  intro θ z
  show φ (rot θ z) + ψ (rot θ z) = Complex.exp (2 * Complex.I * θ) * (φ z + ψ z)
  rw [hφ θ z, hψ θ z]
  ring

theorem IsAngularTwo.smul (c : ℂ) {φ : 𝓢(ℝ × ℝ, ℂ)} (hφ : IsAngularTwo φ) :
    IsAngularTwo (c • φ) := by
  intro θ z
  show c * φ (rot θ z) = Complex.exp (2 * Complex.I * θ) * (c * φ z)
  rw [hφ θ z]
  ring

theorem toLp_schProf_add (φ ψ : 𝓢(ℝ × ℝ, ℂ)) :
    (memLp_schProf (φ + ψ)).toLp _ = (memLp_schProf φ).toLp _ + (memLp_schProf ψ).toLp _ := by
  rw [← MeasureTheory.MemLp.toLp_add]
  exact MeasureTheory.MemLp.toLp_congr _ _
    (Filter.Eventually.of_forall fun r => by simp [schProf, mul_add])

theorem toLp_schProf_smul (c : ℂ) (φ : 𝓢(ℝ × ℝ, ℂ)) :
    (memLp_schProf (c • φ)).toLp _ = c • (memLp_schProf φ).toLp _ := by
  rw [← MeasureTheory.MemLp.toLp_const_smul]
  exact MeasureTheory.MemLp.toLp_congr _ _
    (Filter.Eventually.of_forall fun r => by
      show (Real.sqrt (radialGaussianWeight r) : ℂ) * (c * φ (r, 0)) =
        c * ((Real.sqrt (radialGaussianWeight r) : ℂ) * φ (r, 0))
      ring)

/-- **The Schwartz class in `X_G`**: the functions `U_G⁻¹ φ = √G φ` with `φ ∈ 𝓢(ℝ², ℂ)` of angular
weight two (tex line 1505). -/
def schwartzCore : Submodule ℂ XG where
  carrier := {f | ∃ φ : 𝓢(ℝ × ℝ, ℂ), IsAngularTwo φ ∧ f = (memLp_schProf φ).toLp _}
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hφ.add hψ, (toLp_schProf_add φ ψ).symm⟩
  zero_mem' := by
    refine ⟨0, fun θ z => by simp, ?_⟩
    symm
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    refine (memLp_schProf 0).coeFn_toLp.trans (Filter.Eventually.of_forall fun r => ?_)
    simp [schProf]
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hφ.smul c, (toLp_schProf_smul c φ).symm⟩

theorem schwartzCore_le_domain : schwartzCore ≤ D.domain := by
  rintro f ⟨φ, hφ, rfl⟩
  exact (schwartz_mem_D φ hφ).1

theorem prof_mem_schwartzCore (p : ℂ[X]) : prof p ∈ schwartzCore := by
  refine ⟨coreS p, isAngularTwo_coreS p, ?_⟩
  show (memLp_profFun p).toLp _ = _
  exact MeasureTheory.MemLp.toLp_congr (memLp_profFun p) (memLp_schProf (coreS p))
    (Filter.Eventually.of_forall fun r => (congrFun (schProf_coreS p) r).symm)

theorem Dcore_le_restrict : Dcore ≤ D.domRestrict schwartzCore := by
  refine ⟨fun x hx => ⟨?_, Dcore_le_D.1 hx⟩, fun x y hxy => ?_⟩
  · obtain ⟨p, rfl⟩ := hx
    exact prof_mem_schwartzCore p
  · rw [LinearPMap.domRestrict_apply (y := ⟨(y : XG), y.2.2⟩) rfl]
    exact Dcore_le_D.2 hxy

/-- **`D` has Schwartz core** (tex line 1505, "Its selfadjoint closure has Schwartz core"):
`schwartzCore ≤ 𝒟(D)` and the closure of `D` restricted to `schwartzCore` is `D`. -/
theorem hasCore_schwartzCore : D.HasCore schwartzCore where
  le_domain := schwartzCore_le_domain
  closure_eq := by
    refine (closure_eq_D_of_symmetric Dcore_le_restrict fun x y => ?_).2
    rw [LinearPMap.domRestrict_apply (y := ⟨(x : XG), x.2.2⟩) rfl,
      LinearPMap.domRestrict_apply (y := ⟨(y : XG), y.2.2⟩) rfl]
    exact D_symm ⟨(x : XG), x.2.2⟩ ⟨(y : XG), y.2.2⟩

/-! ## The angular-two Hermite levels (tex lines 1506--1510) -/

/-- The coefficients of the Laguerre-type operator `lag p = 4 X p'' + (12 - X) p'`. -/
theorem coeff_lag (p : ℂ[X]) (k : ℕ) :
    (lag p).coeff k =
      4 * ((k : ℂ) + 1) * ((k : ℂ) + 3) * p.coeff (k + 1) - (k : ℂ) * p.coeff k := by
  rw [lag_apply]
  have h4 : (4 : ℂ[X]) * X * derivative (derivative p) =
      C 4 * (derivative (derivative p) * X) := by
    rw [show (4 : ℂ[X]) = C 4 from (map_ofNat C 4).symm]
    ring
  have h12 : ((12 : ℂ[X]) - X) * derivative p = C 12 * derivative p - derivative p * X := by
    rw [show (12 : ℂ[X]) = C 12 from (map_ofNat C 12).symm]
    ring
  rw [h4, h12, coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul]
  cases k with
  | zero =>
    simp only [coeff_mul_X_zero, coeff_derivative]
    push_cast
    ring
  | succ k =>
    rw [coeff_mul_X, coeff_mul_X]
    simp only [coeff_derivative]
    push_cast
    ring

/-- An eigenpolynomial `lag q = -n q`, `q ≠ 0`, has degree exactly `n`. -/
theorem natDegree_eq_of_lag_eigen {q : ℂ[X]} (hq : q ≠ 0) {n : ℕ}
    (h : lag q = -(n : ℂ) • q) : q.natDegree = n := by
  have h1 := congrArg (fun r : ℂ[X] => r.coeff q.natDegree) h
  simp only [coeff_lag, coeff_smul, smul_eq_mul] at h1
  have hz : q.coeff (q.natDegree + 1) = 0 := coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  have hlc : q.coeff q.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.2 hq
  have h2 : (q.natDegree : ℂ) * q.coeff q.natDegree = (n : ℂ) * q.coeff q.natDegree := by
    linear_combination -h1 + (4 * ((q.natDegree : ℂ) + 1) * ((q.natDegree : ℂ) + 3)) * hz
  exact_mod_cast mul_right_cancel₀ hlc h2

theorem coreS_smul (c : ℂ) (q : ℂ[X]) : coreS (c • q) = c • coreS q := by
  ext z
  rw [smul_apply, coreS_apply, coreS_apply, eval_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The core vector `prof p` is the Schwartz-class vector `U_G⁻¹ (coreS p)`. -/
theorem prof_eq_toLp_schProf (p : ℂ[X]) :
    prof p = (memLp_schProf (coreS p)).toLp (schProf (coreS p)) := by
  show (memLp_profFun p).toLp _ = _
  exact MeasureTheory.MemLp.toLp_congr (memLp_profFun p) (memLp_schProf (coreS p))
    (Filter.Eventually.of_forall fun r => (congrFun (schProf_coreS p) r).symm)

/-- **The angular-two Hermite levels** (tex lines 1506--1510). The `ℓ`-th eigenvector of `D` is
`U_G⁻¹` of `coreS q = √(4π) (y₁ + i y₂)² q(|y|²) e^{-|y|²/8}` with `deg q = ℓ`: a polynomial of
total degree `N = 2 + 2ℓ` times `e^{-|y|²/8}`, of angular weight two, on which the oscillator
`Δ - |y|²/16 + 3/2` of `eq:st18-t00067` acts by the eigenvalue `1 - N/2 = -ℓ`. -/
theorem oscBasis_level (n : ℕ) :
    ∃ q : ℂ[X], q.natDegree = n ∧ IsAngularTwo (coreS q) ∧
      oscBasis n = (memLp_schProf (coreS q)).toLp (schProf (coreS q)) ∧
      oscS (coreS q) = (1 - ((2 + 2 * n : ℕ) : ℂ) / 2) • coreS q := by
  obtain ⟨q, hq, hlag⟩ := oscBasis_eigen n
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h1 := oscBasis.orthonormal.1 n
    rw [hq, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨q, natDegree_eq_of_lag_eigen hq0 hlag, isAngularTwo_coreS q, ?_, ?_⟩
  · rw [hq, prof_eq_toLp_schProf]
  · rw [← coreS_lag, hlag, coreS_smul]
    congr 1
    push_cast
    ring

end UnforcedLeray.B0094
