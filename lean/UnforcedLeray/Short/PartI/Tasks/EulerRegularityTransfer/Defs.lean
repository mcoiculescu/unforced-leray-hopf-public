import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.Sub.S13a

/-!
# Part I, task `PartI:S13c`: concrete objects for the regularity transfer to `H^j_M`

Source of record: `the November 2 reference manuscript`,
lines 853-889.

Downstream check (the `j = 0`-suffices question): the all-`j` statements cannot be dropped.  The
dilation corollary (lines 936-950) conjugates `eq:short-seed-complement` on `H^j_M` by the
dilations `J_a`, "uniformly bounded on `H^j_M`", so the first complement estimate is used for every
`j`; the spectrum statement (lines 593-598) is also stated for every `j`.  Part III (line 2930)
only uses the full-space (`j = 0`) stability.  Hence `SeedEulerSpectrum`/`SeedEulerComplement`
remain quantified over all `j`, and `PartI:S13c` is kept.

Objects defined here (all concrete, none a free predicate on source objects):

* `IsFreeTransportGroupHjM`: a family `T t` of operators on `H^j_M` representing the free
  transport `T(t)f(r,ϑ) = f(r, ϑ - Ω(r) t)` (`freeFlow`), a strongly continuous group with
  `‖T(t)‖ ≤ C (1+|t|)^j` (output of `transport_group_HjM`, lines 841-852).
* `IsEulerEvolutionHjM`: a strongly continuous group `S t` on `H^j_M` whose values are those of
  `Planar.eulerGroupW hM t` on `L²_M` (the realization `e^{t𝓛}` of lines 858-860).
* `EulerEvolutionHjMExists`: such an `S` exists, and maps `𝒳_{j,M}` to itself (lines 858-860).
* `DuhamelDifferenceCompactHjM`: `e^{t𝓛} - T(t)` is compact for `t > 0` (lines 862-865).
* `EssentialGrowthBoundZeroHjM`: the essential growth bound is `≤ 0`, in the concrete form
  "for every `η > 0` `e^{t𝓛}` is within `C e^{ηt}` of a compact operator" (line 866).
* `GrowingSpectrumDiscreteHjM`: for each `η > 0`, the spectrum in `{Re z ≥ η}` is a finite set of
  eigenvalues with finite-dimensional root spaces (lines 866-868).
* `EulerResolventAgreeHjM`, `EulerResolventTransfer`: resolvents on `H^j_M` and `H^0_M` agree
  (lines 876-878); part (a) of `euler_regularity_transfer`.
* `EulerComplementHjM`: the first estimate of `eq:short-seed-complement` for a fixed `j, M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- `T` represents the free transport on `H^j_M`: a strongly continuous group with polynomial
growth `‖T(t)‖ ≤ C (1+|t|)^j` whose values are `f(r, ϑ - Ω(r) t)` (`freeFlow`). -/
def IsFreeTransportGroupHjM (j : ℕ) {M : ℝ} (T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M)) : Prop :=
  (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) ∧
  (∀ s t, T (s + t) = T s * T t) ∧ T 0 = 1 ∧
  (∀ F, Continuous fun t => T t F) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C * (1 + |t|) ^ j)

/-- `S` represents the Euler evolution `e^{t𝓛}` on `H^j_M`: a strongly continuous group of bounded
operators whose values are those of the `L²_M` Euler group `Planar.eulerGroupW hM t`. -/
def IsEulerEvolutionHjM (j : ℕ) {M : ℝ} (hM : 1 < M)
    (S : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M)) : Prop :=
  (∀ t F, ((S t F).value : ℂ → ℂ) =ᵐ[volume] ⇑(Planar.eulerGroupW hM t F.value)) ∧
  (∀ s t, S (s + t) = S s * S t) ∧ S 0 = 1 ∧ (∀ F, Continuous fun t => S t F)

/-- **Part (b)** (lines 858-860, 884-889): the Euler evolution exists on `H^j_M` (restriction of
`Planar.eulerGroupW`) and leaves `𝒳_{j,M}` invariant. -/
def EulerEvolutionHjMExists (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∃ S : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M), IsEulerEvolutionHjM j hM S ∧
    ∀ t, ∀ F ∈ B0008.XjM j M, S t F ∈ B0008.XjM j M

/-- **Compact Duhamel difference** (lines 862-865): `e^{t𝓛} - T(t)` is a compact operator on
`H^j_M` for every `t > 0`. -/
def DuhamelDifferenceCompactHjM (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ S T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
    IsEulerEvolutionHjM j hM S → IsFreeTransportGroupHjM j T →
      ∀ t : ℝ, 0 < t → IsCompactOperator (S t - T t)

/-- **Essential growth bound `≤ 0`** (line 866), without Mathlib essential-spectrum theory: for
every `η > 0` there is `C` with `e^{t𝓛}` within `C e^{ηt}` (operator norm) of a compact operator
on `H^j_M`, for all `t ≥ 0`. -/
def EssentialGrowthBoundZeroHjM (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ S : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M), IsEulerEvolutionHjM j hM S →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∃ K : B0008.HjM j M →L[ℂ] B0008.HjM j M, IsCompactOperator K ∧
        ‖S t - K‖ ≤ C * Real.exp (η * t)

/-- The root space of `𝓛` at `z` on `𝒳_{j,M}`: `F` with `(z - 𝓛)^n F = 0` for some `n`, given as a
chain `G 0 = F`, `(z - 𝓛) G i = G (i+1)`, `G n = 0` inside `𝒟(𝓛)`. -/
def eulerRootSpace (j : ℕ) {M : ℝ} (hM : 1 < M) (z : ℂ) : Set (B0008.XjM j M) :=
  {F | ∃ (n : ℕ) (G : ℕ → (B0009.generator j hM).domain),
    ((G 0 : (B0009.generator j hM).domain) : B0008.XjM j M) = F ∧
    (∀ i, i < n → (⇑(B0009.generator j hM (G i)) : ℂ → ℂ) =ᵐ[volume]
      fun y => z * xValue ((G i : (B0009.generator j hM).domain) : B0008.XjM j M) y -
        xValue ((G (i + 1) : (B0009.generator j hM).domain) : B0008.XjM j M) y) ∧
    ((G n : (B0009.generator j hM).domain) : B0008.XjM j M) = 0}

/-- **Growing spectrum is discrete of finite algebraic multiplicity** (lines 866-868): for each
`η > 0` the set of `z` with `Re z ≥ η` outside the resolvent set is finite, each such `z` is an
eigenvalue, and its root space is contained in the span of finitely many vectors. -/
def GrowingSpectrumDiscreteHjM (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ η : ℝ, 0 < η →
    {z : ℂ | η ≤ z.re ∧ ¬ EulerResolvent j hM z}.Finite ∧
    ∀ z : ℂ, η ≤ z.re → ¬ EulerResolvent j hM z →
      (∃ F, IsEulerEigen j hM z F) ∧
      ∃ s : Finset (B0008.XjM j M),
        eulerRootSpace j hM z ⊆ (Submodule.span ℂ (s : Set (B0008.XjM j M)) : Set _)

/-- **Resolvents agree on intersections of weighted spaces** (lines 876-878): for `Re z > 0` in the
`H^0_M` resolvent set, a solution of `(z - 𝓛) F = g` in `𝒟(𝓛_j)` and a solution of
`(z - 𝓛) F₀ = g₀` in `𝒟(𝓛_0)`, with `g, g₀` equal a.e., are equal a.e. -/
def EulerResolventAgreeHjM (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ z : ℂ, 0 < z.re → EulerResolvent 0 hM z →
    ∀ (g : B0008.XjM j M) (g₀ : B0008.XjM 0 M)
      (F : (B0009.generator j hM).domain) (F₀ : (B0009.generator 0 hM).domain),
      xValue g₀ =ᵐ[volume] xValue g →
      (⇑(B0009.generator j hM F) : ℂ → ℂ) =ᵐ[volume]
        (fun y => z * xValue (F : B0008.XjM j M) y - xValue g y) →
      (⇑(B0009.generator 0 hM F₀) : ℂ → ℂ) =ᵐ[volume]
        (fun y => z * xValue (F₀ : B0008.XjM 0 M) y - xValue g₀ y) →
      xValue (F₀ : B0008.XjM 0 M) =ᵐ[volume] xValue (F : B0008.XjM j M)

/-- **Part (a)** (lines 876-878): `Re z > 0` in the `H^0_M` resolvent set implies `z` is in the
`H^j_M` resolvent set: the solution of `(z - 𝓛) F = g` lies in `𝒳_{j,M}` (in `𝒟(𝓛_j)`) with
`‖F‖_{H^j_M} ≤ C ‖g‖_{H^j_M}`. -/
def EulerResolventTransfer (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ z : ℂ, 0 < z.re → EulerResolvent 0 hM z → EulerResolvent j hM z

/-- **Part (c)**: the first estimate of `eq:short-seed-complement` (lines 612-615) for fixed
`j, M`: `‖e^{t𝓛}(I - 𝒫)‖_{H^j_M → H^j_M} ≤ C e^{ηt}`. -/
def EulerComplementHjM (j : ℕ) {M : ℝ} (hM : 1 < M) : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ f : B0008.XjM j M,
        ∃ (u : Planar.L2w M) (g : B0008.XjM j M),
          (⇑u =ᵐ[volume] fun y => xValue f y - seedProjFun h (xValue f) y) ∧
          xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hM t u) ∧
          ‖g‖ ≤ C * Real.exp (η * t) * ‖f‖

/-- `EulerComplementHjM` for all `j, M` is exactly `SeedEulerComplement`. -/
theorem seedEulerComplement_of_all (h : ∀ (j : ℕ) (M : ℝ) (hM : 1 < M), EulerComplementHjM j hM) :
    SeedEulerComplement :=
  fun lam hh hhh ℓ hs j M hM η hη => h j M hM lam hh hhh ℓ hs η hη

end UnforcedLeray.Short.PartI
