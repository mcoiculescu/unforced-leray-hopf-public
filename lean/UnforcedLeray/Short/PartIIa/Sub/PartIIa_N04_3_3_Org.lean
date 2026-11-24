import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3

/-!
# Sub `PartII-a_N04_3_3_Org`: axis-reaching core class for `A_ε^vec`

Source of record: `the November 2 reference manuscript`,
lines 1838–1845 (the adjoint comparison) and 3340–3363 (the outer semigroup / `A_ε^vec`); the
core statement of the source (lines 1456–1480) uses smooth periodic Schwartz tests with no
support condition at the boundary of the state space, i.e. no band `s₀ ≤ s`.

## Why `IsMeridTest` is not a core (argument, not compiled)

`IsMeridTest c u` forces `u` to vanish for `s < s₀` with `s₀ > 0` (StatementsNear.lean:88),
i.e. the physical lift `fieldU ε u` vanishes in a neighbourhood of the symmetry axis. The domain
of the exact generator `A_ε^vec` (generator of the outer semigroup `S_ε` acting componentwise on
`L²(dx dτ; ℝ³)`) contains axisymmetric `H²(ℝ³)` fields, whose axial component `u_z` need not vanish
on the axis. A line has positive `H²` capacity in `ℝ³` (transversally `H² ⊂ C⁰` in dimension 2),
so evaluation of `u_z` on the axis is a graph-norm continuous functional on the domain which
vanishes on every axis-avoiding test and not on the domain. Hence the closure of the
band-test operator is a proper restriction of `A_ε^vec`, `(μ - A_ε^vec)(IsMeridTest c)` is not dense
(its orthogonal complement contains a Riesz vector of this functional), and the leaf
`MeridTestResolventDense` (hence `RepsVecAdjointOfWeakEq` with the band class) is false as stated.

## The repair

`IsMeridCoreTest ε c` is the class of complex meridional profiles that are smooth for `s > 0`,
`q`-periodic, and whose real and imaginary physical lifts `fieldU ε ·` agree off the axis with
fields that are `C²` on all of `ℝ³ × ℝ` (across the axis), of bounded `x`-support, and
`2εc`-periodic (the lift itself is junk `0` on the axis, see `IsMeridCoreTest`). The restated leaves
`MeridCoreResolventDense` and `RepsVecAdjointOfWeakEqCore` quantify over this class; the
reduction `repsVecAdjointOfWeakEqCore_of` is proved from the left-inverse identity on core tests
and the density leaf.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0221 UnforcedLeray.B0222
open UnforcedLeray.B0223

/-- Axis-reaching vector test fields: every Cartesian component is `C²` on all of `ℝ³ × ℝ`
(including the axis), has bounded `x`-support and is `2εc`-periodic in `τ`. Contrast
`IsTestFieldVec`, which requires vanishing near the axis. -/
structure IsCoreTestFieldVec (ε c : ℝ) (V : Space × ℝ → Space) : Prop where
  smooth : ∀ j : Fin 3, ContDiff ℝ 2 (fun y => V y j)
  bounded : ∃ R : ℝ, ∀ y : Space × ℝ, R < ‖y.1‖ → V y = 0
  periodic : ∀ (x : Space) (τ : ℝ), V (x, τ + 2 * ε * c) = V (x, τ)

/-- **Core tests for `A_ε^vec`.** Complex meridional profiles, smooth on `{s > 0}`, `c`-periodic in
`q`, whose real and imaginary physical lifts extend across the axis to axis-reaching vector test
fields (Cartesian-smooth axisymmetric fields; no band condition at the axis `s → ∞`).

The extension is existential on purpose: on the axis the Lean lift `fieldU` takes the junk value
`0` (`liftA = 0⁻¹ = 0`), so asking `fieldU ε (reMerid f)` itself to be `C²` across the axis would
force the axial component to vanish on the axis. That class misses the (graph-continuous) axis
trace functional, is not a core, and makes `MeridCoreResolventDense` false, exactly as for
`IsMeridTest`. Here only the off-axis values of the lift are prescribed. -/
structure IsMeridCoreTest (ε c : ℝ) (f : Profile → MeridC) : Prop where
  smooth : ContDiffOn ℝ ∞ f {p : Profile | 0 < p.1}
  periodic : QPeriodic c f
  re_core : ∃ V : Space × ℝ → Space, IsCoreTestFieldVec ε c V ∧
    ∀ y : Space × ℝ, B0220.radius y.1 ≠ 0 → V y = B0220.fieldU ε (reMerid f) y
  im_core : ∃ V : Space × ℝ → Space, IsCoreTestFieldVec ε c V ∧
    ∀ y : Space × ℝ, B0220.radius y.1 ≠ 0 → V y = B0220.fieldU ε (imMerid f) y

/-- **Leaf 2, repaired (`MeridCoreResolventDense`)**: `(μ - AepsVecC ν ε)(IsMeridCoreTest ε c)` has
trivial orthogonal complement in `HSpace c MeridC` for `0 < μ.re + 1/4`. -/
def MeridCoreResolventDense : Prop :=
  ∀ (ν c ε : ℝ), 0 < ν → 0 < c → 0 < ε → ε ≤ 1 →
    ∀ (P : ℝ) [Fact (0 < P)], P = 2 * ε * c → P ≤ 1 →
      ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
        ∀ W : HSpace c MeridC,
          (∀ (u : Profile → MeridC) (AUε : HSpace c MeridC),
            IsMeridCoreTest ε c u →
            (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
            inner ℂ AUε W = 0) →
          W = 0

/-- **Leaf 3, repaired (`RepsVecAdjointOfWeakEqCore`)**: weak characterization of
`RepsVec.adjoint R0` against axis-reaching core tests. -/
def RepsVecAdjointOfWeakEqCore : Prop :=
  ∀ (ν c ε : ℝ) (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
    ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
        ∀ V R0 : HSpace c MeridC,
          (∀ (u : Profile → MeridC) (U AUε : HSpace c MeridC),
            IsMeridCoreTest ε c u →
            (U : Profile → MeridC) =ᵐ[measureH c] u →
            (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
            inner ℂ AUε V = inner ℂ U R0) →
          V = ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) R0

/-- Left-inverse identity on core tests (the repaired counterpart of `repsVec_left_of_outerS`). -/
def RepsVecLeftOnCore : Prop :=
  ∀ (ν c ε : ℝ) (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε), ε ≤ 1 →
    ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
        ∀ (u : Profile → MeridC) (U AUε : HSpace c MeridC),
          IsMeridCoreTest ε c u →
          (U : Profile → MeridC) =ᵐ[measureH c] u →
          (AUε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • u p - AepsVecC ν ε u p) →
          B0223.RepsVec hν hε hc hP μ AUε = U

/-- Core tests are square integrable (analytic input: the lift is `C²`, compactly supported,
`‖u‖_H² = ∫ s^{-3/2}…`; Haiku-sized leaf). -/
def MeridCoreTestMemLp : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ u : Profile → MeridC,
    IsMeridCoreTest ε c u → MemLp u 2 (measureH c)

/-- Conditional assembly of `RepsVecAdjointOfWeakEqCore` from the left inverse on core tests, the
square integrability of core tests and the repaired density leaf. -/
theorem repsVecAdjointOfWeakEqCore_of
    (hLeft : RepsVecLeftOnCore) (hMem : MeridCoreTestMemLp)
    (hDense : MeridCoreResolventDense) : RepsVecAdjointOfWeakEqCore := by
  intro ν c ε hν hc hε hε1 P _ hP hP1 μ hγ V R0 hweak
  rw [← sub_eq_zero]
  refine hDense ν c ε hν hc hε hε1 P hP hP1 μ hγ
    (V - ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) R0) ?_
  intro u AUε hu hAUε
  have hU_mem : MemLp u 2 (measureH c) := hMem c ε hc hε u hu
  set U : HSpace c MeridC := hU_mem.toLp u
  rw [inner_sub_right, hweak u U AUε hu hU_mem.coeFn_toLp hAUε,
    ContinuousLinearMap.adjoint_inner_right,
    hLeft ν c ε hν hc hε hε1 P hP hP1 μ hγ u U AUε hu hU_mem.coeFn_toLp hAUε, sub_self]

end UnforcedLeray.Short.PartIIa
