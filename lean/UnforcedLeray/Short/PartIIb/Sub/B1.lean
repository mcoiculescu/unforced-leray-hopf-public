import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPhasePairing
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedNewtonCurlPotential

/-!
# Part II-b, task `PartII-b:B1`: uniqueness for the ordinary relation (conditional)

Target: `ordRel_unique (p : Params) (z : p.Z) (g g' : p.Y) (h : p.OrdRel z g) (h' : p.OrdRel z g')
: g = g'`. The relational form `OrdRel` of the ordinary system (the Cartesian projected equation
`g = A₀w + 𝔓B_{U_raw}w + …`, tested against solenoidal phase tests) is what the choose-with-default
`Params.lin` is built from; uniqueness of `g` is what makes that definition meaningful. The source
of record fixes the Cartesian Leray projection `𝔓 = ℙ`
(`the November 2 reference manuscript`, lines 119-120), says that "the projected
inverse is obtained by applying Cartesian Leray projection to `f`" (line 1364) and that `R_μ` acts on
solenoidal body forces (line 4147): the force space `Y = Y_{q₀,σ} ∩ {real} ∩ {𝒪-invariant}` consists
of solenoidal elements, which are determined by their pairings with *solenoidal* tests.

## Reduction (proved here, no gap)

`OrdRel` is linear in `g`, so `g - g' ∈ forceSpace` pairs to zero with every solenoidal phase test
(`ordRel_unique_of`). All phase tests separate points of `Y_q`
(`UnforcedLeray.B0411.eq_zero_of_forall_phasePair`). The missing step is
`SolTestSeparation`: a solenoidal `d ∈ Y_{q₀}` that pairs to zero with all solenoidal phase tests
pairs to zero with all phase tests.

## Decomposition of `SolTestSeparation`

For a phase test `Φ` and `d ∈ Y_{q₀,σ}` the existing
`Cons.C03.Concrete.phasePair_lerayProjected_eq_of_phaseSolenoidal` gives `⟪Φ, d⟫ = ⟪𝔓Φ, d⟫` with
`𝔓Φ = projTest P Φ` the slice-wise Leray projection (in `L^{q₀'}`, not compactly supported).
`SolTestApprox` says that `𝔓Φ` is a weak limit (in the pairing with `Y_{q₀}`) of solenoidal phase
tests; `solTestSeparation_of` is the one-line conclusion. For a real test `φ` the approximants are
`curl(χ_R B)` with `B = curl(N * φ)` (`projectedTestNewtonVectorPotentialCurl`), solenoidal tests
by `isSolTest_projectedTestNewtonVectorPotentialCurlCutoff`.

Proved here (complete proofs): `solTestSeparation_of (SolTestApprox)`, `ordRel_unique_of
(SolTestSeparation)`, `phasePairLimit_of (TestElemLimit)`, `realSolTestApprox_of (PhasePairLimit)
(RealSliceConvergence)`. Leaves (tasks `PartII-b:B1/1-9`): `TestElemLimit` (dominated convergence
over the phase), `ProjTestIsNewtonCurl` (`𝔓(realC φ) = curl B`), `NewtonPotentialDerivative`,
`NewtonCurlPotentialDecay` (`|B| ≤ M/(1+|y|)`), `CurlCutoffProductRule`, `CutoffCrossBound` (uses
`3/q₀' = 21/11 < 2`), `CutoffTailSmall`, `RealSliceConvergence` (assembly of the previous ones), and
the complexification `RealSolTestApprox → SolTestApprox`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.RieszLp

/-- The dual exponent `q₀' = 11/7` of `q₀ = 11/4` is at least `1`. -/
instance fact_one_le_conjExp_q0E_B1 : Fact (1 ≤ conjExp q0E) :=
  ⟨by norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

open Classical in
/-- The slice-wise Leray projection `𝔓Φ` of a phase test `Φ` (as a pointwise field, for
`IsPhaseTest P Φ`; the junk value `0` is used otherwise). It is a slice test in `L^{q₀'}`
(`isSliceTest_lerayProjectedPhaseTest`). -/
def projTest (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  if h : IsPhaseTest P Φ then
    lerayProjectedPhaseTest (one_lt_of_holderConjugate q0E_ne_top)
      (conjExp_ne_top one_lt_q0E) (h.isSliceTest (conjExp q0E))
  else 0

theorem projTest_of_isPhaseTest {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (h : IsPhaseTest P Φ) :
    projTest P Φ = lerayProjectedPhaseTest (one_lt_of_holderConjugate q0E_ne_top)
      (conjExp_ne_top one_lt_q0E) (h.isSliceTest (conjExp q0E)) := by
  simp [projTest, h]

/-! ## The statements -/

/-- **Separation by solenoidal tests.** An element `d` of the force space (real, solenoidal,
`𝒪`-invariant) that pairs to zero with every solenoidal phase test pairs to zero with every phase
test. (Source of record: the force space `Y` is built from solenoidal fields on which the
Cartesian Leray projection `𝔓 = ℙ` acts, `the November 2 reference manuscript` lines 119-120, 1364, 4147.) -/
def SolTestSeparation : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (d : Yq P q0E), d ∈ forceSpace P →
    (∀ Φ : ℝ × Space → CVec3, IsSolTest P Φ → phasePair P q0E Φ d = 0) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → phasePair P q0E Φ d = 0

/-- **Solenoidal approximation of the Leray-projected test.** For every complex phase test `Φ`
there are solenoidal phase tests `Ψ n` whose pairings with every `d ∈ Y_{q₀}` converge to the
pairing of `d` with the Leray projection `𝔓Φ` (a weak limit in `Y_{q₀'}`; in fact the approximation
is in the norm of `Y_{q₀'}`). -/
def SolTestApprox : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    ∃ Ψ : ℕ → ℝ × Space → CVec3, (∀ n, IsSolTest P (Ψ n)) ∧
      ∀ d : Yq P q0E,
        Tendsto (fun n => phasePair P q0E (Ψ n) d) atTop (𝓝 (phasePair P q0E (projTest P Φ) d))

/-- **The real case of `SolTestApprox`.** The same for the complexification `realC ∘ φ` of a real
phase test `φ`. -/
def RealSolTestApprox : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∃ Ψ : ℕ → ℝ × Space → CVec3, (∀ n, IsSolTest P (Ψ n)) ∧
      ∀ d : Yq P q0E,
        Tendsto (fun n => phasePair P q0E (Ψ n) d)
          atTop (𝓝 (phasePair P q0E (projTest P (fun z => realC (φ z))) d))

/-- **Norm convergence in `Y_{q₀'}` from slice convergence** (dominated convergence over the
phase, `UnforcedLeray.B0411.norm_rpow_Yq`). If slice tests `Θ n` converge to the slice test `Θ'` in
`L^{q₀'}(ℝ³)` for every phase `τ ∈ [0, P]`, with a bound uniform in `n` and `τ`, then
`testElem (Θ n) → testElem Θ'` in `Y_{q₀'}`. -/
def TestElemLimit : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Θ : ℕ → ℝ × Space → CVec3) (Θ' : ℝ × Space → CVec3),
    (∀ n, IsSliceTest P (conjExp q0E) (Θ n)) → IsSliceTest P (conjExp q0E) Θ' →
    (∀ τ ∈ Icc (0 : ℝ) P, Tendsto (fun n =>
      eLpNorm (fun y => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume) atTop (𝓝 0)) →
    (∃ C : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) P,
      eLpNorm (fun y => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume ≤ ENNReal.ofReal C) →
    Tendsto (fun n => testElem P (conjExp q0E) (Θ n)) atTop (𝓝 (testElem P (conjExp q0E) Θ'))

/-- **Pairing convergence from slice convergence**: the same hypotheses give
`⟪Θ n, d⟫ → ⟪Θ', d⟫` for every `d ∈ Y_{q₀}`. -/
def PhasePairLimit : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (Θ : ℕ → ℝ × Space → CVec3) (Θ' : ℝ × Space → CVec3),
    (∀ n, IsSliceTest P (conjExp q0E) (Θ n)) → IsSliceTest P (conjExp q0E) Θ' →
    (∀ τ ∈ Icc (0 : ℝ) P, Tendsto (fun n =>
      eLpNorm (fun y => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume) atTop (𝓝 0)) →
    (∃ C : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) P,
      eLpNorm (fun y => Θ n (τ, y) - Θ' (τ, y)) (conjExp q0E) volume ≤ ENNReal.ofReal C) →
    ∀ d : Yq P q0E,
      Tendsto (fun n => phasePair P q0E (Θ n) d) atTop (𝓝 (phasePair P q0E Θ' d))

/-- **Derivative of the Newton vector potential**: for a real phase test `φ`, the derivative of
`N * φ` in the spatial direction `e_j` is the Newton potential of the derivative `∂_j φ`
(differentiation under the integral sign: `φ` is smooth with compact spatial support, `N` is
locally integrable). -/
def NewtonPotentialDerivative : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∀ (j : Fin 3) (τ : ℝ) (y : Space),
      fderiv ℝ (projectedTestNewtonVectorPotential φ) (τ, y) (0, coordinateVector j) =
        projectedTestNewtonVectorPotential
          (fun z => fderiv ℝ φ z (0, coordinateVector j)) (τ, y)

/-- **The Leray projection of a real test is the curl of its Newton curl potential.** For a real
phase test `φ`, each slice of `𝔓(realC ∘ φ)` equals a.e. `realC (curl B)`, where
`B = curl (N * φ)`. (Exists privately as `lerayProjected_complexify_eq_actual_ae` in
`Cons/L2/BackgroundConcrete/SelectedProjectedCurlCellLp.lean`.) -/
def ProjTestIsNewtonCurl : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ → ∀ τ : ℝ,
    (fun y => projTest P (fun z => realC (φ z)) (τ, y)) =ᵐ[volume]
      fun y => realC (spatialCurlST (projectedTestNewtonVectorPotentialCurl φ) (τ, y))

/-- **Decay of the Newton curl potential.** For a real phase test `φ`, `B = curl (N * φ)` is
bounded by `M / (1 + |y|)` uniformly for phases in `[0, P]` (`N` the Newtonian kernel; the potential
`N * φ` itself decays like `|y|⁻¹`, and `∂_j (N * φ) = N * ∂_j φ`). -/
def NewtonCurlPotentialDecay : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc (0 : ℝ) P, ∀ y : Space,
      ‖projectedTestNewtonVectorPotentialCurl φ (τ, y)‖ ≤ M / (1 + ‖y‖)

/-- **Product rule for the curl of a cut-off field**: `curl (χ_R B) = χ_R curl B + ∇χ_R × B`. -/
def CurlCutoffProductRule : Prop :=
  ∀ (B : ℝ × Space → Space), ContDiff ℝ ∞ B → ∀ (R τ : ℝ) (y : Space),
    spatialCurlST (fun z => NavierStokesR3.ComparisonCutoffs.cutoff R z.2 • B z) (τ, y) =
      NavierStokesR3.ComparisonCutoffs.cutoff R y • spatialCurlST B (τ, y) +
        Blueprint.crossProd (gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y) (B (τ, y))

/-- **The cross term of the cutoff is small.** If `|B(y)| ≤ M/(1+|y|)` then
`‖∇χ_R × B‖_{L^{q₀'}} ≤ C M R^{-1/11}` for `R ≥ 1`, with `C` an absolute constant: `∇χ_R` is
supported in `R ≤ |y| ≤ 2R` and bounded by `C₀ / R`, so the norm is `≲ M R⁻² · R^{3/q₀'}` and
`3/q₀' = 21/11`, `21/11 - 2 = -1/11`. -/
def CutoffCrossBound : Prop :=
  ∃ C : ℝ, ∀ (M : ℝ) (B : Space → Space), (∀ y : Space, ‖B y‖ ≤ M / (1 + ‖y‖)) →
    ∀ R : ℝ, 1 ≤ R →
      eLpNorm (fun y => Blueprint.crossProd
        (gradField (NavierStokesR3.ComparisonCutoffs.cutoff R) y) (B y)) (conjExp q0E) volume
        ≤ ENNReal.ofReal (C * M * R ^ (-(1 / 11 : ℝ)))

/-- **The cutoff tail vanishes** (dominated convergence): for `F ∈ L^{q₀'}(ℝ³; ℝ³)`,
`‖F - χ_R F‖_{L^{q₀'}} → 0` as `R → ∞`. -/
def CutoffTailSmall : Prop :=
  ∀ F : Space → Space, MemLp F (conjExp q0E) volume →
    Tendsto (fun R : ℝ => eLpNorm (fun y => F y - NavierStokesR3.ComparisonCutoffs.cutoff R y • F y)
      (conjExp q0E) volume) atTop (𝓝 0)

/-- **Slice convergence of the cut-off curl potentials** (the analytic heart of the real case). For
a real phase test `φ`, with `B = curl (N * φ)` and `Ψ_n = curl (χ_{n+1} B)` the solenoidal
cutoff tests (`projectedPotentialCurlCutoff`), the slices `Ψ_n(τ, ·)` converge to the slice of
`𝔓(realC ∘ φ)` in `L^{q₀'}(ℝ³)` for every `τ ∈ [0, P]`, with a bound uniform in `n` and `τ`. -/
def RealSliceConvergence : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (φ : ℝ × Space → Space), IsPhaseTest P φ →
    (∀ τ ∈ Icc (0 : ℝ) P, Tendsto (fun n : ℕ => eLpNorm (fun y =>
        projectedPotentialCurlCutoff ((n : ℝ) + 1) (projectedTestNewtonVectorPotentialCurl φ) (τ, y)
          - projTest P (fun z => realC (φ z)) (τ, y)) (conjExp q0E) volume) atTop (𝓝 0)) ∧
    (∃ C : ℝ, ∀ n : ℕ, ∀ τ ∈ Icc (0 : ℝ) P, eLpNorm (fun y =>
        projectedPotentialCurlCutoff ((n : ℝ) + 1) (projectedTestNewtonVectorPotentialCurl φ) (τ, y)
          - projTest P (fun z => realC (φ z)) (τ, y)) (conjExp q0E) volume
        ≤ ENNReal.ofReal C)

/-! ## The conditional theorems (proved) -/

/-- `SolTestApprox` implies `SolTestSeparation`: for `d` in the force space, `⟪Φ, d⟫ = ⟪𝔓Φ, d⟫`
(`phasePair_lerayProjected_eq_of_phaseSolenoidal`) and `⟪𝔓Φ, d⟫` is the limit of the pairings of
`d` with solenoidal tests, which are zero. -/
theorem solTestSeparation_of (h : SolTestApprox) : SolTestSeparation := by
  intro P _ d hd hsol Φ hΦ
  obtain ⟨Ψ, hΨ, hlim⟩ := h P Φ hΦ
  have hdσ : IsPhaseSolenoidal d := (mem_Ysigma).1 ((mem_forceSpace P).1 hd).2.1
  have h1 : phasePair P q0E (projTest P Φ) d = phasePair P q0E Φ d := by
    rw [projTest_of_isPhaseTest hΦ]
    exact phasePair_lerayProjected_eq_of_phaseSolenoidal hΦ hdσ
  have h2 : Tendsto (fun n => phasePair P q0E (Ψ n) d) atTop (𝓝 0) := by
    have : (fun n => phasePair P q0E (Ψ n) d) = fun _ => (0 : ℂ) :=
      funext fun n => hsol _ (hΨ n)
    rw [this]
    exact tendsto_const_nhds
  rw [← h1]
  exact tendsto_nhds_unique (hlim d) h2

/-- **`ordRel_unique`, conditional on `SolTestSeparation`.** Two solutions of the ordinary
relation `OrdRel z` coincide. -/
theorem ordRel_unique_of (hsep : SolTestSeparation)
    (p : Params) (z : p.Z) (g g' : p.Y)
    (h : p.OrdRel z (g : Yq p.period q0E)) (h' : p.OrdRel z (g' : Yq p.period q0E)) :
    g = g' := by
  have hd : (g : Yq p.period q0E) - (g' : Yq p.period q0E) ∈ forceSpace p.period :=
    Submodule.sub_mem _ g.2 g'.2
  have hsol : ∀ Φ : ℝ × Space → CVec3, IsSolTest p.period Φ →
      phasePair p.period q0E Φ ((g : Yq p.period q0E) - (g' : Yq p.period q0E)) = 0 := by
    intro Φ hΦ
    rw [map_sub, h Φ hΦ, h' Φ hΦ, sub_self]
  have h0 : (g : Yq p.period q0E) - (g' : Yq p.period q0E) = 0 :=
    UnforcedLeray.B0411.eq_zero_of_forall_phasePair
      (fun Φ hΦ => hsep p.period _ hd hsol Φ hΦ)
  exact Subtype.ext (sub_eq_zero.1 h0)

/-- `TestElemLimit` gives `PhasePairLimit` (continuity of the pairing `Y_{q₀'} × Y_{q₀} → ℂ`). -/
theorem phasePairLimit_of (h : TestElemLimit) : PhasePairLimit := by
  intro P _ Θ Θ' hΘ hΘ' hpt hbd d
  have hcont : Continuous (fun a : Yq P (conjExp q0E) => phasePairing P q0E a d) :=
    (ContinuousLinearMap.apply ℂ ℂ d).continuous.comp (phasePairing P q0E).continuous
  exact (hcont.tendsto _).comp (h P Θ Θ' hΘ hΘ' hpt hbd)

/-- The complexification `realC ∘ φ` of a real phase test is a phase test. -/
theorem isPhaseTest_realC_comp {P : ℝ} {φ : ℝ × Space → Space} (hφ : IsPhaseTest P φ) :
    IsPhaseTest P (fun z => realC (φ z)) := by
  have hmap : realC = UnforcedLeray.Axi.cplxV := by
    funext x
    ext i
    simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]
  change IsPhaseTest P (fun z => realC (φ z))
  rw [hmap]
  exact hφ.clm_comp UnforcedLeray.Axi.cplxV

/-- `PhasePairLimit` and `RealSliceConvergence` give `RealSolTestApprox`: the approximants are
`Ψ n = curl (χ_{n+1} B)`, solenoidal tests by
`isSolTest_projectedTestNewtonVectorPotentialCurlCutoff`. -/
theorem realSolTestApprox_of (h1 : PhasePairLimit) (h2 : RealSliceConvergence) :
    RealSolTestApprox := by
  intro P _ φ hφ
  obtain ⟨hconv, hbound⟩ := h2 P φ hφ
  have hsol : ∀ n : ℕ, IsSolTest P (projectedPotentialCurlCutoff ((n : ℝ) + 1)
      (projectedTestNewtonVectorPotentialCurl φ)) := fun n =>
    isSolTest_projectedTestNewtonVectorPotentialCurlCutoff (Fact.out) hφ (by positivity)
  refine ⟨fun n => projectedPotentialCurlCutoff ((n : ℝ) + 1)
    (projectedTestNewtonVectorPotentialCurl φ), hsol, fun d => ?_⟩
  have hc : IsPhaseTest P (fun z => realC (φ z)) := isPhaseTest_realC_comp hφ
  have hslice : IsSliceTest P (conjExp q0E) (projTest P (fun z => realC (φ z))) := by
    rw [projTest_of_isPhaseTest hc]
    exact isSliceTest_lerayProjectedPhaseTest _ _ _
  exact h1 P _ _ (fun n => (hsol n).1.isSliceTest (conjExp q0E)) hslice hconv hbound d

end UnforcedLeray.Short.IIb
