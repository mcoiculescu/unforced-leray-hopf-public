import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Sub.F05_1

/-!
# Part II-a, `PartII-a:F14/1/1/org`: the truncated resolvent and the leaf statements of the core

Source of record: `the November 2 reference manuscript`.

* Lines 1370-1376: the heat-dilation inverse `S(t)h(y) = e^{t/2}[e^{ν(e^t-1)Δ}h](e^{t/2}y)`,
  `ℛ_μ f(τ) = ∫₀^∞ e^{-μt} S(t) f(τ-t) dt`, whose integrand has `Y_r` norm `≤ e^{-a_r t}‖f‖`.
* Lines 1456-1467 (the core of `D_r`): "approximate the right side by smooth periodic Schwartz
  functions and truncate the inverse integral at `M`. Such a truncated integral is Schwartz and its
  equation has right side `f - e^{-μM}S(M)f(τ-M)`. The remainder tends to zero in `Y_r`; the graph
  estimate gives graph convergence of the truncations. Thus the smooth periodic Schwartz class is a
  core. Radial cutoffs approximate it in this graph ...".

The spec of this organizer task cites lines 1424-1445; the core paragraph is at 1456-1467 of the
current file (1424-1445 are the end of the heat estimate and the window estimate, which give the
graph estimate used here).

Concrete objects (the right sides are phase tests, a subclass of the smooth periodic Schwartz
functions):

* `fwdW ν t = √(ν(e^t - 1))`: the heat time `ν(e^t - 1) = fwdW²` of `S(t)`;
* `fwdIntegrand ν μ f t (τ, y) = e^{-(μ-1/2)t} H(w(t); τ - t, e^{t/2} y)` with
  `H = heatGauss f` (the scaled Gaussian average of `Sub/F05_1.lean`, `H(w) = e^{w²Δ}` on slices):
  this is `e^{-μt} [S(t) f(τ - t, ·)](y)`;
* `truncRes ν μ M f = ∫_{(0,M]} fwdIntegrand ν μ f t dt`: the truncated inverse integral.

The leaf `Prop`s below are the analytic facts the source uses; `Sub/F14_1_org.lean` assembles them
into `D2CoreDense` (`d2CoreDense_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-! ### The truncated resolvent integral (lines 1370-1376, 1456-1462) -/

/-- The heat parameter of the forward semigroup: `w(t) = √(ν (e^t - 1))`, so that
`e^{ν(e^t-1)Δ} = e^{w(t)²Δ}` (line 1372). -/
def fwdW (ν t : ℝ) : ℝ := Real.sqrt (ν * (Real.exp t - 1))

/-- The integrand of the body resolvent (lines 1372-1373):
`e^{-μt} [S(t) f(τ - t, ·)](y) = e^{-(μ - 1/2)t} H(w(t); τ - t, e^{t/2} y)`, where
`S(t)h(y) = e^{t/2}[e^{ν(e^t-1)Δ}h](e^{t/2}y)` and `H(w) = heatGauss f w = e^{w²Δ}` on slices. -/
def fwdIntegrand (ν : ℝ) (μ : ℂ) (f : ℝ × Space → CVec3) (t : ℝ) (p : ℝ × Space) : CVec3 :=
  Complex.exp (-((μ - 1 / 2) * (t : ℂ))) •
    heatGauss f (fwdW ν t) (p.1 - t, Real.exp (t / 2) • p.2)

/-- **The truncated inverse integral** (lines 1456-1458): `∫₀^M e^{-μt} S(t) f(τ - t) dt`. -/
def truncRes (ν : ℝ) (μ : ℂ) (M : ℝ) (f : ℝ × Space → CVec3) (p : ℝ × Space) : CVec3 :=
  ∫ t in Ioc (0 : ℝ) M, fwdIntegrand ν μ f t p

/-! ### Leaf statements: the integrand (analogues of the proved `AdjIntegrand*` of `Sub/F05_1.lean`) -/

/-- **Regularity of the integrand** (lines 1372-1376): for a phase test `f`, every
`fwdIntegrand ν μ f t` is `C^∞` and `P`-periodic in the phase, its `(τ, y)`-derivatives are
continuous in `t`, and on every bounded interval `[0, M]` they are bounded uniformly in the
phase-space point (the affine map `(τ, y) ↦ (τ - t, e^{t/2} y)` has linear part of norm
`≤ e^{M/2}`, `‖e^{-(μ-1/2)t}‖ ≤ e^{|Re μ - 1/2| M}`, and `heatGauss f w` has derivative bounds
uniform in `w`, `HeatGaussSmooth`). -/
def FwdIntegrandRegular : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    (∀ t : ℝ, ContDiff ℝ ∞ (fwdIntegrand ν μ f t)) ∧
    (∀ (t τ : ℝ) (y : Space), fwdIntegrand ν μ f t (τ + P, y) = fwdIntegrand ν μ f t (τ, y)) ∧
    (∀ (k : ℕ) (p : ℝ × Space),
      Continuous (fun t : ℝ => iteratedFDeriv ℝ k (fwdIntegrand ν μ f t) p)) ∧
    ∀ (M : ℝ) (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) M, ∀ p : ℝ × Space,
      ‖iteratedFDeriv ℝ k (fwdIntegrand ν μ f t) p‖ ≤ C

/-- **The `t`-derivative of the integrand** (the heat-dilation formula solves
`∂_t S(t) = (νΔ + ½ y·∇ + ½) S(t)`, line 1372): for `t > 0`,
`∂_t F = -(μ - 1/2) F - ∂_τ F + ½ (y·∇)F + ν ΔF`. With `w(t)² = ν(e^t - 1)`, `2 w w' = ν e^t`, and
`∂_w H = 2w Δ_z H` (`HeatGaussEquation`), `∂_w H · w' = ν e^t Δ_z H = ν ΔF / (prefactor)`;
`∂_τ F` picks up the shift `τ - t` with sign `-1`, and `(y·∇)F` the dilation `e^{t/2}y`. -/
def FwdIntegrandDeriv : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ t : ℝ, 0 < t → ∀ p : ℝ × Space,
      HasDerivAt (fun s => fwdIntegrand ν μ f s p)
        (-(μ - 1 / 2) • fwdIntegrand ν μ f t p - dτ (fwdIntegrand ν μ f t) p
          + (1 / 2 : ℝ) • radialT (fwdIntegrand ν μ f t) p
          + ν • lapT (fwdIntegrand ν μ f t) p) t

/-- **Continuity in `t` and the initial value** (`S(0) = 1`): `t ↦ F(t, p)` is continuous on `ℝ`
(`fwdW` is continuous and `heatGauss` is jointly smooth in `(w, τ, z)`, `HeatGaussSmooth`), and
`F(0, p) = f(p)` (`fwdW ν 0 = 0`, `HeatGaussInitial`). -/
def FwdIntegrandCont : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ p : ℝ × Space, Continuous (fun t : ℝ => fwdIntegrand ν μ f t p) ∧
      fwdIntegrand ν μ f 0 p = f p

/-- **Decay of the integrand and its operators on bounded `t`-intervals** ("such a truncated
integral is Schwartz", line 1458): for `t ∈ [0, M]` the integrand and its `∂_τ`, `∂_{y_j}`,
`y·∇`, `Δ` decay like `(1 + |y|)^{-N}` for every `N`, uniformly in `t` and the phase (input
`HeatGaussDecay` with `W = √(ν(e^M - 1)) ≥ |w(t)|`; the argument `z = e^{t/2}y` has `|z| ≥ |y|`,
and `(y·∇)F` is the prefactor times `(z·∇_z H)(τ - t, z)`). -/
def FwdIntegrandDecay : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ (M : ℝ) (N : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) M, ∀ (τ : ℝ) (y : Space),
      ‖fwdIntegrand ν μ f t (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) ∧
      ‖dτ (fwdIntegrand ν μ f t) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) ∧
      (∀ j, ‖dy j (fwdIntegrand ν μ f t) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ))) ∧
      ‖radialT (fwdIntegrand ν μ f t) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) ∧
      ‖lapT (fwdIntegrand ν μ f t) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ))

/-! ### Leaf statements: the truncated integral -/

/-- **The truncated integral is Schwartz** (line 1458): for a phase test `f` and `M ≥ 0`,
`truncRes ν μ M f` is a Schwartz-type phase test in `Y_2` (smooth, periodic, with
`W, ∂ⱼW, ΔW, T₀ᵗW` slice continuous into `L²`). From `FwdIntegrandRegular`,
`FwdIntegrandDecay`, the proved `paramIntegralSmooth_proof`, `opsUnderIntegral_proof` (measure
`volume.restrict (Ioc 0 M)`, constant integrable bounds) and `sliceContOfDecay` (`N = 2`). -/
def TruncResSchwartz : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ M : ℝ, 0 ≤ M → IsPhaseSchwartz P 2 (truncRes ν μ M f)

/-- **The equation of the truncated integral** (lines 1458-1462): pointwise,
`(μ + L₀) W = f - e^{-μM} S(M) f(τ - M)` for `W = truncRes ν μ M f`, `L₀ = 𝒯₀ - νΔ - ½`
(`B0411.L0`). The fundamental theorem of calculus on `[0, M]` applied to
`∂_t F = -(μ + L₀)F` (`FwdIntegrandDeriv`), with `F(0) = f` (`FwdIntegrandCont`), the operators
passed under the integral (`opsUnderIntegral_proof`). -/
def TruncResEquation : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ M : ℝ, 0 ≤ M → ∀ p : ℝ × Space,
      μ • truncRes ν μ M f p + L0 ν (truncRes ν μ M f) p = f p - fwdIntegrand ν μ f M p

/-! ### Leaf statements: the remainder `e^{-μM} S(M) f(τ - M)` (lines 1375-1376, 1463) -/

/-- **`L²` contraction of the Gaussian average**: `‖e^{w²Δ} f(τ, ·)‖_2 ≤ ‖f(τ, ·)‖_2`
(`w = 0`: `HeatGaussInitial`; `w ≠ 0`: `heatGauss_eq_average` and the `L²` contraction of the heat
average, e.g. `Heat.heatLp_rep`, `Heat.norm_heatLpLin_le`, or Jensen plus Tonelli with
`∫ kernel 1 = 1`). -/
def HeatGaussL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (f : ℝ × Space → CVec3), IsPhaseTest P f → ∀ (w τ : ℝ),
    eLpNorm (fun z => heatGauss f w (τ, z)) 2 volume ≤ eLpNorm (fun z => f (τ, z)) 2 volume

/-- **The slice bound of the remainder** (line 1375-1376 at `r = 2`, `γ_2 = 1/4`):
`‖e^{-μM}[S(M) f(τ - M)]‖_{L²} ≤ e^{-(Re μ + 1/4)M} ‖f(τ - M)‖_{L²}`; the prefactor has modulus
`e^{-(Re μ - 1/2)M}` and the dilation `y ↦ e^{M/2}y` scales the `L²` norm by `e^{-3M/4}`. -/
def FwdSliceL2 : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ (M τ : ℝ), 0 ≤ M →
      eLpNorm (fun y => fwdIntegrand ν μ f M (τ, y)) 2 volume ≤
        ENNReal.ofReal (Real.exp (-(μ.re + 1 / 4) * M)) *
          eLpNorm (fun y => f (τ - M, y)) 2 volume

/-- **The remainder tends to zero in `Y_2`** (line 1463, with the rate of line 1376): the
remainder `e^{-μM}S(M)f(τ - M)` is a slice test of `Y_2` with
`‖·‖_{Y_2} ≤ e^{-(Re μ + 1/4)M} ‖f‖_{Y_2}`. -/
def FwdRemainderBound : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ (μ : ℂ) (f : ℝ × Space → CVec3), IsPhaseTest P f →
    ∀ M : ℝ, 0 ≤ M → IsSliceTest P 2 (fwdIntegrand ν μ f M) ∧
      ‖testElem P 2 (fwdIntegrand ν μ f M)‖ ≤
        Real.exp (-(μ.re + 1 / 4) * M) * ‖testElem P 2 f‖

/-! ### Leaf statements: the Schwartz class in the graph, density of the right sides -/

/-- **Schwartz-type functions lie in the maximal graph with their classical operators** (the
classical `𝒯₀Ψ`, `νΔΨ` are the distributional ones; integration by parts against phase tests of
bounded support, as in `B0005.hasT0_testElem`, `B0005.hasHLap_testElem`, where only the test needs
bounded support). -/
def SchwartzGraphIBP : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (q : ℝ≥0∞) [Fact (1 ≤ q)] (ν : ℝ) (Ψ : ℝ × Space → CVec3),
    IsPhaseSchwartz P q Ψ →
      HasPhaseOp (nuLapT ν) (testElem P q Ψ) (testElem P q (nuLapT ν Ψ)) ∧
      HasPhaseOp driftT (testElem P q Ψ) (testElem P q (B0005.T0op Ψ))

/-- **The right sides can be approximated by phase tests** (line 1456-1457, "approximate the
right side by smooth periodic Schwartz functions"): phase tests are dense in `Y_2`
(orthogonality: `phaseInnerEqPairing`, `B0411.eq_zero_of_forall_phasePair`,
`le_topologicalClosure_of_orthogonal` of `Sub/F12.lean`). -/
def PhaseTestsDenseY2 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (g : Yq P 2), ∃ G : ℕ → ℝ × Space → CVec3,
    (∀ n, IsPhaseTest P (G n)) ∧ Tendsto (fun n => testElem P 2 (G n)) atTop (𝓝 g)

end UnforcedLeray.Short.PartIIa
