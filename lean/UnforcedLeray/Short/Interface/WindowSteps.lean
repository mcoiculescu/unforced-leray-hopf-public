import UnforcedLeray.Short.Interface.Statements
import UnforcedLeray.Units.B0423

/-!
# Interface: the steps of `L²` maximal regularity of the free equation

Decomposition of the two leaves `FreeWindowRegularity` and `WindowsToGlobalLaplacian` of
`Statements.lean` into drafting-sized Props. The mathematics is the proof of
`eq:free-stress-13`-`-17` of the old manuscript (`paper/main.tex` lines 7479-7536; blueprint
B0424-B0426, B0438) for `q = 2`:

* chart `v(t,x) = e^{-t/2} w(τ₀ + t, e^{-t/2}x)`, `g = e^{-t/2}(-f - μw)(τ₀ + t, e^{-t/2}x)` gives
  `v_t - h e^t Δ_x v = g` (13);
* time change `θ = e^t` and a cutoff `χ ∈ C_c^∞(-2,2)`, `χ = 1` on `[-1,1]`, give
  `(∂_θ - hΔ_x)u = θ^{-1}(χg + χ'v)` for `u = χ v` (14);
* the compiled heat maximal regularity (`Units/B0423.lean`, `heat_estimate_laplacian`, `q = 2`)
  gives `Δ_x u ∈ L²`;
* back to `(τ, y)`: `Δ_y w(τ₀ + t, y) = e^{3t/2}(Δ_x u)(e^t, e^{t/2}y)` for `|t| < 1`.

Here `f` is a periodic `𝒴₂` representative of `𝔓g` (`exists_projected_rep`,
`Cons/C08PhysicalMode/Free.lean`), so that the free equation reads
`(μ + 𝒯₀ - hΔ - ½)w + f = 0` (`IsSourceFreeSolution`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic

/-- The free equation `(μ + 𝒯₀ - hΔ - ½)w + f = 0` in distributions on `ℝ × ℝ³`, every
derivative on the test, each pairing integrable. -/
def IsSourceFreeSolution (h μ : ℝ) (w f : ℝ → SpatialField) : Prop :=
  (∀ ψ, IsSimilarityTest ψ →
    Integrable (pairTerm w ψ) ∧ Integrable (temporalTerm w ψ) ∧ Integrable (dilationTerm w ψ) ∧
      Integrable (diffusionTerm w ψ) ∧ Integrable (pairTerm f ψ)) ∧
  ∀ ψ, IsSimilarityTest ψ →
    (∫ z, weakModeIntegrand h μ w ψ z) + (∫ z, pairTerm f ψ z) = 0

/-- The window estimate in source form (`f` a `𝒴₂` field instead of `𝔓g`). -/
def SourceWindowRegularity : Prop :=
  ∀ (h μ P : ℝ) (w f : ℝ → SpatialField), 0 < h → 0 < P →
    B0005.IsY2 P w → B0005.IsY2 P f → IsSourceFreeSolution h μ w f →
    ∀ τ₀ : ℝ, ∃ Λ : ℝ → SpatialField,
      MemLp (fun z : SpaceTime => Λ z.1 z.2) 2 (volume.restrict (windowSlab τ₀ 1)) ∧
      ∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ windowSlab τ₀ 1 → laplacianPairing w Λ ψ

/-- Step W0: `FreeWindowRegularity` from the source form, with `f` the periodic `𝒴₂`
representative of `𝔓g` (`exists_projected_rep`, `integral_pairTerm_projected`,
`Cons/C08PhysicalMode/Free.lean`). -/
def WindowReduction : Prop := SourceWindowRegularity → FreeWindowRegularity

/-- The time cutoff of line 7490: `χ ∈ C_c^∞(-2,2)`, `χ = 1` on `[-1,1]`. -/
structure IsWindowCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  compact : HasCompactSupport χ
  support : tsupport χ ⊆ Ioo (-2 : ℝ) 2
  one : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1

/-- The chart field `v(t,x) = e^{-t/2} w(τ₀ + t, e^{-t/2}x)` (line 7485). -/
def chartField (τ₀ : ℝ) (w : ℝ → SpatialField) (t : ℝ) (x : Space) : Space :=
  Real.exp (-(t / 2)) • w (τ₀ + t) (Real.exp (-(t / 2)) • x)

/-- Component `i` of `u(θ,x) = χ(log θ) v(log θ, x)`, extended by zero for `θ ≤ 0`
(line 7493). -/
def windowU (χ : ℝ → ℝ) (τ₀ : ℝ) (w : ℝ → SpatialField) (i : Fin 3) (X : ℝ × Space) : ℝ :=
  if 0 < X.1 then χ (Real.log X.1) * chartField τ₀ w (Real.log X.1) X.2 i else 0

/-- Component `i` of `θ⁻¹(χg + χ'v)` with `g = -(chartField f + μ chartField w)` (lines
7488, 7493), zero for `θ ≤ 0`. -/
def windowF (χ : ℝ → ℝ) (μ τ₀ : ℝ) (w f : ℝ → SpatialField) (i : Fin 3) (X : ℝ × Space) : ℝ :=
  if 0 < X.1 then
    X.1⁻¹ * (χ (Real.log X.1) * (-(chartField τ₀ f (Real.log X.1) X.2 i +
        μ * chartField τ₀ w (Real.log X.1) X.2 i)) +
      deriv χ (Real.log X.1) * chartField τ₀ w (Real.log X.1) X.2 i)
  else 0

/-- Step W1 (`eq:free-stress-13`, `-14`): `(∂_θ - hΔ_x)u = F` in distributions on
`(0,∞) × ℝ³ ⊂ PS 3`. Large: distributional chain rule under the dilation and the time change;
the transposed tests are in `Units/B0424/Calc.lean` (`phaseTest`, `L0T_phaseTest`) and
`Units/B0424/Tests.lean` (`timeTest`, `lapTest`); the Jacobians in `Units/B0424/Chart.lean`. -/
def WindowChartEquation : Prop :=
  ∀ (h μ P : ℝ) (w f : ℝ → SpatialField) (χ : ℝ → ℝ) (τ₀ : ℝ) (i : Fin 3), 0 < h → 0 < P →
    B0005.IsY2 P w → B0005.IsY2 P f → IsSourceFreeSolution h μ w f → IsWindowCutoff χ →
    B0423.IsWeakHeatSol (d := 3) h (windowU χ τ₀ w i) (windowF χ μ τ₀ w f i)

/-- Step W2: `u` and `F` are in `L²(ℝ × ℝ³)` (Jacobians `dx = e^{3t/2}dy`, `dθ = e^t dt`;
`Units/B0424/Chart.lean`, `Units/B0424/Rep.lean`). -/
def WindowChartL2 : Prop :=
  ∀ (h μ P : ℝ) (w f : ℝ → SpatialField) (χ : ℝ → ℝ) (τ₀ : ℝ) (i : Fin 3), 0 < P →
    B0005.IsY2 P w → B0005.IsY2 P f → IsWindowCutoff χ →
    MemLp (windowU χ τ₀ w i) 2 volume ∧ MemLp (windowF χ μ τ₀ w f i) 2 volume

/-- Step W4: from the weak second derivatives of the three components `u_i` (the output of the
heat maximal regularity) to the window Laplacian of `w` (transport back to `(τ, y)`:
`Λ_i(τ₀ + t, y) = e^{3t/2} Σ_j D2_{ijj}(e^t, e^{t/2}y)` for `|t| < 1`; test transfer by
`lapTest`, `sLap_lapTest` of `Units/B0424/Tests.lean`). -/
def WindowTransportBack : Prop :=
  ∀ (P : ℝ) (w : ℝ → SpatialField) (χ : ℝ → ℝ) (τ₀ : ℝ), 0 < P →
    B0005.IsY2 P w → IsWindowCutoff χ →
    (∀ i : Fin 3, ∃ D2 : Fin 3 → Fin 3 → ℝ × Space → ℝ, ∀ a b,
      MemLp (D2 a b) 2 volume ∧ B0423.HasWeakSpaceDeriv2 (d := 3) (windowU χ τ₀ w i) a b (D2 a b)) →
    ∃ Λ : ℝ → SpatialField,
      MemLp (fun z : SpaceTime => Λ z.1 z.2) 2 (volume.restrict (windowSlab τ₀ 1)) ∧
      ∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ windowSlab τ₀ 1 → laplacianPairing w Λ ψ

/-! ## Patching the windows -/

/-- Step G1 (fundamental lemma): two locally integrable weak Laplacians of `w` on an open set
agree almost everywhere there (Mathlib `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`,
applied to the components). -/
def WeakLaplacianUnique : Prop :=
  ∀ (w Λ₁ Λ₂ : ℝ → SpatialField) (O : Set SpaceTime), IsOpen O →
    LocallyIntegrableOn (fun z : SpaceTime => Λ₁ z.1 z.2) O volume →
    LocallyIntegrableOn (fun z : SpaceTime => Λ₂ z.1 z.2) O volume →
    (∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ O → laplacianPairing w Λ₁ ψ) →
    (∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ O → laplacianPairing w Λ₂ ψ) →
    (fun z : SpaceTime => Λ₁ z.1 z.2) =ᵐ[volume.restrict O] (fun z : SpaceTime => Λ₂ z.1 z.2)

/-- Step G2a (gluing): window Laplacians on the windows `(n-1,n+1) × ℝ³`, `n ∈ ℤ`, glue to one
field `L` that is a weak Laplacian of `w` against all tests (partition of unity in the phase
subordinate to the windows; a test has compact support, so only finitely many pieces occur). -/
def WindowGlueLocal : Prop :=
  ∀ (w : ℝ → SpatialField) (Λ : ℤ → ℝ → SpatialField),
    (∀ n : ℤ, MemLp (fun z : SpaceTime => Λ n z.1 z.2) 2 (volume.restrict (windowSlab n 1)) ∧
      ∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ windowSlab n 1 → laplacianPairing w (Λ n) ψ) →
    ∃ L : ℝ → SpatialField,
      AEStronglyMeasurable (fun z : SpaceTime => L z.1 z.2) volume ∧
      (∀ n : ℤ, MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (windowSlab n 1))) ∧
      ∀ ψ, IsSimilarityTest ψ → laplacianPairing w L ψ

/-- Step G2b (periodic selection): a locally `L²` weak Laplacian `L` of a `𝒯`-periodic `w` is
almost everywhere `𝒯`-periodic (translate the test, then `WeakLaplacianUnique` on `ℝ × ℝ³`), so
`τ ↦ L(toIocMod τ)` (`periodize`, `Cons/C08PhysicalMode/Slices.lean`) is a `𝒴₂` field that is
again a weak Laplacian. -/
def PeriodicSelection : Prop :=
  ∀ (P : ℝ) (w L : ℝ → SpatialField), 0 < P → B0005.IsY2 P w →
    AEStronglyMeasurable (fun z : SpaceTime => L z.1 z.2) volume →
    (∀ n : ℤ, MemLp (fun z : SpaceTime => L z.1 z.2) 2 (volume.restrict (windowSlab n 1))) →
    (∀ ψ, IsSimilarityTest ψ → laplacianPairing w L ψ) →
    ∃ lapB : ℝ → SpatialField, B0005.IsY2 P lapB ∧
      ∀ ψ, IsSimilarityTest ψ → laplacianPairing w lapB ψ

end UnforcedLeray.Short.Interface
