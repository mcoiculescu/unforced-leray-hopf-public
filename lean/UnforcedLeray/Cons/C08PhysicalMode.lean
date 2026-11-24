import UnforcedLeray.Cons.C08PhysicalMode.BodyForce
import UnforcedLeray.Cons.C08PhysicalMode.Free
import UnforcedLeray.Cons.C08PhysicalMode.Symmetry

/-!
# Step C8: the lift of a zero-entrance mode is a graph mode (`StepPhysicalMode`)

`StepPhysicalMode` (`Blueprint/Construction/Steps.lean`, line 359); `paper/main.tex`
lines 10900–10911 (`eq:st18-t00633`, the weak-to-body upgrade), 13693–13707
(`eq:st18-t00770` and the sentence at 13702), 13726–13742 (the identification with
`prop:unstable-background`), 7700–7720 (the Hilbert structure of the free operator). Blueprint
units B0773 (`eq:st18-t00633`), B1005 (`eq:st18-t00770`), B1006 (`unlabeled:13702`).

**What is proved.** `stepPhysicalMode_of : FreeLaplacianRegularity → StepPhysicalMode`, with one
named hypothesis, the `L²` Laplacian estimate for the free equation (blueprint units B0424 and
B0426, `eq:free-stress-15`, `eq:free-stress-17`, tex 7479–7536; the regularity half of the
maximal-domain statement B0438, tex 7601–7604), which no compiled module provides:

* `FreeLaplacianRegularity`: a real periodic `w` in the `H¹` class solving the free equation
  `(μ + 𝒯₀ - hΔ - ½) w + 𝔓 g = 0` in distributions, with `g ∈ 𝒴₂` and `μ > -1/4`, has
  `Δw ∈ 𝒴₂`.

Everything else in lines 10900–10911 and 13693–13742 is proved:
* the body force: `𝔓 div(U⊗w + w⊗U) = 𝔓 f` with `f ∈ 𝒴₂`, phase by phase, for bounded
  `U, ∇U` and `w, ∇w ∈ 𝒴₂` (`exists_bodyForce`, `C08PhysicalMode/BodyForce.lean`), so the
  zero-entrance equation is a free equation with a `𝒴₂` right side (`isWeakFreeSolution_of`);
* `𝒯₀w = hΔw - (μ - ½)w - 𝔓f ∈ 𝒴₂` from the equation (tex 7535, "The equation gives the same
  type of bound on `T₀w`"), with a jointly measurable representative of `𝔓f`, and the graph
  `loc:eq:graph` with solenoidal `Δw`, `𝒯₀w` through the compiled B0005 bridge
  (`inPeriodicGraph_of_laplacian`, `C08PhysicalMode/Free.lean`); hence the maximal-domain form
  `FreeGraphMaximalDomain` (B0438) follows (`freeGraphMaximalDomain_of`);
* the exact mode equation `loc:eq:mode` with the literal `𝔓` from the graph identities
  (`solvesModeEquation_of`);
* the symmetry of the lift (`cylinderLift_axisymmetric`, `C08PhysicalMode/Symmetry.lean`), at
  every phase, from the formula `eq:st18-t00770`;
* nonvanishing is the hypothesis of the step, passed through.

The solenoidality of `U` and the bounds `R > 0`, `σ < 1/4` of the step are not used: the body
force is kept as the literal divergence `Σ_j ∂_j(U_jw + w_jU)`, which equals `U·∇w + w·∇U` only
because both fields are solenoidal, and `σ > 0 > -1/4` is all the free estimate needs.

**On the hypothesis.** The manuscript states the free theorem under the standing assumptions
`ν > 0`, `0 < P ≤ 1` of §`sec:st18-8873` (tex 7306–7308), for complex `Y_q` fields. The
Laplacian bound is the fixed-window local estimate (B0424, tex 7479–7500, which "applies to
every distributional `Y_q` solution with a `Y_q` right side") integrated in its center
(B0425–B0426, tex 7519–7536); the windows have fixed length, so `P ≤ 1` only makes the constants
uniform, and no sign of `Re μ` is used. Real fields are real parts of complex solutions. The
hypothesis is stated for real fields, every `P > 0`, real `μ > -1/4`, with the extra
assumptions that `w` is in the `H¹` class and that the right side is a Leray projection `𝔓 g`
(both make it weaker than B0424/B0438). `StepPhysicalMode` quantifies over all periods; in the
construction the period is `P_n = 2ε_nc_n → 0`.

Junk values: every pairing in `IsWeakFreeSolution` carries its integrability clause;
`toL2 (g τ)` is the junk `0` only on the null set of phases where `g(τ) ∉ L²`.

Status: `StepPhysicalMode` is proved from `FreeLaplacianRegularity`; the hypothesis is open in
Lean. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C08

open UnforcedLeray.Blueprint

/-! ## The named hypothesis -/

/-- **Named hypothesis: the `L²` Laplacian estimate for the free equation** (blueprint units
B0424 `eq:free-stress-15` and B0426 `eq:free-stress-17`, the regularity half of B0438
`unlabeled:7601`; tex 7479–7536, 7601–7604; used at 10904–10905, B0773: the body inverse
"places `w` in the original graph with `νΔw, Bw ∈ Y₂`").

For `h > 0`, `𝒯 > 0` and real `μ > -1/4`: a real `𝒯`-periodic field `w` of the periodic `H¹`
class (`w, ∇w ∈ 𝒴₂`, `w` solenoidal) solving `(μ + 𝒯₀ - hΔ - ½) w + 𝔓 g = 0` in distributions
(`IsWeakFreeSolution`), with `g ∈ 𝒴₂` real and `𝒯`-periodic, has `Δw ∈ 𝒴₂`: there is a real
periodic `lapB ∈ 𝒴₂` with `∫∫⟨w, Δψ⟩ = ∫∫⟨lapB, ψ⟩` for every test.

The manuscript proves it for complex fields under `0 < P ≤ 1` (B0424: for "any distributional
solution of `(μ+L₀)w = P_σ f` with `f ∈ Y_q`", `∫_{τ₀-1}^{τ₀+1}‖νΔw‖_q^q ≤
C_q∫_{τ₀-2}^{τ₀+2}(‖f‖_q^q + (1+|μ|)^q‖w‖_q^q)`, averaged over the center in B0426); see the
module docstring for why the proof applies to every `P > 0`. -/
def FreeLaplacianRegularity : Prop :=
  ∀ (h P μ : ℝ) (w g : ℝ → SpatialField), 0 < h → 0 < P → -(1 / 4 : ℝ) < μ →
    IsH1Periodic P w → B0005.IsY2 P g → IsWeakFreeSolution h μ w g →
      ∃ lapB : ℝ → SpatialField, B0005.IsY2 P lapB ∧
        ∀ ψ, IsSimilarityTest ψ → laplacianPairing w lapB ψ

/-- **The free graph is the maximal distributional domain at `q = 2`**
(blueprint units B0438 `unlabeled:7601`, B0424 `eq:free-stress-15`, B0439 `unlabeled:7364`,
B0440 `eq:m3-free-graph`; tex 7364–7387, 7479–7536, 7598–7604; used at 10904–10905, B0773:
"Section `sec:free-stress`'s body inverse then places `w` in the original graph with
`νΔw, Bw ∈ Y₂`").

For `h > 0`, `𝒯 > 0` and real `μ > -1/4`: a real `𝒯`-periodic field `w` of the periodic `H¹`
class (`w, ∇w ∈ 𝒴₂`, `w` solenoidal) solving `(μ + 𝒯₀ - hΔ - ½) w + 𝔓 g = 0` in distributions,
with `g ∈ 𝒴₂` real and `𝒯`-periodic, lies in the graph `loc:eq:graph`: there are
`Δw, 𝒯₀w ∈ 𝒴_{2,div}`.

The manuscript proves it (B0438: "every distributional `w ∈ Y_q` solving `(μ+L₀)w = g` with
`g ∈ Y_q` belongs to `D_(ν,q)`") for complex fields under `0 < P ≤ 1`; see the module docstring
for why the proof applies to every `P > 0`. It follows from `FreeLaplacianRegularity`
(`freeGraphMaximalDomain_of`): `𝒯₀w` is read off the equation and the solenoidality of `Δw`,
`𝒯₀w` is automatic (`B0005.inPeriodicGraph_iff`). -/
def FreeGraphMaximalDomain : Prop :=
  ∀ (h P μ : ℝ) (w g : ℝ → SpatialField), 0 < h → 0 < P → -(1 / 4 : ℝ) < μ →
    IsH1Periodic P w → B0005.IsY2 P g → IsWeakFreeSolution h μ w g →
      ∃ lapB driftB : ℝ → SpatialField, InPeriodicGraph P w lapB driftB

/-- The Laplacian estimate gives the maximal-domain statement (tex 7533–7536, 7601–7604). -/
theorem freeGraphMaximalDomain_of (H : FreeLaplacianRegularity) : FreeGraphMaximalDomain := by
  intro h P μ w g hh hP hμ hw hg hsol
  obtain ⟨lapB, hlap, hL⟩ := H h P μ w g hh hP hμ hw hg hsol
  obtain ⟨driftB, hG⟩ := inPeriodicGraph_of_laplacian hh hP hw hg hsol hlap hL
  exact ⟨lapB, driftB, hG⟩

/-! ## From the zero-entrance equation to the free equation -/

/-- The zero-entrance equation of the cylinder problem is a free equation whose right side is
the body force, once the stress pairing and the body-force pairing agree at almost every
phase (line 10902). -/
theorem isWeakFreeSolution_of {h σ : ℝ} {U w g : ℝ → SpatialField}
    (hsol : IsWeakModeSolution h σ U w)
    (hg : ∀ᵐ τ, ∀ ψ, IsSimilarityTest ψ → weakCoupling U w ψ τ = forcePairing g ψ τ) :
    IsWeakFreeSolution h σ w g where
  value_integrable := hsol.value_integrable
  temporal_integrable := hsol.temporal_integrable
  dilation_integrable := hsol.dilation_integrable
  diffusion_integrable := hsol.diffusion_integrable
  force_integrable ψ hψ := (hsol.coupling_time_integrable ψ hψ).congr
    (hg.mono fun τ hτ => hτ ψ hψ)
  identity ψ hψ := by
    rw [← integral_congr_ae (hg.mono fun τ hτ => hτ ψ hψ)]
    exact hsol.identity ψ hψ

/-! ## From the graph to the exact mode equation -/

/-- The columns of `U⊗w + w⊗U` are in `L²` where `w(τ)` is, for bounded continuous `U(τ)`. -/
theorem columnsL2_symTensor {U₀ w₀ : SpatialField} (hU : Continuous U₀) {C : ℝ}
    (hC : ∀ x, ‖U₀ x‖ ≤ C) (hw : MemLp w₀ 2 volume) :
    ColumnsL2 (symTensorColumns U₀ w₀) := fun j => by
  rw [symTensorColumns_eq]
  exact memLp_bilin_bdd (symCol j) hU.aestronglyMeasurable hC hw

/-- **The exact mode equation** (`eq:st18-t00633`, line 13738: "The mode solves
`loc:eq:mode`"). If `w` solves the zero-entrance equation in its stress form and lies in the
graph with `Δw = lapB`, `𝒯₀w = driftB`, then `w` solves `loc:eq:mode` with the literal `𝔓`. -/
theorem solvesModeEquation_of {h σ P : ℝ} {U w lapB driftB : ℝ → SpatialField}
    (hsol : IsWeakModeSolution h σ U w) (hG : InPeriodicGraph P w lapB driftB)
    (hU : ∀ τ, Continuous (U τ)) {C : ℝ} (hC : ∀ τ x, ‖U τ x‖ ≤ C)
    (hwL : ∀ᵐ τ, MemLp (w τ) 2 volume) :
    SolvesModeEquation h σ U w lapB driftB := by
  have hcol : ∀ᵐ τ, ColumnsL2 (symTensorColumns (U τ) (w τ)) :=
    hwL.mono fun τ hτ => columnsL2_symTensor (hU τ) (hC τ) hτ
  have hcoup : ∀ ψ : SpaceTime → Space,
      (fun τ => weakCoupling U w ψ τ) =ᵐ[volume] projectedCoupling U w ψ := fun ψ =>
    hcol.mono fun τ hτ => lerayDivIntegral_eq_lerayDivPairing hτ (slice ψ τ)
  refine
    { tensor_memL2 := hcol
      value_integrable := hsol.value_integrable
      laplacian_integrable := fun ψ hψ => (hG.laplacian_weak ψ hψ).right_integrable
      drift_integrable := fun ψ hψ => (hG.drift_weak ψ hψ).right_integrable
      coupling_integrable := fun ψ hψ => (hsol.coupling_time_integrable ψ hψ).congr (hcoup ψ)
      identity := fun ψ hψ => ?_ }
  have hL := hG.laplacian_weak ψ hψ
  have hD := hG.drift_weak ψ hψ
  have hv := hsol.value_integrable ψ hψ
  have hrest : Integrable (fun z => (pairTerm driftB ψ z - driftAdjointTerm w ψ z) -
      h * (pairTerm lapB ψ z - diffusionTerm w ψ z)) :=
    (hD.right_integrable.sub hD.left_integrable).sub
      ((hL.right_integrable.sub hL.left_integrable).const_mul h)
  have hweak : Integrable (weakModeIntegrand h σ w ψ) :=
    ((hv.const_mul (σ - 1 / 2)).add hD.left_integrable).sub
      (hL.left_integrable.const_mul h)
  have i1 : Integrable (fun z => pairTerm driftB ψ z - driftAdjointTerm w ψ z) :=
    hD.right_integrable.sub hD.left_integrable
  have i2 : Integrable (fun z => pairTerm lapB ψ z - diffusionTerm w ψ z) :=
    hL.right_integrable.sub hL.left_integrable
  have e1 : ∫ z, (pairTerm driftB ψ z - driftAdjointTerm w ψ z) = 0 := by
    rw [integral_sub hD.right_integrable hD.left_integrable, hD.eq, sub_self]
  have e2 : ∫ z, (pairTerm lapB ψ z - diffusionTerm w ψ z) = 0 := by
    rw [integral_sub hL.right_integrable hL.left_integrable, hL.eq, sub_self]
  have hzero : ∫ z, ((pairTerm driftB ψ z - driftAdjointTerm w ψ z) -
      h * (pairTerm lapB ψ z - diffusionTerm w ψ z)) = 0 := by
    rw [integral_sub i1 (i2.const_mul h), integral_const_mul, e1, e2]
    simp
  have hlin : ∫ z, linearModeIntegrand h σ w lapB driftB ψ z =
      ∫ z, weakModeIntegrand h σ w ψ z := by
    rw [← add_zero (∫ z, weakModeIntegrand h σ w ψ z), ← hzero, ← integral_add hweak hrest]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [linearModeIntegrand, weakModeIntegrand]
    ring
  rw [hlin, ← integral_congr_ae (hcoup ψ)]
  exact hsol.identity ψ hψ

/-! ## Step C8 -/

/-- **Step C8 from the free maximal-domain statement** (`eq:st18-t00633`, `unlabeled:13702`,
`eq:st18-t00770`; units B0773, B1005, B1006). On a periodic background with bounded `U` and
`∇U`, the lift `𝒩_v b` of a nonzero zero-entrance solution is a graph mode: it lies in the
periodic graph, solves `loc:eq:mode` with the literal `𝔓`, is nonzero and is axisymmetric
without swirl. -/
theorem stepPhysicalMode_of_maximalDomain (H : FreeGraphMaximalDomain) : StepPhysicalMode := by
  intro B R σ b hh hP _ hσ0 _ hU hUper _ hsol hnz
  have hw : IsH1Periodic B.period (cylinderLift R b) := by
    have h := hsol.remainder
    simp only [sub_zero] at h
    exact h
  obtain ⟨C, hC⟩ := hU.bounded
  obtain ⟨g, hg, hgae⟩ := exists_bodyForce hP hU hUper hw
  have hfree : IsWeakFreeSolution B.h σ (cylinderLift R b) g :=
    isWeakFreeSolution_of hsol.equation (hgae.mono fun τ hτ => hτ.2)
  obtain ⟨lapB, driftB, hG⟩ :=
    H B.h B.period σ (cylinderLift R b) g hh hP (by linarith) hw hg hfree
  exact ⟨lapB, driftB,
    { graph := hG
      bstar_nonzero := hnz
      mode_equation := solvesModeEquation_of hsol.equation hG
        (fun τ => (hU.differentiable τ).continuous) (fun τ x => (hC τ x).1)
        (hgae.mono fun τ hτ => hτ.1)
      bstar_symmetric := Eventually.of_forall fun τ => cylinderLift_axisymmetric R b τ }⟩

/-- **Step C8** (`eq:st18-t00633`, `unlabeled:13702`, `eq:st18-t00770`; units B0773, B1005,
B1006), from the `L²` Laplacian estimate of the free equation (B0424, B0426) alone. -/
theorem stepPhysicalMode_of (H : FreeLaplacianRegularity) : StepPhysicalMode :=
  stepPhysicalMode_of_maximalDomain (freeGraphMaximalDomain_of H)

end UnforcedLeray.Cons.C08
