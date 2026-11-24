import UnforcedLeray.Cons.C08PhysicalMode.Slices
import UnforcedLeray.Lib.BochnerTime.Slices
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Blueprint.Construction.Cylinder

/-!
# Step C8, part 4: the free problem; `𝒯₀w` from the equation

`paper/main.tex` lines 7318–7319 (`L₀ = 𝒯₀ - νΔ - ½`), 7429–7437 (the free equation
`(μ + L₀)w = P_σ f` "with Leray projection allowed on the input"), 7533–7536 ("The equation
gives the same type of bound on `T₀w`"), and 10904–10905 (`eq:st18-t00633`, blueprint unit
B0773: the body inverse "places `w` in the original graph with `νΔw, Bw ∈ Y₂`").

* `IsWeakFreeSolution h μ w g`: `(μ + 𝒯₀ - hΔ - ½) w + 𝔓 g = 0` in distributions on
  `ℝ × ℝ³`, every derivative on the test, the right side paired phase by phase
  (`forcePairing`), each pairing convergent.
* `exists_projected_rep`: for `g ∈ 𝒴₂` (real, periodic), the path `τ ↦ 𝔓 g(τ)` has a real
  periodic jointly measurable representative `pg ∈ 𝒴₂` (`L²` slices via `BochnerTime`, a joint
  representative via `Infra.JointMeasurableRep`, then periodization).
* `inPeriodicGraph_of_laplacian` (proved): if a solution of the free equation has
  `Δw ∈ 𝒴₂`, then `𝒯₀w = hΔw - (μ - ½)w - 𝔓g ∈ 𝒴₂` and `w` lies in the periodic graph
  `loc:eq:graph`; the solenoidality of `Δw` and `𝒯₀w` comes from the compiled bridge
  `B0005.inPeriodicGraph_iff`.

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Cons.C08

open UnforcedLeray.Blueprint

/-! ## The free problem with a projected right side -/

/-- `⟨𝔓 g(τ), ψ(τ)⟩_{L²(ℝ³)}`, the phase pairing of a projected right side
("with Leray projection allowed on the input", tex 7376). -/
def forcePairing (g : ℝ → SpatialField) (ψ : SpaceTime → Space) (τ : ℝ) : ℝ :=
  inner ℝ (Leray.projection (toL2 (g τ))) (toL2 (slice ψ τ))

/-- The free equation `(μ + L₀) w + 𝔓 g = 0`, `L₀ = 𝒯₀ - hΔ - ½` (tex 7318–7319, 7429–7437;
`eq:st18-t00633` with the coupling replaced by its body force), in distributions on `ℝ × ℝ³`
with every derivative on the test (`weakModeIntegrand`, `Blueprint/Construction/Cylinder.lean`),
each pairing convergent. -/
structure IsWeakFreeSolution (h μ : ℝ) (w g : ℝ → SpatialField) : Prop where
  value_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm w ψ)
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm w ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm w ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm w ψ)
  force_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (forcePairing g ψ)
  identity : ∀ ψ, IsSimilarityTest ψ →
    (∫ z, weakModeIntegrand h μ w ψ z) + (∫ τ, forcePairing g ψ τ) = 0

/-! ## Pairings of `𝒴₂` fields with similarity tests -/

/-- A periodic slab-`L²` field pairs integrably with every similarity test. -/
theorem integrable_pairTerm_of_isY2 {P : ℝ} (hP : 0 < P) {f : ℝ → SpatialField}
    (hf : B0005.IsY2 P f) {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    Integrable (pairTerm f ψ) := by
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨R, hR0, hT, -⟩ := B0005.exists_window_of_hasCompactSupport hψ.compact
  exact (hf.pairTerm_unfold (B0005.IsSimilarityTest.isPhaseTest hψ) (by linarith) hT).1

/-- A phase slice of a similarity test is in `L²`. -/
theorem memLp_slice_test {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) (τ : ℝ) :
    MemLp (slice ψ τ) 2 volume :=
  (hψ.smooth.comp (contDiff_const.prodMk contDiff_id)).continuous.memLp_of_hasCompactSupport
    (hψ.compact.comp_isClosedEmbedding
      ⟨isEmbedding_prodMkRight τ, (isClosedMap_prodMk_left τ).isClosed_range⟩)

/-! ## A jointly measurable representative of `𝔓 g` -/

/-- **`𝔓 g` has a real periodic representative in `𝒴₂`.** For `g ∈ 𝒴₂` real and periodic,
there is `pg ∈ 𝒴₂` real and periodic with `pg(τ) = 𝔓 g(τ)` in `L²(ℝ³)` at almost every
phase. -/
theorem exists_projected_rep {P : ℝ} (hP : 0 < P) {g : ℝ → SpatialField}
    (hg : B0005.IsY2 P g) :
    ∃ pg : ℝ → SpatialField, B0005.IsY2 P pg ∧
      ∀ᵐ τ, pg τ =ᵐ[volume] (Leray.projection (toL2 (g τ)) : SpatialField) := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) P) with hν
  set F₀ : ℝ × Space → Space := fun z => g z.1 z.2 with hF₀def
  have hF₀ : MemLp F₀ 2 (ν.prod volume) := by
    rw [hν, ← B0005.IsY2.slab_eq]
    exact hg.memL2
  obtain ⟨hpm, hpl⟩ := BochnerTime.stronglyMeasurable_toPath_Lq (q := 2) (ν := ν)
    (μ := (volume : Measure Space)) hF₀
  set u : ℝ → L2Space := fun t => Leray.projection (BochnerTime.toPathLq 2 volume F₀ t)
    with hudef
  have hu : AEStronglyMeasurable u ν := Leray.projection.continuous.comp_aestronglyMeasurable hpm
  have hpath : ∀ t, BochnerTime.toPathLq 2 volume F₀ t = toL2 (g t) := fun t => rfl
  obtain ⟨F', hF'm, hF'⟩ :=
    Infra.JointMeasurableRep.exists_stronglyMeasurable_rep hu.stronglyMeasurable_mk
  -- square integrability of the representative on the slab
  have hF'L : MemLp (fun z : SpaceTime => F' (z.1, z.2)) 2 (volume.restrict (periodSlab P)) := by
    rw [B0005.IsY2.slab_eq]
    refine ⟨hF'm.aestronglyMeasurable, ?_⟩
    have hm : Measurable fun z : ℝ × Space => ‖F' z‖ₑ ^ (2 : ℝ≥0∞).toReal :=
      hF'm.measurable.enorm.pow_const _
    have hlhs : eLpNorm (fun z : SpaceTime => F' (z.1, z.2)) 2 (ν.prod volume) ^
        (2 : ℝ≥0∞).toReal = ∫⁻ t, ∫⁻ x, ‖F' (t, x)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume ∂ν := by
      rw [BochnerTime.eLpNorm_rpow_eq_lintegral two_ne_zero ENNReal.ofNat_ne_top,
        lintegral_prod _ hm.aemeasurable]
    have hslice : ∀ t, ∫⁻ x, ‖F' (t, x)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume =
        ‖hu.mk u t‖ₑ ^ (2 : ℝ≥0∞).toReal := fun t => by
      rw [Lp.enorm_def, BochnerTime.eLpNorm_rpow_eq_lintegral two_ne_zero ENNReal.ofNat_ne_top]
      exact lintegral_congr_ae ((hF' t).mono fun x hx => by dsimp only at hx ⊢; rw [hx])
    have hle : ∫⁻ t, ∫⁻ x, ‖F' (t, x)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume ∂ν ≤
        ∫⁻ t, ‖BochnerTime.toPathLq 2 volume F₀ t‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [hu.ae_eq_mk] with t ht
      rw [hslice t, ← ht]
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Leray.norm_projection_apply_le _)
    have hfin : eLpNorm (fun z : SpaceTime => F' (z.1, z.2)) 2 (ν.prod volume) ^
        (2 : ℝ≥0∞).toReal < ⊤ := by
      rw [hlhs]
      refine lt_of_le_of_lt (hle.trans_eq hpl) ?_
      exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hF₀.eLpNorm_ne_top
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp hfin
  refine ⟨periodize hP (fun t y => F' (t, y)),
    ⟨periodize_periodic _, aestronglyMeasurable_periodize hF'm.aestronglyMeasurable,
      memLp_periodize hF'L⟩, ?_⟩
  refine B0005.ae_of_periodic hP
    (p := fun τ => periodize hP (fun t y => F' (t, y)) τ =ᵐ[volume]
      (Leray.projection (toL2 (g τ)) : SpatialField))
    (fun t => by simp only [periodize_periodic _ t, hg.periodic t]) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hu.ae_eq_mk] with τ hτ hτu
  show periodize hP (fun t y => F' (t, y)) τ =ᵐ[volume] _
  rw [periodize_eq_of_mem _ hτ]
  refine (hF' τ).trans ?_
  rw [← hτu]
  exact EventuallyEq.rfl

/-! ## The drift from the equation -/

/-- The pairing of the projected representative is the phase pairing `forcePairing`. -/
theorem integral_pairTerm_projected {P : ℝ} (hP : 0 < P) {g pg : ℝ → SpatialField}
    (hpg : B0005.IsY2 P pg)
    (hpgae : ∀ᵐ τ, pg τ =ᵐ[volume] (Leray.projection (toL2 (g τ)) : SpatialField))
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    ∫ z, pairTerm pg ψ z = ∫ τ, forcePairing g ψ τ := by
  have hint := integrable_pairTerm_of_isY2 hP hpg hψ
  rw [Measure.volume_eq_prod] at hint
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hpgae] with τ hτ
  rw [forcePairing, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hτ, coeFn_toL2 (memLp_slice_test hψ τ)] with y hy hy'
  rw [pairTerm, ← hy, hy']
  rfl

/-- `∫ (μ + L₀)w ψ` expanded. -/
theorem integral_weakModeIntegrand {h μ : ℝ} {w : ℝ → SpatialField} {ψ : SpaceTime → Space}
    (hv : Integrable (pairTerm w ψ)) (hdA : Integrable (driftAdjointTerm w ψ))
    (hdf : Integrable (diffusionTerm w ψ)) :
    ∫ z, weakModeIntegrand h μ w ψ z = (μ - 1 / 2) * (∫ z, pairTerm w ψ z) +
      (∫ z, driftAdjointTerm w ψ z) - h * (∫ z, diffusionTerm w ψ z) := by
  have e : (fun z => weakModeIntegrand h μ w ψ z) = fun z =>
      ((μ - 1 / 2) * pairTerm w ψ z + driftAdjointTerm w ψ z) - h * diffusionTerm w ψ z := rfl
  have i1 : Integrable (fun z => (μ - 1 / 2) * pairTerm w ψ z + driftAdjointTerm w ψ z) :=
    (hv.const_mul _).add hdA
  rw [e, integral_sub i1 (hdf.const_mul h), integral_add (hv.const_mul _) hdA,
    integral_const_mul, integral_const_mul]

/-- `𝒯₀w = hΔw - (μ - ½)w - 𝔓g`, read off the free equation. -/
def driftOf (h μ : ℝ) (lapB w pg : ℝ → SpatialField) : ℝ → SpatialField :=
  fun τ y => h • lapB τ y - (μ - 1 / 2) • w τ y - pg τ y

theorem isY2_driftOf {P h μ : ℝ} {lapB w pg : ℝ → SpatialField} (hl : B0005.IsY2 P lapB)
    (hw : B0005.IsY2 P w) (hp : B0005.IsY2 P pg) : B0005.IsY2 P (driftOf h μ lapB w pg) := by
  refine ⟨fun τ => ?_, ?_, ?_⟩
  · funext y
    simp only [driftOf, hl.periodic τ, hw.periodic τ, hp.periodic τ]
  · have h1 := ((hl.measurable.const_smul h).sub (hw.measurable.const_smul (μ - 1 / 2))).sub
      hp.measurable
    exact h1
  · have h1 := ((hl.memL2.const_smul h).sub (hw.memL2.const_smul (μ - 1 / 2))).sub hp.memL2
    exact h1

theorem pairTerm_driftOf (h μ : ℝ) (lapB w pg : ℝ → SpatialField) (ψ : SpaceTime → Space) :
    pairTerm (driftOf h μ lapB w pg) ψ = fun z =>
      (h * pairTerm lapB ψ z - (μ - 1 / 2) * pairTerm w ψ z) - pairTerm pg ψ z := by
  funext z
  simp only [pairTerm, driftOf, inner_sub_left, real_inner_smul_left]

/-- The drift identity `⟨𝒯₀w, ψ⟩ = ⟨hΔw - (μ - ½)w - 𝔓g, ψ⟩` from the free equation. -/
theorem driftPairing_driftOf {h P μ : ℝ} (hP : 0 < P) {w g lapB pg : ℝ → SpatialField}
    (hwY : B0005.IsY2 P w) (hsol : IsWeakFreeSolution h μ w g) (hlap : B0005.IsY2 P lapB)
    (hL : ∀ ψ, IsSimilarityTest ψ → laplacianPairing w lapB ψ) (hpg : B0005.IsY2 P pg)
    (hpgae : ∀ᵐ τ, pg τ =ᵐ[volume] (Leray.projection (toL2 (g τ)) : SpatialField))
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    driftPairing w (driftOf h μ lapB w pg) ψ := by
  have hv := hsol.value_integrable ψ hψ
  have hdA : Integrable (driftAdjointTerm w ψ) := by
    show Integrable (fun z => -temporalTerm w ψ z + (3 / 2 : ℝ) * pairTerm w ψ z +
      (1 / 2 : ℝ) * dilationTerm w ψ z)
    exact (((hsol.temporal_integrable ψ hψ).neg).add (hv.const_mul _)).add
      ((hsol.dilation_integrable ψ hψ).const_mul _)
  have hl := integrable_pairTerm_of_isY2 hP hlap hψ
  have hp := integrable_pairTerm_of_isY2 hP hpg hψ
  refine ⟨hdA, integrable_pairTerm_of_isY2 hP (isY2_driftOf hlap hwY hpg) hψ, ?_⟩
  have hI : ∫ z, pairTerm (driftOf h μ lapB w pg) ψ z =
      h * (∫ z, pairTerm lapB ψ z) - (μ - 1 / 2) * (∫ z, pairTerm w ψ z) -
        ∫ z, pairTerm pg ψ z := by
    have i1 : Integrable (fun z => h * pairTerm lapB ψ z - (μ - 1 / 2) * pairTerm w ψ z) :=
      (hl.const_mul h).sub (hv.const_mul _)
    simp only [pairTerm_driftOf]
    rw [integral_sub i1 hp, integral_sub (hl.const_mul h) (hv.const_mul _), integral_const_mul,
      integral_const_mul]
  have hid := hsol.identity ψ hψ
  rw [integral_weakModeIntegrand hv hdA (hsol.diffusion_integrable ψ hψ)] at hid
  rw [hI, integral_pairTerm_projected hP hpg hpgae hψ, ← (hL ψ hψ).eq]
  linarith

/-- **`𝒯₀w ∈ 𝒴₂` from the equation, and the graph** (tex 7533–7536: "The equation gives the
same type of bound on `T₀w`"; 10904–10905). A solution of the free equation in the `H¹` class
with `Δw ∈ 𝒴₂` lies in the periodic graph `loc:eq:graph`, with `𝒯₀w = hΔw - (μ - ½)w - 𝔓g`. -/
theorem inPeriodicGraph_of_laplacian {h P μ : ℝ} (hh : 0 < h) (hP : 0 < P)
    {w g lapB : ℝ → SpatialField} (hw : IsH1Periodic P w) (hg : B0005.IsY2 P g)
    (hsol : IsWeakFreeSolution h μ w g) (hlap : B0005.IsY2 P lapB)
    (hL : ∀ ψ, IsSimilarityTest ψ → laplacianPairing w lapB ψ) :
    ∃ driftB : ℝ → SpatialField, InPeriodicGraph P w lapB driftB := by
  have : Fact (0 < P) := ⟨hP⟩
  obtain ⟨pg, hpg, hpgae⟩ := exists_projected_rep hP hg
  have hwY := hw.value.isY2
  have hd := isY2_driftOf (h := h) (μ := μ) hlap hwY hpg
  have hD : ∀ ψ, IsSimilarityTest ψ → driftPairing w (driftOf h μ lapB w pg) ψ := fun ψ hψ =>
    driftPairing_driftOf hP hwY hsol hlap hL hpg hpgae hψ
  have hdiv : PhaseSpace.IsPhaseSolenoidal (B0005.toY P w) :=
    hwY.isPhaseSolenoidal_of_ae hw.value.solenoidal
  have hV : (B0005.toY P w, (h : ℂ) • B0005.toY P lapB, B0005.toY P (driftOf h μ lapB w pg)) ∈
      B0005.V P 2 h :=
    B0005.mem_V_iff.mpr ⟨hdiv, (B0005.hasHLap_iff hh.ne').mpr
      ((hwY.laplacianPairing_iff hlap).mp hL), (hwY.driftPairing_iff hd).mp hD⟩
  exact ⟨driftOf h μ lapB w pg, (B0005.inPeriodicGraph_iff hh.ne').mpr ⟨hwY, hlap, hd, hV⟩⟩

end UnforcedLeray.Cons.C08
