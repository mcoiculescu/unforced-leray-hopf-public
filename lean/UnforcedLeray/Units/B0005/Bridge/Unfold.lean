import UnforcedLeray.Units.B0005.Bridge.Realize

/-!
# B0005 bridge, part 2: unfolding the phase pairing into the interface's spacetime integrals

Blueprint unit B0005 (tex 136–147) against `Blueprint/Package.lean`. For a real periodic field
`f` (`IsY2 𝒯 f`) and a smooth test `G` of bounded support vanishing outside a phase window
`[A, B]`, the pairing of `toY 𝒯 f` with the periodization `perT 𝒯 G` is the spacetime integral
of the interface (`IsY2.phasePair_perT`):

  `⟪perT G, toY f⟫ = 𝒯⁻¹ ∫_{ℝ × ℝ³} G(z) · f(z) dz`,

with the integrand integrable (`IsY2.integrable_dotL_jointC`). For a real test `χ` this is
`𝒯⁻¹ ∫ Blueprint.pairTerm f χ` (`IsY2.pairTerm_unfold`).

The transposed operators of the phase model agree with the test-function operators of the
interface (`Statement.lean`): `dτ = timeDerivative`, `dy j = spatialDerivative (eⱼ)`,
`lapT = spatialLaplacian`, `radialT = spatialDerivative (y)` (`dτ_eq_timeDerivative`, …), so
`Blueprint.diffusionTerm b χ = pairTerm b (lapT χ)` and
`Blueprint.driftAdjointTerm b χ = pairTerm b (driftT χ)` (`diffusionTerm_eq`,
`driftAdjointTerm_eq`), and complexification commutes with all of them (`lapT_cplxT`,
`driftT_cplxT`).

Status: infrastructure for the B0005 bridge. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Hölder for the bilinear dot product -/

theorem integral_norm_dotL_le (a : Lp CVec3 (conjExp 2) (volume : Measure Space))
    (g : Lp CVec3 2 (volume : Measure Space)) :
    ∫ y, ‖dotL (a y) (g y)‖ ≤ ‖dotL‖ * ‖a‖ * ‖g‖ := by
  have hle := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := conjExp 2) (q := 2) (r := 1)
    (Lp.aestronglyMeasurable a) (Lp.aestronglyMeasurable g) (fun u v => dotL u v) ‖dotL‖₊
    (Eventually.of_forall fun y => dotL.le_opNorm₂ _ _)
  have hfin : (‖dotL‖₊ : ℝ≥0∞) * eLpNorm a (conjExp 2) volume * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top a))
      (Lp.eLpNorm_ne_top g)
  have hmeas : AEStronglyMeasurable (fun y => dotL (a y) (g y)) volume :=
    dotL.aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable a) (Lp.aestronglyMeasurable g)
  rw [integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm]
  calc (eLpNorm (fun y => dotL (a y) (g y)) 1 volume).toReal
      ≤ ((‖dotL‖₊ : ℝ≥0∞) * eLpNorm a (conjExp 2) volume * eLpNorm g 2 volume).toReal :=
        ENNReal.toReal_mono hfin hle
    _ = ‖dotL‖ * ‖a‖ * ‖g‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Lp.norm_def, Lp.norm_def]
        rfl

/-! ### The unfolded pairing -/

section Unfold

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {f : ℝ → SpatialField}

theorem IsY2.integrable_dotL_jointC (hf : IsY2 𝒯 f) {G : ℝ × Space → CVec3}
    (hG0 : IsPhaseTest 0 G) {A B : ℝ} (hG : TimeSupp A B G) :
    Integrable (fun z : ℝ × Space => dotL (G z) (jointC f z)) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => dotL (G z) (jointC f z)) volume :=
    dotL.aestronglyMeasurable_comp₂ hG0.continuous.aestronglyMeasurable
      hf.aestronglyMeasurable_jointC
  rw [Measure.volume_eq_prod ℝ Space] at hmeas ⊢
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [hf.ae_pathOf_eq hT.out] with t ht
    refine (PhaseTrace.integrable_dotL (q := 2) hG0 t (pathOf f t)).congr ?_
    filter_upwards [ht] with y hy
    rw [hy]
  · obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((continuous_sliceL (q := 2) hG0).continuousOn (s := Icc A B))
    have hmeas2 : AEStronglyMeasurable
        (fun t => ∫ y, ‖dotL (G (t, y)) (jointC f (t, y))‖) volume :=
      hmeas.norm.integral_prod_right'
    have hgi : Integrable (Set.indicator (Icc A B)
        fun t : ℝ => ‖dotL‖ * max C 0 * ‖toY 𝒯 f (t : AddCircle 𝒯)‖) := by
      refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
      rcases le_or_gt A B with hAB | hAB
      · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mp
          ((intervalIntegrable_comp_mk (toY 𝒯 f) A B).norm.const_mul _))
      · rw [Icc_eq_empty (not_le.mpr hAB)]
        exact integrableOn_empty
    refine Integrable.mono' hgi hmeas2 ?_
    filter_upwards [hf.ae_pathOf_eq hT.out, hf.toY_ae] with t ht ht'
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    by_cases htAB : t ∈ Icc A B
    · rw [indicator_of_mem htAB]
      calc ∫ y, ‖dotL (G (t, y)) (jointC f (t, y))‖
          = ∫ y, ‖dotL ((sliceL hG0 2 t : Space → CVec3) y) ((pathOf f t : Space → CVec3) y)‖ :=
            integral_congr_ae (by
              filter_upwards [ht, coeFn_sliceL (q := 2) hG0 t] with y h1 h2
              rw [h1, h2])
        _ ≤ ‖dotL‖ * ‖sliceL hG0 2 t‖ * ‖pathOf f t‖ := integral_norm_dotL_le _ _
        _ ≤ ‖dotL‖ * max C 0 * ‖toY 𝒯 f (t : AddCircle 𝒯)‖ := by
            rw [ht']
            gcongr
            exact (hC t htAB).trans (le_max_left _ _)
    · rw [indicator_of_notMem htAB]
      have h0 : ∀ y, G (t, y) = 0 := fun y => hG t y htAB
      simp [h0]

/-- **Unfolding** `⟪perT G, toY f⟫ = 𝒯⁻¹ ∫_{ℝ × ℝ³} G · f`. -/
theorem IsY2.phasePair_perT (hf : IsY2 𝒯 f) {G : ℝ × Space → CVec3}
    (hG0 : IsPhaseTest 0 G) {A B : ℝ} (hAB : A ≤ B) (hG : TimeSupp A B G) :
    phasePair 𝒯 2 (perT 𝒯 G) (toY 𝒯 f) = (𝒯⁻¹ : ℝ) • ∫ z, dotL (G z) (jointC f z) := by
  rw [PhaseTrace.phasePair_perT hG0 hAB hG]
  congr 1
  have hint := hf.integrable_dotL_jointC hG0 hG
  rw [Measure.volume_eq_prod ℝ Space] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_pathOf_eq hT.out, hf.toY_ae] with t ht ht'
  rw [pairH_eq, ht']
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  rw [hy]

end Unfold

/-! ### Complexified real tests -/

/-- The complexification `z ↦ χ(z) + 0i` of a real vector test. -/
def cplxT (χ : ℝ × Space → Space) : ℝ × Space → CVec3 := fun z => cplxL (χ z)

theorem dotL_cplxT_jointC (χ : ℝ × Space → Space) (f : ℝ → SpatialField) (z : ℝ × Space) :
    dotL (cplxT χ z) (jointC f z) = ((Blueprint.pairTerm f χ z : ℝ) : ℂ) := by
  rw [cplxT, jointC, dotL_cplxL]
  rfl

section Real

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {f : ℝ → SpatialField}

/-- **Real form of the unfolding**: for a real smooth test `χ` of bounded support vanishing
outside `[A, B] × ℝ³`, `pairTerm f χ` is integrable on `ℝ × ℝ³` and
`⟪perT (χ + 0i), toY f⟫ = 𝒯⁻¹ ∫ ⟨f, χ⟩`. -/
theorem IsY2.pairTerm_unfold (hf : IsY2 𝒯 f) {χ : ℝ × Space → Space}
    (hχ : IsPhaseTest 0 χ) {A B : ℝ} (hAB : A ≤ B) (hG : TimeSupp A B χ) :
    Integrable (Blueprint.pairTerm f χ) ∧
      phasePair 𝒯 2 (perT 𝒯 (cplxT χ)) (toY 𝒯 f) =
        ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm f χ z : ℝ) : ℂ) := by
  have hc : IsPhaseTest 0 (cplxT χ) := hχ.clm_comp cplxL
  have hcs : TimeSupp A B (cplxT χ) := fun t y ht => by simp [cplxT, hG t y ht]
  have hint := hf.integrable_dotL_jointC hc hcs
  simp_rw [dotL_cplxT_jointC] at hint
  refine ⟨hint.re.congr (Eventually.of_forall fun z => by simp), ?_⟩
  rw [hf.phasePair_perT hc hAB hcs]
  simp_rw [dotL_cplxT_jointC]
  rw [integral_complex_ofReal, Complex.real_smul]
  push_cast
  ring

end Real

/-! ### The operators of the two encodings agree -/

section Ops

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_slice_time {χ : ℝ × Space → F} {t : ℝ} {x : Space}
    (hd : DifferentiableAt ℝ χ (t, x)) :
    fderiv ℝ (fun s => χ (s, x)) t = (fderiv ℝ χ (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ Space) :=
  (hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)).fderiv

theorem fderiv_slice_space {χ : ℝ × Space → F} {t : ℝ} {x : Space}
    (hd : DifferentiableAt ℝ χ (t, x)) :
    fderiv ℝ (fun y => χ (t, y)) x = (fderiv ℝ χ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
  (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem dτ_eq_timeDerivative {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ) (z : ℝ × Space) :
    dτ χ z = timeDerivative χ z.1 z.2 := by
  simp only [dτ, timeDerivative, fderiv_slice_time (hχ z), ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]

theorem dy_eq_spatialDerivative {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ)
    (z : ℝ × Space) (j : Fin 3) :
    dy j χ z = spatialDerivative χ z.1 z.2 (coordinateVector j) := by
  simp only [dy, spatialDerivative, fderiv_slice_space (hχ z), ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

theorem contDiff_dy' {G : ℝ × Space → F} (hG : ContDiff ℝ ∞ G) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j G) :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem lapT_eq_spatialLaplacian {χ : ℝ × Space → Space} (hχ : ContDiff ℝ ∞ χ)
    (z : ℝ × Space) : lapT χ z = spatialLaplacian χ z.1 z.2 := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  simp only [lapT, spatialLaplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y => spatialDerivative χ z.1 y (coordinateVector i)) =
      fun y => dy i χ (z.1, y) := by
    funext y
    exact (dy_eq_spatialDerivative hd (z.1, y) i).symm
  rw [hfun, fderiv_slice_space (((contDiff_dy' hχ i).differentiable (by simp)) _)]
  rfl

theorem radialT_eq_spatialDerivative {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ)
    (z : ℝ × Space) : radialT χ z = spatialDerivative χ z.1 z.2 z.2 := by
  have hx : z.2 = ∑ j : Fin 3, z.2 j • coordinateVector j := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr z.2
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at this
    exact this.symm
  simp only [radialT, dy_eq_spatialDerivative hχ]
  set L := spatialDerivative χ z.1 z.2 with hL
  conv_rhs => rw [hx]
  rw [map_sum]
  simp only [map_smul]

/-- `Blueprint.diffusionTerm b χ = ⟨b, Δχ⟩ = pairTerm b (lapT χ)`. -/
theorem diffusionTerm_eq (b : ℝ → SpatialField) {χ : ℝ × Space → Space}
    (hχ : ContDiff ℝ ∞ χ) : diffusionTerm b χ = Blueprint.pairTerm b (lapT χ) := by
  funext z
  simp only [diffusionTerm, Blueprint.pairTerm, lapT_eq_spatialLaplacian hχ]

/-- `Blueprint.driftAdjointTerm b χ = ⟨b, 𝒯₀ᵗχ⟩ = pairTerm b (driftT χ)`. -/
theorem driftAdjointTerm_eq (b : ℝ → SpatialField) {χ : ℝ × Space → Space}
    (hχ : Differentiable ℝ χ) : Blueprint.driftAdjointTerm b χ = Blueprint.pairTerm b (driftT χ) := by
  funext z
  simp only [Blueprint.driftAdjointTerm, Blueprint.pairTerm, temporalTerm, Blueprint.dilationTerm,
    driftT, dτ_eq_timeDerivative hχ, radialT_eq_spatialDerivative hχ, inner_add_right,
    inner_neg_right, inner_smul_right]
  ring

/-- Complexification commutes with Fréchet derivatives. -/
theorem fderiv_cplxT {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ) (p : ℝ × Space) :
    fderiv ℝ (cplxT χ) p = cplxL.comp (fderiv ℝ χ p) :=
  (cplxL.hasFDerivAt.comp p (hχ p).hasFDerivAt).fderiv

theorem dτ_cplxT {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ) :
    dτ (cplxT χ) = cplxT (dτ χ) := by
  funext p
  simp only [dτ, fderiv_cplxT hχ, ContinuousLinearMap.comp_apply, cplxT]

theorem dy_cplxT {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ) (j : Fin 3) :
    dy j (cplxT χ) = cplxT (dy j χ) := by
  funext p
  simp only [dy, fderiv_cplxT hχ, ContinuousLinearMap.comp_apply, cplxT]

theorem lapT_cplxT {χ : ℝ × Space → Space} (hχ : ContDiff ℝ ∞ χ) :
    lapT (cplxT χ) = cplxT (lapT χ) := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  funext p
  simp only [lapT, dy_cplxT hd, dy_cplxT ((contDiff_dy' hχ _).differentiable (by simp)), cplxT,
    map_sum]

theorem radialT_cplxT {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ) :
    radialT (cplxT χ) = cplxT (radialT χ) := by
  funext p
  simp only [radialT, dy_cplxT hχ, cplxT, map_sum, map_smul]

theorem driftT_cplxT {χ : ℝ × Space → Space} (hχ : Differentiable ℝ χ) :
    driftT (cplxT χ) = cplxT (driftT χ) := by
  funext p
  simp only [driftT, dτ_cplxT hχ, radialT_cplxT hχ, cplxT, map_add, map_neg, map_smul]

/-! ### Phase windows are preserved by the operators -/

theorem timeSupp_fderiv_apply {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G)
    (v : ℝ × Space) : TimeSupp A B (fun p => fderiv ℝ G p v) := by
  intro τ y hτ
  have hev : G =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
    have hopen : IsOpen {p : ℝ × Space | p.1 ∉ Icc A B} :=
      isClosed_Icc.isOpen_compl.preimage continuous_fst
    filter_upwards [hopen.mem_nhds (show ((τ, y) : ℝ × Space) ∈ {p : ℝ × Space | p.1 ∉ Icc A B}
      from hτ)] with p hp
    exact hG p.1 p.2 hp
  simp [hev.fderiv_eq]

theorem timeSupp_dy {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G) (j : Fin 3) :
    TimeSupp A B (dy j G) :=
  timeSupp_fderiv_apply hG _

theorem timeSupp_lapT {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G) :
    TimeSupp A B (lapT G) := by
  intro τ y hτ
  simp only [lapT, timeSupp_dy (timeSupp_dy hG _) _ τ y hτ, Finset.sum_const_zero]

theorem timeSupp_smul_left {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G) (c : ℝ) :
    TimeSupp A B (c • G) := fun τ y hτ => by simp [hG τ y hτ]

end Ops

end UnforcedLeray.B0005
