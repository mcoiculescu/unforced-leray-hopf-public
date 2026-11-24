import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.WeakD.Core
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.WeakD.SliceLoc
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.Approx

/-!
# `convYSliceId`: the slice Laplacian identity survives `y`-mollification

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
For a.e. `τ` the slices `Φ(τ), a(τ)` are locally integrable (`convYW_ae_locInt`).  With `K = η_n`
even, smooth, compactly supported: Fubini + evenness give
`∫ (K * Φ)·Δθ = ∫ Φ·(K * Δθ)` (`slid_fub_vec`), and `K * Δθ = Δ(K * θ)` (`slid_lap_conv`) with
`K * θ` smooth compactly supported, so `SliceLapId` at `K * θ` yields the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution Pointwise

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Integrability of the Fubini integrand. -/
theorem slid_integrable (K : Space → ℝ) (hK : Continuous K) (hKc : HasCompactSupport K)
    (f : Space → ℂ) (hf : LocallyIntegrable f volume) (h : Space → ℂ) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Integrable (fun p : Space × Space => K (p.1 - p.2) • (f p.2 * h p.1)) (volume.prod volume) := by
  obtain ⟨MK, hMK⟩ := hK.bounded_above_of_compact_support hKc
  obtain ⟨Mh, hMh⟩ := hh.bounded_above_of_compact_support hhc
  set S := tsupport h with hS
  have hSc : IsCompact S := hhc
  set T : Set Space := (fun p : Space × Space => p.1 - p.2) '' (S ×ˢ tsupport K) with hT
  have hTc : IsCompact T := (hSc.prod hKc).image (continuous_fst.sub continuous_snd)
  have h1 : Integrable (S.indicator (fun _ : Space => MK * Mh)) volume :=
    (integrable_indicator_iff hSc.measurableSet).2
      (integrableOn_const hSc.measure_lt_top.ne)
  have h2 : Integrable (T.indicator (fun z => ‖f z‖)) volume :=
    (integrable_indicator_iff hTc.measurableSet).2 ((hf.integrableOn_isCompact hTc).norm)
  have h3 := h1.mul_prod h2
  refine h3.mono' ?_ ?_
  · have a1 : AEStronglyMeasurable (fun p : Space × Space => f p.2) (volume.prod volume) :=
      (hf.aestronglyMeasurable).comp_snd
    have a2 : Continuous (fun p : Space × Space => h p.1) := hh.comp continuous_fst
    have a3 : Continuous (fun p : Space × Space => K (p.1 - p.2)) :=
      hK.comp (continuous_fst.sub continuous_snd)
    exact (a3.aestronglyMeasurable.smul (a1.mul a2.aestronglyMeasurable))
  · have hMK0 : 0 ≤ MK := le_trans (norm_nonneg _) (hMK 0)
    have hMh0 : 0 ≤ Mh := le_trans (norm_nonneg _) (hMh 0)
    have hnn : ∀ y z : Space, 0 ≤ S.indicator (fun _ : Space => MK * Mh) y *
        T.indicator (fun z => ‖f z‖) z := fun y z =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => mul_nonneg hMK0 hMh0) _)
        (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
    refine Filter.Eventually.of_forall fun p => ?_
    obtain ⟨y, z⟩ := p
    by_cases hy : y ∈ S
    · by_cases hz : z ∈ T
      · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hz, norm_smul, norm_mul,
          Real.norm_eq_abs]
        have := hMK (y - z)
        have := hMh y
        have e1 : ‖K (y - z)‖ ≤ MK := hMK (y - z)
        have e2 : ‖h y‖ ≤ Mh := hMh y
        have e1' : |K (y - z)| ≤ MK := by simpa using e1
        calc |K (y - z)| * (‖f z‖ * ‖h y‖) ≤ MK * (‖f z‖ * Mh) := by
              gcongr
          _ = MK * Mh * ‖f z‖ := by ring
      · have : K (y - z) = 0 := by
          by_contra hne
          apply hz
          exact ⟨(y, y - z), ⟨hy, subset_tsupport _ hne⟩, by simp⟩
        simpa [this] using hnn y z
    · have : h y = 0 := image_eq_zero_of_notMem_tsupport hy
      simpa [this] using hnn y z

/-- Coordinate projection `ℂ³ → ℂ` as a real continuous linear map. -/
def slidProj (i : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ

theorem slid_locInt_comp (i : Fin 3) {f : Space → CVec3} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun z => f z i) volume := by
  rw [locallyIntegrable_iff] at hf ⊢
  intro C hC
  exact (slidProj i).integrable_comp (hf C hC)

/-- Per-point integrability of the convolution integrand. -/
theorem slid_integrable_left (K : Space → ℝ) (hK : Continuous K) (hKc : HasCompactSupport K)
    {f : Space → CVec3} (hf : LocallyIntegrable f volume) (y : Space) :
    Integrable (fun z => K (y - z) • f z) volume := by
  have hg : Continuous (fun z => K (y - z)) := hK.comp (continuous_const.sub continuous_id)
  have hgc : HasCompactSupport (fun z => K (y - z)) :=
    hKc.comp_isClosedEmbedding (Homeomorph.subLeft y).isClosedEmbedding
  exact hf.integrable_smul_left_of_hasCompactSupport hg hgc

theorem slid_integrable_right (K : Space → ℝ) (hK : Continuous K)
    {h : Space → CVec3} (hh : Continuous h) (hhc : HasCompactSupport h) (z : Space) :
    Integrable (fun y => K (y - z) • h y) volume :=
  by
  have hc : Continuous (fun y => K (y - z) • h y) :=
    (hK.comp (continuous_id.sub continuous_const)).smul hh
  have hs : HasCompactSupport (fun y => K (y - z) • h y) := by
    refine HasCompactSupport.intro hhc fun y hy => ?_
    rw [image_eq_zero_of_notMem_tsupport hy, smul_zero]
  exact hc.integrable_of_hasCompactSupport hs

set_option maxHeartbeats 1600000 in
/-- Fubini with an even kernel, vector version. -/
theorem slid_fub_vec (K : Space → ℝ) (hK : Continuous K) (hKc : HasCompactSupport K)
    {f : Space → CVec3} (hf : LocallyIntegrable f volume) {h : Space → CVec3} (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    ∫ y : Space, ∑ i : Fin 3, (∫ z : Space, K (y - z) • f z) i * h y i
      = ∫ z : Space, ∑ i : Fin 3, f z i * (∫ y : Space, K (y - z) • h y) i := by
  set G : Space → Space → ℂ := fun y z => ∑ i : Fin 3, K (y - z) • (f z i * h y i) with hG
  have hGint : Integrable (Function.uncurry G) (volume.prod volume) := by
    have : Function.uncurry G = fun p : Space × Space =>
        ∑ i : Fin 3, K (p.1 - p.2) • (f p.2 i * h p.1 i) := by
      funext p; simp [hG, Function.uncurry]
    rw [this]
    refine integrable_finsetSum _ fun i _ => ?_
    exact slid_integrable K hK hKc (fun z => f z i) (slid_locInt_comp i hf) (fun y => h y i)
      ((slidProj i).continuous.comp hh) (hhc.comp_left (g := fun v : CVec3 => v i) (by simp))
  have hsw := integral_integral_swap hGint
  have e1 : ∀ y, ∑ i : Fin 3, (∫ z : Space, K (y - z) • f z) i * h y i = ∫ z, G y z := by
    intro y
    have hint := slid_integrable_left K hK hKc hf y
    rw [hG]
    simp only
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hc : (∫ z : Space, K (y - z) • f z) i = ∫ z : Space, K (y - z) • f z i := by
        have := (slidProj i).integral_comp_comm hint
        simpa [slidProj] using this.symm
      rw [hc, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp [smul_mul_assoc]
      ring
    · intro i _
      have := ((slidProj i).integrable_comp (hint)).mul_const (h y i)
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [slidProj, smul_mul_assoc]
      ring
  have e2 : ∀ z, ∑ i : Fin 3, f z i * (∫ y : Space, K (y - z) • h y) i = ∫ y, G y z := by
    intro z
    have hint := slid_integrable_right K hK hh hhc z
    rw [hG]
    simp only
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hc : (∫ y : Space, K (y - z) • h y) i = ∫ y : Space, K (y - z) • h y i := by
        have := (slidProj i).integral_comp_comm hint
        simpa [slidProj] using this.symm
      rw [hc, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [mul_smul_comm]
      ring
    · intro i _
      have := ((slidProj i).integrable_comp (hint)).const_mul (f z i)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp [slidProj, mul_smul_comm]
      ring
  simp_rw [e1, e2]
  exact hsw

/-- The `y`-convolution of a vector field with a scalar kernel. -/
def slidCv (K : Space → ℝ) (θ : Space → CVec3) : Space → CVec3 :=
  fun y => ∫ z : Space, K (y - z) • θ z

theorem slid_cv_eq (K : Space → ℝ) (θ : Space → CVec3) :
    slidCv K θ = convolution K θ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
      volume :=
  funext (convYW_conv_eq K θ)

theorem slid_cv_test (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    ContDiff ℝ ∞ (slidCv K θ) ∧ HasCompactSupport (slidCv K θ) := by
  have hKl : LocallyIntegrable K volume := hK.continuous.locallyIntegrable
  rw [slid_cv_eq]
  exact ⟨hθc.contDiff_convolution_right _ hKl hθ,
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
      hKc hθc⟩

theorem slid_cv_fderiv (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (y e : Space) :
    fderiv ℝ (slidCv K θ) y e = ∫ z : Space, K (y - z) • fderiv ℝ θ z e := by
  have hKl : LocallyIntegrable K volume := hK.continuous.locallyIntegrable
  have hd := hθc.hasFDerivAt_convolution_right
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3))
    hKl (hθ.of_le (by norm_num)) y
  rw [slid_cv_eq, hd.fderiv]
  have hθ' : Continuous (fderiv ℝ θ) := hθ.continuous_fderiv (by simp)
  have hex := (HasCompactSupport.fderiv (𝕜 := ℝ) hθc).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompR Space)
    hKl hθ'
  have hint := (hex y).integrable
  rw [convolution_def, ContinuousLinearMap.integral_apply hint e]
  have h2 := integral_sub_left_eq_self (fun u : Space => K (y - u) • fderiv ℝ θ u e) volume y
  simp only [sub_sub_cancel] at h2
  rw [← h2]
  rfl

theorem slid_D_smooth {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (e : Space) :
    ContDiff ℝ ∞ (fun w => fderiv ℝ θ w e) ∧ HasCompactSupport (fun w => fderiv ℝ θ w e) :=
  ⟨(hθ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, hθc.fderiv_apply (𝕜 := ℝ) e⟩

theorem slid_lap_cv (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (y : Space) :
    lapS (slidCv K θ) y = ∫ z : Space, K (y - z) • lapS θ z := by
  unfold lapS
  have h1 : ∀ j : Fin 3, fderiv ℝ (fun z => fderiv ℝ (slidCv K θ) z
      (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ))
      = ∫ z : Space, K (y - z) • fderiv ℝ (fun w => fderiv ℝ θ w
          (EuclideanSpace.single j (1 : ℝ))) z (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    have e : (fun z => fderiv ℝ (slidCv K θ) z (EuclideanSpace.single j (1 : ℝ)))
        = slidCv K (fun w => fderiv ℝ θ w (EuclideanSpace.single j (1 : ℝ))) := by
      funext z
      exact slid_cv_fderiv K hK hKc hθ hθc z _
    rw [e]
    obtain ⟨a, b⟩ := slid_D_smooth hθ hθc (EuclideanSpace.single j (1 : ℝ))
    exact slid_cv_fderiv K hK hKc a b y _
  simp only [h1, Finset.smul_sum]
  rw [integral_finsetSum]
  intro j _
  obtain ⟨a, b⟩ := slid_D_smooth hθ hθc (EuclideanSpace.single j (1 : ℝ))
  have hc : Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ θ w
        (EuclideanSpace.single j (1 : ℝ))) z (EuclideanSpace.single j (1 : ℝ))) :=
    (a.continuous_fderiv (by simp)).clm_apply continuous_const
  exact slid_integrable_left K hK.continuous hKc hc.locallyIntegrable y

theorem slid_lap_test {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) :
    Continuous (lapS θ) ∧ HasCompactSupport (lapS θ) := by
  have hD := fun j : Fin 3 => slid_D_smooth hθ hθc (EuclideanSpace.single j (1 : ℝ))
  have hc : ∀ j : Fin 3, Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ θ w
      (EuclideanSpace.single j (1 : ℝ))) z (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    ((hD j).1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : ∀ j : Fin 3, HasCompactSupport (fun z => fderiv ℝ (fun w => fderiv ℝ θ w
      (EuclideanSpace.single j (1 : ℝ))) z (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    (hD j).2.fderiv_apply (𝕜 := ℝ) _
  have e : lapS θ = fun z => ∑ j : Fin 3, fderiv ℝ (fun w => fderiv ℝ θ w
      (EuclideanSpace.single j (1 : ℝ))) z (EuclideanSpace.single j (1 : ℝ)) := by
    funext z; simp [lapS]
  rw [e]
  refine ⟨continuous_finsetSum _ fun j _ => hc j, ?_⟩
  simp only [Fin.sum_univ_three]
  exact ((hs 0).add (hs 1)).add (hs 2)

theorem slid_molScale_even {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) (y : Space) :
    molScale η n (-y) = molScale η n y := by
  unfold molScale
  rw [smul_neg, hη.2.2.1]

/-- **`convYSliceId`** (source 1334-1337, 1351-1362, 1470-1480): the slice Laplacian identity
survives `y`-mollification. -/
theorem convYSliceId : ConvYSliceId := by
  intro P ν hP hν η hη n Φ a hΦ ha hid
  have hK := apx_molScale_contDiff hη n
  have hKc := apx_molScale_compact hη n
  have hKe := slid_molScale_even hη n
  set K := molScale η n with hKdef
  have hsym : ∀ z y : Space, K (y - z) = K (z - y) := by
    intro z y
    rw [← hKe (z - y), neg_sub]
  have hI : ∀ (z : Space) (g : Space → CVec3),
      ∫ y : Space, K (y - z) • g y = ∫ y : Space, K (z - y) • g y := by
    intro z g
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hsym z y])
  unfold SliceLapId at hid ⊢
  filter_upwards [hid, convYW_ae_locInt hP hΦ, convYW_ae_locInt hP ha] with τ hτ hfΦ hfa
  intro θ hθ hθc
  obtain ⟨hT, hTc⟩ := slid_cv_test K hK hKc hθ hθc
  have key := hτ (slidCv K θ) hT hTc
  obtain ⟨hLc, hLcc⟩ := slid_lap_test hθ hθc
  have l1 : ∫ y : Space, ∑ i : Fin 3, convYMol K Φ (τ, y) i * lapS θ y i
      = ∫ z : Space, ∑ i : Fin 3, Φ (τ, z) i * lapS (slidCv K θ) z i := by
    have := slid_fub_vec K hK.continuous hKc hfΦ hLc hLcc
    refine this.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
    simp only
    rw [hI z (lapS θ), ← slid_lap_cv K hK hKc hθ hθc z]
  have l2 : ∫ y : Space, ∑ i : Fin 3, convYMol K a (τ, y) i * θ y i
      = ∫ z : Space, ∑ i : Fin 3, a (τ, z) i * slidCv K θ z i := by
    have := slid_fub_vec K hK.continuous hKc hfa hθ.continuous hθc
    refine this.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
    simp only
    rw [hI z θ]
    rfl
  rw [l1, l2]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
