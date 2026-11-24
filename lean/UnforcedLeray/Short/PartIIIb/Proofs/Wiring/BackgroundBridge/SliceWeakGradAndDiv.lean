import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Sub.PartIIIb_IIIb_D5_bridge_1

/-!
# `PartIII-b:IIIb-D5/bridge/3`: Classical solenoidal slice and Riesz-pressure weak gradient

Source of record: `the November 2 reference manuscript`, lines 2641-2642, 4139-4141.

Proves `ShortBgExactProfileAux.SmoothSolenoidalAndStressGrad`: for a smooth solenoidal `W^{2,4}(ℝ³)`
slice `f` with `f ⊗ f ∈ L²(ℝ³)` and smooth `G =ᵐ 𝐏(f · ∇f) - f · ∇f`,
1. `∑ j : Fin 3, physPd f j y j = 0` pointwise on `Space`;
2. `G` is the distributional gradient of `Cons.C03.Concrete.stressPressureL2 f hT`:
   `∫ y, G y j * φ y = -∫ y, stressPressureL2 f hT y * spatialTestDerivative j φ y`
   for every `j : Fin 3` and `IsSpatialTest φ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring

open UnforcedLeray UnforcedLeray.Blueprint

namespace SliceWeakGradAndDivAux

private theorem contDiff_coord {f : SpatialField} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y : Space => f y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.comp hf

private theorem fderiv_coord_eq_physPd {f : SpatialField} (hf : ContDiff ℝ ∞ f)
    (k i : Fin 3) (y : Space) :
    fderiv ℝ (fun y' : Space => f y' i) y (coordinateVector k) = physPd f k y i :=
  (Cons.C09.fderiv_apply_coord (hf.differentiable (by simp) y) (coordinateVector k) i).symm

private theorem integrable_mul_spatialTest {a φ : Space → ℝ}
    (ha : Continuous a) (hφ : IsSpatialTest φ) :
    Integrable (fun y : Space => a y * φ y) volume :=
  (ha.mul hφ.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left

private theorem ibp_scalar {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) (k : Fin 3)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    (∫ y : Space, a y * spatialTestDerivative k φ y) =
      -∫ y : Space, fderiv ℝ a y (coordinateVector k) * φ y := by
  let v : Space := coordinateVector k
  have hda : Continuous (fun y : Space => fderiv ℝ a y v) :=
    ((ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have i1 : Integrable (fun y : Space =>
      (ContinuousLinearMap.mul ℝ ℝ) (fderiv ℝ a y v) (φ y)) volume :=
    integrable_mul_spatialTest hda hφ
  have i2 : Integrable (fun y : Space =>
      (ContinuousLinearMap.mul ℝ ℝ) (a y) (fderiv ℝ φ y v)) volume :=
    integrable_mul_spatialTest ha.continuous (hφ.derivative k)
  have i3 : Integrable (fun y : Space =>
      (ContinuousLinearMap.mul ℝ ℝ) (a y) (φ y)) volume :=
    integrable_mul_spatialTest ha.continuous hφ
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) i1 i2 i3
    (fun y _ => ha.differentiable (by simp) y)
    (fun y _ => hφ.smooth.differentiable (by simp) y)

private theorem not_pos_of_integral_spatialTest_eq_zero {g : Space → ℝ}
    (hg : Continuous g)
    (hint : ∀ φ : Space → ℝ, IsSpatialTest φ → (∫ y : Space, g y * φ y) = 0)
    {y₀ : Space} (hpos : 0 < g y₀) : False := by
  have hmem : {y : Space | g y₀ / 2 < g y} ∈ 𝓝 y₀ :=
    (isOpen_lt continuous_const hg).mem_nhds (half_lt_self hpos)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  let b : ContDiffBump y₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hb_test : IsSpatialTest (b : Space → ℝ) := ⟨b.contDiff, b.hasCompactSupport⟩
  have hzero : (∫ y : Space, g y * b y) = 0 := hint b hb_test
  have hpt : ∀ y : Space, (g y₀ / 2) * b y ≤ g y * b y := by
    intro y
    by_cases hy : y ∈ Metric.ball y₀ r
    · exact mul_le_mul_of_nonneg_right (le_of_lt (hball hy)) b.nonneg
    · have hdist : b.rOut ≤ dist y y₀ := le_of_not_gt (by simpa [Metric.mem_ball, b] using hy)
      have hb0 : (b : Space → ℝ) y = 0 := b.zero_of_le_dist hdist
      simp [hb0]
  have hle : (g y₀ / 2) * (∫ y : Space, (b : Space → ℝ) y) ≤ ∫ y : Space, g y * b y := by
    rw [← integral_const_mul]
    exact integral_mono (b.integrable.const_mul (g y₀ / 2))
      (integrable_mul_spatialTest hg hb_test) hpt
  have hstrict : 0 < (g y₀ / 2) * (∫ y : Space, (b : Space → ℝ) y) :=
    mul_pos (half_pos hpos) b.integral_pos
  linarith

private theorem eq_zero_of_integral_spatialTest_eq_zero {g : Space → ℝ}
    (hg : Continuous g)
    (hint : ∀ φ : Space → ℝ, IsSpatialTest φ → (∫ y : Space, g y * φ y) = 0)
    (y : Space) : g y = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine not_pos_of_integral_spatialTest_eq_zero (g := fun y' => -g y') hg.neg ?_
      (neg_pos.mpr hlt)
    intro φ hφ
    simp_rw [neg_mul]
    rw [integral_neg, hint φ hφ, neg_zero]
  · exact not_pos_of_integral_spatialTest_eq_zero hg hint hgt

private theorem div_eq_zero_of_smooth_solenoidal {f : SpatialField}
    (hf : ContDiff ℝ ∞ f) (hsol : IsSolenoidal f) (y : Space) :
    ∑ k : Fin 3, physPd f k y k = 0 := by
  have hpd_cont : ∀ k i : Fin 3, Continuous (fun y' : Space => physPd f k y' i) := fun k i => by
    have heq : (fun y' : Space => physPd f k y' i) =
        fun y' : Space => fderiv ℝ (fun z => f z i) y' (coordinateVector k) :=
      funext fun y' => (fderiv_coord_eq_physPd hf k i y').symm
    rw [heq]
    exact (((contDiff_coord hf i).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const).continuous
  have hdiv_cont : Continuous (fun y' : Space => ∑ k : Fin 3, physPd f k y' k) :=
    continuous_finsetSum _ fun k _ => hpd_cont k k
  refine eq_zero_of_integral_spatialTest_eq_zero hdiv_cont (fun φ hφ => ?_) y
  have h0 := hsol.identity φ hφ
  have hintL : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y' : Space => f y' k * spatialTestDerivative k φ y') volume :=
    fun k _ => integrable_mul_spatialTest (contDiff_coord hf k).continuous (hφ.derivative k)
  have hintR : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y' : Space => physPd f k y' k * φ y') volume :=
    fun k _ => integrable_mul_spatialTest (hpd_cont k k) hφ
  rw [integral_finsetSum _ hintL] at h0
  have hstep : ∀ k : Fin 3,
      (∫ y' : Space, f y' k * spatialTestDerivative k φ y') =
        -∫ y' : Space, physPd f k y' k * φ y' := by
    intro k
    rw [ibp_scalar (contDiff_coord hf k) k hφ]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
    dsimp only
    rw [fderiv_coord_eq_physPd hf k k y']
  simp_rw [hstep] at h0
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hintR] at h0
  have h0' : (∫ y' : Space, ∑ k : Fin 3, physPd f k y' k * φ y') = 0 := neg_eq_zero.mp h0
  rw [← h0']
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  dsimp only
  rw [Finset.sum_mul]

private theorem lerayDivPairing_coord_test {f L : SpatialField} {C : ℝ}
    (hf : ContDiff ℝ ∞ f) (hsol : IsSolenoidal f)
    (hf0 : eLpNorm f 4 volume ≤ ENNReal.ofReal C)
    (hf1 : eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C)
    (hf2 : eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C)
    (hLae : L =ᵐ[volume] ⇑(Leray.projection (toL2 (fun y => fderiv ℝ f y (f y)))))
    (j : Fin 3) {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    lerayDivPairing (tensorColumns f f) (fun y => φ y • coordinateVector j) =
      ∫ y : Space, L y j * φ y := by
  let ψ₀ : Space → Space := fun y => φ y • coordinateVector j
  have hψ₀ : IsVectorTest ψ₀ :=
    { smooth := hφ.smooth.smul contDiff_const
      compact := HasCompactSupport.intro hφ.compact.isCompact fun y hy => by
        simp [ψ₀, image_eq_zero_of_notMem_tsupport hy] }
  have hf2_cd : ContDiff ℝ 2 f := hf.of_le (by simp)
  let Pcol := IIb.B3RemH2Sub.stressColH2 f hf2_cd hf0 hf1 hf2
  have hPval : ∀ k : Fin 3, ((Pcol k).value : SpatialField) =ᵐ[volume] tensorColumns f f k :=
    fun k => coeFn_toL2 (IIb.B3RemH2Sub.memLp_stressCol hf2_cd hf0 k).1
  have hMinus := Blueprint.L10.isMinusLerayDiv_minusLerayDivX Pcol (tensorColumns f f) hPval
  have hpair := hMinus.2 ψ₀ hψ₀
  rw [IIb.B3RemH2Sub.Xclass_minusLerayDivX_stressColH2 f hf2_cd hsol hf0 hf1 hf2,
    inner_neg_left] at hpair
  have hpair' : lerayDivPairing (tensorColumns f f) ψ₀ =
      inner ℝ (Leray.projection (toL2 (fun y => fderiv ℝ f y (f y)))) (toL2 ψ₀) :=
    neg_inj.mp hpair.symm
  have hLm2 : MemLp L 2 volume :=
    (Lp.memLp (Leray.projection (toL2 (fun y => fderiv ℝ f y (f y))))).ae_eq hLae.symm
  have htoL2 : toL2 L = Leray.projection (toL2 (fun y => fderiv ℝ f y (f y))) :=
    Blueprint.L10.toL2_of_ae_eq_coeFn hLae.symm
  rw [hpair', ← htoL2, Cons.C09.inner_toL2_toL2 hLm2 (Blueprint.L10.vectorTest_memLp hψ₀ 2)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only [ψ₀]
  rw [real_inner_comm, Cons.C09.inner_smul_coordinateVector, mul_comm]

private def timeBump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

private theorem timeBump0_at_zero : (timeBump0 : ℝ → ℝ) 0 = 1 :=
  timeBump0.one_of_mem_closedBall (Metric.mem_closedBall_self one_pos.le)

private def coordSimTest (j : Fin 3) (φ : Space → ℝ) : SpaceTime → Space :=
  fun z => (timeBump0 z.1 * φ z.2) • coordinateVector j

private theorem isSimilarityTest_coordSimTest (j : Fin 3) {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) : IsSimilarityTest (coordSimTest j φ) where
  smooth := ((timeBump0.contDiff.comp contDiff_fst).mul
    (hφ.smooth.comp contDiff_snd)).smul contDiff_const
  compact := by
    have hb : HasCompactSupport (timeBump0 : ℝ → ℝ) := timeBump0.hasCompactSupport
    refine IsCompact.of_isClosed_subset (hb.isCompact.prod hφ.compact.isCompact)
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro z hz
    refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
    · intro h
      apply hz
      simp [coordSimTest, h]
    · intro h
      apply hz
      simp [coordSimTest, h]

private theorem slice_coordSimTest_zero (j : Fin 3) (φ : Space → ℝ) :
    slice (coordSimTest j φ) 0 = fun y => φ y • coordinateVector j := by
  funext y
  simp [slice, coordSimTest, timeBump0_at_zero]

private theorem spatialDerivative_coordSimTest_zero (j : Fin 3) {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (y v : Space) :
    spatialDerivative (coordSimTest j φ) 0 y v = (fderiv ℝ φ y v) • coordinateVector j := by
  have heq : (fun y' : Space => coordSimTest j φ (0, y')) =
      fun y' : Space => φ y' • coordinateVector j := slice_coordSimTest_zero j φ
  unfold spatialDerivative
  rw [heq, fderiv_smul_const (hφ.smooth.differentiable (by simp) y) (coordinateVector j)]
  rfl

private theorem spatialDivergence_coordSimTest_zero (j : Fin 3) {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (y : Space) :
    spatialDivergence (coordSimTest j φ) 0 y = spatialTestDerivative j φ y := by
  unfold spatialDivergence
  rw [Finset.sum_eq_single j]
  · rw [spatialDerivative_coordSimTest_zero j hφ y (coordinateVector j)]
    simp [coordinateVector, spatialTestDerivative]
  · intro i _ hij
    rw [spatialDerivative_coordSimTest_zero j hφ y (coordinateVector i)]
    simp [coordinateVector, hij]
  · simp

private theorem convectionTerm_coordSimTest_zero {f : SpatialField} (j : Fin 3)
    {φ : Space → ℝ} (hφ : IsSpatialTest φ) (y : Space) :
    convectionTerm (fun _ => f) (coordSimTest j φ) (0, y) =
      ∑ k : Fin 3, (f y k * f y j) * spatialTestDerivative k φ y := by
  unfold convectionTerm
  dsimp only
  rw [spatialDerivative_coordSimTest_zero j hφ y (f y), real_inner_comm,
    Cons.C09.inner_smul_coordinateVector]
  have hf_sum : fderiv ℝ φ y (f y) = ∑ k : Fin 3, f y k * spatialTestDerivative k φ y := by
    conv_lhs => rw [RieszLp.eq_sum_coordinateVector (f y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [hf_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem fderiv_self_coord_eq_sum_physPd (f : SpatialField)
    (j : Fin 3) (y : Space) :
    fderiv ℝ f y (f y) j = ∑ k : Fin 3, f y k * physPd f k y j := by
  have hf_sum : fderiv ℝ f y (f y) = ∑ k : Fin 3, f y k • physPd f k y := by
    conv_lhs => rw [RieszLp.eq_sum_coordinateVector (f y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl
  change (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j) (fderiv ℝ f y (f y)) = _
  rw [hf_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

private theorem integral_convectionTerm_coordSimTest_zero {f : SpatialField}
    (hf : ContDiff ℝ ∞ f) (hdiv : ∀ y : Space, ∑ k : Fin 3, physPd f k y k = 0)
    (j : Fin 3) {φ : Space → ℝ} (hφ : IsSpatialTest φ) :
    (∫ y : Space, convectionTerm (fun _ => f) (coordSimTest j φ) (0, y)) =
      -∫ y : Space, fderiv ℝ f y (f y) j * φ y := by
  have hpt_eq : (fun y : Space => convectionTerm (fun _ => f) (coordSimTest j φ) (0, y)) =
      fun y : Space => ∑ k : Fin 3, (f y k * f y j) * spatialTestDerivative k φ y :=
    funext (convectionTerm_coordSimTest_zero j hφ)
  have hak : ∀ k : Fin 3, ContDiff ℝ ∞ (fun y : Space => f y k * f y j) :=
    fun k => (contDiff_coord hf k).mul (contDiff_coord hf j)
  have hdak : ∀ (k : Fin 3) (y : Space),
      fderiv ℝ (fun y' : Space => f y' k * f y' j) y (coordinateVector k) =
        physPd f k y k * f y j + f y k * physPd f k y j := by
    intro k y
    have hk := ((contDiff_coord hf k).differentiable (by simp) y).hasFDerivAt
    have hj := ((contDiff_coord hf j).differentiable (by simp) y).hasFDerivAt
    have hmul := (hk.mul hj).fderiv
    have happ := congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector k)) hmul
    rw [show ((fun y' : Space => f y' k) * fun y' : Space => f y' j) =
        (fun y' : Space => f y' k * f y' j) from rfl] at happ
    rw [happ]
    simp only [add_apply, smul_apply, smul_eq_mul,
      fderiv_coord_eq_physPd hf k k y, fderiv_coord_eq_physPd hf k j y]
    ring
  have hdak_cont : ∀ k : Fin 3,
      Continuous (fun y : Space =>
        fderiv ℝ (fun y' : Space => f y' k * f y' j) y (coordinateVector k)) :=
    fun k => (((hak k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hintL : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y : Space => (f y k * f y j) * spatialTestDerivative k φ y) volume :=
    fun k _ => integrable_mul_spatialTest (hak k).continuous (hφ.derivative k)
  have hintR : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y : Space =>
        fderiv ℝ (fun y' : Space => f y' k * f y' j) y (coordinateVector k) * φ y) volume :=
    fun k _ => integrable_mul_spatialTest (hdak_cont k) hφ
  rw [hpt_eq, integral_finsetSum _ hintL]
  simp_rw [fun k => ibp_scalar (hak k) k hφ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hintR]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [hdak _ y]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hdiv y, zero_mul, zero_add,
    fderiv_self_coord_eq_sum_physPd f j y]

end SliceWeakGradAndDivAux

/-- **Leaf 3 (`PartIII-b:IIIb-D5/bridge/3`)**: classical divergence-free identity and weak
Riesz-pressure gradient relation for a smooth solenoidal `W^{2,4}(ℝ³)` slice `f` with `f ⊗ f ∈ L²`
and smooth `G =ᵐ 𝐏(f · ∇f) - f · ∇f`. -/
theorem smoothSolenoidalAndStressGrad_proof :
    UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ShortBgExactProfileAux.SmoothSolenoidalAndStressGrad := by
  intro f G C hT hf hG hsol hf0 hf1 hf2 hGae
  have hdiv : ∀ y : Space, ∑ j : Fin 3, physPd f j y j = 0 :=
    SliceWeakGradAndDivAux.div_eq_zero_of_smooth_solenoidal hf hsol
  refine ⟨hdiv, fun j φ hφ => ?_⟩
  let N : SpatialField := fun y => fderiv ℝ f y (f y)
  let L : SpatialField := fun y => G y + N y
  have hN_smooth : ContDiff ℝ ∞ N :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply hf
  have hLae : L =ᵐ[volume] ⇑(Leray.projection (toL2 N)) := by
    filter_upwards [hGae] with y hy
    dsimp only [L, N]
    rw [hy, sub_add_cancel]
  have hpairL : lerayDivPairing (tensorColumns f f) (fun y => φ y • coordinateVector j) =
      ∫ y : Space, L y j * φ y :=
    SliceWeakGradAndDivAux.lerayDivPairing_coord_test hf hsol hf0 hf1 hf2 hLae j hφ
  let Ψ : SpaceTime → Space := SliceWeakGradAndDivAux.coordSimTest j φ
  have hΨ : IsSimilarityTest Ψ := SliceWeakGradAndDivAux.isSimilarityTest_coordSimTest j hφ
  have hproj_eq : projectedConvection (fun _ => f) Ψ 0 = ∫ y : Space, L y j * φ y := by
    rw [projectedConvection, SliceWeakGradAndDivAux.slice_coordSimTest_zero j φ, hpairL]
  have hc09 := Cons.C09.projectedConvection_eq_of_relation
    (U := fun _ => f)
    (p := fun _ => (Cons.C03.Concrete.stressPressureL2 f hT : Space → ℝ))
    (τ := 0) hT (Lp.memLp (Cons.C03.Concrete.stressPressureL2 f hT))
    (fun Φ hΦ => Cons.C03.Concrete.stressPressureL2_c09Relation f hT hΦ) hΨ
  have hpres_eq :
      (∫ y : Space,
        pressureSimilarityTerm (fun _ => (Cons.C03.Concrete.stressPressureL2 f hT : Space → ℝ))
          Ψ (0, y)) =
        ∫ y : Space, Cons.C03.Concrete.stressPressureL2 f hT y * spatialTestDerivative j φ y := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [pressureSimilarityTerm]
    rw [SliceWeakGradAndDivAux.spatialDivergence_coordSimTest_zero j hφ y]
  have hconv_eq : (∫ y : Space, convectionTerm (fun _ => f) Ψ (0, y)) =
      -∫ y : Space, N y j * φ y :=
    SliceWeakGradAndDivAux.integral_convectionTerm_coordSimTest_zero hf hdiv j hφ
  have hintG : Integrable (fun y : Space => G y j * φ y) volume :=
    SliceWeakGradAndDivAux.integrable_mul_spatialTest
      (SliceWeakGradAndDivAux.contDiff_coord hG j).continuous hφ
  have hintN : Integrable (fun y : Space => N y j * φ y) volume :=
    SliceWeakGradAndDivAux.integrable_mul_spatialTest
      (SliceWeakGradAndDivAux.contDiff_coord hN_smooth j).continuous hφ
  have hL_split : (∫ y : Space, L y j * φ y) =
      (∫ y : Space, G y j * φ y) + ∫ y : Space, N y j * φ y := by
    rw [← integral_add hintG hintN]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [L]
    rw [PiLp.add_apply, add_mul]
  rw [hproj_eq, hconv_eq, hpres_eq, hL_split] at hc09
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring
