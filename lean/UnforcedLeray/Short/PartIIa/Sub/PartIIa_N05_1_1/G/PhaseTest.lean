import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1_1.G.Defs

/-!
# `Sub/PartII-a_N05_1_1/G/PhaseTest`: Phase test lift, `L²` inner-product transfer, and `mulUnitR`

Connects smooth meridional tests `φ` (`IsMeridTest c φ`) to smooth phase tests
`meridPhaseTest ε P φ` (`IsPhaseTest P`), identifies `U (B0223.liftVec hε hc hP (toH hφ))` with
`testElem P 2 (meridPhaseTest ε P φ)`, links `Yq P 2` inner products to `phasePair`, and defines
the contractive radial multipliers `mulUnitR P j : Yq P 2 →L[ℂ] Yq P 2` (`j : Fin 2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1_1G

/-! ### 1. Age scaling and `HSpace c MeridC` test elements -/

/-- Multiplication of a meridional profile by `s^a`. -/
def ageScaleMerid (a : ℝ) (φ : Profile → MeridC) (p : Profile) : MeridC :=
  (p.1 ^ a) • φ p

theorem isMeridTest_ageScaleMerid {c : ℝ} (a : ℝ) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    IsMeridTest c (ageScaleMerid a φ) where
  smooth := by
    obtain ⟨s0, _s1, _L, hs0, hb⟩ := hφ.band
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : 0 < p.1
    · exact ((Real.contDiffAt_rpow_const_of_ne hp.ne').comp p contDiffAt_fst).smul
        hφ.smooth.contDiffAt
    · refine (contDiffAt_const (c := (0 : MeridC))).congr_of_eventuallyEq ?_
      have hW : IsOpen {q : Profile | q.1 < s0} := isOpen_lt continuous_fst continuous_const
      filter_upwards [hW.mem_nhds (lt_of_le_of_lt (not_lt.1 hp) hs0)] with q hq
      have h0 : φ q = 0 := by
        by_contra hne
        exact absurd (hb q hne).1.1 (not_le.2 hq)
      simp [ageScaleMerid, h0]
  periodic p := by
    show ageScaleMerid a φ _ = ageScaleMerid a φ p
    simp only [ageScaleMerid, hφ.periodic p]
  band := by
    obtain ⟨s0, s1, L, hs0, hb⟩ := hφ.band
    exact ⟨s0, s1, L, hs0, fun p hp => hb p (fun h0 => hp (by simp [ageScaleMerid, h0]))⟩

theorem memLp_meridTest {c : ℝ} {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    MemLp φ 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hφ.band
  set s1' := max s1 s0
  set L' := max L 0
  set A : Set Profile := Icc s0 s1' ×ˢ (Icc 0 (max c 0) ×ˢ Icc (-L') L')
  have hA : IsCompact A := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hμA : measureH c A ≠ (⊤ : ℝ≥0∞) := by
    unfold measureH
    rw [withDensity_apply _ hAm]
    have hle : ∫⁻ p in A, weightH p ∂(cellMeasure c) ≤
        ∫⁻ _p in A, ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) ∂(cellMeasure c) := by
      refine setLIntegral_mono' hAm fun p hp => ?_
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hp.1.1 (by norm_num))
    refine (lt_of_le_of_lt hle ?_).ne
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    unfold cellMeasure
    exact (Measure.restrict_apply_le _ _).trans_lt hA.measure_lt_top
  have hcell : ∀ᵐ p ∂(measureH c), p ∈ cell c := by
    unfold measureH cellMeasure
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cell c))
  refine B0226.memLp_of_continuous_of_ae_vanish hφ.smooth.continuous hA hμA ?_ 2
  filter_upwards [hcell] with p hp hpA
  by_contra hne
  obtain ⟨hs, hη⟩ := hb p hne
  exact hpA ⟨⟨hs.1, hs.2.trans (le_max_left _ _)⟩,
    ⟨hp.2.1.1.le, hp.2.1.2.trans (le_max_left _ _)⟩,
    abs_le.1 (hη.trans (le_max_left _ _))⟩

/-- Element of `HSpace c MeridC` represented by `φ`. -/
def toH {c : ℝ} {φ : Profile → MeridC} (hφ : IsMeridTest c φ) : HSpace c MeridC :=
  (memLp_meridTest hφ).toLp φ

private theorem inner_rsmul_left_merid (r : ℝ) (x y : MeridC) :
    inner ℂ (r • x) y = (r : ℂ) * inner ℂ x y := by simp

private theorem inner_rsmul_right_merid (r : ℝ) (x y : MeridC) :
    inner ℂ x (r • y) = (r : ℂ) * inner ℂ x y := by simp

theorem inner_toH_ageScale {c : ℝ} (hc : 0 < c) (W : HSpace c MeridC) (a : ℝ)
    {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    inner ℂ W (toH (isMeridTest_ageScaleMerid a hφ)) =
      ∫ p, inner ℂ ((p.1 ^ (a - 3 / 2 : ℝ)) • periodize c (W : Profile → MeridC) p) (φ p)
        ∂(cellMeasure c) := by
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun p => inner ℂ ((W : Profile → MeridC) p)
      ((toH (isMeridTest_ageScaleMerid a hφ) : Profile → MeridC) p)) =ᵐ[measureH c]
      fun p => inner ℂ ((W : Profile → MeridC) p) (ageScaleMerid a φ p) := by
    filter_upwards [MemLp.coeFn_toLp (memLp_meridTest (isMeridTest_ageScaleMerid a hφ))] with p hp
    rw [toH, hp]
  rw [integral_congr_ae hae]
  unfold measureH
  rw [integral_withDensity_eq_integral_toReal_smul measurable_weightH
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold cellMeasure
  refine setIntegral_congr_fun (measurableSet_cell c) fun p hp => ?_
  have hp1 : 0 < p.1 := hp.1
  have hw0 : 0 ≤ p.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp1.le _
  rw [periodize_of_mem hc _ hp]
  simp only [weightH, ENNReal.toReal_ofReal hw0, ageScaleMerid, Complex.real_smul,
    inner_rsmul_left_merid, inner_rsmul_right_merid]
  have hr : p.1 ^ (-(3 / 2 : ℝ)) * p.1 ^ a = p.1 ^ (a - 3 / 2 : ℝ) := by
    rw [← Real.rpow_add hp1]
    congr 1
    ring
  have hrc := congrArg (fun x : ℝ => (x : ℂ)) hr
  push_cast at hrc
  rw [← mul_assoc, hrc]

/-! ### 2. Complex conjugation on `CVec3` and `Yq P 2` inner product vs `phasePair` -/

/-- Coordinatewise complex conjugation on `CVec3 = EuclideanSpace ℂ (Fin 3)` as a continuous
`ℝ`-linear map. -/
def conjVecCLM : CVec3 →L[ℝ] CVec3 :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ))

theorem conjVecCLM_apply (v : CVec3) (i : Fin 3) :
    conjVecCLM v i = starRingEnd ℂ (v i) := rfl

/-- Pointwise complex conjugation of a phase test. -/
def conjTest (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun q => conjVecCLM (Φ q)

theorem isPhaseTest_conjTest {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    IsPhaseTest P (conjTest Φ) :=
  hΦ.clm_comp conjVecCLM

theorem dy_conjTest (j : Fin 3) {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    dy j (conjTest Φ) = conjTest (dy j Φ) := by
  funext q
  have hd : DifferentiableAt ℝ Φ q := (hΦ.smooth.differentiable (by simp)) q
  have hc : HasFDerivAt (conjTest Φ) (conjVecCLM.comp (fderiv ℝ Φ q)) q :=
    conjVecCLM.hasFDerivAt.comp q hd.hasFDerivAt
  simp only [dy, conjTest, hc.fderiv, ContinuousLinearMap.comp_apply]

theorem neg_conjTest (Φ : ℝ × Space → CVec3) : -conjTest Φ = conjTest (-Φ) := by
  funext q
  simp [conjTest]

theorem inner_testElem_left {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (f : Yq P 2) :
    inner ℂ (testElem P 2 Φ) f = phasePair P 2 (conjTest Φ) f := by
  have hs := hΦ.isSliceTest 2
  rw [phasePair_eq_periodIntegral (isPhaseTest_conjTest hΦ) f, MeasureTheory.L2.inner_def,
    testElem_of hs]
  have h1 : (fun τ : AddCircle P => inner ℂ
      ((ContinuousMap.toLp (E := Lp CVec3 2 (volume : Measure Space)) 2
        AddCircle.haarAddCircle ℂ (circleSlice hs)) τ) (f τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => inner ℂ (circleSlice hs τ) (f τ) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
      (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)] with τ hτ
    rw [hτ]
  rw [integral_congr_ae h1, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage (T := P) (0 : ℝ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [circleSlice_coe, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
  simp only [sliceMap] at hy ⊢
  rw [hy, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, dotL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [conjTest, conjVecCLM_apply, mul_comm]

theorem inner_testElem_right {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (f : Yq P 2) :
    inner ℂ f (testElem P 2 Φ) = starRingEnd ℂ (phasePair P 2 (conjTest Φ) f) := by
  rw [← inner_conj_symm f (testElem P 2 Φ), inner_testElem_left hΦ f]

/-! ### 3. Contractive radial multipliers `mulUnitR` on `Yq P 2` -/

/-- Normalized horizontal coordinate `y_j / r_y` (`0` on the axis). -/
def unitRScalar (j : Fin 3) (y : Space) : ℝ := y j / radius y

theorem measurable_unitRScalar (j : Fin 3) : Measurable (unitRScalar j) :=
  ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable).div measurable_radius

theorem abs_unitRScalar_le (j : Fin 2) (y : Space) : |unitRScalar j.castSucc y| ≤ 1 := by
  unfold unitRScalar
  by_cases hr : radius y = 0
  · simp [hr]
  · have hr0 : 0 < radius y := lt_of_le_of_ne (by unfold radius; exact Real.sqrt_nonneg _) (Ne.symm hr)
    rw [abs_div, abs_of_pos hr0, div_le_one hr0]
    have hsq : y j.castSucc ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2 := by
      fin_cases j <;> simp <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    calc |y j.castSucc| = Real.sqrt (y j.castSucc ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ radius y := Real.sqrt_le_sqrt hsq

theorem memLp_unitRScalar_smul (j : Fin 2) {f : Space → CVec3} (hf : MemLp f 2 volume) :
    MemLp (fun y => unitRScalar j.castSucc y • f y) 2 volume :=
  hf.of_le_mul (c := 1) ((measurable_unitRScalar j.castSucc).aestronglyMeasurable.smul hf.1)
    (Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_unitRScalar_le j y) (norm_nonneg _))

/-- Spatial multiplication by `y_j / r_y` on `L²(ℝ³; ℂ³)` (`j : Fin 2`). -/
def mulUnitRSpace (j : Fin 2) :
    Lp CVec3 2 (volume : Measure Space) →L[ℂ] Lp CVec3 2 (volume : Measure Space) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_unitRScalar_smul j (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_unitRScalar_smul j (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_unitRScalar_smul j (Lp.memLp f)).coeFn_toLp,
          (memLp_unitRScalar_smul j (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_unitRScalar_smul j (Lp.memLp f)).toLp _)
            ((memLp_unitRScalar_smul j (Lp.memLp g)).toLp _),
          Lp.coeFn_add f g] with y h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [(memLp_unitRScalar_smul j (Lp.memLp (a • f))).coeFn_toLp,
          (memLp_unitRScalar_smul j (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_unitRScalar_smul j (Lp.memLp f)).toLp _),
          Lp.coeFn_smul a f] with y h1 h2 h3 h4
        simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
        exact smul_comm _ _ _ }
    1 fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_unitRScalar_smul j (Lp.memLp f)).coeFn_toLp] with y hy
      simp only [LinearMap.coe_mk, AddHom.coe_mk, hy, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_unitRScalar_le j y) (norm_nonneg _)

/-- Phase-space multiplication by `y_j / r_y` on `Yq P 2` (`j : Fin 2`). -/
def mulUnitR (P : ℝ) [Fact (0 < P)] (j : Fin 2) : Yq P 2 →L[ℂ] Yq P 2 :=
  (mulUnitRSpace j).compLpL 2 (AddCircle.haarAddCircle (T := P))

theorem norm_mulUnitR_le {P : ℝ} [Fact (0 < P)] (j : Fin 2) (g : Yq P 2) :
    ‖mulUnitR P j g‖ ≤ ‖g‖ := by
  have h1 : ‖mulUnitRSpace j‖ ≤ 1 := by
    unfold mulUnitRSpace
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖mulUnitR P j g‖ ≤ ‖mulUnitR P j‖ * ‖g‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖mulUnitRSpace j‖ * ‖g‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compLpL_le _) (norm_nonneg _)
    _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖g‖ := one_mul _

/-- Pointwise multiplication of a phase test by `y_j / r_y`. -/
def unitRTest (j : Fin 3) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun q => unitRScalar j q.2 • Φ q

theorem mulUnitRSpace_coeFn (j : Fin 2) (f : Lp CVec3 2 (volume : Measure Space)) :
    (mulUnitRSpace j f : Space → CVec3) =ᵐ[volume] fun y => unitRScalar j.castSucc y • f y :=
  (memLp_unitRScalar_smul j (Lp.memLp f)).coeFn_toLp

theorem mulUnitR_coeFn {P : ℝ} [Fact (0 < P)] (j : Fin 2) (g : Yq P 2) :
    (mulUnitR P j g : AddCircle P → Lp CVec3 2 (volume : Measure Space)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => mulUnitRSpace j (g τ) :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := AddCircle.haarAddCircle (T := P))
    (mulUnitRSpace j) g

theorem conjTest_unitRTest (j : Fin 3) (Φ : ℝ × Space → CVec3) :
    conjTest (unitRTest j Φ) = unitRTest j (conjTest Φ) := by
  funext q
  simp [conjTest, unitRTest]

theorem phasePair_mulUnitR {P : ℝ} [Fact (0 < P)] (j : Fin 2) (g : Yq P 2)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ)
    (hUΨ : IsPhaseTest P (unitRTest j.castSucc Ψ)) :
    phasePair P 2 Ψ (mulUnitR P j g) = phasePair P 2 (unitRTest j.castSucc Ψ) g := by
  have hP0 : (0 : ℝ) < P := Fact.out
  rw [phasePair_eq_periodIntegral hΨ (mulUnitR P j g), phasePair_eq_periodIntegral hUΨ g]
  congr 1
  have hae_vol : ∀ᵐ τ ∂(volume : Measure (AddCircle P)),
      (mulUnitR P j g) τ = mulUnitRSpace j (g τ) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP0).ne').2
      (mulUnitR_coeFn j g)
  refine integral_congr_ae ?_
  filter_upwards [(AddCircle.measurePreserving_mk (T := P) (0 : ℝ)).quasiMeasurePreserving.ae
    hae_vol] with t ht
  have ht' : (mulUnitR P j g) (t : AddCircle P) = mulUnitRSpace j (g (t : AddCircle P)) := ht
  rw [ht']
  refine integral_congr_ae ?_
  filter_upwards [mulUnitRSpace_coeFn j (g (t : AddCircle P))] with y hy
  rw [hy]
  simp only [unitRTest, dotL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

theorem inner_mulUnitR_testElem {P : ℝ} [Fact (0 < P)] (j : Fin 2) (g : Yq P 2)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (hUΦ : IsPhaseTest P (unitRTest j.castSucc Φ)) :
    inner ℂ (mulUnitR P j g) (testElem P 2 Φ) =
      inner ℂ g (testElem P 2 (unitRTest j.castSucc Φ)) := by
  have hcU : IsPhaseTest P (unitRTest j.castSucc (conjTest Φ)) := by
    rw [← conjTest_unitRTest]
    exact isPhaseTest_conjTest hUΦ
  rw [inner_testElem_right hΦ (mulUnitR P j g), inner_testElem_right hUΦ g,
    conjTest_unitRTest, phasePair_mulUnitR j g (isPhaseTest_conjTest hΦ) hcU]

/-! ### 4. Lifted meridional phase tests `meridPhaseTest` and `lift_toH_eq_testElem` -/

/-- Prefactor `(√P ε^{3/2}) (√(2π) ε)⁻¹`. -/
def liftPrefactor (ε P : ℝ) : ℝ :=
  Real.sqrt P * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹

/-- Smooth phase test obtained by lifting a meridional test `ψ` via `(U ∘ liftVec)`. -/
def meridPhaseTest (ε P : ℝ) (ψ : Profile → MeridC) : ℝ × Space → CVec3 :=
  fun q => (liftPrefactor ε P * liftA (ε • q.2)) • frameC (ε • q.2) (ψ (chart ε (ε • q.2, q.1)))

theorem radius_smul_pos {ε : ℝ} (hε : 0 < ε) (y : Space) :
    radius (ε • y) = ε * radius y := by
  unfold radius
  rw [show (ε • y) 0 ^ 2 + (ε • y) 1 ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) by
    simp only [PiLp.smul_apply, smul_eq_mul]; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]

theorem frameC_smul_pos {ε : ℝ} (hε : 0 < ε) {y : Space} (hy : radius y ≠ 0) (v : MeridC) :
    frameC (ε • y) v = frameC y v := by
  have h1 : unitRC (ε • y) = unitRC y := by
    unfold unitRC
    rw [radius_smul_pos hε]
    simp only [PiLp.smul_apply, smul_eq_mul]
    congr 2 <;> congr 1 <;> field_simp [hε.ne', hy]
  simp only [frameC_apply, h1]

theorem meridPhaseTest_zero_near_axis {c ε : ℝ} (hε : 0 < ε) (P : ℝ) {ψ : Profile → MeridC}
    (hψ : IsMeridTest c ψ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × Space, q.2 0 ^ 2 + q.2 1 ^ 2 < δ →
      meridPhaseTest ε P ψ q = 0 := by
  obtain ⟨s0, s1, _L, hs0, hb⟩ := hψ.band
  set s1' := max s1 s0
  have hs1' : 0 < s1' := lt_of_lt_of_le hs0 (le_max_right _ _)
  refine ⟨(2 * ε ^ 2 * s1')⁻¹, by positivity, fun q hq => ?_⟩
  by_cases hr : radius q.2 = 0
  · have hr' : radius (ε • q.2) = 0 := by rw [radius_smul_pos hε, hr, mul_zero]
    simp [meridPhaseTest, liftA, hr']
  · have hr0 : 0 < radius q.2 :=
      lt_of_le_of_ne (by unfold radius; exact Real.sqrt_nonneg _) (Ne.symm hr)
    have hsq : radius q.2 ^ 2 = q.2 0 ^ 2 + q.2 1 ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hage : s1 < (chart ε (ε • q.2, q.1)).1 := by
      show s1 < ageS (ε • q.2)
      unfold ageS
      rw [radius_smul_pos hε, mul_pow, hsq]
      have hpos : 0 < ε ^ 2 * (q.2 0 ^ 2 + q.2 1 ^ 2) := by
        nlinarith [pow_pos hε 2, pow_pos hr0 2]
      have hlt : ε ^ 2 * (q.2 0 ^ 2 + q.2 1 ^ 2) < (2 * s1')⁻¹ := by
        calc ε ^ 2 * (q.2 0 ^ 2 + q.2 1 ^ 2)
            < ε ^ 2 * (2 * ε ^ 2 * s1')⁻¹ := mul_lt_mul_of_pos_left hq (pow_pos hε 2)
          _ = (2 * s1')⁻¹ := by field_simp [hε.ne', hs1'.ne']
      have hinv : 2 * s1' < (ε ^ 2 * (q.2 0 ^ 2 + q.2 1 ^ 2))⁻¹ := by
        have := inv_strictAnti₀ hpos hlt
        rwa [inv_inv] at this
      have : s1 ≤ s1' := le_max_left _ _
      linarith
    have hψ0 : ψ (chart ε (ε • q.2, q.1)) = 0 := by
      by_contra hne
      exact absurd (hb _ hne).1.2 (not_le.2 hage)
    simp [meridPhaseTest, hψ0]

private theorem contDiffAt_radius_snd {q : ℝ × Space} (hr : radius q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space => radius p.2) q := by
  have hc0 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 0) :=
    ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
  have hc1 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 1) :=
    ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
  have hsum : q.2 0 ^ 2 + q.2 1 ^ 2 ≠ 0 := by
    intro h0
    apply hr
    unfold radius
    rw [h0, Real.sqrt_zero]
  exact ((hc0.pow 2).add (hc1.pow 2)).contDiffAt.sqrt hsum

theorem frameC_coord_zero (x : Space) (v : MeridC) :
    frameC x v 0 = (x 0 / radius x) • v 0 := by
  simp [frameC_apply, unitRC, unitZC, Complex.real_smul, mul_comm]

theorem frameC_coord_one (x : Space) (v : MeridC) :
    frameC x v 1 = (x 1 / radius x) • v 0 := by
  simp [frameC_apply, unitRC, unitZC, Complex.real_smul, mul_comm]

theorem frameC_coord_two (x : Space) (v : MeridC) :
    frameC x v 2 = v 1 := by
  simp [frameC_apply, unitRC, unitZC]

private theorem contDiffAt_meridPhaseTest_offAxis {ε : ℝ} (hε : 0 < ε) (P : ℝ)
    {ψ : Profile → MeridC} (hψ : ContDiff ℝ ∞ ψ) {q : ℝ × Space} (hr : radius q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (meridPhaseTest ε P ψ) q := by
  have hc0 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 0) :=
    ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
  have hc1 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 1) :=
    ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
  have hc2 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 2) :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
  have hrad : ContDiffAt ℝ ∞ (fun p : ℝ × Space => radius p.2) q := contDiffAt_radius_snd hr
  have hεr : ContDiffAt ℝ ∞ (fun p : ℝ × Space => ε * radius p.2) q :=
    contDiffAt_const.mul hrad
  have hεrne : ε * radius q.2 ≠ 0 := mul_ne_zero hε.ne' hr
  have hs : ContDiffAt ℝ ∞ (fun p : ℝ × Space => ageS (ε • p.2)) q := by
    have hfun : (fun p : ℝ × Space => ageS (ε • p.2)) = fun p => ((ε * radius p.2) ^ 2)⁻¹ := by
      funext p; simp [ageS, radius_smul_pos hε]
    rw [hfun]
    exact (hεr.pow 2).inv (pow_ne_zero 2 hεrne)
  have hQ : ContDiffAt ℝ ∞ (fun p : ℝ × Space => cellQ ε (ε • p.2) p.1) q := by
    have hfun : (fun p : ℝ × Space => cellQ ε (ε • p.2) p.1) =
        fun p => ε⁻¹ * Real.log (ε * radius p.2) + p.1 / (2 * ε) := by
      funext p; simp [cellQ, radius_smul_pos hε]
    rw [hfun]
    exact (contDiffAt_const.mul (hεr.log hεrne)).add (contDiffAt_fst.div_const _)
  have hη : ContDiffAt ℝ ∞ (fun p : ℝ × Space => etaCoord ε (ε • p.2)) q := by
    have hfun : (fun p : ℝ × Space => etaCoord ε (ε • p.2)) =
        fun p => (ε * p.2 2) / (ε * (ε * radius p.2)) := by
      funext p; simp [etaCoord, radius_smul_pos hε, PiLp.smul_apply, smul_eq_mul]
    rw [hfun]
    exact (contDiffAt_const.mul hc2.contDiffAt).div
      (contDiffAt_const.mul hεr) (mul_ne_zero hε.ne' hεrne)
  have hchart : ContDiffAt ℝ ∞ (fun p : ℝ × Space => chart ε (ε • p.2, p.1)) q :=
    hs.prodMk (hQ.prodMk hη)
  have hψc : ContDiffAt ℝ ∞ (fun p : ℝ × Space => ψ (chart ε (ε • p.2, p.1))) q :=
    hψ.contDiffAt.comp q hchart
  have hψ0 : ContDiffAt ℝ ∞ (fun p : ℝ × Space => ψ (chart ε (ε • p.2, p.1)) 0) q :=
    ((EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.contDiffAt.comp
      q hψc
  have hψ1 : ContDiffAt ℝ ∞ (fun p : ℝ × Space => ψ (chart ε (ε • p.2, p.1)) 1) q :=
    ((EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.contDiffAt.comp
      q hψc
  have hpref : ContDiffAt ℝ ∞ (fun p : ℝ × Space => liftPrefactor ε P * (ε * radius p.2)⁻¹) q :=
    contDiffAt_const.mul (hεr.inv hεrne)
  refine contDiffAt_piLp' 2 fun i => ?_
  match i with
  | ⟨0, _⟩ =>
    change ContDiffAt ℝ ∞ (fun p : ℝ × Space => meridPhaseTest ε P ψ p 0) q
    have hfun : (fun p : ℝ × Space => meridPhaseTest ε P ψ p 0) = fun p =>
        (liftPrefactor ε P * (ε * radius p.2)⁻¹ * ((ε * p.2 0) / (ε * radius p.2))) •
          ψ (chart ε (ε • p.2, p.1)) 0 := by
      funext p
      simp only [meridPhaseTest, liftA, radius_smul_pos hε, frameC_coord_zero, PiLp.smul_apply,
        smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    rw [hfun]
    exact (hpref.mul (((contDiffAt_const (c := ε)).mul hc0.contDiffAt).div hεr hεrne)).smul hψ0
  | ⟨1, _⟩ =>
    change ContDiffAt ℝ ∞ (fun p : ℝ × Space => meridPhaseTest ε P ψ p 1) q
    have hfun : (fun p : ℝ × Space => meridPhaseTest ε P ψ p 1) = fun p =>
        (liftPrefactor ε P * (ε * radius p.2)⁻¹ * ((ε * p.2 1) / (ε * radius p.2))) •
          ψ (chart ε (ε • p.2, p.1)) 0 := by
      funext p
      simp only [meridPhaseTest, liftA, radius_smul_pos hε, frameC_coord_one, PiLp.smul_apply,
        smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    rw [hfun]
    exact (hpref.mul (((contDiffAt_const (c := ε)).mul hc1.contDiffAt).div hεr hεrne)).smul hψ0
  | ⟨2, _⟩ =>
    change ContDiffAt ℝ ∞ (fun p : ℝ × Space => meridPhaseTest ε P ψ p 2) q
    have hfun : (fun p : ℝ × Space => meridPhaseTest ε P ψ p 2) = fun p =>
        (liftPrefactor ε P * (ε * radius p.2)⁻¹) • ψ (chart ε (ε • p.2, p.1)) 1 := by
      funext p
      simp only [meridPhaseTest, liftA, radius_smul_pos hε, frameC_coord_two, PiLp.smul_apply]
    rw [hfun]
    exact hpref.smul hψ1

theorem isPhaseTest_meridPhaseTest {c ε P : ℝ} (hε : 0 < ε) (hP : P = 2 * ε * c)
    {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    IsPhaseTest P (meridPhaseTest ε P ψ) where
  smooth := by
    obtain ⟨δ, hδ, hzero⟩ := meridPhaseTest_zero_near_axis hε P hψ
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hr : radius q.2 = 0
    · refine (contDiffAt_const (c := (0 : CVec3))).congr_of_eventuallyEq ?_
      have hc0 : Continuous (fun p : ℝ × Space => p.2 0 ^ 2 + p.2 1 ^ 2) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_snd).pow 2).add
          (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_snd).pow 2)
      have hopen : IsOpen {p : ℝ × Space | p.2 0 ^ 2 + p.2 1 ^ 2 < δ} :=
        isOpen_lt hc0 continuous_const
      have hmem : q.2 0 ^ 2 + q.2 1 ^ 2 < δ := by
        have hsq : q.2 0 ^ 2 + q.2 1 ^ 2 = radius q.2 ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
        rw [hsq, hr, sq, zero_mul]
        exact hδ
      filter_upwards [hopen.mem_nhds hmem] with p hp
      exact hzero p hp
    · exact contDiffAt_meridPhaseTest_offAxis hε P hψ.smooth hr
  periodic τ y := by
    have hq : cellQ ε (ε • y) (τ + P) = cellQ ε (ε • y) τ + c := by
      unfold cellQ
      rw [hP]
      field_simp [hε.ne']
      ring
    have hch : chart ε (ε • y, τ + P) =
        ((chart ε (ε • y, τ)).1, (chart ε (ε • y, τ)).2.1 + c, (chart ε (ε • y, τ)).2.2) := by
      simp [chart, hq]
    simp only [meridPhaseTest, hch, hψ.periodic (chart ε (ε • y, τ))]
  bounded_support := by
    obtain ⟨s0, _s1, L, hs0, hb⟩ := hψ.band
    have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
    set R := (ε * Real.sqrt s0)⁻¹ + |L| * (Real.sqrt s0)⁻¹ + 1
    refine ⟨R, fun τ y hy => ?_⟩
    by_contra hne
    have hr : radius y ≠ 0 := by
      intro h0
      apply hne
      have hr' : radius (ε • y) = 0 := by rw [radius_smul_pos hε, h0, mul_zero]
      simp [meridPhaseTest, liftA, hr']
    have hr0 : 0 < radius y :=
      lt_of_le_of_ne (by unfold radius; exact Real.sqrt_nonneg _) (Ne.symm hr)
    have hψne : ψ (chart ε (ε • y, τ)) ≠ 0 := by
      intro h0
      exact hne (by simp [meridPhaseTest, h0])
    obtain ⟨⟨hs_lo, _⟩, hη_le⟩ := hb _ hψne
    have hεr_le : ε * radius y ≤ (Real.sqrt s0)⁻¹ := by
      have h1 : s0 ≤ ((ε * radius y) ^ 2)⁻¹ := by
        simpa [chart, ageS, radius_smul_pos hε] using hs_lo
      have h2 : (ε * radius y) ^ 2 ≤ s0⁻¹ := by
        have := inv_anti₀ hs0 h1
        rwa [inv_inv] at this
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_inv] at h3
    have hr_le : radius y ≤ (ε * Real.sqrt s0)⁻¹ := by
      rw [mul_inv, mul_comm ε⁻¹]
      have := mul_le_mul_of_nonneg_right hεr_le (inv_nonneg.2 hε.le)
      rwa [mul_comm ε, mul_inv_cancel_right₀ hε.ne'] at this
    have hy2_le : |y 2| ≤ |L| * (Real.sqrt s0)⁻¹ := by
      have h1 : |y 2 / (ε * radius y)| ≤ L := by
        have heq : etaCoord ε (ε • y) = y 2 / (ε * radius y) := by
          unfold etaCoord
          rw [radius_smul_pos hε]
          simp only [PiLp.smul_apply, smul_eq_mul]
          field_simp [hε.ne', hr]
        simpa [chart, heq] using hη_le
      have hL0 : 0 ≤ L := (abs_nonneg _).trans h1
      rw [abs_of_nonneg hL0]
      rw [abs_div, abs_of_pos (mul_pos hε hr0), div_le_iff₀ (mul_pos hε hr0)] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hεr_le hL0)
    have hnorm_le : ‖y‖ ≤ radius y + |y 2| := by
      have hsq : ‖y‖ ^ 2 ≤ (radius y + |y 2|) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
        simp only [Real.norm_eq_abs, sq_abs]
        have hr2 : radius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
        have hnn : 0 ≤ radius y * |y 2| := mul_nonneg hr0.le (abs_nonneg _)
        nlinarith [sq_abs (y 2)]
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    linarith

theorem isPhaseTest_unitRTest_meridPhaseTest {c ε P : ℝ} (hε : 0 < ε)
    (hP : P = 2 * ε * c) (j : Fin 3) {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    IsPhaseTest P (unitRTest j (meridPhaseTest ε P ψ)) := by
  have hΦ := isPhaseTest_meridPhaseTest hε hP hψ
  refine ⟨?_, fun τ y => by simp [unitRTest, hΦ.periodic τ y], ?_⟩
  · obtain ⟨δ, hδ, hzero⟩ := meridPhaseTest_zero_near_axis hε P hψ
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hr : radius q.2 = 0
    · refine (contDiffAt_const (c := (0 : CVec3))).congr_of_eventuallyEq ?_
      have hc0 : Continuous (fun p : ℝ × Space => p.2 0 ^ 2 + p.2 1 ^ 2) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_snd).pow 2).add
          (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_snd).pow 2)
      have hopen : IsOpen {p : ℝ × Space | p.2 0 ^ 2 + p.2 1 ^ 2 < δ} :=
        isOpen_lt hc0 continuous_const
      have hmem : q.2 0 ^ 2 + q.2 1 ^ 2 < δ := by
        have hsq : q.2 0 ^ 2 + q.2 1 ^ 2 = radius q.2 ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
        rw [hsq, hr, sq, zero_mul]
        exact hδ
      filter_upwards [hopen.mem_nhds hmem] with p hp
      simp [unitRTest, hzero p hp]
    · have hcj : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 j) :=
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff).comp contDiff_snd
      have hu : ContDiffAt ℝ ∞ (fun p : ℝ × Space => unitRScalar j p.2) q :=
        hcj.contDiffAt.div (contDiffAt_radius_snd hr) hr
      exact hu.smul hΦ.smooth.contDiffAt
  · obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, fun τ y hy => by simp [unitRTest, hR τ y hy]⟩

/-- Identification of `(U ∘ liftVec) (toH hψ)` with `testElem P 2 (meridPhaseTest ε P ψ)`. -/
theorem lift_toH_eq_testElem {c ε P : ℝ} [Fact (0 < P)] (hc : 0 < c) (hε : 0 < ε)
    (hP : P = 2 * ε * c) (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (hU : N01.IsPhaseLift ε P U)
    {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    U (B0223.liftVec hε hc hP (toH hψ)) = testElem P 2 (meridPhaseTest ε P ψ) := by
  have hP0 : (0 : ℝ) < P := Fact.out
  have hΦ := (isPhaseTest_meridPhaseTest hε hP hψ).isSliceTest 2
  set F := B0223.liftVec hε hc hP (toH hψ)
  let rep : AddCircle P → ℝ := fun θ =>
    ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ)
  have hrep : ∀ θ, ((rep θ : ℝ) : AddCircle P) = θ := fun θ => AddCircle.coe_equivIoc
  have hF : ∀ᵐ z ∂(volume : Measure (B0223.PSpace P)),
      (F : B0223.PSpace P → SpaceC) z =
        ((Real.sqrt (2 * Real.pi) * ε)⁻¹ * liftA z.1) •
          frameC z.1 (ψ (chart ε (z.1, rep z.2))) := by
    filter_upwards [(B0223.liftVecWC hε hc hP).coeFn_toLI_toLp (memLp_meridTest hψ)] with z hz
    change (B0223.wcToLIC (B0223.liftVecWC hε hc hP) _ (toH hψ) : B0223.PSpace P → SpaceC) z = _
    rw [B0223.wcToLIC_apply, toH, hz]
    simp only [WeightedComp.compFun, B0223.liftVecWC, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, jConst, cellChart, toCell]
    rw [periodic_reduceIoc_eq ψ hψ.periodic]
    rfl
  have hdil : Measure.QuasiMeasurePreserving
      (fun z : B0223.PSpace P => (ε • z.1, z.2)) volume volume := by
    refine ⟨((measurable_const_smul ε).comp measurable_fst).prodMk measurable_snd, ?_⟩
    rw [B0223.map_dil hε]
    exact Measure.smul_absolutelyContinuous
  have hF2 : ∀ᵐ z ∂(volume : Measure (B0223.PSpace P)),
      (F : B0223.PSpace P → SpaceC) (ε • z.1, z.2) =
        ((Real.sqrt (2 * Real.pi) * ε)⁻¹ * liftA (ε • z.1)) •
          frameC (ε • z.1) (ψ (chart ε (ε • z.1, rep z.2))) := hdil.ae hF
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × Space → B0223.PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure Space))
      (volume : Measure (B0223.PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hall0 : ∀ᵐ θ ∂(volume : Measure (AddCircle P)), ∀ᵐ y ∂(volume : Measure Space),
      (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
        ((Real.sqrt (2 * Real.pi) * ε)⁻¹ * liftA (ε • y)) •
          frameC (ε • y) (ψ (chart ε (ε • y, rep θ))) :=
    Measure.ae_ae_of_ae_prod (hsw.quasiMeasurePreserving.ae hF2)
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)), ∀ᵐ y ∂(volume : Measure Space),
      (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
        ((Real.sqrt (2 * Real.pi) * ε)⁻¹ * liftA (ε • y)) •
          frameC (ε • y) (ψ (chart ε (ε • y, rep θ))) := by
    have h' : ∀ᵐ θ ∂(ENNReal.ofReal P • (AddCircle.haarAddCircle (T := P))),
        ∀ᵐ y ∂(volume : Measure Space),
        (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
          ((Real.sqrt (2 * Real.pi) * ε)⁻¹ * liftA (ε • y)) •
            frameC (ε • y) (ψ (chart ε (ε • y, rep θ))) := by
      rw [← AddCircle.volume_eq_smul_haarAddCircle]
      exact hall0
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hP0).ne').1 h'
  have hT : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((testElem P 2 (meridPhaseTest ε P ψ) : Yq P 2) θ : Space → CVec3) =ᵐ[volume]
        fun y => meridPhaseTest ε P ψ (rep θ, y) := by
    rw [testElem_of hΦ]
    filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 2 (volume : Measure Space))
      (p := 2) (μ := AddCircle.haarAddCircle (T := P)) (𝕜 := ℂ) (circleSlice hΦ)] with θ hθ
    rw [hθ]
    conv_lhs => rw [← hrep θ]
    rw [show (circleSlice hΦ) ((rep θ : ℝ) : AddCircle P) = sliceMap hΦ.2 (rep θ) from
      circleSlice_coe hΦ (rep θ)]
    exact MemLp.coeFn_toLp _
  apply Lp.ext
  filter_upwards [hU F, hall, hT] with θ h1 h2 h3
  apply Lp.ext
  filter_upwards [h1, h2, h3] with y e1 e2 e3
  rw [e1, e2, e3]
  ext i
  simp only [meridPhaseTest, liftPrefactor, PiLp.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

end N05_1_1G

end UnforcedLeray.Short.PartIIa
