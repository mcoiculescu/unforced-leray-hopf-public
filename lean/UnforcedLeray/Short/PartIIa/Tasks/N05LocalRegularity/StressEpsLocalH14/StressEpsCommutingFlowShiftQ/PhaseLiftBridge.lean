import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_3_1
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ.SliceGrad

/-!
# Phase-lift measure and difference bridges (`measureH c` ↔ `phaseVol P`)

Connects `B0220.measureH c` profile shift integrals of `b = periodize c W` to `phaseVol P`
difference integrals of `V₀ = ⇑(prodLpEquiv.symm (U (B0223.liftVec hε hc hP W)))`:
1. `lintegral_profileBox_shiftQ_sub_sq_eq`: `shiftQ h` ↔ phase translation `τ ↦ τ + 2εh`.
2. `lintegral_profileBox_shiftEta_sub_sq_eq`: `shiftEta h` ↔ vertical shear `shearZ (h * ε)`.
3. `lintegral_measureH_exp_age_sub_sq_eq`: `e^{-t/4} b(e^t s, q, η) - b(s, q, η)` ↔
   `‖FreeStress.phaseDilation P t v - v‖ₑ ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N05FlowAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0428
open UnforcedLeray.FreeStress UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223
open MeasureTheory.Measure (QuasiMeasurePreserving)

/-! ### 1. Chart map, density factor, and profile/spatial boxes -/

/-- Pullback of `cellChart ε c` to `(ℝ/Pℤ) × ℝ³` via `(τ, y) ↦ (ε • y, τ)`. -/
def phaseChartMap (ε c P : ℝ) [Fact (0 < P)] (z : AddCircle P × Space) : Profile :=
  cellChart ε c (toCell P (ε • z.2, z.1))

theorem measurable_phaseChartMap (ε c P : ℝ) [Fact (0 < P)] :
    Measurable (phaseChartMap ε c P) :=
  (measurable_cellChart ε c).comp
    (measurable_toCell.comp ((measurable_snd.const_smul ε).prodMk measurable_fst))

/-- Pointwise radial scalar factor of `U (liftVec W)` on `(ℝ/Pℤ) × ℝ³`. -/
def phaseLiftRho (ε P : ℝ) (y : Space) : ℝ :=
  Real.sqrt P * ε ^ (3 / 2 : ℝ) * (jConst ε * liftA (ε • y))

theorem phaseLiftRho_nonneg {ε : ℝ} (hε : 0 < ε) (P : ℝ) (y : Space) :
    0 ≤ phaseLiftRho ε P y := by
  unfold phaseLiftRho
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg P) (Real.rpow_nonneg hε.le _))
    (mul_nonneg (jConst_nonneg hε) (liftA_nonneg _))

theorem measurable_phaseLiftRho (ε P : ℝ) : Measurable (phaseLiftRho ε P) := by
  unfold phaseLiftRho
  exact ((measurable_liftA.comp (measurable_const_smul ε)).const_mul _).const_mul _

/-- Compact age-transverse box `[s₀, s₁] × ℝ × [-L, L]` in `Profile`. -/
def profileBox (s₀ s₁ L : ℝ) : Set Profile :=
  {p : Profile | s₀ ≤ p.1 ∧ p.1 ≤ s₁ ∧ |p.2.2| ≤ L}

theorem measurableSet_profileBox (s₀ s₁ L : ℝ) : MeasurableSet (profileBox s₀ s₁ L) := by
  have h1 : MeasurableSet {p : Profile | s₀ ≤ p.1} :=
    measurableSet_Ici.preimage measurable_fst
  have h2 : MeasurableSet {p : Profile | p.1 ≤ s₁} :=
    measurableSet_Iic.preimage measurable_fst
  have h3 : MeasurableSet {p : Profile | |p.2.2| ≤ L} :=
    measurableSet_Iic.preimage (continuous_abs.measurable.comp (measurable_snd.comp measurable_snd))
  exact h1.inter (h2.inter h3)

/-- Spatial preimage of `profileBox s₀ s₁ L` under `y ↦ ε • y`. -/
def spaceBox (ε s₀ s₁ L : ℝ) : Set Space :=
  {y : Space | s₀ ≤ ageS (ε • y) ∧ ageS (ε • y) ≤ s₁ ∧ |etaCoord ε (ε • y)| ≤ L}

theorem measurableSet_spaceBox (ε s₀ s₁ L : ℝ) : MeasurableSet (spaceBox ε s₀ s₁ L) := by
  have hage : Measurable fun y : Space => ageS (ε • y) :=
    measurable_ageS.comp (measurable_const_smul ε)
  have heta : Measurable fun y : Space => |etaCoord ε (ε • y)| :=
    continuous_abs.measurable.comp ((measurable_etaCoord ε).comp (measurable_const_smul ε))
  exact (measurableSet_Ici.preimage hage).inter
    ((measurableSet_Iic.preimage hage).inter (measurableSet_Iic.preimage heta))

theorem preimage_phaseChartMap_profileBox (ε c P : ℝ) [Fact (0 < P)] (s₀ s₁ L : ℝ) :
    phaseChartMap ε c P ⁻¹' profileBox s₀ s₁ L = univ ×ˢ spaceBox ε s₀ s₁ L := by
  ext z
  simp [phaseChartMap, cellChart, toCell, profileBox, spaceBox]

/-- Isometry norm identity `‖U (liftVec W)‖ = ‖W‖`. -/
theorem norm_phaseLift_liftVec {ε c P : ℝ} [Fact (0 < P)] (hε : 0 < ε) (hc : 0 < c)
    (hP : P = 2 * ε * c) (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (W : HSpace c MeridC) :
    ‖U (B0223.liftVec hε hc hP W)‖ = ‖W‖ := by
  rw [U.norm_map, (B0223.liftVec hε hc hP).norm_map]

theorem measurable_periodize_any {E : Type*} [MeasurableSpace E] (c : ℝ) {b : Profile → E}
    (hb : Measurable b) : Measurable (periodize c b) :=
  hb.comp (measurable_fst.prodMk
    (((measurable_reduceIoc c).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

theorem measurePreserving_phaseAdd {P : ℝ} [Fact (0 < P)] (θ : AddCircle P) :
    MeasurePreserving (fun z : AddCircle P × Space => (z.1 + θ, z.2))
      (phaseVol P) (phaseVol P) :=
  MeasurePreserving.prod
    ⟨measurable_add_const θ, Measure.IsAddRightInvariant.map_add_right_eq_self θ⟩
    (MeasurePreserving.id (volume : Measure Space))

/-! ### 2. Elementary scaling and geometric bounds on `spaceBox` -/

theorem radius_smul_pos {α : ℝ} (hα : 0 < α) (y : Space) :
    radius (α • y) = α * radius y := by
  unfold radius
  rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
  calc √((α * y 0) ^ 2 + (α * y 1) ^ 2)
      = √(α ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) := by congr 1; ring
    _ = √(α ^ 2) * √(y 0 ^ 2 + y 1 ^ 2) := Real.sqrt_mul (sq_nonneg α) _
    _ = α * √(y 0 ^ 2 + y 1 ^ 2) := by rw [Real.sqrt_sq hα.le]

theorem liftA_smul_pos {α : ℝ} (hα : 0 < α) (y : Space) :
    liftA (α • y) = α⁻¹ * liftA y := by
  unfold liftA
  rw [radius_smul_pos hα, mul_inv]

theorem ageS_smul_pos {α : ℝ} (hα : 0 < α) (y : Space) :
    ageS (α • y) = (α ^ 2)⁻¹ * ageS y := by
  unfold ageS
  rw [radius_smul_pos hα, mul_pow, mul_inv]

theorem etaCoord_smul_pos (ε : ℝ) {α : ℝ} (hα : 0 < α) (y : Space) :
    etaCoord ε (α • y) = etaCoord ε y := by
  unfold etaCoord
  rw [radius_smul_pos hα, PiLp.smul_apply, smul_eq_mul]
  calc (α * y 2) / (ε * (α * radius y))
      = (α * y 2) / (α * (ε * radius y)) := by ring
    _ = y 2 / (ε * radius y) := mul_div_mul_left _ _ hα.ne'

theorem unitRC_smul_pos {α : ℝ} (hα : 0 < α) (y : Space) :
    unitRC (α • y) = unitRC y := by
  unfold unitRC
  rw [radius_smul_pos hα, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ hα.ne', mul_div_mul_left _ _ hα.ne']

theorem frameC_smul_pos {α : ℝ} (hα : 0 < α) (y : Space) (v : MeridC) :
    frameC (α • y) v = frameC y v := by
  rw [frameC_apply, frameC_apply, unitRC_smul_pos hα]

theorem norm_phaseLiftRho_smul_frameC {ε : ℝ} (hε : 0 < ε) (P : ℝ) (y : Space) (v : MeridC) :
    ‖phaseLiftRho ε P y • frameC (ε • y) v‖ = phaseLiftRho ε P y * ‖v‖ := by
  unfold phaseLiftRho
  rw [mul_smul, norm_smul,
    Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg P) (Real.rpow_nonneg hε.le _)),
    norm_smul_frameC hε (ε • y) v]
  ring

theorem eps_mul_radius_le_of_mem_spaceBox {ε s₀ s₁ L : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀)
    {y : Space} (hy : y ∈ spaceBox ε s₀ s₁ L) :
    0 < radius y ∧ ε * radius y ≤ (Real.sqrt s₀)⁻¹ := by
  have hage : s₀ ≤ ageS (ε • y) := hy.1
  unfold ageS at hage
  have hr_eps_ne : radius (ε • y) ≠ 0 := by
    intro h0
    rw [h0] at hage
    norm_num at hage
    linarith
  have hr_eps_pos : 0 < radius (ε • y) :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) hr_eps_ne.symm
  have hr_pos : 0 < radius y := by
    rw [radius_smul_pos hε] at hr_eps_pos
    exact (mul_pos_iff_of_pos_left hε).1 hr_eps_pos
  have hsq : radius (ε • y) ^ 2 ≤ s₀⁻¹ := by
    have hpos2 : 0 < radius (ε • y) ^ 2 := pow_pos hr_eps_pos 2
    exact (le_inv_comm₀ hs₀ hpos2).1 hage
  have hsqrt : radius (ε • y) ≤ (Real.sqrt s₀)⁻¹ := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hr_eps_pos.le, Real.sqrt_inv] at h1
  rw [radius_smul_pos hε] at hsqrt
  exact ⟨hr_pos, hsqrt⟩

/-- Every point of `spaceBox ε s₀ s₁ L` (`0 < ε ≤ 1`, `0 < s₀`, `0 ≤ L`) lies in the Euclidean
ball of radius `ε⁻¹ * (1 + L) * (√s₀)⁻¹`. -/
theorem spaceBox_subset_closedBall {ε s₀ s₁ L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hs₀ : 0 < s₀) (hL : 0 ≤ L) :
    spaceBox ε s₀ s₁ L ⊆ Metric.closedBall 0 (ε⁻¹ * (1 + L) * (Real.sqrt s₀)⁻¹) := by
  intro y hy
  obtain ⟨hr_pos, hr_bd⟩ := eps_mul_radius_le_of_mem_spaceBox hε hs₀ hy
  have h1_le_inv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hrad_le : radius y ≤ ε⁻¹ * (Real.sqrt s₀)⁻¹ := by
    calc radius y
        = ε⁻¹ * (ε * radius y) := by field_simp
      _ ≤ ε⁻¹ * (Real.sqrt s₀)⁻¹ := mul_le_mul_of_nonneg_left hr_bd (inv_nonneg.2 hε.le)
  have heta : |etaCoord ε (ε • y)| ≤ L := hy.2.2
  rw [etaCoord_smul_pos ε hε y] at heta
  unfold etaCoord at heta
  have hy2_le : |y 2| ≤ ε⁻¹ * L * (Real.sqrt s₀)⁻¹ := by
    have hden_pos : 0 < ε * radius y := mul_pos hε hr_pos
    rw [abs_div, abs_of_pos hden_pos, div_le_iff₀ hden_pos] at heta
    calc |y 2|
        ≤ L * (ε * radius y) := heta
      _ ≤ L * (Real.sqrt s₀)⁻¹ := mul_le_mul_of_nonneg_left hr_bd hL
      _ = 1 * L * (Real.sqrt s₀)⁻¹ := by ring
      _ ≤ ε⁻¹ * L * (Real.sqrt s₀)⁻¹ := by gcongr
  rw [Metric.mem_closedBall, dist_zero_right]
  have hR0 : 0 ≤ ε⁻¹ * (1 + L) * (Real.sqrt s₀)⁻¹ := by positivity
  have hnorm_sq : ‖y‖ ^ 2 ≤ (ε⁻¹ * (1 + L) * (Real.sqrt s₀)⁻¹) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    have hr2 : y 0 ^ 2 + y 1 ^ 2 = radius y ^ 2 := (Real.sq_sqrt (by positivity)).symm
    have hsum : radius y + |y 2| ≤ ε⁻¹ * (1 + L) * (Real.sqrt s₀)⁻¹ := by
      calc radius y + |y 2|
          ≤ ε⁻¹ * (Real.sqrt s₀)⁻¹ + ε⁻¹ * L * (Real.sqrt s₀)⁻¹ := add_le_add hrad_le hy2_le
        _ = ε⁻¹ * (1 + L) * (Real.sqrt s₀)⁻¹ := by ring
    calc y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2
        = radius y ^ 2 + |y 2| ^ 2 := by rw [hr2, sq_abs]
      _ ≤ (radius y + |y 2|) ^ 2 := by
          nlinarith [mul_nonneg hr_pos.le (abs_nonneg (y 2))]
      _ ≤ (ε⁻¹ * (1 + L) * (Real.sqrt s₀)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (add_nonneg hr_pos.le (abs_nonneg _)) hsum 2
  exact (abs_le_of_sq_le_sq' hnorm_sq hR0).2

/-- On `spaceBox ε s₀ s₁ L`, the vertical shear displacement `|(h * ε) * radius y|` is bounded
uniformly in `ε` by `|h| * (√s₀)⁻¹`. -/
theorem abs_mul_radius_le_of_mem_spaceBox {ε s₀ s₁ L : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀)
    (h : ℝ) {y : Space} (hy : y ∈ spaceBox ε s₀ s₁ L) :
    |(h * ε) * radius y| ≤ |h| * (Real.sqrt s₀)⁻¹ := by
  obtain ⟨hr_pos, hr_bd⟩ := eps_mul_radius_le_of_mem_spaceBox hε hs₀ hy
  rw [mul_assoc, abs_mul, abs_of_pos (mul_pos hε hr_pos)]
  exact mul_le_mul_of_nonneg_left hr_bd (abs_nonneg h)

/-! ### 3. Exact `lintegral` change of variables `measureH c` ↔ `phaseVol P` -/

theorem lintegral_measureH_eq_phaseVol {ε c P : ℝ} [hPpos : Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    {F : Profile → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(measureH c) =
      ∫⁻ z, ENNReal.ofReal (phaseLiftRho ε P z.2 ^ 2) * F (phaseChartMap ε c P z) ∂(phaseVol P) := by
  have hT : Measurable fun x : PSpace P => cellChart ε c (toCell P x) :=
    (measurable_cellChart ε c).comp measurable_toCell
  have hmap := B0223.map_liftDensity hε hc hP
  have hd : Measurable fun x : PSpace P => ENNReal.ofReal ((jConst ε * liftA x.1) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_liftA.comp measurable_fst).const_mul _).pow_const 2)
  have hFT : Measurable fun x : PSpace P => F (cellChart ε c (toCell P x)) := hF.comp hT
  rw [← hmap, lintegral_map hF hT, lintegral_withDensity_eq_lintegral_mul _ hd hFT]
  set G : PSpace P → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((jConst ε * liftA x.1) ^ 2) * F (cellChart ε c (toCell P x))
  have hG : Measurable G := hd.mul hFT
  have hdil : ∫⁻ x : PSpace P, G (ε • x.1, x.2) =
      ENNReal.ofReal |(ε ^ 3)⁻¹| * ∫⁻ x : PSpace P, G x := by
    have hm_dil : Measurable fun x : PSpace P => (ε • x.1, x.2) :=
      (measurable_fst.const_smul ε).prodMk measurable_snd
    have h := lintegral_map hG hm_dil (μ := (volume : Measure (PSpace P)))
    rw [B0223.map_dil hε, lintegral_smul_measure] at h
    exact h.symm
  have hdil' : ∫⁻ x : PSpace P, G x =
      ENNReal.ofReal (ε ^ 3) * ∫⁻ x : PSpace P, G (ε • x.1, x.2) := by
    rw [hdil, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × Space → PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure Space))
      (volume : Measure (PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hGdil : Measurable fun x : PSpace P => G (ε • x.1, x.2) :=
    hG.comp ((measurable_fst.const_smul ε).prodMk measurable_snd)
  have hswap_eq : ∫⁻ x : PSpace P, G (ε • x.1, x.2) =
      ENNReal.ofReal P * ∫⁻ z : AddCircle P × Space, G (ε • z.2, z.1) ∂(phaseVol P) := by
    rw [← hsw.lintegral_comp hGdil, AddCircle.volume_eq_smul_haarAddCircle,
      Measure.prod_smul_left, lintegral_smul_measure]
    rfl
  change ∫⁻ x : PSpace P, G x = _
  rw [hdil', hswap_eq, ← mul_assoc, ← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  refine lintegral_congr fun z => ?_
  dsimp only [G, Prod.swap, phaseChartMap]
  rw [← mul_assoc]
  congr 1
  have hP0 : 0 < P := hPpos.out
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hrpow : (ε ^ (3 / 2 : ℝ)) ^ 2 = ε ^ 3 := by
    rw [← Real.rpow_natCast (ε ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hε.le]
    norm_num
  unfold phaseLiftRho
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hP0.le, hrpow]
  ring

theorem lintegral_profileBox_measureH_eq_phaseVol {ε c P : ℝ} [Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (s₀ s₁ L : ℝ)
    {F : Profile → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p in profileBox s₀ s₁ L, F p ∂(measureH c) =
      ∫⁻ z in univ ×ˢ spaceBox ε s₀ s₁ L,
        ENNReal.ofReal (phaseLiftRho ε P z.2 ^ 2) * F (phaseChartMap ε c P z) ∂(phaseVol P) := by
  have hmB := measurableSet_profileBox s₀ s₁ L
  have hmS : MeasurableSet ((univ : Set (AddCircle P)) ×ˢ spaceBox ε s₀ s₁ L) :=
    MeasurableSet.univ.prod (measurableSet_spaceBox ε s₀ s₁ L)
  rw [← lintegral_indicator hmB,
    lintegral_measureH_eq_phaseVol hε hc hP (hF.indicator hmB),
    ← lintegral_indicator hmS]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ (univ : Set (AddCircle P)) ×ˢ spaceBox ε s₀ s₁ L
  · have hp : phaseChartMap ε c P z ∈ profileBox s₀ s₁ L := by
      rw [← preimage_phaseChartMap_profileBox ε c P s₀ s₁ L] at hz
      exact hz
    rw [indicator_of_mem hp, indicator_of_mem hz]
  · have hp : phaseChartMap ε c P z ∉ profileBox s₀ s₁ L := by
      intro hmem
      apply hz
      rw [← preimage_phaseChartMap_profileBox ε c P s₀ s₁ L]
      exact hmem
    rw [indicator_of_notMem hp, indicator_of_notMem hz, mul_zero]

/-! ### 4. Product-model formula for `U (B0223.liftVec W)` -/

/-- Explicit Borel-measurable representative of `U (liftVec W)` on `(ℝ/Pℤ) × ℝ³`. -/
def phaseLiftRep (ε c P : ℝ) [Fact (0 < P)] (b : Profile → MeridC)
    (z : AddCircle P × Space) : SpaceC :=
  phaseLiftRho ε P z.2 • frameC (ε • z.2) (b (phaseChartMap ε c P z))

theorem measurable_phaseLiftRep (ε c P : ℝ) [Fact (0 < P)] {b : Profile → MeridC}
    (hb : Measurable b) :
    Measurable (phaseLiftRep ε c P b) := by
  unfold phaseLiftRep
  have h0 : Measurable fun z : AddCircle P × Space => (b (phaseChartMap ε c P z)) 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).measurable.comp
      (hb.comp (measurable_phaseChartMap ε c P))
  have h1 : Measurable fun z : AddCircle P × Space => (b (phaseChartMap ε c P z)) 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).measurable.comp
      (hb.comp (measurable_phaseChartMap ε c P))
  have hfr : Measurable fun z : AddCircle P × Space =>
      frameC (ε • z.2) (b (phaseChartMap ε c P z)) := by
    simp only [frameC_apply]
    exact (h0.smul (measurable_unitRC.comp (measurable_snd.const_smul ε))).add (h1.smul_const _)
  exact ((measurable_phaseLiftRho ε P).comp measurable_snd).smul hfr

theorem prodLpEquiv_symm_phaseLift_liftVec_ae {ε c P : ℝ} [hPpos : Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (hU : N01.IsPhaseLift ε P U)
    (W : HSpace c MeridC) :
    (prodLpEquiv.symm (U (B0223.liftVec hε hc hP W)) : AddCircle P × Space → CVec3) =ᵐ[phaseVol P]
      phaseLiftRep ε c P (periodize c (W : Profile → MeridC)) := by
  obtain ⟨F, hF_def⟩ : ∃ F : B0223.X SpaceC P, B0223.liftVec hε hc hP W = F := ⟨_, rfl⟩
  rw [hF_def]
  obtain ⟨v, hv_def⟩ : ∃ v : Yq P 2, U F = v := ⟨_, rfl⟩
  rw [hv_def]
  obtain ⟨b, hb_def⟩ : ∃ b : Profile → MeridC, periodize c (W : Profile → MeridC) = b := ⟨_, rfl⟩
  rw [hb_def]
  have hb_meas : Measurable b := by
    rw [← hb_def]
    exact N05_4Aux.measurable_periodize_meridC c (Lp.stronglyMeasurable W).measurable
  have hset : MeasurableSet
      {z : AddCircle P × Space |
        (prodLpEquiv.symm v : AddCircle P × Space → CVec3) z = phaseLiftRep ε c P b z} :=
    (Lp.stronglyMeasurable (prodLpEquiv.symm v)).measurableSet_eq_fun
      (measurable_phaseLiftRep ε c P hb_meas).stronglyMeasurable
  refine (Measure.ae_prod_iff_ae_ae hset).2 ?_
  have hF : ∀ᵐ x ∂(volume : Measure (PSpace P)),
      (F : PSpace P → SpaceC) x =
        (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA x.1 •
          frameC x.1 (b (chart ε (toCell P x))) := by
    rw [← hF_def, ← hb_def]
    exact B0223.coeFn_liftVec hε hc hP W
  have hdil : QuasiMeasurePreserving
      (fun x : PSpace P => (ε • x.1, x.2)) volume volume := by
    refine ⟨(measurable_fst.const_smul ε).prodMk measurable_snd, ?_⟩
    rw [B0223.map_dil hε]
    exact Measure.smul_absolutelyContinuous
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × Space → PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure Space))
      (volume : Measure (PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hall0 : ∀ᵐ θ ∂(volume : Measure (AddCircle P)),
      ∀ᵐ y ∂(volume : Measure Space),
        (F : PSpace P → SpaceC) (ε • y, θ) =
          (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            frameC (ε • y) (b (chart ε (toCell P (ε • y, θ)))) :=
    Measure.ae_ae_of_ae_prod (hsw.quasiMeasurePreserving.ae (hdil.ae hF))
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ∀ᵐ y ∂(volume : Measure Space),
        (F : PSpace P → SpaceC) (ε • y, θ) =
          (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            frameC (ε • y) (b (chart ε (toCell P (ε • y, θ)))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle] at hall0
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 hPpos.out).ne').1 hall0
  have hU_v : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((v θ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) =ᵐ[volume]
        fun y => (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) •
          (F : PSpace P → SpaceC) (ε • y, θ) := by
    rw [← hv_def]
    exact hU F
  have hb_per : QPeriodic c b := by
    rw [← hb_def]
    exact qPeriodic_periodize hc _
  filter_upwards [prodLpEquiv_symm_ae (ν := AddCircle.haarAddCircle (T := P))
      (μ := (volume : Measure Space)) v, hU_v, hall] with θ hV hUθ hFθ
  filter_upwards [hV, hUθ, hFθ] with y eV eU eF
  show (prodLpEquiv.symm v : AddCircle P × Space → CVec3) (θ, y) = phaseLiftRep ε c P b (θ, y)
  rw [eV, eU, eF]
  have hper_eq : b (chart ε (toCell P (ε • y, θ))) = b (phaseChartMap ε c P (θ, y)) := by
    dsimp only [phaseChartMap, cellChart, chart]
    exact (periodic_reduceIoc_eq b hb_per _ _ _).symm
  rw [hper_eq, Complex.coe_smul, smul_smul, smul_smul]
  dsimp only [phaseLiftRep, phaseLiftRho, jConst]
  congr 1
  ring

/-! ### 5. Pointwise shift relations on `(ℝ/Pℤ) × ℝ³` and exact `lintegral` bridges -/

private theorem equivIoc_add_shift {P : ℝ} [Fact (0 < P)] (θ : AddCircle P) (t : ℝ) :
    ∃ n : ℤ,
      ((AddCircle.measurableEquivIoc P 0 (θ + (t : AddCircle P)) : Ioc (0 : ℝ) (0 + P)) : ℝ) =
        ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ) + t + (n : ℝ) * P := by
  set τ₁ : ℝ :=
    ((AddCircle.measurableEquivIoc P 0 (θ + (t : AddCircle P)) : Ioc (0 : ℝ) (0 + P)) : ℝ)
  set τ₀ : ℝ := ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ)
  have h0 : ((τ₁ - (τ₀ + t) : ℝ) : AddCircle P) = 0 := by
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add]
    have e1 : (τ₁ : AddCircle P) = θ + (t : AddCircle P) := AddCircle.coe_equivIoc
    have e0 : (τ₀ : AddCircle P) = θ := AddCircle.coe_equivIoc
    rw [e1, e0, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).1 h0
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn
  linarith

private theorem periodic_shiftQ_reduceIoc {E : Type*} {c : ℝ} {b : Profile → E}
    (hb : QPeriodic c b) (h s q η : ℝ) :
    b (shiftQ h (s, reduceIoc c q, η)) = b (s, q + h, η) := by
  have hper : Function.Periodic (fun r => b (s, r, η)) c := fun r => hb (s, r, η)
  dsimp only [shiftQ]
  rw [reduceIoc_eq_sub c q]
  have hrew : q - ((⌈q / c⌉ - 1 : ℤ) : ℝ) * c + h =
      (q + h) - ((⌈q / c⌉ - 1 : ℤ) : ℝ) * c := by ring
  rw [hrew]
  exact hper.sub_int_mul_eq _

private theorem periodic_add_int_mul {E : Type*} {c : ℝ} {b : Profile → E}
    (hb : QPeriodic c b) (s q η : ℝ) (n : ℤ) :
    b (s, q + (n : ℝ) * c, η) = b (s, q, η) := by
  have hper : Function.Periodic (fun r => b (s, r, η)) c := fun r => hb (s, r, η)
  exact hper.int_mul n q

private theorem enorm_phaseLiftRho_smul_frameC_sq {ε : ℝ} (hε : 0 < ε) (P : ℝ)
    (y : Space) (u : MeridC) :
    ‖phaseLiftRho ε P y • frameC (ε • y) u‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (phaseLiftRho ε P y ^ 2) * ‖u‖ₑ ^ (2 : ℝ) := by
  rw [← ofReal_norm, norm_phaseLiftRho_smul_frameC hε P y,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (phaseLiftRho_nonneg hε P y) (norm_nonneg u))
      (by norm_num),
    Real.rpow_two, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg u) (by norm_num), Real.rpow_two]

/-- **Bridge 1 (`shiftQ`)**: profile `shiftQ h` on `measureH c` equals phase shift `2 * ε * h` on
`phaseVol P`. -/
theorem lintegral_profileBox_shiftQ_sub_sq_eq {ε c P : ℝ} [Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (hU : N01.IsPhaseLift ε P U)
    (W : HSpace c MeridC) (s₀ s₁ L h : ℝ) :
    ∫⁻ p in profileBox s₀ s₁ L,
        ‖periodize c (W : Profile → MeridC) (shiftQ h p) -
            periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ∫⁻ z in univ ×ˢ spaceBox ε s₀ s₁ L,
        ‖(prodLpEquiv.symm (U (B0223.liftVec hε hc hP W)) : AddCircle P × Space → CVec3)
            (z.1 + ((2 * ε * h : ℝ) : AddCircle P), z.2) -
          (prodLpEquiv.symm (U (B0223.liftVec hε hc hP W)) : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ)
        ∂(phaseVol P) := by
  have hb_per : QPeriodic c (periodize c (W : Profile → MeridC)) := qPeriodic_periodize hc _
  have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hF_meas : Measurable fun p : Profile =>
      ‖periodize c (W : Profile → MeridC) (shiftQ h p) -
        periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) :=
    ((hb_meas.comp (N05_3_1Aux.measurable_shiftQ h)).sub hb_meas).enorm.pow_const _
  rw [lintegral_profileBox_measureH_eq_phaseVol hε hc hP s₀ s₁ L hF_meas]
  have hV₀ := prodLpEquiv_symm_phaseLift_liftVec_ae hε hc hP U hU W
  set θ_h : AddCircle P := ((2 * ε * h : ℝ) : AddCircle P)
  have hV_shift := (measurePreserving_phaseAdd θ_h).quasiMeasurePreserving.ae_eq_comp hV₀
  refine setLIntegral_congr_fun_ae (MeasurableSet.univ.prod (measurableSet_spaceBox ε s₀ s₁ L)) ?_
  filter_upwards [hV_shift, hV₀] with z hz1 hz0 _
  simp only [Function.comp_apply] at hz1
  rw [hz1, hz0]
  obtain ⟨θ, y⟩ := z
  obtain ⟨n, hn⟩ := equivIoc_add_shift θ (2 * ε * h)
  have hnP : (n : ℝ) * P = (n : ℝ) * (2 * ε * c) := by rw [hP]
  have hchart_q :
      periodize c (W : Profile → MeridC) (phaseChartMap ε c P (θ + θ_h, y)) =
        periodize c (W : Profile → MeridC) (shiftQ h (phaseChartMap ε c P (θ, y))) := by
    dsimp only [phaseChartMap, cellChart, toCell, θ_h]
    rw [periodic_reduceIoc_eq _ hb_per, periodic_shiftQ_reduceIoc hb_per]
    have hcellQ : cellQ ε (ε • y)
        ((AddCircle.measurableEquivIoc P 0 (θ + ((2 * ε * h : ℝ) : AddCircle P)) :
          Ioc (0 : ℝ) (0 + P)) : ℝ) =
        cellQ ε (ε • y)
          ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ) + h + (n : ℝ) * c := by
      rw [hn, hnP]
      unfold cellQ
      have h2ε : 2 * ε ≠ 0 := by positivity
      field_simp
      ring
    rw [hcellQ, periodic_add_int_mul hb_per]
  have hdiff :
      phaseLiftRep ε c P (periodize c (W : Profile → MeridC)) (θ + θ_h, y) -
        phaseLiftRep ε c P (periodize c (W : Profile → MeridC)) (θ, y) =
      phaseLiftRho ε P y •
        frameC (ε • y)
          (periodize c (W : Profile → MeridC) (shiftQ h (phaseChartMap ε c P (θ, y))) -
            periodize c (W : Profile → MeridC) (phaseChartMap ε c P (θ, y))) := by
    dsimp only [phaseLiftRep]
    rw [hchart_q, ← smul_sub, ← map_sub]
  rw [hdiff, enorm_phaseLiftRho_smul_frameC_sq hε P y]

/-- **Bridge 2 (`shiftEta`)**: profile `shiftEta h` on `measureH c` equals vertical shear
`shearZ (h * ε)` on `phaseVol P`. -/
theorem lintegral_profileBox_shiftEta_sub_sq_eq {ε c P : ℝ} [Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (hU : N01.IsPhaseLift ε P U)
    (W : HSpace c MeridC) (s₀ s₁ L h : ℝ) :
    ∫⁻ p in profileBox s₀ s₁ L,
        ‖periodize c (W : Profile → MeridC) (shiftEta h p) -
            periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ∫⁻ z in univ ×ˢ spaceBox ε s₀ s₁ L,
        ‖(prodLpEquiv.symm (U (B0223.liftVec hε hc hP W)) : AddCircle P × Space → CVec3)
            (z.1, shearZ (h * ε) z.2) -
          (prodLpEquiv.symm (U (B0223.liftVec hε hc hP W)) : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ)
        ∂(phaseVol P) := by
  have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hF_meas : Measurable fun p : Profile =>
      ‖periodize c (W : Profile → MeridC) (shiftEta h p) -
        periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) :=
    ((hb_meas.comp (N05_3_1Aux.measurable_shiftEta h)).sub hb_meas).enorm.pow_const _
  rw [lintegral_profileBox_measureH_eq_phaseVol hε hc hP s₀ s₁ L hF_meas]
  have hV₀ := prodLpEquiv_symm_phaseLift_liftVec_ae hε hc hP U hU W
  have hmp_sh : MeasurePreserving (fun z : AddCircle P × Space => (z.1, shearZ (h * ε) z.2))
      (phaseVol P) (phaseVol P) :=
    (MeasurePreserving.id _).prod (measurePreserving_shearZ (h * ε))
  have hV_sh := hmp_sh.quasiMeasurePreserving.ae_eq_comp hV₀
  refine setLIntegral_congr_fun_ae (MeasurableSet.univ.prod (measurableSet_spaceBox ε s₀ s₁ L)) ?_
  filter_upwards [hV_sh, hV₀] with z hz1 hz0 _
  simp only [Function.comp_apply] at hz1
  rw [hz1, hz0]
  obtain ⟨θ, y⟩ := z
  by_cases hr0 : radius y = 0
  · have hr_eps : radius (ε • y) = 0 := by rw [radius_smul_pos hε, hr0, mul_zero]
    have hr_sh : radius (ε • shearZ (h * ε) y) = 0 := by
      rw [radius_smul_pos hε, radius_shearZ, hr0, mul_zero]
    have hρ0 : phaseLiftRho ε P y = 0 := by
      unfold phaseLiftRho; rw [liftA_eq_zero hr_eps]; ring
    have hρ1 : phaseLiftRho ε P (shearZ (h * ε) y) = 0 := by
      unfold phaseLiftRho; rw [liftA_eq_zero hr_sh]; ring
    simp [phaseLiftRep, hρ0, hρ1]
  · have hr_sh_eps : radius (ε • shearZ (h * ε) y) = radius (ε • y) := by
      rw [radius_smul_pos hε, radius_shearZ, radius_smul_pos hε]
    have hρ_eq : phaseLiftRho ε P (shearZ (h * ε) y) = phaseLiftRho ε P y := by
      unfold phaseLiftRho liftA
      rw [hr_sh_eps]
    have hunit_eq : unitRC (ε • shearZ (h * ε) y) = unitRC (ε • y) := by
      rw [unitRC_smul_pos hε, unitRC_smul_pos hε]
      unfold unitRC
      rw [shearZ_apply_zero, shearZ_apply_one, radius_shearZ]
    have hframe_eq : ∀ v : MeridC, frameC (ε • shearZ (h * ε) y) v = frameC (ε • y) v := by
      intro v
      rw [frameC_apply, frameC_apply, hunit_eq]
    have hchart_sh : phaseChartMap ε c P (θ, shearZ (h * ε) y) =
        shiftEta h (phaseChartMap ε c P (θ, y)) := by
      have h1 : ageS (ε • shearZ (h * ε) y) = ageS (ε • y) := by
        unfold ageS; rw [hr_sh_eps]
      have h2 : cellQ ε (ε • shearZ (h * ε) y)
          ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ) =
          cellQ ε (ε • y)
            ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ) := by
        unfold cellQ; rw [hr_sh_eps]
      have h3 : etaCoord ε (ε • shearZ (h * ε) y) = etaCoord ε (ε • y) + h := by
        rw [etaCoord_smul_pos ε hε, etaCoord_smul_pos ε hε]
        unfold etaCoord
        rw [shearZ_apply_two, radius_shearZ]
        have hden : ε * radius y ≠ 0 := mul_ne_zero hε.ne' hr0
        field_simp
      simp only [phaseChartMap, cellChart, toCell, shiftEta, h1, h2, h3]
    have hdiff :
        phaseLiftRep ε c P (periodize c (W : Profile → MeridC)) (θ, shearZ (h * ε) y) -
          phaseLiftRep ε c P (periodize c (W : Profile → MeridC)) (θ, y) =
        phaseLiftRho ε P y •
          frameC (ε • y)
            (periodize c (W : Profile → MeridC) (shiftEta h (phaseChartMap ε c P (θ, y))) -
              periodize c (W : Profile → MeridC) (phaseChartMap ε c P (θ, y))) := by
      dsimp only [phaseLiftRep]
      rw [hρ_eq, hframe_eq, hchart_sh, ← smul_sub, ← map_sub]
    rw [hdiff, enorm_phaseLiftRho_smul_frameC_sq hε P y]

/-- **Bridge 3 (`phaseDilation`)**: `L²(measureH c)` norm squared of
`e^{-t/4} • b(e^t s, q, η) - b(s, q, η)` equals `‖phaseDilation P t v - v‖ₑ ^ 2`. -/
theorem lintegral_measureH_exp_age_sub_sq_eq {ε c P : ℝ} [Fact (0 < P)]
    (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) (hU : N01.IsPhaseLift ε P U)
    (W : HSpace c MeridC) (t : ℝ) :
    ∫⁻ p,
        ‖(Real.exp (-(t / 4)) : ℂ) •
            periodize c (W : Profile → MeridC) (Real.exp t * p.1, p.2) -
          periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
      ‖FreeStress.phaseDilation P t (U (B0223.liftVec hε hc hP W)) -
        U (B0223.liftVec hε hc hP W)‖ₑ ^ (2 : ℝ) := by
  have hb_per : QPeriodic c (periodize c (W : Profile → MeridC)) := qPeriodic_periodize hc _
  have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hscale_meas : Measurable fun p : Profile => (Real.exp t * p.1, p.2) :=
    (measurable_fst.const_mul (Real.exp t)).prodMk measurable_snd
  have hF_meas : Measurable fun p : Profile =>
      ‖(Real.exp (-(t / 4)) : ℂ) •
          periodize c (W : Profile → MeridC) (Real.exp t * p.1, p.2) -
        periodize c (W : Profile → MeridC) p‖ₑ ^ (2 : ℝ) :=
    (((hb_meas.comp hscale_meas).const_smul ((Real.exp (-(t / 4)) : ℂ))).sub
      hb_meas).enorm.pow_const _
  rw [lintegral_measureH_eq_phaseVol hε hc hP hF_meas]
  have hV₀ := prodLpEquiv_symm_phaseLift_liftVec_ae hε hc hP U hU W
  obtain ⟨v, hv_def⟩ : ∃ v : Yq P 2, U (B0223.liftVec hε hc hP W) = v := ⟨_, rfl⟩
  rw [hv_def] at hV₀ ⊢
  set α : ℝ := Real.exp (-(t / 2))
  have hα_pos : 0 < α := Real.exp_pos _
  have hqmp_dil : QuasiMeasurePreserving
      (fun z : AddCircle P × Space => (z.1 + (t : AddCircle P), α • z.2))
      (phaseVol P) (phaseVol P) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (MeasurePreserving.quasiMeasurePreserving
        ⟨measurable_add_const (t : AddCircle P),
          Measure.IsAddRightInvariant.map_add_right_eq_self (t : AddCircle P)⟩)
      (quasiMeasurePreserving_smul_space hα_pos.ne')
  have hV_dil := hqmp_dil.ae_eq_comp hV₀
  have hsub_ae := Lp.coeFn_sub (prodLpEquiv.symm (phaseDilation P t v)) (prodLpEquiv.symm v)
  have hmap_sub : prodLpEquiv.symm (phaseDilation P t v - v) =
      prodLpEquiv.symm (phaseDilation P t v) - prodLpEquiv.symm v := map_sub _ _ _
  have hlhs_eq : ∫⁻ z,
      ENNReal.ofReal (phaseLiftRho ε P z.2 ^ 2) *
        ‖(Real.exp (-(t / 4)) : ℂ) •
            periodize c (W : Profile → MeridC)
              (Real.exp t * (phaseChartMap ε c P z).1, (phaseChartMap ε c P z).2) -
          periodize c (W : Profile → MeridC) (phaseChartMap ε c P z)‖ₑ ^ (2 : ℝ) ∂(phaseVol P) =
      ∫⁻ z, ‖(prodLpEquiv.symm (phaseDilation P t v - v) : AddCircle P × Space → CVec3) z‖ₑ ^
        (2 : ℝ) ∂(phaseVol P) := by
    refine lintegral_congr_ae ?_
    filter_upwards [phaseDilation_ae P t v, hV_dil, hV₀, hsub_ae] with z hD hz1 hz0 hsub
    simp only [Function.comp_apply] at hz1
    rw [hmap_sub, hsub, Pi.sub_apply, hD, hz1, hz0]
    obtain ⟨θ, y⟩ := z
    by_cases hr0 : radius y = 0
    · have hr_eps : radius (ε • y) = 0 := by rw [radius_smul_pos hε, hr0, mul_zero]
      have hr_dil : radius (ε • (α • y)) = 0 := by
        rw [radius_smul_pos hε, radius_smul_pos hα_pos, hr0, mul_zero, mul_zero]
      have hρ0 : phaseLiftRho ε P y = 0 := by
        unfold phaseLiftRho; rw [liftA_eq_zero hr_eps]; ring
      have hρ1 : phaseLiftRho ε P (α • y) = 0 := by
        unfold phaseLiftRho; rw [liftA_eq_zero hr_dil]; ring
      simp [phaseLiftRep, hρ0, hρ1]
    · have hr_pos : 0 < radius y :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
      have hr_eps_pos : 0 < radius (ε • y) := by
        rw [radius_smul_pos hε]; exact mul_pos hε hr_pos
      have hcomm : ε • (α • y) = α • (ε • y) := smul_comm ε α y
      have hα_inv : α⁻¹ = Real.exp (t / 2) := by
        dsimp only [α]
        rw [← Real.exp_neg, neg_neg]
      have hα_sq_inv : (α ^ 2)⁻¹ = Real.exp t := by
        dsimp only [α]
        rw [← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1
        push_cast
        ring
      have hρ_dil : phaseLiftRho ε P (α • y) = Real.exp (t / 2) * phaseLiftRho ε P y := by
        unfold phaseLiftRho
        rw [hcomm, liftA_smul_pos hα_pos, hα_inv]
        ring
      have hframe_dil : ∀ u : MeridC, frameC (ε • (α • y)) u = frameC (ε • y) u := by
        intro u
        rw [hcomm, frameC_smul_pos hα_pos]
      obtain ⟨n, hn⟩ := equivIoc_add_shift θ t
      have hnP : (n : ℝ) * P = (n : ℝ) * (2 * ε * c) := by rw [hP]
      have hchart_dil :
          periodize c (W : Profile → MeridC)
              (phaseChartMap ε c P (θ + (t : AddCircle P), α • y)) =
            periodize c (W : Profile → MeridC)
              (Real.exp t * (phaseChartMap ε c P (θ, y)).1, (phaseChartMap ε c P (θ, y)).2) := by
        dsimp only [phaseChartMap, cellChart, toCell]
        rw [periodic_reduceIoc_eq _ hb_per]
        have hage_eq : ageS (ε • (α • y)) = Real.exp t * ageS (ε • y) := by
          rw [hcomm, ageS_smul_pos hα_pos, hα_sq_inv]
        have heta_eq : etaCoord ε (ε • (α • y)) = etaCoord ε (ε • y) := by
          rw [hcomm, etaCoord_smul_pos ε hα_pos]
        have hcellQ_eq : cellQ ε (ε • (α • y))
            ((AddCircle.measurableEquivIoc P 0 (θ + (t : AddCircle P)) :
              Ioc (0 : ℝ) (0 + P)) : ℝ) =
            cellQ ε (ε • y)
              ((AddCircle.measurableEquivIoc P 0 θ : Ioc (0 : ℝ) (0 + P)) : ℝ) + (n : ℝ) * c := by
          rw [hn, hnP, hcomm]
          unfold cellQ
          rw [radius_smul_pos hα_pos, Real.log_mul hα_pos.ne' hr_eps_pos.ne',
            show Real.log α = -(t / 2) from Real.log_exp _]
          have h2ε : 2 * ε ≠ 0 := by positivity
          have hε0 : ε ≠ 0 := hε.ne'
          field_simp
          ring
        rw [hage_eq, heta_eq, hcellQ_eq, periodic_add_int_mul hb_per]
        exact (periodic_reduceIoc_eq _ hb_per _ _ _).symm
      have hexp_mul : Real.exp (-(3 / 4) * t) * Real.exp (t / 2) = Real.exp (-(t / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hdiff :
          (Real.exp (-(3 / 4) * t) : ℂ) •
              phaseLiftRep ε c P (periodize c (W : Profile → MeridC))
                (θ + (t : AddCircle P), α • y) -
            phaseLiftRep ε c P (periodize c (W : Profile → MeridC)) (θ, y) =
          phaseLiftRho ε P y • frameC (ε • y)
            ((Real.exp (-(t / 4)) : ℂ) •
              periodize c (W : Profile → MeridC)
                (Real.exp t * (phaseChartMap ε c P (θ, y)).1, (phaseChartMap ε c P (θ, y)).2) -
              periodize c (W : Profile → MeridC) (phaseChartMap ε c P (θ, y))) := by
        have hscalar : Real.exp (-(3 / 4) * t) * (Real.exp (t / 2) * phaseLiftRho ε P y) =
            phaseLiftRho ε P y * Real.exp (-(t / 4)) := by
          calc Real.exp (-(3 / 4) * t) * (Real.exp (t / 2) * phaseLiftRho ε P y)
              = (Real.exp (-(3 / 4) * t) * Real.exp (t / 2)) * phaseLiftRho ε P y := by ring
            _ = Real.exp (-(t / 4)) * phaseLiftRho ε P y := by rw [hexp_mul]
            _ = phaseLiftRho ε P y * Real.exp (-(t / 4)) := by ring
        dsimp only [phaseLiftRep]
        rw [hρ_dil, hframe_dil, hchart_dil, map_sub, map_smul, smul_sub,
          Complex.coe_smul, Complex.coe_smul, smul_smul, smul_smul, hscalar]
      rw [hdiff, enorm_phaseLiftRho_smul_frameC_sq hε P y]
  rw [hlhs_eq, lintegral_enorm_sq_eq_ofReal_norm_sq, prodLpEquiv.symm.norm_map,
    ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

end UnforcedLeray.Short.PartIIa.N05FlowAux
