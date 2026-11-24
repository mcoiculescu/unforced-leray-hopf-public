import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.CompactFreeBodyRate.NormBridge
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3
import UnforcedLeray.Short.PartIIa.Sub.N01.Reduction
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L2.Slices

/-!
# Identification of `Teps` with `IIb.IsResponse` at `r = 2`

Shows that for `F, bε ∈ InHr c 2` with `IsResponse ν c ε μ 2 F bε`, the periodic extension
`B0220.periodize c (PartIIa.Teps ... FH)` agrees `hMeas c 2`-almost everywhere with `bε`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.CompactFreeRateSub

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (measurePreserving_shiftQ)

private theorem qPeriodic_int {c : ℝ} {b : Profile → MeridC} (hper : B0220.QPeriodic c b)
    (m : ℤ) (p : Profile) :
    b (p.1, p.2.1 + (m : ℝ) * c, p.2.2) = b p := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e : p.2.1 + ((k + 1 : ℤ) : ℝ) * c = (p.2.1 + ((k : ℤ) : ℝ) * c) + c := by push_cast; ring
    rw [e, hper (p.1, p.2.1 + ((k : ℤ) : ℝ) * c, p.2.2), ih]
  | pred k ih =>
    have e : (p.2.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c) + c = p.2.1 + ((-(k : ℤ) : ℤ) : ℝ) * c := by
      push_cast; ring
    have hstep := hper (p.1, p.2.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, p.2.2)
    dsimp only at hstep
    rw [e] at hstep
    exact hstep.symm.trans ih

private theorem radius_smul_pos {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    radius (ε • y) = ε * radius y := by
  unfold radius
  simp only [PiLp.smul_apply, smul_eq_mul]
  have h : (ε * y 0) ^ 2 + (ε * y 1) ^ 2 = ε ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

private theorem ageS_smul_eq_age {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    ageS (ε • y) = UnforcedLeray.Axi.age ε⁻¹ y := by
  have hr : radius y = UnforcedLeray.Axi.ϱ y := rfl
  unfold ageS UnforcedLeray.Axi.age
  rw [radius_smul_pos hε, hr]
  by_cases hy : UnforcedLeray.Axi.ϱ y = 0
  · simp [hy]
  · have hε0 : ε ≠ 0 := hε.ne'
    field_simp

private theorem liftA_smul_eq_sqrt_age {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    liftA (ε • y) = Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) := by
  rw [← ageS_smul_eq_age hε y]
  have hrad : 0 ≤ radius (ε • y) := by unfold radius; exact Real.sqrt_nonneg _
  unfold ageS liftA
  rw [Real.sqrt_inv, Real.sqrt_sq hrad]

private theorem chart_smul_eq_axiChart {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) (τ : ℝ) :
    B0220.chart ε (ε • y, τ) = UnforcedLeray.Axi.chart ε⁻¹ τ y := by
  have hr : radius y = UnforcedLeray.Axi.ϱ y := rfl
  have hε0 : ε ≠ 0 := hε.ne'
  unfold B0220.chart UnforcedLeray.Axi.chart
  refine Prod.ext (ageS_smul_eq_age hε y) (Prod.ext ?_ ?_)
  · unfold cellQ UnforcedLeray.Axi.phase
    rw [← ageS_smul_eq_age hε y]
    unfold ageS
    rw [Real.log_inv, Real.log_pow]
    push_cast
    field_simp
    ring
  · unfold etaCoord UnforcedLeray.Axi.trans
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [radius_smul_pos hε, hr]
    by_cases hy : UnforcedLeray.Axi.ϱ y = 0
    · simp [hy]
    · field_simp

private theorem unitRC_smul_pos {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) :
    unitRC (ε • y) = unitRC y := by
  have hε0 : ε ≠ 0 := hε.ne'
  unfold unitRC
  simp only [PiLp.smul_apply, smul_eq_mul, radius_smul_pos hε, mul_div_mul_left _ _ hε0]

private theorem frameC_smul_pos {ε : ℝ} (hε : 0 < ε) (y : UnforcedLeray.Space) (v : MeridC) :
    B0223.frameC (ε • y) v = B0223.frameC y v := by
  simp only [B0223.frameC_apply, unitRC_smul_pos hε]

private theorem axiChart_shift_int {ε c : ℝ} (hR0 : (ε⁻¹ : ℝ) ≠ 0)
    (hPdiv : 2 * ε * c = 2 * c / ε⁻¹) (τ : ℝ) (y : UnforcedLeray.Space) (m : ℤ) :
    UnforcedLeray.Axi.chart ε⁻¹ (τ + (m : ℝ) * (2 * ε * c)) y =
      ((UnforcedLeray.Axi.chart ε⁻¹ τ y).1,
        (UnforcedLeray.Axi.chart ε⁻¹ τ y).2.1 + (m : ℝ) * c,
        (UnforcedLeray.Axi.chart ε⁻¹ τ y).2.2) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have e1 : τ + ((k + 1 : ℤ) : ℝ) * (2 * ε * c) =
        (τ + ((k : ℤ) : ℝ) * (2 * ε * c)) + 2 * ε * c := by push_cast; ring
    rw [e1, UnforcedLeray.Axi.chart_add_period hR0 hPdiv]
    have ih1 := congrArg Prod.fst ih
    have ih2 := congrArg (fun p => p.2.1) ih
    have ih3 := congrArg (fun p => p.2.2) ih
    dsimp only [UnforcedLeray.Axi.chart] at ih1 ih2 ih3 ⊢
    refine Prod.ext ih1 (Prod.ext ?_ ih3)
    rw [ih2]
    push_cast
    ring
  | pred k ih =>
    have e1 : (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c)) + 2 * ε * c =
        τ + ((-(k : ℤ) : ℤ) : ℝ) * (2 * ε * c) := by push_cast; ring
    have hstep := UnforcedLeray.Axi.chart_add_period hR0 hPdiv
      (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * (2 * ε * c)) y
    rw [e1] at hstep
    have heq := hstep.symm.trans ih
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg (fun p => p.2.1) heq
    have h3 := congrArg (fun p => p.2.2) heq
    dsimp only [UnforcedLeray.Axi.chart] at h1 h2 h3 ⊢
    refine Prod.ext h1.symm (Prod.ext ?_ h3.symm)
    push_cast at h2 ⊢
    linarith

private theorem nvC_pointwise_eq {ε c : ℝ} (hε : 0 < ε) {b : Profile → MeridC}
    (hper : B0220.QPeriodic c b) (κ : ℝ) (τ : ℝ) (y : UnforcedLeray.Space) (n : ℤ) :
    NvC ε⁻¹ (fun p => ((κ : ℝ) : ℂ) • b p) (τ, y) =
      (((κ * liftA (ε • y) : ℝ) : ℂ)) •
        B0223.frameC (ε • y) (b (B0220.chart ε (ε • y, τ + (n : ℝ) * (2 * ε * c)))) := by
  have hR0 : (ε⁻¹ : ℝ) ≠ 0 := inv_ne_zero hε.ne'
  have hPdiv : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hchart_shift :
      b (B0220.chart ε (ε • y, τ + (n : ℝ) * (2 * ε * c))) = b (UnforcedLeray.Axi.chart ε⁻¹ τ y) := by
    rw [chart_smul_eq_axiChart hε, axiChart_shift_int hR0 hPdiv τ y n]
    exact qPeriodic_int hper n (UnforcedLeray.Axi.chart ε⁻¹ τ y)
  rw [hchart_shift, frameC_smul_pos hε, liftA_smul_eq_sqrt_age hε]
  have hr : radius y = UnforcedLeray.Axi.ϱ y := rfl
  have hv0 := Complex.re_add_im (b (UnforcedLeray.Axi.chart ε⁻¹ τ y) 0)
  have hv1 := Complex.re_add_im (b (UnforcedLeray.Axi.chart ε⁻¹ τ y) 1)
  ext i
  simp only [NvC, UnforcedLeray.Axi.Nv,
    UnforcedLeray.Axi.frameL_apply, reM, imM, B0223.frameC_apply, unitRC, unitZC,
    UnforcedLeray.Axi.eR, UnforcedLeray.Axi.hor, UnforcedLeray.Axi.e3,
    UnforcedLeray.coordinateVector, UnforcedLeray.B0412.realC_apply,
    PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hr]
  fin_cases i
  · simp [div_eq_inv_mul]
    linear_combination ((Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) : ℂ) * κ *
      ((UnforcedLeray.Axi.ϱ y : ℂ)⁻¹ * y 0)) * hv0
  · simp [div_eq_inv_mul]
    linear_combination ((Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) : ℂ) * κ *
      ((UnforcedLeray.Axi.ϱ y : ℂ)⁻¹ * y 1)) * hv0
  · simp
    linear_combination ((Real.sqrt (UnforcedLeray.Axi.age ε⁻¹ y) : ℂ) * κ) * hv1

private theorem lift_prefactor_eq {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    Real.sqrt (2 * ε * c) * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹ =
      Real.sqrt (c / Real.pi) * ε := by
  have h1 : 0 ≤ Real.sqrt (2 * ε * c) * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹ := by
    positivity
  have h2 : 0 ≤ Real.sqrt (c / Real.pi) * ε := by positivity
  rw [← sq_eq_sq₀ h1 h2]
  have hrpow : (ε ^ (3 / 2 : ℝ)) ^ 2 = ε ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [mul_pow, mul_pow, inv_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hrpow]
  field_simp

private theorem toCell_snd_shift {P : ℝ} [Fact (0 < P)] (τ : ℝ) :
    ∃ n : ℤ, ((AddCircle.measurableEquivIoc P 0 (τ : AddCircle P) : Ioc (0 : ℝ) (0 + P)) : ℝ) =
      τ + (n : ℝ) * P := by
  set t' : ℝ := ((AddCircle.measurableEquivIoc P 0 (τ : AddCircle P) : Ioc (0 : ℝ) (0 + P)) : ℝ)
  have h0 : ((t' - τ : ℝ) : AddCircle P) = 0 := by
    rw [QuotientAddGroup.mk_sub]
    have heq : (t' : AddCircle P) = (τ : AddCircle P) := AddCircle.coe_equivIoc
    rw [heq, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff P).mp h0
  refine ⟨n, ?_⟩
  rw [zsmul_eq_mul] at hn
  linarith

private theorem hasRepY_phaseLift_liftVec {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    [hPpos : Fact (0 < 2 * ε * c)]
    (U : B0223.X SpaceC (2 * ε * c) →ₗᵢ[ℂ] Yq (2 * ε * c) 2)
    (hU : N01.IsPhaseLift ε (2 * ε * c) U) (w : HSpace c MeridC) :
    HasRepY
      (U (B0223.liftVec hε hc rfl w))
      (NvC ε⁻¹
        (fun p => ((Real.sqrt (c / Real.pi) * ε : ℝ) : ℂ) •
          periodize c (w : Profile → MeridC) p)) := by
  set P : ℝ := 2 * ε * c
  set κ : ℝ := Real.sqrt (c / Real.pi) * ε
  set b_w : Profile → MeridC := periodize c (w : Profile → MeridC)
  set b₀ : CProf := fun p => ((κ : ℝ) : ℂ) • b_w p
  set F : B0223.X SpaceC P := B0223.liftVec hε hc rfl w
  have hb₀_meas : Measurable b₀ :=
    (measurable_periodize_merid c (Lp.stronglyMeasurable w).measurable).const_smul ((κ : ℝ) : ℂ)
  refine ⟨(NvCInYrHelp.measurable_NvC' ε⁻¹ hb₀_meas).aestronglyMeasurable, ?_⟩
  have hF : ∀ᵐ z ∂(volume : Measure (B0223.PSpace P)),
      (F : B0223.PSpace P → SpaceC) z =
        (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA z.1 •
          B0223.frameC z.1 (b_w (B0220.chart ε (B0223.toCell P z))) :=
    B0223.coeFn_liftVec hε hc rfl w
  have hdil : Measure.QuasiMeasurePreserving
      (fun z : B0223.PSpace P => (ε • z.1, z.2)) volume volume := by
    refine ⟨((measurable_const_smul ε).comp measurable_fst).prodMk measurable_snd, ?_⟩
    rw [B0223.map_dil hε]
    exact Measure.smul_absolutelyContinuous
  have hF2 := hdil.ae hF
  have hsw : MeasurePreserving (Prod.swap : AddCircle P × UnforcedLeray.Space → B0223.PSpace P)
      ((volume : Measure (AddCircle P)).prod (volume : Measure UnforcedLeray.Space))
      (volume : Measure (B0223.PSpace P)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hall0 : ∀ᵐ θ ∂(volume : Measure (AddCircle P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
        (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
          (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            B0223.frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ)))) :=
    Measure.ae_ae_of_ae_prod (hsw.quasiMeasurePreserving.ae hF2)
  have hall : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
        (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
          (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            B0223.frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ)))) := by
    have h' : ∀ᵐ θ ∂(ENNReal.ofReal P • (AddCircle.haarAddCircle (T := P))),
        ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space),
          (F : B0223.PSpace P → SpaceC) (ε • y, θ) =
            (Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
              B0223.frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ)))) := by
      rw [← AddCircle.volume_eq_smul_haarAddCircle]
      exact hall0
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hPpos.out).ne').1 h'
  have hslice_circle : ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := P)),
      ((U F θ : Lp CVec3 2 (volume : Measure UnforcedLeray.Space)) :
          UnforcedLeray.Space → CVec3) =ᵐ[volume]
        fun y => (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) •
          ((Real.sqrt (2 * Real.pi) * ε)⁻¹ • liftA (ε • y) •
            B0223.frameC (ε • y) (b_w (B0220.chart ε (B0223.toCell P (ε • y, θ))))) := by
    filter_upwards [hU F, hall] with θ h1 h2
    filter_upwards [h1, h2] with y e1 e2
    rw [e1, e2]
  filter_upwards [UnforcedLeray.PhaseTrace.ae_comp_mk hslice_circle] with τ hτ
  obtain ⟨n, hn⟩ := toCell_snd_shift (P := P) τ
  filter_upwards [hτ] with y hy
  rw [hy]
  have htoCell : B0223.toCell P (ε • y, (τ : AddCircle P)) = (ε • y, τ + (n : ℝ) * P) :=
    Prod.ext rfl hn
  rw [htoCell, nvC_pointwise_eq hε (qPeriodic_periodize hc (w : Profile → MeridC)) κ τ y n]
  have hpref : Real.sqrt P * ε ^ (3 / 2 : ℝ) * (Real.sqrt (2 * Real.pi) * ε)⁻¹ = κ :=
    lift_prefactor_eq hc hε
  rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  rw [← hpref]
  push_cast
  ring

private theorem periodize_eq_self_of_qPeriodic {c : ℝ} {f : Profile → MeridC}
    (hper : B0220.QPeriodic c f) :
    B0220.periodize c f = f := by
  funext p
  unfold B0220.periodize
  set m : ℤ := 1 - ⌈p.2.1 / c⌉
  have hred : B0220.reduceIoc c p.2.1 = p.2.1 + (m : ℝ) * c := by
    unfold B0220.reduceIoc
    push_cast [m]
    ring
  rw [hred]
  exact qPeriodic_int hper m p

private theorem exists_periodic_null_superset (c : ℝ) {N : Set Coord} (hN : volume N = 0) :
    ∃ M' : Set Coord, N ⊆ M' ∧ MeasurableSet M' ∧ volume M' = 0 ∧
      ∀ s q η, (s, (q + c, η)) ∈ M' ↔ (s, (q, η)) ∈ M' := by
  obtain ⟨E, hNE, hEm, hE0⟩ := exists_measurable_superset_of_null hN
  let shift (m : ℤ) (p : Coord) : Coord := (p.1, p.2.1 + (m : ℝ) * c, p.2.2)
  let M' : Set Coord := ⋃ m : ℤ, shift m ⁻¹' E
  refine ⟨M', ?_, ?_, ?_, ?_⟩
  · intro p hp
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    simpa [shift] using hNE hp
  · refine MeasurableSet.iUnion fun m => hEm.preimage ?_
    exact measurable_fst.prodMk
      (((measurable_fst.comp measurable_snd).add_const _).prodMk (measurable_snd.comp measurable_snd))
  · refine measure_iUnion_null fun m => ?_
    exact (measurePreserving_shiftQ ((m : ℝ) * c)).quasiMeasurePreserving.preimage_null hE0
  · intro s q η
    simp only [M', Set.mem_iUnion, Set.mem_preimage, shift]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m + 1, ?_⟩
      have heq : q + ((m + 1 : ℤ) : ℝ) * c = q + c + (m : ℝ) * c := by push_cast; ring
      rwa [heq]
    · rintro ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩
      have heq : q + c + ((m - 1 : ℤ) : ℝ) * c = q + (m : ℝ) * c := by push_cast; ring
      rwa [heq]

private theorem volume_pos_periodize_ne_zero {c : ℝ} (hc : 0 < c)
    {f g : Profile → MeridC} (hfg : f =ᵐ[measureH c] g) :
    volume {p : Coord | 0 < p.1 ∧ B0220.periodize c f p ≠ B0220.periodize c g p} = 0 := by
  set G : Set Profile := {p | 0 < p.1 ∧ B0220.periodize c f p ≠ B0220.periodize c g p}
  have hcl : MeasurableSet (B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hnull : measureH c {p | f p ≠ g p} = 0 := ae_iff.1 hfg
  have hw : AEMeasurable weightH (volume.restrict (B0220.cell c)) :=
    measurable_weightH.aemeasurable
  have hcell : volume (G ∩ B0220.cell c) = 0 := by
    unfold measureH cellMeasure at hnull
    rw [withDensity_apply_eq_zero' hw, Measure.restrict_apply' hcl] at hnull
    refine measure_mono_null ?_ hnull
    rintro p ⟨hpG, hpc⟩
    refine ⟨⟨?_, ?_⟩, hpc⟩
    · exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpc.1 _)).ne'
    · intro heq
      apply hpG.2
      unfold B0220.periodize
      rw [B0220.reduceIoc_of_mem hc hpc.2.1]
      exact heq
  have hGcl : ∀ m : ℤ, volume ((fun p : Profile =>
      (p.1, p.2.1 + (m : ℝ) * c, p.2.2)) ⁻¹' (G ∩ B0220.cell c)) = 0 := fun m =>
    (measurePreserving_shiftQ ((m : ℝ) * c)).quasiMeasurePreserving.preimage_null hcell
  have hsub : G ⊆ ⋃ m : ℤ, (fun p : Profile =>
      (p.1, p.2.1 + (m : ℝ) * c, p.2.2)) ⁻¹' (G ∩ B0220.cell c) := by
    intro p hp
    set m : ℤ := 1 - ⌈p.2.1 / c⌉
    have hval : p.2.1 + (m : ℝ) * c = B0220.reduceIoc c p.2.1 := by
      unfold B0220.reduceIoc; push_cast [m]; ring
    have hmem : B0220.reduceIoc c p.2.1 ∈ Ioc 0 c := B0220.reduceIoc_mem hc _
    have hfix : ∀ K : Profile → MeridC,
        B0220.periodize c K (p.1, p.2.1 + (m : ℝ) * c, p.2.2) = B0220.periodize c K p := fun K => by
      unfold B0220.periodize
      rw [hval, B0220.reduceIoc_of_mem hc hmem]
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    show (p.1, p.2.1 + (m : ℝ) * c, p.2.2) ∈ G ∩ B0220.cell c
    refine ⟨⟨hp.1, ?_⟩, ⟨hp.1, ?_, trivial⟩⟩
    · show B0220.periodize c f (p.1, p.2.1 + (m : ℝ) * c, p.2.2) ≠
        B0220.periodize c g (p.1, p.2.1 + (m : ℝ) * c, p.2.2)
      rw [hfix f, hfix g]
      exact hp.2
    · show p.2.1 + (m : ℝ) * c ∈ Ioc 0 c
      rw [hval]
      exact hmem
  exact measure_mono_null hsub (measure_iUnion_null hGcl)

private theorem hasRepY_congr_ae {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {G : Yq P q} {u v : ℝ × UnforcedLeray.Space → CVec3}
    (hu : HasRepY G u) (huv : u =ᵐ[volume] v) :
    HasRepY G v := by
  have huv_prod : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure UnforcedLeray.Space)),
      u x = v x := by
    rw [← Measure.volume_eq_prod]
    exact huv
  refine ⟨hu.meas.congr huv, ?_⟩
  filter_upwards [hu.slice, Measure.ae_ae_of_ae_prod huv_prod] with τ h1 h2
  filter_upwards [h1, h2] with y hy1 hy2
  exact hy2.symm.trans hy1

private theorem nvC_sub (R : ℝ) (b₁ b₂ : CProf) (x : ℝ × UnforcedLeray.Space) :
    NvC R (b₁ - b₂) x = NvC R b₁ x - NvC R b₂ x := by
  ext i
  simp only [NvC, UnforcedLeray.Axi.Nv, UnforcedLeray.Axi.frameL_apply, reM, imM,
    UnforcedLeray.B0412.realC_apply, Pi.sub_apply, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, Complex.sub_re, Complex.sub_im, smul_eq_mul]
  push_cast
  ring

theorem teps_ae_eq_phys_response {ν c ε : ℝ} {μ : ℂ} [Fact (0 < 2 * ε * c)]
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hP1 : 2 * ε * c ≤ 1) (hγ : 0 < μ.re + 1 / 4)
    {F bε : CProf} (hbε : InHr c 2 bε) (hresp : IsResponse ν c ε μ 2 F bε)
    {F' : CProf} {M : Set Coord} {FH : HSpace c MeridC}
    (hF'per : ∀ s q η, F' (s, (q + c, η)) = F' (s, (q, η)))
    (hM0 : volume M = 0)
    (hFF' : ∀ x : Coord, 0 < x.1 → x ∉ M → F x = F' x)
    (hFH_coe : (FH : Profile → MeridC) =ᵐ[measureH c] F') :
    B0220.periodize c (Teps hν hε hc (P := 2 * ε * c) rfl μ FH : Profile → MeridC)
      =ᵐ[hMeas c 2] bε := by
  set P : ℝ := 2 * ε * c
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hPdiv : P = 2 * c / ε⁻¹ := by simp [P]; field_simp
  set κ : ℝ := Real.sqrt (c / Real.pi) * ε
  have hκ : 0 < κ := by positivity
  obtain ⟨U, hU⟩ := N01.phaseLiftExists ε P hε
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hγ
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 h1 h3 P ν hν μ hμ'
  -- 1. Represent `NvC ε⁻¹ F` by `Ff := U (liftVec (((κ⁻¹ : ℝ) : ℂ) • FH))`
  set w_F : HSpace c MeridC := ((κ⁻¹ : ℝ) : ℂ) • FH
  set Ff : Yq P 2 := U (B0223.liftVec hε hc rfl w_F)
  have hw_F_ae : (w_F : Profile → MeridC) =ᵐ[measureH c] fun p => ((κ⁻¹ : ℝ) : ℂ) • F' p := by
    filter_upwards [Lp.coeFn_smul ((κ⁻¹ : ℝ) : ℂ) FH, hFH_coe] with p hp1 hp2
    rw [hp1, Pi.smul_apply, hp2]
  have hper_F'_smul : B0220.QPeriodic c (fun p : Profile => ((κ⁻¹ : ℝ) : ℂ) • F' p) := fun p => by
    show ((κ⁻¹ : ℝ) : ℂ) • F' (p.1, p.2.1 + c, p.2.2) = _
    rw [hF'per p.1 p.2.1 p.2.2]
  have hN_F_zero : volume (M ∪ {p : Coord | 0 < p.1 ∧
      B0220.periodize c (w_F : Profile → MeridC) p ≠
        B0220.periodize c (fun q => ((κ⁻¹ : ℝ) : ℂ) • F' q) p}) = 0 :=
    measure_union_null hM0 (volume_pos_periodize_ne_zero hc hw_F_ae)
  obtain ⟨MF, hMF_sub, hMF_m, hMF_0, hMF_per⟩ := exists_periodic_null_superset c hN_F_zero
  have hax : ∀ᵐ x : ℝ × UnforcedLeray.Space, x.2 ∉ UnforcedLeray.Axi.axis :=
    Measure.quasiMeasurePreserving_snd.ae UnforcedLeray.Axi.ae_not_mem_axis
  have hFf_nvC_ae : NvC ε⁻¹ (fun p => ((κ : ℝ) : ℂ) • B0220.periodize c (w_F : Profile → MeridC) p)
      =ᵐ[volume] NvC ε⁻¹ F := by
    filter_upwards [NvCInYrHelp.chart_null_all hR hc hPdiv MF hMF_m hMF_0 hMF_per, hax]
      with x hxMF hxax
    have hpos : 0 < (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2).1 := UnforcedLeray.Axi.age_pos hR0 hxax
    have hxM : UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2 ∉ M := fun hm => hxMF (hMF_sub (Or.inl hm))
    have hxP : B0220.periodize c (w_F : Profile → MeridC) (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) =
        B0220.periodize c (fun q => ((κ⁻¹ : ℝ) : ℂ) • F' q) (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) := by
      by_contra hne
      exact hxMF (hMF_sub (Or.inr ⟨hpos, hne⟩))
    have hval : ((κ : ℝ) : ℂ) • B0220.periodize c (w_F : Profile → MeridC)
        (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) = F (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) := by
      rw [hxP, periodize_eq_self_of_qPeriodic hper_F'_smul]
      simp only [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hκ.ne',
        Complex.ofReal_one, one_smul]
      exact (hFF' _ hpos hxM).symm
    simp only [NvC, UnforcedLeray.Axi.Nv, hval]
  have hFf_rep : HasRepY Ff (NvC ε⁻¹ F) :=
    hasRepY_congr_ae (hasRepY_phaseLift_liftVec hc hε U hU w_F) hFf_nvC_ae
  -- 2. Represent `b_T := periodize c (Teps ... FH)` and show `v_T` solves `bodyOp v = lerayY Ff`
  set w_T : HSpace c MeridC := Teps hν hε hc rfl μ FH
  set b_T : CProf := B0220.periodize c (w_T : Profile → MeridC)
  set w_Ts : HSpace c MeridC := ((κ⁻¹ : ℝ) : ℂ) • w_T
  set v_T : Yq P 2 := U (B0223.liftVec hε hc rfl w_Ts)
  have hw_Ts_ae : (w_Ts : Profile → MeridC) =ᵐ[measureH c]
      fun p => ((κ⁻¹ : ℝ) : ℂ) • (w_T : Profile → MeridC) p :=
    Lp.coeFn_smul ((κ⁻¹ : ℝ) : ℂ) w_T
  obtain ⟨MT, hMT_sub, hMT_m, hMT_0, hMT_per⟩ :=
    exists_periodic_null_superset c (volume_pos_periodize_ne_zero hc hw_Ts_ae)
  have hv_T_nvC_ae : NvC ε⁻¹ (fun p => ((κ : ℝ) : ℂ) • B0220.periodize c (w_Ts : Profile → MeridC) p)
      =ᵐ[volume] NvC ε⁻¹ b_T := by
    filter_upwards [NvCInYrHelp.chart_null_all hR hc hPdiv MT hMT_m hMT_0 hMT_per, hax]
      with x hxMT hxax
    have hpos : 0 < (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2).1 := UnforcedLeray.Axi.age_pos hR0 hxax
    have hxP : B0220.periodize c (w_Ts : Profile → MeridC) (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) =
        B0220.periodize c (fun q => ((κ⁻¹ : ℝ) : ℂ) • (w_T : Profile → MeridC) q)
          (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) := by
      by_contra hne
      exact hxMT (hMT_sub ⟨hpos, hne⟩)
    have hval : ((κ : ℝ) : ℂ) • B0220.periodize c (w_Ts : Profile → MeridC)
        (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) = b_T (UnforcedLeray.Axi.chart ε⁻¹ x.1 x.2) := by
      rw [hxP]
      unfold B0220.periodize b_T
      simp only [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hκ.ne',
        Complex.ofReal_one, one_smul]
      rfl
    simp only [NvC, UnforcedLeray.Axi.Nv, hval]
  have hv_T_rep : HasRepY v_T (NvC ε⁻¹ b_T) :=
    hasRepY_congr_ae (hasRepY_phaseLift_liftVec hc hε U hU w_Ts) hv_T_nvC_ae
  have hv_T_eq_Rm : v_T = Rm (lerayY P 2 h1 ENNReal.ofNat_ne_top Ff) := by
    have hw_Ts_eq : w_Ts = B0223.RepsVec hν hε hc rfl μ (PepsC ε c w_F) := by
      change ((κ⁻¹ : ℝ) : ℂ) • Teps hν hε hc rfl μ FH = Teps hν hε hc rfl μ w_F
      exact (map_smul (Teps hν hε hc rfl μ) ((κ⁻¹ : ℝ) : ℂ) FH).symm
    change U (B0223.liftVec hε hc rfl w_Ts) = _
    rw [hw_Ts_eq,
      phaseLift_liftVec_RepsVec hν hε hc rfl hγ hU Rm ENNReal.ofNat_ne_top hRm (PepsC ε c w_F),
      phaseLift_liftVec_PepsC hε hc rfl hU w_F]
  obtain ⟨vD, hvD_coe, hvD_eq⟩ :=
    N01.bodyResolvent_bodyOp hP1 hν hγ Rm ENNReal.ofNat_ne_top hRm
      (lerayY P 2 h1 ENNReal.ofNat_ne_top Ff)
  -- 3. Represent `NvC ε⁻¹ bε` in `Yq P 2` and show it solves the same `bodyOp` equation
  have hbε_yr : IsInYr P 2 (NvC ε⁻¹ bε) := nvCInYr_proof c ε 2 bε hc hε two_pos hbε
  obtain ⟨Wq, hWq_rep, -⟩ :=
    exists_hasRepY_q P 2 two_pos (q := 2) ENNReal.ofNat_ne_top (by norm_num) (NvC ε⁻¹ bε) hbε_yr
  obtain ⟨a, ha, hpa⟩ := hresp.lapl
  obtain ⟨b, hb, hpb⟩ := hresp.drift
  obtain ⟨A, hA_rep, -⟩ :=
    exists_hasRepY_q P 2 two_pos (q := 2) ENNReal.ofNat_ne_top (by norm_num) a ha
  obtain ⟨B, hB_rep, -⟩ :=
    exists_hasRepY_q P 2 two_pos (q := 2) ENNReal.ofNat_ne_top (by norm_num) b hb
  have hD_W : Wq ∈ D P ν 2 :=
    mem_D.2 ⟨⟨A, (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => isPhaseTest_nuLapT hΦ ν) hWq_rep hA_rep).1 hpa⟩,
      ⟨B, (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => hΦ.driftT) hWq_rep hB_rep).1 hpb⟩⟩
  have hs_W : Wq ∈ Ysigma P 2 := fun φ hφ => by
    rw [phasePair_eq_pairF_of_hasRepY Wq _ hWq_rep hφ.gradT]
    exact hresp.solenoidal φ hφ
  have hpair_W : ∀ Φ, IsSolTest P Φ →
      phasePair P 2 Φ (bodyOp P ν 2 μ ⟨Wq, hD_W⟩) = phasePair P 2 Φ Ff := by
    intro Φ hΦ
    have hT : IsPhaseTest P (fun x => L0T ν Φ x + μ • Φ x) :=
      (isPhaseTest_L0T hΦ.1 ν).add (hΦ.1.const_smul μ)
    rw [phasePair_bodyOp μ ⟨Wq, hD_W⟩ hΦ.1,
      phasePair_eq_pairF_of_hasRepY Wq _ hWq_rep hT,
      phasePair_eq_pairF_of_hasRepY Ff _ hFf_rep hΦ.1]
    exact hresp.equation Φ hΦ
  have hbody_W : bodyOp P ν 2 μ ⟨Wq, hD_W⟩ = lerayY P 2 h1 ENNReal.ofNat_ne_top Ff :=
    (bodyOp_eq_leray_iff lerayPairSol solSeparation h1 ENNReal.ofNat_ne_top μ ⟨Wq, hD_W⟩ hs_W Ff).1
      hpair_W
  -- 4. Injectivity of `bodyOp` at `q = 2` yields `Wq = v_T`, hence `b_T =ᵐ[hMeas c 2] bε`
  have hinj := bodyOp_injective_of_bound commonBodyGraphBound 2 h1 h3 P hP1 ν hν μ hμ'
  have hWv : (⟨Wq, hD_W⟩ : D P ν 2) = vD := hinj (hbody_W.trans hvD_eq.symm)
  have hWq_eq_vT : Wq = v_T := by
    calc Wq = ((⟨Wq, hD_W⟩ : D P ν 2) : Yq P 2) := rfl
      _ = (vD : Yq P 2) := congrArg Subtype.val hWv
      _ = Rm (lerayY P 2 h1 ENNReal.ofNat_ne_top Ff) := hvD_coe
      _ = v_T := hv_T_eq_Rm.symm
  rw [← hWq_eq_vT] at hv_T_rep
  have hslice_zero : ∀ᵐ τ : ℝ, ∫⁻ y : UnforcedLeray.Space,
      ‖NvC ε⁻¹ (bε - b_T) (τ, y)‖ₑ ^ (2 : ℝ) = 0 := by
    filter_upwards [hWq_rep.slice, hv_T_rep.slice] with τ h1s h2s
    have hy0 : ∀ᵐ y : UnforcedLeray.Space, ‖NvC ε⁻¹ (bε - b_T) (τ, y)‖ₑ ^ (2 : ℝ) = 0 := by
      filter_upwards [h1s, h2s] with y hy1 hy2
      rw [nvC_sub, hy1, hy2, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (lintegral_congr_ae hy0).trans lintegral_zero
  have hpnorm_zero : phaseLpNorm P 2 (NvC ε⁻¹ (bε - b_T)) = 0 := by
    unfold phaseLpNorm
    have h0 : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space,
        ‖NvC ε⁻¹ (bε - b_T) (t, y)‖ₑ ^ (2 : ℝ) = 0 :=
      (lintegral_congr_ae (ae_restrict_of_ae hslice_zero)).trans lintegral_zero
    rw [h0, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  have hb_T_hr : InHr c 2 b_T := inHr_periodize hc w_T
  have hper_diff : QPeriodic c (bε - b_T) := by
    filter_upwards [hbε.periodic, hb_T_hr.periodic] with x hx1 hx2
    simp [hx1, hx2]
  have hmeas_diff : AEStronglyMeasurable (bε - b_T) (hMeas c 2) := hbε.meas.sub hb_T_hr.meas
  have hnv_norm := phaseLpNorm_NvC hc two_pos hε (bε - b_T) hper_diff hmeas_diff
  change phaseLpNorm P 2 (NvC ε⁻¹ (bε - b_T)) = _ at hnv_norm
  rw [hpnorm_zero] at hnv_norm
  have hfac_ne : ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / (2 : ℝ))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (mul_pos Real.pi_pos (sq_pos_of_pos hR)) _)).ne'
  have hhnorm_zero : hNorm c 2 (bε - b_T) = 0 := by
    rcases mul_eq_zero.1 hnv_norm.symm with h | h
    · exact absurd h hfac_ne
    · exact h
  have heLp_zero : eLpNorm (bε - b_T) 2 (hMeas c 2) = 0 := by
    have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    unfold hNorm at hhnorm_zero
    rwa [h2] at hhnorm_zero
  have hdiff_ae : bε - b_T =ᵐ[hMeas c 2] 0 :=
    (eLpNorm_eq_zero_iff hmeas_diff (by norm_num)).1 heLp_zero
  filter_upwards [hdiff_ae] with p hp
  exact (sub_eq_zero.1 hp).symm

end UnforcedLeray.Short.IIb.CompactFreeRateSub
