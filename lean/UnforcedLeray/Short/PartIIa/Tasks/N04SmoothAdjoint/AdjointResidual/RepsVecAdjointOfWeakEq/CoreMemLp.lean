import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_Org
import UnforcedLeray.Units.B0220.Frame

/-!
# Core tests are square integrable (`MeridCoreTestMemLp`)

Source of record: `the November 2 reference manuscript`,
lines 3290-3295 (the `L²` identities for the lifts `U = a b`, `‖U‖² = 2πε² ∫ s^{-3/2}|b|²`).

Proof outline. A core test `u` is split into real and imaginary meridional parts. Each part is
modified off the half space `{s > 0}` (set to zero there), which makes it measurable without
changing its lift on the physical space. The `L²` identity `lintegral_fieldU` then bounds the
weighted integral over the cell by the physical `L²` norm of the lift, which is finite because the
lift is `C²`, vanishes for large `|x|`, and is bounded on one `τ`-period.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220
open UnforcedLeray.B0223
open UnforcedLeray.Short.PartIIIb.NearInst.Body

/-- Pointwise splitting of the squared norm of a complex meridional vector into real and imaginary
parts. -/
theorem enorm_sq_split_merid (z : MeridC) :
    ‖z‖ₑ ^ 2 = ‖merReL z‖ₑ ^ 2 + ‖merReL ((-Complex.I) • z)‖ₑ ^ 2 := by
  have hz : ‖z‖ ^ 2 = ‖merReL z‖ ^ 2 + ‖merReL ((-Complex.I) • z)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [merReL, merReLin, Complex.sq_norm, Complex.normSq_apply]
    ring
  have h1 : ∀ w : MeridC, ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := fun w => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h1m : ∀ w : Merid, ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := fun w => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h1 z, hz, ENNReal.ofReal_add (by positivity) (by positivity), h1m (merReL z),
    h1m (merReL ((-Complex.I) • z))]

/-- The physical lift of a profile is unchanged by modifying the profile off `{s > 0}`. -/
theorem fieldU_congr_of_pos {ε : ℝ} {f g : Profile → Merid}
    (h : ∀ p : Profile, 0 < p.1 → f p = g p) : fieldU ε f = fieldU ε g := by
  funext y
  by_cases hr : radius y.1 = 0
  · simp [fieldU, liftA_eq_zero hr]
  · have hpos : 0 < radius y.1 := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
    have hs : 0 < (chart ε y).1 := by
      show 0 < ageS y.1
      unfold ageS
      exact inv_pos.2 (pow_pos hpos 2)
    simp only [fieldU, h _ hs]

/-- The `L²` norm of a real meridional profile with an `L²`-bounded lift is finite on the cell. -/
theorem lintegral_merid_lt_top {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {b : Profile → Merid} (hb : Measurable b) (hper : QPeriodic c b)
    (hcore : ∃ V : Space × ℝ → Space, IsCoreTestFieldVec ε c V ∧
      ∀ y : Space × ℝ, radius y.1 ≠ 0 → V y = fieldU ε b y) :
    ∫⁻ p, ‖b p‖ₑ ^ 2 ∂measureH c < ⊤ := by
  obtain ⟨V, hV, hVeq⟩ := hcore
  obtain ⟨R, hR⟩ := hV.bounded
  have hVcont : Continuous V := by
    have h : Continuous fun y : Space × ℝ => (WithLp.toLp 2 (fun j : Fin 3 => V y j) : Space) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => (hV.smooth j).continuous)
    simpa using h
  have hVle : ∀ y, ‖fieldU ε b y‖ ≤ ‖V y‖ := by
    intro y
    by_cases hr : radius y.1 = 0
    · simp [fieldU, liftA_eq_zero hr]
    · rw [hVeq y hr]
  set P : ℝ := 2 * ε * c with hP
  set K : Set (Space × ℝ) := Metric.closedBall (0 : Space) R ×ˢ Icc 0 P with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hVcont.continuousOn
  set k : ℝ≥0∞ := ENNReal.ofReal |C| ^ 2 with hk
  have hkt : k < ⊤ := ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hD : MeasurableSet (physDomain ε c) := MeasurableSet.univ.prod measurableSet_Ioc
  have hpt : ∀ᵐ y ∂(physMeasure ε c), ‖fieldU ε b y‖ₑ ^ 2 ≤ K.indicator (fun _ => k) y := by
    rw [physMeasure]
    filter_upwards [ae_restrict_mem hD] with y hy
    obtain ⟨-, hy2⟩ := hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
      have hle : ‖fieldU ε b y‖ₑ ≤ ENNReal.ofReal |C| := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((hVle y).trans ((hC y hyK).trans (le_abs_self C)))
      rw [hk]
      exact pow_le_pow_left₀ (by positivity) hle 2
    · have hx : R < ‖y.1‖ := by
        by_contra hcon
        exact hyK ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.1 hcon,
          ⟨hy2.1.le, hy2.2⟩⟩
      have h0 : fieldU ε b y = 0 := by
        have := hVle y
        rw [hR y hx, norm_zero] at this
        exact norm_le_zero_iff.1 this
      rw [h0, Set.indicator_of_notMem hyK]
      simp
  have hfin : ∫⁻ y, ‖fieldU ε b y‖ₑ ^ 2 ∂(physMeasure ε c) < ⊤ := by
    calc ∫⁻ y, ‖fieldU ε b y‖ₑ ^ 2 ∂(physMeasure ε c)
        ≤ ∫⁻ y, K.indicator (fun _ => k) y ∂(physMeasure ε c) := lintegral_mono_ae hpt
      _ = k * (physMeasure ε c) K := lintegral_indicator_const hK.isClosed.measurableSet k
      _ < ⊤ := by
        refine ENNReal.mul_lt_top hkt ?_
        rw [physMeasure]
        exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top
  have hid := lintegral_fieldU hε hc b hb hper
  have hC0 : ENNReal.ofReal (2 * Real.pi * ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC1 : ENNReal.ofReal (2 * Real.pi * ε ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hcellfin : ∫⁻ p in cell c, weightH p * ‖b p‖ₑ ^ 2 < ⊤ := by
    have h2 : ENNReal.ofReal (2 * Real.pi * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖b p‖ₑ ^ 2 < ⊤ := by
      rw [← hid]; exact hfin
    exact ENNReal.lt_top_of_mul_ne_top_right h2.ne hC1
  have hw : Measurable weightH :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hg : Measurable (fun p : Profile => ‖b p‖ₑ ^ 2) := hb.enorm.pow_const 2
  rw [measureH, lintegral_withDensity_eq_lintegral_mul _ hw hg]
  exact hcellfin

/-- Core tests are square integrable (`MeridCoreTestMemLp`). -/
theorem meridCoreTestMemLp : MeridCoreTestMemLp := by
  intro c ε hc hε u hu
  classical
  set U : Set Profile := {p : Profile | 0 < p.1} with hUdef
  have hUm : MeasurableSet U := measurableSet_lt measurable_const measurable_fst
  set u' : Profile → MeridC := U.piecewise u 0 with hu'def
  have hucont : ContinuousOn u U := hu.smooth.continuousOn
  have hu'm : Measurable u' :=
    hucont.measurable_piecewise continuousOn_const hUm
  have hu'eq : ∀ p : Profile, 0 < p.1 → u' p = u p := fun p hp =>
    Set.piecewise_eq_of_mem _ _ _ (show p ∈ U from hp)
  have hu'per : ∀ p : Profile, u' (p.1, p.2.1 + c, p.2.2) = u' p := by
    intro p
    by_cases hp : 0 < p.1
    · rw [hu'eq (p.1, p.2.1 + c, p.2.2) hp, hu'eq p hp]
      exact hu.periodic p
    · have hp' : ¬ (0 < (p.1, p.2.1 + c, p.2.2).1) := hp
      simp [u', Set.piecewise, U, hp, hp']
  -- real and imaginary parts of the modified profile
  set b1 : Profile → Merid := fun p => merReL (u' p) with hb1def
  set b2 : Profile → Merid := fun p => merReL ((-Complex.I) • u' p) with hb2def
  have hb1m : Measurable b1 := merReL.continuous.measurable.comp hu'm
  have hb2m : Measurable b2 :=
    merReL.continuous.measurable.comp (hu'm.const_smul (-Complex.I))
  have hb1per : QPeriodic c b1 := fun p => by
    show merReL (u' _) = merReL (u' p)
    rw [hu'per p]
  have hb2per : QPeriodic c b2 := fun p => by
    show merReL ((-Complex.I) • u' _) = merReL ((-Complex.I) • u' p)
    rw [hu'per p]
  have hf1 : fieldU ε b1 = fieldU ε (reMerid u) := by
    apply fieldU_congr_of_pos
    intro p hp
    show merReL (u' p) = merReL (u p)
    rw [hu'eq p hp]
  have hf2 : fieldU ε b2 = fieldU ε (imMerid u) := by
    apply fieldU_congr_of_pos
    intro p hp
    show merReL ((-Complex.I) • u' p) = merReL ((-Complex.I) • u p)
    rw [hu'eq p hp]
  have hcore1 : ∃ V : Space × ℝ → Space, IsCoreTestFieldVec ε c V ∧
      ∀ y : Space × ℝ, radius y.1 ≠ 0 → V y = fieldU ε b1 y := by
    rw [hf1]; exact hu.re_core
  have hcore2 : ∃ V : Space × ℝ → Space, IsCoreTestFieldVec ε c V ∧
      ∀ y : Space × ℝ, radius y.1 ≠ 0 → V y = fieldU ε b2 y := by
    rw [hf2]; exact hu.im_core
  have hint1 := lintegral_merid_lt_top hε hc hb1m hb1per hcore1
  have hint2 := lintegral_merid_lt_top hε hc hb2m hb2per hcore2
  -- the modified profile lies in `L²(measureH c)`
  have hsplit : ∫⁻ p, ‖u' p‖ₑ ^ 2 ∂measureH c < ⊤ := by
    have hpt : ∀ p : Profile, ‖u' p‖ₑ ^ 2 = ‖b1 p‖ₑ ^ 2 + ‖b2 p‖ₑ ^ 2 :=
      fun p => enorm_sq_split_merid (u' p)
    simp_rw [hpt]
    rw [lintegral_add_left (hb1m.enorm.pow_const 2)]
    exact ENNReal.add_lt_top.2 ⟨hint1, hint2⟩
  -- the modified profile is `L²`
  have hMem' : MemLp u' 2 (measureH c) := by
    refine ⟨hu'm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simpa using hsplit
  -- `u = u'` almost everywhere for `measureH c`
  have hcellM : MeasurableSet (cell c) := measurableSet_cell c
  have hae : ∀ᵐ p ∂(measureH c), p ∈ U := by
    have hac : measureH c ≪ cellMeasure c := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (ae_restrict_mem hcellM)] with p hp
    exact hp.1
  have hae' : u' =ᵐ[measureH c] u := by
    filter_upwards [hae] with p hp
    exact Set.piecewise_eq_of_mem _ _ _ hp
  exact hMem'.ae_eq hae'

end UnforcedLeray.Short.PartIIa
