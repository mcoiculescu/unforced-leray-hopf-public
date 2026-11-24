import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntSliceL2.Contract

/-!
# `PartII-a:N01/9/1/2/4/6/3`: `HeatIntSliceL2`

Source `the November 2 reference manuscript`,
lines 1650-1658, 1684-1689, 3379-3383.  For `s ∈ [s₁,s₂]` the causal heat integral of a smooth
force has uniformly bounded `L²(cell)` slices.

Proof: the integrand is supported in `σ > a/2` (`a` the lower support of `F`), the weight is bounded
there; Cauchy–Schwarz in `σ` over the finite interval, Tonelli, and the `L²(cell)` contraction of
the positive-time plane heat (`HeatIntSliceL2Aux.planeHeat_cell_lintegral_contract_E`) give a bound
by `B² · s₂² · (r² · vol T')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.Short.PartIIa.N01.HeatIntSliceL2Aux

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The Gaussian slice integral of the force at a fixed time `σ`, for the time `s`. -/
def phiSlice (ν s : ℝ) (F : Profile → MeridC) (σ : ℝ) (x : ℝ × ℝ) : MeridC :=
  ∫ y : Euc 2, gaussKernel 2 (ν * (s - σ)) y •
    (σ⁻¹ • F (σ, x - UnforcedLeray.B0224.planeι y))

theorem periodize_force_eq {c : ℝ} {F : Profile → MeridC}
    (hFper : ∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) (σ : ℝ) (z : ℝ × ℝ) :
    UnforcedLeray.B0220.periodize c (fun q : Profile => (q.1)⁻¹ • F q) (σ, z)
      = σ⁻¹ • F (σ, z) := by
  have hQ : UnforcedLeray.B0220.QPeriodic c (fun q : Profile => (q.1)⁻¹ • F q) := by
    intro p
    show (p.1)⁻¹ • F (p.1, p.2.1 + c, p.2.2) = (p.1)⁻¹ • F p
    rw [hFper p]
  exact congrFun (UnforcedLeray.B0220.periodize_of_periodic _ hQ) (σ, z)

theorem planeHeat_zero_fun (θ : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat θ (fun _ : ℝ × ℝ => (0 : MeridC)) x = 0 := by
  by_cases h : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos h]
    simp
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 h)]

theorem planeHeat_eq_phiSlice {ν s : ℝ} {F : Profile → MeridC} {σ : ℝ} (hθ : 0 < ν * (s - σ))
    (x : ℝ × ℝ) :
    UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z : ℝ × ℝ => σ⁻¹ • F (σ, z)) x = phiSlice ν s F σ x := by
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rfl

theorem force_bound {c : ℝ} (hc : 0 < c) {F : Profile → MeridC} (hFc : Continuous F)
    (hFper : ∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) {a b R : ℝ}
    (hsupp : ∀ p : Profile, (p.1 < a ∨ b < p.1 ∨ R < |p.2.2|) → F p = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Profile, ‖F p‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    : IsCompact (Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R))).exists_bound_of_continuousOn
    hFc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun p => ?_⟩
  by_cases hp : p.1 < a ∨ b < p.1 ∨ R < |p.2.2|
  · rw [hsupp p hp, norm_zero]
    exact le_max_right _ _
  · push_neg at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hr := UnforcedLeray.B0220.reduceIoc_mem hc p.2.1
    have hmem : (p.1, UnforcedLeray.B0220.reduceIoc c p.2.1, p.2.2) ∈
        Icc a b ×ˢ (Icc 0 c ×ˢ Icc (-R) R) := by
      refine ⟨⟨h1, h2⟩, ⟨hr.1.le, hr.2⟩, ?_⟩
      exact abs_le.1 h3
    have e : F p = F (p.1, UnforcedLeray.B0220.reduceIoc c p.2.1, p.2.2) :=
      (UnforcedLeray.B0220.periodic_reduceIoc_eq F hFper p.1 p.2.1 p.2.2).symm
    rw [e]
    exact (hM _ hmem).trans (le_max_left _ _)

theorem weight_bound (μ : ℂ) {α : ℝ} (hα : 0 < α) :
    ∃ B : ℝ, ∀ t : ℝ, t ∈ Icc α 1 → ‖((t : ℝ) : ℂ) ^ μ‖ ≤ B := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ μ.re) (Icc α 1) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hα ht.1)))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨B, fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le hα ht.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
  have h := hB t ht
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _)] at h

theorem lintegral_sq_le_mul {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f : α → ℝ≥0∞) (hf : AEMeasurable f ν) :
    (∫⁻ a, f a ∂ν) ^ 2 ≤ ν Set.univ * ∫⁻ a, f a ^ 2 ∂ν := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (aemeasurable_const (b := (1 : ℝ≥0∞))) hf
  simp only [Pi.mul_apply, one_mul, one_pow, lintegral_one, ENNReal.rpow_two] at H
  have key : ∀ A : ℝ≥0∞, (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
    intro A
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, f a ∂ν) ^ 2 ≤ (ν Set.univ ^ (1 / 2 : ℝ) * (∫⁻ a, f a ^ (2 : ℕ) ∂ν) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = ν Set.univ * ∫⁻ a, f a ^ (2 : ℕ) ∂ν := by
        rw [mul_pow, key, key]


theorem measurable_gaussKernel_joint :
    Measurable (fun q : ℝ × Euc 2 => gaussKernel 2 q.1 q.2) := by
  unfold gaussKernel
  first
  | fun_prop
  | measurability

theorem measurable_phiSlice (ν s : ℝ) {F : Profile → MeridC} (hFc : Continuous F) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => phiSlice ν s F p.2 p.1) := by
  have hι : Measurable (UnforcedLeray.B0224.planeι : Euc 2 → ℝ × ℝ) :=
    UnforcedLeray.B0224.continuous_planeι.measurable
  have h1 : Measurable (fun q : ((ℝ × ℝ) × ℝ) × Euc 2 =>
      gaussKernel 2 (ν * (s - q.1.2)) q.2) :=
    measurable_gaussKernel_joint.comp
      ((measurable_const.mul (measurable_const.sub (measurable_snd.comp measurable_fst))).prodMk
        measurable_snd)
  have h2' : Measurable (fun q : ((ℝ × ℝ) × ℝ) × Euc 2 => q.1.2⁻¹) :=
    measurable_inv.comp (measurable_snd.comp measurable_fst)
  have h3 : Measurable (fun q : ((ℝ × ℝ) × ℝ) × Euc 2 =>
      F (q.1.2, q.1.1 - UnforcedLeray.B0224.planeι q.2)) :=
    hFc.measurable.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).sub (hι.comp measurable_snd)))
  have h4 : Measurable (fun q : ((ℝ × ℝ) × ℝ) × Euc 2 =>
      q.1.2⁻¹ • F (q.1.2, q.1.1 - UnforcedLeray.B0224.planeι q.2)) :=
    Measurable.smul h2' h3
  have hm : Measurable (fun q : ((ℝ × ℝ) × ℝ) × Euc 2 =>
      gaussKernel 2 (ν * (s - q.1.2)) q.2 •
        (q.1.2⁻¹ • F (q.1.2, q.1.1 - UnforcedLeray.B0224.planeι q.2))) :=
    Measurable.smul h1 h4
  have hsm := hm.stronglyMeasurable
  have key := MeasureTheory.StronglyMeasurable.integral_prod_right (ν := (volume : Measure (Euc 2)))
    (f := fun (p : (ℝ × ℝ) × ℝ) (y : Euc 2) => gaussKernel 2 (ν * (s - p.2)) y •
        (p.2⁻¹ • F (p.2, p.1 - UnforcedLeray.B0224.planeι y))) hsm
  exact key.measurable

theorem smoothHeatInt_eq_setIntegral {c ν : ℝ} {μ : ℂ} {F : Profile → MeridC}
    (hFper : ∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) {a s : ℝ} (ha : 0 < a)
    (hzero : ∀ σ : ℝ, ∀ z : ℝ × ℝ, σ < a → F (σ, z) = 0) (hs : 0 < s) (hν : 0 < ν)
    (x : ℝ × ℝ) :
    UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F (s, x)
      = ∫ σ in Ioo (a / 2) s, ((σ / s : ℝ) : ℂ) ^ μ • phiSlice ν s F σ x := by
  unfold UnforcedLeray.Short.PartIIa.N01.smoothHeatInt
  show (∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ •
      UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c
          (fun q : Profile => (q.1)⁻¹ • F q) (σ, z)) x) = _
  rw [intervalIntegral.integral_of_le hs.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hsub : Ioo (a / 2) s ⊆ Ioo 0 s := fun σ hσ => ⟨by linarith [hσ.1, half_pos ha], hσ.2⟩
  have hvan : ∀ σ ∈ Ioo 0 s \ Ioo (a / 2) s,
      ((σ / s : ℝ) : ℂ) ^ μ •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c
            (fun q : Profile => (q.1)⁻¹ • F q) (σ, z)) x = 0 := by
    rintro σ ⟨⟨hσ0, hσs⟩, hnot⟩
    have hσa : σ ≤ a / 2 := by
      by_contra h
      push_neg at h
      exact hnot ⟨h, hσs⟩
    have hG0 : (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c
        (fun q : Profile => (q.1)⁻¹ • F q) (σ, z)) = fun _ => 0 := by
      funext z
      rw [periodize_force_eq hFper σ z, hzero σ z (by linarith)]
      simp
    rw [hG0, planeHeat_zero_fun, smul_zero]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hsub hvan]
  refine setIntegral_congr_fun measurableSet_Ioo ?_
  intro σ hσ
  have hθ : 0 < ν * (s - σ) := mul_pos hν (by linarith [hσ.2])
  have hGσ : (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c
      (fun q : Profile => (q.1)⁻¹ • F q) (σ, z)) = fun z : ℝ × ℝ => σ⁻¹ • F (σ, z) :=
    funext (periodize_force_eq hFper σ)
  dsimp only
  rw [hGσ, planeHeat_eq_phiSlice hθ x]

theorem slice_L2_bound {c ν s σ a R r : ℝ} {F : Profile → MeridC} (hc : 0 < c) (hν : 0 < ν)
    (hFc : Continuous F) (hFper : ∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p)
    (hσ : 0 < σ) (hσs : σ < s)
    (hGb : ∀ z : ℝ × ℝ, ‖σ⁻¹ • F (σ, z)‖ ≤ r)
    (hR : ∀ z : ℝ × ℝ, R < |z.2| → F (σ, z) = 0) (hr : 0 ≤ r) :
    ∫⁻ x in UnforcedLeray.B0579.cell c, ‖phiSlice ν s F σ x‖ₑ ^ 2 ≤
      ENNReal.ofReal r ^ 2 * volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) := by
  have hθ : 0 < ν * (s - σ) := mul_pos hν (by linarith)
  set G : ℝ × ℝ → MeridC := fun z => σ⁻¹ • F (σ, z) with hGdef
  have hGc : Continuous G := by
    have hF' : Continuous fun z : ℝ × ℝ => F (σ, z) :=
      hFc.comp (continuous_const.prodMk continuous_id)
    exact hF'.const_smul σ⁻¹
  have hGp : ∀ z : ℝ × ℝ, G (z.1 + c, z.2) = G z := by
    intro z
    exact congrArg (fun v => σ⁻¹ • v) (hFper (σ, z))
  have hT : MeasurableSet (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hTfin : volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) < ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hpt : ∀ x ∈ UnforcedLeray.B0579.cell c,
      ‖G x‖ₑ ^ 2 ≤
        (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (fun _ => ENNReal.ofReal r ^ 2) x := by
    intro x hx
    by_cases hxT : x ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
    · rw [Set.indicator_of_mem hxT]
      have h1 : ‖G x‖ₑ ≤ ENNReal.ofReal r := by
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hGb x)
      gcongr
    · rw [Set.indicator_of_notMem hxT]
      have hxc : x.1 ∈ Ico (-(c / 2)) (c / 2) :=
        (show x ∈ Ico (-(c / 2)) (c / 2) ×ˢ univ from hx).1
      have hxR : R < |x.2| := by
        by_contra h
        push_neg at h
        exact hxT ⟨⟨hxc.1, hxc.2.le⟩, abs_le.1 h⟩
      have hG0 : G x = 0 := by
        show σ⁻¹ • F (σ, x) = 0
        rw [hR x hxR, smul_zero]
      rw [hG0]
      simp
  calc ∫⁻ x in UnforcedLeray.B0579.cell c, ‖phiSlice ν s F σ x‖ₑ ^ 2
      = ∫⁻ x in UnforcedLeray.B0579.cell c, ‖UnforcedLeray.B0224.planeHeat (ν * (s - σ)) G x‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards with x
        rw [planeHeat_eq_phiSlice hθ x]
    _ ≤ ∫⁻ x in UnforcedLeray.B0579.cell c, ‖G x‖ₑ ^ 2 :=
        planeHeat_cell_lintegral_contract_E hc hθ hGc hGp
    _ ≤ ∫⁻ x in UnforcedLeray.B0579.cell c,
          (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (fun _ => ENNReal.ofReal r ^ 2) x :=
        setLIntegral_mono' (UnforcedLeray.B0579.measurableSet_cell c) hpt
    _ ≤ ∫⁻ x, (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R).indicator (fun _ => ENNReal.ofReal r ^ 2) x :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal r ^ 2 * volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
        lintegral_indicator_const hT _

end UnforcedLeray.Short.PartIIa.N01.HeatIntSliceL2Aux

open UnforcedLeray.Short.PartIIa.N01.HeatIntSliceL2Aux

theorem heatIntSliceL2 : UnforcedLeray.Short.PartIIa.N01.HeatIntSliceL2 := by
  intro c ν hc hν μ F hF s₁ s₂ hs₁ hs₁₂
  unfold UnforcedLeray.Short.PartIIa.N01.IsSmoothForceFn at hF
  obtain ⟨hFcd, hFper, a, b, R, ha, hsupp⟩ := hF
  have hFc : Continuous F := hFcd.continuous
  have hzero : ∀ σ : ℝ, ∀ z : ℝ × ℝ, σ < a → F (σ, z) = 0 :=
    fun σ z h => hsupp (σ, z) (Or.inl h)
  obtain ⟨M, hM0, hM⟩ := force_bound hc hFc hFper hsupp
  have hs₂ : 0 < s₂ := lt_trans hs₁ hs₁₂
  obtain ⟨B, hB⟩ := weight_bound μ (α := a / 2 / s₂) (div_pos (half_pos ha) hs₂)
  have hr0 : 0 ≤ 2 / a * M := mul_nonneg (div_nonneg two_pos.le ha.le) hM0
  refine ⟨ENNReal.ofReal B ^ 2 *
      (ENNReal.ofReal s₂ * ((ENNReal.ofReal (2 / a * M) ^ 2 *
        volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) * ENNReal.ofReal s₂)), ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top))
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  intro s hs i
  obtain ⟨hs1, hs2⟩ := hs
  have hspos : 0 < s := lt_of_lt_of_le hs₁ hs1
  have hΦm := measurable_phiSlice ν s hFc
  -- weight bound on the σ-range
  have hwb : ∀ σ ∈ Ioo (a / 2) s, ‖((σ / s : ℝ) : ℂ) ^ μ‖ₑ ≤ ENNReal.ofReal B := by
    intro σ hσ
    have hσ0 : 0 ≤ σ := (half_pos ha).trans hσ.1 |>.le
    have hmem : σ / s ∈ Icc (a / 2 / s₂) 1 := by
      constructor
      · rw [div_le_div_iff₀ hs₂ hspos]
        have h1 : a / 2 * s ≤ σ * s := mul_le_mul_of_nonneg_right hσ.1.le hspos.le
        have h2 : σ * s ≤ σ * s₂ := mul_le_mul_of_nonneg_left hs2 hσ0
        linarith
      · rw [div_le_one hspos]
        exact hσ.2.le
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hB _ hmem)
  -- representation of the heat integral as a σ-integral over (a/2, s)
  have hnorm : ∀ x : ℝ × ℝ, ‖UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F (s, x)‖ₑ ≤
      ENNReal.ofReal B * ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ := by
    intro x
    rw [smoothHeatInt_eq_setIntegral hFper ha hzero hspos hν x]
    calc ‖∫ σ in Ioo (a / 2) s, ((σ / s : ℝ) : ℂ) ^ μ • phiSlice ν s F σ x‖ₑ
        ≤ ∫⁻ σ in Ioo (a / 2) s, ‖((σ / s : ℝ) : ℂ) ^ μ • phiSlice ν s F σ x‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ σ in Ioo (a / 2) s, ‖((σ / s : ℝ) : ℂ) ^ μ‖ₑ * ‖phiSlice ν s F σ x‖ₑ :=
          lintegral_congr fun σ => enorm_smul _ _
      _ ≤ ∫⁻ σ in Ioo (a / 2) s, ENNReal.ofReal B * ‖phiSlice ν s F σ x‖ₑ :=
          setLIntegral_mono' measurableSet_Ioo
            (fun σ hσ => mul_le_mul_of_nonneg_right (hwb σ hσ) zero_le)
      _ = ENNReal.ofReal B * ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Cauchy–Schwarz on the σ-interval
  have hholder : ∀ x : ℝ × ℝ, (∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ) ^ 2 ≤
      volume (Ioo (a / 2) s) * ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ ^ 2 := by
    intro x
    have hmeasx : Measurable (fun σ : ℝ => ((x, σ) : (ℝ × ℝ) × ℝ)) :=
      measurable_const.prodMk measurable_id
    have hm : AEMeasurable (fun σ => ‖phiSlice ν s F σ x‖ₑ)
        (volume.restrict (Ioo (a / 2) s)) :=
      ((hΦm.comp hmeasx).enorm).aemeasurable
    have := lintegral_sq_le_mul (volume.restrict (Ioo (a / 2) s)) _ hm
    rwa [Measure.restrict_apply_univ] at this
  have hsq : ∀ x : ℝ × ℝ, ‖UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F (s, x)‖ₑ ^ 2 ≤
      ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) *
        ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ ^ 2) := by
    intro x
    calc ‖UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F (s, x)‖ₑ ^ 2
        ≤ (ENNReal.ofReal B * ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ) ^ 2 := by
          gcongr
          exact hnorm x
      _ = ENNReal.ofReal B ^ 2 * (∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ) ^ 2 :=
          mul_pow _ _ _
      _ ≤ ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) *
          ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ ^ 2) := by
          gcongr
          exact hholder x
  -- integrate over the cell, Tonelli
  have hVle : volume (Ioo (a / 2) s) ≤ ENNReal.ofReal s₂ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hVtop : volume (Ioo (a / 2) s) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hc2 : ENNReal.ofReal B ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hswap : ∫⁻ x in UnforcedLeray.B0579.cell c, ∫⁻ σ in Ioo (a / 2) s,
      ‖phiSlice ν s F σ x‖ₑ ^ 2 =
      ∫⁻ σ in Ioo (a / 2) s, ∫⁻ x in UnforcedLeray.B0579.cell c, ‖phiSlice ν s F σ x‖ₑ ^ 2 := by
    refine lintegral_lintegral_swap (f := fun x σ => ‖phiSlice ν s F σ x‖ₑ ^ 2) ?_
    exact (hΦm.enorm.pow_const 2).aemeasurable
  have hcellJ : ∫⁻ σ in Ioo (a / 2) s, ∫⁻ x in UnforcedLeray.B0579.cell c,
      ‖phiSlice ν s F σ x‖ₑ ^ 2 ≤
      ∫⁻ σ in Ioo (a / 2) s, ((ENNReal.ofReal (2 / a * M) ^ 2 *
        volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R))) := by
    refine setLIntegral_mono' measurableSet_Ioo (fun σ hσ => ?_)
    have hσ0 : 0 < σ := (half_pos ha).trans hσ.1
    have hσinv : σ⁻¹ ≤ 2 / a := by
      rw [inv_eq_one_div, div_le_div_iff₀ hσ0 ha]
      linarith [hσ.1]
    refine slice_L2_bound (a := a) hc hν hFc hFper hσ0 hσ.2 (fun z => ?_)
      (fun z hz => hsupp (σ, z) (Or.inr (Or.inr hz))) hr0
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hσ0.le)]
    exact mul_le_mul hσinv (hM _) (norm_nonneg _) (div_nonneg two_pos.le ha.le)
  have hCGeq : ∫⁻ σ in Ioo (a / 2) s, ((ENNReal.ofReal (2 / a * M) ^ 2 *
        volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R))) =
      (ENNReal.ofReal (2 / a * M) ^ 2 * volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) *
        volume (Ioo (a / 2) s) :=
    setLIntegral_const _ _
  have htot : ∫⁻ x in UnforcedLeray.B0579.cell c,
      ‖UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F (s, x)‖ₑ ^ 2 ≤
      ENNReal.ofReal B ^ 2 * (ENNReal.ofReal s₂ * ((ENNReal.ofReal (2 / a * M) ^ 2 *
        volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) * ENNReal.ofReal s₂)) := by
    calc ∫⁻ x in UnforcedLeray.B0579.cell c,
          ‖UnforcedLeray.Short.PartIIa.N01.smoothHeatInt c ν μ F (s, x)‖ₑ ^ 2
        ≤ ∫⁻ x in UnforcedLeray.B0579.cell c, ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) *
            ∫⁻ σ in Ioo (a / 2) s, ‖phiSlice ν s F σ x‖ₑ ^ 2) :=
          lintegral_mono fun x => hsq x
      _ = ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) *
            ∫⁻ x in UnforcedLeray.B0579.cell c, ∫⁻ σ in Ioo (a / 2) s,
              ‖phiSlice ν s F σ x‖ₑ ^ 2) := by
          rw [lintegral_const_mul' _ _ hc2, lintegral_const_mul' _ _ hVtop]
      _ = ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) *
            ∫⁻ σ in Ioo (a / 2) s, ∫⁻ x in UnforcedLeray.B0579.cell c,
              ‖phiSlice ν s F σ x‖ₑ ^ 2) := by
          rw [hswap]
      _ ≤ ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) *
            ∫⁻ σ in Ioo (a / 2) s, ((ENNReal.ofReal (2 / a * M) ^ 2 *
              volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)))) := by
          gcongr
      _ = ENNReal.ofReal B ^ 2 * (volume (Ioo (a / 2) s) * ((ENNReal.ofReal (2 / a * M) ^ 2 *
              volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) * volume (Ioo (a / 2) s))) := by
          rw [hCGeq]
      _ ≤ ENNReal.ofReal B ^ 2 * (ENNReal.ofReal s₂ * ((ENNReal.ofReal (2 / a * M) ^ 2 *
              volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) * ENNReal.ofReal s₂)) := by
          gcongr
  refine le_trans ?_ htot
  refine lintegral_mono fun x => ?_
  gcongr
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ i)
