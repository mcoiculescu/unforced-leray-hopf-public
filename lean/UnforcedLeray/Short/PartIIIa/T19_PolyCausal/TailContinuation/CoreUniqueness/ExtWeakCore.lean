import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness.CoreTruncData
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.Limit
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.SliceTested

/-!
# Part III-a, helper 2 of `PartIII-a:T19/3/4`: extended weak and slice-tested identity on `(0, H')`

For truncated core causal solution data `CoreTruncData c ν H' μ F b G`, any time weight
`ψ ∈ C^∞_c(0, ∞)` with `tsupport ψ ⊆ Ioo 0 H'` is supported in `[a, u] ⊂ (0, H')`, so spatial flat
tests multiplied by `ψ` vanish for `s ≥ (u + H') / 2 < H'`. Thus the extended weak identity
(`extWeak_trunc`) and the slice-tested identity (`sliceTested_trunc`) hold for all such `ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A compactly supported time weight with `tsupport ⊆ (0, H')` lies in some `[a, u]` with
`0 < a` and `u < H'`. -/
lemma exists_Icc_of_tsupport_Ioo {H' : ℝ} (hH' : 0 < H') {ψ : ℝ → ℝ}
    (hc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioo 0 H') :
    ∃ a u : ℝ, 0 < a ∧ u < H' ∧ tsupport ψ ⊆ Icc a u := by
  rcases (tsupport ψ).eq_empty_or_nonempty with h | hne
  · exact ⟨H' / 2, H' / 2, half_pos hH', half_lt_self hH', by rw [h]; exact empty_subset _⟩
  · obtain ⟨x, hx, hmin⟩ := hc.isCompact.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨y, hy, hmax⟩ := hc.isCompact.exists_isMaxOn hne continuous_id.continuousOn
    exact ⟨x, y, (hts hx).1, (hts hy).2, fun z hz => ⟨hmin hz, hmax hz⟩⟩

/-- The extended tested identity for a spatial flat test `φ` against `ψ` with
`tsupport ψ ⊆ Ioo 0 H'`. -/
lemma spatial_extWeak_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {ψ : ℝ → ℝ} {φ : ℝ × ℝ → Fin 2 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioo 0 H')
    (hφ : IsFlatSpatialTest c φ) :
    IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0 := by
  have hts_pos : tsupport ψ ⊆ Ioi 0 := fun s hs => (hts hs).1
  obtain ⟨a, u, _ha, huH', hab⟩ := exists_Icc_of_tsupport_Ioo hD.pos_H' hψc hts
  have hΦ := isFlatTest_mul_spatial (c := c) hψ hψc hts_pos hφ
  have hH₀ : (u + H') / 2 < H' := by linarith
  have hsupp : ∀ s x i, (u + H') / 2 ≤ s → ψ s * φ x i = 0 := by
    intro s x i hs
    have hs_not : s ∉ Icc a u := fun hm => by linarith [hm.2]
    rw [(weight_zero_of_not_mem_Icc hab hs_not).1, zero_mul]
  have hF := hD.integrable_core ((u + H') / 2) hH₀ _ hΦ hsupp
  have hW := hD.weak_core ((u + H') / 2) hH₀ _ hΦ hsupp
  have hE := errTerm_integrableOn (ν := ν) hψ hψc hts_pos hφ hD.measurable hD.gradMeasurable
    hD.energyLoc
  have hZ := errTerm_integral_zero (ν := ν) hψ hψc hts_pos hφ hD.measurable hD.gradMeasurable
    hD.energyLoc hD.weakGrad
  have hfun : extWeakIntegrand ν μ F b G ψ φ = fun p =>
      flatIntegrand ν μ (fun _ _ _ => 0) F b (fun s x i => ψ s * φ x i) p + errTerm ν b G ψ φ p :=
    funext fun p => extWeak_eq_flat_add c ν μ F b G ψ φ hφ p
  rw [hfun]
  exact ⟨hF.add hE, by rw [integral_add hF hE, hW, hZ, add_zero]⟩

/-- Square integrability of `qNorm` on `[a, u] × cell` for `CoreTruncData`. -/
lemma qNorm_sq_integrableOn_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {a u : ℝ} (ha : 0 < a) :
    IntegrableOn (fun p => qNorm b G F p ^ 2) (Icc a u ×ˢ B0579.cell c) := by
  have hs1 : 0 < a / 2 := by linarith
  have hs2 : a / 2 < max u a + 1 := by linarith [le_max_right u a]
  have hE := hD.energyLoc (a / 2) (max u a + 1) hs1 hs2
  have hF := hD.l2loc (a / 2) (max u a + 1) hs1 hs2
  have hsub : Icc a u ×ˢ B0579.cell c ⊆ Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c :=
    prod_mono (Icc_subset_Icc (by linarith) (by linarith [le_max_left u a])) subset_rfl
  have hIE : IntegrableOn (fun p => vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)
      (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c) := by
    refine ⟨((measurable_vnorm2' hD.measurable).pow_const 2 |>.add
      ((measurable_tnorm2' hD.gradMeasurable).pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)]
    exact hE
  have hIF : IntegrableOn (fun p => tnorm2 (F p) ^ 2)
      (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c) := by
    refine ⟨((measurable_tnorm2' hD.meas).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)]
    exact hF
  have hsum0 : IntegrableOn (fun p => 3 * ((vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) + tnorm2 (F p) ^ 2))
      (Icc (a / 2) (max u a + 1) ×ˢ B0579.cell c) :=
    (hIE.add hIF).const_mul 3
  have hsum : IntegrableOn (fun p => 3 * ((vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) + tnorm2 (F p) ^ 2))
      (Icc a u ×ˢ B0579.cell c) :=
    hsum0.mono_set hsub
  refine Integrable.mono' hsum ?_ (Eventually.of_forall fun p => ?_)
  · unfold qNorm
    exact ((((measurable_vnorm2' hD.measurable).add
      (measurable_tnorm2' hD.gradMeasurable)).add
      (measurable_tnorm2' hD.meas)).pow_const 2).aestronglyMeasurable
  · have hq := qNorm_nonneg b G F p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    unfold qNorm at hq ⊢
    nlinarith [sq_nonneg (vnorm2 (b p) - tnorm2 (G p)), sq_nonneg (vnorm2 (b p) - tnorm2 (F p)),
      sq_nonneg (tnorm2 (G p) - tnorm2 (F p)), vnorm2_nonneg' (b p), tnorm2_nonneg' (G p),
      tnorm2_nonneg' (F p)]

/-- Integrability of the difference of extended integrands on `[a, u] × cell` for `CoreTruncData`. -/
lemma diff_integrableOn_T_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {a u Cψ Cd : ℝ} (ha : 0 < a) (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    (hCψ : ∀ x, ‖ψ x‖ ≤ Cψ) (hCd : ∀ x, ‖deriv ψ x‖ ≤ Cd)
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ)
    {φk : ℝ × ℝ → Fin 2 → ℝ} (hk : IsFlatSpatialTest c φk)
    (hD2 : Integrable (D2 φk φ) (volume.restrict (B0579.cell c))) :
    IntegrableOn (fun p => extWeakIntegrand ν μ F b G ψ φk p - extWeakIntegrand ν μ F b G ψ φ p)
      (Icc a u ×ˢ B0579.cell c) := by
  have hTm : MeasurableSet (Icc a u ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hmk : Measurable (extWeakIntegrand ν μ F b G ψ φk) :=
    measurable_extWeak hD.measurable hD.gradMeasurable hD.meas hψ.continuous
      (hψ.continuous_deriv (by simp)) (fun i => (hk.smooth i).continuous)
      (fun i j => continuous_pd_of_contDiff (hk.smooth i) j)
  have hmφ : Measurable (extWeakIntegrand ν μ F b G ψ φ) :=
    measurable_extWeak hD.measurable hD.gradMeasurable hD.meas hψ.continuous
      (hψ.continuous_deriv (by simp)) (fun i => (hφ.smooth i).continuous)
      (fun i j => continuous_pd_of_contDiff (hφ.smooth i) j)
  have hq := qNorm_sq_integrableOn_trunc (u := u) hD ha
  have hD' := integrableOn_snd_T hD2 a u
  have hg : IntegrableOn (fun p : ℝ × (ℝ × ℝ) => 3 * 1 * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 +
      1 / (2 * 1) * D2 φk φ p.2) (Icc a u ×ˢ B0579.cell c) :=
    (hq.const_mul _).add (hD'.const_mul _)
  refine Integrable.mono' hg ((hmk.sub hmφ).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun p hp => ?_)
  have hpa : a ≤ p.1 := (Set.mem_prod.1 hp).1.1
  have hb := extWeak_sub_bound ν μ F b G ha hCψ0 hCd0 hCψ hCd φk φ hpa one_pos
  exact hb.trans_eq (by unfold D2; ring)

/-- Bound on the integral of the difference of extended integrands on `[a, u] × cell`. -/
lemma norm_diff_integral_T_le_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {a u Cψ Cd : ℝ} (ha : 0 < a) (hCψ0 : 0 ≤ Cψ) (hCd0 : 0 ≤ Cd)
    {ψ : ℝ → ℝ} (hCψ : ∀ x, ‖ψ x‖ ≤ Cψ) (hCd : ∀ x, ‖deriv ψ x‖ ≤ Cd)
    {φ φk : ℝ × ℝ → Fin 2 → ℝ}
    (hD2 : Integrable (D2 φk φ) (volume.restrict (B0579.cell c))) {t : ℝ} (ht : 0 < t) :
    ‖∫ p in Icc a u ×ˢ B0579.cell c, (extWeakIntegrand ν μ F b G ψ φk p -
        extWeakIntegrand ν μ F b G ψ φ p)‖ ≤
      3 * t * Kconst ν μ a Cψ Cd ^ 2 * (∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
        1 / (2 * t) * (volume.real (Icc a u) * ∫ x in B0579.cell c, D2 φk φ x) := by
  have hTm : MeasurableSet (Icc a u ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hq := qNorm_sq_integrableOn_trunc (u := u) hD ha
  have hD' := integrableOn_snd_T hD2 a u
  have hg : IntegrableOn (fun p : ℝ × (ℝ × ℝ) => 3 * t * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 +
      1 / (2 * t) * D2 φk φ p.2) (Icc a u ×ˢ B0579.cell c) :=
    (hq.const_mul _).add (hD'.const_mul _)
  have hae : ∀ᵐ p ∂(volume.restrict (Icc a u ×ˢ B0579.cell c)),
      ‖extWeakIntegrand ν μ F b G ψ φk p - extWeakIntegrand ν μ F b G ψ φ p‖ ≤
        3 * t * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 + 1 / (2 * t) * D2 φk φ p.2 := by
    refine (ae_restrict_iff' hTm).2 (Eventually.of_forall fun p hp => ?_)
    have hpa : a ≤ p.1 := (Set.mem_prod.1 hp).1.1
    have hb := extWeak_sub_bound ν μ F b G ha hCψ0 hCd0 hCψ hCd φk φ hpa ht
    exact hb.trans_eq (by unfold D2; ring)
  calc ‖∫ p in Icc a u ×ˢ B0579.cell c, (extWeakIntegrand ν μ F b G ψ φk p -
        extWeakIntegrand ν μ F b G ψ φ p)‖
      ≤ ∫ p in Icc a u ×ˢ B0579.cell c, (3 * t * Kconst ν μ a Cψ Cd ^ 2 * qNorm b G F p ^ 2 +
          1 / (2 * t) * D2 φk φ p.2) :=
        norm_integral_le_of_norm_le hg hae
    _ = 3 * t * Kconst ν μ a Cψ Cd ^ 2 * (∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
        1 / (2 * t) * (volume.real (Icc a u) * ∫ x in B0579.cell c, D2 φk φ x) := by
        rw [integral_add (hq.const_mul _) (hD'.const_mul _), integral_const_mul, integral_const_mul,
          setIntegral_snd_T (D2 φk φ) a u c]

/-- The extended tested identity for `H¹` divergence-free test fields against `ψ` with
`tsupport ψ ⊆ Ioo 0 H'`. -/
theorem extWeak_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioo 0 H')
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : IsH1DivFreeTest c φ) :
    IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0 := by
  obtain ⟨φk, hk, hT⟩ := divFreeCutoffDensity c hD.pos_c φ hφ
  have hT' : Tendsto (fun k => ∫⁻ x in B0579.cell c, ENNReal.ofReal (D2 (φk k) φ x))
      atTop (𝓝 0) := hT
  have hts_pos : tsupport ψ ⊆ Ioi 0 := fun s hs => (hts hs).1
  obtain ⟨a, u, ha, hsub⟩ := exists_Icc_of_tsupport hψc hts_pos
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Cd, hCd⟩ := (hψ.continuous_deriv (by simp)).bounded_above_of_compact_support hψc.deriv
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0)
  have hTm : MeasurableSet (Icc a u ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hTS : Icc a u ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
    prod_mono (fun s hs => Set.mem_Ioi.2 (lt_of_lt_of_le ha hs.1)) subset_rfl
  have hvan : ∀ φ' : ℝ × ℝ → Fin 2 → ℝ,
      ∀ p ∈ (Ioi (0 : ℝ) ×ˢ B0579.cell c) \ (Icc a u ×ˢ B0579.cell c),
        extWeakIntegrand ν μ F b G ψ φ' p = 0 := by
    intro φ' p hp
    apply extWeak_eq_zero_of_not_mem hsub φ'
    intro h
    exact hp.2 (Set.mem_prod.2 ⟨h, (Set.mem_prod.1 hp.1).2⟩)
  have hkT : ∀ k, IntegrableOn (extWeakIntegrand ν μ F b G ψ (φk k)) (Icc a u ×ˢ B0579.cell c) ∧
      ∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ (φk k) p = 0 := by
    intro k
    obtain ⟨h1, h2⟩ := spatial_extWeak_trunc hD hψ hψc hts (hk k)
    refine ⟨h1.mono_set hTS, ?_⟩
    exact ((setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSm hTS
      (fun p hp => hvan (φk k) p hp)).symm).trans h2
  obtain ⟨k0, hk0⟩ := (eventually_D2_integrable hφ hk hT').exists
  have hEφT : IntegrableOn (extWeakIntegrand ν μ F b G ψ φ) (Icc a u ×ˢ B0579.cell c) := by
    have hD_int := diff_integrableOn_T_trunc (u := u) hD hψ ha hCψ0 hCd0 hCψ hCd hφ (hk k0) hk0
    have h : IntegrableOn (fun p => extWeakIntegrand ν μ F b G ψ (φk k0) p -
        (extWeakIntegrand ν μ F b G ψ (φk k0) p - extWeakIntegrand ν μ F b G ψ φ p))
        (Icc a u ×ˢ B0579.cell c) := (hkT k0).1.sub hD_int
    refine h.congr_fun (fun p _ => ?_) hTm
    dsimp only
    ring
  have hbound : ∀ t : ℝ, 0 < t →
      ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ ≤
        3 * t * (Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) := by
    intro t ht
    have h0 := tendsto_D2_integral hφ hk hT'
    have h1 : Tendsto (fun k => 3 * t * (Kconst ν μ a Cψ Cd ^ 2 *
          ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
        1 / (2 * t) * (volume.real (Icc a u) * ∫ x in B0579.cell c, D2 (φk k) φ x)) atTop
        (𝓝 (3 * t * (Kconst ν μ a Cψ Cd ^ 2 *
          ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) +
          1 / (2 * t) * (volume.real (Icc a u) * 0))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul h0))
    simp only [mul_zero, add_zero] at h1
    refine ge_of_tendsto h1 ?_
    filter_upwards [eventually_D2_integrable hφ hk hT'] with k hkI
    have hd := norm_diff_integral_T_le_trunc (u := u) hD ha hCψ0 hCd0 hCψ hCd hkI ht
    have hs : ∫ p in Icc a u ×ˢ B0579.cell c, (extWeakIntegrand ν μ F b G ψ (φk k) p -
        extWeakIntegrand ν μ F b G ψ φ p) =
        -(∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p) := by
      rw [integral_sub (hkT k).1 hEφT, (hkT k).2, zero_sub]
    rw [hs, norm_neg] at hd
    exact hd.trans_eq (by ring)
  have hC1 : 0 ≤ ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2 :=
    setIntegral_nonneg hTm fun p _ => sq_nonneg _
  have hA0 : 0 ≤ Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2 :=
    mul_nonneg (sq_nonneg _) hC1
  have hJ0 : ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ ≤ 0 := by
    by_contra hnpos
    have hpos : 0 < ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ :=
      not_le.1 hnpos
    have hden : 0 < 6 * (Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) + 1 :=
      by linarith
    have ht : 0 < ‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖ /
        (6 * (Kconst ν μ a Cψ Cd ^ 2 * ∫ p in Icc a u ×ˢ B0579.cell c, qNorm b G F p ^ 2) + 1) :=
      div_pos hpos hden
    have hteq := div_mul_cancel₀ (‖∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p‖)
      hden.ne'
    have hb := hbound _ ht
    nlinarith [hb, hteq, ht, hpos]
  have hJ : ∫ p in Icc a u ×ˢ B0579.cell c, extWeakIntegrand ν μ F b G ψ φ p = 0 :=
    norm_le_zero_iff.1 hJ0
  refine ⟨IntegrableOn.of_forall_sdiff_eq_zero hEφT hSm (fun p hp => hvan φ p hp), ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSm hTS (fun p hp => hvan φ p hp)]
  exact hJ

/-- The tested equation for a complexified test `w`, slicewise in `s`, for `ψ` with
`tsupport ψ ⊆ Ioo 0 H'`. -/
theorem sliceTested_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ) (hts : tsupport ψ ⊆ Ioo 0 H')
    (w : LMSpField) (hre : IsH1DivFreeTest c (fun x i => (w x i).re))
    (him : IsH1DivFreeTest c (fun x i => (w x i).im)) :
    ∫ s in Ioi (0 : ℝ),
      (-(((deriv ψ s : ℝ) : ℂ) * LMIp c w (fun y => b (s, y))) +
        ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * LMIp c w (fun y => b (s, y))) +
        ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j) = 0 := by
  obtain ⟨hI1, hZ1⟩ := extWeak_trunc hD hψ hcs hts hre
  obtain ⟨hI2, hZ2⟩ := extWeak_trunc hD hψ hcs hts him
  have hΦ : IntegrableOn (fun p =>
      extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) p -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := hI1.sub (hI2.const_mul _)
  have hΦ0 : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      (extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) p -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) p) = 0 := by
    rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul, hZ1, hZ2]
    simp
  have hprod := setIntegral_prod (μ := volume) (ν := volume) _ hΦ
  refine (setIntegral_congr_ae measurableSet_Ioi ?_).trans (hprod.symm.trans hΦ0)
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 (aeGoodSlice_trunc hD)]
    with s hsg hs0
  have hs := hsg hs0
  have hwL : LMCellL2 c w := fun i => by
    have h := (hre.l2 i).ofReal (K := ℂ) |>.add ((him.l2 i).ofReal (K := ℂ) |>.const_mul Complex.I)
    refine h.ae_eq (ae_of_all _ fun x => ?_)
    show ((w x i).re : ℂ) + Complex.I * ((w x i).im : ℂ) = w x i
    rw [mul_comm]
    exact Complex.re_add_im _
  have hdw : ∀ j : Fin 2, LMCellL2 c (fun x i => LMPd j (fun y => w y i) x) := fun j i =>
    (hre.l2grad i j).ofReal (K := ℂ) |>.add ((him.l2grad i j).ofReal (K := ℂ) |>.const_mul Complex.I)
  have hT := fun j => lmTens_col_cellL2 (ν := ν) hs j
  have hAi : Integrable (fun x => ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => lmIp_integrable hwL hs.1 i
  have hBi : ∀ i j : Fin 2, Integrable
      (fun x => starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j)
      (volume.restrict (B0579.cell c)) := fun i j => lmIp_integrable (hdw j) (hT j) i
  have hBsum : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hBi i j
  have hpt : ∀ x : ℝ × ℝ, extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) (s, x) -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) (s, x) =
      -(((deriv ψ s : ℝ) : ℂ) * ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i) +
        ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i) +
        ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2,
          starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j := by
    intro x
    have hw : ∀ i : Fin 2, starRingEnd ℂ (w x i) =
        (((w x i).re : ℝ) : ℂ) - Complex.I * (((w x i).im : ℝ) : ℂ) := fun i => by
      apply Complex.ext <;> simp
    simp only [extWeakIntegrand, lmTens, LMPd, Fin.sum_univ_two, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I, hw]
    push_cast
    ring
  have i1 : Integrable (fun x => -(((deriv ψ s : ℝ) : ℂ) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)) (volume.restrict (B0579.cell c)) :=
    (hAi.const_mul _).fun_neg
  have i2 : Integrable (fun x => ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)) (volume.restrict (B0579.cell c)) :=
    (hAi.const_mul _).const_mul _
  have i3 := hBsum.const_mul ((ψ s : ℝ) : ℂ)
  have hsum : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
        starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hBi i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hBi i j
  show _ = ∫ x in B0579.cell c,
      (extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) (s, x) -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) (s, x))
  have i12 : Integrable (fun x => -(((deriv ψ s : ℝ) : ℂ) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i) + ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)) (volume.restrict (B0579.cell c)) :=
    i1.add i2
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add i12 i3, integral_add i1 i2,
    integral_neg, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hsum]
  rfl

end UnforcedLeray.Short.IIIa
