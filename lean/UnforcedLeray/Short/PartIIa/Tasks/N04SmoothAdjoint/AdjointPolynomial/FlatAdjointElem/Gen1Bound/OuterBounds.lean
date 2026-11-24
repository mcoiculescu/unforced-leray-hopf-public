import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound.SliceDerivs

/-!
# Outer Multiplier Bounds, Commutation Identities, and `opLamRep` Bounds (`OuterBounds`)

Helper module for `PartII-a:N04/2/2/2` (`Gen1Bound`) and `PartII-a:N04/2/2/3` (`Gen2Bound`).
Provides:
1. Additional commutation lemmas for `opS`, `etaMul`, and `laplaceQEta`.
2. Upper-age support (`p.1 ≤ H1`) of `causalAdjointRep` and derived expressions.
3. `L²(measureH c)` bound for the outer multiplier `nuSMul ν 1` (`p ↦ (ν * p.1) • F p`) on
   profiles vanishing for `H1 < p.1`.
4. `L²(measureHT c)` bound from `L²(measureH c)` on profiles vanishing for `H1 < p.1`.
5. Pointwise identification and `L²(measureH c)` norm bounds for `opLamRep ν μ h` and
   `opLamRep ν μ (pdQ h)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.FlatAdjointElemAux

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226

/-! ### 1. Additional commutation and boundedness helpers -/

theorem pdEta_pdQ_comm_fun {u : Profile → MeridC} (hu : ContDiff ℝ ∞ u) :
    pdEta (pdQ u) = pdQ (pdEta u) := by
  funext p
  exact (pdQ_pdEta_comm hu p).symm

theorem opS_etaMul_eq {u : Profile → MeridC} {p : Profile} (hu : DifferentiableAt ℝ u p) :
    opS (etaMul u) p = etaMul (opS u) p := by
  have heta : HasFDerivAt (fun q : Profile => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
  have hsmul := heta.smul hu.hasFDerivAt
  change p.1 • fderiv ℝ ((fun q : Profile => q.2.2) • u) p (1, 0, 0) = p.2.2 • (p.1 • pdS u p)
  rw [hsmul.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', zero_smul, add_zero, smul_apply]
  rw [smul_comm]
  rfl

theorem bdd_etaMul_of_isBaseDeriv {c σ H1 : ℝ} {h u : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u) :
    ∃ B : ℝ, ∀ q : Profile, ‖etaMul u q‖ ≤ B := by
  obtain ⟨B, hB⟩ := hh.bounded_moments a hu.ha 1 (by decide) m hu.hm
  refine ⟨B, fun q => ?_⟩
  rw [← etaMul_one_iter, norm_etaMul_iter]
  exact (mul_le_mul_of_nonneg_left (hu.norm_le q) (by positivity)).trans (hB q)

theorem bdd_etaMul2_of_isBaseDeriv {c σ H1 : ℝ} {h u : Profile → MeridC}
    (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hu : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m u) :
    ∃ B : ℝ, ∀ q : Profile, ‖etaMul (etaMul u) q‖ ≤ B := by
  obtain ⟨B, hB⟩ := hh.bounded_moments a hu.ha 2 (by decide) m hu.hm
  refine ⟨B, fun q => ?_⟩
  rw [← etaMul_two_iter, norm_etaMul_iter]
  exact (mul_le_mul_of_nonneg_left (hu.norm_le q) (by positivity)).trans (hB q)

theorem nuSMul_laplaceQEta_eq (ν : ℝ) (l : ℕ) (w : Profile → MeridC) :
    nuSMul ν l (laplaceQEta w) = nuSMul ν l (pdQ (pdQ w)) + nuSMul ν l (pdEta (pdEta w)) := by
  funext p
  simp [nuSMul, laplaceQEta, smul_add]

theorem memLp_nuSMul_laplaceQEta {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {h w : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hwQ2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdQ (pdQ w)))
    (hwE2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdEta (pdEta w))) (l : ℕ) :
    MemLp (nuSMul ν l (laplaceQEta w)) 2 (measureH c) := by
  rw [nuSMul_laplaceQEta_eq]
  exact (memLp_nuSMul_etaMul hν hσ hσH1 hh hwQ2 (j := 0) (by decide) l).add
    (memLp_nuSMul_etaMul hν hσ hσH1 hh hwE2 (j := 0) (by decide) l)

theorem norm_toLp_nuSMul_laplaceQEta_le {c σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {h w : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h) {a m : ℕ}
    (hwQ2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdQ (pdQ w)))
    (hwE2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdEta (pdEta w))) (l : ℕ) :
    ‖(memLp_nuSMul_laplaceQEta hν hσ hσH1 hh hwQ2 hwE2 l).toLp (nuSMul ν l (laplaceQEta w))‖ ≤
      2 * ((ν * H1) ^ l * flatProjMomentNorm c h) := by
  set mQ : MemLp (nuSMul ν l (pdQ (pdQ w))) 2 (measureH c) :=
    memLp_nuSMul_etaMul hν hσ hσH1 hh hwQ2 (j := 0) (by decide) l
  set mE : MemLp (nuSMul ν l (pdEta (pdEta w))) 2 (measureH c) :=
    memLp_nuSMul_etaMul hν hσ hσH1 hh hwE2 (j := 0) (by decide) l
  have hcongr : (memLp_nuSMul_laplaceQEta hν hσ hσH1 hh hwQ2 hwE2 l).toLp
      (nuSMul ν l (laplaceQEta w)) =
      mQ.toLp (nuSMul ν l (pdQ (pdQ w))) + mE.toLp (nuSMul ν l (pdEta (pdEta w))) := by
    rw [← MemLp.toLp_add mQ mE]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall
      (congrFun (nuSMul_laplaceQEta_eq ν l w)))
  rw [hcongr]
  have h1 := norm_toLp_nuSMul_etaMul_le hν hσ hσH1 hh hwQ2 (j := 0) (by decide) l
  have h2 := norm_toLp_nuSMul_etaMul_le hν hσ hσH1 hh hwE2 (j := 0) (by decide) l
  calc ‖mQ.toLp (nuSMul ν l (pdQ (pdQ w))) + mE.toLp (nuSMul ν l (pdEta (pdEta w)))‖
      ≤ ‖mQ.toLp (nuSMul ν l (pdQ (pdQ w)))‖ + ‖mE.toLp (nuSMul ν l (pdEta (pdEta w)))‖ :=
        norm_add_le _ _
    _ ≤ (ν * H1) ^ l * flatProjMomentNorm c h + (ν * H1) ^ l * flatProjMomentNorm c h :=
        add_le_add h1 h2
    _ = 2 * ((ν * H1) ^ l * flatProjMomentNorm c h) := by ring

theorem memLp_causal_nuSMul_laplaceQEta {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h w : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (hws : ContDiff ℝ ∞ w) (hwp : QPeriodic c w) {a m : ℕ}
    (hwQ2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdQ (pdQ w)))
    (hwE2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdEta (pdEta w))) (k l : ℕ) :
    MemLp (causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (laplaceQEta w))) 2 (measureH c) :=
  memLp_causalAdjointRep hc ν (hγs.trans_le hμγ) (continuous_thetaWeight k) (norm_thetaWeight_le k)
    (contDiff_nuSMul ν l (contDiff_laplaceQEta hws)).continuous.stronglyMeasurable
    (periodic_nuSMul ν l (periodic_laplaceQEta hwp))
    (memLp_nuSMul_laplaceQEta hν hσ hσH1 hh hwQ2 hwE2 l)

theorem norm_causal_nuSMul_laplaceQEta_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h w : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (hws : ContDiff ℝ ∞ w) (hwp : QPeriodic c w) {a m : ℕ}
    (hwQ2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdQ (pdQ w)))
    (hwE2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h a m (pdEta (pdEta w))) (k l : ℕ) :
    ‖(memLp_causal_nuSMul_laplaceQEta hc hν hσ hσH1 hγs hμγ hh hws hwp hwQ2 hwE2 k l).toLp
      (causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (laplaceQEta w)))‖ ≤
      2 * γs⁻¹ * (ν * H1) ^ l * flatProjMomentNorm c h := by
  have h1 := norm_causalAdjointRep_le hc ν hγs hμγ (continuous_thetaWeight k) (norm_thetaWeight_le k)
    (contDiff_nuSMul ν l (contDiff_laplaceQEta hws)).continuous.stronglyMeasurable
    (periodic_nuSMul ν l (periodic_laplaceQEta hwp))
    (memLp_nuSMul_laplaceQEta hν hσ hσH1 hh hwQ2 hwE2 l)
  have h2 := norm_toLp_nuSMul_laplaceQEta_le hν hσ hσH1 hh hwQ2 hwE2 l
  calc ‖(memLp_causal_nuSMul_laplaceQEta hc hν hσ hσH1 hγs hμγ hh hws hwp hwQ2 hwE2 k l).toLp
        (causalAdjointRep ν μ (thetaWeight k) (nuSMul ν l (laplaceQEta w)))‖
      ≤ γs⁻¹ * ‖(memLp_nuSMul_laplaceQEta hν hσ hσH1 hh hwQ2 hwE2 l).toLp
          (nuSMul ν l (laplaceQEta w))‖ := h1
    _ ≤ γs⁻¹ * (2 * ((ν * H1) ^ l * flatProjMomentNorm c h)) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hγs.le)
    _ = 2 * γs⁻¹ * (ν * H1) ^ l * flatProjMomentNorm c h := by ring

/-! ### 2. Upper-age support (`p.1 ≤ H1`) of `causalAdjointRep` -/

theorem flatAdjointSlice_eq_zero_of_support_H1 {H1 : ℝ} (hH1 : 0 < H1)
    (ν : ℝ) (μ : ℂ) {w : Profile → MeridC} (hw : ∀ q : Profile, H1 < q.1 → w q = 0)
    {p : Profile} (hp : H1 < p.1) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    flatAdjointSlice ν μ w t p = 0 := by
  have hp_pos : 0 < p.1 := hH1.trans hp
  have hexp : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hlt : H1 < Real.exp t * p.1 := by
    calc H1 < p.1 := hp
      _ = 1 * p.1 := (one_mul p.1).symm
      _ < Real.exp t * p.1 := mul_lt_mul_of_pos_right hexp hp_pos
  have hzero : (fun y : ℝ × ℝ => w (Real.exp t * p.1, y)) = fun _ => 0 := by
    funext y
    exact hw (Real.exp t * p.1, y) hlt
  simp only [flatAdjointSlice, hzero, planeHeat_zero, smul_zero]

theorem causalAdjointRep_eq_zero_of_support_H1 {H1 : ℝ} (hH1 : 0 < H1)
    (ν : ℝ) (μ : ℂ) (Φ : ℝ → ℂ) {w : Profile → MeridC} (hw : ∀ q : Profile, H1 < q.1 → w q = 0)
    {p : Profile} (hp : H1 < p.1) :
    causalAdjointRep ν μ Φ w p = 0 := by
  simp only [causalAdjointRep]
  split_ifs with hp_pos
  · have hcongr : EqOn (fun t => Φ t • flatAdjointSlice ν μ w t p)
        (fun _ => (0 : MeridC)) (Ioi 0) := by
      intro t ht
      simp [flatAdjointSlice_eq_zero_of_support_H1 hH1 ν μ hw hp ht]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_const, smul_zero]
  · rfl

theorem causalAdjointRep_eq_zero_of_support_s {σ H1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (ν : ℝ) (μ : ℂ) (Φ : ℝ → ℂ) {w : Profile → MeridC}
    (hw : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0)
    {p : Profile} (hp : H1 < p.1) :
    causalAdjointRep ν μ Φ w p = 0 :=
  causalAdjointRep_eq_zero_of_support_H1 (hσ.trans_le hσH1) ν μ Φ
    (fun q hq => hw q (Or.inr hq)) hp

/-! ### 3. Outer `(ν * p.1)` multiplier on `L²(measureH c)` -/

theorem ae_pos_of_measureH (c : ℝ) : ∀ᵐ p ∂(measureH c), 0 < p.1 := by
  filter_upwards [ae_cell_measureH c] with p hp
  exact hp.1

theorem memLp_nuSMul_one_of_support_H1 {c ν H1 : ℝ} (hν : 0 < ν) (hH1 : 0 < H1)
    {F : Profile → MeridC} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0) :
    MemLp (nuSMul ν 1 F) 2 (measureH c) := by
  have hmeas : AEStronglyMeasurable (nuSMul ν 1 F) (measureH c) := by
    have hcont : Continuous (fun p : Profile => (ν * p.1) ^ 1) := by fun_prop
    exact hcont.aestronglyMeasurable.smul hF.1
  refine (hF.const_smul (ν * H1)).mono hmeas ?_
  filter_upwards [ae_pos_of_measureH c] with p hp
  by_cases hpH : p.1 ≤ H1
  · rw [nuSMul_one_apply, Pi.smul_apply, norm_smul, norm_smul,
      Real.norm_of_nonneg (mul_pos hν hp).le,
      Real.norm_of_nonneg (mul_pos hν hH1).le]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpH hν.le) (norm_nonneg _)
  · have hpH' : H1 < p.1 := not_le.mp hpH
    simp [nuSMul_one_apply, hsupp p hpH']

theorem norm_toLp_nuSMul_one_le_of_support_H1 {c ν H1 : ℝ} (hν : 0 < ν) (hH1 : 0 < H1)
    {F : Profile → MeridC} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0) :
    ‖(memLp_nuSMul_one_of_support_H1 hν hH1 hF hsupp).toLp (nuSMul ν 1 F)‖ ≤
      (ν * H1) * ‖hF.toLp F‖ := by
  have hle : ∀ᵐ p ∂(measureH c), ‖nuSMul ν 1 F p‖ ≤ ‖((ν * H1) • F) p‖ := by
    filter_upwards [ae_pos_of_measureH c] with p hp
    by_cases hpH : p.1 ≤ H1
    · rw [nuSMul_one_apply, Pi.smul_apply, norm_smul, norm_smul,
        Real.norm_of_nonneg (mul_pos hν hp).le, Real.norm_of_nonneg (mul_pos hν hH1).le]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpH hν.le) (norm_nonneg _)
    · have hpH' : H1 < p.1 := not_le.mp hpH
      simp [nuSMul_one_apply, hsupp p hpH']
  have he : eLpNorm (nuSMul ν 1 F) 2 (measureH c) ≤
      eLpNorm ((ν * H1) • F) 2 (measureH c) := eLpNorm_mono_ae hle
  have h1 : ‖(memLp_nuSMul_one_of_support_H1 hν hH1 hF hsupp).toLp (nuSMul ν 1 F)‖ =
      ENNReal.toReal (eLpNorm (nuSMul ν 1 F) 2 (measureH c)) :=
    Lp.norm_toLp (nuSMul ν 1 F) (memLp_nuSMul_one_of_support_H1 hν hH1 hF hsupp)
  have h2 : ‖(hF.const_smul (ν * H1)).toLp ((ν * H1) • F)‖ =
      ENNReal.toReal (eLpNorm ((ν * H1) • F) 2 (measureH c)) :=
    Lp.norm_toLp ((ν * H1) • F) (hF.const_smul (ν * H1))
  have h3 : ‖(hF.const_smul (ν * H1)).toLp ((ν * H1) • F)‖ = (ν * H1) * ‖hF.toLp F‖ := by
    rw [MemLp.toLp_const_smul, norm_smul, Real.norm_of_nonneg (mul_pos hν hH1).le]
  rw [h1, ← h3, h2]
  exact ENNReal.toReal_mono (hF.const_smul (ν * H1)).2.ne he

theorem memLp_of_eqOn_pos_nuSMul_one {c ν H1 : ℝ} (hν : 0 < ν) (hH1 : 0 < H1)
    {F G : Profile → MeridC} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0)
    (heq : ∀ p : Profile, 0 < p.1 → G p = (ν * p.1) • F p) :
    MemLp G 2 (measureH c) := by
  refine (memLp_nuSMul_one_of_support_H1 hν hH1 hF hsupp).ae_eq ?_
  filter_upwards [ae_pos_of_measureH c] with p hp
  rw [nuSMul_one_apply, heq p hp]

theorem norm_toLp_of_eqOn_pos_nuSMul_one_le {c ν H1 : ℝ} (hν : 0 < ν) (hH1 : 0 < H1)
    {F G : Profile → MeridC} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0)
    (heq : ∀ p : Profile, 0 < p.1 → G p = (ν * p.1) • F p) :
    ‖(memLp_of_eqOn_pos_nuSMul_one hν hH1 hF hsupp heq).toLp G‖ ≤
      (ν * H1) * ‖hF.toLp F‖ := by
  have hae : nuSMul ν 1 F =ᵐ[measureH c] G := by
    filter_upwards [ae_pos_of_measureH c] with p hp
    rw [nuSMul_one_apply, heq p hp]
  have htoLp : (memLp_of_eqOn_pos_nuSMul_one hν hH1 hF hsupp heq).toLp G =
      (memLp_nuSMul_one_of_support_H1 hν hH1 hF hsupp).toLp (nuSMul ν 1 F) :=
    MemLp.toLp_congr _ _ hae.symm
  rw [htoLp]
  exact norm_toLp_nuSMul_one_le_of_support_H1 hν hH1 hF hsupp

/-! ### 4. Measure transfer `measureH c → measureHT c` on `p.1 ≤ H1` -/

theorem measureHT_eq_measureH_withDensity (c : ℝ) :
    (measureH c).withDensity (fun p => ENNReal.ofReal p.1) = measureHT c := by
  have hm : Measurable fun p : Profile => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  rw [measureH, ← withDensity_mul _ measurable_weightH hm, measureHT]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
  have hs : 0 < p.1 := hp.1
  rw [Pi.mul_apply, weightH, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
    ← Real.rpow_add_one hs.ne']
  norm_num

theorem measureHT_ac_measureH (c : ℝ) : measureHT c ≪ measureH c := by
  rw [← measureHT_eq_measureH_withDensity c]
  exact withDensity_absolutelyContinuous _ _

private theorem enorm_smul_rpow_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0 ≤ a) (v : E) :
    ‖a • v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (a ^ 2) * ‖v‖ₑ ^ (2 : ℝ) := by
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg ha, ENNReal.ofReal_mul ha, ofReal_norm,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), Real.rpow_two]

theorem eLpNorm_measureHT_le_of_support_H1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {c H1 : ℝ} (hH1 : 0 < H1) {F : Profile → E} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0) :
    eLpNorm F 2 (measureHT c) ≤ eLpNorm ((1 + H1) • F) 2 (measureH c) := by
  set f : Profile → E := hF.1.mk F
  have hf_meas : StronglyMeasurable f := hF.1.stronglyMeasurable_mk
  have hf_ae_H : F =ᵐ[measureH c] f := hF.1.ae_eq_mk
  have hf_ae_HT : F =ᵐ[measureHT c] f := (measureHT_ac_measureH c).ae_le hf_ae_H
  have h1H : 0 ≤ 1 + H1 := by linarith
  rw [eLpNorm_congr_ae hf_ae_HT,
    eLpNorm_congr_ae (hf_ae_H.const_smul (1 + H1)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hm_s : Measurable fun p : Profile => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have hm_f : Measurable fun p : Profile => ‖f p‖ₑ ^ (2 : ℝ) :=
    hf_meas.measurable.enorm.pow_const (2 : ℝ)
  rw [← measureHT_eq_measureH_withDensity c,
    lintegral_withDensity_eq_lintegral_mul _ hm_s hm_f]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_pos_of_measureH c, hf_ae_H] with p hp hFp
  dsimp only [Pi.mul_apply, Pi.smul_apply]
  rw [enorm_smul_rpow_two h1H (f p)]
  by_cases hpH : p.1 ≤ H1
  · have hle : p.1 ≤ (1 + H1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle) (by positivity)
  · have hpH' : H1 < p.1 := not_le.mp hpH
    have hf0 : f p = 0 := by rw [← hFp, hsupp p hpH']
    simp [hf0]

theorem memLp_measureHT_of_support_H1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {c H1 : ℝ} (hH1 : 0 < H1) {F : Profile → E} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0) :
    MemLp F 2 (measureHT c) :=
  ⟨hF.1.mono_ac (measureHT_ac_measureH c),
    (eLpNorm_measureHT_le_of_support_H1 hH1 hF hsupp).trans_lt (hF.const_smul (1 + H1)).2⟩

theorem norm_toLp_measureHT_le_of_support_H1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {c H1 : ℝ} (hH1 : 0 < H1) {F : Profile → E} (hF : MemLp F 2 (measureH c))
    (hsupp : ∀ p : Profile, H1 < p.1 → F p = 0) :
    ‖(memLp_measureHT_of_support_H1 hH1 hF hsupp).toLp F‖ ≤
      (1 + H1) * ‖hF.toLp F‖ := by
  have h1H : 0 ≤ 1 + H1 := by linarith
  have he := eLpNorm_measureHT_le_of_support_H1 hH1 hF hsupp
  have h1 : ‖(memLp_measureHT_of_support_H1 hH1 hF hsupp).toLp F‖ =
      ENNReal.toReal (eLpNorm F 2 (measureHT c)) :=
    Lp.norm_toLp F (memLp_measureHT_of_support_H1 hH1 hF hsupp)
  have h2 : ‖(hF.const_smul (1 + H1)).toLp ((1 + H1) • F)‖ =
      ENNReal.toReal (eLpNorm ((1 + H1) • F) 2 (measureH c)) :=
    Lp.norm_toLp ((1 + H1) • F) (hF.const_smul (1 + H1))
  have h3 : ‖(hF.const_smul (1 + H1)).toLp ((1 + H1) • F)‖ = (1 + H1) * ‖hF.toLp F‖ := by
    rw [MemLp.toLp_const_smul, norm_smul, Real.norm_of_nonneg h1H]
  rw [h1, ← h3, h2]
  exact ENNReal.toReal_mono (hF.const_smul (1 + H1)).2.ne he

/-! ### 5. `opLamRep`: explicit causal decomposition of `opLam (causalAdjointRep ν μ (thetaWeight 0) w)` -/

/-- Explicit causal representation of `opLam (causalAdjointRep ν μ (thetaWeight 0) w)` on
`{p : Profile | 0 < p.1}`. -/
def opLamRep (ν : ℝ) (μ : ℂ) (w : Profile → MeridC) : Profile → MeridC :=
  (2 : ℝ) • (causalAdjointRep ν μ (thetaWeight 0) (opS w) +
    causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (laplaceQEta w))) +
  (causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta w)) -
    (2 : ℝ) • causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (pdEta (pdEta w)))) +
  causalAdjointRep ν μ (thetaWeight 0) w

theorem opLam_causalAdjointRep_eq_opLamRep {σ H1 ν : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w)
    (hB_etaE1 : ∃ M : ℝ, ∀ q, ‖etaMul (pdEta w) q‖ ≤ M)
    {p : Profile} (hp : 0 < p.1) :
    opLam (causalAdjointRep ν μ (thetaWeight 0) w) p = opLamRep ν μ w p := by
  have hS := opS_causalAdjointRep hν hσ hσH1 hμ 0 hw hp
  have hEta := pdEta_causalAdjointRep hν hσ hσH1 hμ 0 hw hp
  have hetaEta : p.2.2 • pdEta (causalAdjointRep ν μ (thetaWeight 0) w) p =
      causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta w)) p -
        (2 : ℝ) • causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (pdEta (pdEta w))) p := by
    rw [hEta]
    exact etaMul_causalAdjointRep hν hσ hσH1 hμ 0 (contDiff_pdEta hw.smooth)
      (support_s_pdEta hw.support_s) hw.bdd_pdEta hw.bdd_pdEta2 hB_etaE1 hp
  simp only [opLam, opK, opLamRep, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hS, hetaEta]

theorem opLamRep_eq_zero_of_H1_lt {σ H1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (ν : ℝ) (μ : ℂ) {w : Profile → MeridC} (hw : IsDiffProfile σ H1 w)
    {p : Profile} (hp : H1 < p.1) :
    opLamRep ν μ w p = 0 := by
  have h1 := causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ (thetaWeight 0)
    (support_s_opS hw.support_s) hp
  have h2 := causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ (thetaWeight 1)
    (support_s_nuSMul ν 1 (support_s_laplaceQEta hw.support_s)) hp
  have h3 := causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ (thetaWeight 0)
    (support_s_etaMul (support_s_pdEta hw.support_s)) hp
  have h4 := causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ (thetaWeight 1)
    (support_s_nuSMul ν 1 (support_s_pdEta (support_s_pdEta hw.support_s))) hp
  have h5 := causalAdjointRep_eq_zero_of_support_s hσ hσH1 ν μ (thetaWeight 0)
    hw.support_s hp
  simp [opLamRep, h1, h2, h3, h4, h5]

theorem norm_toLp_add_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖(hf.add hg).toLp (f + g)‖ ≤ ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
  rw [MemLp.toLp_add]
  exact norm_add_le _ _

theorem norm_toLp_sub_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖(hf.sub hg).toLp (f - g)‖ ≤ ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
  rw [MemLp.toLp_sub]
  exact norm_sub_le _ _

theorem norm_toLp_const_smul_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure α} (r : ℝ) {f : α → E} (hf : MemLp f 2 μ) :
    ‖(hf.const_smul r).toLp (r • f)‖ = |r| * ‖hf.toLp f‖ := by
  rw [MemLp.toLp_const_smul, norm_smul, Real.norm_eq_abs]

theorem norm_toLp_complex_smul_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {μ : Measure α} (z : ℂ) {f : α → E} (hf : MemLp f 2 μ) :
    ‖(hf.const_smul z).toLp (z • f)‖ = ‖z‖ * ‖hf.toLp f‖ := by
  rw [MemLp.toLp_const_smul, norm_smul]

theorem memLp_opLamRep {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h w : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (hws : ContDiff ℝ ∞ w) (hwp : QPeriodic c w) {m m1 m2 : ℕ}
    (hw0 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m w)
    (hwS : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 1 m (opS w))
    (hwQ2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m2 (pdQ (pdQ w)))
    (hwE1 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m1 (pdEta w))
    (hwE2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m2 (pdEta (pdEta w))) :
    MemLp (opLamRep ν μ w) 2 (measureH c) := by
  have mS : MemLp (causalAdjointRep ν μ (thetaWeight 0) (opS w)) 2 (measureH c) := by
    simpa [nuSMul_zero] using memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hwS
      (j := 0) (by decide) 0 0
  have mL : MemLp (causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (laplaceQEta w)))
      2 (measureH c) :=
    memLp_causal_nuSMul_laplaceQEta hc hν hσ hσH1 hγs hμγ hh hws hwp hwQ2 hwE2 1 1
  have mE1 : MemLp (causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta w)))
      2 (measureH c) := by
    simpa [nuSMul_zero, etaMul_one_iter] using
      memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hwE1 (j := 1) (by decide) 0 0
  have mE2 : MemLp (causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (pdEta (pdEta w))))
      2 (measureH c) :=
    memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hwE2 (j := 0) (by decide) 1 1
  have m0 : MemLp (causalAdjointRep ν μ (thetaWeight 0) w) 2 (measureH c) := by
    simpa [nuSMul_zero] using memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hw0
      (j := 0) (by decide) 0 0
  exact (((mS.add mL).const_smul (2 : ℝ)).add (mE1.sub (mE2.const_smul (2 : ℝ)))).add m0

theorem norm_toLp_opLamRep_le {c σ H1 ν γs : ℝ} (hc : 0 < c) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hγs : 0 < γs) {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {h w : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (hws : ContDiff ℝ ∞ w) (hwp : QPeriodic c w) {m m1 m2 : ℕ}
    (hw0 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m w)
    (hwS : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 1 m (opS w))
    (hwQ2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m2 (pdQ (pdQ w)))
    (hwE1 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m1 (pdEta w))
    (hwE2 : IsBaseDeriv (c := c) (σ := σ) (H1 := H1) h 0 m2 (pdEta (pdEta w))) :
    ‖(memLp_opLamRep hc hν hσ hσH1 hγs hμγ hh hws hwp hw0 hwS hwQ2 hwE1 hwE2).toLp
      (opLamRep ν μ w)‖ ≤
      (4 + 6 * (ν * H1)) * γs⁻¹ * flatProjMomentNorm c h := by
  set mS : MemLp (causalAdjointRep ν μ (thetaWeight 0) (opS w)) 2 (measureH c) := by
    simpa [nuSMul_zero] using memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hwS
      (j := 0) (by decide) 0 0
  set mL := memLp_causal_nuSMul_laplaceQEta hc hν hσ hσH1 hγs hμγ hh hws hwp hwQ2 hwE2 1 1
  set mE1 : MemLp (causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta w)))
      2 (measureH c) := by
    simpa [nuSMul_zero, etaMul_one_iter] using
      memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hwE1 (j := 1) (by decide) 0 0
  set mE2 : MemLp (causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (pdEta (pdEta w))))
      2 (measureH c) :=
    memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hwE2 (j := 0) (by decide) 1 1
  set m0 : MemLp (causalAdjointRep ν μ (thetaWeight 0) w) 2 (measureH c) := by
    simpa [nuSMul_zero] using memLp_causal_baseDeriv hc hν hσ hσH1 hγs hμγ hh hw0
      (j := 0) (by decide) 0 0
  have hS : ‖mS.toLp (causalAdjointRep ν μ (thetaWeight 0) (opS w))‖ ≤
      γs⁻¹ * flatProjMomentNorm c h := by
    simpa [nuSMul_zero] using norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hwS
      (j := 0) (by decide) 0 0
  have hL : ‖mL.toLp (causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (laplaceQEta w)))‖ ≤
      2 * γs⁻¹ * (ν * H1) * flatProjMomentNorm c h := by
    simpa using norm_causal_nuSMul_laplaceQEta_le hc hν hσ hσH1 hγs hμγ hh hws hwp hwQ2 hwE2 1 1
  have hE1 : ‖mE1.toLp (causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta w)))‖ ≤
      γs⁻¹ * flatProjMomentNorm c h := by
    simpa [nuSMul_zero, etaMul_one_iter] using
      norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hwE1 (j := 1) (by decide) 0 0
  have hE2 : ‖mE2.toLp (causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (pdEta (pdEta w))))‖ ≤
      γs⁻¹ * (ν * H1) * flatProjMomentNorm c h := by
    simpa using norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hwE2 (j := 0) (by decide) 1 1
  have h0 : ‖m0.toLp (causalAdjointRep ν μ (thetaWeight 0) w)‖ ≤
      γs⁻¹ * flatProjMomentNorm c h := by
    simpa [nuSMul_zero] using norm_causal_baseDeriv_le hc hν hσ hσH1 hγs hμγ hh hw0
      (j := 0) (by decide) 0 0
  have hstep1 := norm_toLp_add_le
    (((mS.add mL).const_smul (2 : ℝ)).add (mE1.sub (mE2.const_smul (2 : ℝ)))) m0
  have hstep2 := norm_toLp_add_le
    ((mS.add mL).const_smul (2 : ℝ)) (mE1.sub (mE2.const_smul (2 : ℝ)))
  have hstep3 : ‖((mS.add mL).const_smul (2 : ℝ)).toLp
      ((2 : ℝ) • (causalAdjointRep ν μ (thetaWeight 0) (opS w) +
        causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (laplaceQEta w))))‖ ≤
      2 * (‖mS.toLp _‖ + ‖mL.toLp _‖) := by
    rw [norm_toLp_const_smul_eq (2 : ℝ) (mS.add mL), abs_of_pos (by norm_num)]
    exact mul_le_mul_of_nonneg_left (norm_toLp_add_le mS mL) (by positivity)
  have hstep4 : ‖(mE1.sub (mE2.const_smul (2 : ℝ))).toLp
      (causalAdjointRep ν μ (thetaWeight 0) (etaMul (pdEta w)) -
        (2 : ℝ) • causalAdjointRep ν μ (thetaWeight 1) (nuSMul ν 1 (pdEta (pdEta w))))‖ ≤
      ‖mE1.toLp _‖ + 2 * ‖mE2.toLp _‖ := by
    refine (norm_toLp_sub_le mE1 (mE2.const_smul (2 : ℝ))).trans ?_
    rw [norm_toLp_const_smul_eq (2 : ℝ) mE2, abs_of_pos (by norm_num)]
  change ‖((((mS.add mL).const_smul (2 : ℝ)).add (mE1.sub (mE2.const_smul (2 : ℝ)))).add m0).toLp
      (opLamRep ν μ w)‖ ≤ _
  unfold opLamRep
  linarith

end UnforcedLeray.Short.PartIIa.FlatAdjointElemAux
