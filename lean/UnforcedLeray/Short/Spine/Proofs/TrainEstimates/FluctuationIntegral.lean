import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Sub.PartI_T14
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Helper for `Spine:SP-EST`: `TrainFluctuationIntegral` without the `cellL2_jet_zero` clash

`Short.PartI.Tasks.TrainL2DecayProof` and `Short.PartI.Tasks.TrainFluctuationIntegralProof` both
declare `UnforcedLeray.Short.PartI.cellL2_jet_zero`, preventing them from being imported together.
This helper places the `PartI:T19` proof in namespace `UnforcedLeray.Short.Spine` with `private`
lemmas so `TrainEstimates.lean` can assemble `TrainEstimatesAll` cleanly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)
open UnforcedLeray.Short.PartI

private theorem hmean_vec_continuous {c : ℝ} {f : Plane → Vec} (hf : Continuous f) :
    Continuous (fun η : ℝ => hmean c f η) := by
  have hF' : Continuous (fun p : ℝ × ℝ => f (p.2, p.1)) :=
    hf.comp (continuous_snd.prodMk continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun η q : ℝ => f (q, η)) hF' (isCompact_Icc : IsCompact (Icc (-c / 2) (c / 2)))
  have heq : (fun η : ℝ => hmean c f η) =
      fun η : ℝ => c⁻¹ • ∫ q in Icc (-c / 2) (c / 2), f (q, η) := by
    funext η
    unfold hmean
    rw [integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact h.const_smul c⁻¹

private theorem hfluct_vec_continuous {c : ℝ} {f : Plane → Vec} (hf : Continuous f) :
    Continuous (hfluct c f) :=
  hf.sub ((hmean_vec_continuous hf).comp continuous_snd)

private theorem continuous_train_v_slice {ν c s : ℝ} (tr : B0140.TrainSol ν c) (hs : 0 ≤ s) :
    Continuous (tr.v s) := by
  have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
    (fun z => ⟨hs, mem_univ z⟩)

private theorem cellL2_hmean_le {c : ℝ} (hc : 0 < c) {f : Plane → Vec} (hf : Continuous f)
    (hl2 : cellL2 c f < ⊤) :
    cellL2 c (fun z : Plane => hmean c f z.2) ≤ cellL2 c f := by
  have hmem : MemLp (fun z : Plane => ‖f z‖) 2 (Cyl.cellμ c) := by
    refine ⟨hf.norm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    exact hl2
  have hprod : Integrable (fun z : Plane => ‖f z‖ ^ 2)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) := by
    rw [← Cyl.cellμ_eq_prod]
    exact hmem.integrable_sq
  set Φ : ℝ → ℝ := fun η => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2
  have hΦ_int : Integrable Φ volume := hprod.integral_prod_right.const_mul c⁻¹
  have : IsFiniteMeasure (volume.restrict (Ico (-c / 2) (c / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  have hΦ_prod : Integrable (fun z : Plane => Φ z.2) (Cyl.cellμ c) := by
    rw [Cyl.cellμ_eq_prod]
    exact hΦ_int.comp_snd _
  set g : Plane → Vec := fun z => hmean c f z.2
  have hg_cont : Continuous g := (hmean_vec_continuous hf).comp continuous_snd
  have hg_sq : ∀ z : Plane, ‖g z‖ ^ 2 ≤ Φ z.2 := by
    intro z
    have h1 : ‖hmean c f z.2‖ ≤ hmean c (fun w : Plane => ‖f w‖) z.2 := by
      unfold hmean
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.2 hc.le)
    have h2 : ‖hmean c f z.2‖ ^ 2 ≤ hmean c (fun w : Plane => ‖f w‖) z.2 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := meanEnergy_hmean_sq_le hc hf.norm (hf.norm.pow 2) (fun _ => le_rfl) z.2
    exact h2.trans h3
  have hg_mem : MemLp (fun z : Plane => ‖g z‖) 2 (Cyl.cellμ c) := by
    refine (memLp_two_iff_integrable_sq hg_cont.norm.aestronglyMeasurable).2 ?_
    refine Integrable.mono' hΦ_prod (hg_cont.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hg_sq z
  have heq_g : cellL2 c g =
      ENNReal.ofReal (Real.sqrt (∫ z : Plane, ‖g z‖ ^ 2 ∂(Cyl.cellμ c))) := by
    unfold cellL2
    rw [← eLpNorm_norm]
    have h := jl2_abs_eLpNorm (Cyl.cellμ c) (fun z : Plane => ‖g z‖) hg_mem
    simpa [abs_of_nonneg (norm_nonneg _)] using h
  have heq_f : cellL2 c f =
      ENNReal.ofReal (Real.sqrt (∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c))) := by
    unfold cellL2
    rw [← eLpNorm_norm]
    have h := jl2_abs_eLpNorm (Cyl.cellμ c) (fun z : Plane => ‖f z‖) hmem
    simpa [abs_of_nonneg (norm_nonneg _)] using h
  have hint_Φ : ∫ z : Plane, Φ z.2 ∂(Cyl.cellμ c) = ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c) := by
    rw [Cyl.cellμ_eq_prod]
    have h1 := integral_prod (fun z : Plane => Φ z.2) (by rwa [← Cyl.cellμ_eq_prod])
    rw [h1]
    have hconst : ∫ _q in Ico (-c / 2) (c / 2), (∫ η : ℝ, Φ η) = c * ∫ η : ℝ, Φ η := by
      rw [setIntegral_const, Measure.real, Real.volume_Ico,
        show c / 2 - (-c / 2) = c by ring, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
    rw [hconst]
    have hmul : ∫ η : ℝ, Φ η = c⁻¹ * ∫ η : ℝ, ∫ q in Ico (-c / 2) (c / 2), ‖f (q, η)‖ ^ 2 :=
      integral_const_mul c⁻¹ _
    rw [hmul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
      MeasureTheory.integral_prod_symm _ hprod]
  have hint_le : ∫ z : Plane, ‖g z‖ ^ 2 ∂(Cyl.cellμ c) ≤
      ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c) := by
    calc ∫ z : Plane, ‖g z‖ ^ 2 ∂(Cyl.cellμ c)
        ≤ ∫ z : Plane, Φ z.2 ∂(Cyl.cellμ c) :=
          integral_mono hg_mem.integrable_sq hΦ_prod hg_sq
      _ = ∫ z : Plane, ‖f z‖ ^ 2 ∂(Cyl.cellμ c) := hint_Φ
  rw [heq_g, heq_f]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hint_le)

private theorem cellL2_hfluct_le_of_le {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) {f : Plane → Vec}
    (hf : Continuous f) (hl2 : cellL2 c f ≤ ENNReal.ofReal B) :
    cellL2 c (hfluct c f) ≤ ENNReal.ofReal (2 * B) := by
  have hg_cont : Continuous (fun z : Plane => hmean c f z.2) :=
    (hmean_vec_continuous hf).comp continuous_snd
  have htri : cellL2 c (hfluct c f) ≤ cellL2 c f + cellL2 c (fun z : Plane => hmean c f z.2) := by
    unfold cellL2 hfluct
    exact eLpNorm_sub_le hf.aestronglyMeasurable hg_cont.aestronglyMeasurable one_le_two
  have hmean_le : cellL2 c (fun z : Plane => hmean c f z.2) ≤ ENNReal.ofReal B :=
    (cellL2_hmean_le hc hf (hl2.trans_lt ENNReal.ofReal_lt_top)).trans hl2
  calc cellL2 c (hfluct c f)
      ≤ cellL2 c f + cellL2 c (fun z : Plane => hmean c f z.2) := htri
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hl2 hmean_le
    _ = ENNReal.ofReal (2 * B) := by
        rw [← ENNReal.ofReal_add hB hB, two_mul]

private theorem hmean_const_smul_vec (c a : ℝ) (F : Plane → Vec) (Y : ℝ) :
    hmean c (fun y : Plane => a • F y) Y = a • hmean c F Y := by
  unfold hmean
  rw [integral_smul, smul_comm]

private theorem hfluct_scaleField {c : ℝ} (hc : 0 < c) (f : Plane → Vec) :
    hfluct 1 (scaleField c f) = scaleField c (hfluct c f) := by
  funext y
  unfold hfluct scaleField
  have h1 : hmean 1 (fun w : Plane => c ^ 3 • f (c • w)) y.2 =
      c ^ 3 • hmean c f (c * y.2) := by
    rw [hmean_const_smul_vec, hmean_scale_unit hc f y.2]
  rw [h1]
  simp [Prod.smul_snd, smul_eq_mul, smul_sub]

private theorem cellL2_scaleField {c : ℝ} (hc : 0 < c) {g : Plane → Vec} (hg : Continuous g) :
    cellL2 1 (scaleField c g) = ENNReal.ofReal (c ^ 2) * cellL2 c g := by
  have hfun : scaleField c g = (c ^ 3 : ℝ) • (fun y : Plane => g (c • y)) := rfl
  unfold cellL2
  rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
  change ENNReal.ofReal (c ^ 3) * cellL2 1 (fun y : Plane => g (c • y)) = _
  rw [cellL2_one_comp_smul hc hg]
  unfold cellL2
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

private theorem cellL2_jet_zero_vec (c : ℝ) (g : Plane → Vec) :
    cellL2 c (jet 0 g) = cellL2 c g := by
  unfold cellL2
  rw [← eLpNorm_norm (jet 0 g), ← eLpNorm_norm g]
  have hnorm : (fun y : Plane => ‖jet 0 g y‖) = fun y : Plane => ‖g y‖ := by
    funext y
    exact norm_iteratedFDeriv_zero
  rw [hnorm]

private theorem cellL2_hfluct_postOverlap_le {ν c C_ov lam s : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hs0 : 0 ≤ s) (hs : B0146.overlapAge ν c ≤ s)
    (hOv0 : ∀ T : ℝ, 0 ≤ T →
      cellL2 1 (jet 0 (hfluct 1 (overlapField ν c tr.v T))) ≤
        ENNReal.ofReal (C_ov * Real.exp (-(lam * T)))) :
    cellL2 c (hfluct c (tr.v s)) ≤
      ENNReal.ofReal (C_ov * (c ^ 2)⁻¹ *
        Real.exp (-((lam * ν / c ^ 2) * (s - B0146.overlapAge ν c)))) := by
  set s_c := B0146.overlapAge ν c
  set T := ν * (s - s_c) / c ^ 2
  have hT : 0 ≤ T := div_nonneg (mul_nonneg hν.le (sub_nonneg.2 hs)) (sq_nonneg c)
  have hs_eq : s_c + c ^ 2 * T / ν = s := by
    have hν0 : ν ≠ 0 := hν.ne'
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
    dsimp [T]
    field_simp
    ring
  have hU_eq : overlapField ν c tr.v T = scaleField c (tr.v s) := by
    funext y
    simp [overlapField, scaleField, s_c, hs_eq]
  have hg_cont : Continuous (hfluct c (tr.v s)) :=
    hfluct_vec_continuous (continuous_train_v_slice tr hs0)
  have h1 := hOv0 T hT
  rw [cellL2_jet_zero_vec, hU_eq, hfluct_scaleField hc, cellL2_scaleField hc hg_cont] at h1
  have hmul := mul_le_mul_of_nonneg_left h1 (zero_le : 0 ≤ ENNReal.ofReal (c ^ 2)⁻¹)
  have hc2_pos : 0 < c ^ 2 := sq_pos_of_pos hc
  have hlhs : ENNReal.ofReal (c ^ 2)⁻¹ * (ENNReal.ofReal (c ^ 2) * cellL2 c (hfluct c (tr.v s))) =
      cellL2 c (hfluct c (tr.v s)) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc2_pos.le),
      inv_mul_cancel₀ hc2_pos.ne', ENNReal.ofReal_one, one_mul]
  rw [hlhs, ← ENNReal.ofReal_mul (inv_nonneg.2 hc2_pos.le)] at hmul
  refine hmul.trans (le_of_eq ?_)
  congr 1
  dsimp [T]
  ring_nf

private theorem lintegral_preOverlap_inv_width {K ν c σ₀ : ℝ} (hK : 0 ≤ K) (hν : 0 < ν)
    (hσ₀ : 0 ≤ σ₀) (hσc : 1 + σ₀ ≤ c ^ 2) :
    ∫⁻ s in Ioc (σ₀ / ν) (B0146.overlapAge ν c), ENNReal.ofReal (K * (width ν s)⁻¹) =
      ENNReal.ofReal (K * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀))) := by
  set s₀ := σ₀ / ν
  set s_c := B0146.overlapAge ν c
  have hs₀_nn : 0 ≤ s₀ := div_nonneg hσ₀ hν.le
  have hs₀_le_sc : s₀ ≤ s_c := by
    dsimp [s₀, s_c, B0146.overlapAge]
    exact div_le_div_of_nonneg_right (by linarith) hν.le
  set f : ℝ → ℝ := fun s => K * (width ν s)⁻¹
  set F : ℝ → ℝ := fun s => K * ν⁻¹ * Real.log (1 + ν * s)
  have hf_pos : ∀ s ∈ uIcc s₀ s_c, 0 < 1 + ν * s := by
    intro s hs
    rw [uIcc_of_le hs₀_le_sc] at hs
    have hs_nn : 0 ≤ s := hs₀_nn.trans hs.1
    nlinarith
  have hf_cont : ContinuousOn f (uIcc s₀ s_c) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ ?_ (fun s hs => (hf_pos s hs).ne'))
    exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  have hderiv : ∀ s ∈ uIcc s₀ s_c, HasDerivAt F (f s) s := by
    intro s hs
    have hw_pos : 0 < 1 + ν * s := hf_pos s hs
    have hd1 : HasDerivAt (fun r : ℝ => 1 + ν * r) ν s := by
      simpa using ((hasDerivAt_id s).const_mul ν).const_add 1
    have hd2 : HasDerivAt (fun r : ℝ => Real.log (1 + ν * r)) (ν / (1 + ν * s)) s :=
      hd1.log hw_pos.ne'
    have hd3 : HasDerivAt F (K * ν⁻¹ * (ν / (1 + ν * s))) s :=
      hd2.const_mul (K * ν⁻¹)
    have heq : K * ν⁻¹ * (ν / (1 + ν * s)) = f s := by
      dsimp [f, width]
      have hν0 : ν ≠ 0 := hν.ne'
      field_simp
    rwa [heq] at hd3
  have hint_Ioc : IntegrableOn f (Ioc s₀ s_c) volume := by
    rw [uIcc_of_le hs₀_le_sc] at hf_cont
    exact hf_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hf_nn : 0 ≤ᵐ[volume.restrict (Ioc s₀ s_c)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hw : 0 < width ν s := by
      change 0 < 1 + ν * s
      have : 0 ≤ s := hs₀_nn.trans hs.1.le
      nlinarith
    exact mul_nonneg hK (inv_nonneg.2 hw.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_Ioc hf_nn,
    ← intervalIntegral.integral_of_le hs₀_le_sc,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hf_cont.intervalIntegrable)]
  congr 1
  have h1 : 1 + ν * s_c = c ^ 2 := width_overlapAge hν.ne'
  have h2 : 1 + ν * s₀ = 1 + σ₀ := by
    dsimp [s₀]
    have hν0 : ν ≠ 0 := hν.ne'
    field_simp
  have hc2_pos : 0 < c ^ 2 := by linarith
  have hσ_pos : 0 < 1 + σ₀ := by linarith
  dsimp [F]
  rw [h1, h2, ← mul_sub, ← Real.log_div hc2_pos.ne' hσ_pos.ne']

private theorem lintegral_postOverlap_exp {C_ov lam ν c : ℝ} (hC_ov : 0 ≤ C_ov) (hlam : 0 < lam)
    (hν : 0 < ν) (hc : 0 < c) :
    ∫⁻ s in Ioi (B0146.overlapAge ν c),
        ENNReal.ofReal (C_ov * (c ^ 2)⁻¹ *
          Real.exp (-((lam * ν / c ^ 2) * (s - B0146.overlapAge ν c)))) =
      ENNReal.ofReal (C_ov / (lam * ν)) := by
  set s_c := B0146.overlapAge ν c
  set k := lam * ν / c ^ 2
  have hk_pos : 0 < k := by positivity
  have hfun : ∀ s : ℝ, C_ov * (c ^ 2)⁻¹ * Real.exp (-(k * (s - s_c))) =
      (C_ov * (c ^ 2)⁻¹ * Real.exp (k * s_c)) * Real.exp ((-k) * s) := by
    intro s
    rw [mul_assoc (C_ov * (c ^ 2)⁻¹), ← Real.exp_add]
    congr 2
    ring
  have hint : IntegrableOn
      (fun s : ℝ => (C_ov * (c ^ 2)⁻¹ * Real.exp (k * s_c)) * Real.exp ((-k) * s))
      (Ioi s_c) volume :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hk_pos) s_c).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi s_c)]
      fun s : ℝ => (C_ov * (c ^ 2)⁻¹ * Real.exp (k * s_c)) * Real.exp ((-k) * s) :=
    ae_of_all _ fun s => by positivity
  change ∫⁻ s in Ioi s_c, ENNReal.ofReal (C_ov * (c ^ 2)⁻¹ * Real.exp (-(k * (s - s_c)))) =
    ENNReal.ofReal (C_ov / (lam * ν))
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_exp_mul_Ioi (neg_lt_zero.2 hk_pos) s_c]
  congr 1
  have hexp : Real.exp (k * s_c) * (-Real.exp (-k * s_c) / -k) = k⁻¹ := by
    have hk0 : k ≠ 0 := hk_pos.ne'
    have hmul_exp : Real.exp (k * s_c) * Real.exp (-k * s_c) = 1 := by
      rw [← Real.exp_add]
      simp
    calc Real.exp (k * s_c) * (-Real.exp (-k * s_c) / -k)
        = (Real.exp (k * s_c) * Real.exp (-k * s_c)) / k := by ring
      _ = 1 / k := by rw [hmul_exp]
      _ = k⁻¹ := one_div k
  rw [mul_assoc, hexp]
  dsimp [k]
  have hc0 : c ≠ 0 := hc.ne'
  have hν0 : ν ≠ 0 := hν.ne'
  have hlam0 : lam ≠ 0 := hlam.ne'
  field_simp

theorem trainFluctuationIntegral_proof (hL2 : PartI.TrainL2Decay) (hOv : PartI.TrainOverlap) :
    PartI.TrainFluctuationIntegral := by
  intro ρ hρ
  obtain ⟨C₁, ν₁, hC₁, hν₁, hL2'⟩ := hL2 ρ hρ
  obtain ⟨C₂, lam, ν₂, hC₂, hlam, hν₂, hOv'⟩ := hOv ρ hρ 0
  refine ⟨2 * C₁ + C₂ / lam, min (min ν₁ ν₂) (1 / 2), by positivity,
    lt_min (lt_min hν₁ hν₂) (by norm_num), ?_⟩
  intro ν hν hν_le tr htr σ₀ hσ₀ hσc
  have hν_1 : ν ≤ ν₁ := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_2 : ν ≤ ν₂ := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  let c := trainPeriod ρ ν
  have hc1 : 1 < c := by
    unfold c trainPeriod
    have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans hc1
  set s₀ := σ₀ / ν
  set s_c := B0146.overlapAge ν c
  have hs₀_nn : 0 ≤ s₀ := div_nonneg hσ₀ hν.le
  have hs₀_le_sc : s₀ ≤ s_c := by
    dsimp [s₀, s_c, B0146.overlapAge]
    exact div_le_div_of_nonneg_right (by linarith) hν.le
  have hsc_nn : 0 ≤ s_c := hs₀_nn.trans hs₀_le_sc
  have hunion : Ioi s₀ = Ioc s₀ s_c ∪ Ioi s_c :=
    (Ioc_union_Ioi_eq_Ioi hs₀_le_sc).symm
  have hsplit : ∫⁻ s in Ioi s₀, cellL2 c (hfluct c (tr.v s)) ≤
      (∫⁻ s in Ioc s₀ s_c, cellL2 c (hfluct c (tr.v s))) +
        (∫⁻ s in Ioi s_c, cellL2 c (hfluct c (tr.v s))) := by
    conv_lhs => rw [hunion]
    exact lintegral_union_le _ _ _
  have hpre : ∫⁻ s in Ioc s₀ s_c, cellL2 c (hfluct c (tr.v s)) ≤
      ENNReal.ofReal (2 * C₁ * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀))) := by
    rw [← lintegral_preOverlap_inv_width (by positivity : 0 ≤ 2 * C₁) hν hσ₀ hσc]
    refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
    have hs_nn : 0 ≤ s := hs₀_nn.trans hs.1.le
    have hw_pos : 0 < width ν s := by
      change 0 < 1 + ν * s
      nlinarith
    have hl2_s := (hL2' ν hν hν_1 tr htr s hs_nn).1 hs.2
    have hfl := cellL2_hfluct_le_of_le hc0 (by positivity)
      (continuous_train_v_slice tr hs_nn) hl2_s
    simpa [mul_assoc] using hfl
  have hpost : ∫⁻ s in Ioi s_c, cellL2 c (hfluct c (tr.v s)) ≤
      ENNReal.ofReal (C₂ / (lam * ν)) := by
    rw [← lintegral_postOverlap_exp hC₂.le hlam hν hc0]
    refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
    have hs_sc : s_c ≤ s := hs.le
    have hs_nn : 0 ≤ s := hsc_nn.trans hs_sc
    exact cellL2_hfluct_postOverlap_le hν hc0 tr hs_nn hs_sc
      (fun T hT => (hOv' ν hν hν_2 tr htr T hT).2.2.2.2.1)
  have hlog_nn : 0 ≤ Real.log (c ^ 2 / (1 + σ₀)) := by
    apply Real.log_nonneg
    rw [ one_le_div (by linarith) ]
    exact hσc
  have hsum_le : 2 * C₁ * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀)) + C₂ / (lam * ν) ≤
      (2 * C₁ + C₂ / lam) / ν * (1 + Real.log (c ^ 2 / (1 + σ₀))) := by
    have h1 : C₂ / (lam * ν) = (C₂ / lam) * ν⁻¹ := by ring
    have h2 : (2 * C₁ + C₂ / lam) / ν * (1 + Real.log (c ^ 2 / (1 + σ₀))) =
        2 * C₁ * ν⁻¹ + (C₂ / lam) * ν⁻¹ +
          2 * C₁ * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀)) +
          (C₂ / lam) * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀)) := by ring
    rw [h1, h2]
    have hp1 : 0 ≤ 2 * C₁ * ν⁻¹ := by positivity
    have hp2 : 0 ≤ (C₂ / lam) * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀)) := by positivity
    linarith
  calc ∫⁻ s in Ioi s₀, cellL2 c (hfluct c (tr.v s))
      ≤ (∫⁻ s in Ioc s₀ s_c, cellL2 c (hfluct c (tr.v s))) +
          (∫⁻ s in Ioi s_c, cellL2 c (hfluct c (tr.v s))) := hsplit
    _ ≤ ENNReal.ofReal (2 * C₁ * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀))) +
          ENNReal.ofReal (C₂ / (lam * ν)) := add_le_add hpre hpost
    _ = ENNReal.ofReal (2 * C₁ * ν⁻¹ * Real.log (c ^ 2 / (1 + σ₀)) + C₂ / (lam * ν)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((2 * C₁ + C₂ / lam) / ν * (1 + Real.log (c ^ 2 / (1 + σ₀)))) :=
        ENNReal.ofReal_le_ofReal hsum_le

end UnforcedLeray.Short.Spine

end
