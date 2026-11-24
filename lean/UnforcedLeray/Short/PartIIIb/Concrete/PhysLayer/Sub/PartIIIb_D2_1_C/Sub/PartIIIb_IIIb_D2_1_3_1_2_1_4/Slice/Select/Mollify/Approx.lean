import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.Membership
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# `convYApprox`: approximate identity in `Y_2` for the mollifier `η_n = (n+1)³ η((n+1)·)`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Per slice: `‖η_n *_y g - g‖_{L²} → 0` for `g ∈ L²` (translation continuity in `L²` plus Minkowski);
then dominated convergence in `τ ∈ (0,P]` with bound `4 ‖Φ(τ)‖²_{L²}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma apx_h2z : (2 : ℝ≥0∞) ≠ 0 := by norm_num

lemma apx_h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num

lemma apx_molScale_contDiff {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) :
    ContDiff ℝ ∞ (molScale η n) := by
  unfold molScale
  exact contDiff_const.mul (hη.1.comp (contDiff_const_smul _))

lemma apx_molScale_continuous {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) :
    Continuous (molScale η n) :=
  (apx_molScale_contDiff hη n).continuous

lemma apx_molScale_compact {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) :
    HasCompactSupport (molScale η n) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have := hη.2.1.comp_isClosedEmbedding
    ((Homeomorph.smulOfNeZero ((n : ℝ) + 1) hn).isClosedEmbedding)
  unfold molScale
  exact this.mul_left

lemma apx_molScale_nonneg {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) (y : Space) :
    0 ≤ molScale η n y := by
  unfold molScale
  exact mul_nonneg (by positivity) (hη.2.2.2.1 _)

lemma apx_molScale_integral {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) :
    ∫ y : Space, molScale η n y = 1 := by
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold molScale
  rw [integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin,
    hη.2.2.2.2, smul_eq_mul, mul_one, abs_of_pos (inv_pos.mpr (pow_pos hc 3))]
  field_simp

lemma apx_molScale_support {η : Space → ℝ} (hη : IsMollifier η) :
    ∃ R : ℝ, ∀ n : ℕ, ∀ y : Space, R / ((n : ℝ) + 1) < ‖y‖ → molScale η n y = 0 := by
  obtain ⟨R, hR⟩ := hη.2.1.isCompact.isBounded.subset_closedBall (0 : Space)
  refine ⟨R, fun n y hy => ?_⟩
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : R < ‖((n : ℝ) + 1) • y‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc.le]
    rw [div_lt_iff₀ hc] at hy
    linarith
  have hout : ((n : ℝ) + 1) • y ∉ Metric.closedBall (0 : Space) R := by
    rw [mem_closedBall_zero_iff]
    exact not_le.mpr hlt
  have hη0 : η (((n : ℝ) + 1) • y) = 0 := by
    by_contra hne
    exact hout (hR (subset_tsupport η (Function.mem_support.mpr hne)))
  unfold molScale
  rw [hη0, mul_zero]

lemma apx_lintegral_enorm_one {φ : Space → ℝ} (hφi : Integrable φ volume)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1) : ∫⁻ t, ‖φ t‖ₑ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hφi]
  have hn : (fun t => ‖φ t‖) = φ := funext fun t => Real.norm_of_nonneg (hφ0 t)
  rw [hn, hφ1, ENNReal.ofReal_one]

lemma apx_mol_one {η : Space → ℝ} (hη : IsMollifier η) (n : ℕ) :
    ∫⁻ t, ‖molScale η n t‖ₑ = 1 :=
  apx_lintegral_enorm_one ((apx_molScale_continuous hη n).integrable_of_hasCompactSupport
    (apx_molScale_compact hη n)) (apx_molScale_nonneg hη n) (apx_molScale_integral hη n)

/-- Minkowski bound for the slice convolution minus the function, in `L^p`. -/
lemma apx_cv_sub_le {φ : Space → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∫ y, φ y = 1) {r : ℝ} (hφr : ∀ y, r < ‖y‖ → φ y = 0)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp' : p ≠ ⊤) {f : Space → CVec3} (hf : MemLp f p volume)
    {η : ℝ≥0∞} (hη : ∀ h : Space, ‖h‖ ≤ r → eLpNorm (fun y => f (y + h) - f y) p volume ≤ η) :
    eLpNorm (fun x => Sob.cv volume φ f x - f x) p volume ≤ η := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable hp1
  have hφi : Integrable φ volume := hφc.integrable_of_hasCompactSupport hφs
  have hrepr : ∀ x, Sob.cv volume φ f x - f x = ∫ t, φ t • (f (x - t) - f x) := by
    intro x
    rw [Sob.cv_apply_swap]
    have h1 := Sob.integrable_kernel_swap hφc hφs hloc x
    have h2 : Integrable (fun t => φ t • f x) volume := hφi.smul_const (f x)
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, hφ1, one_smul]
  have e : (fun x => Sob.cv volume φ f x - f x) = fun x => ∫ t, φ t • (f (x - t) - f x) :=
    funext hrepr
  rw [e]
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x t => φ t • (f (x - t) - f x))
      (volume.prod volume) := by
    have h1 := Sob.aestronglyMeasurable_kernel_prod (μ := volume) hφc hf.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : Space × Space => φ z.2 • f z.1)
        (volume.prod volume) :=
      (hφc.comp continuous_snd).aestronglyMeasurable.smul hf.aestronglyMeasurable.comp_fst
    refine (h1.sub h2).congr (Eventually.of_forall fun z => ?_)
    simp [Function.uncurry, smul_sub]
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hmeas hp1 hp').trans ?_
  calc ∫⁻ t, eLpNorm (fun x => φ t • (f (x - t) - f x)) p volume
      ≤ ∫⁻ t, ‖φ t‖ₑ * η := by
        refine lintegral_mono fun t => ?_
        rw [show (fun x => φ t • (f (x - t) - f x)) = φ t • (fun x => f (x - t) - f x) from rfl,
          eLpNorm_const_smul]
        by_cases ht : ‖t‖ ≤ r
        · have hb : eLpNorm (fun x => f (x - t) - f x) p volume ≤ η := by
            have := hη (-t) (by rw [norm_neg]; exact ht)
            simpa only [sub_eq_add_neg] using this
          gcongr
        · have h0 : φ t = 0 := hφr t (not_le.mp ht)
          simp [h0]
    _ = η := by
        rw [lintegral_mul_const _ hφc.measurable.enorm, apx_lintegral_enorm_one hφi hφ0 hφ1,
          one_mul]

/-- Approximate identity in `L²` along the rescaled mollifiers. -/
lemma apx_tendsto_cv {η : Space → ℝ} (hη : IsMollifier η) {g : Space → CVec3}
    (hg : MemLp g 2 volume) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => Sob.cv volume (molScale η n) g x - g x) 2 volume)
      atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := apx_molScale_support hη
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have hT := Sob.tendsto_eLpNorm_translate_sub (μ := volume) apx_h2t hg
  rw [ENNReal.tendsto_nhds_zero] at hT ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hT ε hε)
  have hR' : Tendsto (fun n : ℕ => R / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  filter_upwards [hR'.eventually (gt_mem_nhds hδ)] with n hn
  refine apx_cv_sub_le (apx_molScale_continuous hη n) (apx_molScale_compact hη n)
    (apx_molScale_nonneg hη n) (apx_molScale_integral hη n) (fun y hy => hR n y hy)
    one_le_two apx_h2t hg (fun h hh => ?_)
  apply hball
  rw [dist_zero_right]
  exact lt_of_le_of_lt hh hn

lemma apx_slice_eq (L : Space → ℝ) (G : ℝ × Space → CVec3) (t : ℝ) :
    (fun y : Space => convYMol L G (t, y)) = Sob.cv volume L (fun z : Space => G (t, z)) := by
  funext y
  rw [Sob.cv_apply]
  rfl

lemma apx_convY_sm {L : Space → ℝ} (hL : Continuous L) {G : ℝ × Space → CVec3}
    (hG : StronglyMeasurable G) : StronglyMeasurable (convYMol L G) := by
  have hF : StronglyMeasurable
      (fun p : (ℝ × Space) × Space => L (p.1.2 - p.2) • G (p.1.1, p.2)) := by
    have h1 : StronglyMeasurable (fun p : (ℝ × Space) × Space => L (p.1.2 - p.2)) :=
      (hL.comp ((continuous_snd.comp continuous_fst).sub continuous_snd)).stronglyMeasurable
    have h2 : StronglyMeasurable (fun p : (ℝ × Space) × Space => G (p.1.1, p.2)) :=
      hG.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact StronglyMeasurable.smul h1 h2
  exact StronglyMeasurable.integral_prod_right
    (f := fun (x : ℝ × Space) (z : Space) => L (x.2 - z) • G (x.1, z)) hF

lemma apx_convY_ae_rep {L : Space → ℝ} {Φ G : ℝ × Space → CVec3} (hΦG : Φ =ᵐ[volume] G) :
    convYMol L Φ =ᵐ[volume] convYMol L G := by
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ z : Space, Φ (t, z) = G (t, z) :=
    Measure.ae_ae_of_ae_prod hΦG
  refine ae_of_ae_slice (R := fun x : ℝ × Space => convYMol L Φ x = convYMol L G x) ?_
  filter_upwards [h1] with t ht y
  show (∫ z, L (y - z) • Φ (t, z)) = ∫ z, L (y - z) • G (t, z)
  exact integral_congr_ae (ht.mono fun z hz => by simp only [hz])

lemma apx_sq_eLpNorm (f : Space → CVec3) :
    (eLpNorm f 2 volume) ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal apx_h2z apx_h2t, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_mul]
  norm_num

/-- Dominated convergence in `τ` gives the `Y_2` approximate identity for `G`. -/
theorem apx_tendsto_main {P : ℝ} (hP : 0 < P) {η : Space → ℝ} (hη : IsMollifier η)
    {G : ℝ × Space → CVec3} (hG : StronglyMeasurable G)
    (hGfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 G < ⊤) :
    Tendsto (fun n : ℕ => UnforcedLeray.Short.IIb.phaseLpNorm P 2
      (fun x => convYMol (molScale η n) G x - G x)) atTop (𝓝 0) := by
  have hBm : Measurable (fun t : ℝ => ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ)) :=
    (hG.measurable.enorm.pow_const (2 : ℝ)).lintegral_prod_right'
  have hJ : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ) < ⊤ := by
    have hGfin' := hGfin
    unfold UnforcedLeray.Short.IIb.phaseLpNorm at hGfin'
    have ha0 : ENNReal.ofReal P⁻¹ ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.mpr hP
    have hne : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ)
        ≠ ⊤ := by
      intro h
      rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at hGfin'
      exact lt_irrefl _ hGfin'
    apply lt_top_iff_ne_top.mpr
    intro h
    apply hne
    rw [h, ENNReal.mul_top ha0]
  have hK : (2 : ℝ≥0∞) ^ (2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) apx_h2t
  have hslice : ∀ (n : ℕ) (t : ℝ),
      eLpNorm (fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y)) 2 volume
        ≤ 2 * eLpNorm (fun z : Space => G (t, z)) 2 volume := by
    intro n t
    have hfm : AEStronglyMeasurable (fun z : Space => G (t, z)) volume :=
      (hG.comp_measurable measurable_prodMk_left).aestronglyMeasurable
    have hcm : AEStronglyMeasurable (fun y : Space => convYMol (molScale η n) G (t, y)) volume :=
      ((apx_convY_sm (apx_molScale_continuous hη n) hG).comp_measurable
        measurable_prodMk_left).aestronglyMeasurable
    have e1 : eLpNorm (fun y : Space => convYMol (molScale η n) G (t, y)) 2 volume
        ≤ eLpNorm (fun z : Space => G (t, z)) 2 volume := by
      rw [apx_slice_eq (molScale η n) G t]
      have := Sob.eLpNorm_cv_le (μ := volume) (apx_molScale_continuous hη n) hfm
        (p := 2) one_le_two apx_h2t
      rwa [apx_mol_one hη n, one_mul] at this
    have hsub := eLpNorm_sub_le hcm hfm (one_le_two (α := ℝ≥0∞))
    calc eLpNorm (fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y)) 2 volume
        ≤ eLpNorm (fun y : Space => convYMol (molScale η n) G (t, y)) 2 volume
            + eLpNorm (fun z : Space => G (t, z)) 2 volume := hsub
      _ ≤ eLpNorm (fun z : Space => G (t, z)) 2 volume
            + eLpNorm (fun z : Space => G (t, z)) 2 volume := by gcongr
      _ = 2 * eLpNorm (fun z : Space => G (t, z)) 2 volume := (two_mul _).symm
  have hpt : ∀ (n : ℕ) (t : ℝ),
      (∫⁻ y : Space, ‖convYMol (molScale η n) G (t, y) - G (t, y)‖ₑ ^ (2 : ℝ))
        ≤ (2 : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ) := by
    intro n t
    have key := ENNReal.rpow_le_rpow (hslice n t) (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), apx_sq_eLpNorm,
      apx_sq_eLpNorm] at key
    exact key
  have hdct : Tendsto (fun n : ℕ => ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖convYMol (molScale η n) G (t, y) - G (t, y)‖ₑ ^ (2 : ℝ)) atTop
      (𝓝 (∫⁻ _t in Ioc (0 : ℝ) P, (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun t => (2 : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · intro n
      exact (((((apx_convY_sm (apx_molScale_continuous hη n) hG).sub hG).measurable.enorm).pow_const
        (2 : ℝ)).lintegral_prod_right')
    · intro n
      exact Filter.Eventually.of_forall fun t => hpt n t
    · rw [lintegral_const_mul' _ _ hK]
      exact ENNReal.mul_ne_top hK hJ.ne
    · filter_upwards [ae_lt_top hBm hJ.ne] with t ht
      have ht' : ∫⁻ z : Space, ‖G (t, z)‖ₑ ^ (2 : ℝ) < ⊤ := ht
      have hfm : AEStronglyMeasurable (fun z : Space => G (t, z)) volume :=
        (hG.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      have hmem : MemLp (fun z : Space => G (t, z)) 2 volume := by
        refine ⟨hfm, ?_⟩
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal apx_h2z apx_h2t, ENNReal.toReal_ofNat]
        exact (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ht'.ne).lt_top
      have hlim := apx_tendsto_cv hη hmem
      have hlim2 : Tendsto (fun n : ℕ => eLpNorm
          (fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y)) 2 volume) atTop (𝓝 0) := by
        refine Tendsto.congr (fun n => ?_) hlim
        show eLpNorm (fun x : Space => Sob.cv volume (molScale η n) (fun z => G (t, z)) x
            - G (t, x)) 2 volume
          = eLpNorm (fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y)) 2 volume
        have hfun : (fun x : Space => Sob.cv volume (molScale η n) (fun z => G (t, z)) x
            - G (t, x)) = fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y) := by
          funext y
          rw [Sob.cv_apply]
          rfl
        rw [hfun]
      have hpow : Tendsto (fun n : ℕ => (eLpNorm
          (fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y)) 2 volume) ^ (2 : ℝ))
          atTop (𝓝 0) := by
        have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hlim2
        rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at this
      exact Tendsto.congr
        (fun n => apx_sq_eLpNorm (fun y : Space => convYMol (molScale η n) G (t, y) - G (t, y)))
        hpow
  rw [lintegral_zero] at hdct
  have hA : Tendsto (fun n : ℕ => ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖convYMol (molScale η n) G (t, y) - G (t, y)‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal P⁻¹) hdct (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  have hB : Tendsto (fun n : ℕ => (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P,
      ∫⁻ y : Space, ‖convYMol (molScale η n) G (t, y) - G (t, y)‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)))
      atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).tendsto (0 : ℝ≥0∞)).comp hA
    rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  exact hB

/-- (3) Approximate identity in `Y_2` (source 1351-1362). -/
theorem convYApprox : ConvYApprox := by
  intro P hP η hη Φ hΦ
  obtain ⟨G, hG, hΦG⟩ : ∃ G : ℝ × Space → CVec3, StronglyMeasurable G ∧ Φ =ᵐ[volume] G :=
    ⟨hΦ.meas.mk Φ, hΦ.meas.stronglyMeasurable_mk, hΦ.meas.ae_eq_mk⟩
  have hGfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 G < ⊤ := by
    rw [← phaseLpNorm_congr_ae hΦG]
    exact hΦ.finite
  have hrep : ∀ n : ℕ, UnforcedLeray.Short.IIb.phaseLpNorm P 2
      (fun x => convYMol (molScale η n) Φ x - Φ x)
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => convYMol (molScale η n) G x - G x) := by
    intro n
    apply phaseLpNorm_congr_ae
    filter_upwards [apx_convY_ae_rep (L := molScale η n) hΦG, hΦG] with x h1 h2
    simp only [h1, h2]
  unfold YConv
  exact Tendsto.congr (fun n => (hrep n).symm) (apx_tendsto_main hP hη hG hGfin)

end UnforcedLeray.Short.PartIIIb.Concrete
