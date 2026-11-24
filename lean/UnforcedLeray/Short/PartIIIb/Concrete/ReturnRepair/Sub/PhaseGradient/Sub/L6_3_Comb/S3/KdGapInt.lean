import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L5

/-!
# `KdGapInt` (`PartIII-b:C/rep/2/6/3/3/6`)

Integrability of the `h`-majorant `gMaj` against `mHZ = (dh|_{(0,∞)}) ⊗ dz`, by the change of
variables `l = exp(-h/2)` (`dl = (l/2) dh`) from `sepRho = (dl|_{(0,1)}) ⊗ dz`.
Source 3603-3626, 3800-3807, 4171-4200, 5223.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma measurable_expPhi :
    Measurable (fun p : ℝ × Space => (Real.exp (-p.1 / 2), p.2)) :=
  (Real.measurable_exp.comp (measurable_fst.neg.div_const 2)).prodMk measurable_snd

lemma expHalf_image : (fun h : ℝ => Real.exp (-h / 2)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext l
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < h := hh
    linarith
  · rintro ⟨hl0, hl1⟩
    refine ⟨-2 * Real.log l, ?_, ?_⟩
    · have : Real.log l < 0 := Real.log_neg hl0 hl1
      show (0 : ℝ) < -2 * Real.log l
      linarith
    · show Real.exp (-(-2 * Real.log l) / 2) = l
      rw [show -(-2 * Real.log l) / 2 = Real.log l by ring, Real.exp_log hl0]

lemma expHalf_hasDeriv : ∀ x ∈ Ioi (0 : ℝ),
    HasDerivWithinAt (fun h : ℝ => Real.exp (-h / 2)) (Real.exp (-x / 2) * (-1 / 2)) (Ioi 0) x := by
  intro x _
  have h1 : HasDerivAt (fun h : ℝ => -h / 2) (-1 / 2) x := by
    simpa using ((hasDerivAt_id x).neg).div_const 2
  exact (h1.exp).hasDerivWithinAt

lemma expHalf_injOn : InjOn (fun h : ℝ => Real.exp (-h / 2)) (Ioi 0) := by
  intro a _ b _ hab
  have := Real.exp_injective hab
  linarith

/-- Change of variables for the product measure: `(h,z) ↦ (e^{-h/2}, z)` carries
`mHZ` with density `e^{-h/2}/2` onto `sepRho`. -/
lemma cv_mHZ (F : ℝ × Space → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) * F (Real.exp (-p.1 / 2), p.2) ∂mHZ
      = ∫⁻ q, F q ∂sepRho := by
  have hcm : Measurable (fun p : ℝ × Space => ENNReal.ofReal (Real.exp (-p.1 / 2) / 2)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (measurable_fst.neg.div_const 2)).div_const 2)
  have hmeas : Measurable (fun p : ℝ × Space =>
      ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) * F (Real.exp (-p.1 / 2), p.2)) :=
    hcm.mul (hF.comp measurable_expPhi)
  unfold mHZ sepRho
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ h : ℝ, ∫⁻ z, ENNReal.ofReal (Real.exp (-h / 2) / 2) * F (Real.exp (-h / 2), z)
        ∂volume
      = ENNReal.ofReal (Real.exp (-h / 2) / 2) * ∫⁻ z, F (Real.exp (-h / 2), z) ∂volume :=
    fun h => lintegral_const_mul _ (hF.comp (measurable_const.prodMk measurable_id))
  simp only [hinner]
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun h : ℝ => Real.exp (-h / 2))
    (f' := fun h : ℝ => Real.exp (-h / 2) * (-1 / 2)) measurableSet_Ioi expHalf_hasDeriv
    expHalf_injOn (fun l => ∫⁻ z, F (l, z) ∂volume)
  rw [expHalf_image] at hcv
  have habs : ∀ x : ℝ, ENNReal.ofReal |Real.exp (-x / 2) * (-1 / 2)|
      = ENNReal.ofReal (Real.exp (-x / 2) / 2) := by
    intro x
    congr 1
    rw [show Real.exp (-x / 2) * (-1 / 2) = -(Real.exp (-x / 2) / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
  simp only [habs] at hcv
  rw [lintegral_prod _ hF.aemeasurable]
  exact hcv.symm

/-- Transfer of a.e. equality from `sepRho` to `mHZ` along `(h,z) ↦ (e^{-h/2}, z)`. -/
lemma ae_transfer (f g : ℝ × Space → ℝ) (hfg : f =ᵐ[sepRho] g) :
    ∀ᵐ p ∂mHZ, f (Real.exp (-p.1 / 2), p.2) = g (Real.exp (-p.1 / 2), p.2) := by
  obtain ⟨M, hsub, hMmeas, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfg)
  have hI : Measurable (M.indicator fun _ => (1 : ℝ≥0∞)) :=
    (measurable_const (a := (1 : ℝ≥0∞))).indicator hMmeas
  have h0 := cv_mHZ (M.indicator fun _ => (1 : ℝ≥0∞)) hI
  have hR : ∫⁻ q, M.indicator (fun _ => (1 : ℝ≥0∞)) q ∂sepRho = 0 := by
    rw [lintegral_indicator_const hMmeas, hM0, mul_zero]
  have hcm : Measurable (fun p : ℝ × Space => ENNReal.ofReal (Real.exp (-p.1 / 2) / 2)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (measurable_fst.neg.div_const 2)).div_const 2)
  have hmeasL : Measurable (fun p : ℝ × Space =>
      ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) *
        M.indicator (fun _ => (1 : ℝ≥0∞)) (Real.exp (-p.1 / 2), p.2)) :=
    hcm.mul (hI.comp measurable_expPhi)
  have hae := (lintegral_eq_zero_iff hmeasL).1 (h0.trans hR)
  filter_upwards [hae] with p hp
  have hc : ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hnot : (Real.exp (-p.1 / 2), p.2) ∉ M := by
    intro hmem
    have h2 := (mul_eq_zero.1 hp).resolve_left hc
    rw [Set.indicator_of_mem hmem] at h2
    exact one_ne_zero h2
  by_contra hne
  exact hnot (hsub hne)

/-- An a.e.-finite lintegral transfers along an a.e. equality. -/
lemma lintegral_enorm_lt_top_of_ae (f g : ℝ × Space → ℝ) (hfg : f =ᵐ[sepRho] g)
    (hf : Integrable f sepRho) : ∫⁻ q, ‖g q‖ₑ ∂sepRho < ∞ := by
  have h := hasFiniteIntegral_iff_enorm.1 hf.2
  have he : (fun q => ‖f q‖ₑ) =ᵐ[sepRho] (fun q => ‖g q‖ₑ) :=
    hfg.mono fun q hq => by simp only [hq]
  rw [lintegral_congr_ae he] at h
  exact h

/-- Integrability of the combined `h`-majorant on `mHZ`. -/
lemma integrable_mHZ_comb (g1 g2 : ℝ × Space → ℝ) (hg1 : Measurable g1) (hg2 : Measurable g2)
    (hfin1 : ∫⁻ q, ‖g1 q‖ₑ ∂sepRho < ∞) (hfin2 : ∫⁻ q, ‖g2 q‖ₑ ∂sepRho < ∞) :
    Integrable (fun p : ℝ × Space => Real.exp (-p.1 / 2) / 2 *
      (g1 (Real.exp (-p.1 / 2), p.2) + g2 (Real.exp (-p.1 / 2), p.2))) mHZ := by
  have hcm : Measurable (fun p : ℝ × Space => Real.exp (-p.1 / 2) / 2) :=
    (Real.measurable_exp.comp (measurable_fst.neg.div_const 2)).div_const 2
  have hH : Measurable (fun p : ℝ × Space => Real.exp (-p.1 / 2) / 2 *
      (g1 (Real.exp (-p.1 / 2), p.2) + g2 (Real.exp (-p.1 / 2), p.2))) :=
    hcm.mul ((hg1.comp measurable_expPhi).add (hg2.comp measurable_expPhi))
  refine ⟨hH.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 ?_⟩
  have hpt : ∀ p : ℝ × Space,
      ‖Real.exp (-p.1 / 2) / 2 * (g1 (Real.exp (-p.1 / 2), p.2) + g2 (Real.exp (-p.1 / 2), p.2))‖ₑ
        ≤ ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) *
          (‖g1 (Real.exp (-p.1 / 2), p.2)‖ₑ + ‖g2 (Real.exp (-p.1 / 2), p.2)‖ₑ) := by
    intro p
    rw [enorm_mul, Real.enorm_eq_ofReal (by positivity)]
    exact mul_le_mul' le_rfl (enorm_add_le _ _)
  have hF : Measurable (fun q : ℝ × Space => ‖g1 q‖ₑ + ‖g2 q‖ₑ) :=
    hg1.enorm.add hg2.enorm
  calc ∫⁻ p, ‖Real.exp (-p.1 / 2) / 2 * (g1 (Real.exp (-p.1 / 2), p.2) + g2 (Real.exp (-p.1 / 2), p.2))‖ₑ ∂mHZ
      ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (-p.1 / 2) / 2) *
          (‖g1 (Real.exp (-p.1 / 2), p.2)‖ₑ + ‖g2 (Real.exp (-p.1 / 2), p.2)‖ₑ) ∂mHZ :=
        lintegral_mono hpt
    _ = ∫⁻ q, (‖g1 q‖ₑ + ‖g2 q‖ₑ) ∂sepRho := cv_mHZ _ hF
    _ = ∫⁻ q, ‖g1 q‖ₑ ∂sepRho + ∫⁻ q, ‖g2 q‖ₑ ∂sepRho := lintegral_add_left hg1.enorm _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hfin1, hfin2⟩

theorem kdGapInt : KdGapInt := by
  intro ν μ rOut P T hd τ n hn
  obtain ⟨_, hμ, _, hP, hT, hM⟩ := hd
  have hI1 := sepGapMajorantIntegrable (μ : ℂ) P rOut T
    (by rw [Complex.ofReal_re]; exact hμ) hP hT hM τ n hn
  have hI2 := sepGapMajorantIntegrable ((μ : ℂ) + 1) P rOut T
    (by rw [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith) hP hT hM τ n hn
  have hg1m := hI1.1.stronglyMeasurable_mk
  have hg2m := hI2.1.stronglyMeasurable_mk
  have hfg1 := hI1.1.ae_eq_mk
  have hfg2 := hI2.1.ae_eq_mk
  have hfin1 := lintegral_enorm_lt_top_of_ae _ _ hfg1 hI1
  have hfin2 := lintegral_enorm_lt_top_of_ae _ _ hfg2 hI2
  have hI := integrable_mHZ_comb _ _ hg1m.measurable hg2m.measurable hfin1 hfin2
  refine hI.congr ?_
  filter_upwards [ae_transfer _ _ hfg1, ae_transfer _ _ hfg2] with p h1 h2
  simp only [gMaj]
  rw [h1, h2]

end UnforcedLeray.Short.PartIIIb.Concrete
