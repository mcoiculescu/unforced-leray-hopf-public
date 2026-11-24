import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.Pairing

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/5/1/1`: absolute integrability for the unfolding

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836.
Under `KerYoung c m k M`, `(x, y) ↦ k(x - y) f̃(y) ψ(x)` is integrable on `C_c × ℝ²`
(weighted Cauchy-Schwarz: the majorant `A(x) = ∫ |k(x - y)| |f̃(y)| dy` lies in `X_{-m,c}` and
`ψ` lies in `X_{m,c}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjUnf_integrable_mul {c m : ℝ} {a : ℝ × ℝ → ℝ}
    (ha : MemLp a 2 (B0579.cellMeasure c (-m))) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    Integrable (fun x => a x * ψ x) (volume.restrict (B0579.cell c)) := by
  have hnorm : eLpNorm (B0579.mulFun m ψ) 2 (B0579.cellMeasure c (-m)) =
      eLpNorm ψ 2 (B0579.cellMeasure c m) := by
    have h2 : (m - -m) / 2 = m := by ring
    have := B0579.eLpNorm_mulFun c m (-m) ψ
    rw [h2] at this
    exact this
  have hmeas : Continuous (B0579.mulFun m ψ) :=
    (B0579.continuous_jb_rpow m).mul hψ.continuous
  have hAm : MemLp (B0579.mulFun m ψ) 2 (B0579.cellMeasure c (-m)) :=
    ⟨hmeas.aestronglyMeasurable, by rw [hnorm]; exact (hψ.memLp m).2⟩
  have hint := ha.integrable_mul hAm
  have hint' := (integrable_withDensity_iff_integrable_smul
    (B0579.measurable_density (-m))).1 hint
  refine Integrable.congr hint' (Eventually.of_forall fun x => ?_)
  have hp : B0579.jb x ^ (-m) * B0579.jb x ^ m = 1 := by
    rw [← Real.rpow_add (B0579.jb_pos x)]
    simp
  simp only [NNReal.smul_def, B0579.coe_density, B0579.mulFun, smul_eq_mul, Pi.mul_apply]
  linear_combination (a x * ψ x) * hp

theorem adjKerUnfold_int {c m : ℝ} {k : ℝ × ℝ → ℝ} {M : ℝ} (hc : 0 < c) (hk : Continuous k)
    (hY : KerYoung c m k M) (w : AdjX c m) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k (p.1 - p.2) : ℂ) * perRep c (⇑w) p.2 * (ψ p.1 : ℂ))
      ((volume.restrict (B0579.cell c)).prod volume) := by
  classical
  have hgm : StronglyMeasurable (perRep c (⇑w)) :=
    stronglyMeasurable_perRep hc (Lp.stronglyMeasurable w)
  have hF : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ‖k (p.1 - p.2)‖ₑ * ‖perRep c (⇑w) p.2‖ₑ) :=
    ((hk.comp (continuous_fst.sub continuous_snd)).measurable.enorm).mul
      ((hgm.measurable.comp measurable_snd).enorm)
  have hAmeas : Measurable (fun x : ℝ × ℝ => ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) :=
    hF.lintegral_prod_right'
  have hfin : eLpNorm (fun x : ℝ × ℝ => ∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) 2
      (B0579.cellMeasure c (-m)) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_lt_top w).ne) (hY w)
  have hae := UnforcedLeray.B0295.ae_lt_top_of_eLpNorm_ne_top hAmeas.aemeasurable
    (by norm_num) (by norm_num) hfin
  have hae' : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) < ⊤ :=
    (B0579.ac_cellMeasure c (-m)).ae_le hae
  have ha : MemLp (fun x : ℝ × ℝ => (∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ).toReal) 2
      (B0579.cellMeasure c (-m)) := by
    refine ⟨hAmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_enorm fun x => ?_) hfin.lt_top
    rw [enorm_eq_self]
    exact (Real.enorm_eq_ofReal ENNReal.toReal_nonneg).le.trans ENNReal.ofReal_toReal_le
  have hI := adjUnf_integrable_mul ha hψ
  have hmeasF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (k (p.1 - p.2) : ℂ) * perRep c (⇑w) p.2 * (ψ p.1 : ℂ))
      ((volume.restrict (B0579.cell c)).prod volume) := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (k (p.1 - p.2) : ℂ)) :=
      Complex.measurable_ofReal.comp (hk.measurable.comp (measurable_fst.sub measurable_snd))
    have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (ψ p.1 : ℂ)) :=
      Complex.measurable_ofReal.comp (hψ.continuous.measurable.comp measurable_fst)
    exact ((h1.mul (hgm.measurable.comp measurable_snd)).mul h2).aestronglyMeasurable
  refine ⟨hmeasF1, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeasF1.enorm]
  have hcast : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ‖r‖ₑ := fun r => by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
  have hinner : ∀ x : ℝ × ℝ, ∫⁻ y, ‖(k (x - y) : ℂ) * perRep c (⇑w) y * (ψ x : ℂ)‖ₑ =
      (∫⁻ y, ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) * ‖ψ x‖ₑ := by
    intro x
    have hm : Measurable (fun y : ℝ × ℝ => ‖k (x - y)‖ₑ * ‖perRep c (⇑w) y‖ₑ) :=
      ((hk.measurable.comp (measurable_const.sub measurable_id)).enorm).mul hgm.measurable.enorm
    rw [← lintegral_mul_const _ hm]
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, enorm_mul, hcast, hcast]
  simp only [hinner]
  have hI2 := hI.hasFiniteIntegral
  unfold HasFiniteIntegral at hI2
  refine lt_of_le_of_lt (le_of_eq ?_) hI2
  refine lintegral_congr_ae ?_
  filter_upwards [hae'] with x hx
  rw [enorm_mul, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

end UnforcedLeray.Short.IIIa
