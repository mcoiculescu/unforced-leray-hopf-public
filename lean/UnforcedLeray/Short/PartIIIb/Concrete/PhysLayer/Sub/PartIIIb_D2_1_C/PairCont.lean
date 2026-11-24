import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_3
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The phase measure `(Lebesgue on (0,P]) ⊗ Lebesgue` on `ℝ × ℝ³`. -/
abbrev muP (P : ℝ) : Measure (ℝ × Space) :=
  ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)

theorem dotL_norm_le (a b : CVec3) : ‖dotL a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [dotL_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  calc ‖∑ i : Fin 3, a i * b i‖ ≤ ∑ i : Fin 3, ‖a i‖ * ‖b i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp [norm_mul]
    _ ≤ √(∑ i : Fin 3, ‖a i‖ ^ 2) * √(∑ i : Fin 3, ‖b i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem dotL_enorm_le (a b : CVec3) : ‖dotL a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (dotL_norm_le a b)

theorem dotL_cont : Continuous fun p : CVec3 × CVec3 => dotL p.1 p.2 :=
  dotL.continuous₂

theorem muP_ac (P : ℝ) : muP P ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod Measure.restrict_le_self.absolutelyContinuous
    (le_refl (volume : Measure Space)).absolutelyContinuous

theorem aesm_muP {P : ℝ} {h : ℝ × Space → CVec3} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable h (muP P) :=
  hh.mono_ac (muP_ac P)

theorem phaseLpNorm_eq (P : ℝ) (h : ℝ × Space → CVec3) (hh : AEStronglyMeasurable h volume) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 h
      = (ENNReal.ofReal P⁻¹ * ∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) := by
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  have hm : AEMeasurable (fun z => ‖h z‖ₑ ^ (2 : ℝ)) (muP P) :=
    AEMeasurable.pow_const (AEStronglyMeasurable.enorm (aesm_muP hh)) 2
  rw [lintegral_prod _ hm]

theorem lint_lt_top_of_phaseLpNorm {P : ℝ} (hP : 0 < P) {h : ℝ × Space → CVec3}
    (hh : AEStronglyMeasurable h volume)
    (hfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 h < ⊤) :
    ∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P) < ⊤ := by
  rw [phaseLpNorm_eq P h hh] at hfin
  by_contra hJt
  have hJeq := top_unique (not_lt.mp hJt)
  have hc : ENNReal.ofReal P⁻¹ ≠ 0 := by simp [hP]
  rw [hJeq, ENNReal.mul_top hc, ENNReal.top_rpow_of_pos (by norm_num)] at hfin
  exact lt_irrefl _ hfin

theorem lintegral_dot_le (P : ℝ) (h w : ℝ × Space → CVec3)
    (hh : AEStronglyMeasurable h volume) (hw : AEStronglyMeasurable w volume) :
    ∫⁻ z, ‖dotL (h z) (w z)‖ₑ ∂(muP P)
      ≤ (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)
        * (∫⁻ z, ‖w z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf : AEMeasurable (fun z => ‖h z‖ₑ) (muP P) := AEStronglyMeasurable.enorm (aesm_muP hh)
  have hg : AEMeasurable (fun z => ‖w z‖ₑ) (muP P) := AEStronglyMeasurable.enorm (aesm_muP hw)
  calc ∫⁻ z, ‖dotL (h z) (w z)‖ₑ ∂(muP P)
      ≤ ∫⁻ z, (fun z => ‖h z‖ₑ) z * (fun z => ‖w z‖ₑ) z ∂(muP P) :=
        lintegral_mono fun z => dotL_enorm_le _ _
    _ ≤ _ := ENNReal.lintegral_mul_le_Lp_mul_Lq (muP P) hpq hf hg

set_option maxHeartbeats 1000000 in
theorem dot_integrable {P : ℝ} (hP : 0 < P) {h w : ℝ × Space → CVec3}
    (hh : UnforcedLeray.Short.IIb.IsInYr P 2 h) (hw : UnforcedLeray.Short.IIb.IsInYr P 2 w) :
    Integrable (fun z => dotL (h z) (w z)) (muP P) := by
  have hm : AEStronglyMeasurable (fun z => dotL (h z) (w z)) volume :=
    dotL.aestronglyMeasurable_comp₂ hh.meas hw.meas
  refine ⟨hm.mono_ac (muP_ac P), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_dot_le P h w hh.meas hw.meas) ?_
  have hI := lint_lt_top_of_phaseLpNorm hP hh.meas hh.finite
  have hJ := lint_lt_top_of_phaseLpNorm hP hw.meas hw.finite
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hI.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ.ne)

theorem pair_eq_integral (P : ℝ) (h w : ℝ × Space → CVec3)
    (hint : Integrable (fun z => dotL (h z) (w z)) (muP P)) :
    pairF P h w = (P⁻¹ : ℝ) • ∫ z, dotL (h z) (w z) ∂(muP P) := by
  unfold pairF phaseInt
  rw [integral_prod _ hint]

theorem ennreal_identity (c a b : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    c * (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) = (c * a) ^ (1 / 2 : ℝ) * (c * b) ^ (1 / 2 : ℝ) := by
  have hcc : c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c := by
    rw [← ENNReal.rpow_add _ _ hc0 hct]
    norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  conv_lhs => rw [← hcc]
  ring

theorem pair_enorm_le {P : ℝ} (hP : 0 < P) (h w : ℝ × Space → CVec3)
    (hh : AEStronglyMeasurable h volume) (hw : AEStronglyMeasurable w volume)
    (hint : Integrable (fun z => dotL (h z) (w z)) (muP P)) :
    ‖pairF P h w‖ₑ ≤ UnforcedLeray.Short.IIb.phaseLpNorm P 2 h
      * UnforcedLeray.Short.IIb.phaseLpNorm P 2 w := by
  rw [pair_eq_integral P h w hint, phaseLpNorm_eq P h hh, phaseLpNorm_eq P w hw]
  rw [enorm_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hP.le)]
  have h1 : ‖∫ z, dotL (h z) (w z) ∂(muP P)‖ₑ ≤ ∫⁻ z, ‖dotL (h z) (w z)‖ₑ ∂(muP P) :=
    enorm_integral_le_lintegral_enorm _
  have hc0 : ENNReal.ofReal P⁻¹ ≠ 0 := by simp [hP]
  have hct : ENNReal.ofReal P⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ENNReal.ofReal P⁻¹ * ‖∫ z, dotL (h z) (w z) ∂(muP P)‖ₑ
      ≤ ENNReal.ofReal P⁻¹ * ((∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)
          * (∫⁻ z, ‖w z‖ₑ ^ (2 : ℝ) ∂(muP P)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans (lintegral_dot_le P h w hh hw)) (zero_le)
    _ = _ := ennreal_identity _ _ _ hc0 hct

theorem fwuPairCont : FWUPairCont := by
  intro P hP g f w hg hf hw hconv
  have hint : ∀ n, Integrable (fun z => dotL (g n z) (w z)) (muP P) :=
    fun n => dot_integrable hP (hg n) hw
  have hintf : Integrable (fun z => dotL (f z) (w z)) (muP P) :=
    dot_integrable hP hf hw
  have hdiffint : ∀ n, Integrable (fun z => dotL (g n z - f z) (w z)) (muP P) := by
    intro n
    refine ((hint n).sub hintf).congr (ae_of_all _ fun z => ?_)
    simp
  have hdiff : ∀ n, pairF P (g n) w = pairF P f w + pairF P (fun x => g n x - f x) w := by
    intro n
    rw [pair_eq_integral P _ w (hint n), pair_eq_integral P _ w hintf,
      pair_eq_integral P (fun x => g n x - f x) w (hdiffint n)]
    have key : ∫ z, dotL (g n z - f z) (w z) ∂(muP P)
        = ∫ z, dotL (g n z) (w z) ∂(muP P) - ∫ z, dotL (f z) (w z) ∂(muP P) := by
      rw [← integral_sub (hint n) hintf]
      congr 1
      funext z
      simp
    rw [key, smul_sub]
    abel
  have hx : Tendsto (fun n => pairF P (fun x => g n x - f x) w) atTop (𝓝 0) := by
    have hBtop : UnforcedLeray.Short.IIb.phaseLpNorm P 2 w ≠ ⊤ := hw.finite.ne
    have hU : Tendsto (fun n => UnforcedLeray.Short.IIb.phaseLpNorm P 2
        (fun x => g n x - f x) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 w) atTop
        (𝓝 (0 * UnforcedLeray.Short.IIb.phaseLpNorm P 2 w)) :=
      ENNReal.Tendsto.mul_const hconv (Or.inr hBtop)
    rw [zero_mul] at hU
    have hev : ∀ᶠ n in atTop, UnforcedLeray.Short.IIb.phaseLpNorm P 2
        (fun x => g n x - f x) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 w < ⊤ :=
      hU.eventually (gt_mem_nhds ENNReal.zero_lt_top)
    have hlim : Tendsto (fun n => (UnforcedLeray.Short.IIb.phaseLpNorm P 2
        (fun x => g n x - f x) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 w).toReal) atTop
        (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hU
      simpa only [Function.comp_def, ENNReal.toReal_zero] using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev] with n hn
    have hmeas : AEStronglyMeasurable (fun x => g n x - f x) volume :=
      (hg n).meas.sub hf.meas
    have hle := pair_enorm_le hP (fun x => g n x - f x) w hmeas hw.meas (hdiffint n)
    have hnorm : ‖pairF P (fun x => g n x - f x) w‖
        = (‖pairF P (fun x => g n x - f x) w‖ₑ).toReal := by
      simp
    rw [hnorm]
    exact ENNReal.toReal_mono hn.ne hle
  have hfinal := (tendsto_const_nhds (x := pairF P f w)).add hx
  rw [add_zero] at hfinal
  exact Tendsto.congr (fun n => (hdiff n).symm) hfinal

end UnforcedLeray.Short.PartIIIb.Concrete
