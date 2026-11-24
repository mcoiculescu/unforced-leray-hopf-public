import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `liftPDecay` (`PartIII-b:C/rep/8/2/pres/3/2/1/6`): reduction to the pointwise decay of `p_lift`

Source of record: `the November 2 reference manuscript`
(73 pages): 1202 (bounded train pressure), 1213-1225, 2541-2552 (large radius: unprojected
derivatives `≤ C ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`; `ϱ < R`: all-age heat expansion, arbitrary axial decay),
2697-2713 (age powers), 5274-5276.

`liftP L τ y = s p_cyl(s,q,η)`, `s = R²/ϱ²`, `η = R y₃/ϱ`.  With `N ≥ 4` the weighted bounds give,
for fixed `ν`, `|p_lift| ≲ ϱ^{-2}(1+|y₃|/ϱ)^{-4} ≲ (1+|y|)^{-2}` and
`|∇p_lift| ≲ (1+|y|)^{-4}` (large radius), and arbitrary axial decay on `ϱ < R`.

## Proved here
`liftPDecayAt_of_pointwise`: the pointwise decay `LiftPPointwiseAt` (the single missing estimate,
a Prop below) gives `LiftPDecayAt` with `r = 2` (the `L^{11/4}` bound for the gradient: `2·11/4 > 3`),
using measurability off the axis (`liftP_contDiffOn`, `pf2_physGrad_slice_contOn`) and
`integrable_one_add_norm`; `liftPDecay_of_pointwise` is its `SeqData` form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The pointwise decay of the lifted pressure** (source 1202, 1213-1225, 2541-2552, 2697-2713;
the estimate to be decomposed): at every phase there is `C ≥ 0` with
`|p_lift(τ,y)| ≤ C(1+|y|)^{-2}` and `|∇p_lift(τ,y)| ≤ C(1+|y|)^{-2}` off the axis.
Young range `0 < s ≤ 1/ν` (`ϱ ≥ R√ν`): `WJetP`/`TailW` weighted jets of `p_cyl` with `(1+|η|)^4`,
`s = R²/ϱ²`; old range `s > 1/ν` (`ϱ` small): heat-expansion decay `p_cyl = O(s^{-1})` with
arbitrary `η`-weights (2697-2713) so that `s p_cyl` and `∇(s p_cyl)` decay in `y₃`. -/
def LiftPPointwiseAt (L : ReturnLevel) : Prop :=
  ∀ τ : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ∉ axis →
    |liftP L τ y| ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) ∧
    ‖physGrad (liftP L τ) y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)

/-- A function with `|f| ≤ C(1+|y|)^{-2}` a.e. is in `L^q` for `1 ≤ q`, `3 < 2q`. -/
theorem lpd_memLp_of_decay {E : Type} [NormedAddCommGroup E] (f : Space → E)
    (hf : AEStronglyMeasurable f volume) {C q : ℝ} (hC : 0 ≤ C) (_hq1 : 1 ≤ q) (hq : 3 < 2 * q)
    (h : ∀ᵐ y ∂(volume : Measure Space), ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)) :
    MemLp f (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  have hne0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  rw [← integrable_norm_rpow_iff hf hne0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(2 * q))) volume := by
    apply integrable_one_add_norm
    simpa using hq
  refine (hint.const_mul (C ^ q)).mono' (hf.norm.aemeasurable.pow_const q).aestronglyMeasurable ?_
  filter_upwards [h] with y hy
  have h1 : 0 ≤ (1 + ‖y‖) ^ (-2 : ℝ) := by positivity
  have h2 : ‖f y‖ ^ q ≤ (C * (1 + ‖y‖) ^ (-2 : ℝ)) ^ q :=
    Real.rpow_le_rpow (norm_nonneg _) hy hq0.le
  have h3 : (C * (1 + ‖y‖) ^ (-2 : ℝ)) ^ q = C ^ q * (1 + ‖y‖) ^ (-(2 * q)) := by
    rw [Real.mul_rpow hC h1, ← Real.rpow_mul (by positivity)]
    congr 2
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact h2.trans_eq h3

theorem lpd_aesm_real {f : Space → ℝ} (hf : ContinuousOn f axisᶜ) :
    AEStronglyMeasurable f volume := by
  have h1 : AEStronglyMeasurable f ((volume : Measure Space).restrict axisᶜ) :=
    hf.aestronglyMeasurable isOpen_compl_axis.measurableSet
  have h2 : (volume : Measure Space).restrict axisᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_not_mem_axis
  rwa [h2] at h1

/-- **`LiftPDecayAt` from the pointwise decay** (source 1202, 2541-2552), `r = 2`. -/
theorem liftPDecayAt_of_pointwise (L : ReturnLevel) (h : LiftPPointwiseAt L) : LiftPDecayAt L := by
  intro τ
  obtain ⟨C, hC, hb⟩ := h τ
  have hcd := liftP_contDiffOn L L.ε_pos
  have hP : ContinuousOn (liftP L τ) axisᶜ := by
    have hmaps : MapsTo (fun y : Space => ((τ, y) : ℝ × Space)) axisᶜ offAxisSet := fun y hy => hy
    have hc : ContinuousOn (fun y : Space => ((τ, y) : ℝ × Space)) axisᶜ :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h0 := ContinuousOn.comp (g := fun x : ℝ × Space => liftP L x.1 x.2) hcd.continuousOn hc hmaps
    refine h0.congr (fun y _ => ?_)
    simp only [Function.comp_apply]
  have hG : ContinuousOn (physGrad (liftP L τ)) axisᶜ :=
    pf2_physGrad_slice_contOn (F := fun x : ℝ × Space => liftP L x.1 x.2) hcd τ
  have hae : ∀ᵐ y ∂(volume : Measure Space), y ∉ axis := ae_not_mem_axis
  refine ⟨⟨2, by norm_num, ?_⟩, ?_⟩
  · have := lpd_memLp_of_decay (liftP L τ) (lpd_aesm_real hP) hC (q := 2) (by norm_num)
      (by norm_num) (by filter_upwards [hae] with y hy; simpa using (hb y hy).1)
    simpa using this
  · have := lpd_memLp_of_decay (physGrad (liftP L τ)) (pf2_aesm_of_continuousOn hG) hC
      (q := 11 / 4) (by norm_num) (by norm_num) (by filter_upwards [hae] with y hy; exact (hb y hy).2)
    have e : ENNReal.ofReal (11 / 4 : ℝ) = (11 / 4 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp
    rwa [e] at this

/-- **`LiftPDecay` along the sequence from the pointwise decay** (source 1202, 2541-2552). -/
theorem liftPDecay_of_pointwise (D : SeqData)
    (h : ∀ᶠ n : ℕ in atTop, LiftPPointwiseAt (D.level n)) : D.LiftPDecay := by
  unfold SeqData.LiftPDecay
  filter_upwards [h] with n hn
  exact liftPDecayAt_of_pointwise _ hn

end UnforcedLeray.Short.PartIIIb.Concrete
