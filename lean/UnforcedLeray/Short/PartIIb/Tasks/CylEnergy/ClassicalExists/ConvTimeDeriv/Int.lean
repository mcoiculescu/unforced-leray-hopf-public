import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_11
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRCont

/-!


Integrability of `r ↦ H_{ν(t-r)} F(r)(x)` on `[s, T]`. Source:
`the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
Route: bounded by `2 e^{ν(T-s)} B` (`HeatWBounds`); measurable since on `[s, t]` it equals the scaled
integral `∫ K_1(w) F(clamp r)(x - √(max (ν(t-r)) 0) w) dw`, continuous in `r` by dominated
continuity (clamped `F` is jointly continuous), and on `[t, T]` it equals `F r x`, continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CTDI

lemma Phi_continuous {ν s T B : ℝ} (hsT : s ≤ T) {F : ℝ → Pl → ℝ}
    (hF : ContinuousOn (fun z : ℝ × Pl => F z.1 z.2) (Icc s T ×ˢ univ))
    (hb : ∀ r ∈ Icc s T, WB B (F r)) (t : ℝ) (x : Pl) :
    Continuous (fun r : ℝ => ∫ w : Pl, heatK 1 w *
      F (CC.clampT s T r) (x - Real.sqrt (max (ν * (t - r)) 0) • w)) := by
  obtain ⟨-, hI, -, -⟩ := heatKernelMoments 1 one_pos
  have hKc := HC.heatK1_continuous
  have hFc := CC.gext_continuous hsT hF
  refine continuous_of_dominated (bound := fun w => |heatK 1 w| * B) ?_ ?_ ?_ ?_
  · intro r
    have h1 : Continuous (fun w : Pl => (r,
        x - Real.sqrt (max (ν * (t - r)) 0) • w)) :=
      continuous_const.prodMk (continuous_const.sub (by fun_prop))
    exact (hKc.mul (hFc.comp h1)).aestronglyMeasurable
  · intro r
    refine ae_of_all _ fun w => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (HC.gbound (hb _ (CC.clampT_mem hsT r)) _) (abs_nonneg _)
  · exact hI.abs.mul_const B
  · refine ae_of_all _ fun w => ?_
    have h2 : Continuous (fun r : ℝ => Real.sqrt (max (ν * (t - r)) 0)) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).max continuous_const).sqrt
    have h1 : Continuous (fun r : ℝ => (r,
        x - Real.sqrt (max (ν * (t - r)) 0) • w)) :=
      continuous_id.prodMk (continuous_const.sub (h2.smul continuous_const))
    refine continuous_const.mul ?_
    exact hFc.comp h1

end CTDI

open CTDI in
/-- **`PartII-b:T22/1/11/2`** Integrability of `r ↦ H_{ν(t-r)} F(r)(x)` on `[s, T]`. -/
theorem convTD_Int : UnforcedLeray.Short.IIb.CylPDE.ConvTD_Int := by
  intro ν s T hν hsT B F hF hb t ht x
  have hs0 : s ∈ Icc s T := ⟨le_rfl, hsT⟩
  have hB0 : 0 ≤ B := by
    have h0 := hb s hs0 0
    simp only [Prod.snd_zero, Real.cosh_zero, mul_one] at h0
    exact le_trans (abs_nonneg _) h0
  set f : ℝ → ℝ := fun r => heatSG (ν * (t - r)) (F r) x with hf
  -- boundedness
  have hbd : ∀ r ∈ Icc s T, ‖f r‖ ≤ 2 * Real.exp (ν * (T - s)) * B := by
    intro r hr
    have hE : 1 ≤ Real.exp (ν * (T - s)) := Real.one_le_exp (by nlinarith [hr.1, hr.2])
    rw [Real.norm_eq_abs]
    by_cases ha : 0 ≤ ν * (t - r)
    · have h1 := (heatWBounds B (F r) (hb r hr)).1 _ ha x
      have hc : 1 ≤ Real.cosh x.2 := Real.one_le_cosh _
      have h2 : |heatSG (ν * (t - r)) (F r) x| ≤ 2 * Real.exp (ν * (t - r)) * B := by
        nlinarith [abs_nonneg (heatSG (ν * (t - r)) (F r) x)]
      have h3 : Real.exp (ν * (t - r)) ≤ Real.exp (ν * (T - s)) :=
        Real.exp_le_exp.2 (by nlinarith [ht.1, ht.2, hr.1, hr.2])
      calc |f r| ≤ 2 * Real.exp (ν * (t - r)) * B := h2
        _ ≤ 2 * Real.exp (ν * (T - s)) * B := by gcongr
    · have hneg : ν * (t - r) ≤ 0 := (not_le.1 ha).le
      have : f r = F r x := by simp only [hf, heatSG, if_pos hneg]
      rw [this]
      have := HC.gbound (hb r hr) x
      nlinarith
  -- measurability on [s, t]
  have hmeas1 : ContinuousOn f (Icc s t) := by
    have hC := Phi_continuous (ν := ν) hsT hF.contF hb t x
    refine hC.continuousOn.congr ?_
    intro r hr
    have hrI : r ∈ Icc s T := ⟨hr.1, hr.2.trans ht.2⟩
    have hra : 0 ≤ ν * (t - r) := by nlinarith [hr.2]
    show heatSG (ν * (t - r)) (F r) x =
      ∫ w : Pl, heatK 1 w * F (CC.clampT s T r) (x - Real.sqrt (max (ν * (t - r)) 0) • w)
    rw [CC.clampT_of_mem hrI, max_eq_left hra]
    rcases hra.lt_or_eq with hp | hz
    · exact HC.heatSG_pos_eq hp (F r) x
    · have hint := (heatKernelMoments 1 one_pos).2.2.1
      rw [← hz]
      simp only [heatSG, le_refl, if_true, Real.sqrt_zero, zero_smul, sub_zero]
      rw [integral_mul_const, hint, one_mul]
  -- measurability on [t, T]
  have hmeas2 : ContinuousOn f (Icc t T) := by
    have hc : ContinuousOn (fun r : ℝ => F r x) (Icc t T) := by
      have h1 : ContinuousOn (fun r : ℝ => (r, x)) (Icc t T) :=
        (continuous_id.prodMk continuous_const).continuousOn
      have h2 : MapsTo (fun r : ℝ => (r, x)) (Icc t T) (Icc s T ×ˢ univ) :=
        fun r hr => ⟨⟨ht.1.trans hr.1, hr.2⟩, mem_univ _⟩
      exact hF.contF.comp h1 h2
    refine hc.congr ?_
    intro r hr
    have hneg : ν * (t - r) ≤ 0 := by nlinarith [hr.1]
    simp only [hf, heatSG, if_pos hneg]
  have hm : AEStronglyMeasurable f (volume.restrict (Ioc s T)) := by
    have hsub : Ioc s T ⊆ Icc s t ∪ Icc t T := by
      intro r hr
      rcases le_total r t with h | h
      · exact Or.inl ⟨hr.1.le, h⟩
      · exact Or.inr ⟨h, hr.2⟩
    refine AEStronglyMeasurable.mono_measure ((aestronglyMeasurable_union_iff).2
      ⟨hmeas1.aestronglyMeasurable measurableSet_Icc,
        hmeas2.aestronglyMeasurable measurableSet_Icc⟩) (Measure.restrict_mono hsub le_rfl)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hsT]
  refine Integrable.mono' (integrable_const (2 * Real.exp (ν * (T - s)) * B)) hm ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact ae_of_all _ fun r hr => hbd r ⟨hr.1.le, hr.2⟩

end UnforcedLeray.Short.IIb.CylPDE
