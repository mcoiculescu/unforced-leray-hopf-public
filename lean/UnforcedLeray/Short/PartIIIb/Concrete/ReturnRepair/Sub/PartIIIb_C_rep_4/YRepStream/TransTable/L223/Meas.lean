import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.L223.OutMaj
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.PointL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1

/-!
# `L223/Meas`: Minkowski for the phase norm and measurability of the transition majorant
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace L223

theorem ltauLq_add_le {P q : ℝ} (hq : 1 ≤ q) {f f' : ℝ → Space → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hf' : Measurable (Function.uncurry f')) :
    IIIa.ltauLq P q (fun τ y => f τ y + f' τ y) ≤ IIIa.ltauLq P q f + IIIa.ltauLq P q f' := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hm : ∀ {h : ℝ → Space → ℝ≥0∞}, Measurable (Function.uncurry h) →
      Measurable (fun τ => lqNorm q (h τ)) := by
    intro h hh
    have h1 : Measurable (fun p : ℝ × Space => h p.1 p.2 ^ q) := hh.pow_const _
    have h2 := h1.lintegral_prod_right' (ν := (volume : Measure Space))
    exact h2.pow_const _
  have hpt : ∀ τ, lqNorm q (fun y => f τ y + f' τ y) ≤ lqNorm q (f τ) + lqNorm q (f' τ) := by
    intro τ
    unfold lqNorm
    exact ENNReal.lintegral_Lp_add_le
      (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (hf'.comp (measurable_const.prodMk measurable_id)).aemeasurable hq
  rw [← ltauAt_lqNorm_eq, ← ltauAt_lqNorm_eq, ← ltauAt_lqNorm_eq]
  refine (IIIa.ltauAt_mono P (fun τ => hpt τ)).trans ?_
  exact IIIa.ltauAt_add_le P (hm hf) (hm hf')

theorem measurable_outMaj3 (a D : ℝ) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × ℝ × ℝ => outMaj a D g p.1 p.2.1 p.2.2) := by
  have h1 : Measurable (Function.uncurry (IIIa.sepDom a 0 D g)) := sd_measurable_sepDom a 0 D g hg
  have h2 : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ => (q.1.1, (!₂[q.2, 0, q.1.2.2] : Space))) := by
    refine (measurable_fst.comp measurable_fst).prodMk ?_
    have : Continuous (fun q : (ℝ × ℝ × ℝ) × ℝ => (!₂[q.2, 0, q.1.2.2] : Space)) := by
      refine (PiLp.continuous_toLp 2 _).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp <;> fun_prop
    exact this.measurable
  have hr : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hρ : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ => q.2) := measurable_snd
  have h3 : Measurable (fun q : (ℝ × ℝ × ℝ) × ℝ =>
      if q.1.2.1 < q.2 then ENNReal.ofReal q.2 *
        (Function.uncurry (IIIa.sepDom a 0 D g)) (q.1.1, (!₂[q.2, 0, q.1.2.2] : Space)) else 0) :=
    Measurable.ite (measurableSet_lt hr hρ)
      ((ENNReal.measurable_ofReal.comp hρ).mul (h1.comp h2)) measurable_const
  have h4 := h3.lintegral_prod_right' (ν := (volume : Measure ℝ))
  convert h4 using 1
  funext p
  unfold outMaj
  rw [← lintegral_indicator measurableSet_Ioi]
  congr 1

theorem measurableSet_ann (ν R : ℝ) : MeasurableSet (streamAnn ν R) := by
  have : streamAnn ν R = ϱ ⁻¹' Icc (R * Real.sqrt ν) (R * Real.sqrt (5 * ν / 4)) := by
    ext y; simp [streamAnn]
  rw [this]
  exact measurable_ϱ measurableSet_Icc

end L223

end UnforcedLeray.Short.PartIIIb.Concrete

end
