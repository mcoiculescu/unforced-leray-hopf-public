import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_2

/-!
# `PartIII-b:C/rep/2/5/2`: measurability of the three slice densities `WGXMeas`

Source `the November 2 reference manuscript` 3622-3647, 4171-4192.

`sepX0` is jointly measurable in `(τ, y)` (`sepWre_measurable`), so the order-zero density is
measurable.  The first derivative density is measurable for any function (`measurable_fderiv`),
and the outward primitive is jointly measurable (`outPrim_measurable`) on the annulus.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

set_option maxHeartbeats 1600000 in
/-- A slice of a jointly measurable map is measurable. -/
theorem measurable_slice_gen {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α × β → γ) (hf : Measurable f) (a : α) :
    Measurable fun b : β => f (a, b) :=
  hf.comp (measurable_const.prodMk measurable_id)

set_option maxHeartbeats 1600000 in
theorem wgxMeas : WGXMeas := by
  intro ν μ R P hν hR hP T hT hSM τ
  have hTm : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j := hT.measurable
  -- joint measurability of the separated `X₀`
  have hX0 : Measurable (fun q : ℝ × Space => sepX0 ν μ T q.1 q.2) := by
    have hc : ∀ i : Fin 3, Measurable (fun q : ℝ × Space =>
        (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i - IIIa.sepW ν ((μ : ℂ) + 1) T q.2 q.1 i).re) := by
      intro i
      exact Complex.measurable_re.comp
        ((T8_1.measurable_sepW_comp ν (μ : ℂ) T i hTm).sub
          (T8_1.measurable_sepW_comp ν ((μ : ℂ) + 1) T i hTm))
    have hv : Measurable (fun q : ℝ × Space => fun i : Fin 3 =>
        (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i - IIIa.sepW ν ((μ : ℂ) + 1) T q.2 q.1 i).re) :=
      measurable_pi_lambda _ fun i => hc i
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hv
  have hX0τ : Measurable (fun y : Space => sepX0 ν μ T τ y) :=
    measurable_slice_gen (fun q : ℝ × Space => sepX0 ν μ T q.1 q.2) hX0 τ
  have hset : MeasurableSet {y : Space | R * Real.sqrt ν ≤ ϱ y} :=
    measurableSet_le measurable_const continuous_ϱ.measurable
  -- order one: `‖iteratedFDeriv 1 f y‖ = ‖fderiv f y‖` is measurable for any `f`
  have hJ1 : Measurable (wgxJet 1 ν μ (R * Real.sqrt ν) T τ) := by
    unfold wgxJet
    refine Measurable.ite hset ?_ measurable_const
    have e1 : ∀ y : Space, ‖iteratedFDeriv ℝ 1 (sepX0 ν μ T τ) y‖ₑ =
        ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ := by
      intro y
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact congrArg (fun r : NNReal => (r : ENNReal)) (NNReal.eq (norm_iteratedFDeriv_one _))
    have hd : Measurable (fun y : Space => ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ) :=
      (measurable_fderiv ℝ (sepX0 ν μ T τ)).enorm
    exact (funext e1 ▸ hd : Measurable (fun y : Space => ‖iteratedFDeriv ℝ 1 (sepX0 ν μ T τ) y‖ₑ))
  -- order zero: `‖iteratedFDeriv 0 f y‖ = ‖f y‖` and `f = sepX0 τ` is measurable
  have hJ0 : Measurable (wgxJet 0 ν μ (R * Real.sqrt ν) T τ) := by
    unfold wgxJet
    refine Measurable.ite hset ?_ measurable_const
    have e0 : ∀ y : Space, ‖iteratedFDeriv ℝ 0 (sepX0 ν μ T τ) y‖ₑ =
        ‖sepX0 ν μ T τ y‖ₑ := by
      intro y
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact congrArg (fun r : NNReal => (r : ENNReal)) (NNReal.eq norm_iteratedFDeriv_zero)
    have hd : Measurable (fun y : Space => ‖sepX0 ν μ T τ y‖ₑ) := hX0τ.enorm
    exact (funext e0 ▸ hd : Measurable (fun y : Space => ‖iteratedFDeriv ℝ 0 (sepX0 ν μ T τ) y‖ₑ))
  -- the outward primitive on the annulus
  have hPsi : Measurable (wgxPsi ν μ R T τ) := by
    unfold wgxPsi
    have hO : Measurable fun q : ℝ × ℝ × ℝ => outPrim (sepX0 ν μ T) q.1 q.2.1 q.2.2 :=
      outPrim_measurable hX0
    have hcoord : Measurable fun v : Space => v 2 :=
      (measurable_pi_apply 2).comp (PiLp.continuous_ofLp 2 _).measurable
    have hmap : Measurable fun y : Space => ((τ, ϱ y, y 2) : ℝ × ℝ × ℝ) :=
      measurable_const.prodMk (continuous_ϱ.measurable.prodMk hcoord)
    have hM : Measurable fun y : Space => outPrim (sepX0 ν μ T) τ (ϱ y) (y 2) :=
      hO.comp hmap
    have hS : MeasurableSet (streamAnn ν R) := by
      unfold streamAnn
      rw [Set.ofPred_and]
      exact (measurableSet_le measurable_const continuous_ϱ.measurable).inter
        (measurableSet_le continuous_ϱ.measurable measurable_const)
    exact Measurable.indicator (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hM)) hS
  exact ⟨hJ1.aemeasurable, hJ0.aemeasurable, hPsi.aemeasurable⟩

end UnforcedLeray.Short.PartIIIb.Concrete

end
