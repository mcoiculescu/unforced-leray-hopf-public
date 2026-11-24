import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.WreCut
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Meas

/-!
# `PartIII-b:C/rep/2/7`, measurability of the slice densities

Source 3622-3647, 4171-4192.  The densities of `Re W_μ` (orders 0, 1, and the outward primitive) and
the second-order density of `X₀` are measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wgy_sepWre_measurable {ν μ P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {rOut : ℝ}
    (hT : IIIa.IsSepSource P rOut T) :
    Measurable (fun q : ℝ × Space => sepWre ν μ T q.1 q.2) := by
  have hTm : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j := hT.measurable
  have hc : ∀ i : Fin 3, Measurable (fun q : ℝ × Space =>
      (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i).re) := by
    intro i
    exact Complex.measurable_re.comp (T8_1.measurable_sepW_comp ν (μ : ℂ) T i hTm)
  have hv : Measurable (fun q : ℝ × Space => fun i : Fin 3 =>
      (IIIa.sepW ν (μ : ℂ) T q.2 q.1 i).re) :=
    measurable_pi_lambda _ fun i => hc i
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hv

theorem wgyMeas_W (ν μ R P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (τ : ℝ) :
    AEMeasurable (wgyWJet 1 ν μ (R * Real.sqrt ν) T τ) volume ∧
      AEMeasurable (wgyWJet 0 ν μ (R * Real.sqrt ν) T τ) volume ∧
      AEMeasurable (wgyWPsi ν μ R T τ) volume := by
  have hX0 := wgy_sepWre_measurable (ν := ν) (μ := μ) hT
  have hX0τ : Measurable (fun y : Space => sepWre ν μ T τ y) :=
    measurable_slice_gen (fun q : ℝ × Space => sepWre ν μ T q.1 q.2) hX0 τ
  have hset : MeasurableSet {y : Space | R * Real.sqrt ν ≤ ϱ y} :=
    measurableSet_le measurable_const continuous_ϱ.measurable
  have hJ1 : Measurable (wgyWJet 1 ν μ (R * Real.sqrt ν) T τ) := by
    unfold wgyWJet
    refine Measurable.ite hset ?_ measurable_const
    have e1 : ∀ y : Space, ‖iteratedFDeriv ℝ 1 (sepWre ν μ T τ) y‖ₑ =
        ‖fderiv ℝ (sepWre ν μ T τ) y‖ₑ := by
      intro y
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact congrArg (fun r : NNReal => (r : ENNReal)) (NNReal.eq (norm_iteratedFDeriv_one _))
    have hd : Measurable (fun y : Space => ‖fderiv ℝ (sepWre ν μ T τ) y‖ₑ) :=
      (measurable_fderiv ℝ (sepWre ν μ T τ)).enorm
    exact (funext e1 ▸ hd : Measurable (fun y : Space => ‖iteratedFDeriv ℝ 1 (sepWre ν μ T τ) y‖ₑ))
  have hJ0 : Measurable (wgyWJet 0 ν μ (R * Real.sqrt ν) T τ) := by
    unfold wgyWJet
    refine Measurable.ite hset ?_ measurable_const
    have e0 : ∀ y : Space, ‖iteratedFDeriv ℝ 0 (sepWre ν μ T τ) y‖ₑ =
        ‖sepWre ν μ T τ y‖ₑ := by
      intro y
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      exact congrArg (fun r : NNReal => (r : ENNReal)) (NNReal.eq norm_iteratedFDeriv_zero)
    have hd : Measurable (fun y : Space => ‖sepWre ν μ T τ y‖ₑ) := hX0τ.enorm
    exact (funext e0 ▸ hd : Measurable (fun y : Space => ‖iteratedFDeriv ℝ 0 (sepWre ν μ T τ) y‖ₑ))
  have hPsi : Measurable (wgyWPsi ν μ R T τ) := by
    unfold wgyWPsi
    have hO : Measurable fun q : ℝ × ℝ × ℝ => outPrim (sepWre ν μ T) q.1 q.2.1 q.2.2 :=
      outPrim_measurable hX0
    have hcoord : Measurable fun v : Space => v 2 :=
      (measurable_pi_apply 2).comp (PiLp.continuous_ofLp 2 _).measurable
    have hmap : Measurable fun y : Space => ((τ, ϱ y, y 2) : ℝ × ℝ × ℝ) :=
      measurable_const.prodMk (continuous_ϱ.measurable.prodMk hcoord)
    have hM : Measurable fun y : Space => outPrim (sepWre ν μ T) τ (ϱ y) (y 2) :=
      hO.comp hmap
    have hS : MeasurableSet (streamAnn ν R) := by
      unfold streamAnn
      rw [Set.ofPred_and]
      exact (measurableSet_le measurable_const continuous_ϱ.measurable).inter
        (measurableSet_le continuous_ϱ.measurable measurable_const)
    exact Measurable.indicator (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hM)) hS
  exact ⟨hJ1.aemeasurable, hJ0.aemeasurable, hPsi.aemeasurable⟩

theorem wgyMeas_X2 (ν μ rIn : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) :
    AEMeasurable (wgxJet 2 ν μ rIn T τ) volume := by
  have hset : MeasurableSet {y : Space | rIn ≤ ϱ y} :=
    measurableSet_le measurable_const continuous_ϱ.measurable
  refine Measurable.aemeasurable ?_
  unfold wgxJet
  refine Measurable.ite hset ?_ measurable_const
  have e1 : ∀ y : Space, ‖iteratedFDeriv ℝ 2 (sepX0 ν μ T τ) y‖ₑ =
      ‖fderiv ℝ (fderiv ℝ (sepX0 ν μ T τ)) y‖ₑ := by
    intro y
    have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 1) (f := sepX0 ν μ T τ) (x := y)
    rw [norm_iteratedFDeriv_one] at h
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h]
  have hd : Measurable (fun y : Space => ‖fderiv ℝ (fderiv ℝ (sepX0 ν μ T τ)) y‖ₑ) :=
    (measurable_fderiv ℝ (fderiv ℝ (sepX0 ν μ T τ))).enorm
  exact (funext e1 ▸ hd : Measurable (fun y : Space => ‖iteratedFDeriv ℝ 2 (sepX0 ν μ T τ) y‖ₑ))

end UnforcedLeray.Short.PartIIIb.Concrete

end
