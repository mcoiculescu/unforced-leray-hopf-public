import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Strip

/-!
# Part III-a, `PartIII-a:T21/3/11`: a.e. invariance of linearised flows

Source of record: `the November 2 reference manuscript`, the full forward train
estimate (existence of `U(s,t)`). Statement `FlowCongrAE` is in `Sub/T21_3.lean` (amended by the

`ω t` and the statement is false).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa

theorem flowIntegrand_congr_ae {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {ω ω' : ℝ × ℝ → ℂ} {u u' : ℝ × ℝ → Fin 2 → ℂ} (r : ℝ) (φ : ℝ × ℝ → ℝ)
    (hω : ω =ᵐ[volume.restrict (B0579.cell c)] ω')
    (hu : u =ᵐ[volume.restrict (B0579.cell c)] u') :
    flowIntegrand tr ω u r φ =ᵐ[volume.restrict (B0579.cell c)] flowIntegrand tr ω' u' r φ := by
  filter_upwards [hω, hu] with x h1 h2
  unfold flowIntegrand
  rw [h1, h2]

theorem isBiotSavart_congr_ae {c : ℝ} {ω ω' : ℝ × ℝ → ℂ} {u u' : ℝ × ℝ → Fin 2 → ℂ}
    (hω : ω =ᵐ[volume.restrict (B0579.cell c)] ω')
    (hu : u =ᵐ[volume.restrict (B0579.cell c)] u') (h : IsBiotSavart c ω u) :
    IsBiotSavart c ω' u' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).ae_eq ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · filter_upwards [hu] with x hx using by rw [hx]
  · rw [← h2 ψ hψ]
    refine integral_congr_ae ?_
    filter_upwards [hu] with x hx
    rw [hx]
  · calc ∫ x in B0579.cell c, ω' x * (ψ x : ℂ) = ∫ x in B0579.cell c, ω x * (ψ x : ℂ) := by
          refine integral_congr_ae ?_
          filter_upwards [hω] with x hx
          rw [hx]
      _ = _ := h3 ψ hψ
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [hu] with x hx
          rw [hx]

theorem flowCongrAE : FlowCongrAE := by
  unfold FlowCongrAE
  intro ν c m tr t T f f' ω ω' u u' htT h hf hω hu
  have hμ : ∀ s ∈ Icc t T, ω' s =ᵐ[volume.restrict (B0579.cell c)] ω s :=
    fun s hs => (hω s hs).symm
  have hint : ∀ r ∈ Icc t T, ∀ φ,
      (∫ x in B0579.cell c, flowIntegrand tr (ω' r) (u' r) r φ x) =
        ∫ x in B0579.cell c, flowIntegrand tr (ω r) (u r) r φ x := fun r hr φ =>
    (integral_congr_ae (flowIntegrand_congr_ae tr r φ (hω r hr) (hu r hr))).symm
  exact
    { initial := by
        have := hμ t ⟨le_rfl, htT⟩
        exact this.trans (h.initial.trans hf)
      memX := fun s hs => (h.memX s hs).ae_eq ((B0579.cellMeasure_ac c m).ae_eq (hω s hs))
      strongCont := fun s hs => by
        refine (h.strongCont s hs).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s' hs'
        unfold xNorm
        refine eLpNorm_congr_ae ?_
        have a1 := (B0579.cellMeasure_ac c m).ae_eq (hω s' hs')
        have a2 := (B0579.cellMeasure_ac c m).ae_eq (hω s hs)
        filter_upwards [a1, a2] with x h1 h2
        simp [h1, h2]
      biotSavart := fun s hs =>
        isBiotSavart_congr_ae (hω s hs) (hu s hs) (h.biotSavart s hs)
      integrable := fun φ hφ r hr =>
        (h.integrable φ hφ r hr).congr_fun_ae (flowIntegrand_congr_ae tr r φ (hω r hr) (hu r hr))
      timeIntegrable := fun φ hφ s hs => by
        have h0 := h.timeIntegrable φ hφ s hs
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1] at h0 ⊢
        refine h0.congr_fun (fun r hr => ?_) measurableSet_Ioc
        exact (hint r ⟨hr.1.le, hr.2.trans hs.2⟩ φ).symm
      weak := fun φ hφ s hs => by
        have e1 : (∫ x in B0579.cell c, ω' s x * (φ x : ℂ)) =
            ∫ x in B0579.cell c, ω s x * (φ x : ℂ) := by
          refine integral_congr_ae ?_
          filter_upwards [hω s hs] with x hx
          rw [hx]
        have e2 : (∫ x in B0579.cell c, f' x * (φ x : ℂ)) =
            ∫ x in B0579.cell c, f x * (φ x : ℂ) := by
          refine integral_congr_ae ?_
          filter_upwards [hf] with x hx
          rw [hx]
        have e3 : (∫ r in t..s, ∫ x in B0579.cell c, flowIntegrand tr (ω' r) (u' r) r φ x) =
            ∫ r in t..s, ∫ x in B0579.cell c, flowIntegrand tr (ω r) (u r) r φ x := by
          refine intervalIntegral.integral_congr (fun r hr => ?_)
          rw [uIcc_of_le hs.1] at hr
          exact hint r ⟨hr.1, hr.2.trans hs.2⟩ φ
        rw [e1, e2, e3]
        exact h.weak φ hφ s hs }

end UnforcedLeray.Short.IIIa.Exist
