import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MeanPart.VBound

/-!
# Mean part helper: measurability for the `sepVmu0` integrand (T17/2)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mpV3_continuous : Continuous mpV3 := by
  unfold mpV3
  fun_prop

theorem mpRho2_ae_mem : ∀ᵐ p ∂mpRho2, p.1 ∈ Ioo (0 : ℝ) 1 := by
  have h : mpRho2 {p : ℝ × ((ℝ × ℝ) × ℝ) | p.1 ∉ Ioo (0 : ℝ) 1} = 0 := by
    have : {p : ℝ × ((ℝ × ℝ) × ℝ) | p.1 ∉ Ioo (0 : ℝ) 1} =
        (Ioo (0 : ℝ) 1)ᶜ ×ˢ (univ : Set ((ℝ × ℝ) × ℝ)) := by
      ext p; simp
    rw [this, mpRho2, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl]
    simp
  exact measure_eq_zero_iff_ae_notMem.mp h |> fun h' => by
    filter_upwards [h'] with p hp
    simpa using hp

theorem mpVF_measurable (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) (x : Space) (i : Fin 3) :
    Measurable fun p => mpVF μ G p x i := by
  unfold mpVF
  have hu : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => x - p.1 • mpV3 p.2 :=
    measurable_const.sub (measurable_fst.smul (mpV3_continuous.measurable.comp measurable_snd))
  refine measurable_const.mul (((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_))
  refine Measurable.mul ?_ ?_
  · exact Complex.measurable_ofReal.comp
      ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).continuous.measurable.comp
        ((measurable_fderiv ℝ (fun x => heatLerayK0 i j x)).comp hu))
  · exact Complex.measurable_ofReal.comp ((hGm j k).comp measurable_snd)

theorem mpVF'_measurable (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) (x : Space) (i : Fin 3) :
    Measurable fun p => mpVF' μ G p x i := by
  unfold mpVF'
  have hu : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => x - p.1 • mpV3 p.2 :=
    measurable_const.sub (measurable_fst.smul (mpV3_continuous.measurable.comp measurable_snd))
  have hsum : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => ∑ j : Fin 3, ∑ k : Fin 3,
      ((G p.2.1 p.2.2 j k : ℝ) : ℂ) • (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
          (fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2)))) := by
    refine Finset.measurable_sum (M := Space →L[ℝ] ℂ) _ fun j _ =>
      Finset.measurable_sum (M := Space →L[ℝ] ℂ) _ fun k _ => ?_
    have hc : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => ((G p.2.1 p.2.2 j k : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((hGm j k).comp measurable_snd)
    have hΛ : Continuous fun A : Space →L[ℝ] (Space →L[ℝ] ℝ) => Complex.ofRealCLM.comp
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp A) := by
      fun_prop
    have hM : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => Complex.ofRealCLM.comp
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).comp
          (fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x)) (x - p.1 • mpV3 p.2))) :=
      hΛ.measurable.comp ((measurable_fderiv ℝ (fderiv ℝ (fun x => heatLerayK0 i j x))).comp hu)
    exact hc.smul hM
  have hcp : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => (p.1 : ℂ) ^ (2 * μ + 2) :=
    (Complex.measurable_ofReal.comp measurable_fst).pow_const _
  exact (hcp.smul hsum).const_smul (-2 : ℂ)

end UnforcedLeray.Short.IIIa

end
