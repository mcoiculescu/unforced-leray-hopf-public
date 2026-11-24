import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1_aux

/-!
# Leaf `PartII-b:T11/2/2/4/3` (`DualRemMeasurable`)

Source: `the November 2 reference manuscript`
lines 1923-1927.  `dualRem` is built from `fderiv`s of fixed functions (measurable for arbitrary
functions) and the continuous cutoff `φ`; `dualG` is measurable since `H` is smooth on `σ > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cpdC_measurable (j : Fin 3) (f : Coord → ℂ) : Measurable (cpdC j f) :=
  measurable_fderiv_apply_const ℝ f (cdir j)

theorem perpC_measurable (ψ : Coord → ℂ) (i : Fin 2) : Measurable (fun x => perpC ψ x i) := by
  fin_cases i
  · simpa [perpC] using cpdC_measurable 2 ψ
  · exact (cpdC_measurable 1 ψ).neg

theorem flatTransposeC_perpC_measurable (ν : ℝ) (μ : ℂ) (ψ : Coord → ℂ) (i : Fin 2) :
    Measurable (fun x => flatTransposeC ν μ (perpC ψ) x i) := by
  unfold flatTransposeC
  have h1 : Measurable (fun x : Coord => (x.1 : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_fst
  have h0 := cpdC_measurable 0 (fun y => perpC ψ y i)
  have h1' := cpdC_measurable 1 (fun y => cpdC 1 (fun z => perpC ψ z i) y)
  have h2' := cpdC_measurable 2 (fun y => cpdC 2 (fun z => perpC ψ z i) y)
  have h3 := perpC_measurable ψ i
  have h4 : Measurable (fun _ : Coord => ((ν : ℂ))) := measurable_const
  have h5 : Measurable (fun _ : Coord => (μ - 1)) := measurable_const
  exact ((h5.mul h3).sub (h1.mul h0)).sub ((h4.mul h1).mul (h1'.add h2'))

theorem dualRem_measurable (ν : ℝ) (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ)
    (hφ : Measurable φ) (i : Fin 2) : Measurable (fun x => dualRem ν μ χ φ H s L x i) := by
  unfold dualRem
  have h2 : Measurable (fun x : Coord => (φ (x.2.2 / L) : ℂ)) :=
    Complex.measurable_ofReal.comp (hφ.comp (measurable_snd.comp measurable_snd |>.div_const L))
  exact (flatTransposeC_perpC_measurable ν μ _ i).sub
    (h2.mul (flatTransposeC_perpC_measurable ν μ _ i))

/-- `ageμ c 0 ≪ ageμ c e`: the weights differ by a positive density on `s > 0`. -/
theorem ageμ_zero_ac (c e : ℝ) : Axi.ageμ c 0 ≪ Axi.ageμ c e := by
  have : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  have hw : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ e))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)).aemeasurable
  have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (s ^ e) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs e)).ne'
  have h1 : (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (s ^ (0 : ℝ))) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ e) :=
    (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous' hw hne)
  exact h1.prod (Measure.AbsolutelyContinuous.refl (Cyl.avgμ c))

theorem dualG_measurable {c ν r' : ℝ} {H : Coord → ℝ} {s : ℝ} {χ : ℝ → ℝ}
    (hH : HeatSol c ν r' H) (hχ : DFChi s χ) (μ : Measure Coord) :
    AEStronglyMeasurable (fun x => dualG χ H s x) μ := by
  set U : Set Coord := {z | z.1 < s} with hU
  have hUo : IsOpen U := isOpen_lt continuous_fst continuous_const
  set g : Coord → ℝ := fun z => H (s - z.1, z.2) with hg
  have hcd : ContDiffOn ℝ ∞ g U := by
    refine hH.smooth.comp (f := fun z : Coord => (s - z.1, z.2)) (by fun_prop) ?_
    intro z hz
    exact ⟨show 0 < s - z.1 from sub_pos.2 hz, mem_univ _⟩
  set K : Set Coord := Prod.fst ⁻¹' tsupport χ with hK
  have hKm : MeasurableSet K := (isClosed_tsupport χ).preimage continuous_fst |>.measurableSet
  have hKU : K ⊆ U := fun z hz => (hχ.2.2 hz).2
  set F : Coord → ℝ := fun x => ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n g x‖ with hF
  have hFc : ContinuousOn F U := by
    refine continuousOn_finsetSum _ (fun n _ => ?_)
    have := hcd.continuousOn_iteratedFDerivWithin (m := n) (n := ∞) (by exact_mod_cast le_top)
      hUo.uniqueDiffOn
    exact (this.congr (iteratedFDerivWithin_of_isOpen n hUo).symm).norm
  have heq : (fun x => dualG χ H s x) = K.indicator F := by
    funext x
    unfold dualG
    by_cases hx : x ∈ K
    · have : x.1 ∈ tsupport χ := hx
      simp [Set.indicator_of_mem hx, this, hF, hg]
    · have : x.1 ∉ tsupport χ := hx
      simp [Set.indicator_of_notMem hx, this]
  rw [heq, aestronglyMeasurable_indicator_iff hKm]
  exact (hFc.mono hKU).aestronglyMeasurable hKm

theorem b_coord_aestronglyMeasurable {c r : ℝ} {b : CProf} (hb : InHr c r b) (i : Fin 2) :
    AEStronglyMeasurable (fun x => b x i) (Axi.ageμ c 0) := by
  have h : AEStronglyMeasurable b (Axi.ageμ c 0) := by
    have := hb.meas
    unfold hMeas at this
    exact this.mono_ac (ageμ_zero_ac c _)
  exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable h

theorem dualRemMeasurable : UnforcedLeray.Short.IIb.DualRemMeasurable := by
  intro c r ν μ b H s χ φ L hc hν hs hr hb hH hχ hφ
  have hφm : Measurable φ := hφ.1.continuous.measurable
  refine ⟨?_, ?_⟩
  · unfold pairC
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact (b_coord_aestronglyMeasurable hb i).mul
      (dualRem_measurable ν μ χ φ H s L hφm i).aestronglyMeasurable
  · exact (continuous_norm.comp_aestronglyMeasurable (hb.meas.mono_ac (ageμ_zero_ac c _))).mul
      (dualG_measurable hH hχ _)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualRemMeasurable
