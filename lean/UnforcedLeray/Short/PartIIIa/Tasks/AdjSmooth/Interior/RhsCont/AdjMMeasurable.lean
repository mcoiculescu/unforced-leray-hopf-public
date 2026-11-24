import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.FieldDiffSmall
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PdEcCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PairInt

/-!
# `PartIII-a:T21/2/7/2/1/1/3/4`: measurability of the adjoint multiplier (`AdjMMeasurable`)

Source: `the November 2 reference manuscript` lines 3052-3058.
For `r ≥ 0`, the velocity `v(r, ·)`, the cylinder test `ψ` with its derivatives, and `∂_j E_c(r)`
are continuous; `uψ j` is a.e. strongly measurable on the cell since `uψ j - meanShear ∈ L²`
and the mean shear is measurable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem adjMMeasurable : UnforcedLeray.Short.IIIa.AdjMMeasurable := by
  unfold UnforcedLeray.Short.IIIa.AdjMMeasurable
  intro ν hν hν1 tr ψ uψ hψ hu r hr
  have hvc : ∀ j : Fin 2, Continuous (fun x : ℝ × ℝ => tr.v r x j) := by
    intro j
    have hf : ContinuousOn (fun x : ℝ × ℝ => ((r, x) : ℝ × (ℝ × ℝ))) univ :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h := (UnforcedLeray.Short.IIIa.PdEc.wComp_contDiffOn tr j).continuousOn.comp hf
      (fun x _ => ⟨hr, mem_univ x⟩)
    exact continuousOn_univ.1 h
  have hlap : Continuous (UnforcedLeray.Short.IIIa.lapP ψ) := by
    unfold UnforcedLeray.Short.IIIa.lapP
    exact ((hψ.pd 0).pd 0).continuous.add ((hψ.pd 1).pd 1).continuous
  have hpsi : ∀ j : Fin 2, Continuous (UnforcedLeray.B0579.pd j ψ) := fun j =>
    (hψ.pd j).continuous
  have hEc : ∀ j : Fin 2, Continuous
      (fun x : ℝ × ℝ => UnforcedLeray.B0579.pd j (UnforcedLeray.B0238.Ec tr r) x) := fun j =>
    UnforcedLeray.Short.IIIa.FieldDiffSmallAux.pd_Ec_cont tr hr j
  have hU : ∀ j : Fin 2, AEStronglyMeasurable (fun x : ℝ × ℝ => uψ x j)
      (volume.restrict (UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)))) := by
    intro j
    have h1 := (hu.1 j).aestronglyMeasurable
    have h2 := (UnforcedLeray.Short.IIIa.PairIntAux.ms_measurable (ν ^ (-2 : ℝ))
      (∫ y in UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ)), ψ y) j).aestronglyMeasurable
      (μ := volume.restrict (UnforcedLeray.B0579.cell (ν ^ (-2 : ℝ))))
    have h3 := h1.add h2
    refine h3.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  unfold UnforcedLeray.Short.IIIa.adjM
  exact ((((hlap.aestronglyMeasurable).const_mul ν).sub
      ((((hvc 0).mul (hpsi 0)).aestronglyMeasurable).add
        (((hvc 1).mul (hpsi 1)).aestronglyMeasurable))).sub
    (((hU 0).mul ((hEc 0).aestronglyMeasurable)).add
      ((hU 1).mul ((hEc 1).aestronglyMeasurable))))
