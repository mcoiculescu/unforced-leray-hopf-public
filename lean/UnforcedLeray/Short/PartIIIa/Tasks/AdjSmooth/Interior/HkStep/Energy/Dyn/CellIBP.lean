import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The two cell definitions agree (`B0579.cell c` and `Cyl.cell c`). -/
theorem cellIBP_cell_eq (c : ℝ) : B0579.cell c = UnforcedLeray.Cyl.cell c := by
  unfold B0579.cell UnforcedLeray.Cyl.cell
  rw [neg_div]

/-- A continuous field vanishing for `|x₂|` large is integrable on the cell. -/
theorem integrableOn_cell_cplx {c : ℝ} {F : ℝ × ℝ → ℂ} (hF : Continuous F) {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → F x = 0) : IntegrableOn F (B0579.cell c) := by
  have hv : ∀ x ∈ B0579.cell c, x ∉ B0579.box c R → F x = 0 := fun x hx hxK =>
    hR x (by
      by_contra hcon
      exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 hcon)))
  exact (hF.continuousOn.integrableOn_compact (B0579.isCompact_box c R)).of_forall_sdiff_eq_zero
    (B0579.measurableSet_cell c) (fun x hx => hv x hx.1 hx.2)

/-- The product rule in the direction `j`, and the integrability of the three pieces. -/
theorem cellIBP_jet {c : ℝ} {g : ℝ × ℝ → ℂ} {h : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hh : B0579.IsCylTest c h) (j : Fin 2) :
    (∀ z : ℝ × ℝ, fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir j) =
        UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ) +
          g z * ((B0579.pd j h z : ℝ) : ℂ)) ∧
      IntegrableOn (fun z => fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir j))
        (B0579.cell c) ∧
      IntegrableOn (fun z => UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ))
        (B0579.cell c) ∧
      IntegrableOn (fun z => g z * ((B0579.pd j h z : ℝ) : ℂ)) (B0579.cell c) := by
  obtain ⟨R, hR⟩ := hh.band
  obtain ⟨R', hR'⟩ := (hh.pd j).band
  have hprod : ∀ z : ℝ × ℝ, fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir j) =
      UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ) +
        g z * ((B0579.pd j h z : ℝ) : ℂ) := by
    intro z
    have hgd : HasFDerivAt g (fderiv ℝ g z) z := ((hg.differentiable (by simp)) z).hasFDerivAt
    have hhd : HasFDerivAt (fun y => ((h y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ h z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (hh.differentiable z).hasFDerivAt
    have hm : HasFDerivAt (fun y => g y * ((h y : ℝ) : ℂ))
        (g z • Complex.ofRealCLM.comp (fderiv ℝ h z) + ((h z : ℝ) : ℂ) • fderiv ℝ g z) z :=
      hgd.mul hhd
    rw [hm.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
      UnforcedLeray.Short.IIIa.pdCx, B0579.pd]
    ring
  have hdc : Continuous (fun z => UnforcedLeray.Short.IIIa.pdCx j g z) := by
    unfold UnforcedLeray.Short.IIIa.pdCx
    exact ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hF1 : Continuous (fun z => UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ)) :=
    hdc.mul (Complex.continuous_ofReal.comp hh.continuous)
  have hF2 : Continuous (fun z => g z * ((B0579.pd j h z : ℝ) : ℂ)) :=
    hg.continuous.mul (Complex.continuous_ofReal.comp (hh.pd j).continuous)
  have hband1 : ∀ z : ℝ × ℝ, max R R' < |z.2| →
      UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ) = 0 := fun z hz => by
    rw [hR z (lt_of_le_of_lt (le_max_left _ _) hz)]; simp
  have hband2 : ∀ z : ℝ × ℝ, max R R' < |z.2| →
      g z * ((B0579.pd j h z : ℝ) : ℂ) = 0 := fun z hz => by
    rw [hR' z (lt_of_le_of_lt (le_max_right _ _) hz)]; simp
  have hIF1 : IntegrableOn (fun z => UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ))
      (B0579.cell c) := integrableOn_cell_cplx hF1 hband1
  have hIF2 : IntegrableOn (fun z => g z * ((B0579.pd j h z : ℝ) : ℂ)) (B0579.cell c) :=
    integrableOn_cell_cplx hF2 hband2
  have e : (fun z => fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir j)) =
      fun z => UnforcedLeray.Short.IIIa.pdCx j g z * ((h z : ℝ) : ℂ) +
        g z * ((B0579.pd j h z : ℝ) : ℂ) := funext hprod
  refine ⟨hprod, ?_, hIF1, hIF2⟩
  rw [e]
  exact hIF1.add hIF2

/-- The `q`-derivative of `g · h` has zero cell integral (periodicity). -/
theorem cellIBP_zero_q {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ} {h : ℝ × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hper : ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x)
    (hh : B0579.IsCylTest c h) :
    ∫ z in B0579.cell c, fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir 0) = 0 := by
  have hGs : ContDiff ℝ ∞ (fun z => g z * ((h z : ℝ) : ℂ)) :=
    hg.mul (Complex.ofRealCLM.contDiff.comp hh.smooth)
  have hGp : UnforcedLeray.Cyl.IsPeriodic c (fun z => g z * ((h z : ℝ) : ℂ)) := fun z => by
    simp only [hper z, hh.periodic z]
  have hd0 : ∀ q η : ℝ, HasDerivAt (fun q' => (fun z => g z * ((h z : ℝ) : ℂ)) (q', η))
      (fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) (q, η) (B0579.dir 0)) q := by
    intro q η
    have hc1 : HasDerivAt (fun t : ℝ => ((t, η) : ℝ × ℝ)) (B0579.dir 0) q := by
      have := (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
      simpa [B0579.dir] using this
    exact (hGs.differentiable (by simp) (q, η)).hasFDerivAt.comp_hasDerivAt q hc1
  have hI := (cellIBP_jet hg hh 0).2.1
  rw [cellIBP_cell_eq] at hI ⊢
  exact UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc hGp hd0 hI

/-- The `η`-derivative of `g · h` has zero cell integral (compact support in `η`). -/
theorem cellIBP_zero_eta {c : ℝ} {g : ℝ × ℝ → ℂ} {h : ℝ × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : B0579.IsCylTest c h) :
    ∫ z in B0579.cell c, fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir 1) = 0 := by
  obtain ⟨R, hR⟩ := hh.band
  have hGs : ContDiff ℝ ∞ (fun z => g z * ((h z : ℝ) : ℂ)) :=
    hg.mul (Complex.ofRealCLM.contDiff.comp hh.smooth)
  have hGband : ∀ z : ℝ × ℝ, R < |z.2| → g z * ((h z : ℝ) : ℂ) = 0 := fun z hz => by
    rw [hR z hz]; simp
  have hF : IntegrableOn (fun z => g z * ((h z : ℝ) : ℂ)) (B0579.cell c) :=
    integrableOn_cell_cplx hGs.continuous hGband
  have hd1 : ∀ q η : ℝ, HasDerivAt (fun η' => (fun z => g z * ((h z : ℝ) : ℂ)) (q, η'))
      (fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) (q, η) (B0579.dir 1)) η := by
    intro q η
    have hc1 : HasDerivAt (fun t : ℝ => ((q, t) : ℝ × ℝ)) (B0579.dir 1) η := by
      have := (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
      simpa [B0579.dir] using this
    exact (hGs.differentiable (by simp) (q, η)).hasFDerivAt.comp_hasDerivAt η hc1
  have hI := (cellIBP_jet hg hh 1).2.1
  rw [cellIBP_cell_eq] at hF hI ⊢
  exact UnforcedLeray.Cyl.integral_cell_deriv_eta hd1 hF hI

/-- **(A5) Integration by parts on the cell.** -/
theorem cellIBP : UnforcedLeray.Short.IIIa.CellIBP := by
  unfold CellIBP
  intro c g h hc hg hper hh l
  have hz : ∫ z in B0579.cell c, fderiv ℝ (fun z => g z * ((h z : ℝ) : ℂ)) z (B0579.dir l) = 0 := by
    fin_cases l
    · exact cellIBP_zero_q hc hg hper hh
    · exact cellIBP_zero_eta hg hh
  obtain ⟨hpr, _, hIF1, hIF2⟩ := cellIBP_jet hg hh l
  simp only [hpr] at hz
  rw [integral_add hIF1 hIF2] at hz
  linear_combination hz

end UnforcedLeray.Short.IIIa
