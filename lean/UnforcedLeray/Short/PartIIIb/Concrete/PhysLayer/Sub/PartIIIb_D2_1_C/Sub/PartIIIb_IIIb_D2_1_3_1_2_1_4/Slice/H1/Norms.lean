import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_2

/-!
# `splitNorms`: Pythagoras for the real/imaginary splitting

Source `the November 2 reference manuscript` lines 1351-1362.
Pointwise `‖f y‖² = ‖reC f y‖² + ‖imC f y‖²`, and for real-valued `gr, gi`,
`‖gr + I gi‖² = ‖gr‖² + ‖gi‖²`; integrals split by `integral_add`, the summands being
integrable as squared norms of `L²` functions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma h1nmMemLpRe (f : Space → CVec3) (hf : MemLp f 2 volume) : MemLp (reC f) 2 volume := by
  refine MemLp.of_le hf ?_ ?_
  · have hΦ : Continuous fun z : CVec3 => (WithLp.toLp 2 fun i => (((z i).re : ℝ) : ℂ) : CVec3) := by
      fun_prop
    exact hΦ.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    have h1 : ‖reC f y i‖ = |(f y i).re| := by simp [reC]
    rw [h1]
    gcongr
    exact Complex.abs_re_le_norm _

lemma h1nmMemLpIm (f : Space → CVec3) (hf : MemLp f 2 volume) : MemLp (imC f) 2 volume := by
  refine MemLp.of_le hf ?_ ?_
  · have hΦ : Continuous fun z : CVec3 => (WithLp.toLp 2 fun i => (((z i).im : ℝ) : ℂ) : CVec3) := by
      fun_prop
    exact hΦ.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    have h1 : ‖imC f y i‖ = |(f y i).im| := by simp [imC]
    rw [h1]
    gcongr
    exact Complex.abs_im_le_norm _

theorem splitNorms : SplitNorms := by
  unfold SplitNorms
  refine ⟨fun f hf => ?_, fun gr gi hgr hgi mgr mgi => ?_⟩
  · have pt : ∀ y, ‖f y‖ ^ 2 = ‖reC f y‖ ^ 2 + ‖imC f y‖ ^ 2 := by
      intro y
      simp only [EuclideanSpace.norm_sq_eq]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : ‖reC f y i‖ ^ 2 = (f y i).re ^ 2 := by simp [reC]
      have h2 : ‖imC f y i‖ ^ 2 = (f y i).im ^ 2 := by simp [imC]
      have h3 : ‖f y i‖ ^ 2 = (f y i).re ^ 2 + (f y i).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      rw [h1, h2, h3]
    have i1 : Integrable (fun y => ‖reC f y‖ ^ 2) volume :=
      (h1nmMemLpRe f hf).integrable_norm_pow two_ne_zero
    have i2 : Integrable (fun y => ‖imC f y‖ ^ 2) volume :=
      (h1nmMemLpIm f hf).integrable_norm_pow two_ne_zero
    simp only [pt]
    rw [integral_add i1 i2]
  · have pt2 : ∀ y, ‖gr y + Complex.I • gi y‖ ^ 2 = ‖gr y‖ ^ 2 + ‖gi y‖ ^ 2 := by
      intro y
      simp only [EuclideanSpace.norm_sq_eq]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ha := hgr y i
      have hb := hgi y i
      have e1 : ‖gr y i‖ ^ 2 = (gr y i).re ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, ha]
        ring
      have e2 : ‖gi y i‖ ^ 2 = (gi y i).re ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hb]
        ring
      have e3 : ‖(gr y + Complex.I • gi y) i‖ ^ 2 = (gr y i).re ^ 2 + (gi y i).re ^ 2 := by
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, ha, hb]
        ring
      rw [e1, e2, e3]
    have i1 : Integrable (fun y => ‖gr y‖ ^ 2) volume := mgr.integrable_norm_pow two_ne_zero
    have i2 : Integrable (fun y => ‖gi y‖ ^ 2) volume := mgi.integrable_norm_pow two_ne_zero
    simp only [pt2]
    rw [integral_add i1 i2]

end UnforcedLeray.Short.PartIIIb.Concrete
