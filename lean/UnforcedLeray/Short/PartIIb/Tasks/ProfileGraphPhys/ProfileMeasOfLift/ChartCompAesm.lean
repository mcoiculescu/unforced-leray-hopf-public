import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2_1

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The two test vectors `(e_r, e_3)` of the meridional frame. -/
def chartTT (y : UnforcedLeray.Space) : Fin 2 → UnforcedLeray.Space :=
  ![UnforcedLeray.Axi.eR y, UnforcedLeray.Axi.e3]

lemma chartTT_measurable_apply (j : Fin 3) (i : Fin 2) :
    Measurable fun y : UnforcedLeray.Space => chartTT y i j := by
  have hj : Measurable fun v : UnforcedLeray.Space => v j :=
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp _ _)
  fin_cases i
  · exact hj.comp UnforcedLeray.Axi.measurable_eR
  · simp [chartTT]

/-- The frame coefficients recover a meridional vector from its ring lift. -/
lemma sum_frame (y : UnforcedLeray.Space) (hy : y ∉ UnforcedLeray.Axi.axis)
    (v : UnforcedLeray.Axi.Merid) (i : Fin 2) :
    ∑ j : Fin 3, UnforcedLeray.Axi.frameL y v j * chartTT y i j = v i := by
  have hϱ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hsq := UnforcedLeray.Axi.eR_sq_sum hy
  have hf : ∀ j : Fin 3, UnforcedLeray.Axi.frameL y v j
      = v 0 * UnforcedLeray.Axi.eR y j + v 1 * UnforcedLeray.Axi.e3 j := by
    intro j
    rw [UnforcedLeray.Axi.frameL_apply]
    simp
  rw [Fin.sum_univ_three]
  simp only [hf]
  fin_cases i
  · simp [chartTT, UnforcedLeray.Axi.eR_apply_zero, UnforcedLeray.Axi.eR_apply_one,
      UnforcedLeray.Axi.eR_apply_two, UnforcedLeray.Axi.e3_apply]
    have hϱne : UnforcedLeray.Axi.ϱ y ≠ 0 := hϱ.ne'
    field_simp
    linear_combination (-(v 0)) * UnforcedLeray.Axi.ϱ_sq y
  · simp [chartTT, UnforcedLeray.Axi.eR_apply_zero, UnforcedLeray.Axi.eR_apply_one,
      UnforcedLeray.Axi.eR_apply_two, UnforcedLeray.Axi.e3_apply]

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa in
lemma nvC_apply (R : ℝ) (b : CProf) (x : ℝ × UnforcedLeray.Space) (j : Fin 3) :
    NvC R b x j
      = (((Real.sqrt (UnforcedLeray.Axi.age R x.2)) *
          UnforcedLeray.Axi.frameL x.2 (reM (b (UnforcedLeray.Axi.chart R x.1 x.2))) j : ℝ) : ℂ)
        + Complex.I * (((Real.sqrt (UnforcedLeray.Axi.age R x.2)) *
          UnforcedLeray.Axi.frameL x.2 (imM (b (UnforcedLeray.Axi.chart R x.1 x.2))) j : ℝ) : ℂ) := by
  simp only [NvC, UnforcedLeray.Axi.Nv, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    UnforcedLeray.B0412.realC_apply]

lemma sum_nvC (R : ℝ) (hR : 0 < R) (b : CProf) (x : ℝ × UnforcedLeray.Space)
    (hy : x.2 ∉ UnforcedLeray.Axi.axis) (i : Fin 2) :
    ∑ j : Fin 3, NvC R b x j * (chartTT x.2 i j : ℂ)
      = (Real.sqrt (UnforcedLeray.Axi.age R x.2) : ℂ) *
          (b (UnforcedLeray.Axi.chart R x.1 x.2) i) := by
  have hs : 0 < Real.sqrt (UnforcedLeray.Axi.age R x.2) :=
    Real.sqrt_pos.2 (UnforcedLeray.Axi.age_pos hR.ne' hy)
  set z := UnforcedLeray.Axi.chart R x.1 x.2 with hz
  set s := Real.sqrt (UnforcedLeray.Axi.age R x.2) with hs_def
  have hA : (∑ j : Fin 3, ((UnforcedLeray.Axi.frameL x.2 (reM (b z)) j : ℝ) : ℂ)
      * (chartTT x.2 i j : ℂ)) = ((reM (b z) i : ℝ) : ℂ) := by
    have := sum_frame x.2 hy (reM (b z)) i
    exact_mod_cast this
  have hB : (∑ j : Fin 3, ((UnforcedLeray.Axi.frameL x.2 (imM (b z)) j : ℝ) : ℂ)
      * (chartTT x.2 i j : ℂ)) = ((imM (b z) i : ℝ) : ℂ) := by
    have := sum_frame x.2 hy (imM (b z)) i
    exact_mod_cast this
  have hbz : b z i = ((reM (b z) i : ℝ) : ℂ) + Complex.I * ((imM (b z) i : ℝ) : ℂ) := by
    simp only [reM, imM, PiLp.toLp_apply]
    rw [mul_comm]
    exact (Complex.re_add_im (b z i)).symm
  have expand : ∑ j : Fin 3, NvC R b x j * (chartTT x.2 i j : ℂ)
      = (s : ℂ) * (∑ j : Fin 3, ((UnforcedLeray.Axi.frameL x.2 (reM (b z)) j : ℝ) : ℂ)
          * (chartTT x.2 i j : ℂ))
        + Complex.I * (s : ℂ) * (∑ j : Fin 3, ((UnforcedLeray.Axi.frameL x.2 (imM (b z)) j : ℝ) : ℂ)
          * (chartTT x.2 i j : ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nvC_apply, ← hz, ← hs_def]
    push_cast
    ring
  rw [expand, hA, hB, hbz]
  ring

/-- The reconstruction `(u, y) ↦ (√(age y))⁻¹ Σⱼ uⱼ (e_r, e_3)ⱼ` is measurable. -/
lemma measurable_xi (R : ℝ) :
    Measurable (fun p : UnforcedLeray.PhaseSpace.CVec3 × (ℝ × UnforcedLeray.Space) =>
      ((WithLp.toLp 2 (fun i : Fin 2 =>
        (((Real.sqrt (UnforcedLeray.Axi.age R p.2.2))⁻¹ : ℝ) : ℂ) *
          ∑ j : Fin 3, p.1 j * (chartTT p.2.2 i j : ℂ))) : CMerid)) := by
  have hpj : ∀ j : Fin 3, Measurable fun p : UnforcedLeray.PhaseSpace.CVec3 × (ℝ × UnforcedLeray.Space) =>
      p.1 j := fun j =>
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp _ _)).comp measurable_fst
  have hc : Measurable fun p : UnforcedLeray.PhaseSpace.CVec3 × (ℝ × UnforcedLeray.Space) =>
      p.2.2 := measurable_snd.comp measurable_snd
  have hcomp : ∀ i : Fin 2, Measurable fun p : UnforcedLeray.PhaseSpace.CVec3 × (ℝ × UnforcedLeray.Space) =>
      (((Real.sqrt (UnforcedLeray.Axi.age R p.2.2))⁻¹ : ℝ) : ℂ) *
          ∑ j : Fin 3, p.1 j * (chartTT p.2.2 i j : ℂ) := by
    intro i
    refine (Complex.measurable_ofReal.comp
      ((Real.continuous_sqrt.measurable.comp ((UnforcedLeray.Axi.measurable_age R).comp hc)).inv)).mul ?_
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (hpj j).mul (Complex.measurable_ofReal.comp
      ((chartTT_measurable_apply j i).comp hc))
  have h1 : Measurable (fun p : UnforcedLeray.PhaseSpace.CVec3 × (ℝ × UnforcedLeray.Space) =>
      fun i : Fin 2 =>
        (((Real.sqrt (UnforcedLeray.Axi.age R p.2.2))⁻¹ : ℝ) : ℂ) *
          ∑ j : Fin 3, p.1 j * (chartTT p.2.2 i j : ℂ)) :=
    measurable_pi_lambda _ hcomp
  exact (WithLp.measurable_toLp _ _).comp h1

theorem chartCompAesm_proof : UnforcedLeray.Short.IIb.ChartCompAesm := by
  intro R b hR hNvC
  have hpair : AEStronglyMeasurable (fun x : ℝ × UnforcedLeray.Space => (NvC R b x, x)) volume :=
    hNvC.prodMk aestronglyMeasurable_id
  have hm := ((measurable_xi R).comp_aemeasurable hpair.aemeasurable).aestronglyMeasurable
  refine hm.congr ?_
  have hax : ∀ᵐ x : ℝ × UnforcedLeray.Space, x.2 ∉ UnforcedLeray.Axi.axis :=
    (Measure.quasiMeasurePreserving_snd).ae UnforcedLeray.Axi.ae_not_mem_axis
  filter_upwards [hax] with x hx
  dsimp only [Function.comp]
  ext i
  simp only [PiLp.toLp_apply]
  rw [sum_nvC R hR b x hx i]
  have hne : (Real.sqrt (UnforcedLeray.Axi.age R x.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (UnforcedLeray.Axi.age_pos hR.ne' hx)).ne'
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end UnforcedLeray.Short.IIb
