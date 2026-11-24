import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_3.AeStrip

/-!
# Real and imaginary parts of a divergence-free field, and the real pairings

Helpers for `pepsC0SliceOrthCell` (source `the November 2 reference manuscript`
1650-1656, 1676): `Re/Im v ∈ Cyl.divFree c`, and `⟨g, F - P0 F⟩ = 0` for `g ∈ divFree c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (toL2v reVec imVec P0C cplxOf P0re P0im)

theorem memLp_reVec_imVec {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → Fin 2 → ℂ}
    (h : MemLp (fun x => toMC (f x)) 2 μ) :
    MemLp (reVec f) 2 μ ∧ MemLp (imVec f) 2 μ := by
  have hc1 : Continuous fun z : UnforcedLeray.B0223.MeridC =>
      UnforcedLeray.Cyl.vec (z 0).re (z 1).re :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
      fin_cases i
      · exact Complex.continuous_re.comp (continuous_apply 0 |>.comp (PiLp.continuous_ofLp 2 _))
      · exact Complex.continuous_re.comp (continuous_apply 1 |>.comp (PiLp.continuous_ofLp 2 _)))
  have hc2 : Continuous fun z : UnforcedLeray.B0223.MeridC =>
      UnforcedLeray.Cyl.vec (z 0).im (z 1).im :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by
      fin_cases i
      · exact Complex.continuous_im.comp (continuous_apply 0 |>.comp (PiLp.continuous_ofLp 2 _))
      · exact Complex.continuous_im.comp (continuous_apply 1 |>.comp (PiLp.continuous_ofLp 2 _)))
  constructor
  · refine h.of_le (hc1.comp_aestronglyMeasurable h.aestronglyMeasurable) (Eventually.of_forall
      fun x => ?_)
    show ‖UnforcedLeray.Cyl.vec (f x 0).re (f x 1).re‖ ≤ ‖toMC (f x)‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Fin.sum_univ_two, toMC, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (f x 0).im, sq_nonneg (f x 1).im]
  · refine h.of_le (hc2.comp_aestronglyMeasurable h.aestronglyMeasurable) (Eventually.of_forall
      fun x => ?_)
    show ‖UnforcedLeray.Cyl.vec (f x 0).im (f x 1).im‖ ≤ ‖toMC (f x)‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Fin.sum_univ_two, toMC, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (f x 0).re, sq_nonneg (f x 1).re]

theorem toL2v_ae {c : ℝ} {F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2}
    (hF : MemLp F 2 (UnforcedLeray.Cyl.cellμ c)) :
    (toL2v c F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) =ᵐ[UnforcedLeray.Cyl.cellμ c] F := by
  unfold toL2v
  rw [dif_pos hF]
  exact hF.coeFn_toLp

/-- `⟨g, F - P0 F⟩ = 0` for `g ∈ divFree`: integrable and of integral `0`. -/
theorem pair_zero (c : ℝ) (F G : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hF : MemLp F 2 (UnforcedLeray.Cyl.cellμ c)) (hG : MemLp G 2 (UnforcedLeray.Cyl.cellμ c))
    (hg : toL2v c G ∈ UnforcedLeray.Cyl.divFree c) :
    Integrable (fun x : ℝ × ℝ => ∑ i : Fin 2,
        (F x i - (UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i) *
          G x i) (UnforcedLeray.Cyl.cellμ c) ∧
      ∫ x, ∑ i : Fin 2,
        (F x i - (UnforcedLeray.Cyl.P0 c (toL2v c F) : ℝ × ℝ → UnforcedLeray.Cyl.Vec2) x i) *
          G x i ∂(UnforcedLeray.Cyl.cellμ c) = 0 := by
  have hO : ⟪toL2v c G, toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 (UnforcedLeray.Cyl.sub_P0_mem_orthogonal (toL2v c F))
      _ hg
  have hpt : ∀ᵐ a ∂(UnforcedLeray.Cyl.cellμ c),
      ⟪(toL2v c G) a, (toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)) a⟫_ℝ =
        ∑ i : Fin 2, (F a i - (UnforcedLeray.Cyl.P0 c (toL2v c F) :
          ℝ × ℝ → UnforcedLeray.Cyl.Vec2) a i) * G a i := by
    filter_upwards [Lp.coeFn_sub (toL2v c F) (UnforcedLeray.Cyl.P0 c (toL2v c F)),
      toL2v_ae hF, toL2v_ae hG] with a h2 h3 h4
    rw [h2, Pi.sub_apply, h3, h4, real_inner_comm, PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm]
  have hInt : Integrable (fun a => ⟪(toL2v c G) a,
      (toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)) a⟫_ℝ) (UnforcedLeray.Cyl.cellμ c) :=
    L2.integrable_inner _ _
  refine ⟨hInt.congr hpt, ?_⟩
  have hI0 : ∫ a, ⟪(toL2v c G) a, (toL2v c F - UnforcedLeray.Cyl.P0 c (toL2v c F)) a⟫_ℝ
      ∂(UnforcedLeray.Cyl.cellμ c) = 0 := ((L2.inner_def _ _).symm).trans hO
  rw [← integral_congr_ae hpt]
  exact hI0

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
