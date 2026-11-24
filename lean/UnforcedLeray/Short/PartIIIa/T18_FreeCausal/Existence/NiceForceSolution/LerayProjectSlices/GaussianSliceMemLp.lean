import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2

/-!
# Part III-a, task `PartIII-a:T18/2/4/2/7`: slices of a nice family are in `L²(cell)`

Target (`Sub/T18_2_4_2.lean`): `GaussianSliceMemLp`. For `c > 0`, a `NiceSlices c u` family and
every `s`, the real and imaginary parts of `u(s, ·)` and of `∂_j u(s, ·)` lie in `L²(cell c)`.
Source of record: `the November 2 reference manuscript`, lines 3442-3465.

## Proof idea

Continuity gives strong measurability. `GaussianDecayLoc` at `s₂ = s` gives a bound
`‖u(s,x) i‖ ≤ C e^{-κ x₂²}` and `‖fderiv (u(s,·) i) x‖ ≤ C e^{-κ x₂²}`; the classical slice
derivative `pdC j` is bounded by the operator norm since `‖dir j‖ ≤ 1`. Real and imaginary parts
of a complex number are bounded by its norm, and the Euclidean norm of a `ℝ²` vector is at most
the sum of the moduli of its entries. The dominator `e^{-κ x₂²}` lies in `L²(cell)` because the
cell is `Ico × univ` and `e^{-2κ η²}` is integrable on `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The Euclidean norm of `(a, b)` is at most `2 M` when `|a|, |b| ≤ M`. -/
theorem vec_norm_le_two_aux (a b M : ℝ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    ‖UnforcedLeray.Cyl.vec a b‖ ≤ 2 * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg a) ha
  have ha2 : a ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg a, sq_abs a]
  have hb2 : b ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  nlinarith

/-- The Gaussian dominator `η ↦ e^{-κ η²}` on the cell, as a function of `(q, η)`, is in `L²`. -/
theorem gauss_dom_memLp_aux (c κ : ℝ) (hκ : 0 < κ) :
    MemLp (fun x : ℝ × ℝ => Real.exp (-κ * x.2 ^ 2)) 2 (UnforcedLeray.Cyl.cellμ c) := by
  rw [UnforcedLeray.Cyl.cellμ_eq_prod]
  have hcont : Continuous fun x : ℝ × ℝ => Real.exp (-κ * x.2 ^ 2) := by fun_prop
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).mpr ?_
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  have hg : Integrable (fun y : ℝ => Real.exp (-(2 * κ) * y ^ 2)) :=
    integrable_exp_neg_mul_sq (by linarith)
  have hcomp := hg.comp_snd (volume.restrict (Ico (-c / 2) (c / 2)))
  refine hcomp.congr (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-(2 * κ) * x.2 ^ 2) = Real.exp (-κ * x.2 ^ 2) ^ 2
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A field with the Gaussian pointwise bound is in `L²(cellμ c)`. -/
theorem memLp_of_gauss_bound_aux (c C κ : ℝ) (hκ : 0 < κ) (F : ℝ × ℝ → UnforcedLeray.Cyl.Vec2)
    (hF : Continuous F) (hb : ∀ x, ‖F x‖ ≤ 2 * (C * Real.exp (-κ * x.2 ^ 2))) :
    MemLp F 2 (UnforcedLeray.Cyl.cellμ c) := by
  have hD := ((gauss_dom_memLp_aux c κ hκ).const_mul C).const_mul 2
  refine hD.of_le hF.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (hb x).trans (le_abs_self _)

theorem continuous_vec2_aux (a b : ℝ × ℝ → ℝ) (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => UnforcedLeray.Cyl.vec (a x) (b x) := by
  unfold UnforcedLeray.Cyl.vec
  fun_prop

/-- **Slices of a nice family are in `L²`** (`PartIII-a:T18/2/4/2/7`). -/
theorem gaussianSliceMemLp : UnforcedLeray.Short.IIIa.GaussianSliceMemLp := by
  unfold UnforcedLeray.Short.IIIa.GaussianSliceMemLp
  intro c hc u hu s
  obtain ⟨C, κ, hκ, hb⟩ := hu.decay s
  -- pointwise bounds on the components
  have hA : ∀ (i : Fin 2) (x : ℝ × ℝ), ‖u (s, x) i‖ ≤ C * Real.exp (-κ * x.2 ^ 2) := by
    intro i x
    have h1 := hb s x i le_rfl
    linarith [norm_nonneg (fderiv ℝ (fun y => u (s, y) i) x)]
  have hdir : ∀ j : Fin 2, ‖B0579.dir j‖ ≤ 1 := by
    intro j
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  have hB : ∀ (i j : Fin 2) (x : ℝ × ℝ),
      ‖pdC j (fun y => u (s, y) i) x‖ ≤ C * Real.exp (-κ * x.2 ^ 2) := by
    intro i j x
    have h1 := hb s x i le_rfl
    have h2 : ‖pdC j (fun y => u (s, y) i) x‖ ≤ ‖fderiv ℝ (fun y => u (s, y) i) x‖ := by
      unfold pdC
      calc ‖fderiv ℝ (fun y => u (s, y) i) x (B0579.dir j)‖
          ≤ ‖fderiv ℝ (fun y => u (s, y) i) x‖ * ‖B0579.dir j‖ :=
            (fderiv ℝ (fun y => u (s, y) i) x).le_opNorm _
        _ ≤ ‖fderiv ℝ (fun y => u (s, y) i) x‖ * 1 :=
            mul_le_mul_of_nonneg_left (hdir j) (norm_nonneg _)
        _ = _ := mul_one _
    linarith [norm_nonneg (u (s, x) i)]
  -- continuity
  have hcont : ∀ i : Fin 2, Continuous fun x : ℝ × ℝ => u (s, x) i := fun i =>
    (hu.smooth i).continuous.comp (continuous_const.prodMk continuous_id)
  have hcontD : ∀ i j : Fin 2, Continuous fun x : ℝ × ℝ => pdC j (fun y => u (s, y) i) x := by
    intro i j
    have hC : ContDiff ℝ ∞ fun y : ℝ × ℝ => u (s, y) i :=
      (hu.smooth i).comp (contDiff_const.prodMk contDiff_id)
    have hf := hC.continuous_fderiv (by simp)
    unfold pdC
    exact hf.clm_apply continuous_const
  have hreU : Continuous fun x => UnforcedLeray.Cyl.vec ((u (s, x) 0).re) ((u (s, x) 1).re) :=
    continuous_vec2_aux _ _ (Complex.continuous_re.comp (hcont 0))
      (Complex.continuous_re.comp (hcont 1))
  have himU : Continuous fun x => UnforcedLeray.Cyl.vec ((u (s, x) 0).im) ((u (s, x) 1).im) :=
    continuous_vec2_aux _ _ (Complex.continuous_im.comp (hcont 0))
      (Complex.continuous_im.comp (hcont 1))
  have hreD : ∀ j : Fin 2, Continuous fun x => UnforcedLeray.Cyl.vec
      ((pdC j (fun y => u (s, y) 0) x).re) ((pdC j (fun y => u (s, y) 1) x).re) := fun j =>
    continuous_vec2_aux _ _ (Complex.continuous_re.comp (hcontD 0 j))
      (Complex.continuous_re.comp (hcontD 1 j))
  have himD : ∀ j : Fin 2, Continuous fun x => UnforcedLeray.Cyl.vec
      ((pdC j (fun y => u (s, y) 0) x).im) ((pdC j (fun y => u (s, y) 1) x).im) := fun j =>
    continuous_vec2_aux _ _ (Complex.continuous_im.comp (hcontD 0 j))
      (Complex.continuous_im.comp (hcontD 1 j))
  refine ⟨?_, ?_, fun j => ⟨?_, ?_⟩⟩
  · refine memLp_of_gauss_bound_aux c C κ hκ _ hreU fun x => ?_
    exact vec_norm_le_two_aux _ _ _ ((Complex.abs_re_le_norm _).trans (hA 0 x))
      ((Complex.abs_re_le_norm _).trans (hA 1 x))
  · refine memLp_of_gauss_bound_aux c C κ hκ _ himU fun x => ?_
    exact vec_norm_le_two_aux _ _ _ ((Complex.abs_im_le_norm _).trans (hA 0 x))
      ((Complex.abs_im_le_norm _).trans (hA 1 x))
  · refine memLp_of_gauss_bound_aux c C κ hκ _ (hreD j) fun x => ?_
    exact vec_norm_le_two_aux _ _ _ ((Complex.abs_re_le_norm _).trans (hB 0 j x))
      ((Complex.abs_re_le_norm _).trans (hB 1 j x))
  · refine memLp_of_gauss_bound_aux c C κ hκ _ (himD j) fun x => ?_
    exact vec_norm_le_two_aux _ _ _ ((Complex.abs_im_le_norm _).trans (hB 0 j x))
      ((Complex.abs_im_le_norm _).trans (hB 1 j x))

end UnforcedLeray.Short.IIIa
