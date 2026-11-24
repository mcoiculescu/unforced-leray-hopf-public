import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3` leaf: convection and viscous terms are bounded

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
bounded periodic pressure choice) and line 447 (the decaying pressure gauge).

Target: `PbConvViscBound` (`Sub/T02_2_3.lean`).  For a gauge solution `(v, p)` on `[0,T]` there is
`G` with `‖(v·∇)v - νΔv‖ ≤ G` on `[0,T] × ℝ²`.

Proof outline.  Fix `s ∈ [0,T]` and `z`.  The zeroth, first and second iterated derivatives of
`v s` are bounded uniformly in `(s, z)` by `M0`, `M1`, `M2` (`GaugeHyp.bounded`).  For a scalar
`C²` function `g`, the first partials are bounded by `‖iteratedFDeriv 1 g z‖` and the pure second
partials by `‖iteratedFDeriv 2 g z‖` (`pbCV_partial_one`, `pbCV_partial_two`).  For a component
`v s · i` the iterated derivative norms are bounded by those of `v s` (`pbCV_norm_comp_one`,
`pbCV_norm_comp_two`).  Each coordinate of `(v·∇)v - νΔv` is then at most
`2 M0 M1 + |ν| (2 M2)` in modulus, and the Euclidean norm of a vector with two coordinates bounded
by `K` is at most `2K`.  The constant `G = 2K` does not depend on `s` or `z`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-! ### Calculus of a scalar function -/

/-- The first partials of a smooth scalar function are bounded by its first derivative norm. -/
theorem pbCV_partial_one {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) :
    |Cyl.partialQ g z| ≤ ‖iteratedFDeriv ℝ 1 g z‖ ∧
      |Cyl.partialEta g z| ≤ ‖iteratedFDeriv ℝ 1 g z‖ := by
  have hd : Differentiable ℝ g := (hg.of_le gg_two_le).differentiable (by norm_num)
  rw [norm_iteratedFDeriv_one]
  exact ⟨gg_partialQ_le hd z, gg_partialEta_le hd z⟩

/-- The `q`-second partial of a `C^∞` function is the second derivative evaluated at `(1,0)`
twice. -/
theorem pbCV_partialQQ_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) :
    Cyl.partialQ (Cyl.partialQ g) z = iteratedFDeriv ℝ 2 g z (fun _ => ((1 : ℝ), (0 : ℝ))) := by
  have h2 : ContDiff ℝ 2 g := hg.of_le gg_two_le
  have hd : Differentiable ℝ g := h2.differentiable (by norm_num)
  have hC := Cyl.C2.of_contDiff h2
  have hdd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hu : DifferentiableAt ℝ (fun _ : Plane => ((1 : ℝ), (0 : ℝ))) z :=
    differentiableAt_const _
  have hfun : Cyl.partialQ g = fun x => fderiv ℝ g x ((1 : ℝ), (0 : ℝ)) :=
    funext (fun x => Cyl.partialQ_eq_fderiv hd x)
  have key : fderiv ℝ (fun x => fderiv ℝ g x ((1 : ℝ), (0 : ℝ))) z ((1 : ℝ), (0 : ℝ)) =
      fderiv ℝ (fderiv ℝ g) z ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
    rw [fderiv_clm_apply hdd hu]
    simp
  rw [Cyl.partialQ_eq_fderiv hC.diffQ z, hfun, key, iteratedFDeriv_two_apply]

/-- The `η`-second partial of a `C^∞` function is the second derivative evaluated at `(0,1)`
twice. -/
theorem pbCV_partialEtaEta_eq {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) :
    Cyl.partialEta (Cyl.partialEta g) z = iteratedFDeriv ℝ 2 g z (fun _ => ((0 : ℝ), (1 : ℝ))) := by
  have h2 : ContDiff ℝ 2 g := hg.of_le gg_two_le
  have hd : Differentiable ℝ g := h2.differentiable (by norm_num)
  have hC := Cyl.C2.of_contDiff h2
  have hdd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hu : DifferentiableAt ℝ (fun _ : Plane => ((0 : ℝ), (1 : ℝ))) z :=
    differentiableAt_const _
  have hfun : Cyl.partialEta g = fun x => fderiv ℝ g x ((0 : ℝ), (1 : ℝ)) :=
    funext (fun x => Cyl.partialEta_eq_fderiv hd x)
  have key : fderiv ℝ (fun x => fderiv ℝ g x ((0 : ℝ), (1 : ℝ))) z ((0 : ℝ), (1 : ℝ)) =
      fderiv ℝ (fderiv ℝ g) z ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
    rw [fderiv_clm_apply hdd hu]
    simp
  rw [Cyl.partialEta_eq_fderiv hC.diffEta z, hfun, key, iteratedFDeriv_two_apply]

/-- A second derivative evaluated at a unit vector repeated twice is bounded by the norm. -/
theorem pbCV_norm_two_apply_le (g : Plane → ℝ) (e : Plane) (he : ‖e‖ = 1) (z : Plane) :
    |iteratedFDeriv ℝ 2 g z (fun _ => e)| ≤ ‖iteratedFDeriv ℝ 2 g z‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ 2 g z (fun _ => e)‖
      ≤ ‖iteratedFDeriv ℝ 2 g z‖ * ∏ i : Fin 2, ‖(fun _ : Fin 2 => e) i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 2 g z‖ := by simp [he]

/-- The pure second partials of a smooth scalar function are bounded by its second derivative
norm. -/
theorem pbCV_partial_two {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (z : Plane) :
    |Cyl.partialQ (Cyl.partialQ g) z| ≤ ‖iteratedFDeriv ℝ 2 g z‖ ∧
      |Cyl.partialEta (Cyl.partialEta g) z| ≤ ‖iteratedFDeriv ℝ 2 g z‖ := by
  refine ⟨?_, ?_⟩
  · rw [pbCV_partialQQ_eq hg z]
    exact pbCV_norm_two_apply_le g ((1 : ℝ), (0 : ℝ)) (by simp) z
  · rw [pbCV_partialEtaEta_eq hg z]
    exact pbCV_norm_two_apply_le g ((0 : ℝ), (1 : ℝ)) (by simp) z

/-! ### Passing from a vector field to one of its components -/

/-- The first derivative norm of a component is at most that of the field. -/
theorem pbCV_norm_comp_one {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) (i : Fin 2) (z : Plane) :
    ‖iteratedFDeriv ℝ 1 (fun x => w x i) z‖ ≤ ‖iteratedFDeriv ℝ 1 w z‖ := by
  have h1 := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (f := w) (x := z) (N := ∞) (n := 1) hw.contDiffAt (by norm_num)
  calc ‖iteratedFDeriv ℝ 1 (fun x => w x i) z‖
      ≤ ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ 1 w z‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ 1 w z‖ :=
        mul_le_mul_of_nonneg_right (gg_proj_norm_le i) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ 1 w z‖ := one_mul _

/-- The second derivative norm of a component is at most that of the field. -/
theorem pbCV_norm_comp_two {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) (i : Fin 2) (z : Plane) :
    ‖iteratedFDeriv ℝ 2 (fun x => w x i) z‖ ≤ ‖iteratedFDeriv ℝ 2 w z‖ := by
  have h1 := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (f := w) (x := z) (N := ∞) (n := 2) hw.contDiffAt gg_two_le
  calc ‖iteratedFDeriv ℝ 2 (fun x => w x i) z‖
      ≤ ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ 2 w z‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ 2 w z‖ :=
        mul_le_mul_of_nonneg_right (gg_proj_norm_le i) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ 2 w z‖ := one_mul _

/-! ### Algebra of the operators in components -/

theorem pbCV_adv_apply (u : Plane → Vec) (z : Plane) (i : Fin 2) :
    Train.advection u z i = u z 0 * Cyl.partialQ (fun w => u w i) z +
      u z 1 * Cyl.partialEta (fun w => u w i) z := by
  fin_cases i <;> rfl

theorem pbCV_lap_apply (u : Plane → Vec) (z : Plane) (i : Fin 2) :
    Train.vecLaplacian u z i = Train.lapS (fun w => u w i) z := by
  fin_cases i <;> rfl

theorem pbCV_lap_eq (f : Plane → ℝ) (z : Plane) :
    Train.lapS f z = Cyl.partialQ (Cyl.partialQ f) z + Cyl.partialEta (Cyl.partialEta f) z :=
  rfl

theorem pbCV_abs_sum_le {a b x y M N : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M)
    (hx : |x| ≤ N) (hy : |y| ≤ N) : |a * x + b * y| ≤ 2 * M * N := by
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = |a| * |x| + |b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ M * N + M * N :=
        add_le_add (mul_le_mul ha hx (abs_nonneg _) hM) (mul_le_mul hb hy (abs_nonneg _) hM)
    _ = 2 * M * N := by ring

/-- One coordinate of `(v·∇)v - νΔv` is bounded, given the bounds on the field and its
component partials. -/
theorem pbCV_coord (u : Plane → Vec) (z : Plane) (ν M0 M1 M2 : ℝ) (hM0 : 0 ≤ M0) (i : Fin 2)
    (hu : ∀ j : Fin 2, |u z j| ≤ M0)
    (hf : |Cyl.partialQ (fun x => u x i) z| ≤ M1 ∧ |Cyl.partialEta (fun x => u x i) z| ≤ M1)
    (hs : |Cyl.partialQ (Cyl.partialQ (fun x => u x i)) z| ≤ M2 ∧
      |Cyl.partialEta (Cyl.partialEta (fun x => u x i)) z| ≤ M2) :
    |(Train.advection u z - ν • Train.vecLaplacian u z) i| ≤ 2 * M0 * M1 + |ν| * (2 * M2) := by
  have hadv : |Train.advection u z i| ≤ 2 * M0 * M1 := by
    rw [pbCV_adv_apply]
    exact pbCV_abs_sum_le hM0 (hu 0) (hu 1) hf.1 hf.2
  have hlap : |Train.vecLaplacian u z i| ≤ 2 * M2 := by
    rw [pbCV_lap_apply, pbCV_lap_eq]
    have h3 := abs_add_le (Cyl.partialQ (Cyl.partialQ (fun x => u x i)) z)
      (Cyl.partialEta (Cyl.partialEta (fun x => u x i)) z)
    linarith [hs.1, hs.2]
  have hn : |ν * Train.vecLaplacian u z i| ≤ |ν| * (2 * M2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlap (abs_nonneg _)
  have hsub : (Train.advection u z - ν • Train.vecLaplacian u z) i =
      Train.advection u z i - ν * Train.vecLaplacian u z i := by
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hsub]
  obtain ⟨a1, a2⟩ := abs_le.mp hadv
  obtain ⟨b1, b2⟩ := abs_le.mp hn
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### The convection-viscosity bound -/

/-- **Convection and viscous terms are bounded** (leaf of `PbTimeGrad`; `PbConvViscBound`). -/
theorem pbConvViscBound : PbConvViscBound := by
  intro ν c T v p h
  obtain ⟨M0, hM0⟩ := h.bounded 0
  obtain ⟨M1, hM1⟩ := h.bounded 1
  obtain ⟨M2, hM2⟩ := h.bounded 2
  refine ⟨2 * (2 * M0 * M1 + |ν| * (2 * M2)), fun s hs z => ?_⟩
  have hv : ContDiff ℝ ∞ (v s) := gg_slice_contDiff hs h.classical.smooth_v
  have hz0 : ‖v s z‖ ≤ M0 := by
    have h0 := hM0 s hs z
    rwa [norm_iteratedFDeriv_zero] at h0
  have hz1 : ‖iteratedFDeriv ℝ 1 (v s) z‖ ≤ M1 := hM1 s hs z
  have hz2 : ‖iteratedFDeriv ℝ 2 (v s) z‖ ≤ M2 := hM2 s hs z
  have hM0nn : 0 ≤ M0 := (norm_nonneg _).trans hz0
  have hcoord : ∀ j : Fin 2, |v s z j| ≤ M0 := fun j => by
    have h0 := (PiLp.norm_apply_le (v s z) j).trans hz0
    rwa [Real.norm_eq_abs] at h0
  have hcomp : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x => v s x j) := fun j =>
    (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).contDiff.comp hv
  have hfirst : ∀ j : Fin 2, |Cyl.partialQ (fun x => v s x j) z| ≤ M1 ∧
      |Cyl.partialEta (fun x => v s x j) z| ≤ M1 := fun j => by
    have hb := pbCV_partial_one (hcomp j) z
    have hn := pbCV_norm_comp_one hv j z
    exact ⟨hb.1.trans (hn.trans hz1), hb.2.trans (hn.trans hz1)⟩
  have hsecond : ∀ j : Fin 2, |Cyl.partialQ (Cyl.partialQ (fun x => v s x j)) z| ≤ M2 ∧
      |Cyl.partialEta (Cyl.partialEta (fun x => v s x j)) z| ≤ M2 := fun j => by
    have hb := pbCV_partial_two (hcomp j) z
    have hn := pbCV_norm_comp_two hv j z
    exact ⟨hb.1.trans (hn.trans hz2), hb.2.trans (hn.trans hz2)⟩
  have hA0 := pbCV_coord (v s) z ν M0 M1 M2 hM0nn 0 hcoord (hfirst 0) (hsecond 0)
  have hA1 := pbCV_coord (v s) z ν M0 M1 M2 hM0nn 1 hcoord (hfirst 1) (hsecond 1)
  set K := 2 * M0 * M1 + |ν| * (2 * M2) with hKdef
  set X := Train.advection (v s) z - ν • Train.vecLaplacian (v s) z with hXdef
  have hK : 0 ≤ K := (abs_nonneg _).trans hA0
  have hx0 : X 0 * X 0 ≤ K * K := by
    have h0 := mul_le_mul hA0 hA0 (abs_nonneg _) hK
    rwa [abs_mul_abs_self] at h0
  have hx1 : X 1 * X 1 ≤ K * K := by
    have h1 := mul_le_mul hA1 hA1 (abs_nonneg _) hK
    rwa [abs_mul_abs_self] at h1
  have hsq : ‖X‖ ^ 2 = X 0 * X 0 + X 1 * X 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    ring
  nlinarith [norm_nonneg X, mul_nonneg hK hK, hx0, hx1, hsq, hK]

end UnforcedLeray.Short.PartI
