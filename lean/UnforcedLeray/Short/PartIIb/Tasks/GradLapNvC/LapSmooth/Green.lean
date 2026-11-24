import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5

/-!
# Part II-b, task `PartII-b:T09/5/7`: the Green identity for `lapT` on phase tests

Target: `lapGreen_proof : UnforcedLeray.Short.IIb.LapGreen`.

Proof outline. Fix a period-slice `t`. Each spatial slice `y ↦ Φ(t,y)` is `C²` with compact
support, and so is `y ↦ w(t,y)`. Then
* `PhaseSpace.dy j F (t,y) = fderiv (fun y' ↦ F (t,y')) y (coordinateVector j)` (chain rule);
* for each direction `v`, `∫ dotL (D_v² f) g = ∫ dotL f (D_v² g)` by two applications of
  Mathlib's `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`;
* summing over `j` gives the slice identity; integrating over `t ∈ (0, P]` and using `ν`-linearity
  of `dotL` gives `pairF P (nuLapT ν Φ) w = pairF P Φ (nuLapT ν w)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

namespace GreenHelp

theorem dotL_smul_left (c : ℝ) (a b : CVec3) : dotL (c • a) b = (c : ℂ) * dotL a b := by
  rw [dotL_apply, dotL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

theorem dotL_smul_right (c : ℝ) (a b : CVec3) : dotL a (c • b) = (c : ℂ) * dotL a b := by
  rw [dotL_apply, dotL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

theorem cont_dot {a b : Space → CVec3} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun y => dotL (a y) (b y)) :=
  (dotL.continuous.comp ha).clm_apply hb

theorem integrable_dot_left {a b : Space → CVec3} (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) : Integrable (fun y => dotL (a y) (b y)) := by
  refine (cont_dot ha hb).integrable_of_hasCompactSupport ?_
  exact HasCompactSupport.intro hac.isCompact
    (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])

theorem integrable_dot_right {a b : Space → CVec3} (ha : Continuous a) (hb : Continuous b)
    (hbc : HasCompactSupport b) : Integrable (fun y => dotL (a y) (b y)) := by
  refine (cont_dot ha hb).integrable_of_hasCompactSupport ?_
  exact HasCompactSupport.intro hbc.isCompact
    (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])

theorem cont_dir1 {f : Space → CVec3} (hf : ContDiff ℝ 1 f) (v : Space) :
    Continuous (fun y => fderiv ℝ f y v) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem cont_dir2 {f : Space → CVec3} (hf : ContDiff ℝ 2 f) (v : Space) :
    Continuous (fun y => fderiv ℝ f y v) :=
  cont_dir1 (hf.of_le (by norm_num)) v

theorem cd1_dir {f : Space → CVec3} (hf : ContDiff ℝ 2 f) (v : Space) :
    ContDiff ℝ 1 (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- Integration by parts in one direction, applied twice. -/
theorem ibp_dir {f g : Space → CVec3} (v : Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∫ y, dotL (fderiv ℝ (fun y' => fderiv ℝ f y' v) y v) (g y) =
      ∫ y, dotL (f y) (fderiv ℝ (fun y' => fderiv ℝ g y' v) y v) := by
  have hu1 := cd1_dir hf v
  have hg1 := cd1_dir hg v
  have s1 := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := dotLR) (f := fun y => fderiv ℝ f y v) (g := g) (v := v)
    (by simp only [dotLR_apply]
        exact integrable_dot_right (cont_dir1 hu1 v) hg.continuous hgc)
    (by simp only [dotLR_apply]
        exact integrable_dot_left (cont_dir2 hf v) (cont_dir2 hg v)
          (hfc.fderiv_apply (𝕜 := ℝ) v))
    (by simp only [dotLR_apply]
        exact integrable_dot_left (cont_dir2 hf v) hg.continuous
          (hfc.fderiv_apply (𝕜 := ℝ) v))
    (fun x _ => hu1.differentiable one_ne_zero x)
    (fun x _ => hg.differentiable (by norm_num) x)
  have s2 := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := dotLR) (f := f) (g := fun y => fderiv ℝ g y v) (v := v)
    (by simp only [dotLR_apply]
        exact integrable_dot_left (cont_dir2 hf v) (cont_dir2 hg v)
          (hfc.fderiv_apply (𝕜 := ℝ) v))
    (by simp only [dotLR_apply]
        exact integrable_dot_left hf.continuous (cont_dir1 hg1 v) hfc)
    (by simp only [dotLR_apply]
        exact integrable_dot_left hf.continuous (cont_dir2 hg v) hfc)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hg1.differentiable one_ne_zero x)
  simp only [dotLR_apply] at s1 s2
  rw [s2, s1, neg_neg]

/-- The spatial Laplacian of a `C²` compactly supported field, tested against a second one. -/
theorem ibp_lap {f g : Space → CVec3} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∫ y, dotL (∑ j : Fin 3, fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector j)) y
        (coordinateVector j)) (g y) =
      ∫ y, dotL (f y) (∑ j : Fin 3, fderiv ℝ (fun y' => fderiv ℝ g y' (coordinateVector j)) y
        (coordinateVector j)) := by
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_dot_right
      (cont_dir1 (cd1_dir hf _) _) hg.continuous hgc)]
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_dot_left hf.continuous
      (cont_dir1 (cd1_dir hg _) _) hfc)]
  exact Finset.sum_congr rfl (fun j _ => ibp_dir (coordinateVector j) hf hg hfc hgc)

/-- Chain rule: the phase derivative `dy j` of a field is the slice derivative. -/
theorem slice_fderiv {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (t : ℝ) (y v : Space) :
    fderiv ℝ (fun y' => F (t, y')) y v = fderiv ℝ F (t, y) (0, v) := by
  have h1 : HasFDerivAt (fun y' : Space => ((t, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have h2 := (hF (t, y)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun y' => F (t, y')) y =
      (fderiv ℝ F (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := h2.fderiv
  rw [h3]
  rfl

theorem contDiff_dy {F : ℝ × Space → CVec3} (hF : ContDiff ℝ 2 F) (j : Fin 3) :
    ContDiff ℝ 1 (PhaseSpace.dy j F) :=
  (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem slice_contDiff {F : ℝ × Space → CVec3} (hF : ContDiff ℝ 2 F) (t : ℝ) :
    ContDiff ℝ 2 (fun y : Space => F (t, y)) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

end GreenHelp

open GreenHelp

theorem dy_slice_vec {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (j : Fin 3) (t : ℝ)
    (y : Space) :
    PhaseSpace.dy j F (t, y) = fderiv ℝ (fun y' => F (t, y')) y (coordinateVector j) :=
  (slice_fderiv hF t y (coordinateVector j)).symm

/-- **Leaf `T09/5/7`**: Green's identity for the phase Laplacian. -/
theorem lapGreen_proof : UnforcedLeray.Short.IIb.LapGreen := by
  intro P ν Φ w _hP hΦ hw _hper hK
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨K, hKc, hKz⟩ := hK
  have hΦ2 : ContDiff ℝ 2 Φ := hΦ.smooth.of_le (by simp)
  have hΦd : Differentiable ℝ Φ := hΦ2.differentiable (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hcsΦ : ∀ t : ℝ, HasCompactSupport (fun y : Space => Φ (t, y)) := fun t =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
      (fun y hy => hR t y (not_le.mp (fun h => hy (mem_closedBall_zero_iff.mpr h))))
  have hcsw : ∀ t : ℝ, HasCompactSupport (fun y : Space => w (t, y)) := fun t =>
    HasCompactSupport.intro hKc (fun y hy => hKz t y hy)
  have key : ∀ t : ℝ, ∫ y, dotL (PhaseSpace.lapT Φ (t, y)) (w (t, y)) =
      ∫ y, dotL (Φ (t, y)) (PhaseSpace.lapT w (t, y)) := by
    intro t
    have eΦ : ∀ y : Space, PhaseSpace.lapT Φ (t, y) = ∑ j : Fin 3,
        fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Φ (t, y'')) y' (coordinateVector j)) y
          (coordinateVector j) := by
      intro y
      simp only [PhaseSpace.lapT]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hdy : Differentiable ℝ (PhaseSpace.dy j Φ) :=
        (contDiff_dy hΦ2 j).differentiable one_ne_zero
      rw [dy_slice_vec hdy j t y]
      rw [show (fun y' => PhaseSpace.dy j Φ (t, y')) = fun y' =>
          fderiv ℝ (fun y'' => Φ (t, y'')) y' (coordinateVector j) from
          funext fun y' => dy_slice_vec hΦd j t y']
    have eW : ∀ y : Space, PhaseSpace.lapT w (t, y) = ∑ j : Fin 3,
        fderiv ℝ (fun y' => fderiv ℝ (fun y'' => w (t, y'')) y' (coordinateVector j)) y
          (coordinateVector j) := by
      intro y
      simp only [PhaseSpace.lapT]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hdy : Differentiable ℝ (PhaseSpace.dy j w) :=
        (contDiff_dy hw j).differentiable one_ne_zero
      rw [dy_slice_vec hdy j t y]
      rw [show (fun y' => PhaseSpace.dy j w (t, y')) = fun y' =>
          fderiv ℝ (fun y'' => w (t, y'')) y' (coordinateVector j) from
          funext fun y' => dy_slice_vec hwd j t y']
    simp only [eΦ, eW]
    exact ibp_lap (slice_contDiff hΦ2 t) (slice_contDiff hw t) (hcsΦ t) (hcsw t)
  simp only [pairF, phaseInt, nuLapT, Pi.smul_apply, dotL_smul_left, dotL_smul_right,
    integral_const_mul, key]

end UnforcedLeray.Short.IIb
