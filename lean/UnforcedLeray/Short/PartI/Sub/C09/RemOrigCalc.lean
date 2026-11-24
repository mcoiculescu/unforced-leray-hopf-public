import UnforcedLeray.Units.B0121.WeakDeriv

/-!
# Helper calculus for `RemovableOrigin` (task PartI:C09, removable origin)

Scaling, Leibniz and bump-function facts on `ℝ × ℝ` with `ℂ`-valued functions, used by
`UnforcedLeray.Short.PartI.Sub.C09.RemovableOrigin`.  No statement of the main task lives here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.RemOrig

open UnforcedLeray.PlanarBS.Sob UnforcedLeray.B0121

theorem dirDeriv_scale_fn {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (c : ℝ) (v : ℝ × ℝ) :
    dirDeriv v (fun y => g (c • y)) = fun y => c • dirDeriv v g (c • y) := by
  funext z
  unfold dirDeriv
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => c • y) (c • ContinuousLinearMap.id ℝ (ℝ × ℝ)) z :=
    (hasFDerivAt_id z).const_smul c
  have h2 : HasFDerivAt (fun y => g (c • y))
      ((fderiv ℝ g (c • z)).comp (c • ContinuousLinearMap.id ℝ (ℝ × ℝ))) z :=
    (hg (c • z)).hasFDerivAt.comp z h1
  rw [h2.fderiv]
  simp

theorem dirDeriv_const_smul_fn {H : ℝ × ℝ → ℂ} (hH : Differentiable ℝ H) (k : ℝ) (v : ℝ × ℝ) :
    dirDeriv v (fun y => k • H y) = fun y => k • dirDeriv v H y := by
  funext z
  unfold dirDeriv
  have h : HasFDerivAt (fun y => k • H y) (k • fderiv ℝ H z) z :=
    (hH z).hasFDerivAt.const_smul k
  rw [h.fderiv]
  simp

theorem dirDeriv_scale_pt {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (c : ℝ) (v z : ℝ × ℝ) :
    dirDeriv v (fun y => g (c • y)) z = c • dirDeriv v g (c • z) := by
  rw [dirDeriv_scale_fn (hg.differentiable (by simp)) c v]

theorem dirDeriv_mul_fn {a b : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (v : ℝ × ℝ) :
    dirDeriv v (fun y => a y * b y) = fun y => a y * dirDeriv v b y + b y * dirDeriv v a y := by
  funext z
  unfold dirDeriv
  have h : HasFDerivAt (fun y => a y * b y) (a z • fderiv ℝ b z + b z • fderiv ℝ a z) z :=
    (ha.differentiable (by simp) z).hasFDerivAt.mul (hb.differentiable (by simp) z).hasFDerivAt
  rw [h.fderiv]
  simp [smul_eq_mul]

theorem dirDeriv_add_fn {P Q : ℝ × ℝ → ℂ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (v : ℝ × ℝ) :
    dirDeriv v (fun y => P y + Q y) = fun y => dirDeriv v P y + dirDeriv v Q y := by
  funext z
  unfold dirDeriv
  have h : HasFDerivAt (fun y => P y + Q y) (fderiv ℝ P z + fderiv ℝ Q z) z :=
    (hP.differentiable (by simp) z).hasFDerivAt.add (hQ.differentiable (by simp) z).hasFDerivAt
  rw [h.fderiv]
  simp

theorem dirDeriv_sub_fn {P Q : ℝ × ℝ → ℂ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (v : ℝ × ℝ) :
    dirDeriv v (fun y => P y - Q y) = fun y => dirDeriv v P y - dirDeriv v Q y := by
  funext z
  unfold dirDeriv
  have h : HasFDerivAt (fun y => P y - Q y) (fderiv ℝ P z - fderiv ℝ Q z) z :=
    (hP.differentiable (by simp) z).hasFDerivAt.sub (hQ.differentiable (by simp) z).hasFDerivAt
  rw [h.fderiv]
  simp

theorem iterDirDeriv2_mul {a b : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (v z : ℝ × ℝ) :
    iterDirDeriv [v, v] (fun y => a y * b y) z = iterDirDeriv [v, v] a z * b z
      + 2 * (dirDeriv v a z * dirDeriv v b z) + a z * iterDirDeriv [v, v] b z := by
  have hA : ContDiff ℝ ∞ (dirDeriv v a) := contDiff_dirDeriv ha v
  have hB : ContDiff ℝ ∞ (dirDeriv v b) := contDiff_dirDeriv hb v
  have hP : ContDiff ℝ ∞ (fun y => a y * dirDeriv v b y) := ha.mul hB
  have hQ : ContDiff ℝ ∞ (fun y => b y * dirDeriv v a y) := hb.mul hA
  simp only [iterDirDeriv_cons, iterDirDeriv_nil]
  rw [dirDeriv_mul_fn ha hb v, dirDeriv_add_fn hP hQ v]
  rw [dirDeriv_mul_fn ha hB v, dirDeriv_mul_fn hb hA v]
  ring

theorem iterDirDeriv2_sub {P Q : ℝ × ℝ → ℂ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (v z : ℝ × ℝ) :
    iterDirDeriv [v, v] (fun y => P y - Q y) z
      = iterDirDeriv [v, v] P z - iterDirDeriv [v, v] Q z := by
  have hA : ContDiff ℝ ∞ (dirDeriv v P) := contDiff_dirDeriv hP v
  have hB : ContDiff ℝ ∞ (dirDeriv v Q) := contDiff_dirDeriv hQ v
  simp only [iterDirDeriv_cons, iterDirDeriv_nil]
  rw [dirDeriv_sub_fn hP hQ v, dirDeriv_sub_fn hA hB v]

theorem iterDirDeriv2_scale {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (c : ℝ) (v z : ℝ × ℝ) :
    iterDirDeriv [v, v] (fun y => g (c • y)) z = c • (c • iterDirDeriv [v, v] g (c • z)) := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hD : Differentiable ℝ (dirDeriv v g) := (contDiff_dirDeriv hg v).differentiable (by simp)
  have hH : Differentiable ℝ (fun y => dirDeriv v g (c • y)) :=
    hD.comp (differentiable_id.const_smul c)
  simp only [iterDirDeriv_cons, iterDirDeriv_nil]
  rw [dirDeriv_scale_fn hg1 c v, dirDeriv_const_smul_fn hH c v, dirDeriv_scale_fn hD c v]

theorem isTestFn_of_smooth_cs {f : ℝ × ℝ → ℂ} (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : IsTestFn univ f :=
  ⟨hs, hc, subset_univ _⟩

theorem hcs_dirDeriv {f : ℝ × ℝ → ℂ} (hf : HasCompactSupport f) (v : ℝ × ℝ) :
    HasCompactSupport (dirDeriv v f) :=
  hf.fderiv_apply (𝕜 := ℝ) v

theorem hcs_iter (vs : List (ℝ × ℝ)) {f : ℝ × ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (iterDirDeriv vs f) := by
  induction vs with
  | nil => simpa using hf
  | cons v vs ih =>
    rw [iterDirDeriv_cons]
    exact hcs_dirDeriv ih v

theorem bdd_dir (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (v : ℝ × ℝ) : ∃ B : ℝ, ∀ w, ‖dirDeriv v f w‖ ≤ B :=
  (contDiff_dirDeriv hf v).continuous.bounded_above_of_compact_support (hcs_dirDeriv hc v)

theorem bdd_iter2 (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (v : ℝ × ℝ) : ∃ B : ℝ, ∀ w, ‖iterDirDeriv [v, v] f w‖ ≤ B :=
  (contDiff_iterDirDeriv hf [v, v]).continuous.bounded_above_of_compact_support
    (hcs_iter [v, v] hc)

theorem deriv_zero_outside {f : ℝ × ℝ → ℂ} {w : ℝ × ℝ} (hw : w ∉ tsupport f) (v : ℝ × ℝ) :
    dirDeriv v f w = 0 ∧ iterDirDeriv [v, v] f w = 0 := by
  have h0 : fderiv ℝ f w = 0 := by
    by_contra hne
    exact hw (support_fderiv_subset ℝ hne)
  have h1 : dirDeriv v f w = 0 := by simp [dirDeriv, h0]
  have hw2 : w ∉ tsupport (dirDeriv v f) := fun h => hw (tsupport_fderiv_apply_subset ℝ v h)
  have h2 : fderiv ℝ (dirDeriv v f) w = 0 := by
    by_contra hne
    exact hw2 (support_fderiv_subset ℝ hne)
  refine ⟨h1, ?_⟩
  simp only [iterDirDeriv_cons, iterDirDeriv_nil]
  simp [dirDeriv, h2]

/-- The fixed bump: `1` on the closed sup-norm ball of radius `1`, support the ball of radius `2`. -/
def bumpR : ContDiffBump (0 : ℝ × ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The bump as a complex-valued function. -/
def Gfun (w : ℝ × ℝ) : ℂ := ((bumpR w : ℝ) : ℂ)

theorem Gfun_contDiff : ContDiff ℝ ∞ Gfun :=
  Complex.ofRealCLM.contDiff.comp bumpR.contDiff

theorem Gfun_tsupport : tsupport Gfun ⊆ closedBall (0 : ℝ × ℝ) 2 := by
  have h := tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
    (bumpR : ℝ × ℝ → ℝ)
  rw [bumpR.tsupport_eq] at h
  exact h

theorem Gfun_hcs : HasCompactSupport Gfun :=
  bumpR.hasCompactSupport.comp_left Complex.ofReal_zero

theorem Gfun_norm_le (w : ℝ × ℝ) : ‖Gfun w‖ ≤ 1 := by
  unfold Gfun
  rw [Complex.norm_real, Real.norm_of_nonneg (bumpR.nonneg' w)]
  exact (by exact bumpR.le_one)

theorem Gfun_eq_one {w : ℝ × ℝ} (hw : ‖w‖ ≤ 1) : Gfun w = 1 := by
  unfold Gfun
  have h : bumpR w = 1 := bumpR.one_of_mem_closedBall (by
    show w ∈ closedBall (0 : ℝ × ℝ) (1 : ℝ)
    simpa using hw)
  simp [h]

theorem Gfun_eq_zero {w : ℝ × ℝ} (hw : 2 ≤ ‖w‖) : Gfun w = 0 := by
  unfold Gfun
  have h : bumpR w = 0 := bumpR.zero_of_le_dist (by
    show (2 : ℝ) ≤ dist w 0
    simpa [dist_zero_right] using hw)
  simp [h]

end UnforcedLeray.Short.PartI.RemOrig
