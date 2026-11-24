import UnforcedLeray.Short.PartI.Sub.C09.RemOrigCalc

/-!
# Helper: cutoffs at the origin for `RemovableOrigin` (task PartI:C09)

Scaled cutoff `cutG ε z = Gfun (ε⁻¹ • z)` (equal to `1` on the sup-norm ball of radius `ε`, zero
off the ball of radius `2ε`), the test function `φ - φ cutG ε` supported away from the origin, and
the pointwise Laplacian identity used in the main argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.RemOrig

open UnforcedLeray.PlanarBS.Sob UnforcedLeray.B0121

/-- The Laplacian `∂₁∂₁ + ∂₂∂₂` used in `WeakLapOn`. -/
def lapf (φ : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z

/-- The cutoff at scale `ε`. -/
def cutG (ε : ℝ) : ℝ × ℝ → ℂ := fun y => Gfun (ε⁻¹ • y)

theorem cutG_contDiff (ε : ℝ) : ContDiff ℝ ∞ (cutG ε) :=
  Gfun_contDiff.comp (contDiff_const_smul _)

theorem norm_scale_inv {ε : ℝ} (hε : 0 < ε) (z : ℝ × ℝ) : ‖ε⁻¹ • z‖ = ε⁻¹ * ‖z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]

theorem cutG_norm_le (ε : ℝ) (z : ℝ × ℝ) : ‖cutG ε z‖ ≤ 1 :=
  Gfun_norm_le _

theorem cutG_eq_one {ε : ℝ} (hε : 0 < ε) {z : ℝ × ℝ} (hz : ‖z‖ < ε) : cutG ε z = 1 := by
  unfold cutG
  apply Gfun_eq_one
  rw [norm_scale_inv hε]
  have h1 : ε⁻¹ * ‖z‖ ≤ ε⁻¹ * ε := mul_le_mul_of_nonneg_left hz.le (inv_pos.2 hε).le
  rw [inv_mul_cancel₀ hε.ne'] at h1
  exact h1

theorem cutG_eq_zero {ε : ℝ} (hε : 0 < ε) {z : ℝ × ℝ} (hz : 2 * ε ≤ ‖z‖) :
    cutG ε z = 0 := by
  unfold cutG
  apply Gfun_eq_zero
  rw [norm_scale_inv hε]
  have h1 : ε⁻¹ * (2 * ε) ≤ ε⁻¹ * ‖z‖ := mul_le_mul_of_nonneg_left hz (inv_pos.2 hε).le
  have h2 : ε⁻¹ * (2 * ε) = 2 := by field_simp
  linarith

theorem cutG_outside {ε : ℝ} (hε : 0 < ε) {z : ℝ × ℝ} (hz : 2 * ε < ‖z‖) (v : ℝ × ℝ) :
    dirDeriv v (cutG ε) z = 0 ∧ iterDirDeriv [v, v] (cutG ε) z = 0 := by
  have hw : ε⁻¹ • z ∉ tsupport Gfun := by
    intro h
    have h2 := Gfun_tsupport h
    rw [mem_closedBall, dist_zero_right, norm_scale_inv hε] at h2
    have h3 : ε⁻¹ * (2 * ε) = 2 := by field_simp
    have h4 : ε⁻¹ * (2 * ε) < ε⁻¹ * ‖z‖ := mul_lt_mul_of_pos_left hz (inv_pos.2 hε)
    linarith
  obtain ⟨h1, h2⟩ := deriv_zero_outside hw v
  unfold cutG
  refine ⟨?_, ?_⟩
  · rw [dirDeriv_scale_pt Gfun_contDiff ε⁻¹ v z, h1, smul_zero]
  · rw [iterDirDeriv2_scale Gfun_contDiff ε⁻¹ v z, h2, smul_zero, smul_zero]

theorem cutG_dir_bound {ε : ℝ} (hε : 0 < ε) (v z : ℝ × ℝ) {B : ℝ}
    (hB : ∀ w, ‖dirDeriv v Gfun w‖ ≤ B) : ‖dirDeriv v (cutG ε) z‖ ≤ ε⁻¹ * B := by
  unfold cutG
  rw [dirDeriv_scale_pt Gfun_contDiff ε⁻¹ v z, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hε)]
  exact mul_le_mul_of_nonneg_left (hB _) (inv_pos.2 hε).le

theorem cutG_iter_bound {ε : ℝ} (hε : 0 < ε) (v z : ℝ × ℝ) {B : ℝ}
    (hB : ∀ w, ‖iterDirDeriv [v, v] Gfun w‖ ≤ B) :
    ‖iterDirDeriv [v, v] (cutG ε) z‖ ≤ ε⁻¹ * (ε⁻¹ * B) := by
  unfold cutG
  rw [iterDirDeriv2_scale Gfun_contDiff ε⁻¹ v z, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hε)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB _) (inv_pos.2 hε).le)
    (inv_pos.2 hε).le

/-- The test function `φ - φ · cutG ε`, which vanishes near the origin. -/
theorem isTestFn_psi {φ : ℝ × ℝ → ℂ} (hφ : IsTestFn univ φ) {ε : ℝ} (hε : 0 < ε) :
    IsTestFn ({0}ᶜ : Set (ℝ × ℝ)) (fun z => φ z - φ z * cutG ε z) := by
  have hsm : ContDiff ℝ ∞ (fun z => φ z - φ z * cutG ε z) :=
    hφ.smooth.sub (hφ.smooth.mul (cutG_contDiff ε))
  have hcs : HasCompactSupport (fun z => φ z - φ z * cutG ε z) :=
    HasCompactSupport.intro hφ.compact (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
  refine ⟨hsm, hcs, ?_⟩
  have hsupp : Function.support (fun z => φ z - φ z * cutG ε z) ⊆ {z : ℝ × ℝ | ε ≤ ‖z‖} := by
    intro z hz
    by_contra hlt
    apply hz
    have h1 : ‖z‖ < ε := lt_of_not_ge hlt
    simp [cutG_eq_one hε h1]
  have hclosed : IsClosed {z : ℝ × ℝ | ε ≤ ‖z‖} :=
    isClosed_le continuous_const continuous_norm
  have ht : tsupport (fun z => φ z - φ z * cutG ε z) ⊆ {z : ℝ × ℝ | ε ≤ ‖z‖} :=
    closure_minimal hsupp hclosed
  intro z hz
  have h2 : ε ≤ ‖z‖ := ht hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h0
  rw [h0, norm_zero] at h2
  linarith

theorem lapf_psi (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (ε : ℝ) (z : ℝ × ℝ) :
    lapf (fun y => φ y - φ y * cutG ε y) z
      = lapf φ z - (cutG ε z * lapf φ z
        + (2 * (dirDeriv (ev 0) φ z * dirDeriv (ev 0) (cutG ε) z
              + dirDeriv (ev 1) φ z * dirDeriv (ev 1) (cutG ε) z)
          + φ z * (iterDirDeriv [ev 0, ev 0] (cutG ε) z
              + iterDirDeriv [ev 1, ev 1] (cutG ε) z))) := by
  have hG := cutG_contDiff ε
  have hQ : ContDiff ℝ ∞ (fun y => φ y * cutG ε y) := hφ.mul hG
  unfold lapf
  rw [iterDirDeriv2_sub hφ hQ (ev 0) z, iterDirDeriv2_sub hφ hQ (ev 1) z,
    iterDirDeriv2_mul hφ hG (ev 0) z, iterDirDeriv2_mul hφ hG (ev 1) z]
  ring

theorem isTestFn_mul_smooth {a f : ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hf : IsTestFn univ f) :
    IsTestFn univ (fun z => a z * f z) :=
  isTestFn_of_smooth_cs (ha.mul hf.smooth)
    (HasCompactSupport.intro hf.compact (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]))

theorem lapf_testFn {φ : ℝ × ℝ → ℂ} (hφ : IsTestFn univ φ) : IsTestFn univ (lapf φ) := by
  refine isTestFn_of_smooth_cs ?_ (HasCompactSupport.intro hφ.compact ?_)
  · exact (contDiff_iterDirDeriv hφ.smooth [ev 0, ev 0]).add
      (contDiff_iterDirDeriv hφ.smooth [ev 1, ev 1])
  · intro z hz
    simp only [lapf, (deriv_zero_outside hz (ev 0)).2, (deriv_zero_outside hz (ev 1)).2, add_zero]

/-- The cross and lower-order terms `T_ε = 2 ∑ ∂φ ∂cutG + φ ∆cutG`. -/
def Tfun (φ : ℝ × ℝ → ℂ) (ε : ℝ) (z : ℝ × ℝ) : ℂ :=
  2 * (dirDeriv (ev 0) φ z * dirDeriv (ev 0) (cutG ε) z
      + dirDeriv (ev 1) φ z * dirDeriv (ev 1) (cutG ε) z)
    + φ z * (iterDirDeriv [ev 0, ev 0] (cutG ε) z + iterDirDeriv [ev 1, ev 1] (cutG ε) z)

theorem Tfun_testFn {φ : ℝ × ℝ → ℂ} (hφ : IsTestFn univ φ) (ε : ℝ) :
    IsTestFn univ (Tfun φ ε) := by
  have hG := cutG_contDiff ε
  have a0 := contDiff_dirDeriv hφ.smooth (ev 0)
  have a1 := contDiff_dirDeriv hφ.smooth (ev 1)
  have b0 := contDiff_dirDeriv hG (ev 0)
  have b1 := contDiff_dirDeriv hG (ev 1)
  have l0 := contDiff_iterDirDeriv hG [ev 0, ev 0]
  have l1 := contDiff_iterDirDeriv hG [ev 1, ev 1]
  have hs : ContDiff ℝ ∞ (Tfun φ ε) := by
    unfold Tfun
    exact (contDiff_const.mul ((a0.mul b0).add (a1.mul b1))).add (hφ.smooth.mul (l0.add l1))
  refine isTestFn_of_smooth_cs hs (HasCompactSupport.intro hφ.compact ?_)
  intro z hz
  have e0 := (deriv_zero_outside hz (ev 0)).1
  have e1 := (deriv_zero_outside hz (ev 1)).1
  have ep := image_eq_zero_of_notMem_tsupport hz
  unfold Tfun
  rw [e0, e1, ep]
  simp

end UnforcedLeray.Short.PartI.RemOrig
