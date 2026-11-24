import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
The cut-off is `etaCut R x = etaBump (x.2 / R)`; with `c = R⁻¹` it is the profile `etaProfT (c * x.2)`.
Its planar derivatives are computed through the chain rule (`pd_scale`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- The one-variable profile of the bump (`= 1` on `[-1,1]`, `= 0` off `(-2,2)`). -/
abbrev etaProfT : ℝ → ℝ := fun s => etaBump s

theorem etaProfT_bdd (g : ℝ → ℝ) (hg : Continuous g) (hgcs : HasCompactSupport g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |g y| ≤ K := by
  obtain ⟨K, hK⟩ := hg.bounded_above_of_compact_support hgcs
  refine ⟨max K 0, le_max_right _ _, fun y => ?_⟩
  rw [← Real.norm_eq_abs]
  exact le_trans (hK y) (le_max_left _ _)

theorem etaProfT_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etaProfT := etaBump.contDiff

theorem etaProfT_deriv_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv etaProfT) := by
  have h := ContDiff.iterate_deriv 1 etaProfT_contDiff
  simpa using h

theorem etaProfT_hasDerivAt (s : ℝ) : HasDerivAt etaProfT (deriv etaProfT s) s :=
  ((etaProfT_contDiff.differentiable (by simp)) s).hasDerivAt

theorem etaProfT_hasDerivAt2 (s : ℝ) :
    HasDerivAt (deriv etaProfT) (deriv (deriv etaProfT) s) s :=
  ((etaProfT_deriv_contDiff.differentiable (by simp)) s).hasDerivAt

theorem etaProfT_nonneg (s : ℝ) : 0 ≤ etaProfT s := etaBump.nonneg

theorem etaProfT_le_one (s : ℝ) : etaProfT s ≤ 1 := etaBump.le_one

theorem etaProfT_one {s : ℝ} (h : |s| ≤ 1) : etaProfT s = 1 := by
  have hm : s ∈ Metric.closedBall (0 : ℝ) etaBump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact h
  exact etaBump.one_of_mem_closedBall hm

theorem etaProfT_zero {s : ℝ} (h : 2 ≤ |s|) : etaProfT s = 0 := by
  have hd : etaBump.rOut ≤ dist s 0 := by
    rw [Real.dist_eq, sub_zero]
    exact h
  exact etaBump.zero_of_le_dist hd

theorem deriv_etaProfT_zero {s : ℝ} (h : |s| < 1) : deriv etaProfT s = 0 := by
  have hev : etaProfT =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp h).1 (abs_lt.mp h).2] with y hy
    exact etaProfT_one (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  rw [hev.deriv_eq, deriv_const]

theorem deriv_deriv_etaProfT_zero {s : ℝ} (h : |s| < 1) :
    deriv (deriv etaProfT) s = 0 := by
  have hev : deriv etaProfT =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp h).1 (abs_lt.mp h).2] with y hy
    exact deriv_etaProfT_zero (abs_lt.mpr hy)
  rw [hev.deriv_eq, deriv_const]

theorem etaProfT_bdd1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |deriv etaProfT y| ≤ K :=
  etaProfT_bdd _ (etaProfT_contDiff.continuous_deriv (by simp))
    etaBump.hasCompactSupport.deriv

theorem etaProfT_bdd2 : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |deriv (deriv etaProfT) y| ≤ K :=
  etaProfT_bdd _ (etaProfT_deriv_contDiff.continuous_deriv (by simp))
    etaBump.hasCompactSupport.deriv.deriv

/-- `etaCut R` as a function of `x.2` (the cut-off is independent of `q`). -/
theorem etaCut_eq_profile (R : ℝ) (y : B0579.Plane) :
    etaCut R y = etaProfT (R⁻¹ * y.2) := by
  show etaBump (y.2 / R) = etaBump (R⁻¹ * y.2)
  rw [div_eq_inv_mul]

/-- Planar derivative of a scaled profile `ψ (c * x.2)`. -/
theorem tdEta_pd_scale (ψ ψ' : ℝ → ℝ) (c : ℝ) (hψ : ∀ s, HasDerivAt ψ (ψ' s) s)
    (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun y : B0579.Plane => ψ (c * y.2)) x =
      ψ' (c * x.2) * (c * (B0579.dir j).2) := by
  have hL : HasFDerivAt (fun y : B0579.Plane => c * y.2)
      (c • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    convert (c • ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt using 1
    ext y
    simp
  have h := (hψ (c * x.2)).comp_hasFDerivAt x hL
  have h' : HasFDerivAt (fun y : B0579.Plane => ψ (c * y.2))
      (ψ' (c * x.2) • (c • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := h
  unfold B0579.pd
  rw [h'.fderiv]
  simp

theorem tdEta_bound_one (a u K : ℝ) (hK : 0 ≤ K) (ha : |a| ≤ K) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |a * u| ≤ K := by
  rw [abs_mul, abs_of_nonneg hu0]
  have h1 : 0 ≤ |a| := abs_nonneg a
  nlinarith

theorem tdEta_bound_two (a u K : ℝ) (hK : 0 ≤ K) (ha : |a| ≤ K) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |a * u * u| ≤ K := by
  rw [abs_mul, abs_mul, abs_of_nonneg hu0]
  have h1 : 0 ≤ |a| := abs_nonneg a
  have h2 : u * u ≤ 1 := by nlinarith
  nlinarith

/-- **Leaf `/1`: the `η`-cut-off.** -/
theorem etaCutProps : UnforcedLeray.Short.IIb.TdSums.EtaCutProps := by
  obtain ⟨K1, hK1nn, hK1⟩ := etaProfT_bdd1
  obtain ⟨K2, hK2nn, hK2⟩ := etaProfT_bdd2
  refine ⟨K1 + K2, by linarith, fun R hR => ?_⟩
  have hRpos : 0 < R := by linarith
  have hR0 : R ≠ 0 := hRpos.ne'
  have hcpos : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hc1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hsv : ∀ y : B0579.Plane, |R⁻¹ * y.2| = R⁻¹ * |y.2| := fun y => by
    rw [abs_mul, abs_of_pos hcpos]
  have hfun : etaCut R = fun y : B0579.Plane => etaProfT (R⁻¹ * y.2) :=
    funext (etaCut_eq_profile R)
  have hd0 : (B0579.dir 0).2 = 0 := by simp [B0579.dir]
  have hd1 : (B0579.dir 1).2 = 1 := by simp [B0579.dir]
  have hp0 : ∀ x : B0579.Plane, B0579.pd 0 (etaCut R) x = 0 := by
    intro x
    rw [hfun, tdEta_pd_scale etaProfT (deriv etaProfT) R⁻¹ etaProfT_hasDerivAt 0 x, hd0]
    simp
  have hp1 : ∀ x : B0579.Plane,
      B0579.pd 1 (etaCut R) x = deriv etaProfT (R⁻¹ * x.2) * (R⁻¹ * 1) := by
    intro x
    rw [hfun, tdEta_pd_scale etaProfT (deriv etaProfT) R⁻¹ etaProfT_hasDerivAt 1 x, hd1]
  have hpz : ∀ x : B0579.Plane, B0579.pd 0 (fun _ : B0579.Plane => (0 : ℝ)) x = 0 :=
    fun x => by simp [B0579.pd]
  have hz : B0579.pd 0 (etaCut R) = fun _ => 0 := funext hp0
  have hsec : B0579.pd 1 (etaCut R) =
      fun y : B0579.Plane => deriv etaProfT (R⁻¹ * y.2) * (R⁻¹ * 1) := funext hp1
  have hlap : ∀ x : B0579.Plane,
      lapP (etaCut R) x = deriv (deriv etaProfT) (R⁻¹ * x.2) * (R⁻¹ * 1) * (R⁻¹ * 1) := by
    intro x
    have key2 : B0579.pd 1
        (fun y : B0579.Plane => deriv etaProfT (R⁻¹ * y.2) * (R⁻¹ * 1)) x =
        deriv (deriv etaProfT) (R⁻¹ * x.2) * (R⁻¹ * 1) * (R⁻¹ * (B0579.dir 1).2) :=
      tdEta_pd_scale (fun s => deriv etaProfT s * (R⁻¹ * 1))
        (fun s => deriv (deriv etaProfT) s * (R⁻¹ * 1)) R⁻¹
        (fun s => (etaProfT_hasDerivAt2 s).mul_const (R⁻¹ * 1)) 1 x
    unfold lapP
    rw [hz, hsec, hpz, key2, hd1, zero_add]
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (etaCut R) := by
    rw [hfun]
    exact etaProfT_contDiff.comp ((contDiff_const (c := R⁻¹)).mul contDiff_snd)
  have hu : 0 ≤ R⁻¹ * 1 := (mul_pos hcpos one_pos).le
  have hu1 : R⁻¹ * 1 ≤ 1 := by rw [mul_one]; exact hc1
  refine ⟨hcd, fun x => ⟨?_, ?_, ?_, ?_, fun a => rfl, hp0 x, ?_, ?_, ?_⟩⟩
  · rw [etaCut_eq_profile]
    exact etaProfT_nonneg _
  · rw [etaCut_eq_profile]
    exact etaProfT_le_one _
  · intro h
    rw [etaCut_eq_profile]
    apply etaProfT_one
    rw [hsv]
    calc R⁻¹ * |x.2| ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left h hcpos.le
      _ = 1 := inv_mul_cancel₀ hR0
  · intro h
    rw [etaCut_eq_profile]
    apply etaProfT_zero
    rw [hsv]
    calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
      _ ≤ R⁻¹ * |x.2| := mul_le_mul_of_nonneg_left h hcpos.le
  · rw [hp1 x]
    exact tdEta_bound_one _ _ _ (by linarith) (hK1 _) hu hu1 |>.trans (by linarith)
  · rw [hlap x]
    exact tdEta_bound_two _ _ _ hK2nn (hK2 _) hu hu1 |>.trans (by linarith)
  · intro h
    have hlt : |R⁻¹ * x.2| < 1 := by
      rw [hsv]
      calc R⁻¹ * |x.2| < R⁻¹ * R := mul_lt_mul_of_pos_left h hcpos
        _ = 1 := inv_mul_cancel₀ hR0
    constructor
    · rw [hp1 x, deriv_etaProfT_zero hlt]
      simp
    · rw [hlap x, deriv_deriv_etaProfT_zero hlt]
      simp

end TdSums

end UnforcedLeray.Short.IIb
