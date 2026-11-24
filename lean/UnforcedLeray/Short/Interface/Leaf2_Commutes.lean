import UnforcedLeray.Short.Interface.Statements

/-!
# Interface helper 2b-2: periodization commutes with the mode differential operators

Statement `PeriodizeCommutes` (Statements.lean, section 2b). For a similarity test `ψ` and a period
`P > 0`, the periodization `periodizeTest P ψ (τ, y) = ∑ᶠ k, ψ(τ + kP, y)` is, on a unit window
around any phase `t₀`, a finite sum of translates `ψ(· + kP, ·)`. Derivatives of a finite sum are
sums of derivatives, and the derivative of a translate is the derivative of `ψ` at the translated
phase. Terms outside a finite index set vanish on the window, by the compact time support of `ψ`.

Proved: `periodizeCommutes : PeriodizeCommutes`, from the finite-sum description on each window and
the compact time support of the test. Only the standard Mathlib and library facts are used.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-- A time derivative vanishes when `u ↦ φ(u, x)` vanishes on a unit window around `c`. -/
theorem pc_timeDerivative_zero {φ : SpaceTime → Space} {c : ℝ} {x : Space}
    (h : ∀ u : ℝ, |u - c| < 1 → φ (u, x) = 0) : timeDerivative φ c x = 0 := by
  unfold timeDerivative
  have hev : (fun u : ℝ => φ (u, x)) =ᶠ[𝓝 c] (fun _ : ℝ => (0 : Space)) := by
    filter_upwards [Metric.ball_mem_nhds c zero_lt_one] with u hu
    exact h u (by rwa [Metric.mem_ball, Real.dist_eq] at hu)
  rw [hev.fderiv_eq]
  simp [fderiv_const_apply]

/-- A spatial derivative vanishes when the phase slice `y ↦ φ(c, y)` is identically zero. -/
theorem pc_spatialDerivative_zero {φ : SpaceTime → Space} {c : ℝ}
    (h : ∀ y : Space, φ (c, y) = 0) (y : Space) : spatialDerivative φ c y = 0 := by
  unfold spatialDerivative
  have hfun : (fun y' : Space => φ (c, y')) = fun _ => (0 : Space) := funext h
  rw [hfun]
  simp [fderiv_const_apply]

/-- A spatial Laplacian vanishes when the phase slice is identically zero. -/
theorem pc_spatialLaplacian_zero {φ : SpaceTime → Space} {c : ℝ}
    (h : ∀ y : Space, φ (c, y) = 0) (x : Space) : spatialLaplacian φ c x = 0 := by
  have hz : ∀ y : Space, spatialDerivative φ c y = 0 := pc_spatialDerivative_zero h
  unfold spatialLaplacian
  simp [hz, fderiv_const_apply]

/-- Translation in the phase: the time derivative of `s ↦ ψ(s + a, x)` at `c` is the time
derivative of `ψ` at `c + a`. -/
theorem pc_fderiv_shift (ψ : SpaceTime → Space) (a c : ℝ) (x : Space) :
    fderiv ℝ (fun s : ℝ => ψ (s + a, x)) c = fderiv ℝ (fun u : ℝ => ψ (u, x)) (c + a) :=
  fderiv_comp_add_right (f := fun u : ℝ => ψ (u, x)) (x := c) a

theorem periodizeCommutes : PeriodizeCommutes := by
  unfold PeriodizeCommutes
  intro P ψ hP hψ z
  rcases z with ⟨t0, x⟩
  -- Step 0: the time support of `ψ` is bounded.
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : SpaceTime)).mp
    hψ.compact.isCompact.isBounded
  have hzero : ∀ (u : ℝ) (y : Space), R < |u| → ψ (u, y) = 0 := by
    intro u y hu
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 : ‖((u, y) : SpaceTime)‖ ≤ R := by
      have h0 := hR hmem
      rwa [Metric.mem_closedBall, dist_zero_right] at h0
    have h2 : |u| ≤ ‖((u, y) : SpaceTime)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_fst_le ((u, y) : SpaceTime)
    linarith
  -- Step 1: a finite index set serving the window `|u - t0| < 1`.
  obtain ⟨K, hK1⟩ : ∃ K : Finset ℤ, ∀ k : ℤ, k ∉ K → ∀ u : ℝ,
      |u - (t0 + (k : ℝ) * P)| < 1 → ∀ y : Space, ψ (u, y) = 0 := by
    refine ⟨Finset.Icc ⌈(-(R + 1) - t0) / P⌉ ⌊((R + 1) - t0) / P⌋, ?_⟩
    intro k hk u hu y
    apply hzero u y
    by_contra hle
    push_neg at hle
    apply hk
    rw [abs_le] at hle
    rw [abs_lt] at hu
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le, div_le_iff₀ hP]
      linarith [hle.1, hu.2]
    · rw [Int.le_floor, le_div_iff₀ hP]
      linarith [hle.2, hu.1]
  -- Step 2: the periodization is a fixed finite sum on the window `|s - t0| < 1`.
  have hfin : ∀ s : ℝ, |s - t0| < 1 → ∀ y : Space,
      periodizeTest P ψ (s, y) = ∑ k ∈ K, ψ (s + (k : ℝ) * P, y) := by
    intro s hs y
    unfold periodizeTest
    apply finsum_eq_sum_of_support_subset
    intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.mem_coe]
    by_contra hkK
    have hsk : |s + (k : ℝ) * P - (t0 + (k : ℝ) * P)| < 1 := by
      rw [show s + (k : ℝ) * P - (t0 + (k : ℝ) * P) = s - t0 by ring]
      exact hs
    have hz : ψ (s + (k : ℝ) * P, y) = 0 := hK1 k hkK (s + (k : ℝ) * P) hsk y
    exact hk hz
  -- Smoothness of the slices and their translates.
  have hsY : ∀ c : ℝ, ContDiff ℝ ∞ (fun y : Space => ψ (c, y)) := fun c =>
    hψ.smooth.comp
      (show ContDiff ℝ ∞ (fun y : Space => ((c, y) : SpaceTime)) from
        contDiff_const.prodMk contDiff_id)
  have hsh : ∀ (a : ℝ) (y : Space), ContDiff ℝ ∞ (fun s : ℝ => ψ (s + a, y)) := fun a y =>
    hψ.smooth.comp
      (show ContDiff ℝ ∞ (fun s : ℝ => ((s + a, y) : SpaceTime)) from
        (contDiff_id.add contDiff_const).prodMk contDiff_const)
  have hdY : ∀ (c : ℝ) (y : Space), DifferentiableAt ℝ (fun y' : Space => ψ (c, y')) y :=
    fun c y => ((hsY c).differentiable (by simp)) y
  have hdT : ∀ k : ℤ, DifferentiableAt ℝ (fun s : ℝ => ψ (s + (k : ℝ) * P, x)) t0 :=
    fun k => ((hsh ((k : ℝ) * P) x).differentiable (by simp)) t0
  have hnhds : ∀ᶠ s in 𝓝 t0, |s - t0| < 1 := by
    filter_upwards [Metric.ball_mem_nhds t0 zero_lt_one] with s hs
    rwa [Metric.mem_ball, Real.dist_eq] at hs
  -- Part 1: the time derivative.
  have part1 : timeDerivative (periodizeTest P ψ) t0 x
      = ∑ᶠ k : ℤ, timeDerivative ψ (t0 + (k : ℝ) * P) x := by
    have hev : (fun s : ℝ => periodizeTest P ψ (s, x)) =ᶠ[𝓝 t0]
        (fun s : ℝ => ∑ k ∈ K, ψ (s + (k : ℝ) * P, x)) := by
      filter_upwards [hnhds] with s hs
      exact hfin s hs x
    have hsupp : Function.support (fun k : ℤ => timeDerivative ψ (t0 + (k : ℝ) * P) x)
        ⊆ (K : Set ℤ) := by
      intro k hk
      rw [Finset.mem_coe]
      by_contra hkK
      rw [Function.mem_support] at hk
      apply hk
      apply pc_timeDerivative_zero
      intro u hu
      exact hK1 k hkK u hu x
    change fderiv ℝ (fun s : ℝ => periodizeTest P ψ (s, x)) t0 1 = _
    rw [hev.fderiv_eq, fderiv_fun_sum (fun k _ => hdT k), ContinuousLinearMap.sum_apply,
      finsum_eq_sum_of_support_subset _ hsupp]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun L : ℝ →L[ℝ] Space => L 1)
      (pc_fderiv_shift ψ ((k : ℝ) * P) t0 x)
  -- Part 3: the spatial derivative in the direction `x` at the point `(t0, x)`.
  have hfunY : (fun y : Space => periodizeTest P ψ (t0, y)) =
      fun y : Space => ∑ k ∈ K, ψ (t0 + (k : ℝ) * P, y) :=
    funext fun y => hfin t0 (by simp) y
  have hSD : ∀ y : Space, spatialDerivative (periodizeTest P ψ) t0 y
      = ∑ k ∈ K, spatialDerivative ψ (t0 + (k : ℝ) * P) y := by
    intro y
    change fderiv ℝ (fun y' : Space => periodizeTest P ψ (t0, y')) y
      = ∑ k ∈ K, fderiv ℝ (fun y' : Space => ψ (t0 + (k : ℝ) * P, y')) y
    rw [hfunY, fderiv_fun_sum (fun (k : ℤ) _ => hdY (t0 + (k : ℝ) * P) y)]
  have hsupp3 : Function.support (fun k : ℤ => spatialDerivative ψ (t0 + (k : ℝ) * P) x x)
      ⊆ (K : Set ℤ) := by
    intro k hk
    rw [Finset.mem_coe]
    by_contra hkK
    rw [Function.mem_support] at hk
    apply hk
    have hz : ∀ y : Space, ψ (t0 + (k : ℝ) * P, y) = 0 := fun y =>
      hK1 k hkK (t0 + (k : ℝ) * P) (by simp) y
    show spatialDerivative ψ (t0 + (k : ℝ) * P) x x = 0
    simp [pc_spatialDerivative_zero (φ := ψ) (c := t0 + (k : ℝ) * P) hz x]
  have part3 : spatialDerivative (periodizeTest P ψ) t0 x x
      = ∑ᶠ k : ℤ, spatialDerivative ψ (t0 + (k : ℝ) * P) x x := by
    rw [hSD x, ContinuousLinearMap.sum_apply, finsum_eq_sum_of_support_subset _ hsupp3]
  -- Part 2: the spatial Laplacian.
  have hfunInner : ∀ i : Fin 3,
      (fun y : Space => spatialDerivative (periodizeTest P ψ) t0 y (coordinateVector i))
        = fun y : Space => ∑ k ∈ K, spatialDerivative ψ (t0 + (k : ℝ) * P) y (coordinateVector i) := by
    intro i
    funext y
    rw [hSD y, ContinuousLinearMap.sum_apply]
  have hLapDiff : ∀ (c : ℝ) (i : Fin 3) (y : Space),
      DifferentiableAt ℝ (fun y' : Space => spatialDerivative ψ c y' (coordinateVector i)) y := by
    intro c i y
    have hfd : DifferentiableAt ℝ (fderiv ℝ (fun y' : Space => ψ (c, y'))) y :=
      ((ContDiff.fderiv_right (m := ∞) (hsY c) (by simp)).differentiable (by simp)) y
    exact hfd.clm_apply (differentiableAt_const _)
  have hsupp2 : Function.support (fun k : ℤ => spatialLaplacian ψ (t0 + (k : ℝ) * P) x)
      ⊆ (K : Set ℤ) := by
    intro k hk
    rw [Finset.mem_coe]
    by_contra hkK
    rw [Function.mem_support] at hk
    apply hk
    exact pc_spatialLaplacian_zero (φ := ψ) (c := t0 + (k : ℝ) * P)
      (fun y => hK1 k hkK (t0 + (k : ℝ) * P) (by simp) y) x
  have part2 : spatialLaplacian (periodizeTest P ψ) t0 x
      = ∑ᶠ k : ℤ, spatialLaplacian ψ (t0 + (k : ℝ) * P) x := by
    have hL : ∀ i : Fin 3,
        fderiv ℝ (fun y : Space => spatialDerivative (periodizeTest P ψ) t0 y
          (coordinateVector i)) x (coordinateVector i)
          = ∑ k ∈ K, fderiv ℝ (fun y : Space => spatialDerivative ψ (t0 + (k : ℝ) * P) y
              (coordinateVector i)) x (coordinateVector i) := by
      intro i
      rw [hfunInner i, fderiv_fun_sum (fun (k : ℤ) _ => hLapDiff (t0 + (k : ℝ) * P) i x),
        ContinuousLinearMap.sum_apply]
    rw [finsum_eq_sum_of_support_subset _ hsupp2]
    unfold spatialLaplacian
    simp only [hL]
    exact Finset.sum_comm
  exact ⟨part1, part2, part3⟩

end UnforcedLeray.Short.Interface
