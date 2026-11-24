import UnforcedLeray.Infra.RieszProjection.Projection

/-!
# Riesz projections, III: the two exponential rates

Let `X` be a complex Banach space, `T : X →L[ℂ] X`, and `r > 0` with the circle `|z| = r` in the
resolvent set. With `P = rieszProj T r` and the outer inverse `S = rieszOuterInv T r`:

* `exists_norm_pow_mul_rieszProj_le`: `‖T ^ n P‖ ≤ C ρ ^ n` for some `0 < ρ < r`;
* `exists_norm_rieszOuterInv_pow_le`: `‖S ^ n‖ ≤ C R⁻¹ ^ n` for some `R > r`;
* `exists_rates`: both at once, with one constant `C ≥ 1`
  (`‖ℳ^n P_-‖ ≤ C e^{β_- n T}`, `‖ℳ_+^{-n}‖ ≤ C e^{-β_+ n T}` of `paper/main.tex`, lines 363-366).

The proof moves the circle into the annulus free of spectrum (`contourOp_eq_of_annulus`): to
`|z| = r - δ` for `T ^ n P = (2πi)⁻¹ ∮ z ^ n (z - T)⁻¹ dz` and to `|z| = r + δ` for
`S ^ (m + 1) = -(2πi)⁻¹ ∮ z^{-(m+1)} (z - T)⁻¹ dz`, and bounds the integrals by the length of the
circle times the maximum of the integrand.

We also prove the elementary spectral-radius bound used for the restricted operators:
`spectrum_subset_closedBall_of_norm_pow_le` (`‖a ^ n‖ ≤ C ρ ^ n` for all `n` implies
`spectrum ℂ a ⊆ closedBall 0 ρ`) and its inverse form `spectrum_subset_of_norm_inv_pow_le`.
-/

set_option autoImplicit false

noncomputable section

open Metric Complex Filter Topology
open scoped Real

namespace UnforcedLeray.Infra.RieszProjection

/-! ### Spectral bounds from power bounds in a Banach algebra -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- If `‖a ^ n‖ ≤ C ρ ^ n` for all `n`, the spectrum of `a` lies in the closed disc of radius
`ρ` (the spectral radius is at most `ρ`). -/
theorem spectrum_subset_closedBall_of_norm_pow_le (a : A) {C ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, ‖a ^ n‖ ≤ C * ρ ^ n) : spectrum ℂ a ⊆ closedBall (0 : ℂ) ρ := by
  intro k hk
  rw [mem_closedBall_zero_iff]
  by_contra hlt
  rw [not_le] at hlt
  have hk0 : 0 < ‖k‖ := hρ.trans_lt hlt
  have hpow : ∀ n : ℕ, ‖k‖ ^ n ≤ C * ‖(1 : A)‖ * ρ ^ n := by
    intro n
    have h1 := spectrum.subset_closedBall_norm_mul (𝕜 := ℂ) (a ^ n) (spectrum.pow_mem_pow a n hk)
    rw [mem_closedBall_zero_iff, norm_pow] at h1
    calc ‖k‖ ^ n ≤ ‖a ^ n‖ * ‖(1 : A)‖ := h1
      _ ≤ C * ρ ^ n * ‖(1 : A)‖ := by
          gcongr
          exact h n
      _ = C * ‖(1 : A)‖ * ρ ^ n := by ring
  have ht : Tendsto (fun n : ℕ => (ρ / ‖k‖) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hk0).2 hlt)
  have hev := ht.const_mul (C * ‖(1 : A)‖)
  rw [mul_zero] at hev
  obtain ⟨n, hn⟩ := (hev.eventually_lt_const zero_lt_one).exists
  have hkn : 0 < ‖k‖ ^ n := pow_pos hk0 n
  rw [div_pow, ← mul_div_assoc, div_lt_one hkn] at hn
  linarith [hpow n]

/-- If `a b = b a = 1` and `‖b ^ n‖ ≤ C R⁻¹ ^ n` for all `n`, the spectrum of `a` lies in
`{z | R ≤ ‖z‖}`. -/
theorem spectrum_subset_of_norm_inv_pow_le {a b : A} (hab : a * b = 1) (hba : b * a = 1)
    {C R : ℝ} (hR : 0 < R) (h : ∀ n : ℕ, ‖b ^ n‖ ≤ C * R⁻¹ ^ n) :
    spectrum ℂ a ⊆ {z : ℂ | R ≤ ‖z‖} := by
  intro z hz
  by_contra hlt
  replace hlt : ‖z‖ < R := not_le.1 hlt
  apply hz
  have h1 : spectrum ℂ (z • b) ⊆ closedBall (0 : ℂ) (‖z‖ * R⁻¹) := by
    refine spectrum_subset_closedBall_of_norm_pow_le (C := C) (z • b) (by positivity)
      (fun n => ?_)
    rw [smul_pow, norm_smul, norm_pow]
    calc ‖z‖ ^ n * ‖b ^ n‖ ≤ ‖z‖ ^ n * (C * R⁻¹ ^ n) := by
          gcongr
          exact h n
      _ = C * (‖z‖ * R⁻¹) ^ n := by ring
  have h2 : (1 : ℂ) ∈ resolventSet ℂ (z • b) := by
    by_contra h3
    have h4 := h1 h3
    rw [mem_closedBall_zero_iff, norm_one] at h4
    have h5 : ‖z‖ * R⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hR, one_mul]
      exact hlt
    linarith
  have h3 : IsUnit (1 - z • b) := by
    have := spectrum.mem_resolventSet_iff.1 h2
    rwa [map_one] at this
  have heq : algebraMap ℂ A z - a = -(1 - z • b) * a := by
    rw [neg_mul, sub_mul, one_mul, smul_mul_assoc, hba, Algebra.algebraMap_eq_smul_one]
    abel
  show IsUnit (algebraMap ℂ A z - a)
  rw [heq]
  exact h3.neg.mul ⟨⟨a, b, hab, hba⟩, rfl⟩

end BanachAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-! ### The two rates -/

section Rates

variable {T : X →L[ℂ] X} {r : ℝ}

omit [CompleteSpace X] in
/-- The norm of a contour operator is at most the radius times a bound of the integrand. -/
theorem norm_contourOp_le {s : ℝ} (hs : 0 ≤ s) {f : ℂ → ℂ} {M : ℝ}
    (hM : ∀ z ∈ sphere (0 : ℂ) s, ‖f z • resolvent T z‖ ≤ M) : ‖contourOp T s f‖ ≤ s * M :=
  circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hs hM

/-- A bound `M ≥ 0` of the resolvent on a circle in the resolvent set. -/
theorem exists_norm_resolvent_le_on_sphere {s : ℝ} (hs : sphere (0 : ℂ) s ⊆ resolventSet ℂ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ sphere (0 : ℂ) s, ‖resolvent T z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) s).exists_bound_of_continuousOn
    (continuousOn_resolvent hs)
  exact ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩

/-- **Inner rate**: `‖T ^ n P‖ ≤ C ρ ^ n` for some `0 < ρ < r`. -/
theorem exists_norm_pow_mul_rieszProj_le (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ < r ∧ 0 ≤ C ∧ ∀ n : ℕ, ‖T ^ n * rieszProj T r‖ ≤ C * ρ ^ n := by
  obtain ⟨δ, hδ, hδr, hann⟩ := exists_annulus_subset_resolventSet T hr hT
  have hρ : 0 < r - δ := by linarith
  obtain ⟨M, hM0, hM⟩ :=
    exists_norm_resolvent_le_on_sphere (sphere_subset_of_annulus hann (s := r - δ) le_rfl
      (by linarith))
  refine ⟨r - δ, (r - δ) * M, hρ, by linarith, by positivity, fun n => ?_⟩
  have hmove : contourOp T (r - δ) (fun z => z ^ n) = contourOp T r (fun z => z ^ n) :=
    contourOp_eq_of_annulus hρ (by linarith) (fun z h1 h2 => hann z h1 (by linarith))
      (fun _ _ _ => differentiableAt_pow n)
  rw [pow_mul_rieszProj hr.le hT n, ← hmove]
  refine (norm_contourOp_le hρ.le (M := (r - δ) ^ n * M) (fun z hz => ?_)).trans
    (le_of_eq (by ring))
  rw [norm_smul, norm_pow, mem_sphere_zero_iff_norm.1 hz]
  gcongr
  exact hM z hz

/-- **Outer rate**: `‖S ^ n‖ ≤ C R⁻¹ ^ n` for some `R > r` and `C ≥ 1`, where
`S = rieszOuterInv T r` is the inverse of `T` on the range of `1 - P`. -/
theorem exists_norm_rieszOuterInv_pow_le (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ R C : ℝ, r < R ∧ 1 ≤ C ∧ ∀ n : ℕ, ‖rieszOuterInv T r ^ n‖ ≤ C * R⁻¹ ^ n := by
  obtain ⟨δ, hδ, -, hann⟩ := exists_annulus_subset_resolventSet T hr hT
  have hR : 0 < r + δ := by linarith
  obtain ⟨M, hM0, hM⟩ :=
    exists_norm_resolvent_le_on_sphere (sphere_subset_of_annulus hann (s := r + δ)
      (by linarith) le_rfl)
  refine ⟨r + δ, max 1 ((r + δ) * M), by linarith, le_max_left _ _, fun n => ?_⟩
  rcases n with _ | m
  · rw [pow_zero, pow_zero, mul_one]
    exact (ContinuousLinearMap.norm_id_le).trans (le_max_left _ _)
  have hmove : contourOp T r (fun z => z⁻¹ ^ (m + 1)) =
      contourOp T (r + δ) (fun z => z⁻¹ ^ (m + 1)) := by
    refine contourOp_eq_of_annulus hr (by linarith) (fun z h1 h2 => hann z (by linarith) h2)
      (fun z h1 _ => ?_)
    have hz : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      linarith
    exact (differentiableAt_inv hz).pow (m + 1)
  rw [rieszOuterInv_pow_succ hr hT m, norm_neg, hmove]
  refine (norm_contourOp_le hR.le (M := (r + δ)⁻¹ ^ (m + 1) * M) (fun z hz => ?_)).trans ?_
  · rw [norm_smul, norm_pow, norm_inv, mem_sphere_zero_iff_norm.1 hz]
    gcongr
    exact hM z hz
  · calc (r + δ) * ((r + δ)⁻¹ ^ (m + 1) * M) = (r + δ) * M * (r + δ)⁻¹ ^ (m + 1) := by ring
      _ ≤ max 1 ((r + δ) * M) * (r + δ)⁻¹ ^ (m + 1) := by
          gcongr
          exact le_max_right _ _

/-- **The two rates of the Riesz splitting.** For every circle `|z| = r` (`r > 0`) in the
resolvent set there are `0 < ρ < r < R` and `C ≥ 1` with
`‖T ^ n P‖ ≤ C ρ ^ n` and `‖S ^ n‖ ≤ C R⁻¹ ^ n` for all `n`, where `P = rieszProj T r` and
`S = rieszOuterInv T r` (the inverse of `T` on the range of `1 - P`). -/
theorem exists_rates (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ ρ R C : ℝ, 0 < ρ ∧ ρ < r ∧ r < R ∧ 1 ≤ C ∧
      (∀ n : ℕ, ‖T ^ n * rieszProj T r‖ ≤ C * ρ ^ n) ∧
      (∀ n : ℕ, ‖rieszOuterInv T r ^ n‖ ≤ C * R⁻¹ ^ n) := by
  obtain ⟨ρ, C₁, hρ, hρr, hC₁, h₁⟩ := exists_norm_pow_mul_rieszProj_le hr hT
  obtain ⟨R, C₂, hR, hC₂, h₂⟩ := exists_norm_rieszOuterInv_pow_le hr hT
  have hR0 : 0 < R := hr.trans hR
  refine ⟨ρ, R, max C₁ C₂, hρ, hρr, hR, hC₂.trans (le_max_right _ _), fun n => ?_, fun n => ?_⟩
  · exact (h₁ n).trans (by gcongr; exact le_max_left _ _)
  · exact (h₂ n).trans (by gcongr; exact le_max_right _ _)

end Rates

end UnforcedLeray.Infra.RieszProjection
