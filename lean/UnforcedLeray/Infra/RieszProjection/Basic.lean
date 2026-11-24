import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Riesz projections, I: contour integrals of the resolvent on a circle

Let `X` be a complex Banach space, `T : X →L[ℂ] X`, and `r > 0` with the circle `|z| = r` in the
resolvent set of `T`. This file sets up the contour operators
`contourOp T r f = (2πi)⁻¹ ∮_{|z|=r} f(z) (z - T)⁻¹ dz` (Mathlib's `resolvent`, i.e.
`resolvent T z = Ring.inverse (algebraMap ℂ _ z - T)`), the Riesz projection
`rieszProj T r = (2πi)⁻¹ ∮_{|z|=r} (z - T)⁻¹ dz` and the outer inverse
`rieszOuterInv T r = -(2πi)⁻¹ ∮_{|z|=r} z⁻¹ (z - T)⁻¹ dz`, and proves the elementary facts:

* `commute_contourOp`: an operator commuting with `T` commutes with every contour operator;
* `mul_contourOp`: `T ∘ contourOp T r f = contourOp T r (z f) - ((2πi)⁻¹∮ f) • 1`;
* `pow_mul_rieszProj`: `T ^ n * P = (2πi)⁻¹ ∮ z ^ n (z - T)⁻¹ dz`;
* `contourOp_eq_of_annulus`: the contour operator does not change when the circle moves through
  an annulus free of spectrum, for `f` holomorphic on the annulus (Cauchy's theorem);
* `exists_annulus_subset_resolventSet`: a circle in the resolvent set has a closed annulus
  `r - δ ≤ |z| ≤ r + δ` (`0 < δ < r`) around it in the resolvent set (the spectrum is compact).

This is the localization of `paper/main.tex`, lines 359-368 (the Riesz integral `P_-` on the
circle `|ξ| = e^{βT}` and its complement `P_+ = I - P_-`).

`circleIntegral_mul_left`, `mul_resolvent_eq` and `pow_mul_rieszProj` are adapted from
`NonUniqueEuler/P/Infra/Dunford/Integral.lean` (`circleIntegral_mul_left`, `smul_resolvent_eq`,
`circleIntegral_pow_smul_resolvent`), with the hypothesis "spectrum inside the circle" replaced by
"circle in the resolvent set".
-/

set_option autoImplicit false

noncomputable section

open Metric Complex
open scoped Real

namespace UnforcedLeray.Infra.RieszProjection

section CircleIntegralAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- A continuous linear map commutes with a circle integral. -/
theorem circleIntegral_comp_comm [CompleteSpace E] [CompleteSpace F] (L : E →L[ℂ] F)
    {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), L (f z)) = L (∮ z in C(c, R), f z) := by
  simp only [circleIntegral]
  rw [← L.intervalIntegral_comp_comm hf.out]
  simp only [map_smul]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A constant factor on the left can be pulled out of a circle integral in a Banach algebra. -/
theorem circleIntegral_mul_left (B : A) {f : ℂ → A} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), B * f z) = B * ∮ z in C(c, R), f z :=
  circleIntegral_comp_comm (ContinuousLinearMap.mul ℂ A B) hf

/-- A constant factor on the right can be pulled out of a circle integral in a Banach algebra. -/
theorem circleIntegral_mul_right (B : A) {f : ℂ → A} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z * B) = (∮ z in C(c, R), f z) * B :=
  circleIntegral_comp_comm ((ContinuousLinearMap.mul ℂ A).flip B) hf

/-- `∮_{|z|=r} z ^ n dz = 0` for `n : ℕ`. -/
theorem circleIntegral_pow_eq_zero (n : ℕ) (r : ℝ) : (∮ z in C(0, r), z ^ n) = 0 := by
  have h := circleIntegral.integral_sub_zpow_of_ne (n := (n : ℤ)) (by omega) 0 0 r
  simpa only [sub_zero, zpow_natCast] using h

/-- `∮_{|z|=r} z⁻¹ ^ (m + 2) dz = 0`. -/
theorem circleIntegral_inv_pow_eq_zero (m : ℕ) (r : ℝ) :
    (∮ z in C(0, r), z⁻¹ ^ (m + 2)) = 0 := by
  have h := circleIntegral.integral_sub_zpow_of_ne (n := -((m + 2 : ℕ) : ℤ)) (by omega) 0 0 r
  simpa only [sub_zero, zpow_neg, zpow_natCast, inv_pow] using h

/-- `∮_{|z|=r} z⁻¹ dz = 2πi` for `r > 0`. -/
theorem circleIntegral_inv_eq {r : ℝ} (hr : 0 < r) : (∮ z in C(0, r), z⁻¹) = 2 * π * I := by
  have h := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := r)
    (mem_ball_self hr)
  simpa only [sub_zero] using h

end CircleIntegralAux

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Definitions -/

/-- The contour operator `(2πi)⁻¹ ∮_{|z|=r} f(z) (z - T)⁻¹ dz` (positively oriented circle). -/
def contourOp (T : X →L[ℂ] X) (r : ℝ) (f : ℂ → ℂ) : X →L[ℂ] X :=
  (2 * π * I)⁻¹ • ∮ z in C(0, r), f z • resolvent T z

/-- The **Riesz projection** `P = (2πi)⁻¹ ∮_{|z|=r} (z - T)⁻¹ dz` of `T` for the circle `|z| = r`
(positively oriented). When the circle lies in the resolvent set, `P` is the spectral projection
onto the part of the spectrum inside the circle (`P_-` of `paper/main.tex`, line 359). -/
def rieszProj (T : X →L[ℂ] X) (r : ℝ) : X →L[ℂ] X :=
  (2 * π * I)⁻¹ • ∮ z in C(0, r), resolvent T z

/-- The **outer inverse** `S = -(2πi)⁻¹ ∮_{|z|=r} z⁻¹ (z - T)⁻¹ dz`. When the circle lies in the
resolvent set, `S` vanishes on the range of the Riesz projection and inverts `T` on the range of
`1 - rieszProj T r` (`ℳ_+⁻¹` of `paper/main.tex`, line 366). -/
def rieszOuterInv (T : X →L[ℂ] X) (r : ℝ) : X →L[ℂ] X :=
  -contourOp T r (fun z => z⁻¹)

theorem rieszProj_eq_contourOp (T : X →L[ℂ] X) (r : ℝ) :
    rieszProj T r = contourOp T r (fun _ => 1) := by
  simp only [rieszProj, contourOp, one_smul]

/-! ### The resolvent on the resolvent set -/

section Resolvent

variable [CompleteSpace X]

theorem continuousAt_resolvent {T : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    ContinuousAt (resolvent T) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).continuousAt

theorem differentiableAt_resolvent {T : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    DifferentiableAt ℂ (resolvent T) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt

theorem continuousOn_resolvent {T : X →L[ℂ] X} {s : Set ℂ} (hs : s ⊆ resolventSet ℂ T) :
    ContinuousOn (resolvent T) s :=
  fun _ hz => (continuousAt_resolvent (hs hz)).continuousWithinAt

omit [CompleteSpace X] in
/-- `T (z - T)⁻¹ = z (z - T)⁻¹ - 1` on the resolvent set. -/
theorem mul_resolvent_eq {T : X →L[ℂ] X} {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    T * resolvent T z = z • resolvent T z - 1 := by
  have h : (algebraMap ℂ (X →L[ℂ] X) z - T) * resolvent T z = 1 :=
    Ring.mul_inverse_cancel _ hz
  rw [Algebra.algebraMap_eq_smul_one, sub_mul, smul_mul_assoc, one_mul] at h
  rw [← h]
  abel

omit [CompleteSpace X] in
/-- An operator commuting with `T` commutes with its resolvent. -/
theorem commute_resolvent {T B : X →L[ℂ] X} (hB : Commute B T) {z : ℂ}
    (hz : z ∈ resolventSet ℂ T) : Commute B (resolvent T z) := by
  have h1 : Commute B (algebraMap ℂ (X →L[ℂ] X) z - T) :=
    (Algebra.commute_algebraMap_right z B).sub_right hB
  obtain ⟨u, hu⟩ := (hz : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - T))
  rw [resolvent, ← hu, Ring.inverse_unit]
  rw [← hu] at h1
  exact h1.units_inv_right

omit [CompleteSpace X] in
/-- The first resolvent identity `(z - T)⁻¹ - (w - T)⁻¹ = (w - z) (z - T)⁻¹ (w - T)⁻¹`. -/
theorem resolvent_sub_resolvent_eq {T : X →L[ℂ] X} {z w : ℂ} (hz : z ∈ resolventSet ℂ T)
    (hw : w ∈ resolventSet ℂ T) :
    resolvent T z - resolvent T w = (w - z) • (resolvent T z * resolvent T w) := by
  have h1 : resolvent T z * (algebraMap ℂ (X →L[ℂ] X) z - T) = 1 :=
    Ring.inverse_mul_cancel _ hz
  have h2 : (algebraMap ℂ (X →L[ℂ] X) w - T) * resolvent T w = 1 :=
    Ring.mul_inverse_cancel _ hw
  calc resolvent T z - resolvent T w
      = resolvent T z * ((algebraMap ℂ (X →L[ℂ] X) w - T) * resolvent T w) -
          (resolvent T z * (algebraMap ℂ (X →L[ℂ] X) z - T)) * resolvent T w := by
        rw [h1, h2, mul_one, one_mul]
    _ = resolvent T z * (algebraMap ℂ (X →L[ℂ] X) w - algebraMap ℂ (X →L[ℂ] X) z) *
          resolvent T w := by
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
    _ = (w - z) • (resolvent T z * resolvent T w) := by
        rw [← map_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]

omit [CompleteSpace X] in
/-- The resolvents at two points commute. -/
theorem commute_resolvent_resolvent (T : X →L[ℂ] X) (z w : ℂ) : Commute (resolvent T z) (resolvent T w) := by
  have hT : Commute (algebraMap ℂ (X →L[ℂ] X) z - T) T :=
    (Algebra.commute_algebraMap_left z T).sub_left (Commute.refl T)
  have h : Commute (algebraMap ℂ (X →L[ℂ] X) z - T) (algebraMap ℂ (X →L[ℂ] X) w - T) :=
    (Algebra.commute_algebraMap_right w _).sub_right hT
  exact h.ringInverse_ringInverse

end Resolvent

/-! ### Elementary properties of the contour operators -/

section ContourOp

variable [CompleteSpace X]

theorem circleIntegrable_smul_resolvent {T : X →L[ℂ] X} {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) :
    CircleIntegrable (fun z => f z • resolvent T z) 0 r :=
  (hf.smul (continuousOn_resolvent hT)).circleIntegrable hr

/-- An operator commuting with `T` commutes with every contour operator of `T`. -/
theorem commute_contourOp {T B : X →L[ℂ] X} (hB : Commute B T) {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) : Commute B (contourOp T r f) := by
  have hint := circleIntegrable_smul_resolvent hr hT hf
  have hcongr : Set.EqOn (fun z => B * (f z • resolvent T z))
      (fun z => (f z • resolvent T z) * B) (sphere (0 : ℂ) r) := by
    intro z hz
    simp only [mul_smul_comm, smul_mul_assoc]
    rw [(commute_resolvent hB (hT hz)).eq]
  show B * contourOp T r f = contourOp T r f * B
  rw [contourOp, mul_smul_comm, smul_mul_assoc, ← circleIntegral_mul_left B hint,
    ← circleIntegral_mul_right B hint, circleIntegral.integral_congr hr hcongr]

/-- An operator commuting with `T` commutes with the Riesz projection. -/
theorem commute_rieszProj {T B : X →L[ℂ] X} (hB : Commute B T) {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) : Commute B (rieszProj T r) := by
  rw [rieszProj_eq_contourOp]
  exact commute_contourOp hB hr hT continuousOn_const

/-- `T` commutes with its Riesz projection. -/
theorem commute_self_rieszProj {T : X →L[ℂ] X} {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) : Commute T (rieszProj T r) :=
  commute_rieszProj (Commute.refl T) hr hT

omit [CompleteSpace X] in
/-- An operator commuting with `T` commutes with `resolvent T z = Ring.inverse (z - T)` for every
`z` (off the resolvent set both sides vanish). -/
theorem commute_resolvent_of_commute {T B : X →L[ℂ] X} (hB : Commute B T) (z : ℂ) :
    Commute B (resolvent T z) := by
  by_cases hz : z ∈ resolventSet ℂ T
  · exact commute_resolvent hB hz
  · rw [resolvent, Ring.inverse_non_unit _ hz]
    exact Commute.zero_right B

/-- An operator commuting with `T` commutes with every contour operator of `T`, with no hypothesis
on the circle (a non-integrable integrand has integral `0`). -/
theorem commute_contourOp_of_commute {T B : X →L[ℂ] X} (hB : Commute B T) (r : ℝ)
    (f : ℂ → ℂ) : Commute B (contourOp T r f) := by
  have hpt : ∀ z, B * (f z • resolvent T z) = (f z • resolvent T z) * B := fun z => by
    rw [mul_smul_comm, smul_mul_assoc, (commute_resolvent_of_commute hB z).eq]
  show B * contourOp T r f = contourOp T r f * B
  by_cases hint : CircleIntegrable (fun z => f z • resolvent T z) 0 r
  · rw [contourOp, mul_smul_comm, smul_mul_assoc, ← circleIntegral_mul_left B hint,
      ← circleIntegral_mul_right B hint]
    simp only [hpt]
  · rw [contourOp, circleIntegral.integral_undef hint, smul_zero, mul_zero, zero_mul]

/-- An operator commuting with `T` commutes with every Riesz projection of `T`. -/
theorem commute_rieszProj_of_commute {T B : X →L[ℂ] X} (hB : Commute B T) (r : ℝ) :
    Commute B (rieszProj T r) := by
  rw [rieszProj_eq_contourOp]
  exact commute_contourOp_of_commute hB r _

/-- An operator commuting with `T` commutes with the outer inverse. -/
theorem commute_rieszOuterInv_of_commute {T B : X →L[ℂ] X} (hB : Commute B T) (r : ℝ) :
    Commute B (rieszOuterInv T r) :=
  (commute_contourOp_of_commute hB r _).neg_right

/-- `T ∘ contourOp T r f = contourOp T r (z ↦ z f(z)) - ((2πi)⁻¹ ∮ f) • 1`, from
`T (z - T)⁻¹ = z (z - T)⁻¹ - 1`. -/
theorem mul_contourOp {T : X →L[ℂ] X} {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) :
    T * contourOp T r f =
      contourOp T r (fun z => z * f z) - ((2 * π * I)⁻¹ * ∮ z in C(0, r), f z) • 1 := by
  have hint := circleIntegrable_smul_resolvent hr hT hf
  have hint1 : CircleIntegrable (fun z => (z * f z) • resolvent T z) 0 r :=
    circleIntegrable_smul_resolvent hr hT (continuousOn_id.mul hf)
  have hint2 : CircleIntegrable (fun z => f z • (1 : X →L[ℂ] X)) 0 r :=
    (hf.smul continuousOn_const).circleIntegrable hr
  have hcongr : Set.EqOn (fun z => T * (f z • resolvent T z))
      (fun z => (z * f z) • resolvent T z - f z • (1 : X →L[ℂ] X)) (sphere (0 : ℂ) r) := by
    intro z hz
    simp only
    rw [mul_smul_comm, mul_resolvent_eq (hT hz), smul_sub, smul_smul, mul_comm (f z) z]
  rw [contourOp, mul_smul_comm, ← circleIntegral_mul_left T hint,
    circleIntegral.integral_congr hr hcongr, circleIntegral.integral_sub hint1 hint2,
    circleIntegral.integral_smul_const, contourOp, smul_sub, smul_smul]

/-- **Moments of the Riesz projection**: `T ^ n P = (2πi)⁻¹ ∮_{|z|=r} z ^ n (z - T)⁻¹ dz`. -/
theorem pow_mul_rieszProj {T : X →L[ℂ] X} {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) (n : ℕ) :
    T ^ n * rieszProj T r = contourOp T r (fun z => z ^ n) := by
  induction n with
  | zero => simp only [pow_zero, one_mul, rieszProj_eq_contourOp]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_contourOp hr hT (continuous_pow n).continuousOn,
      circleIntegral_pow_eq_zero, mul_zero, zero_smul, sub_zero]
    congr 1
    funext z
    rw [pow_succ']

/-- The same formula written with the explicit integral. -/
theorem pow_mul_rieszProj_eq_integral {T : X →L[ℂ] X} {r : ℝ} (hr : 0 ≤ r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) (n : ℕ) :
    T ^ n * rieszProj T r = (2 * π * I)⁻¹ • ∮ z in C(0, r), z ^ n • resolvent T z :=
  pow_mul_rieszProj hr hT n

/-- **Independence of the radius**: if the closed annulus `r₁ ≤ |z| ≤ r₂` lies in the resolvent
set and `f` is holomorphic on it, the contour operators on the two boundary circles agree. -/
theorem contourOp_eq_of_annulus {T : X →L[ℂ] X} {f : ℂ → ℂ} {r₁ r₂ : ℝ} (h0 : 0 < r₁)
    (hle : r₁ ≤ r₂) (hT : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z ∈ resolventSet ℂ T)
    (hf : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → DifferentiableAt ℂ f z) :
    contourOp T r₁ f = contourOp T r₂ f := by
  unfold contourOp
  congr 1
  symm
  refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable h0 hle
    Set.countable_empty ?_ ?_
  · intro z hz
    have h1 : ‖z‖ ≤ r₂ := mem_closedBall_zero_iff.1 hz.1
    have h2 : r₁ ≤ ‖z‖ := not_lt.1 (fun h => hz.2 (mem_ball_zero_iff.2 h))
    exact ((hf z h2 h1).continuousAt.smul
      (continuousAt_resolvent (hT z h2 h1))).continuousWithinAt
  · intro z hz
    have h1 : ‖z‖ ≤ r₂ := (mem_ball_zero_iff.1 hz.1.1).le
    have h2 : r₁ ≤ ‖z‖ := (not_le.1 (fun h => hz.1.2 (mem_closedBall_zero_iff.2 h))).le
    exact (hf z h2 h1).smul (differentiableAt_resolvent (hT z h2 h1))

/-- A circle in the resolvent set has a closed annulus around it in the resolvent set. -/
theorem exists_annulus_subset_resolventSet (T : X →L[ℂ] X) {r : ℝ} (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧
      ∀ z : ℂ, r - δ ≤ ‖z‖ → ‖z‖ ≤ r + δ → z ∈ resolventSet ℂ T := by
  have hK : IsClosed ((fun z : ℂ => ‖z‖) '' spectrum ℂ T) :=
    ((spectrum.isCompact T).image continuous_norm).isClosed
  have hr' : r ∉ (fun z : ℂ => ‖z‖) '' spectrum ℂ T := by
    rintro ⟨z, hz, hzr⟩
    exact hz (hT (mem_sphere_zero_iff_norm.2 hzr))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl r hr'
  refine ⟨min (ε / 2) (r / 2), by positivity, ?_, fun z h1 h2 => ?_⟩
  · have := min_le_right (ε / 2) (r / 2)
    linarith
  · by_contra hz
    have hmin := min_le_left (ε / 2) (r / 2)
    have hmem : ‖z‖ ∈ ball r ε := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hball hmem ⟨z, hz, rfl⟩

end ContourOp

end UnforcedLeray.Infra.RieszProjection
