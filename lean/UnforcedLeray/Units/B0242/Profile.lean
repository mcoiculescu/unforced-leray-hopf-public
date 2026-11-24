import Mathlib

/-!
# B0242, part 1: the one-variable weight profile and Green's identity

Blueprint unit **B0242** (`unlabeled:4173`), `paper/main.tex` lines 4171–4184.

Along every coordinate line of the centered cell the weight `(1+q²+η²)^m` is the profile
`x ↦ (a + x²)^m` with `a = 1 + η²` (a `q`-line) or `a = 1 + q²` (an `η`-line). This file
records the profile, its first two classical derivatives, the bounds
`|P'| ≤ 2m P`, `0 ≤ P'' ≤ (4m² − 2m) P` (for `m ≥ 1`, `a ≥ 1`), and the one-dimensional
Green identities used for the seam inequality: on a bounded interval, and on the whole line
with integrable boundary flux.

All powers are real powers of the strictly positive base `a + x²`, so no junk values of
`rpow` occur.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace UnforcedLeray.B0242

/-- The one-variable profile `x ↦ (a + x²)^m` of the weight along a coordinate line. -/
def profile (m a x : ℝ) : ℝ := (a + x ^ 2) ^ m

/-- Its classical first derivative `2 m x (a + x²)^{m-1}`. -/
def profileD (m a x : ℝ) : ℝ := 2 * m * x * (a + x ^ 2) ^ (m - 1)

/-- Its classical second derivative
`2 m (a + x²)^{m-1} + 4 m (m-1) x² (a + x²)^{m-2}`. -/
def profileDD (m a x : ℝ) : ℝ :=
  2 * m * (a + x ^ 2) ^ (m - 1) + 4 * m * (m - 1) * x ^ 2 * (a + x ^ 2) ^ (m - 2)

theorem base_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < a + x ^ 2 := by positivity

theorem hasDerivAt_base (a x : ℝ) : HasDerivAt (fun y : ℝ => a + y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_pow 2 x).const_add a

theorem hasDerivAt_profile (m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (profile m a) (profileD m a x) x := by
  have := (hasDerivAt_base a x).rpow_const (p := m) (Or.inl (base_pos ha x).ne')
  convert this using 1 <;> first | rfl | (simp only [profileD]; ring)

theorem hasDerivAt_profileD (m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (profileD m a) (profileDD m a x) x := by
  have h2 := (hasDerivAt_base a x).rpow_const (p := m - 1) (Or.inl (base_pos ha x).ne')
  have h3 : HasDerivAt (fun y : ℝ => 2 * m * y) (2 * m) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * m)
  have := h3.mul h2
  convert this using 1 <;> first | rfl |
    (simp only [profileDD]; rw [show m - 1 - 1 = m - 2 by ring]; ring)

theorem continuous_profile (m : ℝ) {a : ℝ} (ha : 0 < a) : Continuous (profile m a) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_profile m ha x).continuousAt

theorem continuous_profileD (m : ℝ) {a : ℝ} (ha : 0 < a) : Continuous (profileD m a) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_profileD m ha x).continuousAt

/-- Joint continuity of the second derivative in the base and the variable. -/
theorem continuous_profileDD_comp {X : Type*} [TopologicalSpace X] (m : ℝ) {A x : X → ℝ}
    (hA : Continuous A) (hx : Continuous x) (hA0 : ∀ t, 0 < A t) :
    Continuous fun t => profileDD m (A t) (x t) := by
  have hb : Continuous fun t => A t + x t ^ 2 := hA.add (hx.pow 2)
  have hb0 : ∀ t, A t + x t ^ 2 ≠ 0 := fun t => (base_pos (hA0 t) (x t)).ne'
  have h1 := hb.rpow_const (p := m - 1) fun t => Or.inl (hb0 t)
  have h2 := hb.rpow_const (p := m - 2) fun t => Or.inl (hb0 t)
  simp only [profileDD]
  exact (continuous_const.mul h1).add ((continuous_const.mul (hx.pow 2)).mul h2)

theorem continuous_profileD_comp {X : Type*} [TopologicalSpace X] (m : ℝ) {A x : X → ℝ}
    (hA : Continuous A) (hx : Continuous x) (hA0 : ∀ t, 0 < A t) :
    Continuous fun t => profileD m (A t) (x t) := by
  have hb : Continuous fun t => A t + x t ^ 2 := hA.add (hx.pow 2)
  have h1 := hb.rpow_const (p := m - 1) fun t => Or.inl (base_pos (hA0 t) (x t)).ne'
  simp only [profileD]
  exact (continuous_const.mul hx).mul h1

theorem continuous_profileDD (m : ℝ) {a : ℝ} (ha : 0 < a) : Continuous (profileDD m a) :=
  continuous_profileDD_comp m continuous_const continuous_id fun _ => ha

theorem profile_pos (m : ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < profile m a x :=
  Real.rpow_pos_of_pos (base_pos ha x) m

theorem profile_neg (m a x : ℝ) : profile m a (-x) = profile m a x := by
  simp [profile]

theorem profileD_neg (m a x : ℝ) : profileD m a (-x) = -profileD m a x := by
  simp only [profileD, neg_sq]
  ring

theorem profileD_nonneg {m a x : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ profileD m a x := by
  have := Real.rpow_pos_of_pos (base_pos ha x) (m - 1)
  simp only [profileD]
  positivity

theorem base_mul_rpow_sub_one {s : ℝ} (hs : 0 < s) (p : ℝ) : s * s ^ (p - 1) = s ^ p := by
  rw [Real.rpow_sub_one hs.ne']
  field_simp

/-- `|P'(x)| ≤ 2 m P(x)` when `m ≥ 0` and `a ≥ 1`. -/
theorem abs_profileD_le {m a : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (x : ℝ) :
    |profileD m a x| ≤ 2 * m * profile m a x := by
  have hs : 0 < a + x ^ 2 := base_pos (by linarith) x
  have hP : 0 < (a + x ^ 2) ^ (m - 1) := Real.rpow_pos_of_pos hs _
  have hx : |x| ≤ a + x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  calc |profileD m a x| = 2 * m * (|x| * (a + x ^ 2) ^ (m - 1)) := by
        simp only [profileD, abs_mul, abs_two, abs_of_nonneg hm, abs_of_nonneg hP.le]
        ring
    _ ≤ 2 * m * ((a + x ^ 2) * (a + x ^ 2) ^ (m - 1)) := by gcongr
    _ = 2 * m * profile m a x := by rw [base_mul_rpow_sub_one hs, profile]

theorem profileDD_nonneg {m a : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (x : ℝ) :
    0 ≤ profileDD m a x := by
  have hs : 0 < a + x ^ 2 := base_pos ha x
  have h1 := Real.rpow_pos_of_pos hs (m - 1)
  have h2 := Real.rpow_pos_of_pos hs (m - 2)
  have hm1 : 0 ≤ m - 1 := by linarith
  simp only [profileDD]
  have : 0 ≤ 4 * m * (m - 1) * x ^ 2 * (a + x ^ 2) ^ (m - 2) := by positivity
  have : 0 ≤ 2 * m * (a + x ^ 2) ^ (m - 1) := by positivity
  linarith

/-- `P''(x) ≤ (4m² − 2m) P(x)` when `m ≥ 1` and `a ≥ 1`; the constant does not depend on `a`. -/
theorem profileDD_le {m a : ℝ} (hm : 1 ≤ m) (ha : 1 ≤ a) (x : ℝ) :
    profileDD m a x ≤ (4 * m ^ 2 - 2 * m) * profile m a x := by
  have hs : 0 < a + x ^ 2 := base_pos (by linarith) x
  have hs1 : 1 ≤ a + x ^ 2 := by nlinarith [sq_nonneg x]
  set s := a + x ^ 2 with hs_def
  have P2 := Real.rpow_pos_of_pos hs (m - 2)
  have P1 := Real.rpow_pos_of_pos hs (m - 1)
  have e1 : s * s ^ (m - 2) = s ^ (m - 1) := by
    rw [show m - 2 = (m - 1) - 1 by ring, base_mul_rpow_sub_one hs]
  have e0 : s * s ^ (m - 1) = s ^ m := base_mul_rpow_sub_one hs m
  have hx2 : x ^ 2 ≤ s := by rw [hs_def]; linarith
  have hm1 : 0 ≤ m * (m - 1) := by nlinarith
  have step1 : x ^ 2 * s ^ (m - 2) ≤ s ^ (m - 1) := by
    rw [← e1]; exact mul_le_mul_of_nonneg_right hx2 P2.le
  have step2 : s ^ (m - 1) ≤ s ^ m := by
    rw [← e0]; nlinarith
  have hC : 0 ≤ 4 * m ^ 2 - 2 * m := by nlinarith
  simp only [profileDD, profile]
  rw [← hs_def]
  have := mul_le_mul_of_nonneg_left step1 (by positivity : 0 ≤ 4 * (m * (m - 1)))
  have h3 : (4 * m ^ 2 - 2 * m) * s ^ (m - 1) ≤ (4 * m ^ 2 - 2 * m) * s ^ m :=
    mul_le_mul_of_nonneg_left step2 hC
  nlinarith

theorem abs_profileDD_le {m a : ℝ} (hm : 1 ≤ m) (ha : 1 ≤ a) (x : ℝ) :
    |profileDD m a x| ≤ (4 * m ^ 2 - 2 * m) * profile m a x := by
  rw [abs_of_nonneg (profileDD_nonneg hm (by linarith) x)]
  exact profileDD_le hm ha x

/-! ### Green identities in one variable -/

/-- Green's identity on a bounded interval:
`∫_a^b (f g'' − f'' g) = [f g' − f' g]_a^b`. -/
theorem integral_green_interval {f f' f'' g g' g'' : ℝ → ℝ} (a b : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hf'' : Continuous f'') (hg'' : Continuous g'') :
    ∫ x in a..b, (f x * g'' x - f'' x * g x) =
      (f b * g' b - f' b * g b) - (f a * g' a - f' a * g a) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  refine integral_eq_sub_of_hasDerivAt (f := fun x => f x * g' x - f' x * g x)
    (fun x _ => ?_) (((hfc.mul hg'').sub (hf''.mul hgc)).intervalIntegrable _ _)
  have := ((hf x).mul (hg' x)).sub ((hf' x).mul (hg x))
  convert this using 1 <;> first | rfl | ring

/-- Green's identity on the whole line, when the flux and the integrand are integrable. -/
theorem integral_green_line {f f' f'' g g' g'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (h1 : Integrable fun x => f x * g' x - f' x * g x)
    (h2 : Integrable fun x => f x * g'' x - f'' x * g x) :
    ∫ x, (f x * g'' x - f'' x * g x) = 0 := by
  refine integral_eq_zero_of_hasDerivAt_of_integrable
    (f := fun x => f x * g' x - f' x * g x) (fun x => ?_) h2 h1
  have := ((hf x).mul (hg' x)).sub ((hf' x).mul (hg x))
  convert this using 1 <;> first | rfl | ring

/-- **The seam on one line.** On the centered interval `[-h, h]`, for a test function `g`
whose value and derivative agree at the two ends (periodicity) and with `g(h) ≥ 0`,
`∫ P g'' ≤ ∫ P'' g`. The defect is the seam term `−2 P'(h) g(h) ≤ 0`: the derivative of the
periodically continued profile jumps by `−2P'(h)` at the seam. -/
theorem seam_interval {m a h : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hh : 0 ≤ h)
    {g g' g'' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x) (hg'' : Continuous g'')
    (hper0 : g (-h) = g h) (hper1 : g' (-h) = g' h) (hpos : 0 ≤ g h) :
    ∫ x in (-h)..h, profile m a x * g'' x ≤ ∫ x in (-h)..h, profileDD m a x * g x := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hG := integral_green_interval (-h) h (hasDerivAt_profile m ha) (hasDerivAt_profileD m ha)
    hg hg' (continuous_profileDD m ha) hg''
  have hsub : ∫ x in (-h)..h, (profile m a x * g'' x - profileDD m a x * g x) =
      (∫ x in (-h)..h, profile m a x * g'' x) - ∫ x in (-h)..h, profileDD m a x * g x :=
    intervalIntegral.integral_sub (((continuous_profile m ha).mul hg'').intervalIntegrable _ _)
      (((continuous_profileDD m ha).mul hgc).intervalIntegrable _ _)
  rw [hsub] at hG
  rw [profile_neg, profileD_neg, hper0, hper1] at hG
  have hD := profileD_nonneg hm ha hh
  have : 0 ≤ profileD m a h * g h := mul_nonneg hD hpos
  linarith

end UnforcedLeray.B0242
