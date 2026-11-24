import UnforcedLeray.Lib.Kernels.CylinderBS
import Mathlib.NumberTheory.ZetaValues

/-!
# Image expansion of the cylinder kernel (helper for `PartIII-a:T21/c5/3/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2876-2881:
`K_d(x-y) - K_∞(x-y) = d⁻² B₁(x-y) + O(d⁻⁴|x-y|³)` for `|x-y| ≤ d/2`.

Verbatim copy (namespace `UnforcedLeray.Short.IIIa.EulerSubCore.KerExp`) of the first part of
`Lib/Kernels/CylinderBSExpansion.lean`, which does not compile as it stands (it lacks the import
`Mathlib.NumberTheory.ZetaValues` of `hasSum_zeta_two`, `hasSum_zeta_four`).
-/
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.IIIa.EulerSubCore.KerExp

open UnforcedLeray.Kernels

/-! ### Sums over ℕ+ -/

theorem hasSum_pnat_of_hasSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M] {f : ℕ → M}
    {a : M} (h : HasSum f a) (h0 : f 0 = 0) : HasSum (fun n : ℕ+ => f n) a := by
  refine (PNat.coe_injective.hasSum_iff (fun x hx => ?_)).mpr h
  have hx0 : x = 0 := by
    by_contra hne
    exact hx ⟨⟨x, Nat.pos_of_ne_zero hne⟩, rfl⟩
  rw [hx0, h0]

theorem hasSum_pnat_inv_sq : HasSum (fun n : ℕ+ => 1 / ((n : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_pnat_of_hasSum (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hasSum_zeta_two (by simp)

theorem hasSum_pnat_inv_four : HasSum (fun n : ℕ+ => 1 / ((n : ℕ) : ℝ) ^ 4) (Real.pi ^ 4 / 90) :=
  hasSum_pnat_of_hasSum (f := fun n : ℕ => 1 / (n : ℝ) ^ 4) hasSum_zeta_four (by simp)

theorem hasSum_pnat_inv_sq_complex :
    HasSum (fun n : ℕ+ => 1 / ((n : ℕ) : ℂ) ^ 2) ((Real.pi : ℂ) ^ 2 / 6) := by
  have h := Complex.hasSum_ofReal.mpr hasSum_pnat_inv_sq
  push_cast at h
  exact h

/-! ### One pair of images -/

section Pair

variable {z : ℂ} {a : ℝ}

theorem pair_norm_sq_le (hza : 2 * ‖z‖ ≤ a) : ‖z‖ ^ 2 ≤ a ^ 2 / 4 := by
  have h := pow_le_pow_left₀ (norm_nonneg z) (show ‖z‖ ≤ a / 2 by linarith) 2
  calc ‖z‖ ^ 2 ≤ (a / 2) ^ 2 := h
    _ = a ^ 2 / 4 := by ring

theorem pair_norm_ge (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    3 / 4 * a ^ 2 ≤ ‖z ^ 2 - (a : ℂ) ^ 2‖ := by
  have h1 : ‖((a : ℂ) ^ 2)‖ - ‖z ^ 2‖ ≤ ‖(a : ℂ) ^ 2 - z ^ 2‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg ha.le] at h1
  have hz2 := pair_norm_sq_le hza
  linarith

theorem pair_sq_ne (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) : z ^ 2 - (a : ℂ) ^ 2 ≠ 0 := by
  intro h
  have := pair_norm_ge ha hza
  rw [h, norm_zero] at this
  have : 0 < 3 / 4 * a ^ 2 := by positivity
  linarith

theorem pair_sub_ne (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) : z - a ≠ 0 := by
  intro h
  apply pair_sq_ne ha hza
  rw [show z ^ 2 - (a : ℂ) ^ 2 = (z - a) * (z + a) by ring, h, zero_mul]

theorem pair_add_ne (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) : z + a ≠ 0 := by
  intro h
  apply pair_sq_ne ha hza
  rw [show z ^ 2 - (a : ℂ) ^ 2 = (z - a) * (z + a) by ring, h, mul_zero]

theorem pair_inv_identity (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    1 / (z - a) + 1 / (z + a) + 2 * z / (a : ℂ) ^ 2 =
      2 * z ^ 3 / ((a : ℂ) ^ 2 * (z ^ 2 - (a : ℂ) ^ 2)) := by
  have h1 := pair_sub_ne ha hza
  have h2 := pair_add_ne ha hza
  have h3 := pair_sq_ne ha hza
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  ring

theorem norm_pair_inv_le (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    ‖1 / (z - a) + 1 / (z + a) + 2 * z / (a : ℂ) ^ 2‖ ≤ 8 / 3 * ‖z‖ ^ 3 / a ^ 4 := by
  rw [pair_inv_identity ha hza, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg ha.le, Complex.norm_ofNat]
  have hD := pair_norm_ge ha hza
  have hD0 : 0 < ‖z ^ 2 - (a : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hD
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 2 * ‖z‖ ^ 3 * a ^ 4 = 8 / 3 * (‖z‖ ^ 3 * a ^ 2) * (3 / 4 * a ^ 2) := by ring
    _ ≤ 8 / 3 * (‖z‖ ^ 3 * a ^ 2) * ‖z ^ 2 - (a : ℂ) ^ 2‖ := by gcongr
    _ = 8 / 3 * ‖z‖ ^ 3 * (a ^ 2 * ‖z ^ 2 - (a : ℂ) ^ 2‖) := by ring

theorem pair_inv_sq_identity (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    (z - a)⁻¹ ^ 2 + (z + a)⁻¹ ^ 2 - 2 / (a : ℂ) ^ 2 =
      (6 * z ^ 2 * (a : ℂ) ^ 2 - 2 * z ^ 4) / ((a : ℂ) ^ 2 * (z ^ 2 - (a : ℂ) ^ 2) ^ 2) := by
  have h1 := pair_sub_ne ha hza
  have h2 := pair_add_ne ha hza
  have h3 := pair_sq_ne ha hza
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  ring

theorem norm_pair_inv_sq_le (ha : 0 < a) (hza : 2 * ‖z‖ ≤ a) :
    ‖(z - a)⁻¹ ^ 2 + (z + a)⁻¹ ^ 2 - 2 / (a : ℂ) ^ 2‖ ≤ 104 / 9 * ‖z‖ ^ 2 / a ^ 4 := by
  rw [pair_inv_sq_identity ha hza, norm_div]
  have hD := pair_norm_ge ha hza
  have hD0 : 0 < ‖z ^ 2 - (a : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hD
  have hnum : ‖6 * z ^ 2 * (a : ℂ) ^ 2 - 2 * z ^ 4‖ ≤ 13 / 2 * ‖z‖ ^ 2 * a ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg ha.le, Complex.norm_ofNat, Complex.norm_ofNat]
    have hz2 := pair_norm_sq_le hza
    calc 6 * ‖z‖ ^ 2 * a ^ 2 + 2 * ‖z‖ ^ 4 = 6 * ‖z‖ ^ 2 * a ^ 2 + 2 * ‖z‖ ^ 2 * ‖z‖ ^ 2 := by
          ring
      _ ≤ 6 * ‖z‖ ^ 2 * a ^ 2 + 2 * ‖z‖ ^ 2 * (a ^ 2 / 4) := by gcongr
      _ = 13 / 2 * ‖z‖ ^ 2 * a ^ 2 := by ring
  have hden : ‖(a : ℂ) ^ 2 * (z ^ 2 - (a : ℂ) ^ 2) ^ 2‖ = a ^ 2 * ‖z ^ 2 - (a : ℂ) ^ 2‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [hden]
  have hden_ge : a ^ 2 * (9 / 16 * a ^ 4) ≤ a ^ 2 * ‖z ^ 2 - (a : ℂ) ^ 2‖ ^ 2 := by
    have : 9 / 16 * a ^ 4 ≤ ‖z ^ 2 - (a : ℂ) ^ 2‖ ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hD 2
      calc 9 / 16 * a ^ 4 = (3 / 4 * a ^ 2) ^ 2 := by ring
        _ ≤ _ := h
    exact mul_le_mul_of_nonneg_left this (sq_nonneg a)
  calc ‖6 * z ^ 2 * (a : ℂ) ^ 2 - 2 * z ^ 4‖ / (a ^ 2 * ‖z ^ 2 - (a : ℂ) ^ 2‖ ^ 2)
      ≤ 13 / 2 * ‖z‖ ^ 2 * a ^ 2 / (a ^ 2 * (9 / 16 * a ^ 4)) := by
        apply div_le_div₀ (by positivity) hnum (by positivity) hden_ge
    _ = 104 / 9 * ‖z‖ ^ 2 / a ^ 4 := by field_simp; ring

end Pair

/-! ### Summation over the images -/

theorem image_le {c : ℝ} (hc : 0 < c) {z : ℂ} (hzc : ‖z‖ ≤ c / 2) (n : ℕ+) :
    0 < ((n : ℕ) : ℝ) * c ∧ 2 * ‖z‖ ≤ ((n : ℕ) : ℝ) * c := by
  have hn : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  refine ⟨by positivity, ?_⟩
  have h1 : c ≤ ((n : ℕ) : ℝ) * c := le_mul_of_one_le_left hc.le hn
  have h2 := norm_nonneg z
  linarith

theorem div_cast_mem_integerComplement {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0)
    (hzc : ‖z‖ ≤ c / 2) : z / c ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hzm : z = (m : ℂ) * c := by rw [hm]; field_simp
  rcases eq_or_ne m 0 with h0 | h0
  · apply hz; rw [hzm, h0]; simp
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs h0
      exact_mod_cast this
    have hn : ‖z‖ = |(m : ℝ)| * c := by
      rw [hzm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
      simp
    rw [hn] at hzc
    have : c ≤ |(m : ℝ)| * c := le_mul_of_one_le_left hc.le h1
    linarith

/-- The constant of `cylinderBS_image_expansion`. -/
def imageConst : ℝ := (2 * Real.pi)⁻¹ * (8 / 3) * (Real.pi ^ 4 / 90)

/-- The image expansion with explicit constant, for any c > 0. -/
theorem cylinderBS_image_expansion' {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0)
    (hzc : ‖z‖ ≤ c / 2) :
    ‖cylinderBS c z - (2 * Real.pi * Complex.I * z)⁻¹ +
        (2 * Real.pi * Complex.I)⁻¹ * (Real.pi ^ 2 / 3) * z / c ^ 2‖ ≤
      imageConst * ‖z‖ ^ 3 / c ^ 4 := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set u : ℕ+ → ℂ := fun n => 1 / (z - ((n : ℕ) : ℂ) * c) + 1 / (z + ((n : ℕ) : ℂ) * c) +
    2 * z / (((n : ℕ) : ℂ) * c) ^ 2 with hu
  set v : ℕ+ → ℂ := fun n => 2 * z / (((n : ℕ) : ℂ) * c) ^ 2 with hv
  have hubound : ∀ n : ℕ+, ‖u n‖ ≤ 8 / 3 * ‖z‖ ^ 3 / c ^ 4 * (1 / ((n : ℕ) : ℝ) ^ 4) := by
    intro n
    obtain ⟨ha, hza⟩ := image_le hc hzc n
    have h := norm_pair_inv_le ha hza
    push_cast at h
    rw [hu]
    refine h.trans (le_of_eq ?_)
    have : ((n : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hg : HasSum (fun n : ℕ+ => 8 / 3 * ‖z‖ ^ 3 / c ^ 4 * (1 / ((n : ℕ) : ℝ) ^ 4))
      (8 / 3 * ‖z‖ ^ 3 / c ^ 4 * (Real.pi ^ 4 / 90)) := hasSum_pnat_inv_four.mul_left _
  have hu_sum : Summable u := Summable.of_norm_bounded hg.summable hubound
  have hv_sum : HasSum v ((Real.pi : ℂ) ^ 2 / 3 * z / c ^ 2) := by
    have h := hasSum_pnat_inv_sq_complex.mul_left (2 * z / (c : ℂ) ^ 2)
    have hfun : v = fun n : ℕ+ => 2 * z / (c : ℂ) ^ 2 * (1 / ((n : ℕ) : ℂ) ^ 2) := by
      rw [hv]
      funext n
      have : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
      field_simp
    have hval : (Real.pi : ℂ) ^ 2 / 3 * z / c ^ 2 = 2 * z / (c : ℂ) ^ 2 * ((Real.pi : ℂ) ^ 2 / 6) := by
      field_simp
      ring
    rw [hfun, hval]
    exact h
  have hsplit : ∑' n : ℕ+, (1 / (z - ((n : ℕ) : ℂ) * c) + 1 / (z + ((n : ℕ) : ℂ) * c)) =
      ∑' n, u n - (Real.pi : ℂ) ^ 2 / 3 * z / c ^ 2 := by
    rw [← hv_sum.tsum_eq, ← hu_sum.tsum_sub hv_sum.summable]
    congr 1
    funext n
    rw [hu, hv]
    ring
  rw [cylinderBS_eq_paired hc (div_cast_mem_integerComplement hc hz hzc)]
  have hsplit' : ∑' n : ℕ+, (1 / (z - (n : ℂ) * c) + 1 / (z + (n : ℂ) * c)) =
      ∑' n, u n - (Real.pi : ℂ) ^ 2 / 3 * z / c ^ 2 := by
    rw [← hsplit]
  rw [hsplit']
  have hexpr : (2 * Real.pi * Complex.I)⁻¹ * (1 / z + (∑' n, u n - (Real.pi : ℂ) ^ 2 / 3 * z / c ^ 2)) -
      (2 * Real.pi * Complex.I * z)⁻¹ +
        (2 * Real.pi * Complex.I)⁻¹ * (Real.pi ^ 2 / 3) * z / c ^ 2 =
      (2 * Real.pi * Complex.I)⁻¹ * ∑' n, u n := by
    rw [mul_inv]
    ring
  rw [hexpr, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  have ht := tsum_of_norm_bounded hg hubound
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
  calc (2 * Real.pi)⁻¹ * ‖∑' n, u n‖ ≤ (2 * Real.pi)⁻¹ * (8 / 3 * ‖z‖ ^ 3 / c ^ 4 *
        (Real.pi ^ 4 / 90)) := by gcongr
    _ = imageConst * ‖z‖ ^ 3 / c ^ 4 := by unfold imageConst; ring

/-- INF22 K8 `cylinderBS_image_expansion` (B0334, B0247): for c ≥ 1, z ≠ 0, ‖z‖ ≤ c/2,
‖K_c(z) − (2πiz)^{-1} + (2πi)^{-1}(π²/3) z/c²‖ ≤ C ‖z‖³/c⁴. -/
theorem cylinderBS_image_expansion : ∃ C, ∀ c : ℝ, 1 ≤ c → ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ c / 2 →
    ‖cylinderBS c z - (2 * Real.pi * Complex.I * z)⁻¹ +
        (2 * Real.pi * Complex.I)⁻¹ * (Real.pi ^ 2 / 3) * z / c ^ 2‖ ≤ C * ‖z‖ ^ 3 / c ^ 4 :=
  ⟨imageConst, fun _ hc _ hz hzc => cylinderBS_image_expansion' (by linarith) hz hzc⟩


end UnforcedLeray.Short.IIIa.EulerSubCore.KerExp
