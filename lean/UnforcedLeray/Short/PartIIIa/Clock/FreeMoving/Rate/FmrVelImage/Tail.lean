import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c2_2_7
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap

/-!
# Part III-a, `PartIII-a:T21/c2/2/7/1` (`FmrVelImage`): helper, width-dependent image tail

Source of record: `the November 2 reference manuscript` line 2955 and lines 291-303.
For the isolated vortex at width `a` (`1 ≤ a ≤ c²`) the image sum on the cell `|x₁| ≤ c/2`
differs from the central term by `(2a+1) e^{-c²/(32a)} Λ`, `Λ` an absolute constant.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

/-- Absolute constant: `Λ = e^{1/32} ∑_m e^{-m²/32}`. -/
def fmrImageLam : ℝ := Real.exp (1 / 32) * ∑' m : ℤ, Real.exp (-((1 / 32) * (m : ℝ) ^ 2))

theorem fmrImageLam_nonneg : 0 ≤ fmrImageLam :=
  mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun _ => (Real.exp_pos _).le))

/-- Pointwise lattice bound uniform in the width. -/
theorem fmrImage_pt {a c x : ℝ} (ha : 1 ≤ a) (hac : a ≤ c ^ 2) (hc : 1 ≤ c)
    (hx : |x| ≤ c / 2) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-((1 / (8 * a)) * (x - n * c) ^ 2)) ≤
      Real.exp (-(c ^ 2 / (32 * a))) * Real.exp (1 / 32) *
        Real.exp (-((1 / 32) * (n : ℝ) ^ 2)) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have ha0 : 0 < a := by linarith
  have hk : |x - ((0 : ℤ) : ℝ) * c| ≤ c / 2 := by simpa using hx
  have hsep := UnforcedLeray.Short.IIb.TrainGap.lattice_sep hc hk n
  simp only [sub_zero] at hsep
  have h0 : 0 ≤ |(n : ℝ)| * c / 2 :=
    div_nonneg (mul_nonneg (abs_nonneg _) hcpos.le) (by norm_num)
  have hsq : (|(n : ℝ)| * c / 2) ^ 2 ≤ |x - n * c| ^ 2 := pow_le_pow_left₀ h0 hsep 2
  rw [sq_abs] at hsq
  have e1 : (|(n : ℝ)| * c / 2) ^ 2 = (n : ℝ) ^ 2 * c ^ 2 / 4 := by
    rw [div_pow, mul_pow, sq_abs]
    ring
  rw [e1] at hsq
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.mpr h1
    rw [Int.cast_abs] at h2
    simpa using h2
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [← sq_abs]
    nlinarith
  set g : ℝ := c ^ 2 / (32 * a) with hg
  have hg1 : 1 / 32 ≤ g := by
    rw [hg, le_div_iff₀ (by linarith)]
    nlinarith
  have hbeta : (1 / (8 * a)) * ((n : ℝ) ^ 2 * c ^ 2 / 4) = (n : ℝ) ^ 2 * g := by
    rw [hg]; field_simp; ring
  have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1 / (8 * a))
  rw [hbeta] at hmul
  have hprod : 0 ≤ ((n : ℝ) ^ 2 - 1) * (g - 1 / 32) :=
    mul_nonneg (by linarith) (by linarith)
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hmul, hprod]

/-- The cell tail of a Gaussian-dominated lattice series, uniform in the width. -/
theorem fmrImage_cell_tail {a c C₀ x : ℝ} (ha : 1 ≤ a) (hac : a ≤ c ^ 2) (hc : 1 ≤ c)
    (hC₀ : 0 ≤ C₀) (hx : |x| ≤ c / 2) {f : ℤ → ℝ}
    (hf : ∀ n : ℤ, |f n| ≤ C₀ * Real.exp (-((1 / (8 * a)) * (x - n * c) ^ 2))) :
    |∑' n, f n - f 0| ≤ C₀ * Real.exp (-(c ^ 2 / (32 * a))) * fmrImageLam := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have ha0 : 0 < a := by linarith
  have hβ : 0 < 1 / (8 * a) := by positivity
  have hsum : Summable f := UnforcedLeray.Short.IIb.TrainGap.summable_of_gauss_bound hβ hc0 hf
  set K : ℝ := C₀ * Real.exp (-(c ^ 2 / (32 * a))) * Real.exp (1 / 32) with hK
  have hH : Summable (fun m : ℤ => K * Real.exp (-((1 / 32) * (m : ℝ) ^ 2))) :=
    (UnforcedLeray.Short.IIb.TrainGap.summable_gauss_int (by norm_num : (0 : ℝ) < 1 / 32)).mul_left K
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC₀ (Real.exp_pos _).le) (Real.exp_pos _).le
  have hH0 : ∀ n : ℤ, 0 ≤ K * Real.exp (-((1 / 32) * (n : ℝ) ^ 2)) :=
    fun n => mul_nonneg hK0 (Real.exp_pos _).le
  have hb : ∀ n : ℤ, n ≠ 0 → |f n| ≤ K * Real.exp (-((1 / 32) * (n : ℝ) ^ 2)) := by
    intro n hn
    calc |f n| ≤ C₀ * Real.exp (-((1 / (8 * a)) * (x - n * c) ^ 2)) := hf n
      _ ≤ C₀ * (Real.exp (-(c ^ 2 / (32 * a))) * Real.exp (1 / 32) *
          Real.exp (-((1 / 32) * (n : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left (fmrImage_pt ha hac hc hx hn) hC₀
      _ = K * Real.exp (-((1 / 32) * (n : ℝ) ^ 2)) := by rw [hK]; ring
  have hmain := UnforcedLeray.Short.IIb.TrainGap.tsum_ite_zero_bound hsum hH hH0 hb
  refine hmain.trans (le_of_eq ?_)
  rw [tsum_mul_left, hK, fmrImageLam]
  ring

theorem fmrImage_tail_u1 {a c : ℝ} (ha : 1 ≤ a) (hac : a ≤ c ^ 2) (hc : 1 ≤ c)
    (x : UnforcedLeray.B0579.Plane) (hx : |x.1| ≤ c / 2) :
    |(∑' n : ℤ, UnforcedLeray.B0146.u1 a (x.1 - n * c, x.2)) - UnforcedLeray.B0146.u1 a x| ≤
      (2 * a + 1) * Real.exp (-(c ^ 2 / (32 * a))) * fmrImageLam := by
  have h := fmrImage_cell_tail (C₀ := 2 * a + 1) (x := x.1) ha hac hc (by linarith) hx
    (f := fun n : ℤ => UnforcedLeray.B0146.u1 a (x.1 - n * c, x.2))
    (fun n => UnforcedLeray.Short.IIb.TrainGap.abs_u1_le ha le_rfl (x.1 - n * c, x.2))
  simpa using h

theorem fmrImage_tail_u2 {a c : ℝ} (ha : 1 ≤ a) (hac : a ≤ c ^ 2) (hc : 1 ≤ c)
    (x : UnforcedLeray.B0579.Plane) (hx : |x.1| ≤ c / 2) :
    |(∑' n : ℤ, UnforcedLeray.B0146.u2 a (x.1 - n * c, x.2)) - UnforcedLeray.B0146.u2 a x| ≤
      (2 * a + 1) * Real.exp (-(c ^ 2 / (32 * a))) * fmrImageLam := by
  have h := fmrImage_cell_tail (C₀ := 2 * a + 1) (x := x.1) ha hac hc (by linarith) hx
    (f := fun n : ℤ => UnforcedLeray.B0146.u2 a (x.1 - n * c, x.2))
    (fun n => UnforcedLeray.Short.IIb.TrainGap.abs_u2_le ha le_rfl (x.1 - n * c, x.2))
  simpa using h

/-- Pure real smallness: `6 Λ a³ e^{-c²/(32a)} ≤ ε/2` on `θ ≥ b`, `c²ν⁴ = 1`. -/
theorem fmrImage_small {a ν b c ε Λ : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hb : 0 < b) (hε : 0 < ε)
    (ha : 1 ≤ a) (hab : a * ν * b ≤ 1) (hc : c ^ 2 * ν ^ 4 = 1) (hΛ : 0 ≤ Λ)
    (hνD : ν ≤ ε * b ^ 9 / (12 * 720 * 32 ^ 6 * (Λ + 1))) :
    6 * Λ * (a ^ 3 * Real.exp (-(c ^ 2 / (32 * a)))) ≤ ε / 2 := by
  have ha0 : 0 < a := by linarith
  set g : ℝ := c ^ 2 / (32 * a) with hg
  have hg0 : 0 ≤ g := by positivity
  have hgq : g * (32 * a * ν ^ 4) = 1 := by
    rw [hg]; field_simp; linarith
  have h1 : g ^ 6 ≤ 720 * Real.exp g := by
    have := Real.pow_div_factorial_le_exp g hg0 6
    have hf : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hf, div_le_iff₀ (by norm_num)] at this
    linarith
  have h2 : Real.exp (-g) * g ^ 6 ≤ 720 := by
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-g)).le
    have e : Real.exp (-g) * (720 * Real.exp g) = 720 := by
      rw [mul_left_comm, ← Real.exp_add]; simp
    linarith
  set q : ℝ := 32 * a * ν ^ 4 with hq
  have hq0 : 0 ≤ q := by positivity
  have h3 : Real.exp (-g) ≤ 720 * q ^ 6 := by
    have h4 := mul_le_mul_of_nonneg_right h2 (pow_nonneg hq0 6)
    have e : Real.exp (-g) * g ^ 6 * q ^ 6 = Real.exp (-g) * (g * q) ^ 6 := by ring
    rw [e, hgq] at h4
    linarith
  -- `a³ e^{-g} b⁹ ≤ 720·32⁶ ν`
  have hpow : (a * ν * b) ^ 9 ≤ 1 := pow_le_one₀ (by positivity) hab
  have h5 : a ^ 3 * Real.exp (-g) * b ^ 9 ≤ 720 * 32 ^ 6 * ν := by
    have e1 : a ^ 3 * (720 * q ^ 6) * b ^ 9 = 720 * 32 ^ 6 * ν ^ 15 * (a * ν * b) ^ 9 := by
      rw [hq]; ring
    have h6 : a ^ 3 * Real.exp (-g) * b ^ 9 ≤ a ^ 3 * (720 * q ^ 6) * b ^ 9 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h7 : ν ^ 15 ≤ ν := by
      have : ν ^ 15 ≤ ν ^ 1 := pow_le_pow_of_le_one hν.le hν1 (by norm_num)
      simpa using this
    have h8 : 720 * 32 ^ 6 * ν ^ 15 * (a * ν * b) ^ 9 ≤ 720 * 32 ^ 6 * ν := by
      have : 720 * 32 ^ 6 * ν ^ 15 * (a * ν * b) ^ 9 ≤ 720 * 32 ^ 6 * ν ^ 15 * 1 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      nlinarith
    linarith
  -- conclude
  have hD : 0 < 12 * 720 * 32 ^ 6 * (Λ + 1) := by positivity
  have hν2 : ν * (12 * 720 * 32 ^ 6 * (Λ + 1)) ≤ ε * b ^ 9 := by
    rwa [le_div_iff₀ hD] at hνD
  have hb9 : 0 < b ^ 9 := by positivity
  have key : 6 * Λ * (a ^ 3 * Real.exp (-g)) * b ^ 9 ≤ ε / 2 * b ^ 9 := by
    have e1 : 6 * Λ * (a ^ 3 * Real.exp (-g)) * b ^ 9 =
        6 * Λ * (a ^ 3 * Real.exp (-g) * b ^ 9) := by ring
    have e2 : 6 * Λ * (a ^ 3 * Real.exp (-g) * b ^ 9) ≤ 6 * Λ * (720 * 32 ^ 6 * ν) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith [mul_nonneg hΛ hν.le, hν2]
  exact le_of_mul_le_mul_right key hb9

end UnforcedLeray.Short.IIIa
