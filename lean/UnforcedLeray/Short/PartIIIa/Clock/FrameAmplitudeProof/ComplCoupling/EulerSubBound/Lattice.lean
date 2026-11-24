import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.TrainDiff
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJet
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.KerExpansion
import UnforcedLeray.Lib.Train.Datum

/-!
# Lattice tails, kernel comparison and weighted norms (helper for `PartIII-a:T21/c5/3/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2876-2897:
the paired-image kernel satisfies `K_d(z) - K_∞(z) = O(d⁻²|z|)` for `|z| ≤ d/2`, the paired
translates of the dual kernels give errors `O(d⁻²)`, and the direct (Gaussian) columns have
Gaussian tails.

* `kerPl`, `kerAdjPl`: the planar Biot-Savart kernel `K_∞(z) = z^⊥/(2π|z|²)` (in the vector form
  `(Re, -Im)` of `(2πi z)⁻¹` used by `kerD`) and the planar adjoint `K_∞^T F`.
* `norm_tsum_sub_zero_le`, `shift_rpow_le`: the lattice tail `∑_{n≠0}` of an `O((1+|n|)^{-2} d^{-2})`
  family.
* `lamP_tails`, `datum_tail`, `datum_jet2_tail`: the `O(d⁻²)` periodization errors of the dual
  kernels (and their gradients), of the Gaussian velocity and of its second jet (weighted by
  `jb²`) on the cell.
* `kerD_sub_kerPl_le`: the image expansion `|K_d - K_∞|(z) ≤ C |z| / d²` for `|z| ≤ d/2`.
* `memLp_and_xNorm_of_le_jb`: the `X_{-m,d}` bound of a field growing like `jb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerSubCore

/-! ## 1. The planar kernel and the planar adjoint -/

/-- The planar Biot-Savart kernel `K_∞(z) = z^⊥ / (2π|z|²)`, component `j`, written as the vector
`(Re, -Im)` of `(2πi z)⁻¹` (the planar limit of `kerD d`, SP 2876-2881). It is `0` at `z = 0`. -/
def kerPl (z : ℝ × ℝ) (j : Fin 2) : ℝ :=
  UnforcedLeray.Cyl.vec
    ((2 * Real.pi * Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I))⁻¹).re
    (-((2 * Real.pi * Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I))⁻¹).im) j

/-- The planar adjoint `K_∞^T F (y) = ∫_{ℝ²} F(x) · K_∞(x - y) dx`. -/
def kerAdjPl (F : Fin 2 → ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ :=
  ∫ x : ℝ × ℝ, ∑ j, F j x * ((kerPl (x - y) j : ℝ) : ℂ)

/-! ## 2. Lattice tails -/

/-- `S = ∑_{n ∈ ℤ} (1 + |n|)^{-2}`. -/
def sZ : ℝ := ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ))

theorem summable_sZ : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
  Gaussian.summable_one_add_abs_int_rpow (by norm_num)

theorem sZ_nonneg : 0 ≤ sZ :=
  tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _

/-- The lattice tail `∑_{n ≠ 0} g n` of a family bounded by `A (1+|n|)^{-2}` off `0`. -/
theorem norm_tsum_sub_zero_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {g : ℤ → E} {A : ℝ} (hg : Summable g) (hA : 0 ≤ A)
    (hb : ∀ n : ℤ, n ≠ 0 → ‖g n‖ ≤ A * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :
    ‖(∑' n, g n) - g 0‖ ≤ A * sZ := by
  classical
  have h2 : HasSum (fun n => g n - (if n = 0 then g 0 else 0)) ((∑' n, g n) - g 0) :=
    hg.hasSum.sub (hasSum_ite_eq 0 (g 0))
  refine h2.norm_le_of_bounded (summable_sZ.hasSum.mul_left A) fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp only [if_true, sub_self, norm_zero]
    exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  · simp only [hn, if_false, sub_zero]
    exact hb n hn

/-- For `|t| ≤ d/2`, `1 ≤ d` and `n ≠ 0`: `(1 + |t + n d|)^{-2} ≤ (16/d²) (1 + |n|)^{-2}`. -/
theorem shift_rpow_le {d t : ℝ} (hd : 1 ≤ d) (ht : |t| ≤ d / 2) {n : ℤ} (hn : n ≠ 0) :
    (1 + |t + n * d|) ^ (-(2 : ℝ)) ≤ 16 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hd0 : 0 < d := by linarith
  have hnd : |(n : ℝ)| * d - |t| ≤ |t + n * d| := by
    have h := abs_sub_abs_le_abs_sub ((n : ℝ) * d) (-t)
    rw [abs_neg, abs_mul, abs_of_pos hd0, sub_neg_eq_add, add_comm] at h
    exact h
  have hkey : d / 4 * (1 + |(n : ℝ)|) ≤ 1 + |t + n * d| := by nlinarith
  have hpos : 0 < d / 4 * (1 + |(n : ℝ)|) := by positivity
  calc (1 + |t + n * d|) ^ (-(2 : ℝ))
      ≤ (d / 4 * (1 + |(n : ℝ)|)) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos hkey (by norm_num)
    _ = (d / 4) ^ (-(2 : ℝ)) * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
        Real.mul_rpow (by positivity) (by positivity)
    _ = 16 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
        congr 1
        rw [perCont_rpow_neg_two_eq _ (by positivity)]
        field_simp
        norm_num

/-- On the cell, `|x₁| ≤ |x₁ - n d|` for every `n ∈ ℤ`. -/
theorem abs_fst_le_of_mem_cell {d : ℝ} (hd : 0 < d) {x : ℝ × ℝ} (hx : x ∈ B0579.cell d)
    (n : ℤ) : |x.1| ≤ |x.1 - n * d| := by
  have h1 : -(d / 2) ≤ x.1 := hx.1.1
  have h2 : x.1 < d / 2 := hx.1.2
  rw [← sq_le_sq]
  have hprod : 0 ≤ ((n : ℝ) * d) * ((n : ℝ) * d - 2 * x.1) := by
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
      have ha : (n : ℝ) * d ≤ -d := by nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · subst hn; simp
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have ha : d ≤ (n : ℝ) * d := by nlinarith
      exact mul_nonneg (by linarith) (by linarith)
  nlinarith [hprod]

/-- `|x₁| ≤ d/2` on the cell. -/
theorem abs_fst_le_half_of_mem_cell {d : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell d) :
    |x.1| ≤ d / 2 :=
  abs_le.2 ⟨hx.1.1, hx.1.2.le⟩

/-- `e^{-t²/16} ≤ 34 (1 + |t|)^{-2}`. -/
theorem exp_neg_sq_div_sixteen_le (t : ℝ) :
    Real.exp (-(t ^ 2) / 16) ≤ 34 * (1 + |t|) ^ (-(2 : ℝ)) := by
  have hpos : 0 < 1 + |t| := by positivity
  rw [perCont_rpow_neg_two_eq _ hpos.le, inv_pow, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  have h1 := Gaussian.pow_mul_exp_neg_le_factorial 1 (s := t ^ 2 / 16) (by positivity)
  have he : Real.exp (-(t ^ 2) / 16) = Real.exp (-(t ^ 2 / 16)) := by ring_nf
  rw [he]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h1
  have hsq : (1 + |t|) ^ 2 ≤ 2 + 2 * t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hE : 0 ≤ Real.exp (-(t ^ 2 / 16)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(t ^ 2 / 16)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  nlinarith

/-- `jb(w)² e^{-|w|²/8} ≤ 1026 e^{-|w|²/16}`. -/
theorem jb_sq_mul_exp_le (w : ℝ × ℝ) :
    B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8) ≤
      1026 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16) := by
  set s : ℝ := w.1 ^ 2 + w.2 ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hjb : B0579.jb w = 1 + s := by simp only [B0579.jb, hs]; ring
  rw [hjb]
  have hsplit : Real.exp (-s / 8) = Real.exp (-s / 16) * Real.exp (-(s / 16)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have h2 := Gaussian.pow_mul_exp_neg_le_factorial 2 (s := s / 16) (by positivity)
  have h1 := Gaussian.pow_mul_exp_neg_le_factorial 1 (s := s / 16) (by positivity)
  have h0 : Real.exp (-(s / 16)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  simp only [pow_one, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat] at h1 h2
  have hE : 0 < Real.exp (-s / 16) := Real.exp_pos _
  have hF : 0 ≤ Real.exp (-(s / 16)) := (Real.exp_pos _).le
  have hpoly : (1 + s) ^ 2 * Real.exp (-(s / 16)) ≤ 1026 := by nlinarith
  calc (1 + s) ^ 2 * (Real.exp (-s / 16) * Real.exp (-(s / 16)))
      = ((1 + s) ^ 2 * Real.exp (-(s / 16))) * Real.exp (-s / 16) := by ring
    _ ≤ 1026 * Real.exp (-s / 16) := mul_le_mul_of_nonneg_right hpoly hE.le

/-! ## 3. The image expansion of the cylinder kernel -/

theorem planeToC_eq (z : ℝ × ℝ) : planeToC z = (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [planeToC]

theorem kerPl_zero (z : ℝ × ℝ) :
    kerPl z 0 = ((2 * Real.pi * Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I))⁻¹).re := rfl

theorem kerPl_one (z : ℝ × ℝ) :
    kerPl z 1 = -((2 * Real.pi * Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I))⁻¹).im := rfl

theorem kerD_zero (d : ℝ) (z : ℝ × ℝ) :
    kerD d z 0 = (Kernels.cylinderBS d ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).re := rfl

theorem kerD_one (d : ℝ) (z : ℝ × ℝ) :
    kerD d z 1 = -(Kernels.cylinderBS d ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).im := rfl

/-- `|K_∞(z)_j| ≤ (2π|z|)⁻¹`. -/
theorem abs_kerPl_le (z : ℝ × ℝ) (j : Fin 2) :
    |kerPl z j| ≤ (2 * Real.pi * ‖planeToC z‖)⁻¹ := by
  have hP : ‖(2 * Real.pi * Complex.I * ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I))⁻¹‖ =
      (2 * Real.pi * ‖planeToC z‖)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, norm_mul, Complex.norm_I, ← planeToC_eq]
    simp [Real.pi_pos.le, abs_of_pos Real.pi_pos]
  rw [← hP]
  fin_cases j
  · rw [Fin.zero_eta, kerPl_zero]
    exact Complex.abs_re_le_norm _
  · rw [Fin.mk_one, kerPl_one, abs_neg]
    exact Complex.abs_im_le_norm _

/-- **Image expansion** (SP 2876-2881): `|K_d(z)_j - K_∞(z)_j| ≤ C_I |z| / d²` for `|z| ≤ d/2`. -/
theorem kerD_sub_kerPl_le : ∃ C_I : ℝ, 0 ≤ C_I ∧ ∀ d : ℝ, 1 ≤ d → ∀ z : ℝ × ℝ,
    ‖planeToC z‖ ≤ d / 2 → ∀ j : Fin 2,
      |kerD d z j - kerPl z j| ≤ C_I * ‖planeToC z‖ / d ^ 2 := by
  refine ⟨Real.pi / 6 + KerExp.imageConst / 4, by
    have := Real.pi_pos; unfold KerExp.imageConst; positivity, fun d hd z hz j => ?_⟩
  have hd0 : 0 < d := by linarith
  set ζ : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I with hζ
  have hζn : ‖ζ‖ = ‖planeToC z‖ := by rw [planeToC_eq]
  set Δ : ℂ := Kernels.cylinderBS d ζ - (2 * Real.pi * Complex.I * ζ)⁻¹ with hΔ
  have hcomp : |kerD d z j - kerPl z j| ≤ ‖Δ‖ := by
    fin_cases j
    · rw [Fin.zero_eta, kerD_zero, kerPl_zero, ← hζ, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    · rw [Fin.mk_one, kerD_one, kerPl_one, ← hζ,
        show -(Kernels.cylinderBS d ζ).im - -((2 * ↑Real.pi * Complex.I * ζ)⁻¹).im =
          -(Δ.im) by rw [hΔ, Complex.sub_im]; ring, abs_neg]
      exact Complex.abs_im_le_norm _
  refine hcomp.trans ?_
  rw [← hζn]
  by_cases hz0 : ζ = 0
  · have hΔ0 : Δ = 0 := by
      rw [hΔ, hz0]
      simp [Kernels.cylinderBS, Complex.cot]
    rw [hΔ0, norm_zero, hz0, norm_zero]
    simp
  set T : ℂ := (2 * Real.pi * Complex.I)⁻¹ * (Real.pi ^ 2 / 3) * ζ / d ^ 2 with hT
  have hexp := KerExp.cylinderBS_image_expansion' hd0 hz0 (by rw [hζn]; exact hz)
  have hTn : ‖T‖ = Real.pi / 6 * ‖ζ‖ / d ^ 2 := by
    rw [hT, norm_div, norm_mul, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
    have hpi2 : ‖((Real.pi : ℂ) ^ 2 / 3)‖ = Real.pi ^ 2 / 3 := by
      rw [norm_div, norm_pow, hpi]; simp
    have hd2 : ‖((d : ℂ) ^ 2)‖ = d ^ 2 := by rw [norm_pow]; simp [abs_of_pos hd0]
    rw [h2, hpi, hpi2, hd2]
    field_simp
    ring
  have hsplit : Δ = (Δ + T) - T := by ring
  have hζle : ‖ζ‖ ≤ d / 2 := by rw [hζn]; exact hz
  calc ‖Δ‖ = ‖(Δ + T) - T‖ := by rw [← hsplit]
    _ ≤ ‖Δ + T‖ + ‖T‖ := norm_sub_le _ _
    _ ≤ KerExp.imageConst * ‖ζ‖ ^ 3 / d ^ 4 + Real.pi / 6 * ‖ζ‖ / d ^ 2 := by
        rw [hTn]
        gcongr
    _ ≤ (Real.pi / 6 + KerExp.imageConst / 4) * ‖ζ‖ / d ^ 2 := by
        have hI : 0 ≤ KerExp.imageConst := by unfold KerExp.imageConst; positivity
        have hsq : ‖ζ‖ ^ 2 ≤ d ^ 2 / 4 := by
          have := norm_nonneg ζ
          nlinarith
        have h3 : KerExp.imageConst * ‖ζ‖ ^ 3 / d ^ 4 ≤ KerExp.imageConst / 4 * ‖ζ‖ / d ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have := norm_nonneg ζ
          have hd2 : 0 < d ^ 2 := by positivity
          nlinarith [mul_nonneg hI (norm_nonneg ζ), mul_nonneg (mul_nonneg hI (norm_nonneg ζ)) hd2.le]
        have hsplit2 : (Real.pi / 6 + KerExp.imageConst / 4) * ‖ζ‖ / d ^ 2 =
            Real.pi / 6 * ‖ζ‖ / d ^ 2 + KerExp.imageConst / 4 * ‖ζ‖ / d ^ 2 := by ring
        linarith [h3]

/-! ## 4. Periodization errors -/

theorem inv_sq_le_rpow (a b : ℝ) : ((1 + |a| + |b|)⁻¹) ^ 2 ≤ (1 + |a|) ^ (-(2 : ℝ)) := by
  rw [perCont_rpow_neg_two_eq _ (by positivity)]
  have h1 : 0 < 1 + |a| := by positivity
  have h2 : 1 + |a| ≤ 1 + |a| + |b| := by linarith [abs_nonneg b]
  have h3 : (1 + |a| + |b|)⁻¹ ≤ (1 + |a|)⁻¹ := inv_anti₀ h1 h2
  have h4 : 0 ≤ (1 + |a| + |b|)⁻¹ := by positivity
  exact pow_le_pow_left₀ h4 h3 2

/-- The periodization error `P_d L - L` of an `O((1+|z₁|)^{-2})` profile, `perSum` convention. -/
theorem perSum_sub_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {L : ℝ × ℝ → E}
    {C : ℝ} (hC0 : 0 ≤ C) (hL : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    {d : ℝ} (hd : 1 ≤ d) {y : ℝ × ℝ} (hy : |y.1| ≤ d / 2) :
    ‖(∑' n : ℤ, L (y.1 + n * d, y.2)) - L y‖ ≤ 16 * C * sZ / d ^ 2 := by
  have hd0 : d ≠ 0 := by positivity
  have hs : Summable (fun n : ℤ => L (y.1 + n * d, y.2)) := by
    refine Summable.of_norm_bounded ((Gaussian.summable_translate (s := 2) (c := -d)
      (by norm_num) (neg_ne_zero.2 hd0) y.1).mul_left C) (fun n => ?_)
    rw [show y.1 - (n : ℝ) * -d = y.1 + n * d by ring]
    exact hL _
  have h := norm_tsum_sub_zero_le hs (A := 16 * C / d ^ 2) (by positivity) (fun n hn => by
    calc ‖L (y.1 + n * d, y.2)‖ ≤ C * (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) := hL _
      _ ≤ C * (16 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (shift_rpow_le hd hy hn) hC0
      _ = 16 * C / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring)
  simp only [Int.cast_zero, zero_mul, add_zero, Prod.mk.eta] at h
  calc ‖(∑' n : ℤ, L (y.1 + n * d, y.2)) - L y‖ ≤ 16 * C / d ^ 2 * sZ := h
    _ = 16 * C * sZ / d ^ 2 := by ring

/-- The `Gaussian.periodize` convention `∑ L(y₁ - n d, y₂)` of `perSum_sub_le`. -/
theorem periodize_sub_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {L : ℝ × ℝ → E}
    {C : ℝ} (hC0 : 0 ≤ C) (hL : ∀ z : ℝ × ℝ, ‖L z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)))
    {d : ℝ} (hd : 1 ≤ d) {y : ℝ × ℝ} (hy : |y.1| ≤ d / 2) :
    ‖(∑' n : ℤ, L (y.1 - n * d, y.2)) - L y‖ ≤ 16 * C * sZ / d ^ 2 := by
  have hd0 : d ≠ 0 := by positivity
  have hs : Summable (fun n : ℤ => L (y.1 - n * d, y.2)) := by
    refine Summable.of_norm_bounded ((Gaussian.summable_translate (s := 2) (c := d)
      (by norm_num) hd0 y.1).mul_left C) (fun n => hL _)
  have hy' : |-y.1| ≤ d / 2 := by rwa [abs_neg]
  have h := norm_tsum_sub_zero_le hs (A := 16 * C / d ^ 2) (by positivity) (fun n hn => by
    calc ‖L (y.1 - n * d, y.2)‖ ≤ C * (1 + |y.1 - n * d|) ^ (-(2 : ℝ)) := hL _
      _ = C * (1 + |-y.1 + n * d|) ^ (-(2 : ℝ)) := by
          rw [show -y.1 + n * d = -(y.1 - n * d) by ring, abs_neg]
      _ ≤ C * (16 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (shift_rpow_le hd hy' hn) hC0
      _ = 16 * C / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring)
  simp only [Int.cast_zero, zero_mul, sub_zero, Prod.mk.eta] at h
  calc ‖(∑' n : ℤ, L (y.1 - n * d, y.2)) - L y‖ ≤ 16 * C / d ^ 2 * sZ := h
    _ = 16 * C * sZ / d ^ 2 := by ring

/-- Jets of the dual kernels (SP 593-610, 2891-2897): `C¹` with `O((1+|z₁|+|z₂|)^{-2})` value and
gradient. -/
theorem lamP_jets {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    (∀ k : Fin 2, Differentiable ℝ (κ.lamP k)) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (k : Fin 2) (z : ℝ × ℝ), ‖κ.lamP k z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) ∧
      (∀ (k : Fin 2) (z : ℝ × ℝ),
        ‖fderiv ℝ (κ.lamP k) z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) := by
  obtain ⟨hCD, C, hC0, h0, h1, -⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  refine ⟨fun k => (hCD k).differentiable (by norm_num), C, hC0, h0, fun k z => ?_⟩
  have h := h1 k z
  have hn : 0 ≤ ‖fderiv ℝ (κ.lamP k) z‖ := norm_nonneg _
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

/-- **Paired translates of the dual kernels** (SP 2891-2897): on the cell, `P_d λ_k - λ_k` and
`∂_l(P_d λ_k) - ∂_l λ_k` are `O(d⁻²)`. -/
theorem lamP_tails {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ d : ℝ, 1 ≤ d → ∀ (k : Fin 2) (y : ℝ × ℝ), y ∈ B0579.cell d →
      ‖perLam0 κ d k y - κ.lamP k y‖ ≤ C₁ / d ^ 2 ∧
      ∀ l : Fin 2, ‖pdCx l (perLam0 κ d k) y - pdCx l (κ.lamP k) y‖ ≤ C₁ / d ^ 2 := by
  obtain ⟨hL, C, hC0, h0, h1⟩ := lamP_jets hκ
  refine ⟨16 * C * sZ, by have := sZ_nonneg; positivity, fun d hd k y hy => ?_⟩
  have hd0 : d ≠ 0 := by positivity
  have hy1 := abs_fst_le_half_of_mem_cell hy
  have hb0 : ∀ z : ℝ × ℝ, ‖κ.lamP k z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z =>
    (h0 k z).trans (mul_le_mul_of_nonneg_left (inv_sq_le_rpow _ _) hC0)
  refine ⟨?_, fun l => ?_⟩
  · have h := perSum_sub_le hC0 hb0 hd hy1
    calc ‖perLam0 κ d k y - κ.lamP k y‖
        = ‖(∑' n : ℤ, κ.lamP k (y.1 + n * d, y.2)) - κ.lamP k y‖ := rfl
      _ ≤ 16 * C * sZ / d ^ 2 := h
  · have hb1 : ∀ z : ℝ × ℝ, ‖pdCx l (κ.lamP k) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z =>
      ((CutFTCGradPerSum.norm_pdCx_le_norm_fderiv _ l z).trans (h1 k z)).trans
        (mul_le_mul_of_nonneg_left (inv_sq_le_rpow _ _) hC0)
    have h := perSum_sub_le hC0 hb1 hd hy1
    rw [show perLam0 κ d k = perSum d (κ.lamP k) from rfl,
      CutFTCGradPerSum.pdCx_perSum_eq_perSum_pdCx (hL k) hd0 (h0 k) (h1 k) l y]
    exact h

/-- The Gaussian velocity `v₀` is `O((1+|z₁|)^{-2})` with a nonnegative constant. -/
theorem v0_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × ℝ,
    ‖UnforcedLeray.Train.v0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := UnforcedLeray.Train.v0_translate_bound 0
  have hC' : ∀ z : ℝ × ℝ, ‖UnforcedLeray.Train.v0 z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro z; have := hC z; rwa [norm_iteratedFDeriv_zero] at this
  have hC0 : 0 ≤ C := by
    have h := hC' 0
    have hp : (0 : ℝ) < (1 + |(0 : ℝ × ℝ).1|) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have : C * (1 + |(0 : ℝ × ℝ).1|) ^ (-(2 : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp
    linarith [norm_nonneg (UnforcedLeray.Train.v0 0)]
  exact ⟨C, hC0, hC'⟩

/-- **Gaussian columns** (SP 2895): the periodized Gaussian velocity differs from `v₀` by
`O(d⁻²)` on the cell. -/
theorem datum_tail : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ d : ℝ, 1 ≤ d → ∀ y : ℝ × ℝ, y ∈ B0579.cell d →
    ‖UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y‖ ≤ C₂ / d ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := v0_bound
  refine ⟨16 * C * sZ, by have := sZ_nonneg; positivity, fun d hd y hy => ?_⟩
  exact periodize_sub_le hC0 hC hd (abs_fst_le_half_of_mem_cell hy)

/-- The second jet of the periodized Gaussian velocity differs from that of `v₀` by
`O(d⁻²)`, with the weight `jb²`, on the cell. -/
theorem datum_jet2_tail : ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ d : ℝ, 1 ≤ d → ∀ x : ℝ × ℝ, x ∈ B0579.cell d →
    B0579.jb x ^ 2 * ‖iteratedFDeriv ℝ 2 (UnforcedLeray.Train.datum d) x -
      iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 x‖ ≤ C₃ / d ^ 2 := by
  obtain ⟨A, hA, hb⟩ := UnforcedLeray.Train.norm_iteratedFDeriv_v0_le 2
  obtain ⟨Ct, hCt⟩ := UnforcedLeray.Train.v0_translate_bound 2
  refine ⟨1026 * 34 * 16 * A * sZ, by have := sZ_nonneg; positivity, fun d hd x hx => ?_⟩
  have hd0 : d ≠ 0 := by positivity
  have hdpos : 0 < d := by linarith
  have hjb : 0 < B0579.jb x := B0579.jb_pos x
  have hjet : iteratedFDeriv ℝ 2 (UnforcedLeray.Train.datum d) x =
      ∑' n : ℤ, iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 (x.1 - n * d, x.2) := by
    have h := congrFun (UnforcedLeray.Train.jet_datum hd0 2) x
    simpa only [UnforcedLeray.Train.jet, Gaussian.periodize] using h
  have hs : Summable (fun n : ℤ => iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 (x.1 - n * d, x.2)) :=
    Summable.of_norm_bounded ((Gaussian.summable_translate (s := 2) (c := d)
      (by norm_num) hd0 x.1).mul_left Ct) (fun n => hCt _)
  have hx' : |-x.1| ≤ d / 2 := by rw [abs_neg]; exact abs_fst_le_half_of_mem_cell hx
  set K : ℝ := 1026 * 34 * 16 * A with hK
  have hterm : ∀ n : ℤ, n ≠ 0 →
      ‖iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 (x.1 - n * d, x.2)‖ ≤
        K / d ^ 2 / B0579.jb x ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    intro n hn
    set w : ℝ × ℝ := (x.1 - n * d, x.2) with hw
    have hxw : x.1 ^ 2 ≤ w.1 ^ 2 := by
      have := abs_fst_le_of_mem_cell hdpos hx n
      exact sq_le_sq.2 (by simpa [hw] using this)
    have hjbw : B0579.jb x ≤ B0579.jb w := by
      simp only [B0579.jb, hw]; linarith
    have hjb2 : B0579.jb x ^ 2 ≤ B0579.jb w ^ 2 := pow_le_pow_left₀ hjb.le hjbw 2
    have hexp : Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16) ≤ Real.exp (-(w.1 ^ 2) / 16) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg w.2])
    have hshift : (1 + |w.1|) ^ (-(2 : ℝ)) ≤ 16 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
      have := shift_rpow_le hd hx' hn
      rwa [show -x.1 + n * d = -(w.1) by simp [hw]; ring, abs_neg] at this
    have hmain : B0579.jb x ^ 2 * ‖iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 w‖ ≤
        K / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
      have hE := Real.exp_pos (-(w.1 ^ 2 + w.2 ^ 2) / 8)
      calc B0579.jb x ^ 2 * ‖iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 w‖
          ≤ B0579.jb w ^ 2 * (A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8)) :=
            mul_le_mul hjb2 (hb w) (norm_nonneg _) (by positivity)
        _ = A * (B0579.jb w ^ 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 8)) := by ring
        _ ≤ A * (1026 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / 16)) :=
            mul_le_mul_of_nonneg_left (jb_sq_mul_exp_le w) hA
        _ ≤ A * (1026 * (34 * (1 + |w.1|) ^ (-(2 : ℝ)))) := by
            gcongr
            exact hexp.trans (exp_neg_sq_div_sixteen_le w.1)
        _ ≤ A * (1026 * (34 * (16 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))))) := by gcongr
        _ = K / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by rw [hK]; ring
    calc ‖iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 w‖
        = (B0579.jb x ^ 2 * ‖iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 w‖) / B0579.jb x ^ 2 := by
          field_simp
      _ ≤ (K / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) / B0579.jb x ^ 2 :=
          div_le_div_of_nonneg_right hmain (by positivity)
      _ = K / d ^ 2 / B0579.jb x ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring
  have h := norm_tsum_sub_zero_le hs (A := K / d ^ 2 / B0579.jb x ^ 2) (by positivity) hterm
  simp only [Int.cast_zero, zero_mul, sub_zero, Prod.mk.eta] at h
  rw [hjet]
  calc B0579.jb x ^ 2 * ‖(∑' n : ℤ, iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 (x.1 - n * d, x.2)) -
        iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 x‖
      ≤ B0579.jb x ^ 2 * (K / d ^ 2 / B0579.jb x ^ 2 * sZ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = K * sZ / d ^ 2 := by field_simp
    _ = 1026 * 34 * 16 * A * sZ / d ^ 2 := by rw [hK]

/-! ## 5. The `X_{-m,d}` norm of a field growing like `jb` -/

/-- A field with `‖F‖ ≤ M jb` on the cell is in `X_{-m,d}` (`m > 3`) with norm at most
`C_{m-2} M`. -/
theorem memLp_and_xNorm_of_le_jb {m d M : ℝ} (hm : 3 < m) (hM : 0 ≤ M) {F : ℝ × ℝ → ℂ}
    (hFm : AEStronglyMeasurable F (volume.restrict (B0579.cell d)))
    (hb : ∀ y ∈ B0579.cell d, ‖F y‖ ≤ M * B0579.jb y) :
    MemLp F 2 (B0579.cellMeasure d (-m)) ∧
    xNorm d (-m) F ≤ ENNReal.ofReal ((B0592.weightConst (m - 2)).toReal * M) := by
  set G : ℝ × ℝ → ℂ := fun y => F y * ((B0579.jb y : ℂ))⁻¹ with hG
  have hjbC : Continuous fun y : ℝ × ℝ => ((B0579.jb y : ℂ))⁻¹ :=
    (Complex.continuous_ofReal.comp B0579.continuous_jb).inv₀
      (fun y => by simp only [Function.comp_apply]; exact_mod_cast (B0579.jb_pos y).ne')
  have hGm : AEStronglyMeasurable G (volume.restrict (B0579.cell d)) :=
    hFm.mul hjbC.aestronglyMeasurable
  have hGb : ∀ y ∈ B0579.cell d, ‖G y‖ ≤ M := by
    intro y hy
    have hj := B0579.jb_pos y
    rw [hG, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hj.le,
      ← div_eq_mul_inv, div_le_iff₀ hj]
    exact hb y hy
  obtain ⟨-, hGx⟩ := ComplCouplingHeat.memLp_and_xNorm_neg_le_of_cell_bdd (m := m - 2)
    (by linarith) hM hGm hGb
  have hFG : ∀ y, F y = (B0579.jb y : ℂ) * G y := by
    intro y
    have : (B0579.jb y : ℂ) ≠ 0 := by exact_mod_cast (B0579.jb_pos y).ne'
    rw [hG]; field_simp
  have hl : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure d (-m)) =
      ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure d (-(m - 2))) := by
    unfold B0579.cellMeasure
    have hdm : ∀ m' : ℝ, Measurable fun x => ((B0579.density m' x : ℝ≥0) : ℝ≥0∞) :=
      fun m' => (B0579.measurable_density m').coe_nnreal_ennreal
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hdm _)
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top),
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hdm _)
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
    refine lintegral_congr fun x => ?_
    have hj := B0579.jb_pos x
    simp only [Pi.mul_apply]
    rw [hFG x, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_assoc]
    congr 1
    have he : ‖(B0579.jb x : ℂ)‖ₑ = ENNReal.ofReal (B0579.jb x) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hj.le]
    rw [he, ENNReal.ofReal_rpow_of_nonneg hj.le (by norm_num)]
    have hd1 : ((B0579.density (-m) x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ (-m)) := rfl
    have hd2 : ((B0579.density (-(m - 2)) x : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (B0579.jb x ^ (-(m - 2))) := rfl
    rw [hd1, hd2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hj.le _), ← Real.rpow_add hj]
    congr 2
    ring
  have hxeq : xNorm d (-m) F = xNorm d (-(m - 2)) G := by
    unfold xNorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [hl]
  have hx : xNorm d (-m) F ≤ ENNReal.ofReal ((B0592.weightConst (m - 2)).toReal * M) :=
    hxeq ▸ hGx
  refine ⟨⟨hFm.mono_ac (B0579.cellMeasure_ac d (-m)), ?_⟩, hx⟩
  exact lt_of_le_of_lt hx ENNReal.ofReal_lt_top

end EulerSubCore

end UnforcedLeray.Short.IIIa
