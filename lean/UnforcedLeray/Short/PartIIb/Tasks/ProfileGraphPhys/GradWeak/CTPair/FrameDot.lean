import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_2_2

/-!
# `PartII-b:T10/7/1/2/2/1` (`ct_frame_dot`): pointwise frame identity

Source `shorter-proof-2026-11-02.tex` lines 1902-1906. Off the axis the frame `(e_r, e_z)` is
orthonormal, so `⟨e_i, e_r b_r + e_z b_z⟩ = b_i`; the real and imaginary parts of `u` are combined
linearly (no conjugation in `dotL`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CTFrameDotAux

open UnforcedLeray

lemma frameL_dot_sum (y : Space) (hy : y ∉ Axi.axis) (v w : Axi.Merid) :
    ∑ k : Fin 3, Axi.frameL y v k * Axi.frameL y w k = v 0 * w 0 + v 1 * w 1 := by
  have hs := Axi.eR_sq_sum hy
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  simp only [Fin.sum_univ_three, Axi.frameL_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two, Axi.e3_apply, h02, h12, if_false,
    ite_false, if_true, ite_true, Fin.isValue, one_pow, mul_one]
  linear_combination (v 0 * w 0) * hs

lemma frameL_dot_single (y : Space) (hy : y ∉ Axi.axis) (i : Fin 2) (w : Axi.Merid) :
    ∑ k : Fin 3, Axi.frameL y (EuclideanSpace.single i 1) k * Axi.frameL y w k = w i := by
  rw [frameL_dot_sum y hy]
  fin_cases i <;> simp

end UnforcedLeray.Short.IIb.CTFrameDotAux

open UnforcedLeray UnforcedLeray.Short.IIb.CTFrameDotAux in
theorem ct_frame_dot : UnforcedLeray.Short.IIb.CTFrameDot := by
  unfold UnforcedLeray.Short.IIb.CTFrameDot
  intro R u i τ y _hR hy
  have hS1 := frameL_dot_single y hy i (UnforcedLeray.Short.IIb.reM (u (Axi.chart R τ y)))
  have hS2 := frameL_dot_single y hy i (UnforcedLeray.Short.IIb.imM (u (Axi.chart R τ y)))
  have hS1c : ∑ k : Fin 3, ((Axi.frameL y (EuclideanSpace.single i 1) k : ℝ) : ℂ) *
      ((Axi.frameL y (UnforcedLeray.Short.IIb.reM (u (Axi.chart R τ y))) k : ℝ) : ℂ) =
      ((UnforcedLeray.Short.IIb.reM (u (Axi.chart R τ y)) i : ℝ) : ℂ) := by
    exact_mod_cast hS1
  have hS2c : ∑ k : Fin 3, ((Axi.frameL y (EuclideanSpace.single i 1) k : ℝ) : ℂ) *
      ((Axi.frameL y (UnforcedLeray.Short.IIb.imM (u (Axi.chart R τ y))) k : ℝ) : ℂ) =
      ((UnforcedLeray.Short.IIb.imM (u (Axi.chart R τ y)) i : ℝ) : ℂ) := by
    exact_mod_cast hS2
  have hre : ((UnforcedLeray.Short.IIb.reM (u (Axi.chart R τ y)) i : ℝ) : ℂ) +
      ((UnforcedLeray.Short.IIb.imM (u (Axi.chart R τ y)) i : ℝ) : ℂ) * Complex.I =
      u (Axi.chart R τ y) i := by
    have hPi : (UnforcedLeray.Short.IIb.reM (u (Axi.chart R τ y))).ofLp i =
        (u (Axi.chart R τ y) i).re := rfl
    have hQi : (UnforcedLeray.Short.IIb.imM (u (Axi.chart R τ y))).ofLp i =
        (u (Axi.chart R τ y) i).im := rfl
    rw [hPi, hQi]
    exact Complex.re_add_im _
  rw [UnforcedLeray.PhaseSpace.dotL_apply, Fin.sum_univ_three]
  simp only [UnforcedLeray.Short.IIb.frameC, UnforcedLeray.Short.IIb.NvC, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, UnforcedLeray.B0412.realC_apply, Axi.Nv]
  rw [Fin.sum_univ_three] at hS1c hS2c
  push_cast
  linear_combination (((Real.sqrt (Axi.age R y) : ℝ) : ℂ)) * hS1c +
    (((Real.sqrt (Axi.age R y) : ℝ) : ℂ) * Complex.I) * hS2c +
    (((Real.sqrt (Axi.age R y) : ℝ) : ℂ)) * hre
