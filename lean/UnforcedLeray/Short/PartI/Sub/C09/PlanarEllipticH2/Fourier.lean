import UnforcedLeray.Lib.SobolevC.Elliptic

/-!
# First-order bound on `Eucl 2` via Plancherel (helper for `PartI:PlanarEllipticH2`)

* `integral_sq_norm_Lp'`: for an `L²` element `G`, `∫ ‖G‖² = ‖G‖²` (Bochner form);
* `alphaFst i`: the word `∂_i` as an element of `Idx 2 2`, with `word = [e i]`;
* `firstOrder_pt`: the Fourier symbol of `∂_i` is `2πi ξ_i`, so `|𝓕(∂_i x)(ξ)|² = (2π)² ξ_i² |𝓕x(ξ)|²`;
* `firstOrder_sum`: `∑_i |𝓕(∂_i x)|² = (2π)² |ξ|² |𝓕x|²` a.e.;
* `lap_fourier_sq`: `(2π)⁴ |ξ|⁴ |𝓕f(ξ)|² = |𝓕g(ξ)|²` a.e. when `Δf = g` weakly;
* `firstOrder_bound`: `∑_i ∫ |∂_i x|² ≤ 2π² (∫ |𝓕f|² + ∫ |ξ|⁴|𝓕f|²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ContDiff ENNReal Real FourierTransform

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Sob

/-- Bochner form of the `L²` norm identity: `∫ ‖G‖² = ‖G‖²`. -/
theorem integral_sq_norm_Lp' (G : Lp ℂ 2 (volume : Measure (Eucl 2))) :
    ∫ y, ‖(G : Eucl 2 → ℂ) y‖ ^ 2 = ‖G‖ ^ 2 := by
  have hm : AEStronglyMeasurable (fun y => ‖(G : Eucl 2 → ℂ) y‖ ^ 2) volume :=
    ((Lp.aestronglyMeasurable G).norm).pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => by positivity) hm]
  have h1 : ∫⁻ y, ENNReal.ofReal (‖(G : Eucl 2 → ℂ) y‖ ^ 2) =
      ∫⁻ y, ‖(G : Eucl 2 → ℂ) y‖ₑ ^ 2 :=
    lintegral_congr fun y => by rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1, eLpNorm_two_sq_Lp, ENNReal.toReal_ofReal (by positivity)]

/-- The word `∂_i` in `Idx 2 2` (a word of length one, viewed in the order-two index set). -/
def alphaFst (i : Fin 2) : Idx 2 2 :=
  Idx.castLE (by norm_num : (1 : ℕ) ≤ 2) (Idx.cons i (Idx.zero : Idx 2 0))

theorem word_alphaFst (i : Fin 2) : (wholeSpace 2).word (alphaFst i) = [e i] := by
  simp [alphaFst, TestDomain.word_castLE, TestDomain.word_cons, wholeSpace_dir]

theorem alphaFst_val (i : Fin 2) : (alphaFst i).1.val = 1 := rfl

theorem polyW_single (i : Fin 2) (ξ : Eucl 2) : polyW [e i] ξ = ((ξ i : ℝ) : ℂ) := by
  simp [polyW, e, EuclideanSpace.inner_single_right]

/-- The Fourier symbol of `∂_i` on `W^{2,2}(ℝ²)`: `|𝓕(∂_i x)(ξ)|² = (2π)² ξ_i² |𝓕x(ξ)|²`
almost everywhere. -/
theorem firstOrder_pt (x : W (wholeSpace 2) 1 ℂ ℂ 2 2) (i : Fin 2) :
    ∀ᵐ ξ ∂volume, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 =
      (2 * π) ^ 2 * ξ i ^ 2 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 := by
  filter_upwards [W.fourierDeriv_ae x (alphaFst i)] with ξ hξ
  rw [← hξ, alphaFst_val, word_alphaFst]
  have e1 : ‖(2 : ℂ) * (π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have e3 : ‖((ξ i : ℝ) : ℂ)‖ = |ξ i| := by rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [Pi.smul_apply, smul_eq_mul, pow_one, polyW_single]
  rw [norm_mul, norm_mul, norm_mul, e1, Complex.norm_I, e3, mul_one, mul_pow, mul_pow, sq_abs]

/-- The first-order symbol summed over `i`: `∑_i |𝓕(∂_i x)|² = (2π)² |ξ|² |𝓕x|²` a.e. -/
theorem firstOrder_sum_pt (x : W (wholeSpace 2) 1 ℂ ℂ 2 2) :
    ∀ᵐ ξ ∂volume, ∑ i : Fin 2, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 =
      (2 * π) ^ 2 * ‖ξ‖ ^ 2 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 := by
  filter_upwards [firstOrder_pt x 0, firstOrder_pt x 1] with ξ h0 h1
  rw [Fin.sum_univ_two, h0, h1]
  have hn : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [hn]
  ring

/-- The Fourier side of the Laplacian: `(2π)⁴ |ξ|⁴ |𝓕f|² = |𝓕g|²` a.e. when `Δf = g` weakly. -/
theorem lap_fourier_pt {F_L G : Lp ℂ 2 (volume : Measure (Eucl 2))}
    (h : IsWeakLaplacian (F_L : Eucl 2 → ℂ) (G : Eucl 2 → ℂ)) :
    ∀ᵐ ξ ∂volume, ‖((𝓕 G : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2 =
      (2 * π) ^ 4 * (‖ξ‖ ^ 4 * ‖((𝓕 F_L : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2) := by
  filter_upwards [h.fourier_ae] with ξ hξ
  have hnn : 0 ≤ (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hl : ‖lapSym ξ‖ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
    unfold lapSym
    rw [Complex.norm_real, Real.norm_eq_abs,
      show -(2 * π) ^ 2 * ‖ξ‖ ^ 2 = -((2 * π) ^ 2 * ‖ξ‖ ^ 2) by ring, abs_neg,
      abs_of_nonneg hnn]
  rw [← hξ, norm_smul, hl]
  ring

/-- The Fourier side integrated: `(2π)⁴ ∫ |ξ|⁴ |𝓕f|² = ‖g‖²`. -/
theorem lap_fourier_integral {F_L G : Lp ℂ 2 (volume : Measure (Eucl 2))}
    (h : IsWeakLaplacian (F_L : Eucl 2 → ℂ) (G : Eucl 2 → ℂ)) :
    (2 * π) ^ 4 * ∫ ξ, ‖ξ‖ ^ 4 * ‖((𝓕 F_L : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2 =
      ‖G‖ ^ 2 := by
  have e1 : ∫ ξ, ‖((𝓕 G : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2 =
      ∫ ξ, (2 * π) ^ 4 * (‖ξ‖ ^ 4 * ‖((𝓕 F_L : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2) :=
    integral_congr_ae (lap_fourier_pt h)
  have e2 : ∫ ξ, ‖((𝓕 G : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2 = ‖G‖ ^ 2 := by
    rw [integral_sq_norm_Lp', Lp.norm_fourier_eq]
  rw [integral_const_mul, e2] at e1
  exact e1.symm

/-- **First-order bound on `Eucl 2`**: `∑_i ∫ |∂_i u|² ≤ 2π² (‖u‖² + ‖g‖²)` for `u = F_L` with
`Δu = g` weakly, where `∂_i` are the first derivatives of the `W^{2,2}` element `x` with field `F_L`. -/
theorem firstOrder_bound (x : W (wholeSpace 2) 1 ℂ ℂ 2 2) {F_L G : Lp ℂ 2 (volume : Measure (Eucl 2))}
    (hx : toVol (W.value (wholeSpace 2) 1 ℂ ℂ 2 2 x) = F_L)
    (h : IsWeakLaplacian (F_L : Eucl 2 → ℂ) (G : Eucl 2 → ℂ)) :
    ∑ i : Fin 2, ∫ y, ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (alphaFst i) x) : Eucl 2 → ℂ) y‖ ^ 2 ≤
      2 * π ^ 2 * (‖F_L‖ ^ 2 + ‖G‖ ^ 2) := by
  have hfv_eq : W.fourierValue x = 𝓕 F_L := by rw [W.fourierValue, hx]
  have step1 : ∀ i : Fin 2,
      ∫ y, ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (alphaFst i) x) : Eucl 2 → ℂ) y‖ ^ 2 =
        ∫ ξ, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 := by
    intro i
    rw [integral_sq_norm_Lp', integral_sq_norm_Lp', W.fourierDeriv, Lp.norm_fourier_eq]
  have hint : ∀ i : Fin 2,
      Integrable (fun ξ => ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2) :=
    fun i => (Lp.memLp _).norm.integrable_sq
  have hfvint : Integrable (fun ξ => ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) :=
    (Lp.memLp _).norm.integrable_sq
  have hBint : Integrable (fun ξ => ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) := by
    have h1 : Integrable (fun ξ => ((2 * π) ^ 4)⁻¹ *
        ‖((𝓕 G : Lp ℂ 2 (volume : Measure (Eucl 2))) : Eucl 2 → ℂ) ξ‖ ^ 2) :=
      ((Lp.memLp _).norm.integrable_sq).const_mul _
    refine h1.congr ?_
    filter_upwards [lap_fourier_pt h] with ξ hξ
    rw [hfv_eq, hξ, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hS1 : ∑ i : Fin 2, ∫ ξ, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 =
      ∫ ξ, ∑ i : Fin 2, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 :=
    (integral_finset_sum Finset.univ fun i _ => hint i).symm
  have hI1 : Integrable (fun ξ => ∑ i : Fin 2, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2) :=
    integrable_finset_sum _ fun i _ => hint i
  have hS2 : ∫ ξ, ∑ i : Fin 2, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 ≤
      ∫ ξ, (2 * π) ^ 2 / 2 * (‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 +
        ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) := by
    refine integral_mono_ae hI1 ((hfvint.add hBint).const_mul _) ?_
    filter_upwards [firstOrder_sum_pt x] with ξ hξ
    rw [hξ]
    have hb : 0 ≤ ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (2 * π)) hb) (sq_nonneg (‖ξ‖ ^ 2 - 1))]
  have hS3 : ∫ ξ, (2 * π) ^ 2 / 2 * (‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 +
        ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) =
      (2 * π) ^ 2 / 2 * (‖F_L‖ ^ 2 + ∫ ξ, ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) := by
    rw [integral_const_mul, integral_add hfvint hBint]
    congr 1
    rw [integral_sq_norm_Lp', hfv_eq, Lp.norm_fourier_eq]
  have hBle : ∫ ξ, ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    have hBnn : 0 ≤ ∫ ξ, ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 :=
      integral_nonneg fun ξ => by positivity
    have hc1 : (1 : ℝ) ≤ (2 * π) ^ 4 := one_le_pow₀ (by linarith [Real.two_le_pi])
    have hBeq := lap_fourier_integral h
    rw [← hfv_eq] at hBeq
    nlinarith [mul_le_mul_of_nonneg_right hc1 hBnn]
  have hpos : (0 : ℝ) ≤ (2 * π) ^ 2 / 2 := by positivity
  have hfin := mul_le_mul_of_nonneg_left hBle hpos
  calc ∑ i : Fin 2, ∫ y, ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (alphaFst i) x) : Eucl 2 → ℂ) y‖ ^ 2
      = ∑ i : Fin 2, ∫ ξ, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => step1 i
    _ = ∫ ξ, ∑ i : Fin 2, ‖(W.fourierDeriv x (alphaFst i) : Eucl 2 → ℂ) ξ‖ ^ 2 := hS1
    _ ≤ ∫ ξ, (2 * π) ^ 2 / 2 * (‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2 +
        ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) := hS2
    _ = (2 * π) ^ 2 / 2 * (‖F_L‖ ^ 2 + ∫ ξ, ‖ξ‖ ^ 4 * ‖(W.fourierValue x : Eucl 2 → ℂ) ξ‖ ^ 2) := hS3
    _ ≤ (2 * π) ^ 2 / 2 * (‖F_L‖ ^ 2 + ‖G‖ ^ 2) := by linarith [hfin]
    _ = 2 * π ^ 2 * (‖F_L‖ ^ 2 + ‖G‖ ^ 2) := by ring

end UnforcedLeray.Short.PartI
