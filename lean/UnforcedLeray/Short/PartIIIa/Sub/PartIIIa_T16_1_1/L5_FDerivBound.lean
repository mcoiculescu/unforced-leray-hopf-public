import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L1_Smooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L4_FDerivApplyShift

/-!
# `PartIII-a:T16/1/1/5` : `SepDiffFDerivBound` (`sep:kernel` for the integrand)

Source `the November 2 reference manuscript` lines 3604-3617 (`sep:kernel` at
`x = y - λz`, `t = ν(1-λ²)`).  Given `SepKernelBounds`, for `ν > 0`, `λ ∈ (0,1)`, `y - λz ≠ 0`,
the component `i` of the integrand is
`-2 λ^{2μ+2} ∑_{j,k} ∂_k K_{t,ij}(y' - λz) T_{jk}`, `t = ν(1-λ²)`.  Its `n`-th `y'`-derivative is
bounded termwise by `|λ^{2μ+2}| |T_{jk}| |D^{n+1}K_t(y - λz)|` (`fDerivApplyShiftBound`), and
`|D^{n+1}K_t(x)| ≤ CK |x|^{-4-n}` (`SepKernelBounds`, `t > 0`).  The nine terms give the constant
`C = 18 max(CK, 0)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `|M_{jk}| ≤ ‖M‖_F` for the Frobenius norm `tensorNorm`. -/
theorem l5_abs_le_tensorNorm (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ tensorNorm M := by
  unfold tensorNorm
  have h1 : M j k ^ 2 ≤ ∑ i, ∑ j', M i j' ^ 2 := by
    calc M j k ^ 2 ≤ ∑ j', M j j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => M j j' ^ 2)
            (fun j' _ => sq_nonneg _) (Finset.mem_univ k)
      _ ≤ ∑ i, ∑ j', M i j' ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j', M i j' ^ 2)
            (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  calc |M j k| = Real.sqrt (M j k ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, ∑ j', M i j' ^ 2) := Real.sqrt_le_sqrt h1

/-- The modulus of the complex prefactor `-2 λ^{2μ+2}` is `2 λ^{2 Re μ + 2}` for `λ > 0`. -/
theorem l5_coef_norm (l : ℝ) (hl : 0 < l) (μ : ℂ) :
    ‖-2 * ((l : ℂ) ^ (2 * μ + 2))‖ = 2 * l ^ (2 * μ.re + 2) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl]
  have hre : (2 * μ + 2 : ℂ).re = 2 * μ.re + 2 := by simp
  rw [hre]
  norm_num

/-- **`PartIII-a:T16/1/1/5`**: `sep:kernel` for the integrand, with a constant `C_n` independent of
`(ν, μ, T, τ, λ, z, y, i)`. -/
theorem sepDiffFDerivBound : UnforcedLeray.Short.IIIa.SepDiffFDerivBound := by
  intro hK n
  obtain ⟨CK, hCK⟩ := hK n
  refine ⟨18 * max CK 0, mul_nonneg (by norm_num) (le_max_right _ _), ?_⟩
  intro ν μ T τ hν l z y hl hx i
  have hl0 : 0 < l := hl.1
  have hl1 : l < 1 := hl.2
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl0, hl1])
  have hCMK : CK ≤ max CK 0 := le_max_left _ _
  have hCM0 : 0 ≤ max CK 0 := le_max_right _ _
  have hN0 : 0 ≤ ‖y - l • z‖ ^ (-4 - (n : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hP0 : 0 ≤ l ^ (2 * μ.re + 2) := Real.rpow_nonneg hl0.le _
  let c : Fin 3 → Fin 3 → ℂ := fun j k =>
    -2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ)
  let G : Fin 3 → Fin 3 → Space → ℂ := fun j k y' =>
    ((fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) (y' - l • z)
      (coordinateVector k) : ℝ) : ℂ)
  have hF : (fun y' => sepDiffF ν μ T τ (l, z) y' i)
      = fun y' => ∑ j : Fin 3, ∑ k : Fin 3, c j k • G j k y' := by
    funext y'
    simp only [sepDiffF, c, G, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hGc : ∀ j k : Fin 3, ContDiff ℝ n (G j k) := by
    intro j k
    have hKs : ContDiff ℝ ∞ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x) :=
      heatLerayKSmoothAll _ ht i j
    have hd : ContDiff ℝ ∞ (fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)) :=
      (contDiff_infty_iff_fderiv.1 hKs).2
    have hinf : ContDiff ℝ ∞ (G j k) :=
      Complex.ofRealCLM.contDiff.comp
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector k)).contDiff.comp
          (hd.comp (contDiff_id.sub contDiff_const)))
    exact hinf.of_le (by exact_mod_cast le_top)
  have hkC : ∀ j k : Fin 3, ContDiff ℝ n (fun y' : Space => c j k • G j k y') :=
    fun j k => (hGc j k).const_smul _
  have hj : ∀ j : Fin 3,
      ContDiffAt ℝ n (fun y' : Space => ∑ k : Fin 3, c j k • G j k y') y :=
    fun j => (ContDiff.sum fun k _ => hkC j k).contDiffAt
  have hterm : ∀ j k : Fin 3, ‖iteratedFDeriv ℝ n (fun y' : Space => c j k • G j k y') y‖
      ≤ 2 * (l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-4 - (n : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log l) z) * max CK 0) := by
    intro j k
    rw [iteratedFDeriv_const_smul_apply' ((hGc j k).contDiffAt), norm_smul]
    have hshift : ‖iteratedFDeriv ℝ n (G j k) y‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z)‖ * ‖coordinateVector k‖ :=
      fDerivApplyShiftBound (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
        (heatLerayKSmoothAll _ ht i j) n (coordinateVector k) (l • z) y
    have hcv : ‖coordinateVector k‖ = 1 := by
      simp [coordinateVector]
    have hbound : ‖iteratedFDeriv ℝ (n + 1) (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y - l • z)‖ ≤ max CK 0 * ‖y - l • z‖ ^ (-4 - (n : ℝ)) :=
      ((hCK (y - l • z) hx i j).1 (ν * (1 - l ^ 2)) ht).trans
        (mul_le_mul_of_nonneg_right hCMK hN0)
    have hK' : ‖iteratedFDeriv ℝ n (G j k) y‖ ≤ max CK 0 * ‖y - l • z‖ ^ (-4 - (n : ℝ)) := by
      rw [hcv, mul_one] at hshift
      exact hshift.trans hbound
    have hc : ‖c j k‖ = 2 * l ^ (2 * μ.re + 2) * |T (τ + 2 * Real.log l) z j k| := by
      simp only [c]
      rw [norm_mul, l5_coef_norm l hl0 μ, Complex.norm_real, Real.norm_eq_abs]
    calc ‖c j k‖ * ‖iteratedFDeriv ℝ n (G j k) y‖
        ≤ (2 * l ^ (2 * μ.re + 2) * |T (τ + 2 * Real.log l) z j k|) *
            (max CK 0 * ‖y - l • z‖ ^ (-4 - (n : ℝ))) := by
          rw [hc]
          exact mul_le_mul_of_nonneg_left hK'
            (mul_nonneg (mul_nonneg (by norm_num) hP0) (abs_nonneg _))
      _ ≤ (2 * l ^ (2 * μ.re + 2) * tensorNorm (T (τ + 2 * Real.log l) z)) *
            (max CK 0 * ‖y - l • z‖ ^ (-4 - (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hCM0 hN0)
          exact mul_le_mul_of_nonneg_left (l5_abs_le_tensorNorm _ j k)
            (mul_nonneg (by norm_num) hP0)
      _ = 2 * (l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-4 - (n : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log l) z) * max CK 0) := by ring
  rw [hF, iteratedFDeriv_fun_sum_apply (fun j _ => hj j)]
  refine (norm_sum_le _ _).trans ?_
  have hj_bound : ∀ j : Fin 3,
      ‖iteratedFDeriv ℝ n (fun y' : Space => ∑ k : Fin 3, c j k • G j k y') y‖
        ≤ ∑ k : Fin 3, 2 * (l ^ (2 * μ.re + 2) * ‖y - l • z‖ ^ (-4 - (n : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log l) z) * max CK 0) := by
    intro j
    rw [iteratedFDeriv_fun_sum_apply (fun k _ => (hkC j k).contDiffAt)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm j k)
  refine (Finset.sum_le_sum fun j _ => hj_bound j).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  push_cast
  ring

end UnforcedLeray.Short.IIIa
