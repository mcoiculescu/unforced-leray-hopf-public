import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Leaves
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.C
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs

/-!
# High-age raw-lift jet bound with transverse weight (`PartIII-b:C/rep/3/4/1`, helper 3)

Source of record: `the November 2 reference manuscript`, lines 1310-1325,
5225-5235, 5461-5465.

On the late range `1 < s`, `y = chartY R pt` satisfies `y 2 = η / √s` and `ϱ y = R / √s < R`, so
`1 + |η / √s| = 1 + |y 2| ≤ 1 + |Axi.trans R y|`. We upgrade the late-age heat-sum + remainder
Cartesian jet bound of `PartII-a:R07` by one power of `1 + |y 2|` (using `lhBound1D 1 n` on the
Gaussian factor of each `heatField` and `late_heatRem_wtd_jet_poly` at weight `j + 2` with
remainder order `N = K + j + 3`), obtaining
`vJetDens (rawU D.Pl L τ) y ≤ P_ν * (1 + |η / √s|)⁻¹` for `1 < s`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.VBgSq.JetAux

section WeightedLateLift

open UnforcedLeray UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI (meanCoeff heatKernel1)

/-- Weighted `1 + |z|` bound on `B0191.profileDeriv ν n z` from `lhBound1D 1 n` at `s = 1`. -/
theorem wtd_profileDeriv_le_poly (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 0 < c → ∀ z : ℝ,
      (1 + |z|) * ‖iteratedFDeriv ℝ 0 (UnforcedLeray.B0191.profileDeriv ν n) z‖ ≤
        C * (1 + c + ν⁻¹) ^ (n + 1) := by
  obtain ⟨C, hC0, hC⟩ := lhBound1D 1 n
  refine ⟨2 * C, by positivity, fun ν c hν hν1 hc z => ?_⟩
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have h1 := hC ν hν hν1 1 le_rfl z
  simp only [pow_one, div_one, mul_one] at h1
  have heq : UnforcedLeray.B0191.profileDeriv ν n z = iteratedDeriv n (heatKernel1 (ν * 1)) z :=
    lhHeatKernelEq ν n z 1
  rw [heq, mul_one]
  have habs : 1 + |z| ≤ 2 * (1 + z ^ 2) := by
    nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  have hw : (1 + |z|) * |iteratedDeriv n (heatKernel1 ν) z| ≤
      2 * (C * ν ^ (-(((n : ℝ) + 1) / 2))) := by
    calc (1 + |z|) * |iteratedDeriv n (heatKernel1 ν) z|
        ≤ (2 * (1 + z ^ 2)) * |iteratedDeriv n (heatKernel1 ν) z| :=
          mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = 2 * ((1 + z ^ 2) * |iteratedDeriv n (heatKernel1 ν) z|) := by ring
      _ ≤ 2 * (C * ν ^ (-(((n : ℝ) + 1) / 2))) :=
          mul_le_mul_of_nonneg_left h1 zero_le_two
  have hν_inv : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hrpow : ν ^ (-(((n : ℝ) + 1) / 2)) ≤ (1 + c + ν⁻¹) ^ (n + 1) := by
    have h_eq : ν ^ (-(((n : ℝ) + 1) / 2)) = (ν⁻¹) ^ (((n : ℝ) + 1) / 2) := by
      rw [Real.inv_rpow hν.le, Real.rpow_neg hν.le]
    rw [h_eq]
    have h_exp : ((n : ℝ) + 1) / 2 ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (ν⁻¹) ^ (((n : ℝ) + 1) / 2)
        ≤ (ν⁻¹) ^ ((n + 1 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hν_inv h_exp
      _ = (ν⁻¹) ^ (n + 1) := Real.rpow_natCast _ _
      _ ≤ (1 + c + ν⁻¹) ^ (n + 1) := pow_le_pow_left₀ (by positivity) (by linarith) (n + 1)
  calc (1 + |z|) * |iteratedDeriv n (heatKernel1 ν) z|
      ≤ 2 * (C * ν ^ (-(((n : ℝ) + 1) / 2))) := hw
    _ ≤ 2 * (C * (1 + c + ν⁻¹) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hC0) zero_le_two
    _ = 2 * C * (1 + c + ν⁻¹) ^ (n + 1) := by ring

/-- Weighted `1 + |z|` bound on the `k`-th derivative of `B0191.profileDeriv ν m`. -/
theorem wtd_iter_profileDeriv_le_poly (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν c : ℝ), 0 < ν → ν ≤ 1 → 0 < c → ∀ z : ℝ,
      (1 + |z|) * ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤
        C * (1 + c + ν⁻¹) ^ (m + k + 1) := by
  obtain ⟨C, hC0, hC⟩ := wtd_profileDeriv_le_poly (m + k)
  refine ⟨C, hC0, fun ν c hν hν1 hc z => ?_⟩
  have h0 := hC ν c hν hν1 hc z
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m]
  exact h0

/-- `R`-uniform and `(ν, c)`-polynomial `(1 + |y 2|)`-weighted Cartesian jet bound for
`heatField ν R j` on `Axi.ϱ y ^ 2 ≤ R ^ 2` for `1 ≤ R`. -/
theorem heatField_wtd_jet_le_unif (j k : ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
      ∀ (ν c R : ℝ), 0 < ν → ν ≤ 1 → 0 < c → 1 ≤ R →
        ∀ y : Space, Axi.ϱ y ^ 2 ≤ R ^ 2 →
          (1 + |y 2|) * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖ ≤ polyConst C d ν c := by
  have c0 : ContDiff ℝ ∞ (fun y : Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : Space => y 1) := by fun_prop
  have cw : ContDiff ℝ ∞ (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have cwj : ContDiff ℝ ∞ (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) := cw.pow j
  have h0 : HeatJetBdd 1 (fun y : Space => y 0) :=
    hfjCoord (W := 1) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd 1 (fun y : Space => y 1) :=
    hfjCoord (W := 1) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hw : HeatJetBdd 1 (fun y : Space => y 0 ^ 2 + y 1 ^ 2) :=
    hfjAdd (c0.pow 2) (c1.pow 2) (hfjPow c0 h0 2) (hfjPow c1 h1 2)
  have hPj : HeatJetBdd 1 (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ j) := hfjPow cw hw j
  set pA0 : Space → ℝ := fun z => -((z 0 ^ 2 + z 1 ^ 2) ^ j * z 0)
  set pA1 : Space → ℝ := fun z => -((z 0 ^ 2 + z 1 ^ 2) ^ j * z 1)
  set pB : Space → ℝ := fun z => (2 * (j : ℝ) + 2) * (z 0 ^ 2 + z 1 ^ 2) ^ j
  have cpA0 : ContDiff ℝ ∞ pA0 := (cwj.mul c0).neg
  have cpA1 : ContDiff ℝ ∞ pA1 := (cwj.mul c1).neg
  have cpB : ContDiff ℝ ∞ pB := contDiff_const.mul cwj
  have hpA0 : HeatJetBdd 1 pA0 := by
    have heq : pA0 = fun z => (-1 : ℝ) * ((z 0 ^ 2 + z 1 ^ 2) ^ j * z 0) := by
      funext z; dsimp [pA0]; ring
    rw [heq]
    exact hfjMul contDiff_const (cwj.mul c0) (hfjConst (-1)) (hfjMul cwj c0 hPj h0)
  have hpA1 : HeatJetBdd 1 pA1 := by
    have heq : pA1 = fun z => (-1 : ℝ) * ((z 0 ^ 2 + z 1 ^ 2) ^ j * z 1) := by
      funext z; dsimp [pA1]; ring
    rw [heq]
    exact hfjMul contDiff_const (cwj.mul c1) (hfjConst (-1)) (hfjMul cwj c1 hPj h1)
  have hpB : HeatJetBdd 1 pB :=
    hfjMul contDiff_const cwj (hfjConst (2 * (j : ℝ) + 2)) hPj
  choose CA0 hCA0_0 hCA0 using fun i => scale_heatJetBdd_one cpA0 hpA0 i
  choose CA1 hCA1_0 hCA1 using fun i => scale_heatJetBdd_one cpA1 hpA1 i
  choose CB hCB_0 hCB using fun i => scale_heatJetBdd_one cpB hpB i
  choose CG1 hCG1_0 hCG1 using fun i => wtd_iter_profileDeriv_le_poly (2 * j + 1) i
  choose CG0 hCG0_0 hCG0 using fun i => wtd_iter_profileDeriv_le_poly (2 * j) i
  set P2 : Space →L[ℝ] ℝ := EuclideanSpace.proj 2
  have hP2_norm : ‖P2‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul]
    exact PiLp.norm_apply_le y 2
  set d : ℕ := 2 * j + 1 + k + 1
  set K0 : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CA0 i * CG1 (k - i)
  set K1 : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CA1 i * CG1 (k - i)
  set K2 : ℝ := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * CB i * CG0 (k - i)
  have hK0_nn : 0 ≤ K0 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA0_0 i)) (hCG1_0 _)
  have hK1_nn : 0 ≤ K1 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA1_0 i)) (hCG1_0 _)
  have hK2_nn : 0 ≤ K2 := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCB_0 i)) (hCG0_0 _)
  set L0 : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 0)
  set L1 : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 1)
  set L2 : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight Axi.e3
  refine ⟨‖L0‖ * K0 + (‖L1‖ * K1 + ‖L2‖ * K2), d, by positivity,
    fun ν c R hν hν1 hc hR y hy => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRinv : |R⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 hR0)]
    exact inv_le_one_of_one_le₀ hR
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  have hw0 : 0 ≤ 1 + |y 2| := by positivity
  have hG_comp : ∀ (m i : ℕ) (CG : ℕ → ℝ),
      (∀ i', ∀ z : ℝ, (1 + |z|) * ‖iteratedFDeriv ℝ i' (UnforcedLeray.B0191.profileDeriv ν m) z‖ ≤
        CG i' * (1 + c + ν⁻¹) ^ (m + i' + 1)) →
      (∀ i', 0 ≤ CG i') →
      i ≤ k → m ≤ 2 * j + 1 →
      (1 + |y 2|) *
        ‖iteratedFDeriv ℝ i (fun z : Space => UnforcedLeray.B0191.profileDeriv ν m (z 2)) y‖ ≤
        CG i * (1 + c + ν⁻¹) ^ d := by
    intro m i CG hCG_bd hCG_nn hik hm
    have hg_sm : ContDiff ℝ ∞ (UnforcedLeray.B0191.profileDeriv ν m) :=
      IIb.contDiff_profileDeriv ν m
    have hfun_g : (fun z : Space => UnforcedLeray.B0191.profileDeriv ν m (z 2)) =
        UnforcedLeray.B0191.profileDeriv ν m ∘ P2 := rfl
    have hcomp_le :
        ‖iteratedFDeriv ℝ i (fun z : Space => UnforcedLeray.B0191.profileDeriv ν m (z 2)) y‖ ≤
          ‖iteratedFDeriv ℝ i (UnforcedLeray.B0191.profileDeriv ν m) (y 2)‖ := by
      rw [hfun_g, P2.iteratedFDeriv_comp_right hg_sm y (by exact_mod_cast le_top)]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hpow1 : ‖P2‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hP2_norm
      have hP2y : P2 y = y 2 := rfl
      rw [hP2y]
      exact (mul_le_mul_of_nonneg_left hpow1 (norm_nonneg _)).trans (by rw [mul_one])
    have hpow2 : (1 + c + ν⁻¹) ^ (m + i + 1) ≤ (1 + c + ν⁻¹) ^ d :=
      pow_le_pow_right₀ hX1 (by dsimp [d]; omega)
    calc (1 + |y 2|) *
            ‖iteratedFDeriv ℝ i (fun z : Space => UnforcedLeray.B0191.profileDeriv ν m (z 2)) y‖
        ≤ (1 + |y 2|) * ‖iteratedFDeriv ℝ i (UnforcedLeray.B0191.profileDeriv ν m) (y 2)‖ :=
          mul_le_mul_of_nonneg_left hcomp_le hw0
      _ ≤ CG i * (1 + c + ν⁻¹) ^ (m + i + 1) := hCG_bd i (y 2)
      _ ≤ CG i * (1 + c + ν⁻¹) ^ d := mul_le_mul_of_nonneg_left hpow2 (hCG_nn i)
  have heqA0 : (fun z : Space => hfjA ν R j z * z 0) =
      fun z : Space => pA0 (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2) := by
    funext z; dsimp [hfjA, pA0]; simp only [mul_pow, ← mul_add, ← inv_pow]; ring
  have heqA1 : (fun z : Space => hfjA ν R j z * z 1) =
      fun z : Space => pA1 (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2) := by
    funext z; dsimp [hfjA, pA1]; simp only [mul_pow, ← mul_add, ← inv_pow]; ring
  have heqB : hfjB ν R j =
      fun z : Space => R⁻¹ * (pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) := by
    funext z; dsimp [hfjB, pB]; simp only [mul_pow, ← mul_add, ← inv_pow]; ring
  have c_scale : ContDiff ℝ ∞ (fun z : Space => R⁻¹ • z) := contDiff_const_smul R⁻¹
  have c_pA0_R : ContDiff ℝ ∞ (fun z : Space => pA0 (R⁻¹ • z)) := cpA0.comp c_scale
  have c_pA1_R : ContDiff ℝ ∞ (fun z : Space => pA1 (R⁻¹ • z)) := cpA1.comp c_scale
  have c_pB_R : ContDiff ℝ ∞ (fun z : Space => pB (R⁻¹ • z)) := cpB.comp c_scale
  have c_g1 : ContDiff ℝ ∞ (fun z : Space => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) :=
    (IIb.contDiff_profileDeriv ν (2 * j + 1)).comp (by fun_prop)
  have c_g0 : ContDiff ℝ ∞ (fun z : Space => UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) :=
    (IIb.contDiff_profileDeriv ν (2 * j)).comp (by fun_prop)
  have hbd_A0 : (1 + |y 2|) * ‖iteratedFDeriv ℝ k (fun z : Space => hfjA ν R j z * z 0) y‖ ≤
      K0 * (1 + c + ν⁻¹) ^ d := by
    rw [heqA0]
    refine (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_mul_le c_pA0_R c_g1 y (by exact_mod_cast le_top)) hw0).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hik : k - i ≤ k := Nat.sub_le k i
    have h1 := hCA0 i R hR y hy
    have h2 := hG_comp (2 * j + 1) (k - i) CG1 (fun i' => hCG1 i' ν c hν hν1 hc) hCG1_0 hik le_rfl
    calc (1 + |y 2|) * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pA0 (R⁻¹ • z)) y‖ *
            ‖iteratedFDeriv ℝ (k - i)
              (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) y‖)
        = ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pA0 (R⁻¹ • z)) y‖) *
            ((1 + |y 2|) * ‖iteratedFDeriv ℝ (k - i)
              (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) y‖) := by ring
      _ ≤ ((k.choose i : ℝ) * CA0 i) * (CG1 (k - i) * (1 + c + ν⁻¹) ^ d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hCA0_0 i))
      _ = (k.choose i : ℝ) * CA0 i * CG1 (k - i) * (1 + c + ν⁻¹) ^ d := by ring
  have hbd_A1 : (1 + |y 2|) * ‖iteratedFDeriv ℝ k (fun z : Space => hfjA ν R j z * z 1) y‖ ≤
      K1 * (1 + c + ν⁻¹) ^ d := by
    rw [heqA1]
    refine (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_mul_le c_pA1_R c_g1 y (by exact_mod_cast le_top)) hw0).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hik : k - i ≤ k := Nat.sub_le k i
    have h1 := hCA1 i R hR y hy
    have h2 := hG_comp (2 * j + 1) (k - i) CG1 (fun i' => hCG1 i' ν c hν hν1 hc) hCG1_0 hik le_rfl
    calc (1 + |y 2|) * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pA1 (R⁻¹ • z)) y‖ *
            ‖iteratedFDeriv ℝ (k - i)
              (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) y‖)
        = ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pA1 (R⁻¹ • z)) y‖) *
            ((1 + |y 2|) * ‖iteratedFDeriv ℝ (k - i)
              (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) (z 2)) y‖) := by ring
      _ ≤ ((k.choose i : ℝ) * CA1 i) * (CG1 (k - i) * (1 + c + ν⁻¹) ^ d) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
            (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hCA1_0 i))
      _ = (k.choose i : ℝ) * CA1 i * CG1 (k - i) * (1 + c + ν⁻¹) ^ d := by ring
  have hbd_B : (1 + |y 2|) * ‖iteratedFDeriv ℝ k (hfjB ν R j) y‖ ≤ K2 * (1 + c + ν⁻¹) ^ d := by
    rw [heqB]
    have hsm_prod : ContDiffAt ℝ k
        (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y :=
      ((c_pB_R.mul c_g0).contDiffAt).of_le (by exact_mod_cast le_top)
    have hconst : (fun z : Space => R⁻¹ *
          (pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2))) =
        R⁻¹ • fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2) :=
      rfl
    rw [hconst, iteratedFDeriv_const_smul_apply hsm_prod, norm_smul, Real.norm_eq_abs]
    have hprod : (1 + |y 2|) * ‖iteratedFDeriv ℝ k
        (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖ ≤
        K2 * (1 + c + ν⁻¹) ^ d := by
      refine (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_mul_le c_pB_R c_g0 y (by exact_mod_cast le_top)) hw0).trans ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have hik : k - i ≤ k := Nat.sub_le k i
      have h1 := hCB i R hR y hy
      have h2 := hG_comp (2 * j) (k - i) CG0 (fun i' => hCG0 i' ν c hν hν1 hc) hCG0_0 hik (by omega)
      calc (1 + |y 2|) * ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pB (R⁻¹ • z)) y‖ *
              ‖iteratedFDeriv ℝ (k - i)
                (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖)
          = ((k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => pB (R⁻¹ • z)) y‖) *
              ((1 + |y 2|) * ‖iteratedFDeriv ℝ (k - i)
                (fun z => UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖) := by ring
        _ ≤ ((k.choose i : ℝ) * CB i) * (CG0 (k - i) * (1 + c + ν⁻¹) ^ d) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
              (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hCB_0 i))
        _ = (k.choose i : ℝ) * CB i * CG0 (k - i) * (1 + c + ν⁻¹) ^ d := by ring
    calc (1 + |y 2|) * (|R⁻¹| * ‖iteratedFDeriv ℝ k
            (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖)
        = |R⁻¹| * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k
            (fun z : Space => pB (R⁻¹ • z) * UnforcedLeray.B0191.profileDeriv ν (2 * j) (z 2)) y‖) :=
          by ring
      _ ≤ 1 * (K2 * (1 + c + ν⁻¹) ^ d) := mul_le_mul hRinv hprod (by positivity) zero_le_one
      _ = K2 * (1 + c + ν⁻¹) ^ d := one_mul _
  have cA0 : ContDiff ℝ ∞ (fun z : Space => hfjA ν R j z * z 0) := by
    rw [heqA0]; exact c_pA0_R.mul c_g1
  have cA1 : ContDiff ℝ ∞ (fun z : Space => hfjA ν R j z * z 1) := by
    rw [heqA1]; exact c_pA1_R.mul c_g1
  have cB : ContDiff ℝ ∞ (hfjB ν R j) := by
    rw [heqB]; exact contDiff_const.mul (c_pB_R.mul c_g0)
  have hT0 : (1 + |y 2|) *
      ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y‖ ≤
      ‖L0‖ * (K0 * (1 + c + ν⁻¹) ^ d) := by
    have hfun : (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) =
        L0 ∘ (fun z : Space => hfjA ν R j z * z 0) := rfl
    rw [hfun]
    calc (1 + |y 2|) * ‖iteratedFDeriv ℝ k (L0 ∘ fun z => hfjA ν R j z * z 0) y‖
        ≤ (1 + |y 2|) * (‖L0‖ * ‖iteratedFDeriv ℝ k (fun z => hfjA ν R j z * z 0) y‖) :=
          mul_le_mul_of_nonneg_left
            (L0.norm_iteratedFDeriv_comp_left cA0.contDiffAt (by exact_mod_cast le_top)) hw0
      _ = ‖L0‖ * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k (fun z => hfjA ν R j z * z 0) y‖) := by ring
      _ ≤ ‖L0‖ * (K0 * (1 + c + ν⁻¹) ^ d) := mul_le_mul_of_nonneg_left hbd_A0 (norm_nonneg _)
  have hT1 : (1 + |y 2|) *
      ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y‖ ≤
      ‖L1‖ * (K1 * (1 + c + ν⁻¹) ^ d) := by
    have hfun : (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) =
        L1 ∘ (fun z : Space => hfjA ν R j z * z 1) := rfl
    rw [hfun]
    calc (1 + |y 2|) * ‖iteratedFDeriv ℝ k (L1 ∘ fun z => hfjA ν R j z * z 1) y‖
        ≤ (1 + |y 2|) * (‖L1‖ * ‖iteratedFDeriv ℝ k (fun z => hfjA ν R j z * z 1) y‖) :=
          mul_le_mul_of_nonneg_left
            (L1.norm_iteratedFDeriv_comp_left cA1.contDiffAt (by exact_mod_cast le_top)) hw0
      _ = ‖L1‖ * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k (fun z => hfjA ν R j z * z 1) y‖) := by ring
      _ ≤ ‖L1‖ * (K1 * (1 + c + ν⁻¹) ^ d) := mul_le_mul_of_nonneg_left hbd_A1 (norm_nonneg _)
  have hT2 : (1 + |y 2|) *
      ‖iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y‖ ≤
      ‖L2‖ * (K2 * (1 + c + ν⁻¹) ^ d) := by
    have hfun : (fun z : Space => hfjB ν R j z • Axi.e3) = L2 ∘ hfjB ν R j := rfl
    rw [hfun]
    calc (1 + |y 2|) * ‖iteratedFDeriv ℝ k (L2 ∘ hfjB ν R j) y‖
        ≤ (1 + |y 2|) * (‖L2‖ * ‖iteratedFDeriv ℝ k (hfjB ν R j) y‖) :=
          mul_le_mul_of_nonneg_left
            (L2.norm_iteratedFDeriv_comp_left cB.contDiffAt (by exact_mod_cast le_top)) hw0
      _ = ‖L2‖ * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k (hfjB ν R j) y‖) := by ring
      _ ≤ ‖L2‖ * (K2 * (1 + c + ν⁻¹) ^ d) := mul_le_mul_of_nonneg_left hbd_B (norm_nonneg _)
  have cT0 : ContDiffAt ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y :=
    ((cA0.smul contDiff_const).contDiffAt).of_le (by exact_mod_cast le_top)
  have cT1 : ContDiffAt ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y :=
    ((cA1.smul contDiff_const).contDiffAt).of_le (by exact_mod_cast le_top)
  have cT2 : ContDiffAt ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y :=
    ((cB.smul contDiff_const).contDiffAt).of_le (by exact_mod_cast le_top)
  have hfun : heatField ν R j = fun z : Space =>
      (hfjA ν R j z * z 0) • coordinateVector 0 +
      ((hfjA ν R j z * z 1) • coordinateVector 1 + hfjB ν R j z • Axi.e3) :=
    funext (hfjField ν R j)
  have e1 : iteratedFDeriv ℝ k (heatField ν R j) y =
      iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y +
      iteratedFDeriv ℝ k (fun z : Space =>
        (hfjA ν R j z * z 1) • coordinateVector 1 + hfjB ν R j z • Axi.e3) y := by
    rw [hfun]
    exact iteratedFDeriv_add_apply cT0 (cT1.add cT2)
  have e2 : iteratedFDeriv ℝ k (fun z : Space =>
        (hfjA ν R j z * z 1) • coordinateVector 1 + hfjB ν R j z • Axi.e3) y =
      iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y +
      iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y :=
    iteratedFDeriv_add_apply cT1 cT2
  rw [e1, e2]
  have htri : ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y +
      (iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y +
        iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y)‖ ≤
      ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y‖ +
        (‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y‖ +
          ‖iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y‖) :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  calc (1 + |y 2|) * _
      ≤ (1 + |y 2|) *
          (‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y‖ +
            (‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y‖ +
              ‖iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y‖)) :=
        mul_le_mul_of_nonneg_left htri hw0
    _ = (1 + |y 2|) *
          ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 0) • coordinateVector 0) y‖ +
          ((1 + |y 2|) *
            ‖iteratedFDeriv ℝ k (fun z : Space => (hfjA ν R j z * z 1) • coordinateVector 1) y‖ +
            (1 + |y 2|) *
              ‖iteratedFDeriv ℝ k (fun z : Space => hfjB ν R j z • Axi.e3) y‖) := by ring
    _ ≤ ‖L0‖ * (K0 * (1 + c + ν⁻¹) ^ d) +
          (‖L1‖ * (K1 * (1 + c + ν⁻¹) ^ d) + ‖L2‖ * (K2 * (1 + c + ν⁻¹) ^ d)) :=
        add_le_add hT0 (add_le_add hT1 hT2)
    _ = polyConst (‖L0‖ * K0 + (‖L1‖ * K1 + ‖L2‖ * K2)) d ν c := by
        unfold polyConst; ring

/-- `R`-uniform and `(ν, c)`-polynomial `(1 + |y 2|)`-weighted Cartesian jet bound for
`heatSum ν R (meanCoeff tr) N` on `Axi.ϱ y ^ 2 ≤ R ^ 2` for `1 ≤ R`. -/
theorem heatSum_wtd_jet_le_unif (hCoeff : LateMeanCoeff) {ρ : ℝ} (hρ : 1 / 2 < ρ) (N k : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ R : ℝ, 1 ≤ R → ∀ y : Space, Axi.ϱ y ^ 2 ≤ R ^ 2 →
            (1 + |y 2|) * ‖iteratedFDeriv ℝ k (heatSum ν R (meanCoeff tr) N) y‖ ≤
              polyConst C d ν (ν ^ (-ρ)) := by
  choose Ca da νa hνa hCa using fun j => hCoeff ρ j hρ
  choose Ch dh hCh0 hCh using fun j => heatField_wtd_jet_le_unif j k
  set S : Finset ℕ := Finset.range (N + 1)
  have hS_ne : S.Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  set ν₀ : ℝ := min (S.inf' hS_ne νa) 1
  have hν₀ : 0 < ν₀ := lt_min ((Finset.lt_inf'_iff hS_ne).2 fun j _ => hνa j) one_pos
  set D : ℕ := ∑ j ∈ S, (da j + dh j)
  set C : ℝ := ∑ j ∈ S, max (Ca j) 0 * Ch j
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => mul_nonneg (le_max_right _ _) (hCh0 j)
  refine ⟨ν₀, C, D, hν₀, hC0, fun ν hν hν_le tr htr R hR y hy => ?_⟩
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν (-ρ)
  have hX1 : 1 ≤ 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  have hw0 : 0 ≤ 1 + |y 2| := by positivity
  have hsm : ∀ j ∈ S, ContDiff ℝ k (fun z => meanCoeff tr j • heatField ν R j z) :=
    fun j _ => ((contDiff_heatField ν R j).const_smul (meanCoeff tr j)).of_le
      (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ k (heatSum ν R (meanCoeff tr) N) y =
      ∑ j ∈ S, iteratedFDeriv ℝ k (fun z => meanCoeff tr j • heatField ν R j z) y := by
    have h := iteratedFDeriv_sum (𝕜 := ℝ) (i := k) hsm
    have h' := congrFun h y
    rw [Finset.sum_apply] at h'
    exact h'
  rw [e]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hw0).trans ?_
  unfold polyConst
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [iteratedFDeriv_const_smul_apply'
      (((contDiff_heatField ν R j).contDiffAt (x := y)).of_le (m := (k : WithTop ℕ∞))
        (by exact_mod_cast le_top)),
    norm_smul, Real.norm_eq_abs]
  have hν_j : ν ≤ νa j := (hν_le.trans (min_le_left _ _)).trans (Finset.inf'_le νa hj)
  have ha_j : |meanCoeff tr j| ≤ max (Ca j) 0 * (1 + ν ^ (-ρ) + ν⁻¹) ^ da j :=
    (hCa j ν hν hν_j tr htr).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hh_j : (1 + |y 2|) * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖ ≤
      Ch j * (1 + ν ^ (-ρ) + ν⁻¹) ^ dh j := hCh j ν (ν ^ (-ρ)) R hν hν1 hc hR y hy
  have hd_le : da j + dh j ≤ D :=
    Finset.single_le_sum (f := fun i => da i + dh i) (fun _ _ => Nat.zero_le _) hj
  have hpow : (1 + ν ^ (-ρ) + ν⁻¹) ^ (da j + dh j) ≤ (1 + ν ^ (-ρ) + ν⁻¹) ^ D :=
    pow_le_pow_right₀ hX1 hd_le
  calc (1 + |y 2|) * (|meanCoeff tr j| * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖)
      = |meanCoeff tr j| * ((1 + |y 2|) * ‖iteratedFDeriv ℝ k (heatField ν R j) y‖) := by ring
    _ ≤ (max (Ca j) 0 * (1 + ν ^ (-ρ) + ν⁻¹) ^ da j) *
          (Ch j * (1 + ν ^ (-ρ) + ν⁻¹) ^ dh j) :=
        mul_le_mul ha_j hh_j (by positivity) (by positivity)
    _ = (max (Ca j) 0 * Ch j) * (1 + ν ^ (-ρ) + ν⁻¹) ^ (da j + dh j) := by
        rw [pow_add]; ring
    _ ≤ (max (Ca j) 0 * Ch j) * (1 + ν ^ (-ρ) + ν⁻¹) ^ D :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) (hCh0 j))

/-- On the late region `1 < Axi.age R y` (`0 < ϱ y ≤ R`), `1 + |y 2| ≤ 1 + |Axi.trans R y|`. -/
theorem one_add_abs_y2_le_trans {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ Axi.axis)
    (hfar : 1 < Axi.age R y) :
    1 + |y 2| ≤ 1 + |Axi.trans R y| := by
  have hϱ0 : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hϱ2 : 0 < Axi.ϱ y ^ 2 := pow_pos hϱ0 2
  have h1 : 1 < R ^ 2 / Axi.ϱ y ^ 2 := hfar
  rw [lt_div_iff₀ hϱ2] at h1
  have hϱR : Axi.ϱ y ≤ R := by nlinarith
  have hdiv : 1 ≤ R / Axi.ϱ y := (one_le_div hϱ0).2 hϱR
  have htr : |Axi.trans R y| = (R / Axi.ϱ y) * |y 2| := by
    have heq : Axi.trans R y = (R / Axi.ϱ y) * y 2 := by
      unfold Axi.trans; ring
    rw [heq, abs_mul, abs_of_pos (div_pos hR hϱ0)]
  rw [htr]
  have hy2 : |y 2| ≤ (R / Axi.ϱ y) * |y 2| := le_mul_of_one_le_left (abs_nonneg _) hdiv
  linarith

/-- Late-age (`1 < Axi.age R y`) `(1 + |y 2|)`-weighted Cartesian jet bound for
`simProfile 1 (liftVelocity R ψ) τ`, uniform in `R ≥ 2` and `τ : ℝ`. -/
theorem late_simProfile_wtd_jet_le (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ ψ pr : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ pr →
          ∀ R : ℝ, 2 ≤ R → ∀ (τ : ℝ) (y : Space),
            Axi.ϱ y ≠ 0 → 1 < Axi.age R y →
              (1 + |y 2|) * ‖iteratedFDeriv ℝ j (simProfile 1 (liftVelocity R ψ) τ) y‖ ≤
                polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨Cnv, K, hCnv0, Hnv⟩ := nv_jet_le_unif j
  obtain ⟨_, _, _, HJ⟩ := ringLiftPtJet j
  have hP := ringProfileMeridJet
  set N : ℕ := K + j + 3 with hNdef
  have hexN : ∀ i : ℕ, ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ x : ℝ × (ℝ × ℝ), 1 ≤ x.1 →
            (1 + |x.2.2|) ^ (j + 2) *
              ‖iteratedFDeriv ℝ i
                (heatRemainder ν (meanCoeff tr) N (fun z => tr.ψ z.1 z.2)) x‖ ≤
                polyConst C d ν (ν ^ (-ρ)) * x.1 ^ (((j + 2 : ℕ) : ℝ) / 2 - N - 3 / 2) :=
    fun i => late_heatRem_wtd_jet_poly hFD hME hρ N (j + 2) i
  choose νN CN dN hνN hCN hbdN using hexN
  obtain ⟨νH, CH, dH, hνH, hCH, Hh⟩ :=
    heatSum_wtd_jet_le_unif (lateMeanCoeff_of hFD UnforcedLeray.Short.PartI.trainMeanEquations_proof)
      hρ N j
  set I := Finset.range (j + 2)
  have hSνN : 0 ≤ ∑ i ∈ I, 1 / νN i :=
    Finset.sum_nonneg fun i _ => (one_div_pos.2 (hνN i)).le
  set ν₀N := 1 / (1 + ∑ i ∈ I, 1 / νN i)
  set ν₀ := min νH ν₀N
  have hν₀ : 0 < ν₀ := lt_min hνH (inv_one_add_pos hSνN)
  set sumCN := ∑ i ∈ I, CN i
  set sumdN := ∑ i ∈ I, dN i
  have hsumCN0 : 0 ≤ sumCN := Finset.sum_nonneg fun i _ => hCN i
  set C := CH + Cnv * 2 ^ (K + 1) * sumCN
  set d := max dH sumdN
  refine ⟨ν₀, C, d, hν₀, by positivity, fun ν hν0 hνle ψ pr hpr R hR τ y hy0 hfar => ?_⟩
  obtain ⟨T, hT, hψ, -⟩ := hpr
  subst hψ
  have hc0 : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hνleH : ν ≤ νH := hνle.trans (min_le_left _ _)
  have hνleN : ν ≤ ν₀N := hνle.trans (min_le_right _ _)
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν0 hc0 T hT
  have hmer : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      merProfile R (trainProfile T.ψ) x =
        Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) x := by
    intro x hx
    rw [← rawProfile_eq_merProfile_of_smooth UnforcedLeray.Short.PartI.trainStreamSmooth
      hν0 hc0 T hT (R := R) rfl hx]
    exact rawStreamProfile ν _ R T hR0 hΨ x hx
  have hy : y ∉ Axi.axis := varrho_ne_zero_iff.1 hy0
  have hevU : simProfile 1 (liftVelocity R (trainProfile T.ψ)) τ =ᶠ[𝓝 y]
      Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    rw [simProfile_liftVelocity_eq_Nv hR0 _ τ hz]
    simp only [Axi.Nv]
    rw [hmer (Axi.chart R τ z) (age_pos_of hR0 hz)]
  rw [(hevU.iteratedFDeriv ℝ j).eq_of_nhds]
  have hs : 0 < Axi.age R y := zero_lt_one.trans hfar
  have hs1 : 1 ≤ Axi.age R y := hfar.le
  have hϱ : Axi.ϱ y ^ 2 ≤ R ^ 2 := by
    have hϱ0 : 0 < Axi.ϱ y ^ 2 := pow_pos (Axi.ϱ_pos hy) 2
    have h1 : 1 < R ^ 2 / Axi.ϱ y ^ 2 := hfar
    rw [lt_div_iff₀ hϱ0] at h1
    linarith
  have hΦN : ContDiffOn ℝ ∞ (heatRemainder ν (meanCoeff T) N
      (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    hΨ.sub (ContDiffOn.sum fun l _ => contDiffOn_const.mul (heatTermSmooth ν hν0 l))
  have hBNs := (hP R _ hΦN).1
  have hev : Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ
      =ᶠ[𝓝 y] heatSum ν R (meanCoeff T) N +
        Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
          (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    exact Nv_heat_decomp hν0 hR0 _ N hΨ τ hz
  have hNvc : ContDiffAt ℝ j (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
      (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y :=
    (((HJ R τ _ hR1 hBNs).1).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le
      (by exact_mod_cast le_top)
  have hHc : ContDiffAt ℝ j (heatSum ν R (meanCoeff T) N) y :=
    (contDiff_heatSum ν R _ N).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_add_apply hHc hNvc]
  have hw0 : 0 ≤ 1 + |y 2| := by positivity
  have h1 := Hh ν hν0 hνleH T hT R hR1 y hϱ
  have h2 := Hnv R _ hR1 hΦN τ y hy
  have htr_le := one_add_abs_y2_le_trans hR0 hy hfar
  have hrpow0 : 0 ≤ Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - N - 3 / 2) :=
    Real.rpow_nonneg hs.le _
  have htermN : ∀ i ∈ I,
      (1 + |Axi.trans R y|) ^ (j + 2) *
        ‖iteratedFDeriv ℝ i (heatRemainder ν (meanCoeff T) N
          (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖ ≤
        polyConst (CN i) sumdN ν (ν ^ (-ρ)) *
          Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - N - 3 / 2) := by
    intro i hi
    have hν_i : ν ≤ νN i :=
      hνleN.trans (inv_one_add_le (hνN i)
        (Finset.single_le_sum (f := fun i => 1 / νN i)
          (fun i _ => (one_div_pos.2 (hνN i)).le) hi))
    have hd_i : dN i ≤ sumdN :=
      Finset.single_le_sum (f := dN) (fun _ _ => Nat.zero_le _) hi
    exact (hbdN i ν hν0 hν_i T hT (Axi.chart R τ y) hs1).trans
      (mul_le_mul_of_nonneg_right (polyConst_mono hν0 hc0 le_rfl (hCN i) hd_i) hrpow0)
  have hw : (1 + |Axi.trans R y|) ^ (j + 2) * ∑ i ∈ I,
      ‖iteratedFDeriv ℝ i (heatRemainder ν (meanCoeff T) N
        (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖ ≤
      polyConst sumCN sumdN ν (ν ^ (-ρ)) *
        Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - N - 3 / 2) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum htermN).trans (le_of_eq ?_)
    dsimp [sumCN]
    unfold polyConst
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have he : ((j + 2 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2 ≤ -((K + 1 : ℕ) : ℝ) := by
    rw [hNdef]; push_cast; linarith
  have hpow : (1 + Axi.age R y) ^ (K + 1) *
      Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) ≤ 2 ^ (K + 1) := by
    have h2s : (1 + Axi.age R y) ^ (K + 1) ≤ 2 ^ (K + 1) * Axi.age R y ^ (K + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hle1 : Axi.age R y ^ (K + 1) *
        Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) ≤ 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs]
      exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by push_cast at he ⊢; linarith)
    calc (1 + Axi.age R y) ^ (K + 1) *
            Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)
        ≤ 2 ^ (K + 1) * Axi.age R y ^ (K + 1) *
            Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) :=
          mul_le_mul_of_nonneg_right h2s hrpow0
      _ = 2 ^ (K + 1) * (Axi.age R y ^ (K + 1) *
            Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)) := by ring
      _ ≤ 2 ^ (K + 1) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = 2 ^ (K + 1) := mul_one _
  have hCnvA : 0 ≤ Cnv * (1 + Axi.age R y) ^ (K + 1) :=
    mul_nonneg hCnv0 (pow_nonneg (by linarith) _)
  have hPCN0 : 0 ≤ polyConst sumCN sumdN ν (ν ^ (-ρ)) :=
    polyConst_nonneg_of hsumCN0 sumdN hν0 hc0
  have hrem : (1 + |y 2|) * ‖iteratedFDeriv ℝ j
      (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
        (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖ ≤
      polyConst (Cnv * 2 ^ (K + 1) * sumCN) sumdN ν (ν ^ (-ρ)) := by
    calc (1 + |y 2|) * ‖iteratedFDeriv ℝ j
            (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
              (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖
        ≤ (1 + |Axi.trans R y|) *
            (Cnv * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (j + 1) *
              ∑ i ∈ I, ‖iteratedFDeriv ℝ i
                (heatRemainder ν (meanCoeff T) N
                  (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖)) :=
          mul_le_mul htr_le h2 (norm_nonneg _) (by positivity)
      _ = Cnv * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (j + 2) *
            ∑ i ∈ I, ‖iteratedFDeriv ℝ i
              (heatRemainder ν (meanCoeff T) N
                (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖) := by
          rw [pow_succ]; ring
      _ ≤ Cnv * (1 + Axi.age R y) ^ (K + 1) *
            (polyConst sumCN sumdN ν (ν ^ (-ρ)) *
              Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - N - 3 / 2)) :=
          mul_le_mul_of_nonneg_left hw hCnvA
      _ = Cnv * polyConst sumCN sumdN ν (ν ^ (-ρ)) *
            ((1 + Axi.age R y) ^ (K + 1) *
              Axi.age R y ^ (((j + 2 : ℕ) : ℝ) / 2 - N - 3 / 2)) := by ring
      _ ≤ Cnv * polyConst sumCN sumdN ν (ν ^ (-ρ)) * 2 ^ (K + 1) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hCnv0 hPCN0)
      _ = polyConst (Cnv * 2 ^ (K + 1) * sumCN) sumdN ν (ν ^ (-ρ)) := by
          unfold polyConst; ring
  calc (1 + |y 2|) * ‖iteratedFDeriv ℝ j (heatSum ν R (meanCoeff T) N) y +
          iteratedFDeriv ℝ j (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
            (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖
      ≤ (1 + |y 2|) * (‖iteratedFDeriv ℝ j (heatSum ν R (meanCoeff T) N) y‖ +
          ‖iteratedFDeriv ℝ j (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
            (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw0
    _ = (1 + |y 2|) * ‖iteratedFDeriv ℝ j (heatSum ν R (meanCoeff T) N) y‖ +
          (1 + |y 2|) * ‖iteratedFDeriv ℝ j
            (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν (meanCoeff T) N
              (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖ := by ring
    _ ≤ polyConst CH dH ν (ν ^ (-ρ)) +
          polyConst (Cnv * 2 ^ (K + 1) * sumCN) sumdN ν (ν ^ (-ρ)) := add_le_add h1 hrem
    _ ≤ polyConst C d ν (ν ^ (-ρ)) := polyConst_add_le hCH (by positivity) dH sumdN hν0 hc0

/-- Bound `polyConst C d ν (ν ^ (-2)) ≤ C * 3 ^ d * ν⁻¹ ^ (2 * d)` for `0 < ν ≤ 1`. -/
theorem polyConst_two_le_pnu {C : ℝ} (hC : 0 ≤ C) (d : ℕ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    polyConst C d ν (ν ^ (-(2 : ℝ))) ≤ C * 3 ^ d * ν⁻¹ ^ (2 * d) := by
  have hνinv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hrpow : ν ^ (-(2 : ℝ)) = ν⁻¹ ^ 2 := by
    have h2 : (-(2 : ℝ)) = -((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
  have hbase : 1 + ν ^ (-(2 : ℝ)) + ν⁻¹ ≤ 3 * ν⁻¹ ^ 2 := by
    rw [hrpow]
    have hsq : ν⁻¹ ≤ ν⁻¹ ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by positivity) hνinv1
    linarith
  unfold polyConst
  calc C * (1 + ν ^ (-(2 : ℝ)) + ν⁻¹) ^ d
      ≤ C * (3 * ν⁻¹ ^ 2) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase d) hC
    _ = C * 3 ^ d * ν⁻¹ ^ (2 * d) := by rw [mul_pow, ← pow_mul]; ring

end WeightedLateLift

private lemma slice_offAxis_raw {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × Space → F) (h : ContDiffOn ℝ 2 f offAxis) (τ : ℝ) :
    ContDiffOn ℝ 2 (fun w : Space => f (τ, w)) UnforcedLeray.Axi.axisᶜ :=
  h.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hw => hw

/-- Pointwise bound on `vJetDens U y` off the axis in terms of Cartesian `iteratedFDeriv`s. -/
theorem vJetDens_le_iteratedFDeriv {U : Space → Space} {y : Space}
    (hy : y ∉ UnforcedLeray.Axi.axis) (hU : ContDiffOn ℝ 2 U UnforcedLeray.Axi.axisᶜ) :
    vJetDens U y ≤ 3 * ‖iteratedFDeriv ℝ 1 U y‖ + 9 * ‖iteratedFDeriv ℝ 2 U y‖ := by
  have hU1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ U x) UnforcedLeray.Axi.axisᶜ :=
    hU.fderiv_of_isOpen UnforcedLeray.Axi.isOpen_compl_axis (by norm_num)
  have hUd1 : DifferentiableAt ℝ (fun x => fderiv ℝ U x) y :=
    (hU1.contDiffAt (UnforcedLeray.Axi.isOpen_compl_axis.mem_nhds hy)).differentiableAt (by norm_num)
  have h1 : ∀ j : Fin 3, ‖physPd U j y‖ ≤ ‖iteratedFDeriv ℝ 1 U y‖ := by
    intro j
    have h := (fderiv ℝ U y).le_opNorm (coordinateVector j)
    rw [norm_coordinateVector_sj, mul_one, ← norm_iteratedFDeriv_one (𝕜 := ℝ)] at h
    exact h
  have h2 : ∀ j l : Fin 3, ‖physPd2 U j l y‖ ≤ ‖iteratedFDeriv ℝ 2 U y‖ := by
    intro j l
    refine (norm_physPd2_le_secondJet U y j l).trans (le_of_eq ?_)
    rw [secondJet_eq_fderiv hUd1, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := U) (x := y) (n := 1)
  unfold vJetDens
  simp only [Fin.sum_univ_three]
  linarith [h1 0, h1 1, h1 2, h2 0 0, h2 0 1, h2 0 2,
    h2 1 0, h2 1 1, h2 1 2, h2 2 0, h2 2 1, h2 2 2]

/-- **Sequence-level high-age (`1 < s`) bound on `vJetDens (rawU D.Pl L τ) y`.** -/
theorem vJetDens_rawU_late_eventually (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ pt : Chart, 1 < pt.1 →
      vJetDens (rawU D.Pl (D.level n) (NearInst.chartTau (D.level n).ε⁻¹ pt))
          (NearInst.chartY (D.level n).ε⁻¹ pt) ≤
        C * (D.level n).ν⁻¹ ^ k * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFluct hOv
  have hME : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
    UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hρ2 : (1 / 2 : ℝ) < (2 : ℝ) := by norm_num
  obtain ⟨ν₁, C₁, d₁, hν₁, hC₁, H₁⟩ := late_simProfile_wtd_jet_le hFD hME hρ2 1
  obtain ⟨ν₂, C₂, d₂, hν₂, hC₂, H₂⟩ := late_simProfile_wtd_jet_le hFD hME hρ2 2
  set ν_lim : ℝ := min dm (min 1 (min ν₁ ν₂))
  have hν_lim : 0 < ν_lim := lt_min hst.dm_pos (lt_min one_pos (lt_min hν₁ hν₂))
  have hν_ev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν_lim :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν_lim)
  set A₁ : ℝ := C₁ * 3 ^ d₁
  set A₂ : ℝ := C₂ * 3 ^ d₂
  set C : ℝ := 3 * A₁ + 9 * A₂
  set k : ℕ := max (2 * d₁) (2 * d₂)
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨C, k, by positivity, ?_⟩
  filter_upwards [hst.actual, hν_ev] with n hn hν_lt pt hp1
  set L := D.level n
  set p := L.params D.Pl
  have hp0 : 0 < pt.1 := zero_lt_one.trans hp1
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hpν : p.ν = L.ν := rfl
  have hpR : p.R = L.ε⁻¹ := rfl
  have hν_dm : L.ν ≤ dm := hν_lt.le.trans (min_le_left _ _)
  have hν1 : L.ν ≤ 1 := hν_lt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_le1 : L.ν ≤ ν₁ :=
    hν_lt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_le2 : L.ν ≤ ν₂ :=
    hν_lt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hR2 : 2 ≤ p.R := R_ge_two hn.regime (hpν ▸ hν_dm)
  set τ := NearInst.chartTau L.ε⁻¹ pt
  set y := NearInst.chartY L.ε⁻¹ pt
  have hy_ax : y ∉ UnforcedLeray.Axi.axis := by
    intro h
    have hy0 : y 0 = L.ε⁻¹ / Real.sqrt pt.1 := by simp [y, NearInst.chartY]
    have hpos : 0 < L.ε⁻¹ / Real.sqrt pt.1 := div_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hp0)
    rw [← hy0, h.1] at hpos
    exact lt_irrefl _ hpos
  have hy_ϱ : UnforcedLeray.Axi.ϱ y ≠ 0 := varrho_ne_zero_iff.2 hy_ax
  have hch : UnforcedLeray.Axi.chart L.ε⁻¹ τ y = pt := chartId L.ε⁻¹ pt (inv_pos.2 hε) hp0
  have hage : UnforcedLeray.Axi.age p.R y = pt.1 := by
    rw [hpR]; exact congrArg Prod.fst hch
  have hfar : 1 < UnforcedLeray.Axi.age p.R y := by rw [hage]; exact hp1
  have hy2 : y 2 = pt.2.2 / Real.sqrt pt.1 := by simp [y, NearInst.chartY]
  have hraw_c2 : ContDiffOn ℝ 2 (p.raw τ) UnforcedLeray.Axi.axisᶜ := by
    have hR := rawU_contDiffOn_offAxis_of p hε (L.train_stream_smooth.of_le (by norm_num))
    exact slice_offAxis_raw (fun x : ℝ × Space => p.raw x.1 x.2) hR τ
  have hev_raw : p.raw τ =ᶠ[𝓝 y]
      UnforcedLeray.B0190.simProfile 1
        (UnforcedLeray.B0185.liftVelocity p.R (UnforcedLeray.Short.IIb.trainStream p)) τ := by
    filter_upwards [UnforcedLeray.Axi.isOpen_compl_axis.mem_nhds hy_ax] with z hz
    exact UnforcedLeray.Short.IIb.rawIsRingLift_proof p hn.regime.train_buc τ z
      (varrho_ne_zero_iff.2 hz)
  have hex_tr := UnforcedLeray.Short.IIb.isExactPlanarTrain_params_rpow p hn.regime.train_buc
    hn.regime.c_eq
  have hb1 : (1 + |y 2|) * ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ ≤ A₁ * L.ν⁻¹ ^ k := by
    rw [(hev_raw.iteratedFDeriv ℝ 1).eq_of_nhds]
    have h := H₁ p.ν (hpν ▸ hν) (hpν ▸ hν_le1) _ _ hex_tr p.R hR2 τ y hy_ϱ hfar
    have hp := polyConst_two_le_pnu hC₁ d₁ (hpν ▸ hν) (hpν ▸ hν1)
    rw [hpν] at h hp
    have hk1 : L.ν⁻¹ ^ (2 * d₁) ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_left _ _)
    exact (h.trans hp).trans (mul_le_mul_of_nonneg_left hk1 hA₁0)
  have hb2 : (1 + |y 2|) * ‖iteratedFDeriv ℝ 2 (p.raw τ) y‖ ≤ A₂ * L.ν⁻¹ ^ k := by
    rw [(hev_raw.iteratedFDeriv ℝ 2).eq_of_nhds]
    have h := H₂ p.ν (hpν ▸ hν) (hpν ▸ hν_le2) _ _ hex_tr p.R hR2 τ y hy_ϱ hfar
    have hp := polyConst_two_le_pnu hC₂ d₂ (hpν ▸ hν) (hpν ▸ hν1)
    rw [hpν] at h hp
    have hk2 : L.ν⁻¹ ^ (2 * d₂) ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_right _ _)
    exact (h.trans hp).trans (mul_le_mul_of_nonneg_left hk2 hA₂0)
  have hw_pos : 0 < 1 + |y 2| := by positivity
  have hjet := vJetDens_le_iteratedFDeriv hy_ax hraw_c2
  have hw_jet : (1 + |y 2|) * vJetDens (p.raw τ) y ≤ C * L.ν⁻¹ ^ k := by
    calc (1 + |y 2|) * vJetDens (p.raw τ) y
        ≤ (1 + |y 2|) * (3 * ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ +
            9 * ‖iteratedFDeriv ℝ 2 (p.raw τ) y‖) :=
          mul_le_mul_of_nonneg_left hjet hw_pos.le
      _ = 3 * ((1 + |y 2|) * ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖) +
            9 * ((1 + |y 2|) * ‖iteratedFDeriv ℝ 2 (p.raw τ) y‖) := by ring
      _ ≤ 3 * (A₁ * L.ν⁻¹ ^ k) + 9 * (A₂ * L.ν⁻¹ ^ k) := by linarith
      _ = C * L.ν⁻¹ ^ k := by simp only [C]; ring
  have hraw_eq : vJetDens (rawU D.Pl L τ) y = vJetDens (p.raw τ) y := rfl
  rw [hraw_eq, ← hy2, ← div_eq_mul_inv]
  exact (le_div_iff₀' hw_pos).2 hw_jet

end UnforcedLeray.Short.PartIIIb.Concrete.VBgSq.JetAux

end
