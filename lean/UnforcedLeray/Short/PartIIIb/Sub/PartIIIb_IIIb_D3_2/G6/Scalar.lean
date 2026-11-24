import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org
import UnforcedLeray.Short.PartIIIb.Concrete.FlatScalar

/-!
# `PartIII-b:IIIb-D3/2/G6/2`: the window-uniform scalar estimate `ScalarWindow`

Source of record: `the November 2 reference manuscript`, lines 4628-4632 and
proof lines 4662-4684.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

open ConcreteYF

/-- `PartIII-b:IIIb-D3/2/G6/2`: window-uniform scalar estimate. -/
theorem scalarWindow : FlatUnif.G6.ScalarWindow := by
  intro S ν μ lam κ ell J a lo hi Cj hlo hνpos hce hwin hJ hAmp hOld hEarly hInt γ' hγ0 hγl
  obtain ⟨C1, N1, hA⟩ := hAmp
  obtain ⟨ω, C2, N2, hωT, hO⟩ := hOld
  obtain ⟨C3, k, N3, hE⟩ := hEarly γ' hγ0 hγl
  obtain ⟨N4, hN4⟩ := eventually_atTop.1 (hce.and (hwin.and hInt))
  refine ⟨fun n => |ω n|, |C2| + |C3| + 3 * Real.pi / 16 * |C1| * Cj, k,
    max (max N1 N2) (max N3 N4), ?_, ?_⟩
  · have h := (continuous_abs.tendsto (0 : ℝ)).comp hωT
    simpa [Function.comp_def] using h
  intro n hn z hz B hB
  have hn12 : max N1 N2 ≤ n := le_trans (le_max_left _ _) hn
  have hn34 : max N3 N4 ≤ n := le_trans (le_max_right _ _) hn
  have h1 : N1 ≤ n := le_trans (le_max_left N1 N2) hn12
  have h2 : N2 ≤ n := le_trans (le_max_right N1 N2) hn12
  have h3 : N3 ≤ n := le_trans (le_max_left N3 N4) hn34
  have h4 : N4 ≤ n := le_trans (le_max_right N3 N4) hn34
  obtain ⟨⟨hcn, hεpos⟩, hwin_n, hInt_n⟩ := hN4 n h4
  have hμz : μ n z ∈ Icc lo hi := hwin_n z hz
  have hμ : 0 < μ n z := lt_of_lt_of_le hlo hμz.1
  have hJle : ‖J (μ n z : ℂ)‖ ≤ Cj := hJ (μ n z) hμz
  have hν : 0 < ν n := hνpos n
  have hA' := hA n h1 z hz B hB
  have hO' := hO n h2 z hz B hB
  have hE' := hE n h3 z hz B hB
  have hint := hInt_n z hz B hB
  have hsplit := flat_IT_split (S n) (ν n ^ (-(3 / 2 : ℝ)))
    (fun s => (S n).Mcell s ((S n).xi (μ n z : ℂ) B s)) hint.1 hint.2
  have hYX : (Complex.I * ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) *
        Nnu lam κ (ν n) * J (μ n z : ℂ)).re
      = -(((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ)).im := by
    rw [show Complex.I * ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ)
        = Complex.I * (((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ))
        by ring]
    simp [Complex.mul_re]
  have hWeq : (Complex.I * aZero lam ell (μ n z : ℂ) B * Nnu lam κ (ν n) * J (μ n z : ℂ)).re
      - (Complex.I * ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ)).re
      = (Complex.I * (aZero lam ell (μ n z : ℂ) B - ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B))
          * Nnu lam κ (ν n) * J (μ n z : ℂ)).re := by
    rw [show Complex.I * (aZero lam ell (μ n z : ℂ) B - ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B))
        * Nnu lam κ (ν n) * J (μ n z : ℂ)
        = Complex.I * aZero lam ell (μ n z : ℂ) B * Nnu lam κ (ν n) * J (μ n z : ℂ)
          - Complex.I * ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ)
          by ring]
    rw [Complex.sub_re]
  have hWn : |(Complex.I * (aZero lam ell (μ n z : ℂ) B - ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B))
        * Nnu lam κ (ν n) * J (μ n z : ℂ)).re|
      ≤ ‖aZero lam ell (μ n z : ℂ) B - ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B)‖
        * ‖Nnu lam κ (ν n)‖ * ‖J (μ n z : ℂ)‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    simp
  have hWb : |(Complex.I * aZero lam ell (μ n z : ℂ) B * Nnu lam κ (ν n) * J (μ n z : ℂ)).re
      - (Complex.I * ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B) * Nnu lam κ (ν n) * J (μ n z : ℂ)).re|
      ≤ C1 * ν n * bNorm a B * ‖Nnu lam κ (ν n)‖ * ‖J (μ n z : ℂ)‖ := by
    rw [hWeq]
    refine hWn.trans ?_
    have hd : ‖aZero lam ell (μ n z : ℂ) B - ((S n).aNuC lam κ (μ n z : ℂ) (ν n) B)‖
        ≤ C1 * ν n * bNorm a B := by
      rw [norm_sub_rev]; exact hA'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) (norm_nonneg _)
  have hP : 0 ≤ (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n)) :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hν.le) k) (Real.exp_pos _).le
  have hp : 0 ≤ ν n ^ (3 + 2 * μ n z) := Real.rpow_nonneg hν.le _
  have hq : ν n ^ (5 + 2 * μ n z) = ν n ^ (3 + 2 * μ n z) * ν n ^ 2 := by
    rw [show (5 + 2 * μ n z) = (3 + 2 * μ n z) + 2 by ring, Real.rpow_add hν, Real.rpow_two]
  have hb : 0 ≤ bNorm a B := ENNReal.toReal_nonneg
  have hcore := flat_core (S n).eps3 (μ n z) (ν n) (ω n) C1 C2 C3
    ((ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) ‖Nnu lam κ (ν n)‖ ‖J (μ n z : ℂ)‖
    (bNorm a B) _ _ _ _ _ (ν n ^ (3 + 2 * μ n z)) (ν n ^ (5 + 2 * μ n z)) (S n).c
    hεpos hμ hν hP (norm_nonneg _) (norm_nonneg _) hb hcn hp hq hYX hO' hE' hWb
  have hfac_nn : 0 ≤ ((S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z)) *
      (|ω n| + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B := by
    have hq_nn : 0 ≤ ν n ^ (5 + 2 * μ n z) := Real.rpow_nonneg hν.le _
    have h1_nn : 0 ≤ (S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z) :=
      mul_nonneg (mul_nonneg hεpos.le (norm_nonneg _)) hq_nn
    have h2_nn : 0 ≤ |ω n| + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n)) :=
      add_nonneg (add_nonneg (abs_nonneg _) hν.le) hP
    exact mul_nonneg (mul_nonneg h1_nn h2_nn) hb
  have hC_le : |C2| + |C3| + 3 * Real.pi / 16 * |C1| * ‖J (μ n z : ℂ)‖ ≤
      |C2| + |C3| + 3 * Real.pi / 16 * |C1| * Cj := by
    have hpi : 0 ≤ 3 * Real.pi / 16 * |C1| := by positivity
    linarith [mul_le_mul_of_nonneg_left hJle hpi]
  dsimp only [FlatSetting.ellMuC]
  rw [hsplit]
  refine hcore.trans ?_
  calc (|C2| + |C3| + 3 * Real.pi / 16 * |C1| * ‖J (μ n z : ℂ)‖) *
        ((S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z)) *
        (|ω n| + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B
      = (|C2| + |C3| + 3 * Real.pi / 16 * |C1| * ‖J (μ n z : ℂ)‖) *
          (((S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z)) *
            (|ω n| + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B) := by ring
    _ ≤ (|C2| + |C3| + 3 * Real.pi / 16 * |C1| * Cj) *
          (((S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z)) *
            (|ω n| + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B) :=
        mul_le_mul_of_nonneg_right hC_le hfac_nn
    _ = (|C2| + |C3| + 3 * Real.pi / 16 * |C1| * Cj) *
          ((S n).eps3 * ‖Nnu lam κ (ν n)‖ * ν n ^ (5 + 2 * μ n z)) *
          (|ω n| + ν n + (ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (ν n))) * bNorm a B := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
