import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.NormSq

/-!
# Part III-a, task `PartIII-a:T18/3/2/8` (gainLocF): gain-conjugated tensor fields are locally `L²`

Source: `the November 2 reference manuscript` lines 3541-3552.
`tCalNorm c (g⁻¹F) < ⊤` gives a finite weighted integral over `(0,∞) × qCell c`
(`NormSq`, `lintegral_ageμ`); on `[s₁,s₂] × cell c` the age weight `s^{-1/2}` is bounded below,
and `1 ≤ ` ... `g = gainG ≤ exp(γ/ν)` gives the bound for `F` itself.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Homogeneity of the tensor norm under a nonnegative real scalar. -/
theorem tnorm2_smul_nonneg (g : ℝ) (hg : 0 ≤ g) (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 (g • T) = g * tnorm2 T := by
  unfold tnorm2
  have h : ∀ i j : Fin 2, ‖(g • T) i j‖ ^ 2 = g ^ 2 * ‖T i j‖ ^ 2 := by
    intro i j
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hg, mul_pow]
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2, ‖(g • T) i j‖ ^ 2
      = g ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
    simp only [h, Finset.mul_sum]
  rw [hsum, Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq hg]

/-- The gain is at most `exp(γ/ν)` for `s > 0`. -/
theorem gainG_le_exp (γ ν s : ℝ) (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 0 < s) :
    gainG γ ν s ≤ Real.exp (γ / ν) := by
  unfold gainG
  apply Real.exp_le_exp.2
  have hd : 0 < 1 + ν * s := by nlinarith [mul_pos hν hs]
  rw [div_le_div_iff₀ hd hν]
  nlinarith [mul_nonneg hγ hs.le]

theorem gainLocF : UnforcedLeray.Short.IIIa.GainLocF := by
  unfold UnforcedLeray.Short.IIIa.GainLocF
  intro c ν γ hc hγ hν F hF hT s1 s2 hs1 hs12
  have hNS : UnforcedLeray.Short.IIIa.NormSq := normSq
  unfold UnforcedLeray.Short.IIIa.NormSq at hNS
  obtain ⟨-, hT2⟩ := hNS
  have hTm : ∀ i j, Measurable fun p => gainConj γ ν F p i j :=
    fun i j => measurable_gainConj_ten γ ν hF i j
  have hTmeas : Measurable fun p => tnorm2 (gainConj γ ν F p) := measurable_tnorm2 hTm
  have hmeasf : Measurable fun p => ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) :=
    ENNReal.measurable_ofReal.comp (hTmeas.pow_const 2)
  have hfin : ∫⁻ p, ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) ∂(ageμ c (-1 / 2)) < ⊤ := by
    rw [← hT2 c (gainConj γ ν F)]
    exact ENNReal.pow_lt_top hT
  rw [lintegral_ageμ hc (-1 / 2) hmeasf] at hfin
  have hs2 : 0 < s2 := by linarith
  have hs1' : 0 < s1 := hs1
  have hm_pos : 0 < c⁻¹ * s2 ^ (-1 / 2 : ℝ) :=
    mul_pos (inv_pos.2 hc) (Real.rpow_pos_of_pos hs2 _)
  set m : ℝ≥0∞ := ENNReal.ofReal (c⁻¹ * s2 ^ (-1 / 2 : ℝ)) with hm
  have hm0 : m ≠ 0 := (ENNReal.ofReal_pos.2 hm_pos).ne'
  have hmtop : m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcell : Icc s1 s2 ×ˢ B0579.cell c ⊆ Ioi (0 : ℝ) ×ˢ qCell c := by
    apply Set.prod_mono
    · intro x hx
      exact lt_of_lt_of_le hs1' hx.1
    · simp [B0579.cell, qCell, neg_div]
  have hS : MeasurableSet (Icc s1 s2 ×ˢ B0579.cell c) := by
    unfold B0579.cell
    exact measurableSet_Icc.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hpt : ∀ p ∈ Icc s1 s2 ×ˢ B0579.cell c,
      ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) ≤
        m⁻¹ * (ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
          ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2)) := by
    intro p hp
    have hp1 : p.1 ∈ Icc s1 s2 := hp.1
    have hpos : 0 < p.1 := lt_of_lt_of_le hs1' hp1.1
    have hle : s2 ^ (-1 / 2 : ℝ) ≤ p.1 ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hpos hp1.2 (by norm_num)
    have hw : m ≤ ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hc.le))
    calc ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2)
        = m⁻¹ * m * ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) := by
          rw [ENNReal.inv_mul_cancel hm0 hmtop, one_mul]
      _ = m⁻¹ * (m * ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2)) := by rw [mul_assoc]
      _ ≤ m⁻¹ * (ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
          ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2)) :=
          by gcongr
  have hint : ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2)
      ≤ m⁻¹ * ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) := by
    calc _ ≤ ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c,
          m⁻¹ * (ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
            ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2)) :=
          setLIntegral_mono' hS hpt
      _ = m⁻¹ * ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c,
          ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
            ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0)
      _ ≤ _ := by
          gcongr
  have hpart2 : ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c,
      ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) < ⊤ :=
    lt_of_le_of_lt hint (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (zero_lt_iff.2 hm0)) hfin)
  have hpart1 : ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤ := by
    have hK : ∀ p ∈ Icc s1 s2 ×ˢ B0579.cell c,
        ENNReal.ofReal (tnorm2 (F p) ^ 2) ≤
          ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
            ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) := by
      intro p hp
      have hpos : 0 < p.1 := lt_of_lt_of_le hs1' hp.1.1
      have hgne : gainG γ ν p.1 ≠ 0 := (Real.exp_pos _).ne'
      have hg0 : 0 ≤ gainG γ ν p.1 := (Real.exp_pos _).le
      have hFp : F p = gainG γ ν p.1 • gainConj γ ν F p := by
        simp only [gainConj, smul_smul, mul_inv_cancel₀ hgne, one_smul]
      have hgK : gainG γ ν p.1 ≤ Real.exp (γ / ν) := gainG_le_exp γ ν p.1 hγ hν hpos
      have hineq : (gainG γ ν p.1 * tnorm2 (gainConj γ ν F p)) ^ 2
          ≤ Real.exp (γ / ν) ^ 2 * tnorm2 (gainConj γ ν F p) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg0 hgK 2) (sq_nonneg _)
      rw [hFp, tnorm2_smul_nonneg _ hg0, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hineq
    calc ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2)
        ≤ ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c,
            ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
              ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) := setLIntegral_mono' hS hK
      _ = ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
            ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c,
              ENNReal.ofReal (tnorm2 (gainConj γ ν F p) ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hpart2
  exact ⟨hpart1, hpart2⟩

end UnforcedLeray.Short.IIIa
