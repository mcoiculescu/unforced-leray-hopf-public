import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `maskedUpperPiece_of`: the upper end of the masked free bound (source 4015-4020, 4028)

On the output region `s ≥ S = ε^{-b}` the far part vanishes (`FarUpperZero`), so the masked
operator is the free energy operator there.  The gain costs `g⁻¹(S)` on the outputs times
`e^{|γ|/ν}` on the inputs, and `g⁻¹(S)e^{|γ|/ν} ≤ e^{γ}` once `ν(1+νS) ≥ 1`, which holds in the
regime since `S = e^{bd/ν} ≥ e^{b d₋/ν}` and `ν` is small.  The free energy (`RealStressBound`)
gives `‖S_ε‖ ≤ Cν^{-1/2} ≤ Cν^{-1}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The input restriction to the whole chart is the identity. -/
theorem mu_inRestr_univ (c mZ ρb : ℝ) :
    inRestr c mZ ρb univ = ContinuousLinearMap.id ℝ (Zsp c mZ ρb) := by
  refine ContinuousLinearMap.ext fun F => (zEquiv c mZ ρb).injective ?_
  rw [zEquiv_inRestr, ContinuousLinearMap.id_apply]
  exact Prod.ext (restrLp_univ_apply _) (restrLp_univ_apply _)

/-- The map `s ↦ s/(1+νs)` is monotone, so `γ s/(1+νs)` is monotone for `γ ≥ 0`. -/
theorem mu_gain_le_of_ge {γ ν S x : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hS : 0 < S) (hx : S ≤ x) :
    γ * S / (1 + ν * S) ≤ γ * x / (1 + ν * x) := by
  have h1 : 0 < 1 + ν * S := by have := mul_pos hν hS; linarith
  have h2 : 0 < 1 + ν * x := by have := mul_pos hν (lt_of_lt_of_le hS hx); linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hx)]

/-- **`maskedUpperPiece_of`** (source 4015-4020, 4028): the upper end of the masked free bound. -/
theorem maskedUpperPiece_of (hE : RealStressBound) (hU : FarUpperZero) (hG : GainBlockBound) :
    MaskedUpperPiece := by
  obtain ⟨CE, hCE0, hEb⟩ := hE
  intro P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  have hγ : 0 < P.eigenvalue.re := hPl.eigenpair.re_pos
  refine ⟨Real.exp P.eigenvalue.re * CE, 1, min (min 1 (dm ^ 3 / 12)) ((dm * b) ^ 3 / 6), ?_, ?_⟩
  · exact lt_min (lt_min one_pos (div_pos (pow_pos hdm 3) (by norm_num)))
      (div_pos (pow_pos (mul_pos hdm hb) 3) (by norm_num))
  intro p d hreg hν ρb hρ hρ1 μ hμ SN hSN
  have hν0 : 0 < p.ν := p.ν_pos
  have hdm' : 0 < dm := hreg.dm_pos
  have hdd : dm ≤ d := hreg.dm_le
  have hd : 0 < d := lt_of_lt_of_le hdm' hdd
  have hb0 : 0 ≤ b := hb.le
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ (dm * b) ^ 3 / 6 := hν.trans (min_le_right _ _)
  -- the regime: `ε ≤ 1`, `P = 2εc ≤ 1`
  have hεe : p.ε = Real.exp (-d / p.ν) := hreg.eps_eq
  have hε1 : p.ε ≤ 1 := by
    rw [hεe, Real.exp_le_one_iff]
    have : 0 ≤ d / p.ν := div_nonneg hd.le hν0.le
    rw [neg_div]; linarith
  have hcc : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hEexp : Real.exp (-d / p.ν) = (Real.exp (d / p.ν))⁻¹ := by
    rw [neg_div, Real.exp_neg]
  have hdmx : 0 ≤ dm / p.ν := div_nonneg hdm'.le hν0.le
  have hE2 : 2 ≤ Real.exp (d / p.ν) * p.ν ^ 2 := by
    have h1 : (dm / p.ν) ^ 3 / 6 ≤ Real.exp (dm / p.ν) := by
      simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (dm / p.ν) hdmx 3
    have h2 : Real.exp (dm / p.ν) ≤ Real.exp (d / p.ν) :=
      Real.exp_le_exp.2 (by gcongr)
    have h3 : (dm / p.ν) ^ 3 / 6 * p.ν ^ 2 = dm ^ 3 / (6 * p.ν) := by
      rw [div_pow]; field_simp
    have h4 : 2 ≤ dm ^ 3 / (6 * p.ν) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hν0)]; linarith
    calc (2 : ℝ) ≤ dm ^ 3 / (6 * p.ν) := h4
      _ = (dm / p.ν) ^ 3 / 6 * p.ν ^ 2 := h3.symm
      _ ≤ Real.exp (dm / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ Real.exp (d / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hP1 : p.period ≤ 1 := by
    unfold Params.period
    rw [hεe, hcc, hEexp]
    have hEp : 0 < Real.exp (d / p.ν) := Real.exp_pos _
    rw [show 2 * (Real.exp (d / p.ν))⁻¹ * (p.ν ^ 2)⁻¹ =
        2 / (Real.exp (d / p.ν) * p.ν ^ 2) by field_simp]
    rw [div_le_one (mul_pos hEp (pow_pos hν0 2))]
    exact hE2
  -- the partial sum `S = ε^{-b} = e^{bd/ν}` and `ν² S ≥ 1`
  have hεpos : 0 < p.ε := p.ε_pos
  have hS0 : p.ε ^ (-b) = Real.exp (d * b / p.ν) := by
    rw [Real.rpow_def_of_pos hεpos, hεe, Real.log_exp]
    congr 1
    ring
  set S : ℝ := p.ε ^ (-b) with hSdef
  have hSpos : 0 < S := by rw [hS0]; exact Real.exp_pos _
  have hνS : 1 ≤ p.ν ^ 2 * S := by
    rw [hS0]
    have hdb : dm * b / p.ν ≤ d * b / p.ν := by
      gcongr
    have hxb : 0 ≤ dm * b / p.ν := div_nonneg (mul_nonneg hdm'.le hb0) hν0.le
    have h1 : (dm * b / p.ν) ^ 3 / 6 ≤ Real.exp (dm * b / p.ν) := by
      simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (dm * b / p.ν) hxb 3
    have h2 : Real.exp (dm * b / p.ν) ≤ Real.exp (d * b / p.ν) := Real.exp_le_exp.2 hdb
    have h3 : (dm * b / p.ν) ^ 3 / 6 * p.ν ^ 2 = (dm * b) ^ 3 / (6 * p.ν) := by
      rw [div_pow]; field_simp
    have h4 : 1 ≤ (dm * b) ^ 3 / (6 * p.ν) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hν0)]; linarith
    calc (1 : ℝ) ≤ (dm * b) ^ 3 / (6 * p.ν) := h4
      _ = (dm * b / p.ν) ^ 3 / 6 * p.ν ^ 2 := h3.symm
      _ ≤ Real.exp (dm * b / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ Real.exp (d * b / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = p.ν ^ 2 * Real.exp (d * b / p.ν) := mul_comm _ _
  -- the gain ratio: `exp(-γS/(1+νS)) · exp(|γ|/ν) ≤ e^γ`
  have hγ0 : 0 ≤ P.eigenvalue.re := hγ.le
  have hpos1 : 0 < 1 + p.ν * S := by have := mul_pos hν0 hSpos; linarith
  have hge1 : 1 ≤ p.ν * (1 + p.ν * S) := by
    have : p.ν * (1 + p.ν * S) = p.ν + p.ν ^ 2 * S := by ring
    linarith
  have hid : P.eigenvalue.re / p.ν - P.eigenvalue.re * S / (1 + p.ν * S) =
      P.eigenvalue.re / (p.ν * (1 + p.ν * S)) := by
    have h1 : (1 + p.ν * S) ≠ 0 := hpos1.ne'
    field_simp
    ring
  have hexp_ineq : -(P.eigenvalue.re * S / (1 + p.ν * S)) + P.eigenvalue.re / p.ν ≤
      P.eigenvalue.re := by
    have : P.eigenvalue.re / (p.ν * (1 + p.ν * S)) ≤ P.eigenvalue.re :=
      div_le_self hγ.le hge1
    linarith
  set a : ℝ := Real.exp (-(P.eigenvalue.re * S / (1 + p.ν * S))) with ha
  set bb : ℝ := Real.exp (|P.eigenvalue.re| / p.ν) with hbb
  have hga : ∀ x : Chart, S ≤ x.1 → gainInvFun P.eigenvalue.re p.ν x ≤ a := by
    intro x hx
    have hmax : max x.1 0 = x.1 := max_eq_left (le_trans hSpos.le hx)
    have hm := mu_gain_le_of_ge hγ0 hν0 hSpos hx
    simp only [gainInvFun, gainFun, UnforcedLeray.Short.IIIa.gainG, hmax, ha]
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.2 (neg_le_neg hm)
  have hgb : ∀ x : Chart, gainFun P.eigenvalue.re p.ν x ≤ bb := by
    intro x
    have h := gainFun_le (γ := P.eigenvalue.re) hν0 x
    rw [abs_of_pos (gainFun_pos _ _ x)] at h
    exact h
  have hab : a * bb ≤ Real.exp P.eigenvalue.re := by
    rw [ha, hbb, ← Real.exp_add, abs_of_pos hγ]
    exact Real.exp_le_exp.2 hexp_ineq
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hb0' : 0 ≤ bb := (Real.exp_pos _).le
  -- the masked operator is the free operator on the upper end
  obtain ⟨Seps, Sf, hpair, hSNeq⟩ := (isMaskedNear_iff p μ δ S SN).1 hSN
  obtain ⟨⟨Seps', hSm, hTr⟩, hF⟩ := hpair
  have hcomp : gainRestrS P.eigenvalue.re p.ν_pos (ageAbove S) SN =
      gainBlockS P.eigenvalue.re p.ν_pos (ageAbove S) univ Seps := by
    rw [hSNeq]
    have hU0 := hU p.c mZ ρb p.R p.ν μ δ S p.c_pos hmZ hρ hρ1 Sf hF
    unfold gainRestrS gainBlockS
    rw [mu_inRestr_univ, ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_sub, hU0, sub_zero]
  rw [hcomp]
  haveI : Fact (0 < p.period) := ⟨p.period_pos⟩
  have hSn : ‖Seps‖ ≤ CE * p.ν ^ (-(1 / 2 : ℝ)) :=
    hEb p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl hε1 hP1 μ (hKsub hμ).1 (hKsub hμ).2
      mZ ρb hmZ hρ hρ1 Seps' Seps hSm hTr
  have hrp : p.ν ^ (-(1 / 2 : ℝ)) ≤ p.ν⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
  calc ‖gainBlockS P.eigenvalue.re p.ν_pos (ageAbove S) univ Seps‖
      ≤ a * bb * ‖Seps‖ :=
        hG p.c mZ ρb P.eigenvalue.re p.ν p.ν_pos (ageAbove S) univ a bb Seps
          (measurableSet_ageAbove S) MeasurableSet.univ ha0 hb0' (fun x hx => hga x hx)
          (fun x _ => hgb x)
    _ ≤ Real.exp P.eigenvalue.re * ‖Seps‖ := mul_le_mul_of_nonneg_right hab (norm_nonneg _)
    _ ≤ Real.exp P.eigenvalue.re * (CE * p.ν⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact hSn.trans (mul_le_mul_of_nonneg_left hrp hCE0)
    _ = Real.exp P.eigenvalue.re * CE * p.ν⁻¹ ^ 1 := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
