import UnforcedLeray.Loc.Hyp.ResidualForce.Weights

/-!
# `H-Residual`, helpers: products of a decaying field and the heat tail

Support for `Loc/Hyp/ResidualForce.lean` (`paper/main.tex` lines 474–491, blueprint B0722).
For a bilinear `B` and smooth fields `F, K` we write `bcol B F K = B(F, K)` (a column of
`F ⊗ K + K ⊗ F`) and compute its first and second coordinate derivatives by the Leibniz
rule. If

* `F` has the decay of `H_h[u_dss]` (line 160): `|D^a F(y)| ≤ C(1 + |y|)^{-1-a}`, `a ≤ 2`
  (`DecayW`), and
* `K` has the decay of the heat tail at scale `δ² = e^{τ/2}`:
  `|D^b K(y)| ≤ C' δ^{2b+2} (1 + δ²|y|)^{-1-b}`, `b ≤ 2` (`DecayK`),

then `|B(F,K)| ≤ C''(1+|y|)^{-2}` and every first and second derivative of `B(F,K)` is
`≤ 2‖B‖CC' ψ_δ`, hence of `L²` norm `≤ 2‖B‖CC' cPsi δ²` (`Weights.psi_L2`). These are the
manuscript's bounds `C⟨x⟩^{-3}`, `C⟨x⟩^{-4}` for the unprojected divergence and its gradient,
in similarity variables (lines 482–491).

Main declarations: `bcol`, `dpart_bcol`, `dpart_dpart_bcol`, `DecayW`, `DecayK`,
`bcol_estimates`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.ResidualForceHyp

open UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L10

section Leibniz

variable (B : Space →L[ℝ] Space →L[ℝ] Space)

/-- `y ↦ B(F(y), K(y))`. -/
def bcol (F K : SpatialField) : SpatialField := fun y => B (F y) (K y)

theorem contDiff_bcol {F K : SpatialField} (hF : ContDiff ℝ ∞ F) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (bcol B F K) :=
  (B.contDiff.comp hF).clm_apply hK

theorem dpart_add {f g : SpatialField} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) : dpart (fun y => f y + g y) i = fun y => dpart f i y + dpart g i y := by
  funext y
  unfold dpart
  rw [fderiv_fun_add (hf y) (hg y)]
  rfl

theorem dpart_bcol {F K : SpatialField} (hF : Differentiable ℝ F) (hK : Differentiable ℝ K)
    (i : Fin 3) :
    dpart (bcol B F K) i = fun y => B (dpart F i y) (K y) + B (F y) (dpart K i y) := by
  funext y
  have h := B.hasFDerivAt_of_bilinear (hF y).hasFDerivAt (hK y).hasFDerivAt
  unfold dpart bcol
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply]
  rw [add_comm]

theorem dpart_dpart_bcol {F K : SpatialField} (hF : ContDiff ℝ ∞ F) (hK : ContDiff ℝ ∞ K)
    (i l : Fin 3) (y : Space) :
    dpart (dpart (bcol B F K) i) l y =
      B (dpart (dpart F i) l y) (K y) + B (dpart F i y) (dpart K l y) +
        (B (dpart F l y) (dpart K i y) + B (F y) (dpart (dpart K i) l y)) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hKd : Differentiable ℝ K := hK.differentiable (by simp)
  have hF1 : ContDiff ℝ ∞ (dpart F i) := contDiff_dpart hF i
  have hK1 : ContDiff ℝ ∞ (dpart K i) := contDiff_dpart hK i
  rw [dpart_bcol B hFd hKd i]
  have e : (fun y => B (dpart F i y) (K y) + B (F y) (dpart K i y)) =
      fun y => bcol B (dpart F i) K y + bcol B F (dpart K i) y := rfl
  rw [e, dpart_add ((contDiff_bcol B hF1 hK).differentiable (by simp))
    ((contDiff_bcol B hF hK1).differentiable (by simp)),
    dpart_bcol B (hF1.differentiable (by simp)) hKd, dpart_bcol B hFd (hK1.differentiable (by simp))]

theorem norm_bcol_le (F K : SpatialField) (y : Space) :
    ‖bcol B F K y‖ ≤ ‖B‖ * ‖F y‖ * ‖K y‖ :=
  B.le_opNorm₂ _ _

theorem norm_dpart_bcol_le {F K : SpatialField} (hF : ContDiff ℝ ∞ F) (hK : ContDiff ℝ ∞ K)
    (i : Fin 3) (y : Space) :
    ‖dpart (bcol B F K) i y‖ ≤
      ‖B‖ * (‖fderiv ℝ F y‖ * ‖K y‖ + ‖F y‖ * ‖fderiv ℝ K y‖) := by
  rw [dpart_bcol B (hF.differentiable (by simp)) (hK.differentiable (by simp)) i]
  refine (norm_add_le _ _).trans ?_
  have h1 := (B.le_opNorm₂ (dpart F i y) (K y)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_dpart_le F i y)
      (norm_nonneg B)) (norm_nonneg _))
  have h2 := (B.le_opNorm₂ (F y) (dpart K i y)).trans
    (mul_le_mul_of_nonneg_left (norm_dpart_le K i y) (mul_nonneg (norm_nonneg B) (norm_nonneg _)))
  nlinarith [h1, h2]

theorem norm_dpart_dpart_bcol_le {F K : SpatialField} (hF : ContDiff ℝ ∞ F)
    (hK : ContDiff ℝ ∞ K) (i l : Fin 3) (y : Space) :
    ‖dpart (dpart (bcol B F K) i) l y‖ ≤
      ‖B‖ * (‖iteratedFDeriv ℝ 2 F y‖ * ‖K y‖ + 2 * (‖fderiv ℝ F y‖ * ‖fderiv ℝ K y‖) +
        ‖F y‖ * ‖iteratedFDeriv ℝ 2 K y‖) := by
  rw [dpart_dpart_bcol B hF hK i l y]
  have hB := norm_nonneg B
  have e1 := (B.le_opNorm₂ (dpart (dpart F i) l y) (K y)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_dpart_dpart_le hF i l y) hB)
      (norm_nonneg _))
  have e2 := (B.le_opNorm₂ (dpart F i y) (dpart K l y)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_dpart_le F i y) hB) (norm_dpart_le K l y)
      (norm_nonneg _) (mul_nonneg hB (norm_nonneg _)))
  have e3 := (B.le_opNorm₂ (dpart F l y) (dpart K i y)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_dpart_le F l y) hB) (norm_dpart_le K i y)
      (norm_nonneg _) (mul_nonneg hB (norm_nonneg _)))
  have e4 := (B.le_opNorm₂ (F y) (dpart (dpart K i) l y)).trans
    (mul_le_mul_of_nonneg_left (norm_dpart_dpart_le hK i l y) (mul_nonneg hB (norm_nonneg _)))
  calc ‖B (dpart (dpart F i) l y) (K y) + B (dpart F i y) (dpart K l y) +
        (B (dpart F l y) (dpart K i y) + B (F y) (dpart (dpart K i) l y))‖
      ≤ ‖B (dpart (dpart F i) l y) (K y)‖ + ‖B (dpart F i y) (dpart K l y)‖ +
        (‖B (dpart F l y) (dpart K i y)‖ + ‖B (F y) (dpart (dpart K i) l y)‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ _ := by nlinarith [e1, e2, e3, e4]

end Leibniz

/-! ## Decay classes and the real-variable estimates -/

/-- The decay of `H_h[u_dss]` (B0710, lines 275–278): `|D^a F| ≤ C(1 + |y|)^{-1-a}`, `a ≤ 2`. -/
def DecayW (F : SpatialField) (C : ℝ) : Prop :=
  ∀ y, ‖F y‖ ≤ C / (1 + ‖y‖) ∧ ‖fderiv ℝ F y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
    ‖iteratedFDeriv ℝ 2 F y‖ ≤ C / (1 + ‖y‖) ^ 3

/-- The decay of the heat tail at scale `δ² = √t` (lines 446–458):
`|D^b K| ≤ C δ^{2b+2}(1 + δ²|y|)^{-1-b}`, `b ≤ 2`. -/
def DecayK (K : SpatialField) (C δ : ℝ) : Prop :=
  ∀ y, ‖K y‖ ≤ C * δ ^ 2 / (1 + δ ^ 2 * ‖y‖) ∧
    ‖fderiv ℝ K y‖ ≤ C * δ ^ 4 / (1 + δ ^ 2 * ‖y‖) ^ 2 ∧
    ‖iteratedFDeriv ℝ 2 K y‖ ≤ C * δ ^ 6 / (1 + δ ^ 2 * ‖y‖) ^ 3

/-- A `K`-type field is `W`-type for `δ ≤ 1`. -/
theorem DecayK.decayW {K : SpatialField} {C δ : ℝ} (hK : DecayK K C δ) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : DecayW K C := by
  intro y
  obtain ⟨h0, h1, h2⟩ := hK y
  have hdq := sq_mul_le_q hδ hδ1 y
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hq : 0 < 1 + δ ^ 2 * ‖y‖ := by positivity
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩
  · rw [div_le_div_iff₀ hq hp]
    nlinarith [mul_le_mul_of_nonneg_left hdq hC]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (δ ^ 2 * (1 + ‖y‖)) ^ 2 ≤ (1 + δ ^ 2 * ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdq 2
    nlinarith [mul_le_mul_of_nonneg_left h3 hC]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (δ ^ 2 * (1 + ‖y‖)) ^ 3 ≤ (1 + δ ^ 2 * ‖y‖) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hdq 3
    nlinarith [mul_le_mul_of_nonneg_left h3 hC]

section Real

variable {δ p q C C' a0 a1 a2 b0 b1 b2 : ℝ}

/-- The value: `a₀b₀ ≤ CC'/p²`. -/
theorem real_value (hδ : 0 < δ) (hp : 0 < p) (hdq : δ ^ 2 * p ≤ q)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (_ha0' : 0 ≤ a0) (hb0' : 0 ≤ b0)
    (ha0 : a0 ≤ C / p) (hb0 : b0 ≤ C' * δ ^ 2 / q) : a0 * b0 ≤ C * C' / p ^ 2 := by
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hdq
  calc a0 * b0 ≤ (C / p) * (C' * δ ^ 2 / q) := mul_le_mul ha0 hb0 hb0' (by positivity)
    _ = C * C' * (δ ^ 2 / (p * q)) := by field_simp
    _ ≤ C * C' * (1 / p ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hC')
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hdq hp.le]
    _ = C * C' / p ^ 2 := by ring

/-- First derivatives: `a₁b₀ + a₀b₁ ≤ 2CC'ψ`. -/
theorem real_first (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hp1 : 1 ≤ p) (hq1 : 1 ≤ q)
    (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (_ha0' : 0 ≤ a0) (_ha1' : 0 ≤ a1) (hb0' : 0 ≤ b0) (hb1' : 0 ≤ b1)
    (ha0 : a0 ≤ C / p) (ha1 : a1 ≤ C / p ^ 2) (hb0 : b0 ≤ C' * δ ^ 2 / q)
    (hb1 : b1 ≤ C' * δ ^ 4 / q ^ 2) :
    a1 * b0 + a0 * b1 ≤ 2 * C * C' * (2 * δ ^ 2 / p ^ 2 + δ ^ 5 / q ^ 3) := by
  have hp : 0 < p := by linarith
  have hq : 0 < q := by linarith
  have hCC : 0 ≤ C * C' := mul_nonneg hC hC'
  have t1 : a1 * b0 ≤ C * C' * (δ ^ 2 / p ^ 2) :=
    calc a1 * b0 ≤ (C / p ^ 2) * (C' * δ ^ 2 / q) := mul_le_mul ha1 hb0 hb0' (by positivity)
      _ = C * C' * (δ ^ 2 / (p ^ 2 * q)) := by field_simp
      _ ≤ C * C' * (δ ^ 2 / p ^ 2) := by
          gcongr
          nlinarith [pow_pos hp 2]
  have t2 : a0 * b1 ≤ C * C' * (δ ^ 2 / p ^ 3 + δ ^ 5 / q ^ 3) :=
    calc a0 * b1 ≤ (C / p) * (C' * δ ^ 4 / q ^ 2) := mul_le_mul ha0 hb1 hb1' (by positivity)
      _ = C * C' * (δ ^ 4 / (p * q ^ 2)) := by field_simp
      _ ≤ C * C' * (δ ^ 2 / p ^ 3 + δ ^ 5 / q ^ 3) :=
          mul_le_mul_of_nonneg_left (case_bound hδ hp hq) hCC
  have t3 : δ ^ 2 / p ^ 3 ≤ δ ^ 2 / p ^ 2 := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hp1 (by norm_num))
  have h0 : 0 ≤ δ ^ 2 / p ^ 2 := by positivity
  have h5 : 0 ≤ δ ^ 5 / q ^ 3 := by positivity
  have e : 2 * C * C' * (2 * δ ^ 2 / p ^ 2 + δ ^ 5 / q ^ 3) =
      C * C' * (2 * (δ ^ 2 / p ^ 2)) + C * C' * (2 * (δ ^ 2 / p ^ 2) + 2 * (δ ^ 5 / q ^ 3)) := by
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left t3 hCC, mul_nonneg hCC h0, mul_nonneg hCC h5]

/-- Second derivatives: `a₂b₀ + 2a₁b₁ + a₀b₂ ≤ 2CC'ψ`. -/
theorem real_second (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp1 : 1 ≤ p) (hq1 : 1 ≤ q)
    (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (_ha0' : 0 ≤ a0) (_ha1' : 0 ≤ a1) (_ha2' : 0 ≤ a2) (hb0' : 0 ≤ b0) (hb1' : 0 ≤ b1)
    (hb2' : 0 ≤ b2)
    (ha0 : a0 ≤ C / p) (ha1 : a1 ≤ C / p ^ 2) (ha2 : a2 ≤ C / p ^ 3)
    (hb0 : b0 ≤ C' * δ ^ 2 / q) (hb1 : b1 ≤ C' * δ ^ 4 / q ^ 2) (hb2 : b2 ≤ C' * δ ^ 6 / q ^ 3) :
    a2 * b0 + 2 * (a1 * b1) + a0 * b2 ≤ 2 * C * C' * (2 * δ ^ 2 / p ^ 2 + δ ^ 5 / q ^ 3) := by
  have hp : 0 < p := by linarith
  have hq : 0 < q := by linarith
  have hCC : 0 ≤ C * C' := mul_nonneg hC hC'
  have hδ2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have t1 : a2 * b0 ≤ C * C' * (δ ^ 2 / p ^ 2) :=
    calc a2 * b0 ≤ (C / p ^ 3) * (C' * δ ^ 2 / q) := mul_le_mul ha2 hb0 hb0' (by positivity)
      _ = C * C' * (δ ^ 2 / (p ^ 3 * q)) := by field_simp
      _ ≤ C * C' * (δ ^ 2 / p ^ 2) := by
          gcongr
          have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp1 (by norm_num)
          nlinarith [pow_pos hp 2]
  have t2 : a1 * b1 ≤ C * C' * (δ ^ 2 / p ^ 2) :=
    calc a1 * b1 ≤ (C / p ^ 2) * (C' * δ ^ 4 / q ^ 2) := mul_le_mul ha1 hb1 hb1' (by positivity)
      _ = C * C' * (δ ^ 4 / (p ^ 2 * q ^ 2)) := by field_simp
      _ ≤ C * C' * (δ ^ 2 / p ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCC
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
          have : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
          rw [this]
          have h1 : δ ^ 2 * δ ^ 2 * p ^ 2 ≤ δ ^ 2 * 1 * p ^ 2 := by gcongr
          have h2 : δ ^ 2 * 1 * p ^ 2 ≤ δ ^ 2 * (p ^ 2 * q ^ 2) := by
            rw [mul_one]; gcongr; nlinarith [pow_pos hp 2]
          linarith
  have t3 : a0 * b2 ≤ C * C' * (δ ^ 2 / p ^ 3 + δ ^ 5 / q ^ 3) :=
    calc a0 * b2 ≤ (C / p) * (C' * δ ^ 6 / q ^ 3) := mul_le_mul ha0 hb2 hb2' (by positivity)
      _ = C * C' * (δ ^ 2 * (δ ^ 4 / (p * q ^ 2)) / q) := by field_simp
      _ ≤ C * C' * (δ ^ 4 / (p * q ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCC
          rw [div_le_iff₀ hq]
          have h0 : 0 ≤ δ ^ 4 / (p * q ^ 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right (hδ2.trans hq1) h0]
      _ ≤ C * C' * (δ ^ 2 / p ^ 3 + δ ^ 5 / q ^ 3) :=
          mul_le_mul_of_nonneg_left (case_bound hδ hp hq) hCC
  have t4 : δ ^ 2 / p ^ 3 ≤ δ ^ 2 / p ^ 2 := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hp1 (by norm_num))
  have h0 : 0 ≤ δ ^ 2 / p ^ 2 := by positivity
  have h5 : 0 ≤ δ ^ 5 / q ^ 3 := by positivity
  have e : 2 * C * C' * (2 * δ ^ 2 / p ^ 2 + δ ^ 5 / q ^ 3) =
      C * C' * (4 * (δ ^ 2 / p ^ 2)) + C * C' * (2 * (δ ^ 5 / q ^ 3)) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left t4 hCC, mul_nonneg hCC h0, mul_nonneg hCC h5]

end Real

/-! ## The `L²` estimates for `B(F, K)` -/

/-- **Product estimates.** For smooth `F` of class `DecayW C` and `K` of class `DecayK C' δ`
(`0 < δ ≤ 1`), the field `B(F,K)` and its first and second coordinate derivatives are
pointwise `≤ c(1 + |y|)^{-2}` (for domination), the derivatives are `≤ 2‖B‖CC'ψ_δ`, and all
are in `L²` with the derivatives of norm `≤ 2‖B‖CC' cPsi δ²`. -/
theorem bcol_estimates (B : Space →L[ℝ] Space →L[ℝ] Space) {F K : SpatialField}
    (hF : ContDiff ℝ ∞ F) (hK : ContDiff ℝ ∞ K) {C C' δ : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hFd : DecayW F C) (hKd : DecayK K C' δ) :
    (∀ y, ‖bcol B F K y‖ ≤ ‖B‖ * C * C' / (1 + ‖y‖) ^ 2) ∧
    (∀ i y, ‖dpart (bcol B F K) i y‖ ≤ 2 * ‖B‖ * C * C' * psi δ y) ∧
    (∀ i l y, ‖dpart (dpart (bcol B F K) i) l y‖ ≤ 2 * ‖B‖ * C * C' * psi δ y) := by
  have hB := norm_nonneg B
  refine ⟨fun y => ?_, fun i y => ?_, fun i l y => ?_⟩
  · obtain ⟨hF0, -, -⟩ := hFd y
    obtain ⟨hK0, -, -⟩ := hKd y
    refine (norm_bcol_le B F K y).trans ?_
    have h := real_value hδ (by positivity) (sq_mul_le_q hδ hδ1 y) hC hC' (norm_nonneg _)
      (norm_nonneg _) hF0 hK0
    calc ‖B‖ * ‖F y‖ * ‖K y‖ = ‖B‖ * (‖F y‖ * ‖K y‖) := by ring
      _ ≤ ‖B‖ * (C * C' / (1 + ‖y‖) ^ 2) := mul_le_mul_of_nonneg_left h hB
      _ = ‖B‖ * C * C' / (1 + ‖y‖) ^ 2 := by ring
  · obtain ⟨hF0, hF1, -⟩ := hFd y
    obtain ⟨hK0, hK1, -⟩ := hKd y
    refine (norm_dpart_bcol_le B hF hK i y).trans ?_
    have hq1 : 1 ≤ 1 + δ ^ 2 * ‖y‖ := by have := norm_nonneg y; nlinarith [sq_nonneg δ]
    have h := real_first hδ hδ1 (by linarith [norm_nonneg y]) hq1 hC hC' (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hF0 hF1 hK0 hK1
    unfold psi
    calc ‖B‖ * (‖fderiv ℝ F y‖ * ‖K y‖ + ‖F y‖ * ‖fderiv ℝ K y‖)
        ≤ ‖B‖ * (2 * C * C' * (2 * δ ^ 2 / (1 + ‖y‖) ^ 2 + δ ^ 5 / (1 + δ ^ 2 * ‖y‖) ^ 3)) :=
          mul_le_mul_of_nonneg_left h hB
      _ = _ := by ring
  · obtain ⟨hF0, hF1, hF2⟩ := hFd y
    obtain ⟨hK0, hK1, hK2⟩ := hKd y
    refine (norm_dpart_dpart_bcol_le B hF hK i l y).trans ?_
    have hq1 : 1 ≤ 1 + δ ^ 2 * ‖y‖ := by have := norm_nonneg y; nlinarith [sq_nonneg δ]
    have h := real_second hδ hδ1 (by linarith [norm_nonneg y]) hq1 hC hC' (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hF0 hF1 hF2 hK0 hK1 hK2
    unfold psi
    calc ‖B‖ * (‖iteratedFDeriv ℝ 2 F y‖ * ‖K y‖ + 2 * (‖fderiv ℝ F y‖ * ‖fderiv ℝ K y‖) +
          ‖F y‖ * ‖iteratedFDeriv ℝ 2 K y‖)
        ≤ ‖B‖ * (2 * C * C' * (2 * δ ^ 2 / (1 + ‖y‖) ^ 2 + δ ^ 5 / (1 + δ ^ 2 * ‖y‖) ^ 3)) :=
          mul_le_mul_of_nonneg_left h hB
      _ = _ := by ring

end UnforcedLeray.ResidualForceHyp
