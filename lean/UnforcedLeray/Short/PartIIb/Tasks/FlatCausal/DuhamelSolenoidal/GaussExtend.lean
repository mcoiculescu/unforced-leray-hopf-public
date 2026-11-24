import UnforcedLeray.Short.PartIIb.Sub.T12_6

/-!
# Part II-b, task `PartII-b:T12/6` (`DsolGaussExtend`): slice solenoidality against
Gaussian-decaying tests

Source of record: `the November 2 reference manuscript`, line 1924 ("the heat flow
preserves solenoidality, `P_0 G = G`"). Target: `DsolGaussExtend` of `Sub/T12_6.lean` (line 155),
proved literally as `UnforcedLeray.Short.IIb.dsolGaussExtend`.

## Proof (cutoff and dominated convergence)

Fix a smooth bump `χ` on `ℝ × ℝ` with `0 ≤ χ ≤ 1`, `χ = 1` on the closed unit ball and compact
support. For `R > 0` put `χ_R(y) = χ(R⁻¹ • y)`. The test `χ_R ψ` is smooth with compact support, so
the hypothesis gives `∫ dsolF G (χ_R ψ) (t, ·) = 0`. The product rule
`∇(χ_R ψ) = χ_R ∇ψ + ψ ∇χ_R` splits this as

  `∫ χ_R D + ∫ ψ E_R = 0`,  `D = dsolF G ψ (t, ·)`,  `E_R = G_0 ∂_q χ_R + G_1 ∂_η χ_R`.

Since `|∂χ_R| ≤ R⁻¹ M` (`M` bounds `‖Dχ‖`) and `|ψ| ≤ C e^{-a|y|²}`, the second integral is at most
`(2 C M ∫ e^{-a|y|²}‖G‖) R⁻¹`, which tends to `0` along `R = n + 1`. The first integral tends to
`∫ D` by dominated convergence (`χ_R → 1` pointwise, `|χ_R D| ≤ |D|`, and `D` is integrable by
`DsolGaussInt`). Uniqueness of limits gives `∫ D = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Helper definitions -/

/-- The scaled cutoff `y ↦ χ (R⁻¹ • y)`. -/
def dsolCut (χ : ℝ × ℝ → ℝ) (R : ℝ) (y : ℝ × ℝ) : ℝ :=
  χ (R⁻¹ • y)

/-- The error term of the product rule: `y ↦ G(t,y)_0 ∂_q c(y) + G(t,y)_1 ∂_η c(y)`. -/
def dsolE (G : CProf) (t : ℝ) (c : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℂ :=
  G (t, y) 0 * (fderiv ℝ c y (1, 0) : ℂ) + G (t, y) 1 * (fderiv ℝ c y (0, 1) : ℂ)

/-! ## Elementary norm bounds -/

lemma dsol_norm_e0_le : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by
  rw [Prod.norm_def]; simp

lemma dsol_norm_e1_le : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by
  rw [Prod.norm_def]; simp

lemma dsol_abs_fderiv_le (f : ℝ × ℝ → ℝ) (z v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    |fderiv ℝ f z v| ≤ ‖fderiv ℝ f z‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ f z v‖ ≤ ‖fderiv ℝ f z‖ * ‖v‖ := (fderiv ℝ f z).le_opNorm v
    _ ≤ ‖fderiv ℝ f z‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = ‖fderiv ℝ f z‖ := mul_one _

lemma dsol_pair_norm_le (z : CMerid) (p q : ℝ) :
    ‖z 0 * (p : ℂ) + z 1 * (q : ℂ)‖ ≤ ‖z‖ * (|p| + |q|) := by
  have h0 : ‖z 0‖ ≤ ‖z‖ := PiLp.norm_apply_le z 0
  have h1 : ‖z 1‖ ≤ ‖z‖ := PiLp.norm_apply_le z 1
  calc ‖z 0 * (p : ℂ) + z 1 * (q : ℂ)‖ ≤ ‖z 0 * (p : ℂ)‖ + ‖z 1 * (q : ℂ)‖ :=
        norm_add_le _ _
    _ = ‖z 0‖ * |p| + ‖z 1‖ * |q| := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖z‖ * |p| + ‖z‖ * |q| :=
        add_le_add (mul_le_mul_of_nonneg_right h0 (abs_nonneg p))
          (mul_le_mul_of_nonneg_right h1 (abs_nonneg q))
    _ = ‖z‖ * (|p| + |q|) := by ring

lemma dsol_mul_ofReal_norm_le {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) (z : ℂ) :
    ‖(c : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-! ## Measurability and integrability of Gaussian-weighted fields -/

lemma dsol_gauss_aesm {g : ℝ × ℝ → CMerid} (hg : DsolGaussInt g) :
    AEStronglyMeasurable g volume := by
  have h1 := (hg 1 one_pos).aestronglyMeasurable
  have hc : Continuous (fun y : ℝ × ℝ => Real.exp (-(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2))) := by
    fun_prop
  -- the scalar-action identities are restated so that they are checked up to defeq
  have hsm : ∀ (c d : ℝ) (v : CMerid), c • d • v = (c * d) • v := fun c d v => smul_smul c d v
  have hone : ∀ v : CMerid, (1 : ℝ) • v = v := fun v => one_smul ℝ v
  refine (hc.aestronglyMeasurable.smul h1).congr (ae_of_all _ fun y => ?_)
  have h0 : Real.exp (-(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2)) * Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) = 1 := by
    rw [← Real.exp_add, show -(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2) + -1 * (y.1 ^ 2 + y.2 ^ 2) = 0 by ring,
      Real.exp_zero]
  show Real.exp (-(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2)) • (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) • g y) = g y
  rw [hsm, h0, hone]

lemma dsol_gauss_norm_integrable {g : ℝ × ℝ → CMerid} (hg : DsolGaussInt g) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖g y‖) := by
  refine (hg a ha).norm.congr (ae_of_all _ fun y => ?_)
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma dsol_pair_aesm {g : ℝ × ℝ → CMerid} (hg : AEStronglyMeasurable g volume)
    {p q : ℝ × ℝ → ℝ} (hp : Continuous p) (hq : Continuous q) :
    AEStronglyMeasurable (fun y => g y 0 * (p y : ℂ) + g y 1 * (q y : ℂ)) volume := by
  have hc0 : Continuous (fun z : CMerid => z 0) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0
  have hc1 : Continuous (fun z : CMerid => z 1) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1
  have h0 : AEStronglyMeasurable (fun y => g y 0) volume := hc0.comp_aestronglyMeasurable hg
  have h1 : AEStronglyMeasurable (fun y => g y 1) volume := hc1.comp_aestronglyMeasurable hg
  exact (h0.mul (Complex.continuous_ofReal.comp hp).aestronglyMeasurable).add
    (h1.mul (Complex.continuous_ofReal.comp hq).aestronglyMeasurable)

lemma dsolE_aesm (G : CProf) (t : ℝ) (hgA : AEStronglyMeasurable (fun y : ℝ × ℝ => G (t, y)) volume)
    {c : ℝ × ℝ → ℝ} (hc : ContDiff ℝ ∞ c) :
    AEStronglyMeasurable (dsolE G t c) volume := by
  have hfd : Continuous (fun y => fderiv ℝ c y) := hc.continuous_fderiv (by simp)
  have hp : Continuous (fun y => fderiv ℝ c y (1, 0)) := hfd.clm_apply continuous_const
  have hq : Continuous (fun y => fderiv ℝ c y (0, 1)) := hfd.clm_apply continuous_const
  exact dsol_pair_aesm hgA hp hq

/-! ## The bump and its scalings -/

lemma dsolBump_exists : ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y : ℝ × ℝ, ‖y‖ ≤ 1 → χ y = 1) := by
  let B : ContDiffBump (0 : ℝ × ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  refine ⟨⇑B, B.contDiff, B.hasCompactSupport, fun y => ⟨B.nonneg, B.le_one⟩, fun y hy => ?_⟩
  exact B.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hy)

lemma dsolCut_contDiff {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (R : ℝ) :
    ContDiff ℝ ∞ (dsolCut χ R) := by
  unfold dsolCut
  exact hχ.comp (contDiff_id.const_smul R⁻¹)

lemma dsolCut_hasCompactSupport {χ : ℝ × ℝ → ℝ} (hχc : HasCompactSupport χ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (dsolCut χ R) := by
  unfold dsolCut
  exact hχc.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))

lemma dsolCut_fderiv {χ : ℝ × ℝ → ℝ} (hχ : Differentiable ℝ χ) (R : ℝ) (y v : ℝ × ℝ) :
    fderiv ℝ (dsolCut χ R) y v = R⁻¹ * fderiv ℝ χ (R⁻¹ • y) v := by
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => R⁻¹ • z)
      (R⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul R⁻¹
  have h2 : HasFDerivAt (dsolCut χ R)
      ((fderiv ℝ χ (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    HasFDerivAt.comp (x := y) (hχ (R⁻¹ • y)).hasFDerivAt h1
  rw [h2.fderiv]
  simp [smul_eq_mul]

lemma dsolCut_fderiv_abs_le {χ : ℝ × ℝ → ℝ} (hχd : Differentiable ℝ χ) {M : ℝ}
    (hM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) {R : ℝ} (hR : 0 < R) (y v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    |fderiv ℝ (dsolCut χ R) y v| ≤ R⁻¹ * M := by
  rw [dsolCut_fderiv hχd R y v, abs_mul, abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul_of_nonneg_left
    ((dsol_abs_fderiv_le χ (R⁻¹ • y) v hv).trans (hM _)) (inv_nonneg.2 hR.le)

lemma dsolCut_eq_one {χ : ℝ × ℝ → ℝ} (hχ1 : ∀ y : ℝ × ℝ, ‖y‖ ≤ 1 → χ y = 1) {R : ℝ}
    (hR : 0 < R) {y : ℝ × ℝ} (hy : ‖y‖ ≤ R) : dsolCut χ R y = 1 := by
  unfold dsolCut
  apply hχ1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  calc R⁻¹ * ‖y‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hR.le)
    _ = 1 := inv_mul_cancel₀ hR.ne'

/-! ## The product rule -/

lemma dsol_pt_identity (G : CProf) (t : ℝ) (ψ c : ℝ × ℝ → ℝ) (y : ℝ × ℝ)
    (hψ : DifferentiableAt ℝ ψ y) (hc : DifferentiableAt ℝ c y) :
    dsolF G (fun z => c z * ψ z) (t, y) =
      (c y : ℂ) * dsolF G ψ (t, y) + (ψ y : ℂ) * dsolE G t c y := by
  have hd : HasFDerivAt (fun z => c z * ψ z) (c y • fderiv ℝ ψ y + ψ y • fderiv ℝ c y) y :=
    hc.hasFDerivAt.mul hψ.hasFDerivAt
  simp only [dsolF, dsolE]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ## One cutoff step -/

/-- For a fixed scale `R > 0`, the cutoff test `χ_R ψ` gives the splitting and the
`O(R⁻¹)` bound on the error term. -/
lemma dsol_cut_step (G : CProf) (t : ℝ) (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hZero : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ y : ℝ × ℝ, dsolF G φ (t, y) = 0)
    (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (M : ℝ) (hM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M)
    (a C : ℝ) (hψb : ∀ y : ℝ × ℝ, ‖ψ y‖ ≤ C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)))
    (hgI : Integrable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖))
    (hgA : AEStronglyMeasurable (fun y : ℝ × ℝ => G (t, y)) volume)
    (hDint : Integrable (fun y : ℝ × ℝ => dsolF G ψ (t, y)))
    {R : ℝ} (hR : 0 < R) :
    (∫ y : ℝ × ℝ, (dsolCut χ R y : ℂ) * dsolF G ψ (t, y) =
        -∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y) ∧
      ‖∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y‖ ≤
        (2 * C * M * ∫ y : ℝ × ℝ, Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) * R⁻¹ := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hcd : ContDiff ℝ ∞ (dsolCut χ R) := dsolCut_contDiff hχ R
  have hcc : HasCompactSupport (dsolCut χ R) := dsolCut_hasCompactSupport hχc hR
  have hcdiff : Differentiable ℝ (dsolCut χ R) := hcd.differentiable (by simp)
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψcont : Continuous ψ := hψ.continuous
  have hcut01 : ∀ y, 0 ≤ dsolCut χ R y ∧ dsolCut χ R y ≤ 1 := fun y => hχ01 _
  -- product rule: the splitting of the test function
  have hpt : ∀ y : ℝ × ℝ, dsolF G (fun z => dsolCut χ R z * ψ z) (t, y) =
      (dsolCut χ R y : ℂ) * dsolF G ψ (t, y) + (ψ y : ℂ) * dsolE G t (dsolCut χ R) y :=
    fun y => dsol_pt_identity G t ψ (dsolCut χ R) y (hψdiff y) (hcdiff y)
  -- integrability of the two pieces
  have hf1 : Integrable (fun y : ℝ × ℝ => (dsolCut χ R y : ℂ) * dsolF G ψ (t, y)) := by
    refine Integrable.mono' hDint.norm ?_ (ae_of_all _ fun y =>
      dsol_mul_ofReal_norm_le (hcut01 y).1 (hcut01 y).2 _)
    exact (Complex.continuous_ofReal.comp hcd.continuous).aestronglyMeasurable.mul
      hDint.aestronglyMeasurable
  have hEm : AEStronglyMeasurable (dsolE G t (dsolCut χ R)) volume :=
    dsolE_aesm G t hgA hcd
  have hEb : ∀ y : ℝ × ℝ, ‖dsolE G t (dsolCut χ R) y‖ ≤ ‖G (t, y)‖ * (2 * (R⁻¹ * M)) := by
    intro y
    have h := dsol_pair_norm_le (G (t, y)) (fderiv ℝ (dsolCut χ R) y (1, 0))
      (fderiv ℝ (dsolCut χ R) y (0, 1))
    have h1 := dsolCut_fderiv_abs_le hχd hM hR y (1, 0) dsol_norm_e0_le
    have h2 := dsolCut_fderiv_abs_le hχd hM hR y (0, 1) dsol_norm_e1_le
    calc ‖dsolE G t (dsolCut χ R) y‖
        ≤ ‖G (t, y)‖ * (|fderiv ℝ (dsolCut χ R) y (1, 0)| + |fderiv ℝ (dsolCut χ R) y (0, 1)|) := h
      _ ≤ ‖G (t, y)‖ * (2 * (R⁻¹ * M)) :=
          mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  have hbound : ∀ y : ℝ × ℝ, ‖(ψ y : ℂ) * dsolE G t (dsolCut χ R) y‖ ≤
      (2 * C * M * R⁻¹) * (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := by
    intro y
    rw [norm_mul, Complex.norm_real]
    calc ‖ψ y‖ * ‖dsolE G t (dsolCut χ R) y‖
        ≤ (C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2))) * (‖G (t, y)‖ * (2 * (R⁻¹ * M))) :=
          mul_le_mul (hψb y) (hEb y) (norm_nonneg _) (le_trans (norm_nonneg _) (hψb y))
      _ = (2 * C * M * R⁻¹) * (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := by ring
  have hPsiE : Integrable (fun y : ℝ × ℝ => (ψ y : ℂ) * dsolE G t (dsolCut χ R) y) := by
    refine Integrable.mono' (hgI.const_mul (2 * C * M * R⁻¹)) ?_ (ae_of_all _ hbound)
    exact (Complex.continuous_ofReal.comp hψcont).aestronglyMeasurable.mul hEm
  -- the splitting of the integral against the test function
  have hsplit : ∫ y : ℝ × ℝ, dsolF G (fun z => dsolCut χ R z * ψ z) (t, y) =
      (∫ y : ℝ × ℝ, (dsolCut χ R y : ℂ) * dsolF G ψ (t, y)) +
        ∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y := by
    rw [← integral_add hf1 hPsiE]
    exact integral_congr_ae (ae_of_all _ hpt)
  have hcs : HasCompactSupport (fun z => dsolCut χ R z * ψ z) := hcc.mul_right
  have hzero := hZero (fun z => dsolCut χ R z * ψ z) (hcd.mul hψ) hcs
  have hsum : (∫ y : ℝ × ℝ, (dsolCut χ R y : ℂ) * dsolF G ψ (t, y)) +
      ∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y = 0 := by
    rw [← hsplit]
    exact hzero
  refine ⟨eq_neg_of_add_eq_zero_left hsum, ?_⟩
  have hint := norm_integral_le_of_norm_le (hgI.const_mul (2 * C * M * R⁻¹)) (ae_of_all _ hbound)
  rw [integral_const_mul] at hint
  calc ‖∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y‖
      ≤ (2 * C * M * R⁻¹) * ∫ y : ℝ × ℝ, Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖ := hint
    _ = (2 * C * M * ∫ y : ℝ × ℝ, Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) * R⁻¹ := by
        ring

/-! ## The target -/

/-- **Leaf `PartII-b:T12/6` (`DsolGaussExtend`).** If the slice `G(t, ·)` is weakly divergence free
against all `C_c^∞` tests and has Gaussian-weighted integrability, it is weakly divergence free
against every smooth `ψ` with `‖ψ y‖ + ‖Dψ y‖ ≤ C e^{-a|y|²}`. Proof: cutoffs `χ(R⁻¹ ·)`,
dominated convergence for `∫ χ_R D → ∫ D`, and the `O(R⁻¹)` bound on `∫ ψ G·∇χ_R`. -/
theorem dsolGaussExtend : DsolGaussExtend := by
  unfold DsolGaussExtend
  intro G t hZero hG ψ hψ hdec
  obtain ⟨a, C, ha, hC⟩ := hdec
  obtain ⟨χ, hχ, hχc, hχ01, hχ1⟩ := dsolBump_exists
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z, ‖fderiv ℝ χ z‖ ≤ M :=
    (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (HasCompactSupport.fderiv ℝ hχc)
  have hgA : AEStronglyMeasurable (fun y : ℝ × ℝ => G (t, y)) volume := dsol_gauss_aesm hG
  have hgI : Integrable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) :=
    dsol_gauss_norm_integrable hG ha
  have hψb : ∀ y : ℝ × ℝ, ‖ψ y‖ ≤ C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) := fun y => by
    have h1 := hC y
    have h2 := norm_nonneg (fderiv ℝ ψ y)
    linarith
  have hψdb : ∀ y : ℝ × ℝ, ‖fderiv ℝ ψ y‖ ≤ C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) :=
    fun y => by
    have h1 := hC y
    have h2 := norm_nonneg (ψ y)
    linarith
  have hfdc : Continuous (fun y => fderiv ℝ ψ y) := hψ.continuous_fderiv (by simp)
  -- the pairing `D = dsolF G ψ (t, ·)` is integrable
  have hDb : ∀ y : ℝ × ℝ, ‖dsolF G ψ (t, y)‖ ≤
      (2 * C) * (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := by
    intro y
    have h := dsol_pair_norm_le (G (t, y)) (fderiv ℝ ψ y (1, 0)) (fderiv ℝ ψ y (0, 1))
    have h1 := dsol_abs_fderiv_le ψ y (1, 0) dsol_norm_e0_le
    have h2 := dsol_abs_fderiv_le ψ y (0, 1) dsol_norm_e1_le
    have h3 := hψdb y
    calc ‖dsolF G ψ (t, y)‖
        ≤ ‖G (t, y)‖ * (|fderiv ℝ ψ y (1, 0)| + |fderiv ℝ ψ y (0, 1)|) := h
      _ ≤ ‖G (t, y)‖ * (2 * (C * Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)))) :=
          mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ = (2 * C) * (Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) := by ring
  have hDint : Integrable (fun y : ℝ × ℝ => dsolF G ψ (t, y)) := by
    refine Integrable.mono' (hgI.const_mul (2 * C)) ?_ (ae_of_all _ hDb)
    have hp : Continuous (fun y => fderiv ℝ ψ y (1, 0)) := hfdc.clm_apply continuous_const
    have hq : Continuous (fun y => fderiv ℝ ψ y (0, 1)) := hfdc.clm_apply continuous_const
    exact dsol_pair_aesm hgA hp hq
  -- the cutoff splitting and the O(R⁻¹) bound, for every scale R > 0
  have hstep : ∀ R : ℝ, 0 < R →
      ((∫ y : ℝ × ℝ, (dsolCut χ R y : ℂ) * dsolF G ψ (t, y) =
          -∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y) ∧
        ‖∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ R) y‖ ≤
          (2 * C * M * ∫ y : ℝ × ℝ, Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖) * R⁻¹) :=
    fun R hR => dsol_cut_step G t ψ hψ hZero χ hχ hχc hχ01 M hM a C hψb hgI hgA hDint hR
  -- dominated convergence: `∫ χ_R D → ∫ D` along `R = n + 1`
  have hFm : ∀ R : ℝ, AEStronglyMeasurable
      (fun y : ℝ × ℝ => (dsolCut χ R y : ℂ) * dsolF G ψ (t, y)) volume := fun R =>
    (Complex.continuous_ofReal.comp (dsolCut_contDiff hχ R).continuous).aestronglyMeasurable.mul
      hDint.aestronglyMeasurable
  have hcut01 : ∀ R y, 0 ≤ dsolCut χ R y ∧ dsolCut χ R y ≤ 1 := fun R y => hχ01 _
  have hDCT : Tendsto (fun n : ℕ => ∫ y : ℝ × ℝ, (dsolCut χ ((n : ℝ) + 1) y : ℂ) * dsolF G ψ (t, y))
      atTop (𝓝 (∫ y : ℝ × ℝ, dsolF G ψ (t, y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y : ℝ × ℝ => ‖dsolF G ψ (t, y)‖)
      (fun n => hFm ((n : ℝ) + 1)) hDint.norm
      (fun n => ae_of_all _ fun y =>
        dsol_mul_ofReal_norm_le (hcut01 ((n : ℝ) + 1) y).1 (hcut01 ((n : ℝ) + 1) y).2 _) ?_
    refine ae_of_all _ fun y => ?_
    have hev : ∀ᶠ n : ℕ in atTop,
        (dsolCut χ ((n : ℝ) + 1) y : ℂ) * dsolF G ψ (t, y) = dsolF G ψ (t, y) := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [dsolCut_eq_one (R := (n : ℝ) + 1) (y := y) hχ1 (by positivity) (by linarith),
        Complex.ofReal_one, one_mul]
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  -- the error term tends to zero along `R = n + 1`
  have hψE : Tendsto (fun n : ℕ => ∫ y : ℝ × ℝ, (ψ y : ℂ) * dsolE G t (dsolCut χ ((n : ℝ) + 1)) y)
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hbnd := hinv.const_mul
      (2 * C * M * ∫ y : ℝ × ℝ, Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖G (t, y)‖)
    rw [mul_zero] at hbnd
    exact squeeze_zero_norm (fun n => (hstep ((n : ℝ) + 1) (by positivity)).2) hbnd
  have hT0 : Tendsto
      (fun n : ℕ => ∫ y : ℝ × ℝ, (dsolCut χ ((n : ℝ) + 1) y : ℂ) * dsolF G ψ (t, y))
      atTop (𝓝 0) := by
    have h := hψE.neg
    rw [neg_zero] at h
    exact h.congr fun n => ((hstep ((n : ℝ) + 1) (by positivity)).1).symm
  exact tendsto_nhds_unique hDCT hT0

end UnforcedLeray.Short.IIb

end
