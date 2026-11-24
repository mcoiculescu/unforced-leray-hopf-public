import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound.SharpDecay
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# `PartIII-a:T21/c5/2/1/2`, helper: `D^#` is the planar adjoint of `D`

Source: `the November 2 reference manuscript` (SP), lines 2905-2912
(`D^# = Δ - ½ y·∇ + 1` is the dual of `D = Δ + ½ y·∇ + 2`).

`integral_dualGen_mul`: for a `C²` kernel `L` with bounded `0, 1, 2`-jets (the first one weighted by
`1 + |y|`) and a `C²` field `e` whose `0, 1, 2`-jets are bounded by a multiple of `e^{-|y|²/8}`
(the first two weighted by `1 + |y|`),
`∫ (D^# L) e = ∫ L (D e)` on the plane. Proof: two integrations by parts in each coordinate for
the Laplacian, one for the Euler term `y·∇`, using
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.OscGramIBP

/-- The Gaussian weight `e^{-|y|²/8}`. -/
def gw (y : ℝ × ℝ) : ℝ := Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)

theorem gw_pos (y : ℝ × ℝ) : 0 < gw y := Real.exp_pos _

theorem integrable_gw : Integrable gw := by
  have h := UnforcedLeray.Gaussian.integrable_gauss_plane (a := 2) (by norm_num)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [gw]
  norm_num

theorem integrable_of_le_gw {F : ℝ × ℝ → ℂ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ y, ‖F y‖ ≤ M * gw y) : Integrable F :=
  (integrable_gw.const_mul M).mono' hF.aestronglyMeasurable (Eventually.of_forall hM)

/-- `∂_w (z ↦ DF(z)[v]) = D²F(z)[w, v]` for `C²` `F`. -/
theorem fderiv_fderiv_apply_const {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 2 F) (x w v : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ F z v) x w = fderiv ℝ (fderiv ℝ F) x w v := by
  have hdF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h : HasFDerivAt (fun z => fderiv ℝ F z v) ((fderiv ℝ (fderiv ℝ F) x).flip v) x := by
    simpa using (hdF x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [h.fderiv, ContinuousLinearMap.flip_apply]

theorem norm_fderiv2_le (F : ℝ × ℝ → ℂ) (x w v : ℝ × ℝ) (hw : ‖w‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ F) x w v‖ ≤ ‖iteratedFDeriv ℝ 2 F x‖ := by
  have e : fderiv ℝ (fderiv ℝ F) x w v = iteratedFDeriv ℝ 2 F x ![w, v] := by
    simp [iteratedFDeriv_two_apply]
  rw [e]
  refine ((iteratedFDeriv ℝ 2 F x).le_opNorm _).trans ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 := norm_nonneg (iteratedFDeriv ℝ 2 F x)
  have h1 : ‖w‖ * ‖v‖ ≤ 1 := by
    nlinarith [norm_nonneg w, norm_nonneg v]
  nlinarith

theorem norm_ofReal_mul_le {t : ℝ} {a b : ℂ} :
    ‖((t : ℝ) : ℂ) * a * b‖ = |t| * ‖a‖ * ‖b‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- One coordinate direction `v` with coordinate functional `ℓ` (`ℓ v = 1`): the Laplacian part
`∫ ∂_v² L · e = ∫ L ∂_v² e` and the Euler part
`∫ ℓ ∂_v L · e = -∫ L e - ∫ L ℓ ∂_v e`, with the integrability of the four integrands. -/
theorem ibp_dir {L e : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) (he : ContDiff ℝ 2 e) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h0 : ∀ z, ‖L z‖ ≤ C) (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C)
    (he0 : ∀ y, (1 + ‖y‖) * ‖e y‖ ≤ B * gw y)
    (he1 : ∀ y, (1 + ‖y‖) * ‖fderiv ℝ e y‖ ≤ B * gw y)
    (he2 : ∀ y, ‖iteratedFDeriv ℝ 2 e y‖ ≤ B * gw y)
    (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) (ℓ : ℝ × ℝ →L[ℝ] ℝ) (hℓ : ∀ y, |ℓ y| ≤ ‖y‖) (hℓv : ℓ v = 1) :
    Integrable (fun y => fderiv ℝ (fun z => fderiv ℝ L z v) y v * e y) ∧
    Integrable (fun y => L y * fderiv ℝ (fun z => fderiv ℝ e z v) y v) ∧
    Integrable (fun y => ((ℓ y : ℝ) : ℂ) * fderiv ℝ L y v * e y) ∧
    Integrable (fun y => L y * (((ℓ y : ℝ) : ℂ) * fderiv ℝ e y v)) ∧
    (∫ y, fderiv ℝ (fun z => fderiv ℝ L z v) y v * e y) =
      (∫ y, L y * fderiv ℝ (fun z => fderiv ℝ e z v) y v) ∧
    (∫ y, ((ℓ y : ℝ) : ℂ) * fderiv ℝ L y v * e y) =
      -(∫ y, L y * e y) - ∫ y, L y * (((ℓ y : ℝ) : ℂ) * fderiv ℝ e y v) := by
  -- regularity
  have hLd : Differentiable ℝ L := hL.differentiable (by norm_num)
  have hed : Differentiable ℝ e := he.differentiable (by norm_num)
  have hL1 : ContDiff ℝ 1 (fderiv ℝ L) := hL.fderiv_right (m := 1) (by norm_num)
  have he1c : ContDiff ℝ 1 (fderiv ℝ e) := he.fderiv_right (m := 1) (by norm_num)
  have hdL : Differentiable ℝ (fun z => fderiv ℝ L z v) :=
    (hL1.differentiable (by norm_num)).clm_apply (differentiable_const v)
  have hde : Differentiable ℝ (fun z => fderiv ℝ e z v) :=
    (he1c.differentiable (by norm_num)).clm_apply (differentiable_const v)
  have cL : Continuous L := hL.continuous
  have ce : Continuous e := he.continuous
  have cdL : Continuous (fun z => fderiv ℝ L z v) := hL1.continuous.clm_apply continuous_const
  have cde : Continuous (fun z => fderiv ℝ e z v) := he1c.continuous.clm_apply continuous_const
  have eddL : (fun y => fderiv ℝ (fun z => fderiv ℝ L z v) y v) =
      fun y => fderiv ℝ (fderiv ℝ L) y v v := funext fun y => fderiv_fderiv_apply_const hL y v v
  have edde : (fun y => fderiv ℝ (fun z => fderiv ℝ e z v) y v) =
      fun y => fderiv ℝ (fderiv ℝ e) y v v := funext fun y => fderiv_fderiv_apply_const he y v v
  have cddL : Continuous (fun y => fderiv ℝ (fun z => fderiv ℝ L z v) y v) := by
    rw [eddL]
    exact ((hL1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply
      continuous_const
  have cdde : Continuous (fun y => fderiv ℝ (fun z => fderiv ℝ e z v) y v) := by
    rw [edde]
    exact ((he1c.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply
      continuous_const
  have cℓ : Continuous (fun y => ((ℓ y : ℝ) : ℂ)) := Complex.continuous_ofReal.comp ℓ.continuous
  -- pointwise bounds
  have bfL : ∀ y, ‖fderiv ℝ L y‖ ≤ C := fun y =>
    le_trans (by nlinarith [norm_nonneg (fderiv ℝ L y), norm_nonneg y]) (h1 y)
  have bdL : ∀ y, ‖fderiv ℝ L y v‖ ≤ C := fun y =>
    calc ‖fderiv ℝ L y v‖ ≤ ‖fderiv ℝ L y‖ * ‖v‖ := (fderiv ℝ L y).le_opNorm v
      _ ≤ ‖fderiv ℝ L y‖ := by nlinarith [norm_nonneg (fderiv ℝ L y), norm_nonneg v]
      _ ≤ C := bfL y
  have bℓdL : ∀ y, |ℓ y| * ‖fderiv ℝ L y v‖ ≤ C := fun y => by
    have h3 : ‖fderiv ℝ L y v‖ ≤ ‖fderiv ℝ L y‖ :=
      ((fderiv ℝ L y).le_opNorm v).trans (by nlinarith [norm_nonneg (fderiv ℝ L y), norm_nonneg v])
    calc |ℓ y| * ‖fderiv ℝ L y v‖ ≤ ‖y‖ * ‖fderiv ℝ L y‖ :=
          mul_le_mul (hℓ y) h3 (norm_nonneg _) (norm_nonneg _)
      _ ≤ (1 + ‖y‖) * ‖fderiv ℝ L y‖ := by nlinarith [norm_nonneg (fderiv ℝ L y)]
      _ ≤ C := h1 y
  have bddL : ∀ y, ‖fderiv ℝ (fun z => fderiv ℝ L z v) y v‖ ≤ C := fun y => by
    rw [fderiv_fderiv_apply_const hL]
    exact (norm_fderiv2_le L y v v hv hv).trans (h2 y)
  have bfe : ∀ y, ‖fderiv ℝ e y‖ ≤ B * gw y := fun y =>
    le_trans (by nlinarith [norm_nonneg (fderiv ℝ e y), norm_nonneg y]) (he1 y)
  have be : ∀ y, ‖e y‖ ≤ B * gw y := fun y =>
    le_trans (by nlinarith [norm_nonneg (e y), norm_nonneg y]) (he0 y)
  have bℓe : ∀ y, |ℓ y| * ‖e y‖ ≤ B * gw y := fun y =>
    calc |ℓ y| * ‖e y‖ ≤ ‖y‖ * ‖e y‖ := mul_le_mul_of_nonneg_right (hℓ y) (norm_nonneg _)
      _ ≤ (1 + ‖y‖) * ‖e y‖ := by nlinarith [norm_nonneg (e y)]
      _ ≤ B * gw y := he0 y
  have bde : ∀ y, ‖fderiv ℝ e y v‖ ≤ B * gw y := fun y =>
    calc ‖fderiv ℝ e y v‖ ≤ ‖fderiv ℝ e y‖ * ‖v‖ := (fderiv ℝ e y).le_opNorm v
      _ ≤ ‖fderiv ℝ e y‖ := by nlinarith [norm_nonneg (fderiv ℝ e y), norm_nonneg v]
      _ ≤ B * gw y := bfe y
  have bℓde : ∀ y, |ℓ y| * ‖fderiv ℝ e y v‖ ≤ B * gw y := fun y => by
    have h3 : ‖fderiv ℝ e y v‖ ≤ ‖fderiv ℝ e y‖ :=
      ((fderiv ℝ e y).le_opNorm v).trans (by nlinarith [norm_nonneg (fderiv ℝ e y), norm_nonneg v])
    calc |ℓ y| * ‖fderiv ℝ e y v‖ ≤ ‖y‖ * ‖fderiv ℝ e y‖ :=
          mul_le_mul (hℓ y) h3 (norm_nonneg _) (norm_nonneg _)
      _ ≤ (1 + ‖y‖) * ‖fderiv ℝ e y‖ := by nlinarith [norm_nonneg (fderiv ℝ e y)]
      _ ≤ B * gw y := he1 y
  have bdde : ∀ y, ‖fderiv ℝ (fun z => fderiv ℝ e z v) y v‖ ≤ B * gw y := fun y => by
    rw [fderiv_fderiv_apply_const he]
    exact (norm_fderiv2_le e y v v hv hv).trans (he2 y)
  have hgw : ∀ y, 0 ≤ gw y := fun y => (gw_pos y).le
  -- the integrands
  have iA : Integrable (fun y => fderiv ℝ (fun z => fderiv ℝ L z v) y v * e y) :=
    integrable_of_le_gw (cddL.mul ce) (M := C * B) fun y => by
      rw [norm_mul]
      nlinarith [mul_le_mul (bddL y) (be y) (norm_nonneg _) hC, hgw y]
  have iA' : Integrable (fun y => L y * fderiv ℝ (fun z => fderiv ℝ e z v) y v) :=
    integrable_of_le_gw (cL.mul cdde) (M := C * B) fun y => by
      rw [norm_mul]
      nlinarith [mul_le_mul (h0 y) (bdde y) (norm_nonneg _) hC, hgw y]
  have iK : Integrable (fun y => ((ℓ y : ℝ) : ℂ) * fderiv ℝ L y v * e y) :=
    integrable_of_le_gw ((cℓ.mul cdL).mul ce) (M := C * B) fun y => by
      rw [norm_ofReal_mul_le]
      nlinarith [mul_le_mul (bℓdL y) (be y) (norm_nonneg _) hC, hgw y]
  have iJ : Integrable (fun y => L y * (((ℓ y : ℝ) : ℂ) * fderiv ℝ e y v)) :=
    integrable_of_le_gw (cL.mul (cℓ.mul cde)) (M := C * B) fun y => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [mul_le_mul (h0 y) (bℓde y) (by positivity) hC, hgw y]
  have iC : Integrable (fun y => fderiv ℝ L y v * fderiv ℝ e y v) :=
    integrable_of_le_gw (cdL.mul cde) (M := C * B) fun y => by
      rw [norm_mul]
      nlinarith [mul_le_mul (bdL y) (bde y) (norm_nonneg _) hC, hgw y]
  have iD : Integrable (fun y => fderiv ℝ L y v * e y) :=
    integrable_of_le_gw (cdL.mul ce) (M := C * B) fun y => by
      rw [norm_mul]
      nlinarith [mul_le_mul (bdL y) (be y) (norm_nonneg _) hC, hgw y]
  have iF : Integrable (fun y => L y * fderiv ℝ e y v) :=
    integrable_of_le_gw (cL.mul cde) (M := C * B) fun y => by
      rw [norm_mul]
      nlinarith [mul_le_mul (h0 y) (bde y) (norm_nonneg _) hC, hgw y]
  have iE : Integrable (fun y => L y * e y) :=
    integrable_of_le_gw (cL.mul ce) (M := C * B) fun y => by
      rw [norm_mul]
      nlinarith [mul_le_mul (h0 y) (be y) (norm_nonneg _) hC, hgw y]
  have iG : Integrable (fun y => fderiv ℝ L y v * (((ℓ y : ℝ) : ℂ) * e y)) :=
    integrable_of_le_gw (cdL.mul (cℓ.mul ce)) (M := C * B) fun y => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [mul_le_mul (bdL y) (bℓe y) (by positivity) hC, hgw y]
  have iI : Integrable (fun y => L y * (((ℓ y : ℝ) : ℂ) * e y)) :=
    integrable_of_le_gw (cL.mul (cℓ.mul ce)) (M := C * B) fun y => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [mul_le_mul (h0 y) (bℓe y) (by positivity) hC, hgw y]
  -- the product rule for `ℓ e`
  have hev : ∀ x, HasFDerivAt (fun y => ((ℓ y : ℝ) : ℂ) * e y)
      (((ℓ x : ℝ) : ℂ) • fderiv ℝ e x + e x • (Complex.ofRealCLM.comp ℓ)) x := by
    intro x
    have hc : HasFDerivAt (fun y => ((ℓ y : ℝ) : ℂ)) (Complex.ofRealCLM.comp ℓ) x :=
      (Complex.ofRealCLM.comp ℓ).hasFDerivAt
    exact hc.mul (hed x).hasFDerivAt
  have hevv : ∀ x, fderiv ℝ (fun y => ((ℓ y : ℝ) : ℂ) * e y) x v =
      e x + ((ℓ x : ℝ) : ℂ) * fderiv ℝ e x v := by
    intro x
    rw [(hev x).fderiv]
    simp [hℓv]
    ring
  have iH : Integrable (fun y => L y * fderiv ℝ (fun y => ((ℓ y : ℝ) : ℂ) * e y) y v) := by
    refine (iE.add iJ).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    rw [hevv y]
    ring
  -- the three integrations by parts
  have ibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
    (f := fun z => fderiv ℝ L z v) (g := e) iA iC iD (fun x _ => hdL x) (fun x _ => hed x)
  have ibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
    (f := L) (g := fun z => fderiv ℝ e z v) iC iA' iF (fun x _ => hLd x) (fun x _ => hde x)
  have ibp3 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
    (f := L) (g := fun y => ((ℓ y : ℝ) : ℂ) * e y) iG iH iI (fun x _ => hLd x)
    (fun x _ => (hev x).differentiableAt)
  have l3 : (∫ x, L x * fderiv ℝ (fun y => ((ℓ y : ℝ) : ℂ) * e y) x v) =
      (∫ x, L x * e x) + ∫ x, L x * (((ℓ x : ℝ) : ℂ) * fderiv ℝ e x v) := by
    rw [← integral_add iE iJ]
    congr 1
    funext x
    rw [hevv x]
    ring
  have r3 : (∫ x, fderiv ℝ L x v * (((ℓ x : ℝ) : ℂ) * e x)) =
      ∫ x, ((ℓ x : ℝ) : ℂ) * fderiv ℝ L x v * e x := by
    congr 1
    funext x
    ring
  rw [l3, r3] at ibp3
  refine ⟨iA, iA', iK, iJ, ?_, ?_⟩
  · linear_combination ibp1 - ibp2
  · linear_combination ibp3

/-- **`D^#` is the planar adjoint of `D`** (SP 2905-2912): `∫ (D^# L) e = ∫ L (D e)`. -/
theorem integral_dualGen_mul {L e : ℝ × ℝ → ℂ} (hL : ContDiff ℝ 2 L) (he : ContDiff ℝ 2 e)
    {C B : ℝ}
    (h0 : ∀ z, ‖L z‖ ≤ C) (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ L z‖ ≤ C)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 L z‖ ≤ C)
    (he0 : ∀ y, (1 + ‖y‖) * ‖e y‖ ≤ B * gw y)
    (he1 : ∀ y, (1 + ‖y‖) * ‖fderiv ℝ e y‖ ≤ B * gw y)
    (he2 : ∀ y, ‖iteratedFDeriv ℝ 2 e y‖ ≤ B * gw y) :
    ∫ y, Gaussian.dualGen L y * e y = ∫ y, L y * movD e y := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (h0 0)
  have hB : 0 ≤ B := by
    by_contra hneg
    push_neg at hneg
    have h := he0 0
    have := mul_neg_of_neg_of_pos hneg (gw_pos 0)
    nlinarith [norm_nonneg (e 0), norm_nonneg (0 : ℝ × ℝ)]
  set v₀ : ℝ × ℝ := B0579.dir 0 with hv₀
  set v₁ : ℝ × ℝ := B0579.dir 1 with hv₁
  have hv₀n : ‖v₀‖ ≤ 1 := by simp [hv₀, B0579.dir]
  have hv₁n : ‖v₁‖ ≤ 1 := by simp [hv₁, B0579.dir]
  set ℓ₀ : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ with hℓ₀
  set ℓ₁ : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ with hℓ₁
  have hℓ₀b : ∀ y : ℝ × ℝ, |ℓ₀ y| ≤ ‖y‖ := fun y => by
    simpa [hℓ₀, Real.norm_eq_abs] using norm_fst_le y
  have hℓ₁b : ∀ y : ℝ × ℝ, |ℓ₁ y| ≤ ‖y‖ := fun y => by
    simpa [hℓ₁, Real.norm_eq_abs] using norm_snd_le y
  have hℓ₀v : ℓ₀ v₀ = 1 := by simp [hℓ₀, hv₀, B0579.dir]
  have hℓ₁v : ℓ₁ v₁ = 1 := by simp [hℓ₁, hv₁, B0579.dir]
  obtain ⟨iA₀, iA'₀, iK₀, iJ₀, eA₀, eK₀⟩ :=
    ibp_dir hL he hC hB h0 h1 h2 he0 he1 he2 v₀ hv₀n ℓ₀ hℓ₀b hℓ₀v
  obtain ⟨iA₁, iA'₁, iK₁, iJ₁, eA₁, eK₁⟩ :=
    ibp_dir hL he hC hB h0 h1 h2 he0 he1 he2 v₁ hv₁n ℓ₁ hℓ₁b hℓ₁v
  have iE : Integrable (fun y => L y * e y) := by
    refine integrable_of_le_gw (hL.continuous.mul he.continuous) (M := C * B) fun y => ?_
    rw [norm_mul]
    have be : ‖e y‖ ≤ B * gw y :=
      le_trans (by nlinarith [norm_nonneg (e y), norm_nonneg y]) (he0 y)
    nlinarith [mul_le_mul (h0 y) be (norm_nonneg _) hC, (gw_pos y).le]
  -- pointwise forms
  have hyv : ∀ y : ℝ × ℝ, y = y.1 • v₀ + y.2 • v₁ := fun y => by
    ext <;> simp [hv₀, hv₁, B0579.dir]
  have hdual : ∀ y, Gaussian.dualGen L y * e y =
      fderiv ℝ (fun z => fderiv ℝ L z v₀) y v₀ * e y +
        fderiv ℝ (fun z => fderiv ℝ L z v₁) y v₁ * e y +
        (-(2 : ℂ)⁻¹) * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ L y v₀ * e y) +
        (-(2 : ℂ)⁻¹) * (((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ L y v₁ * e y) +
        L y * e y := by
    intro y
    have hlap : Cyl.laplacian L y = fderiv ℝ (fun z => fderiv ℝ L z v₀) y v₀ +
        fderiv ℝ (fun z => fderiv ℝ L z v₁) y v₁ := by
      rw [← ComplCouplingHeat.ladLapCx_eq_cyl_laplacian hL y]
      rfl
    have hdil : fderiv ℝ L y y = ((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ L y v₀ +
        ((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ L y v₁ := by
      calc fderiv ℝ L y y = fderiv ℝ L y (y.1 • v₀ + y.2 • v₁) := congrArg _ (hyv y)
        _ = _ := by
          rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
          rfl
    unfold Gaussian.dualGen
    rw [hlap, hdil, Complex.real_smul]
    push_cast
    ring
  have hmov : ∀ y, L y * movD e y =
      L y * fderiv ℝ (fun z => fderiv ℝ e z v₀) y v₀ +
        L y * fderiv ℝ (fun z => fderiv ℝ e z v₁) y v₁ +
        (2 : ℂ)⁻¹ * (L y * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ e y v₀)) +
        (2 : ℂ)⁻¹ * (L y * (((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ e y v₁)) +
        2 * (L y * e y) := by
    intro y
    have h1' : ladLapCx e y = fderiv ℝ (fun z => fderiv ℝ e z v₀) y v₀ +
        fderiv ℝ (fun z => fderiv ℝ e z v₁) y v₁ := rfl
    have h2' : pdCx 0 e y = fderiv ℝ e y v₀ := rfl
    have h3' : pdCx 1 e y = fderiv ℝ e y v₁ := rfl
    have h4' : ((ℓ₀ y : ℝ) : ℂ) = ((y.1 : ℝ) : ℂ) := rfl
    have h5' : ((ℓ₁ y : ℝ) : ℂ) = ((y.2 : ℝ) : ℂ) := rfl
    unfold movD
    rw [h1', h2', h3', h4', h5']
    ring
  have eL : (∫ y, Gaussian.dualGen L y * e y) =
      (∫ y, fderiv ℝ (fun z => fderiv ℝ L z v₀) y v₀ * e y) +
        (∫ y, fderiv ℝ (fun z => fderiv ℝ L z v₁) y v₁ * e y) +
        (-(2 : ℂ)⁻¹) * (∫ y, ((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ L y v₀ * e y) +
        (-(2 : ℂ)⁻¹) * (∫ y, ((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ L y v₁ * e y) +
        ∫ y, L y * e y := by
    rw [integral_congr_ae (Eventually.of_forall hdual)]
    have j1 : Integrable (fun y => fderiv ℝ (fun z => fderiv ℝ L z v₀) y v₀ * e y +
        fderiv ℝ (fun z => fderiv ℝ L z v₁) y v₁ * e y) := iA₀.add iA₁
    have j2 : Integrable (fun y => fderiv ℝ (fun z => fderiv ℝ L z v₀) y v₀ * e y +
        fderiv ℝ (fun z => fderiv ℝ L z v₁) y v₁ * e y +
        (-(2 : ℂ)⁻¹) * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ L y v₀ * e y)) :=
      j1.add (iK₀.const_mul _)
    have j3 : Integrable (fun y => fderiv ℝ (fun z => fderiv ℝ L z v₀) y v₀ * e y +
        fderiv ℝ (fun z => fderiv ℝ L z v₁) y v₁ * e y +
        (-(2 : ℂ)⁻¹) * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ L y v₀ * e y) +
        (-(2 : ℂ)⁻¹) * (((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ L y v₁ * e y)) :=
      j2.add (iK₁.const_mul _)
    rw [integral_add j3 iE, integral_add j2 (iK₁.const_mul _), integral_add j1 (iK₀.const_mul _),
      integral_add iA₀ iA₁, integral_const_mul, integral_const_mul]
  have eR : (∫ y, L y * movD e y) =
      (∫ y, L y * fderiv ℝ (fun z => fderiv ℝ e z v₀) y v₀) +
        (∫ y, L y * fderiv ℝ (fun z => fderiv ℝ e z v₁) y v₁) +
        (2 : ℂ)⁻¹ * (∫ y, L y * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ e y v₀)) +
        (2 : ℂ)⁻¹ * (∫ y, L y * (((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ e y v₁)) +
        2 * ∫ y, L y * e y := by
    rw [integral_congr_ae (Eventually.of_forall hmov)]
    have j1 : Integrable (fun y => L y * fderiv ℝ (fun z => fderiv ℝ e z v₀) y v₀ +
        L y * fderiv ℝ (fun z => fderiv ℝ e z v₁) y v₁) := iA'₀.add iA'₁
    have j2 : Integrable (fun y => L y * fderiv ℝ (fun z => fderiv ℝ e z v₀) y v₀ +
        L y * fderiv ℝ (fun z => fderiv ℝ e z v₁) y v₁ +
        (2 : ℂ)⁻¹ * (L y * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ e y v₀))) :=
      j1.add (iJ₀.const_mul _)
    have j3 : Integrable (fun y => L y * fderiv ℝ (fun z => fderiv ℝ e z v₀) y v₀ +
        L y * fderiv ℝ (fun z => fderiv ℝ e z v₁) y v₁ +
        (2 : ℂ)⁻¹ * (L y * (((ℓ₀ y : ℝ) : ℂ) * fderiv ℝ e y v₀)) +
        (2 : ℂ)⁻¹ * (L y * (((ℓ₁ y : ℝ) : ℂ) * fderiv ℝ e y v₁))) :=
      j2.add (iJ₁.const_mul _)
    rw [integral_add j3 (iE.const_mul _), integral_add j2 (iJ₁.const_mul _),
      integral_add j1 (iJ₀.const_mul _), integral_add iA'₀ iA'₁,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [eL, eR, eA₀, eA₁, eK₀, eK₁]
  ring

end UnforcedLeray.Short.IIIa.OscGramIBP
