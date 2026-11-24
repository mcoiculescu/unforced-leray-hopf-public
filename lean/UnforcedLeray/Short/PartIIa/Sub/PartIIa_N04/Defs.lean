import UnforcedLeray.Short.PartIIa.StatementsNear
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison
import UnforcedLeray.Short.PartIIa.Tasks.N03AdjointGeneratorDiff
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem

/-!


Source of record: `the November 2 reference manuscript`,
lines 1800–1869 (Lemma `near:adjoint-polynomial` and Lemma `near:smooth-adjoint-comparison`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-! ### 1. Concrete differential operators for the adjoint comparison -/

/-- `Λ = K + 1 = 2S + η ∂_η + 1` on profiles (source line 1824). -/
def opLam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Profile → E) :
    Profile → E := fun p => opK f p + f p

/-- The meridional radial selector `E(v_r, v_z) = (v_r, 0)` (source line 1840). -/
def opE (f : Profile → MeridC) : Profile → MeridC := fun p => !₂[f p 0, 0]

/-- First-order coefficient `ν s Λ(∂_q v)` of the generator difference `A_ε* - A_0*`
(source line 1839). -/
def genDiff1 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC := fun p =>
  (ν * p.1) • opLam (pdQ v) p

/-- Second-order coefficient `ν s (Λ² v - E v)` of the generator difference `A_ε* - A_0*`
(source line 1839). -/
def genDiff2 (ν : ℝ) (v : Profile → MeridC) : Profile → MeridC := fun p =>
  (ν * p.1) • (opLam (opLam v) p - opE v p)

/-- Exact generator difference `(A_ε* - A_0*) v = -2ε genDiff1 ν v + ε² genDiff2 ν v`
(source lines 1838–1840). -/
def genDiffC (ν ε : ℝ) (v : Profile → MeridC) : Profile → MeridC := fun p =>
  ((-2 * ε : ℝ) : ℂ) • genDiff1 ν v p + ((ε ^ 2 : ℝ) : ℂ) • genDiff2 ν v p

/-- Unscaled tensor `((K + 1) v_r, (K + 1) v_z, 0, -v_r)` from integrating `s(div_ε - div_0)`
by parts against `v` on `H` (source line 1859). -/
def gradDiff1 (v : Profile → MeridC) : Profile → TensorVal := fun p =>
  WithLp.toLp 2 ![opLam (fun q => v q 0) p, opLam (fun q => v q 1) p, 0, -(v p 0)]

/-- Scaled tensor `ε ((K + 1) v_r, (K + 1) v_z, 0, -v_r)` in `H_T` (source line 1859). -/
def gradDiff (ε : ℝ) (v : Profile → MeridC) : Profile → TensorVal := fun p =>
  ((ε : ℝ) : ℂ) • gradDiff1 v p

/-! ### 2. Pointwise identities for `div_ε - div_0`, `genDiffC`, and `gradDiff` -/

theorem opQ_sub_opQ_zero (ε : ℝ) (f : Profile → ℂ) (p : Profile) :
    opQ ε f p - opQ 0 f p = -((ε : ℝ) : ℂ) * opLam f p := by
  simp only [opQ, opLam, Complex.real_smul, zero_smul, sub_zero]
  ring

theorem divEps_sub_divEps_zero (ε : ℝ) (M : Profile → TensorVal) (p : Profile) :
    divEps ε M p - divEps 0 M p =
      !₂[-((ε : ℝ) : ℂ) * opLam (fun q => M q 0) p - ((ε : ℝ) : ℂ) * M p 3,
        -((ε : ℝ) : ℂ) * opLam (fun q => M q 1) p] := by
  ext i
  fin_cases i
  · change (opQ ε (fun q => M q 0) p + pdEta (fun q => M q 1) p - (ε : ℂ) * M p 3) -
        (opQ 0 (fun q => M q 0) p + pdEta (fun q => M q 1) p - ((0 : ℝ) : ℂ) * M p 3) =
      -((ε : ℝ) : ℂ) * opLam (fun q => M q 0) p - ((ε : ℝ) : ℂ) * M p 3
    have h0 := opQ_sub_opQ_zero ε (fun q => M q 0) p
    push_cast at h0 ⊢
    linear_combination h0
  · change (opQ ε (fun q => M q 1) p + pdEta (fun q => M q 2) p) -
        (opQ 0 (fun q => M q 1) p + pdEta (fun q => M q 2) p) =
      -((ε : ℝ) : ℂ) * opLam (fun q => M q 1) p
    have h1 := opQ_sub_opQ_zero ε (fun q => M q 1) p
    push_cast at h1 ⊢
    linear_combination h1

theorem s_smul_divEps_sub (ε : ℝ) (M : Profile → TensorVal) (p : Profile) :
    (p.1 : ℂ) • divEps ε M p - (p.1 : ℂ) • divEps 0 M p =
      (p.1 : ℂ) • !₂[-((ε : ℝ) : ℂ) * opLam (fun q => M q 0) p - ((ε : ℝ) : ℂ) * M p 3,
        -((ε : ℝ) : ℂ) * opLam (fun q => M q 1) p] := by
  rw [← smul_sub, divEps_sub_divEps_zero]

/-! ### 3. `L²` membership and `O(√ε)` norm bounds for `genDiffC` and `gradDiff` -/

theorem eps_le_sqrt_eps {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : ε ≤ Real.sqrt ε := by
  calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε0).symm
    _ ≤ Real.sqrt ε * 1 := by
      gcongr
      exact Real.sqrt_le_one.mpr hε1
    _ = Real.sqrt ε := mul_one _

theorem eps_sq_le_sqrt_eps {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : ε ^ 2 ≤ Real.sqrt ε := by
  calc ε ^ 2 = ε * ε := sq ε
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε0
    _ = ε := mul_one ε
    _ ≤ Real.sqrt ε := eps_le_sqrt_eps hε0 hε1

theorem memLp_genDiffC {c ν : ℝ} {v : Profile → MeridC}
    (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
    (h2 : MemLp (genDiff2 ν v) 2 (measureH c)) (ε : ℝ) :
    MemLp (genDiffC ν ε v) 2 (measureH c) :=
  (h1.const_smul ((-2 * ε : ℝ) : ℂ)).add (h2.const_smul ((ε ^ 2 : ℝ) : ℂ))

theorem toLp_genDiffC {c ν : ℝ} {v : Profile → MeridC}
    (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
    (h2 : MemLp (genDiff2 ν v) 2 (measureH c)) (ε : ℝ) :
    (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v) =
      ((-2 * ε : ℝ) : ℂ) • h1.toLp (genDiff1 ν v) +
        ((ε ^ 2 : ℝ) : ℂ) • h2.toLp (genDiff2 ν v) := by
  apply Lp.ext
  filter_upwards [(memLp_genDiffC h1 h2 ε).coeFn_toLp,
    Lp.coeFn_add (((-2 * ε : ℝ) : ℂ) • h1.toLp (genDiff1 ν v))
      (((ε ^ 2 : ℝ) : ℂ) • h2.toLp (genDiff2 ν v)),
    Lp.coeFn_smul ((-2 * ε : ℝ) : ℂ) (h1.toLp (genDiff1 ν v)),
    Lp.coeFn_smul ((ε ^ 2 : ℝ) : ℂ) (h2.toLp (genDiff2 ν v)),
    h1.coeFn_toLp, h2.coeFn_toLp] with p hp hadd hsm1 hsm2 hp1 hp2
  simp only [hp, hadd, Pi.add_apply, hsm1, hsm2, Pi.smul_apply, hp1, hp2, genDiffC]

theorem norm_genDiffC_le {c ν ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {v : Profile → MeridC}
    (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
    (h2 : MemLp (genDiff2 ν v) 2 (measureH c)) :
    ‖(memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)‖ ≤
      2 * Real.sqrt ε * (‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖) := by
  rw [toLp_genDiffC h1 h2 ε]
  have hsq1 := eps_le_sqrt_eps hε0.le hε1
  have hsq2 := eps_sq_le_sqrt_eps hε0.le hε1
  have hn1 : ‖((-2 * ε : ℝ) : ℂ) • h1.toLp (genDiff1 ν v)‖ ≤
      2 * Real.sqrt ε * ‖h1.toLp (genDiff1 ν v)‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_neg (by norm_num),
      abs_of_pos hε0]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hn2 : ‖((ε ^ 2 : ℝ) : ℂ) • h2.toLp (genDiff2 ν v)‖ ≤
      2 * Real.sqrt ε * ‖h2.toLp (genDiff2 ν v)‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε)]
    have h2sq : ε ^ 2 ≤ 2 * Real.sqrt ε := by linarith [Real.sqrt_nonneg ε]
    exact mul_le_mul_of_nonneg_right h2sq (norm_nonneg _)
  calc ‖((-2 * ε : ℝ) : ℂ) • h1.toLp (genDiff1 ν v) +
          ((ε ^ 2 : ℝ) : ℂ) • h2.toLp (genDiff2 ν v)‖
      ≤ ‖((-2 * ε : ℝ) : ℂ) • h1.toLp (genDiff1 ν v)‖ +
          ‖((ε ^ 2 : ℝ) : ℂ) • h2.toLp (genDiff2 ν v)‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt ε * ‖h1.toLp (genDiff1 ν v)‖ +
          2 * Real.sqrt ε * ‖h2.toLp (genDiff2 ν v)‖ := add_le_add hn1 hn2
    _ = 2 * Real.sqrt ε * (‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖) := by ring

theorem memLp_gradDiff {c : ℝ} {v : Profile → MeridC}
    (hgd : MemLp (gradDiff1 v) 2 (measureHT c)) (ε : ℝ) :
    MemLp (gradDiff ε v) 2 (measureHT c) :=
  hgd.const_smul ((ε : ℝ) : ℂ)

theorem toLp_gradDiff {c : ℝ} {v : Profile → MeridC}
    (hgd : MemLp (gradDiff1 v) 2 (measureHT c)) (ε : ℝ) :
    (memLp_gradDiff hgd ε).toLp (gradDiff ε v) =
      ((ε : ℝ) : ℂ) • hgd.toLp (gradDiff1 v) := by
  apply Lp.ext
  filter_upwards [(memLp_gradDiff hgd ε).coeFn_toLp,
    Lp.coeFn_smul ((ε : ℝ) : ℂ) (hgd.toLp (gradDiff1 v)),
    hgd.coeFn_toLp] with p hp hsm hp1
  simp only [hp, hsm, Pi.smul_apply, hp1, gradDiff]

theorem norm_gradDiff_le {c ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {v : Profile → MeridC}
    (hgd : MemLp (gradDiff1 v) 2 (measureHT c)) :
    ‖(memLp_gradDiff hgd ε).toLp (gradDiff ε v)‖ ≤
      Real.sqrt ε * ‖hgd.toLp (gradDiff1 v)‖ := by
  rw [toLp_gradDiff hgd ε, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
  exact mul_le_mul_of_nonneg_right (eps_le_sqrt_eps hε0.le hε1) (norm_nonneg _)

/-! ### 4. `GammaBox` dominance and `h6Norm` non-negativity -/

theorem h6Norm_nonneg (c : ℝ) (z : Profile → MeridC) : 0 ≤ h6Norm c z := by
  unfold h6Norm
  refine Finset.sum_nonneg fun k _ => ?_
  exact Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _

theorem one_le_GammaBox {ν c σ H1 L1 M γs : ℝ} (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) :
    1 ≤ GammaBox ν c σ H1 L1 M γs := by
  unfold GammaBox
  have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have h2 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have h3 : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have h4 : 0 ≤ γs⁻¹ := inv_nonneg.mpr hγs.le
  linarith

theorem GammaBox_nonneg {ν c σ H1 L1 M γs : ℝ} (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) :
    0 ≤ GammaBox ν c σ H1 L1 M γs :=
  zero_le_one.trans (one_le_GammaBox hν hc hσ hσH1 hL1 hM hγs)

theorem inv_gammas_le_GammaBox (ν c σ H1 L1 M γs : ℝ) (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) :
    γs⁻¹ ≤ GammaBox ν c σ H1 L1 M γs := by
  unfold GammaBox
  have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have h2 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have h3 : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  linarith

theorem one_add_c_add_inv_c_le_GammaBox (ν c σ H1 L1 M γs : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) :
    1 + c + c⁻¹ ≤ GammaBox ν c σ H1 L1 M γs := by
  unfold GammaBox
  have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have h3 : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have h4 : 0 ≤ γs⁻¹ := inv_nonneg.mpr hγs.le
  linarith

theorem one_add_sigma_H1_L1_le_GammaBox (ν c σ H1 L1 M γs : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (hM : 0 ≤ M) (hγs : 0 < γs) :
    1 + σ⁻¹ + H1 + L1 ≤ GammaBox ν c σ H1 L1 M γs := by
  unfold GammaBox
  have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have h2 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have h4 : 0 ≤ γs⁻¹ := inv_nonneg.mpr hγs.le
  linarith

theorem one_add_M_add_inv_gammas_le_GammaBox (ν c σ H1 L1 M γs : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) :
    1 + M + γs⁻¹ ≤ GammaBox ν c σ H1 L1 M γs := by
  unfold GammaBox
  have h1 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have h2 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have h3 : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  linarith

theorem inv_sqrt_nu_le_GammaBox {ν c σ H1 L1 M γs : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) :
    ν ^ (-(1 / 2 : ℝ)) ≤ GammaBox ν c σ H1 L1 M γs := by
  have hle : ν ^ (-(1 / 2 : ℝ)) ≤ 1 + ν⁻¹ := by
    rcases le_total ν 1 with hν1 | h1ν
    · have hr := Real.rpow_le_rpow_of_exponent_ge hν hν1
        (show (-1 : ℝ) ≤ -(1 / 2 : ℝ) by norm_num)
      rw [Real.rpow_neg_one] at hr
      linarith
    · have hr := Real.rpow_le_one_of_one_le_of_nonpos h1ν
        (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
      have hinv : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
      linarith
  unfold GammaBox
  have h2 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have h3 : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have h4 : 0 ≤ γs⁻¹ := inv_nonneg.mpr hγs.le
  linarith

theorem GammaBox_pow_mono {ν c σ H1 L1 M γs : ℝ} (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ)
    (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM : 0 ≤ M) (hγs : 0 < γs) {j k : ℕ} (hjk : j ≤ k) :
    GammaBox ν c σ H1 L1 M γs ^ j ≤ GammaBox ν c σ H1 L1 M γs ^ k :=
  pow_le_pow_right₀ (one_le_GammaBox hν hc hσ hσH1 hL1 hM hγs) hjk

/-! ### 5. Dense smooth-tensor duality and stress-map adjoint decomposition -/

/-- By density of smooth tensor tests in `HTSpace c` (`Masked.tensorTestDense`), a vector
`Y : HTSpace c` whose inner product with every smooth tensor test representative `F` is bounded
by `B * ‖F‖` has norm at most `B`. -/
theorem norm_le_of_isTensorTest_inner {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (Y : HTSpace c)
    (hY : ∀ (M : Profile → TensorVal) (F : HTSpace c), IsTensorTest c M →
      (F : Profile → TensorVal) =ᵐ[measureHT c] M → ‖inner ℂ F Y‖ ≤ B * ‖F‖) :
    ‖Y‖ ≤ B := by
  have hsq : ‖Y‖ ^ 2 ≤ B * ‖Y‖ := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hden : 0 < B + ‖Y‖ + 1 := by positivity
    set η : ℝ := δ / (B + ‖Y‖ + 1)
    have hη : 0 < η := div_pos hδ hden
    obtain ⟨M, hMt, hM, hdist⟩ :=
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDense c hc Y η hη
    set F : HTSpace c := hM.toLp M
    have hFM : (F : Profile → TensorVal) =ᵐ[measureHT c] M := hM.coeFn_toLp
    have hFY : ‖inner ℂ F Y‖ ≤ B * ‖F‖ := hY M F hMt hFM
    have hFnorm : ‖F‖ ≤ ‖Y‖ + η := by
      have h1 : ‖F‖ = ‖Y - (Y - F)‖ := by rw [sub_sub_cancel]
      rw [h1]
      exact (norm_sub_le Y (Y - F)).trans (by linarith)
    have hYY : ‖Y‖ ^ 2 ≤ ‖Y - F‖ * ‖Y‖ + ‖inner ℂ F Y‖ := by
      have hid : inner ℂ Y Y = inner ℂ (Y - F) Y + inner ℂ F Y := by
        rw [inner_sub_left, sub_add_cancel]
      have hn : ‖inner ℂ Y Y‖ = ‖Y‖ ^ 2 := by
        simp [inner_self_eq_norm_sq_to_K]
      calc ‖Y‖ ^ 2 = ‖inner ℂ Y Y‖ := hn.symm
        _ = ‖inner ℂ (Y - F) Y + inner ℂ F Y‖ := by rw [hid]
        _ ≤ ‖inner ℂ (Y - F) Y‖ + ‖inner ℂ F Y‖ := norm_add_le _ _
        _ ≤ ‖Y - F‖ * ‖Y‖ + ‖inner ℂ F Y‖ := by
          gcongr
          exact norm_inner_le_norm (Y - F) Y
    have hηB : η * (B + ‖Y‖) ≤ δ := by
      calc η * (B + ‖Y‖) ≤ η * (B + ‖Y‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hη.le
        _ = δ := div_mul_cancel₀ δ hden.ne'
    calc ‖Y‖ ^ 2 ≤ ‖Y - F‖ * ‖Y‖ + ‖inner ℂ F Y‖ := hYY
      _ ≤ η * ‖Y‖ + B * (‖Y‖ + η) := by
        have h1 : ‖Y - F‖ * ‖Y‖ ≤ η * ‖Y‖ :=
          mul_le_mul_of_nonneg_right hdist.le (norm_nonneg Y)
        have h2 : ‖inner ℂ F Y‖ ≤ B * (‖Y‖ + η) :=
          hFY.trans (mul_le_mul_of_nonneg_left hFnorm hB)
        linarith
      _ = B * ‖Y‖ + η * (B + ‖Y‖) := by ring
      _ ≤ B * ‖Y‖ + δ := by linarith
  rcases eq_or_lt_of_le (norm_nonneg Y) with h0 | hpos
  · linarith
  · nlinarith

/-- Decomposition of the stress-map adjoint difference against a smooth tensor test `M`:
`⟨F, (S_ε* - S_0*) Z⟩_{H_T} = ⟨G_ε, (T_ε* - T_0*) Z⟩_H + ⟨G_ε - G_0, T_0* Z⟩_H`
(source lines 1848–1858). -/
theorem inner_adjoint_stress_sub {c ε : ℝ} {T1 T2 : HSpace c MeridC →L[ℂ] HSpace c MeridC}
    {S1 S2 : HTSpace c →L[ℂ] HSpace c MeridC}
    (hS1 : IsStressMap c ε T1 S1) (hS2 : IsStressMap c 0 T2 S2)
    {M : Profile → TensorVal} (hM : IsTensorTest c M)
    {F : HTSpace c} {G1 G2 Z : HSpace c MeridC}
    (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] M)
    (hG1 : (G1 : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p))
    (hG2 : (G2 : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p)) :
    inner ℂ F ((ContinuousLinearMap.adjoint S1 - ContinuousLinearMap.adjoint S2) Z) =
      inner ℂ G1 ((ContinuousLinearMap.adjoint T1 - ContinuousLinearMap.adjoint T2) Z) +
        inner ℂ (G1 - G2) (ContinuousLinearMap.adjoint T2 Z) := by
  have hL : inner ℂ F ((ContinuousLinearMap.adjoint S1 - ContinuousLinearMap.adjoint S2) Z) =
      inner ℂ (T1 G1) Z - inner ℂ (T2 G2) Z := by
    simp only [sub_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
      hS1 M hM F G1 hF hG1, hS2 M hM F G2 hF hG2]
  have hR : inner ℂ G1 ((ContinuousLinearMap.adjoint T1 - ContinuousLinearMap.adjoint T2) Z) +
      inner ℂ (G1 - G2) (ContinuousLinearMap.adjoint T2 Z) =
      inner ℂ (T1 G1) Z - inner ℂ (T2 G2) Z := by
    simp only [sub_apply, map_sub, inner_sub_right, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  exact hL.trans hR.symm

/-! ### 6. Intermediate and leaf propositions for `NearSmoothAdjointComparison` -/

/-- **Observation-box `S^1` bound (`ObsBoxS1Bound`)**: on the observation box `σ ≤ s ≤ H₁`,
`|η| ≤ L₁`, the four weighted `L²(measureH c)` norms `(∫ |η|^j² ‖S^a z‖² s^{-3/2})^{1/2}`
(`a, j ∈ {0, 1}`) from `NearLerayComparison` are controlled by
`4 * (1 + σ⁻¹ + H₁ + L₁)³ * h6Norm c z`
(source `the November 2 reference manuscript`
lines 1737–1751, 1844–1846). -/
def ObsBoxS1Bound : Prop :=
  ∀ (c σ H1 L1 : ℝ), 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 →
    ∀ z : Profile → MeridC, IsMeridTest c z →
      (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
        (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
          4 * (1 + σ⁻¹ + H1 + L1) ^ 3 * h6Norm c z

/-- Observation-box Leray difference bound combining `nearLerayComparison` (`PartII-a:N02`)
with `ObsBoxS1Bound`. -/
theorem norm_PepsC_sub_le (hObs : ObsBoxS1Bound) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (ν c σ H1 L1 M γs ε : ℝ), 0 < ν → 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 ≤ M →
        0 < γs → 0 < ε → ε ≤ 1 →
        ∀ (z : Profile → MeridC) (Z : HSpace c MeridC), IsMeridTest c z →
          (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
          (Z : Profile → MeridC) =ᵐ[measureH c] z →
          ‖(PepsC ε c - PepsC 0 c) Z‖ ≤
            C * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z := by
  obtain ⟨d, CL, hCL, hLeray⟩ := nearLerayComparison
  refine ⟨d + 3, 4 * CL, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs ε hν hc hσ hσH1 hL1 hM hγs hε0 hε1 z Z hz hsupp hZ
  have hH1 : 0 ≤ H1 := le_trans hσ.le hσH1
  have hG0 : 0 ≤ GammaBox ν c σ H1 L1 M γs := GammaBox_nonneg hν hc hσ hσH1 hL1 hM hγs
  have h1 := hLeray c ε hc hε0 hε1 z Z hz hZ
  have h2 := hObs c σ H1 L1 hc hσ hσH1 hL1 z hz hsupp
  have hG1 := one_add_c_add_inv_c_le_GammaBox ν c σ H1 L1 M γs hν hσ hσH1 hL1 hM hγs
  have hG2 := one_add_sigma_H1_L1_le_GammaBox ν c σ H1 L1 M γs hν hc hM hγs
  have hpow1 : (1 + c + c⁻¹) ^ d ≤ GammaBox ν c σ H1 L1 M γs ^ d :=
    pow_le_pow_left₀ (by positivity) hG1 d
  have hpow2 : (1 + σ⁻¹ + H1 + L1) ^ 3 ≤ GammaBox ν c σ H1 L1 M γs ^ 3 :=
    pow_le_pow_left₀ (by positivity) hG2 3
  have hh6 := h6Norm_nonneg c z
  calc ‖(PepsC ε c - PepsC 0 c) Z‖
      ≤ CL * (1 + c + c⁻¹) ^ d * Real.sqrt ε *
          ∑ a ∈ Finset.range 2, ∑ j ∈ Finset.range 2,
            (∫ p, (|p.2.2| ^ j) ^ 2 * ‖(opS^[a] z) p‖ ^ 2 ∂(measureH c)) ^ (1 / 2 : ℝ) := h1
    _ ≤ CL * (1 + c + c⁻¹) ^ d * Real.sqrt ε *
          (4 * (1 + σ⁻¹ + H1 + L1) ^ 3 * h6Norm c z) := by
        gcongr
    _ = 4 * CL * ((1 + c + c⁻¹) ^ d * (1 + σ⁻¹ + H1 + L1) ^ 3) * Real.sqrt ε * h6Norm c z := by
        ring
    _ ≤ 4 * CL * (GammaBox ν c σ H1 L1 M γs ^ d * GammaBox ν c σ H1 L1 M γs ^ 3) *
          Real.sqrt ε * h6Norm c z := by
        gcongr
    _ = 4 * CL * GammaBox ν c σ H1 L1 M γs ^ (d + 3) * Real.sqrt ε * h6Norm c z := by
        rw [← pow_add]

/-- **Leaf 1 (`AdjointPolynomialBound`, task `PartII-a:N04/1`)**: Lemma `near:adjoint-polynomial`
(source `the November 2 reference manuscript`
lines 1800–1836). For a smooth test `z` supported in the observation box
`σ ≤ s ≤ H₁`, `|η| ≤ L₁` with `Z =ᵐ[measureH c] z`, the flat adjoint output
`V = (T0flat hc ν μ).adjoint Z` has a `c`-periodic representative `v : Profile → MeridC`
smooth on `{p : Profile | 0 < p.1}` and supported in `s ≤ H₁` such that `genDiff1 ν v`,
`genDiff2 ν v` belong to `L²(measureH c)` and `gradDiff1 v` belongs to `L²(measureHT c)`,
with norms bounded by `C * GammaBox ν c σ H1 L1 M γs ^ k * h6Norm c z`. -/
def AdjointPolynomialBound : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (hc : 0 < c), 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ (z : Profile → MeridC) (Z : HSpace c MeridC), IsMeridTest c z →
          (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
          (Z : Profile → MeridC) =ᵐ[measureH c] z →
          ∃ v : Profile → MeridC,
            ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1} ∧ QPeriodic c v ∧ (∀ p, H1 < p.1 → v p = 0) ∧
            ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
              Profile → MeridC) =ᵐ[measureH c] v ∧
            ∃ (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
              (h2 : MemLp (genDiff2 ν v) 2 (measureH c))
              (hgd : MemLp (gradDiff1 v) 2 (measureHT c)),
              ‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖ +
                ‖hgd.toLp (gradDiff1 v)‖ ≤
                  C * GammaBox ν c σ H1 L1 M γs ^ k * h6Norm c z

/-- **Leaf 2 (`AdjointResidualEq`, task `PartII-a:N04/2`)**: projected adjoint resolvent equation
(source `the November 2 reference manuscript`
lines 1842–1845). Since `(μ̄ - A_ε*) T_ε* = P_ε` and `(μ̄ - A_0*) v = P_0 z`,
the difference `w = (T_ε* - T_0*) Z` solves
`(μ̄ - A_ε*) w = (P_ε - P_0) Z + (A_ε* - A_0*) v`, i.e.
`(Teps.adjoint - T0flat.adjoint) Z = RepsVec.adjoint ((PepsC ε c - PepsC 0 c) Z + genDiffC ν ε v)`. -/
def AdjointResidualEq : Prop :=
  ∀ (ν c σ H1 L1 : ℝ) (hν : 0 < ν) (hc : 0 < c), 0 < σ → σ ≤ H1 → 0 ≤ L1 →
    ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
        ∀ (z v : Profile → MeridC) (Z : HSpace c MeridC), IsMeridTest c z →
          (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
          (Z : Profile → MeridC) =ᵐ[measureH c] z →
          ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1} → QPeriodic c v → (∀ p, H1 < p.1 → v p = 0) →
          ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
            Profile → MeridC) =ᵐ[measureH c] v →
          ∀ (h1 : MemLp (genDiff1 ν v) 2 (measureH c))
            (h2 : MemLp (genDiff2 ν v) 2 (measureH c)),
            (ContinuousLinearMap.adjoint (Teps hν hε hc hP μ) -
                ContinuousLinearMap.adjoint (T0flat hc ν μ)) Z =
              ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ)
                ((PepsC ε c - PepsC 0 c) Z +
                  (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v))

/-- **Adjoint symmetric-gradient / divergence pairing bound (`SymGradAdjointBound`)**
(source `the November 2 reference manuscript`
lines 1848–1860). For `w = RepsVec.adjoint R` and a smooth tensor test `M` with
`F =ᵐ M` in `H_T` and `G =ᵐ s • divEps ε M` in `H`,
`|⟨G, RepsVec* R⟩_H| = |⟨M, G_ε w⟩_{H_T}| ≤ C (1 + M + γs⁻¹) ν^{-1/2} ‖F‖_{H_T} ‖R‖_H`. -/
def SymGradAdjointBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν c M γs : ℝ) (hν : 0 < ν) (hc : 0 < c), 0 < γs →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          ∀ (R : HSpace c MeridC) (Mtest : Profile → TensorVal)
            (F : HTSpace c) (G : HSpace c MeridC),
            IsTensorTest c Mtest →
            (F : Profile → TensorVal) =ᵐ[measureHT c] Mtest →
            (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε Mtest p) →
              ‖inner ℂ G (ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R)‖ ≤
                C * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ * ‖R‖

/-- **Integration by parts of `s(div_ε - div_0) M` against `v` on `H` (`GradDiffIBP`)**
(source `the November 2 reference manuscript`
lines 1856–1863):
`⟨s(div_ε - div_0) M, v⟩_H = ⟨M, ε((K + 1) v_r, (K + 1) v_z, 0, -v_r)⟩_{H_T}`. -/
def GradDiffIBP : Prop :=
  ∀ (c ε H1 : ℝ), 0 < c →
    ∀ (M : Profile → TensorVal) (v : Profile → MeridC)
      (F : HTSpace c) (G1 G2 V : HSpace c MeridC)
      (hgd : MemLp (gradDiff1 v) 2 (measureHT c)),
      IsTensorTest c M →
      ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1} → QPeriodic c v → (∀ p, H1 < p.1 → v p = 0) →
      (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G1 : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
      (G2 : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      (V : Profile → MeridC) =ᵐ[measureH c] v →
      inner ℂ (G1 - G2) V = inner ℂ F ((memLp_gradDiff hgd ε).toLp (gradDiff ε v))

/-! ### 7. Assembly of `NearSmoothAdjointComparison` from the five propositions -/

/-- Norm bound for `RepsVec.adjoint R` using `B0223.norm_RepsVec_le` and
`ContinuousLinearMap.adjoint.norm_map`. -/
theorem norm_adjoint_RepsVec_le {P ν ε c γs : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε)
    (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ} (hγs : 0 < γs) (hμγ : γs ≤ μ.re + 1 / 4)
    (R : HSpace c MeridC) :
    ‖ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R‖ ≤ γs⁻¹ * ‖R‖ := by
  have hμ : 0 < μ.re + 1 / 4 := by linarith
  have h1 : ‖ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R‖ ≤
      ‖ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ)‖ * ‖R‖ :=
    ContinuousLinearMap.le_opNorm _ R
  rw [ContinuousLinearMap.adjoint.norm_map] at h1
  have h2 := B0223.norm_RepsVec_le hν hε hc hP hμ
  have h3 : (μ.re + 1 / 4)⁻¹ ≤ γs⁻¹ := inv_anti₀ hγs hμγ
  exact h1.trans (mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg R))

/-- Norm bound on the adjoint residual `R = (P_ε - P_0) Z + genDiffC ν ε v`. -/
theorem norm_adjoint_residual_le {ν c σ H1 L1 M γs ε CL CP : ℝ} {kL kP : ℕ}
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM0 : 0 ≤ M)
    (hγs : 0 < γs) (hε : 0 < ε) (hε1 : ε ≤ 1) (hCL : 0 ≤ CL) (hCP : 0 ≤ CP)
    {z v : Profile → MeridC} {Z : HSpace c MeridC}
    (h1 : MemLp (genDiff1 ν v) 2 (measureH c)) (h2 : MemLp (genDiff2 ν v) 2 (measureH c))
    (hPLe : ‖(PepsC ε c - PepsC 0 c) Z‖ ≤
      CL * GammaBox ν c σ H1 L1 M γs ^ kL * Real.sqrt ε * h6Norm c z)
    (h12_le : ‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖ ≤
      CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z) :
    ‖(PepsC ε c - PepsC 0 c) Z + (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)‖ ≤
      (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z := by
  have hkL_le : GammaBox ν c σ H1 L1 M γs ^ kL ≤ GammaBox ν c σ H1 L1 M γs ^ (max kL kP) :=
    GammaBox_pow_mono hν hc hσ hσH1 hL1 hM0 hγs (le_max_left kL kP)
  have hkP_le : GammaBox ν c σ H1 L1 M γs ^ kP ≤ GammaBox ν c σ H1 L1 M γs ^ (max kL kP) :=
    GammaBox_pow_mono hν hc hσ hσH1 hL1 hM0 hγs (le_max_right kL kP)
  have hh6 : 0 ≤ h6Norm c z := h6Norm_nonneg c z
  have hPLe' : ‖(PepsC ε c - PepsC 0 c) Z‖ ≤
      CL * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z := by
    calc ‖(PepsC ε c - PepsC 0 c) Z‖
        ≤ CL * GammaBox ν c σ H1 L1 M γs ^ kL * Real.sqrt ε * h6Norm c z := hPLe
      _ ≤ CL * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z := by
          gcongr
  have hgenLe' : ‖(memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)‖ ≤
      2 * CP * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z := by
    calc ‖(memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)‖
        ≤ 2 * Real.sqrt ε * (‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖) :=
          norm_genDiffC_le hε hε1 h1 h2
      _ ≤ 2 * Real.sqrt ε * (CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z) :=
          mul_le_mul_of_nonneg_left h12_le (by positivity)
      _ = 2 * CP * GammaBox ν c σ H1 L1 M γs ^ kP * Real.sqrt ε * h6Norm c z := by ring
      _ ≤ 2 * CP * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z := by
          gcongr
  calc ‖(PepsC ε c - PepsC 0 c) Z + (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)‖
      ≤ ‖(PepsC ε c - PepsC 0 c) Z‖ +
          ‖(memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)‖ := norm_add_le _ _
    _ ≤ CL * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z +
          2 * CP * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z :=
        add_le_add hPLe' hgenLe'
    _ = (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z := by
        ring

/-- Bound on the `S`-adjoint difference `(S_ε* - S_0*) Z` by smooth tensor test duality. -/
theorem norm_adjoint_stress_sub_le (hIBP : GradDiffIBP)
    {P ν c σ H1 L1 M γs ε CL CP CS : ℝ} [Fact (0 < P)] {kL kP : ℕ}
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1) (hM0 : 0 ≤ M)
    (hγs : 0 < γs) (hε : 0 < ε) (hε1 : ε ≤ 1) (hP : P = 2 * ε * c)
    {μ : ℂ} (hCL : 0 ≤ CL) (hCP : 0 ≤ CP) (hCS : 0 ≤ CS)
    (hSymB : ∀ (R : HSpace c MeridC) (Mtest : Profile → TensorVal)
      (F : HTSpace c) (G : HSpace c MeridC),
      IsTensorTest c Mtest →
      (F : Profile → TensorVal) =ᵐ[measureHT c] Mtest →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε Mtest p) →
        ‖inner ℂ G (ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R)‖ ≤
          CS * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ * ‖R‖)
    {z v : Profile → MeridC} {Z R : HSpace c MeridC}
    (hv_smooth : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1})
    (hv_per : QPeriodic c v) (hv_supp : ∀ p, H1 < p.1 → v p = 0)
    (hv_ae : ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
      Profile → MeridC) =ᵐ[measureH c] v)
    (hgd : MemLp (gradDiff1 v) 2 (measureHT c))
    (hResEq : (ContinuousLinearMap.adjoint (Teps hν hε hc hP μ) -
        ContinuousLinearMap.adjoint (T0flat hc ν μ)) Z =
      ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R)
    (hR_le : ‖R‖ ≤
      (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z)
    (hgd_le : ‖hgd.toLp (gradDiff1 v)‖ ≤
      CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z)
    (Seps S0 : HTSpace c →L[ℂ] HSpace c MeridC)
    (hSeps : IsStressMap c ε (Teps hν hε hc hP μ) Seps)
    (hS0 : IsStressMap c 0 (T0flat hc ν μ) S0) :
    ‖(ContinuousLinearMap.adjoint Seps - ContinuousLinearMap.adjoint S0) Z‖ ≤
      ((1 + CS) * (CL + 2 * CP) + CP) *
        GammaBox ν c σ H1 L1 M γs ^ (max kL kP + 2) * Real.sqrt ε * h6Norm c z := by
  set k : ℕ := max kL kP + 2
  set C : ℝ := (1 + CS) * (CL + 2 * CP) + CP
  have hh6 : 0 ≤ h6Norm c z := h6Norm_nonneg c z
  have hG_nonneg : 0 ≤ GammaBox ν c σ H1 L1 M γs :=
    GammaBox_nonneg hν hc hσ hσH1 hL1 hM0 hγs
  have hGkP_le : GammaBox ν c σ H1 L1 M γs ^ kP ≤ GammaBox ν c σ H1 L1 M γs ^ k :=
    GammaBox_pow_mono hν hc hσ hσH1 hL1 hM0 hγs (le_trans (le_max_right kL kP) (by omega))
  have hB_nonneg : 0 ≤ C * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z := by
    positivity
  refine norm_le_of_isTensorTest_inner hc hB_nonneg _ fun Mtest F hMt hF => ?_
  have hGε_mem :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc Mtest hMt
  have hG0_mem :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c 0 hc Mtest hMt
  have hsplit := inner_adjoint_stress_sub hSeps hS0 hMt (Z := Z) hF
    hGε_mem.coeFn_toLp hG0_mem.coeFn_toLp
  rw [hsplit, hResEq]
  have hI1 := hSymB R Mtest F (hGε_mem.toLp _) hMt hF hGε_mem.coeFn_toLp
  have hI2_eq := hIBP c ε H1 hc Mtest v F (hGε_mem.toLp _) (hG0_mem.toLp _)
    (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z) hgd
    hMt hv_smooth hv_per hv_supp hF hGε_mem.coeFn_toLp hG0_mem.coeFn_toLp hv_ae
  have hI2 : ‖inner ℂ (hGε_mem.toLp _ - hG0_mem.toLp _)
      (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z)‖ ≤
      CP * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖ := by
    rw [hI2_eq]
    have hstep1 : Real.sqrt ε * ‖hgd.toLp (gradDiff1 v)‖ ≤
        Real.sqrt ε * (CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z) :=
      mul_le_mul_of_nonneg_left hgd_le (Real.sqrt_nonneg ε)
    have hstep2 : CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z ≤
        CP * GammaBox ν c σ H1 L1 M γs ^ k * h6Norm c z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGkP_le hCP) hh6
    have hstep3 : Real.sqrt ε * (CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z) ≤
        Real.sqrt ε * (CP * GammaBox ν c σ H1 L1 M γs ^ k * h6Norm c z) :=
      mul_le_mul_of_nonneg_left hstep2 (Real.sqrt_nonneg ε)
    calc ‖inner ℂ F ((memLp_gradDiff hgd ε).toLp (gradDiff ε v))‖
        ≤ ‖F‖ * ‖(memLp_gradDiff hgd ε).toLp (gradDiff ε v)‖ := norm_inner_le_norm _ _
      _ ≤ ‖F‖ * (Real.sqrt ε * ‖hgd.toLp (gradDiff1 v)‖) :=
        mul_le_mul_of_nonneg_left (norm_gradDiff_le hε hε1 hgd) (norm_nonneg F)
      _ ≤ ‖F‖ * (Real.sqrt ε * (CP * GammaBox ν c σ H1 L1 M γs ^ k * h6Norm c z)) :=
        mul_le_mul_of_nonneg_left (hstep1.trans hstep3) (norm_nonneg F)
      _ = CP * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖ := by ring
  have hMγ_le := one_add_M_add_inv_gammas_le_GammaBox ν c σ H1 L1 M γs hν hc hσ hσH1 hL1
  have hν_le := inv_sqrt_nu_le_GammaBox hν hc hσ hσH1 hL1 hM0 hγs
  have hprod_le : (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) ≤ GammaBox ν c σ H1 L1 M γs ^ 2 := by
    rw [sq]
    exact mul_le_mul hMγ_le hν_le (by positivity) hG_nonneg
  have hPR : ((1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ))) * ‖R‖ ≤
      GammaBox ν c σ H1 L1 M γs ^ 2 *
        ((CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) *
          Real.sqrt ε * h6Norm c z) :=
    mul_le_mul hprod_le hR_le (norm_nonneg R) (pow_nonneg hG_nonneg 2)
  have hCSF : 0 ≤ CS * ‖F‖ := mul_nonneg hCS (norm_nonneg F)
  have hI1' := calc
    ‖inner ℂ (hGε_mem.toLp _) (ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R)‖
      ≤ CS * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ * ‖R‖ := hI1
    _ = (CS * ‖F‖) * (((1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ))) * ‖R‖) := by ring
    _ ≤ (CS * ‖F‖) * (GammaBox ν c σ H1 L1 M γs ^ 2 *
        ((CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) *
          Real.sqrt ε * h6Norm c z)) :=
      mul_le_mul_of_nonneg_left hPR hCSF
    _ = CS * (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ k *
        Real.sqrt ε * h6Norm c z * ‖F‖ := by
      have hk_eq : GammaBox ν c σ H1 L1 M γs ^ 2 * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) =
          GammaBox ν c σ H1 L1 M γs ^ k := by
        rw [← pow_add, add_comm 2 (max kL kP)]
      linear_combination
        (CS * (CL + 2 * CP) * Real.sqrt ε * h6Norm c z * ‖F‖) * hk_eq
  calc ‖inner ℂ (hGε_mem.toLp _) (ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R) +
          inner ℂ (hGε_mem.toLp _ - hG0_mem.toLp _)
            (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z)‖
      ≤ ‖inner ℂ (hGε_mem.toLp _) (ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R)‖ +
          ‖inner ℂ (hGε_mem.toLp _ - hG0_mem.toLp _)
            (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z)‖ :=
        norm_add_le _ _
    _ ≤ CS * (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖ +
          CP * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖ :=
        add_le_add hI1' hI2
    _ = (CS * (CL + 2 * CP) + CP) *
          (GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖) := by ring
    _ ≤ C * (GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        change CS * (CL + 2 * CP) + CP ≤ (1 + CS) * (CL + 2 * CP) + CP
        linarith
    _ = C * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z * ‖F‖ := by ring

/-- Conditional proof of `NearSmoothAdjointComparison` (`PartII-a:N04`) from the five
propositions. -/
theorem nearSmoothAdjointComparison_of_five (hObs : ObsBoxS1Bound) (hPoly : AdjointPolynomialBound)
    (hRes : AdjointResidualEq) (hSym : SymGradAdjointBound) (hIBP : GradDiffIBP) :
    NearSmoothAdjointComparison := by
  obtain ⟨kL, CL, hCL, hLerayBox⟩ := norm_PepsC_sub_le hObs
  obtain ⟨kP, CP, hCP, hPolyB⟩ := hPoly
  obtain ⟨CS, hCS, hSymB⟩ := hSym
  set k : ℕ := max kL kP + 2
  set C : ℝ := (1 + CS) * (CL + 2 * CP) + CP
  refine ⟨k, C, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hγs ε hε hε1 P _ hP hP1 μ hμM hμγ z Z hz hsupp hZ
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hμ4 : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hμγ
  obtain ⟨v, hv_smooth, hv_per, hv_supp, hv_ae, h1, h2, hgd, hv_bound⟩ :=
    hPolyB ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ z Z hz hsupp hZ
  set R : HSpace c MeridC :=
    (PepsC ε c - PepsC 0 c) Z + (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)
  have hResEq : (ContinuousLinearMap.adjoint (Teps hν hε hc hP μ) -
      ContinuousLinearMap.adjoint (T0flat hc ν μ)) Z =
      ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R :=
    hRes ν c σ H1 L1 hν hc hσ hσH1 hL1 ε hε hε1 P hP hP1 μ hμ4
      z v Z hz hsupp hZ hv_smooth hv_per hv_supp hv_ae h1 h2
  have hPLe := hLerayBox ν c σ H1 L1 M γs ε hν hc hσ hσH1 hL1 hM0 hγs hε hε1 z Z hz hsupp hZ
  have h12_le : ‖h1.toLp (genDiff1 ν v)‖ + ‖h2.toLp (genDiff2 ν v)‖ ≤
      CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z := by
    have hgd0 : 0 ≤ ‖hgd.toLp (gradDiff1 v)‖ := norm_nonneg _
    linarith
  have hgd_le : ‖hgd.toLp (gradDiff1 v)‖ ≤
      CP * GammaBox ν c σ H1 L1 M γs ^ kP * h6Norm c z := by
    have h10 : 0 ≤ ‖h1.toLp (genDiff1 ν v)‖ := norm_nonneg _
    have h20 : 0 ≤ ‖h2.toLp (genDiff2 ν v)‖ := norm_nonneg _
    linarith
  have hR_le : ‖R‖ ≤
      (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) * Real.sqrt ε * h6Norm c z :=
    norm_adjoint_residual_le hν hc hσ hσH1 hL1 hM0 hγs hε hε1 hCL hCP h1 h2 hPLe h12_le
  have hh6 : 0 ≤ h6Norm c z := h6Norm_nonneg c z
  have hG_nonneg : 0 ≤ GammaBox ν c σ H1 L1 M γs :=
    GammaBox_nonneg hν hc hσ hσH1 hL1 hM0 hγs
  have hG1_le : GammaBox ν c σ H1 L1 M γs ^ (max kL kP + 1) ≤ GammaBox ν c σ H1 L1 M γs ^ k :=
    GammaBox_pow_mono hν hc hσ hσH1 hL1 hM0 hγs (by omega)
  refine ⟨?_, ?_⟩
  · -- Part 1: T-adjoint bound
    rw [hResEq]
    have hT1 := norm_adjoint_RepsVec_le hν hε hc hP hγs hμγ R
    have hγG := inv_gammas_le_GammaBox ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM0
    calc ‖ContinuousLinearMap.adjoint (RepsVec hν hε hc hP μ) R‖
        ≤ γs⁻¹ * ‖R‖ := hT1
      _ ≤ GammaBox ν c σ H1 L1 M γs *
          ((CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP) *
            Real.sqrt ε * h6Norm c z) :=
        mul_le_mul hγG hR_le (norm_nonneg R) hG_nonneg
      _ = (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ (max kL kP + 1) *
          Real.sqrt ε * h6Norm c z := by
        rw [pow_succ']
        ring
      _ ≤ (CL + 2 * CP) * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z := by
        gcongr
      _ ≤ C * GammaBox ν c σ H1 L1 M γs ^ k * Real.sqrt ε * h6Norm c z := by
        have hC_ge : CL + 2 * CP ≤ C := by
          change CL + 2 * CP ≤ (1 + CS) * (CL + 2 * CP) + CP
          nlinarith
        gcongr
  · -- Part 2: S-adjoint bound
    intro Seps S0 hSeps hS0
    exact norm_adjoint_stress_sub_le hIBP hν hc hσ hσH1 hL1 hM0 hγs hε hε1 hP
      hCL hCP hCS (hSymB ν c M γs hν hc hγs ε hε hε1 P hP hP1 μ hμM hμγ)
      hv_smooth hv_per hv_supp hv_ae hgd hResEq hR_le hgd_le Seps S0 hSeps hS0

end UnforcedLeray.Short.PartIIa
