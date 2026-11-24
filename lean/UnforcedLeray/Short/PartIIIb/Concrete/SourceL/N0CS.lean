import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_2

/-!
# Cauchy-Schwarz bound `SLLint` for `N₀` (source 4924-4936)

Source `the November 2 reference manuscript` lines 4924-4936.

Pointwise on the old region `u > 6/(5ν)`:
`u^{-3/2}|M| = (g⁻¹ W u^{-1/4}|M|) (g W⁻¹ u^{-5/4})`.
Hölder with exponents `2, 2` splits the integral into
* `∫ (g⁻¹ W u^{-1/4}|T₁|)² dold ≤ ‖T‖²`, since `oldMeasure` is dominated by the age measure
  `s^{-1/2} ds` and `gainZ1Measure = g⁻² W² s^{-1/2} ds` (`slCMP`, `slGain_lint`, `slLp_sq_le`);
* `∫ (g W⁻¹ u^{-5/4})² dold ≤ e^{2γ/ν} (√2 K)`, using `g⁻¹ ≤ e^{γ/ν}`, `SLTrans`, and
  `∫_{1}^∞ s^{-2} = 1` (`slTail_lint`), with `K = max C_T 0`.
The constant is `C = √(√2 K)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ### Elementary facts about `W`, `ginv` -/

theorem slW_pos (mZ : ℝ) (p : Chart) : 0 < UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  exact Real.rpow_pos_of_pos (by positivity) _

theorem slW_meas (mZ : ℝ) :
    Measurable (fun p : Chart => UnforcedLeray.Short.IIIa.transWeight mZ p) := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  fun_prop

theorem slGinv_meas (γ ν : ℝ) : Measurable (fun p : Chart => ginv γ ν p) := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  fun_prop

theorem slGinv_pos (γ ν : ℝ) (p : Chart) : 0 < ginv γ ν p := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  exact inv_pos.2 (Real.exp_pos _)

theorem slGinvInv_eq (γ ν : ℝ) (p : Chart) :
    (ginv γ ν p)⁻¹ = UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) := by
  unfold ginv
  exact inv_inv _

theorem slGainG_le {γ ν s : ℝ} (hγ : 0 < γ) (hν : 0 < ν) (hs : 0 ≤ s) :
    UnforcedLeray.Short.IIIa.gainG γ ν s ≤ Real.exp (γ / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  apply Real.exp_le_exp.2
  have hd : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  rw [div_le_div_iff₀ hd hν]
  nlinarith

theorem slGinvInv_le (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) (p : Chart) (hp : 0 < p.1) :
    (ginv γ ν p)⁻¹ ≤ Real.exp (γ / ν) := by
  rw [slGinvInv_eq]
  exact slGainG_le hγ hν (le_max_of_le_left hp.le)

/-! ### Real-variable identities -/

theorem slAlg (G W A B F : ℝ) (hG : G ≠ 0) (hW : W ≠ 0) :
    (G * W * A * F) * (G⁻¹ * W⁻¹ * B) = A * B * F := by
  have h1 : G * G⁻¹ = 1 := mul_inv_cancel₀ hG
  have h2 : W * W⁻¹ = 1 := mul_inv_cancel₀ hW
  calc (G * W * A * F) * (G⁻¹ * W⁻¹ * B) = (G * G⁻¹) * (W * W⁻¹) * (A * B) * F := by ring
    _ = A * B * F := by rw [h1, h2]; ring

theorem slSqrt_pw {s : ℝ} (hs : 1 ≤ s) :
    s ^ (-(5 / 2 : ℝ)) * Real.sqrt (1 + s) ≤ Real.sqrt 2 * s ^ (-2 : ℝ) := by
  have hs0 : 0 < s := by linarith
  have h1 : Real.sqrt (1 + s) ≤ Real.sqrt 2 * Real.sqrt s := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : s ^ (-(5 / 2 : ℝ)) * Real.sqrt s = s ^ (-2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
    norm_num
  calc s ^ (-(5 / 2 : ℝ)) * Real.sqrt (1 + s)
      ≤ s ^ (-(5 / 2 : ℝ)) * (Real.sqrt 2 * Real.sqrt s) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0.le _)
    _ = Real.sqrt 2 * (s ^ (-(5 / 2 : ℝ)) * Real.sqrt s) := by ring
    _ = Real.sqrt 2 * s ^ (-2 : ℝ) := by rw [h2]
    _ = Real.sqrt 2 * s ^ (-2 : ℝ) := rfl

theorem slTail_lint {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (c * s ^ (-2 : ℝ)) = ENNReal.ofReal c := by
  have hint : IntegrableOn (fun s : ℝ => c * s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] (fun s : ℝ => c * s ^ (-2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
    exact mul_nonneg hc (Real.rpow_nonneg hs0.le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-! ### Measure comparison -/

/-- Comparison of the old region with the age measure: `∫ s^a Φ d(oldMeasure) ≤ ∫ Φ d(ageμ a)`. -/
theorem slCMP {c ν a : ℝ} (hc : 0 < c) (hν : 0 < ν) (Φ : Chart → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ p, ENNReal.ofReal (p.1 ^ a) * Φ p ∂(oldMeasure c ν) ≤ ∫⁻ p, Φ p ∂(ageμ c a) := by
  have hSub : Ioi (6 / 5 / ν) ⊆ Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (div_nonneg (by norm_num) hν.le)
  have hw : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ a)) := measurable_ofReal_rpow a
  have hcell : Measurable (fun z : Chart => ENNReal.ofReal (z.1 ^ a)) := hw.comp measurable_fst
  haveI : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have hI : Measurable (fun s : ℝ => ∫⁻ y, Φ (s, y) ∂(Cyl.avgμ c)) :=
    hΦ.lintegral_prod_right'
  have hΦ' : Measurable (fun p : Chart => ENNReal.ofReal (p.1 ^ a) * Φ p) := hcell.mul hΦ
  have hL : ∫⁻ p, ENNReal.ofReal (p.1 ^ a) * Φ p ∂(oldMeasure c ν)
      = ∫⁻ s in Ioi (6 / 5 / ν), ENNReal.ofReal (s ^ a) * ∫⁻ y, Φ (s, y) ∂(Cyl.avgμ c) := by
    unfold oldMeasure
    rw [lintegral_prod _ hΦ'.aemeasurable]
    refine lintegral_congr fun s => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hL]
  unfold ageμ
  rw [lintegral_prod _ hΦ.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hw hI]
  exact lintegral_mono_set hSub

/-- Splitting the old-region product: integral over `oldMeasure` as an iterated integral. -/
theorem slOld_prod {c ν : ℝ} (Φ : Chart → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ p, Φ p ∂(oldMeasure c ν) = ∫⁻ s in Ioi (6 / 5 / ν), ∫⁻ y, Φ (s, y) ∂(Cyl.avgμ c) := by
  haveI : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  unfold oldMeasure
  rw [lintegral_prod _ hΦ.aemeasurable]

/-- The gain-weighted measure of `Z₁`: `∫ Ψ dgainZ1 = ∫ W² g⁻² Ψ d ageμ(-1/2)`. -/
theorem slGain_lint (c mZ γ ν : ℝ) (Ψ : Chart → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ p, Ψ p ∂(gainZ1Measure c mZ γ ν)
      = ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
          (ENNReal.ofReal (ginv γ ν p ^ 2) * Ψ p) ∂(ageμ c (-1 / 2)) := by
  have hf1 : Measurable (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ((slGinv_meas γ ν).pow_const 2).ennreal_ofReal
  have hf2 : Measurable (fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) :=
    ((slW_meas mZ).pow_const 2).ennreal_ofReal
  unfold gainZ1Measure z1Measure
  rw [lintegral_withDensity_eq_lintegral_mul _ hf1 hΨ,
    lintegral_withDensity_eq_lintegral_mul _ hf2 (hf1.mul hΨ)]
  rfl

/-- `∫ ‖G‖² d μ = ‖R‖²` when `R = G` a.e. and `R` is an `L²` element. -/
theorem slLp_sq_eq {μ : Measure Chart} (R : Lp Ten3 2 μ) (Gm : Chart → Ten3)
    (hRG : R =ᵐ[μ] Gm) :
    ∫⁻ p, ENNReal.ofReal (‖Gm p‖ ^ 2) ∂μ = ENNReal.ofReal (‖R‖ ^ 2) := by
  have h1 : ∫⁻ p, ENNReal.ofReal (‖Gm p‖ ^ 2) ∂μ = ∫⁻ p, ‖R p‖ₑ ^ (2 : ℝ) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hRG] with p hp
    rw [hp, ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h2 : eLpNorm R 2 μ ^ (2 : ℝ) = ∫⁻ p, ‖R p‖ₑ ^ (2 : ℝ) ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := R) (p := 2) (by norm_num)
    simpa using this
  have h3 : eLpNorm R 2 μ = ENNReal.ofReal ‖R‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top R)]
  rw [h1, ← h2, h3, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Frobenius norm of the matrix of a `Ten3` element is its Euclidean norm. -/
theorem slFrob_toMatrix (x : Ten3) : frob (Ten3.toMatrix x) = ‖x‖ := by
  unfold frob Ten3.toMatrix
  rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  simp [Real.norm_eq_abs, sq_abs]

/-! ### The integrand factors -/

/-- The first Hölder factor. -/
def slFr (γ ν mZ : ℝ) (Gm : Chart → Ten3) (p : Chart) : ℝ :=
  ginv γ ν p * UnforcedLeray.Short.IIIa.transWeight mZ p * p.1 ^ (-(1 / 4 : ℝ)) * ‖Gm p‖

/-- The second Hölder factor. -/
def slGr (γ ν mZ : ℝ) (p : Chart) : ℝ :=
  (ginv γ ν p)⁻¹ * (UnforcedLeray.Short.IIIa.transWeight mZ p)⁻¹ * p.1 ^ (-(5 / 4 : ℝ))

theorem slFr_meas (γ ν mZ : ℝ) {Gm : Chart → Ten3} (hGm : Measurable Gm) :
    Measurable (fun p : Chart => slFr γ ν mZ Gm p) := by
  unfold slFr
  exact (((slGinv_meas γ ν).mul (slW_meas mZ)).mul (measurable_fst.pow_const _)).mul
    hGm.norm

theorem slGr_meas (γ ν mZ : ℝ) :
    Measurable (fun p : Chart => slGr γ ν mZ p) := by
  unfold slGr
  exact (((slGinv_meas γ ν).inv.mul (slW_meas mZ).inv)).mul (measurable_fst.pow_const _)

/-! ### The main bound -/

theorem slLint (mZ γ : ℝ) (hT : SLTrans mZ) : SLLint mZ γ := by
  unfold SLLint
  intro hm hγ
  obtain ⟨Cw, hCw⟩ := hT hm
  refine ⟨Real.sqrt (Real.sqrt 2 * max Cw 0), fun c ν ρb hc hν hν1 T => ?_⟩
  have h6 : 0 < 6 / 5 / ν := div_pos (by norm_num) hν
  have hS1 : (1 : ℝ) ≤ 6 / 5 / ν := by
    rw [le_div_iff₀ hν]
    linarith
  have hK0 : 0 ≤ max Cw 0 := le_max_right _ _
  have hE : 0 < Real.exp (γ / ν) := Real.exp_pos _
  have hc0 : 0 ≤ Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hK0)
  -- a measurable representative of the thin component
  obtain ⟨Gm, hGm, hRG⟩ : ∃ Gm : Chart → Ten3, Measurable Gm ∧
      (WithLp.ofLp T).1 =ᵐ[gainZ1Measure c mZ γ ν] Gm :=
    ⟨(Lp.aestronglyMeasurable (WithLp.ofLp T).1).mk _,
      (Lp.aestronglyMeasurable (WithLp.ofLp T).1).stronglyMeasurable_mk.measurable,
      (Lp.aestronglyMeasurable (WithLp.ofLp T).1).ae_eq_mk⟩
  have hRold : ∀ᵐ p ∂(oldMeasure c ν), (WithLp.ofLp T).1 p = Gm p :=
    (oldMeasureAC c mZ γ ν hν).ae_le hRG
  have hRT : ‖(WithLp.ofLp T).1‖ ≤ ‖T‖ := by
    have h1 : ‖T‖ = ‖(WithLp.ofLp T).1‖ + ‖(WithLp.ofLp T).2‖ := WithLp.prod_norm_eq_of_L1 T
    have h2 := norm_nonneg (WithLp.ofLp T).2
    linarith
  -- Step 1: the integrand is a product of two Hölder factors (a.e. on the old region)
  have hmain : ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)) * frob (thinRep T p))
        ∂(oldMeasure c ν)
      = ∫⁻ p, ENNReal.ofReal (slFr γ ν mZ Gm p) * ENNReal.ofReal (slGr γ ν mZ p)
        ∂(oldMeasure c ν) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hRold, ae_old_pos c ν] with p hp hp6
    have hs : 0 < p.1 := lt_trans h6 hp6
    have hfrob : frob (thinRep T p) = ‖Gm p‖ := by
      show frob (Ten3.toMatrix ((WithLp.ofLp T).1 p)) = _
      rw [hp]
      exact slFrob_toMatrix _
    have hfr0 : 0 ≤ slFr γ ν mZ Gm p := by
      unfold slFr
      exact mul_nonneg (mul_nonneg (mul_nonneg (slGinv_pos γ ν p).le (slW_pos mZ p).le)
        (Real.rpow_nonneg hs.le _)) (norm_nonneg _)
    rw [hfrob, ← ENNReal.ofReal_mul hfr0]
    congr 1
    have hsplit : p.1 ^ (-(3 / 2 : ℝ)) = p.1 ^ (-(1 / 4 : ℝ)) * p.1 ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hs]
      norm_num
    unfold slFr slGr
    rw [slAlg _ _ _ _ _ (slGinv_pos γ ν p).ne' (slW_pos mZ p).ne', hsplit]
  rw [hmain]
  have hfm : AEMeasurable (fun p : Chart => ENNReal.ofReal (slFr γ ν mZ Gm p))
      (oldMeasure c ν) :=
    ((slFr_meas γ ν mZ hGm).ennreal_ofReal).aemeasurable
  have hgm : AEMeasurable (fun p : Chart => ENNReal.ofReal (slGr γ ν mZ p))
      (oldMeasure c ν) :=
    ((slGr_meas γ ν mZ).ennreal_ofReal).aemeasurable
  refine le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hfm hgm) ?_
  -- Step 2: the first factor, using the age comparison and the gain-weighted Lp norm
  have hF2 : ∫⁻ p, ENNReal.ofReal (slFr γ ν mZ Gm p) ^ (2 : ℝ) ∂(oldMeasure c ν)
      ≤ ENNReal.ofReal (‖T‖ ^ 2) := by
    have hstep : ∀ᵐ p ∂(oldMeasure c ν), ENNReal.ofReal (slFr γ ν mZ Gm p) ^ (2 : ℝ)
        = ENNReal.ofReal (p.1 ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
            (ENNReal.ofReal (ginv γ ν p ^ 2) * ENNReal.ofReal (‖Gm p‖ ^ 2))) := by
      filter_upwards [ae_old_pos c ν] with p hp6
      have hs : 0 < p.1 := lt_trans h6 hp6
      have hfr0 : 0 ≤ slFr γ ν mZ Gm p := by
        unfold slFr
        exact mul_nonneg (mul_nonneg (mul_nonneg (slGinv_pos γ ν p).le (slW_pos mZ p).le)
          (Real.rpow_nonneg hs.le _)) (norm_nonneg _)
      have hs2 : (p.1 ^ (-(1 / 4 : ℝ))) ^ 2 = p.1 ^ (-1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
        norm_num
      have hsq : slFr γ ν mZ Gm p ^ 2 = p.1 ^ (-1 / 2 : ℝ) *
          (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 *
            (ginv γ ν p ^ 2 * ‖Gm p‖ ^ 2)) := by
        unfold slFr
        rw [← hs2]
        ring
      rw [ENNReal.ofReal_rpow_of_nonneg hfr0 (by norm_num), Real.rpow_two, hsq,
        ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_mul (sq_nonneg _)]
    have hΦ : Measurable (fun p : Chart => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
          (ENNReal.ofReal (ginv γ ν p ^ 2) * ENNReal.ofReal (‖Gm p‖ ^ 2))) := by
      have h1 := ((slW_meas mZ).pow_const 2).ennreal_ofReal
      have h2 := ((slGinv_meas γ ν).pow_const 2).ennreal_ofReal
      have h3 := ((hGm.norm).pow_const 2).ennreal_ofReal
      exact h1.mul (h2.mul h3)
    have hΨ : Measurable (fun p : Chart => ENNReal.ofReal (‖Gm p‖ ^ 2)) :=
      ((hGm.norm).pow_const 2).ennreal_ofReal
    calc ∫⁻ p, ENNReal.ofReal (slFr γ ν mZ Gm p) ^ (2 : ℝ) ∂(oldMeasure c ν)
        = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
              (ENNReal.ofReal (ginv γ ν p ^ 2) * ENNReal.ofReal (‖Gm p‖ ^ 2)))
            ∂(oldMeasure c ν) := lintegral_congr_ae hstep
      _ ≤ ∫⁻ p, (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
            (ENNReal.ofReal (ginv γ ν p ^ 2) * ENNReal.ofReal (‖Gm p‖ ^ 2))) ∂(ageμ c (-1 / 2)) :=
          slCMP hc hν _ hΦ
      _ = ∫⁻ p, ENNReal.ofReal (‖Gm p‖ ^ 2) ∂(gainZ1Measure c mZ γ ν) :=
          (slGain_lint c mZ γ ν _ hΨ).symm
      _ = ENNReal.ofReal (‖(WithLp.ofLp T).1‖ ^ 2) := slLp_sq_eq _ Gm hRG
      _ ≤ ENNReal.ofReal (‖T‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hRT 2)
  -- Step 3: the second factor, using the transverse bound `SLTrans`
  have hG2 : ∫⁻ p, ENNReal.ofReal (slGr γ ν mZ p) ^ (2 : ℝ) ∂(oldMeasure c ν)
      ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0)) := by
    have hstep : ∀ᵐ p ∂(oldMeasure c ν), ENNReal.ofReal (slGr γ ν mZ p) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * p.1 ^ (-(5 / 2 : ℝ))) *
          ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)⁻¹) := by
      filter_upwards [ae_old_pos c ν] with p hp6
      have hs : 0 < p.1 := lt_trans h6 hp6
      have hgr0 : 0 ≤ slGr γ ν mZ p := by
        unfold slGr
        exact mul_nonneg (mul_nonneg (inv_nonneg.2 (slGinv_pos γ ν p).le)
          (inv_nonneg.2 (slW_pos mZ p).le)) (Real.rpow_nonneg hs.le _)
      rw [ENNReal.ofReal_rpow_of_nonneg hgr0 (by norm_num), Real.rpow_two,
        ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _))]
      apply ENNReal.ofReal_le_ofReal
      have hG := slGinvInv_le γ ν hγ hν p hs
      have hG0 : 0 ≤ (ginv γ ν p)⁻¹ := inv_nonneg.2 (slGinv_pos γ ν p).le
      have hG2' : ((ginv γ ν p)⁻¹) ^ 2 ≤ Real.exp (γ / ν) ^ 2 := pow_le_pow_left₀ hG0 hG 2
      have hsq5 : (p.1 ^ (-(5 / 4 : ℝ))) ^ 2 = p.1 ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
        norm_num
      have hgr2 : slGr γ ν mZ p ^ 2 = ((ginv γ ν p)⁻¹) ^ 2 * p.1 ^ (-(5 / 2 : ℝ)) *
          (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)⁻¹ := by
        unfold slGr
        rw [← hsq5]
        ring
      rw [hgr2]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hG2' (Real.rpow_nonneg hs.le _)) (inv_nonneg.2 (sq_nonneg _))
    have hΦg : Measurable (fun p : Chart => ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * p.1 ^ (-(5 / 2 : ℝ))) *
        ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)⁻¹)) :=
      (((measurable_fst.pow_const _).const_mul _).ennreal_ofReal).mul
        (((slW_meas mZ).pow_const 2).inv.ennreal_ofReal)
    have hin : ∀ s ∈ Ioi (6 / 5 / ν),
        ∫⁻ y, ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (s, y).1 ^ (-(5 / 2 : ℝ))) *
          ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (s, y) ^ 2)⁻¹)
            ∂(Cyl.avgμ c)
        ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0) * s ^ (-2 : ℝ)) := by
      intro s hs
      have hs' : 6 / 5 / ν < s := hs
      have hs0 : 0 < s := lt_trans h6 hs'
      have hs1 : 1 ≤ s := le_trans hS1 hs'.le
      have hin1 : ∫⁻ y, ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (s, y) ^ 2)⁻¹)
          ∂(Cyl.avgμ c) ≤ ENNReal.ofReal (max Cw 0 * Real.sqrt (1 + s)) :=
        (hCw c hc s hs0.le).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left Cw 0) (Real.sqrt_nonneg _)))
      have hE2 : 0 ≤ Real.exp (γ / ν) ^ 2 * s ^ (-(5 / 2 : ℝ)) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0.le _)
      have hfac : ∫⁻ y, ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (s, y).1 ^ (-(5 / 2 : ℝ))) *
          ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (s, y) ^ 2)⁻¹)
            ∂(Cyl.avgμ c)
          = ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * s ^ (-(5 / 2 : ℝ))) *
            ∫⁻ y, ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (s, y) ^ 2)⁻¹)
              ∂(Cyl.avgμ c) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [hfac]
      calc ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * s ^ (-(5 / 2 : ℝ))) *
            ∫⁻ y, ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (s, y) ^ 2)⁻¹)
              ∂(Cyl.avgμ c)
          ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * s ^ (-(5 / 2 : ℝ))) *
            ENNReal.ofReal (max Cw 0 * Real.sqrt (1 + s)) := by gcongr
        _ = ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * s ^ (-(5 / 2 : ℝ)) *
            (max Cw 0 * Real.sqrt (1 + s))) := (ENNReal.ofReal_mul hE2).symm
        _ ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0) * s ^ (-2 : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have hpw := slSqrt_pw hs1
          calc Real.exp (γ / ν) ^ 2 * s ^ (-(5 / 2 : ℝ)) * (max Cw 0 * Real.sqrt (1 + s))
              = (Real.exp (γ / ν) ^ 2 * max Cw 0) * (s ^ (-(5 / 2 : ℝ)) * Real.sqrt (1 + s)) := by
                ring
            _ ≤ (Real.exp (γ / ν) ^ 2 * max Cw 0) * (Real.sqrt 2 * s ^ (-2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hpw (mul_nonneg (sq_nonneg _) hK0)
            _ = Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0) * s ^ (-2 : ℝ) := by ring
    calc ∫⁻ p, ENNReal.ofReal (slGr γ ν mZ p) ^ (2 : ℝ) ∂(oldMeasure c ν)
        ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * p.1 ^ (-(5 / 2 : ℝ))) *
            ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)⁻¹)
            ∂(oldMeasure c ν) := lintegral_mono_ae hstep
      _ = ∫⁻ s in Ioi (6 / 5 / ν), ∫⁻ y, ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (s, y).1 ^ (-(5 / 2 : ℝ))) *
            ENNReal.ofReal ((UnforcedLeray.Short.IIIa.transWeight mZ (s, y) ^ 2)⁻¹)
              ∂(Cyl.avgμ c) := slOld_prod _ hΦg
      _ ≤ ∫⁻ s in Ioi (6 / 5 / ν),
            ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0) * s ^ (-2 : ℝ)) :=
          setLIntegral_mono
            (((measurable_id.pow_const _).const_mul _).ennreal_ofReal) hin
      _ ≤ ∫⁻ s in Ioi (1 : ℝ),
            ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0) * s ^ (-2 : ℝ)) :=
          lintegral_mono_set (Set.Ioi_subset_Ioi hS1)
      _ = ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0)) :=
          slTail_lint hc0
  -- Step 4: combine with the Hölder exponent `1/2`
  have hFp : (∫⁻ p, ENNReal.ofReal (slFr γ ν mZ Gm p) ^ (2 : ℝ) ∂(oldMeasure c ν)) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal ‖T‖ := by
    calc _ ≤ (ENNReal.ofReal (‖T‖ ^ 2)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hF2 (by norm_num)
      _ = ENNReal.ofReal ‖T‖ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (norm_nonneg _)]
  have hGp : (∫⁻ p, ENNReal.ofReal (slGr γ ν mZ p) ^ (2 : ℝ) ∂(oldMeasure c ν)) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal (Real.exp (γ / ν) * Real.sqrt (Real.sqrt 2 * max Cw 0)) := by
    calc _ ≤ (ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (Real.sqrt 2 * max Cw 0))) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hG2 (by norm_num)
      _ = ENNReal.ofReal (Real.exp (γ / ν) * Real.sqrt (Real.sqrt 2 * max Cw 0)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hE.le]
  refine le_trans (mul_le_mul' hFp hGp) ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
