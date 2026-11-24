import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3

/-!
# Uniform domination of the dilated family (task `PartIII-b:C/srcL/6/3/4`)

Proves `XSPsiDomination` (see `Sub/PartIII-b_C_srcL_6_3.lean`; source 4178-4186, 4917-4937).

Fix `y` with `b < cylR y ^ 2` and let `a = (b + cylR y ^ 2) / 2`, so `b < a < cylR y ^ 2`.
On the neighbourhood `s = {cylR y' ^ 2 > a}` of `y` and for `σ > 1`:

* chain rule (as in `XSPsiFamMeas`): `D^n (y' ↦ σ Z₂(dil σ y')) y' = σ • (D^n Z₂ (dil σ y')) ∘ dil σ`;
* `‖dil σ‖ ≤ σ`, so the multilinear composition contributes at most `σ^n`;
* `‖D^n Z₂ w‖ ≤ ‖proj‖ ‖D^n Z w‖ ≤ ‖proj‖ C (1 + ‖w‖)^{-(4+n)}` at `w = dil σ y'`, where
  `cylR w^2 ≥ a` and `‖w‖ ≥ σ δ` with `δ = sqrt (a / 2)`.

Altogether the `n`-th derivative is bounded by `K |C| δ^{-(4+n)} σ^{-3}`, integrable on `(1, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The first summand `y ↦ (y 0, y 1, 0)` of the dilation. -/
private def dilD1 : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ![y 0, y 1, 0]
      map_add' := fun x y => by funext i; fin_cases i <;> simp
      map_smul' := fun c x => by funext i; fin_cases i <;> simp }

/-- The second summand `y ↦ (0, 0, y 2)` of the dilation. -/
private def dilD2 : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ![0, 0, y 2]
      map_add' := fun x y => by funext i; fin_cases i <;> simp
      map_smul' := fun c x => by funext i; fin_cases i <;> simp }

/-- The dilation `scaleXY σ` as a continuous linear map, depending continuously on `σ`. -/
private def dilL (σ : ℝ) : Vec3 →L[ℝ] Vec3 := σ • dilD1 + dilD2

private theorem dilL_apply (σ : ℝ) (y : Vec3) : dilL σ y = scaleXY σ y := by
  funext i
  fin_cases i <;> simp [dilL, dilD1, dilD2, scaleXY]

private theorem dilL_cont : Continuous (fun σ : ℝ => dilL σ) := by
  unfold dilL
  exact (continuous_id.smul continuous_const).add continuous_const

private theorem scaleXY_mem {b σ : ℝ} (hσ : 1 ≤ σ) {y : Vec3} (hy : b < cylR y ^ 2) :
    b < cylR (scaleXY σ y) ^ 2 := by
  rw [cylR_sq] at hy ⊢
  unfold scaleXY
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hσ1 : (1 : ℝ) ≤ σ ^ 2 := by nlinarith
  have hnn : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  have hid : (σ * y 0) ^ 2 + (σ * y 1) ^ 2 = σ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by ring
  rw [hid]
  nlinarith [mul_nonneg hnn (sub_nonneg.mpr hσ1)]

private theorem dilL_mem {b σ : ℝ} (hσ : 1 < σ) {y : Vec3} (hy : b < cylR y ^ 2) :
    dilL σ y ∈ {y : Vec3 | b < cylR y ^ 2} := by
  show b < cylR (dilL σ y) ^ 2
  rw [dilL_apply]
  exact scaleXY_mem (le_of_lt hσ) hy

/-- Chain rule and scalar factor for the family, at `σ > 1` (as in `XSPsiFamMeas`). -/
private theorem iteratedFDeriv_family_eq (b : ℝ) (Z : Vec3 → Vec3)
    (hZ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z {y | b < cylR y ^ 2})
    (n : ℕ) {σ : ℝ} (hσ : 1 < σ) {y : Vec3} (hy : b < cylR y ^ 2) :
    iteratedFDeriv ℝ n (fun y' => σ * Z (scaleXY σ y') 2) y =
      σ • ((iteratedFDerivWithin ℝ n (fun v => Z v 2) {y | b < cylR y ^ 2} (dilL σ y)).compContinuousLinearMap
        (fun _ => dilL σ)) := by
  have hUo : IsOpen {y : Vec3 | b < cylR y ^ 2} := isOpen_lt continuous_const (continuous_cylR.pow 2)
  have hUu : UniqueDiffOn ℝ {y : Vec3 | b < cylR y ^ 2} := hUo.uniqueDiffOn
  have hZc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => Z v 2) {y | b < cylR y ^ 2} :=
    (contDiff_apply ℝ ℝ 2).comp_contDiffOn hZ
  have hpre : IsOpen (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) :=
    hUo.preimage (dilL σ).continuous
  have hmapsto : MapsTo (dilL σ) (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2})
      {y : Vec3 | b < cylR y ^ 2} := fun z hz => hz
  have hyP : y ∈ dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2} := dilL_mem hσ hy
  have hZcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun v => Z v 2) ∘ dilL σ)
      (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) :=
    ContDiffOn.comp hZc (dilL σ).contDiff.contDiffOn hmapsto
  have hfun : (fun y' => σ * Z (scaleXY σ y') 2)
      = σ • ((fun v => Z v 2) ∘ dilL σ) := by
    funext y'
    simp [dilL_apply, smul_eq_mul]
  have key := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
    (f := σ • ((fun v => Z v 2) ∘ dilL σ)) n hpre hyP
  rw [hfun, ← key]
  have hc1 : iteratedFDerivWithin ℝ n (σ • ((fun v => Z v 2) ∘ dilL σ))
      (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) y
      = σ • iteratedFDerivWithin ℝ n ((fun v => Z v 2) ∘ dilL σ)
          (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) y :=
    iteratedFDerivWithin_const_smul_apply
      (hZcomp.contDiffWithinAt hyP |>.of_le (by exact_mod_cast le_top)) hpre.uniqueDiffOn hyP
  have hc2 : iteratedFDerivWithin ℝ n ((fun v => Z v 2) ∘ dilL σ)
      (dilL σ ⁻¹' {y : Vec3 | b < cylR y ^ 2}) y
      = (iteratedFDerivWithin ℝ n (fun v => Z v 2) {y | b < cylR y ^ 2} (dilL σ y)).compContinuousLinearMap
          (fun _ => dilL σ) :=
    ContinuousLinearMap.iteratedFDerivWithin_comp_right (dilL σ) hZc
      hUu hpre.uniqueDiffOn hyP (by exact_mod_cast le_top)
  rw [hc1, hc2]

/-- Operator norm of the dilation is at most `σ` for `σ ≥ 1`. -/
private theorem dilL_norm_le {σ : ℝ} (hσ : 1 ≤ σ) : ‖dilL σ‖ ≤ σ := by
  have hσ0 : 0 ≤ σ := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ hσ0 fun y => ?_
  rw [dilL_apply]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hσ0 (norm_nonneg y))).2 ?_
  intro i
  fin_cases i
  · show ‖σ * y 0‖ ≤ σ * ‖y‖
    rw [norm_mul, Real.norm_of_nonneg hσ0]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y 0) hσ0
  · show ‖σ * y 1‖ ≤ σ * ‖y‖
    rw [norm_mul, Real.norm_of_nonneg hσ0]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y 1) hσ0
  · show ‖y 2‖ ≤ σ * ‖y‖
    exact (norm_le_pi_norm y 2).trans (le_mul_of_one_le_left (norm_nonneg y) hσ)

/-- Lower bound `σ sqrt(a/2) ≤ ‖scaleXY σ y‖` when `a < cylR y ^ 2`, `σ > 1`. -/
private theorem scaleXY_norm_lower {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) {y : Vec3}
    (hy : a < cylR y ^ 2) :
    σ * Real.sqrt (a / 2) ≤ ‖scaleXY σ y‖ := by
  have hy2 : a < y 0 ^ 2 + y 1 ^ 2 := by rw [← cylR_sq]; exact hy
  have hσ0 : 0 < σ := by linarith
  have hw0 : (scaleXY σ y) 0 = σ * y 0 := rfl
  have hw1 : (scaleXY σ y) 1 = σ * y 1 := rfl
  have h0 : ‖(scaleXY σ y) 0‖ ≤ ‖scaleXY σ y‖ := norm_le_pi_norm _ 0
  have h1 : ‖(scaleXY σ y) 1‖ ≤ ‖scaleXY σ y‖ := norm_le_pi_norm _ 1
  have hs0 : ‖(scaleXY σ y) 0‖ ^ 2 = (scaleXY σ y 0) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have hs1 : ‖(scaleXY σ y) 1‖ ^ 2 = (scaleXY σ y 1) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have hn0 : ‖(scaleXY σ y) 0‖ ^ 2 ≤ ‖scaleXY σ y‖ ^ 2 := by
    nlinarith [h0, norm_nonneg ((scaleXY σ y) 0), norm_nonneg (scaleXY σ y)]
  have hn1 : ‖(scaleXY σ y) 1‖ ^ 2 ≤ ‖scaleXY σ y‖ ^ 2 := by
    nlinarith [h1, norm_nonneg ((scaleXY σ y) 1), norm_nonneg (scaleXY σ y)]
  have hδ : (Real.sqrt (a / 2)) ^ 2 = a / 2 := Real.sq_sqrt (by linarith)
  have hWsum : (scaleXY σ y 0) ^ 2 + (scaleXY σ y 1) ^ 2 = σ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
    rw [hw0, hw1]; ring
  have hσ2 : σ ^ 2 * a < σ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) :=
    mul_lt_mul_of_pos_left hy2 (by positivity)
  have key : (σ * Real.sqrt (a / 2)) ^ 2 ≤ ‖scaleXY σ y‖ ^ 2 := by
    have e : (σ * Real.sqrt (a / 2)) ^ 2 = σ ^ 2 * (a / 2) := by rw [mul_pow, hδ]
    nlinarith [hn0, hn1, hs0, hs1, hWsum, hσ2]
  nlinarith [key, norm_nonneg (scaleXY σ y), Real.sqrt_nonneg (a / 2)]

/-- Exponent identity: `σ * σ^n * σ^(-(4+n)) = σ^(-3)` for `σ > 0`. -/
private theorem rpow_exponent_identity {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    σ * σ ^ n * σ ^ (-(4 + (n : ℝ))) = σ ^ (-3 : ℝ) := by
  have e : (-3 : ℝ) = 1 + (n : ℝ) + -(4 + (n : ℝ)) := by ring
  rw [e, Real.rpow_add hσ, Real.rpow_add hσ, Real.rpow_one, Real.rpow_natCast]

theorem xsPsiDomination : XSPsiDomination := by
  intro b Z hH n y hy
  obtain ⟨hb, hZ, hdec⟩ := hH
  have hy0 : b < cylR y ^ 2 := hy
  have hUo : IsOpen {y : Vec3 | b < cylR y ^ 2} := isOpen_lt continuous_const (continuous_cylR.pow 2)
  have hba : b < (b + cylR y ^ 2) / 2 := by linarith
  have hay : (b + cylR y ^ 2) / 2 < cylR y ^ 2 := by linarith
  have ha0 : 0 < (b + cylR y ^ 2) / 2 := by linarith
  obtain ⟨C, hC⟩ := hdec ((b + cylR y ^ 2) / 2) hba n
  refine ⟨{y' : Vec3 | (b + cylR y ^ 2) / 2 < cylR y' ^ 2}, ?_,
    fun σ => ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2 : Vec3 →L[ℝ] ℝ)‖
      * |C| * Real.sqrt ((b + cylR y ^ 2) / 2 / 2) ^ (-(4 + (n : ℝ))) * σ ^ (-3 : ℝ), ?_, ?_⟩
  · exact (isOpen_lt continuous_const (continuous_cylR.pow 2)).mem_nhds hay
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) zero_lt_one).const_mul _
  · intro σ hσ y' hy'
    have hσ1 : 1 < σ := hσ
    have hσ1' : 1 ≤ σ := le_of_lt hσ1
    have hσ0 : 0 < σ := by linarith
    have hy'a : (b + cylR y ^ 2) / 2 < cylR y' ^ 2 := hy'
    have hy'U : b < cylR y' ^ 2 := lt_trans hba hy'a
    set a := (b + cylR y ^ 2) / 2 with ha_def
    set δ := Real.sqrt (a / 2) with hδ_def
    have hδpos : 0 < δ := Real.sqrt_pos.2 (by linarith)
    set K := ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2 : Vec3 →L[ℝ] ℝ)‖ with hK_def
    have hK0 : 0 ≤ K := norm_nonneg _
    rw [iteratedFDeriv_family_eq b Z hZ n hσ1 hy'U]
    set w := dilL σ y' with hw_def
    have hwU : w ∈ {y : Vec3 | b < cylR y ^ 2} := dilL_mem hσ1 hy'U
    have hwa : a ≤ cylR w ^ 2 := by
      rw [hw_def, dilL_apply]; exact (scaleXY_mem hσ1' hy'a).le
    -- derivative of the composed component at `w`
    have hMZ : ‖iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w‖
        ≤ K * ‖iteratedFDerivWithin ℝ n Z {y : Vec3 | b < cylR y ^ 2} w‖ :=
      ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)
        (hZ.contDiffWithinAt hwU) hUo.uniqueDiffOn hwU (by exact_mod_cast le_top)
    have hZw : ‖iteratedFDerivWithin ℝ n Z {y : Vec3 | b < cylR y ^ 2} w‖
        ≤ |C| * (1 + ‖w‖) ^ (-(4 + (n : ℝ))) := by
      rw [iteratedFDerivWithin_of_isOpen (f := Z) n hUo hwU]
      exact (hC w hwa).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have hMle : ‖iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w‖
        ≤ K * (|C| * (1 + ‖w‖) ^ (-(4 + (n : ℝ)))) :=
      hMZ.trans (mul_le_mul_of_nonneg_left hZw hK0)
    -- the decay factor
    have hlow : σ * δ ≤ ‖w‖ := by
      rw [hw_def, dilL_apply]; exact scaleXY_norm_lower hσ1 ha0 hy'a
    have hpos : 0 < σ * δ := mul_pos hσ0 hδpos
    have hxle : σ * δ ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    have hz : -(4 + (n : ℝ)) ≤ 0 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hdecay : (1 + ‖w‖) ^ (-(4 + (n : ℝ))) ≤ σ ^ (-(4 + (n : ℝ))) * δ ^ (-(4 + (n : ℝ))) := by
      rw [← Real.mul_rpow hσ0.le hδpos.le]
      exact Real.rpow_le_rpow_of_nonpos hpos hxle hz
    have hM : ‖iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w‖
        ≤ K * (|C| * (σ ^ (-(4 + (n : ℝ))) * δ ^ (-(4 + (n : ℝ))))) :=
      hMle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay (abs_nonneg C)) hK0)
    -- the multilinear composition
    have hprod : ∏ _i : Fin n, ‖dilL σ‖ ≤ σ ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_pow_left₀ (norm_nonneg _) (dilL_norm_le hσ1') n
    have hΦ : ‖(iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w).compContinuousLinearMap
        (fun _ => dilL σ)‖ ≤ ‖iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w‖ * σ ^ n :=
      (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
    calc ‖σ • ((iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w).compContinuousLinearMap
          (fun _ => dilL σ))‖
        = σ * ‖(iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w).compContinuousLinearMap
          (fun _ => dilL σ)‖ := by rw [norm_smul, Real.norm_of_nonneg hσ0.le]
      _ ≤ σ * (‖iteratedFDerivWithin ℝ n (fun v => Z v 2) {y : Vec3 | b < cylR y ^ 2} w‖ * σ ^ n) :=
          mul_le_mul_of_nonneg_left hΦ hσ0.le
      _ ≤ σ * ((K * (|C| * (σ ^ (-(4 + (n : ℝ))) * δ ^ (-(4 + (n : ℝ)))))) * σ ^ n) := by
          gcongr
      _ = K * |C| * δ ^ (-(4 + (n : ℝ))) * (σ * σ ^ n * σ ^ (-(4 + (n : ℝ)))) := by ring
      _ = K * |C| * δ ^ (-(4 + (n : ℝ))) * σ ^ (-3 : ℝ) := by
          rw [rpow_exponent_identity hσ0 n]

end UnforcedLeray.Short.PartIIIb.Concrete
