import UnforcedLeray.Short.PartIIIb.NearInst.Targets

/-!
# Coefficient multipliers (source 2764-2775)

Proves `coeffMultExists : CoeffMultExists` (`NearInst/Targets.lean`).

For measurable coefficients `w₁, w₂ : Chart → Merid` with `√s W|w₁| ≤ B₁` and `√s|w₂| ≤ B₂`
(the second a.e. for `ageμ c (-1/2)`), the map `u ↦ (w₁⊗u + u⊗w₁, w₂⊗u + u⊗w₂)` is a bounded
linear map `H → Z = Z₁ ⊕ ρ_b^{-1/2}H_T`.

Route: `ageμ c (-1/2) = ageμ c (-3/2).withDensity s` (`ageμ_half`), so both `Z₁` and `H_T` norms are
`withDensity` integrals against `μ₀ = ageμ c (-3/2)`, and the pointwise bound
`‖a⊗b+b⊗a‖_F² ≤ 4|a|²|b|²` (copied from `PartIII-a/Compose.lean`) gives the estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.CoeffMult

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIIa

/-! ## Tensor algebra -/

theorem frobSq_symOuter_le' (a b : Merid) : frobSq (symOuter a b) ≤ 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have ha : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  have hb : ‖b‖ ^ 2 = b 0 ^ 2 + b 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  simp only [frobSq, symOuter, embedMerid, Fin.sum_univ_three, ha, hb]
  simp
  nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0)]

theorem norm_sq_ten3Of (M : Matrix (Fin 3) (Fin 3) ℝ) : ‖ten3Of M‖ ^ 2 = frobSq M := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fintype.sum_prod_type]
  simp [ten3Of, frobSq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

theorem enorm_rpow_two' {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_num

theorem ten3_symOuter_add (a b d : Merid) :
    ten3Of (symOuter a (b + d)) = ten3Of (symOuter a b) + ten3Of (symOuter a d) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [ten3Of, symOuter, embedMerid] <;> ring

theorem ten3_symOuter_smul (a b : Merid) (r : ℝ) :
    ten3Of (symOuter a (r • b)) = r • ten3Of (symOuter a b) := by
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [ten3Of, symOuter, embedMerid] <;> ring

theorem continuous_ten3_symOuter :
    Continuous fun q : Merid × Merid => ten3Of (symOuter q.1 q.2) := by
  unfold ten3Of symOuter embedMerid
  fun_prop

theorem measurable_ten3_symOuter {w u : Chart → Merid} (hw : Measurable w) (hu : Measurable u) :
    Measurable fun p => ten3Of (symOuter (w p) (u p)) :=
  continuous_ten3_symOuter.measurable.comp (hw.prodMk hu)

theorem measurable_transWeight' (mZ : ℝ) : Measurable (transWeight mZ) := by
  unfold transWeight
  fun_prop

/-! ## Pointwise bounds -/

theorem pt_z1 (p : Chart) (mZ B : ℝ) (wv uv : Merid)
    (hA : 0 < p.1 → Real.sqrt p.1 * transWeight mZ p * ‖wv‖ ≤ B) :
    ENNReal.ofReal p.1 * (ENNReal.ofReal (transWeight mZ p ^ 2) * ‖ten3Of (symOuter wv uv)‖ₑ ^ (2 : ℝ))
      ≤ ENNReal.ofReal (4 * B ^ 2) * ‖uv‖ₑ ^ (2 : ℝ) := by
  by_cases hs : 0 < p.1
  · have hX : p.1 * (transWeight mZ p ^ 2 * ‖wv‖ ^ 2) ≤ B ^ 2 := by
      have h1 : (Real.sqrt p.1 * transWeight mZ p * ‖wv‖) ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (by unfold transWeight; positivity) (hA hs) 2
      have h2 : (Real.sqrt p.1 * transWeight mZ p * ‖wv‖) ^ 2
          = p.1 * (transWeight mZ p ^ 2 * ‖wv‖ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hs.le]
        ring
      linarith
    have hF : ‖ten3Of (symOuter wv uv)‖ ^ 2 ≤ 4 * ‖wv‖ ^ 2 * ‖uv‖ ^ 2 := by
      rw [norm_sq_ten3Of]
      exact frobSq_symOuter_le' wv uv
    have key : p.1 * (transWeight mZ p ^ 2 * ‖ten3Of (symOuter wv uv)‖ ^ 2)
        ≤ 4 * B ^ 2 * ‖uv‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hF (mul_nonneg hs.le (sq_nonneg (transWeight mZ p))),
        mul_le_mul_of_nonneg_right hX (sq_nonneg ‖uv‖)]
    have e1 : ENNReal.ofReal p.1 *
        (ENNReal.ofReal (transWeight mZ p ^ 2) * ‖ten3Of (symOuter wv uv)‖ₑ ^ (2 : ℝ))
        = ENNReal.ofReal (p.1 * (transWeight mZ p ^ 2 * ‖ten3Of (symOuter wv uv)‖ ^ 2)) := by
      rw [enorm_rpow_two', ENNReal.ofReal_mul hs.le, ENNReal.ofReal_mul (sq_nonneg _)]
    have e2 : ENNReal.ofReal (4 * B ^ 2) * ‖uv‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (4 * B ^ 2 * ‖uv‖ ^ 2) := by
      rw [enorm_rpow_two', ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * B ^ 2)]
    rw [e1, e2]
    exact ENNReal.ofReal_le_ofReal key
  · have h0 : ENNReal.ofReal p.1 = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hs)
    rw [h0, zero_mul]
    exact zero_le

theorem pt_ht (p : Chart) (B : ℝ) (wv uv : Merid)
    (hA : 0 < p.1 → Real.sqrt p.1 * ‖wv‖ ≤ B) :
    ENNReal.ofReal p.1 * ‖ten3Of (symOuter wv uv)‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (4 * B ^ 2) * ‖uv‖ₑ ^ (2 : ℝ) := by
  by_cases hs : 0 < p.1
  · have hX : p.1 * ‖wv‖ ^ 2 ≤ B ^ 2 := by
      have h1 : (Real.sqrt p.1 * ‖wv‖) ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (by positivity) (hA hs) 2
      have h2 : (Real.sqrt p.1 * ‖wv‖) ^ 2 = p.1 * ‖wv‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hs.le]
      linarith
    have hF : ‖ten3Of (symOuter wv uv)‖ ^ 2 ≤ 4 * ‖wv‖ ^ 2 * ‖uv‖ ^ 2 := by
      rw [norm_sq_ten3Of]
      exact frobSq_symOuter_le' wv uv
    have key : p.1 * ‖ten3Of (symOuter wv uv)‖ ^ 2 ≤ 4 * B ^ 2 * ‖uv‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hF hs.le,
        mul_le_mul_of_nonneg_right hX (sq_nonneg ‖uv‖)]
    have e1 : ENNReal.ofReal p.1 * ‖ten3Of (symOuter wv uv)‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (p.1 * ‖ten3Of (symOuter wv uv)‖ ^ 2) := by
      rw [enorm_rpow_two', ENNReal.ofReal_mul hs.le]
    have e2 : ENNReal.ofReal (4 * B ^ 2) * ‖uv‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (4 * B ^ 2 * ‖uv‖ ^ 2) := by
      rw [enorm_rpow_two', ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * B ^ 2)]
    rw [e1, e2]
    exact ENNReal.ofReal_le_ofReal key
  · have h0 : ENNReal.ofReal p.1 = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hs)
    rw [h0, zero_mul]
    exact zero_le

/-! ## The measure `ageμ (-1/2)` and the two target measures -/

theorem lintegral_ageμ_succ' {c : ℝ} (hc : 0 < c) (a : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p, f p ∂ageμ c (a + 1) = ∫⁻ p, ENNReal.ofReal p.1 * f p ∂ageμ c a := by
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal p.1 * f p :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul hf
  rw [lintegral_ageμ hc _ hf, lintegral_ageμ hc _ hm]
  refine setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)) fun p hp => ?_
  have hs : 0 < p.1 := hp.1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [Real.rpow_add hs, Real.rpow_one]
  ring

theorem ageμ_half {c : ℝ} (hc : 0 < c) :
    ageμ c (-1 / 2) = (ageμ c (-3 / 2)).withDensity fun p => ENNReal.ofReal p.1 := by
  have e : (-1 / 2 : ℝ) = -3 / 2 + 1 := by norm_num
  refine Measure.ext fun A hA => ?_
  rw [withDensity_apply _ hA, ← lintegral_indicator hA, ← lintegral_indicator_one hA, e,
    lintegral_ageμ_succ' hc _ (measurable_one.indicator hA)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ A <;> simp [hp]

theorem ageμ_half_ac {c : ℝ} (hc : 0 < c) : ageμ c (-1 / 2) ≪ ageμ c (-3 / 2) := by
  rw [ageμ_half hc]
  exact withDensity_absolutelyContinuous _ _

theorem z1_ac {c : ℝ} (hc : 0 < c) (mZ : ℝ) : z1Measure c mZ ≪ ageμ c (-3 / 2) :=
  (withDensity_absolutelyContinuous (ageμ c (-1 / 2)) _).trans (ageμ_half_ac hc)

theorem htRho_ac {c : ℝ} (hc : 0 < c) (ρb : ℝ) : htRhoMeasure c ρb ≪ ageμ c (-3 / 2) := by
  intro A hA
  have h1 : ageμ c (-1 / 2) A = 0 := ageμ_half_ac hc hA
  simp [htRhoMeasure, h1]

/-! ## Measurable representatives and the pointwise multiplier -/

theorem mul_rep {c : ℝ} (u : Hsp c) :
    ∃ uM : Chart → Merid, Measurable uM ∧ (u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] uM :=
  ⟨_, (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable,
    (Lp.aestronglyMeasurable u).ae_eq_mk⟩

theorem ae_rep {c : ℝ} (ν : Measure Chart) (hν : ν ≪ ageμ c (-3 / 2)) (w : Chart → Merid)
    (u : Hsp c) (uM : Chart → Merid) (hae : (u : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] uM) :
    (fun p => ten3Of (symOuter (w p) (u p))) =ᵐ[ν] fun p => ten3Of (symOuter (w p) (uM p)) := by
  have h : ∀ᵐ p ∂ν, (u : Chart → Merid) p = uM p := hν.ae_le hae
  filter_upwards [h] with p hp
  simp only [hp]

theorem eLpNorm_mul_le {c : ℝ} (ν : Measure Chart) (hν : ν ≪ ageμ c (-3 / 2)) {w : Chart → Merid}
    {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ u : Chart → Merid, Measurable u →
      ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂ν ≤
        ENNReal.ofReal K * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2))
    (u : Hsp c) :
    eLpNorm (fun p => ten3Of (symOuter (w p) (u p))) 2 ν ≤
      ENNReal.ofReal (Real.sqrt K) * eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2)) := by
  obtain ⟨uM, hm, hae⟩ := mul_rep u
  have hF := ae_rep ν hν w u uM hae
  have hU : ∫⁻ p, ‖(u : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)
      = ∫⁻ p, ‖uM p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
    lintegral_congr_ae (hae.mono fun p hp => by simp only [hp])
  have h2 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2' : (2 : ENNReal) ≠ ⊤ := by norm_num
  rw [eLpNorm_congr_ae hF, eLpNorm_eq_lintegral_rpow_enorm h2 h2',
    eLpNorm_eq_lintegral_rpow_enorm h2 h2']
  simp only [ENNReal.toReal_ofNat]
  rw [hU]
  calc _ ≤ (ENNReal.ofReal K * ∫⁻ p, ‖uM p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (hbd uM hm) (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt K) * (∫⁻ p, ‖uM p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hK (by norm_num), Real.sqrt_eq_rpow]

theorem memLp_mul {c : ℝ} (ν : Measure Chart) (hν : ν ≪ ageμ c (-3 / 2)) {w : Chart → Merid}
    (hw : Measurable w) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ u : Chart → Merid, Measurable u →
      ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂ν ≤
        ENNReal.ofReal K * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2))
    (u : Hsp c) : MemLp (fun p => ten3Of (symOuter (w p) (u p))) 2 ν := by
  obtain ⟨uM, hm, hae⟩ := mul_rep u
  have hF := ae_rep ν hν w u uM hae
  refine ⟨?_, ?_⟩
  · exact ((measurable_ten3_symOuter hw hm).aestronglyMeasurable).congr hF.symm
  · exact lt_of_le_of_lt (eLpNorm_mul_le ν hν hK hbd u)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp u).2)

/-- The bounded linear multiplier `u ↦ [w⊗u + u⊗w]` into `Lp Ten3 2 ν`. -/
def multOp {c : ℝ} (ν : Measure Chart) (hν : ν ≪ ageμ c (-3 / 2)) {w : Chart → Merid}
    (hw : Measurable w) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ u : Chart → Merid, Measurable u →
      ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂ν ≤
        ENNReal.ofReal K * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2)) :
    Hsp c →L[ℝ] Lp Ten3 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_mul ν hν hw hK hbd u).toLp (fun p => ten3Of (symOuter (w p) (u p)))
      map_add' := by
        intro u v
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        have h : ∀ᵐ p ∂ν, ((u + v : Hsp c) : Chart → Merid) p
            = ((u : Chart → Merid) + (v : Chart → Merid)) p := hν.ae_le (Lp.coeFn_add u v)
        filter_upwards [h] with p hp
        show ten3Of (symOuter (w p) ((u + v : Hsp c) p))
          = ten3Of (symOuter (w p) (u p)) + ten3Of (symOuter (w p) (v p))
        rw [hp, Pi.add_apply, ten3_symOuter_add]
      map_smul' := by
        intro r u
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        have h : ∀ᵐ p ∂ν, ((r • u : Hsp c) : Chart → Merid) p
            = (r • (u : Chart → Merid)) p := hν.ae_le (Lp.coeFn_smul r u)
        filter_upwards [h] with p hp
        show ten3Of (symOuter (w p) ((r • u : Hsp c) p))
          = r • ten3Of (symOuter (w p) (u p))
        rw [hp, Pi.smul_apply, ten3_symOuter_smul] }
    (Real.sqrt K) (fun u => by
      show ‖(memLp_mul ν hν hw hK hbd u).toLp (fun p => ten3Of (symOuter (w p) (u p)))‖ ≤ Real.sqrt K * ‖u‖
      rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
      calc (eLpNorm (fun p => ten3Of (symOuter (w p) (u p))) 2 ν).toReal
          ≤ (ENNReal.ofReal (Real.sqrt K) * eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal :=
            ENNReal.toReal_mono
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).2.ne)
              (eLpNorm_mul_le ν hν hK hbd u)
        _ = Real.sqrt K * (eLpNorm (u : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)])

theorem multOp_ae {c : ℝ} (ν : Measure Chart) (hν : ν ≪ ageμ c (-3 / 2)) {w : Chart → Merid}
    (hw : Measurable w) {K : ℝ} (hK : 0 ≤ K)
    (hbd : ∀ u : Chart → Merid, Measurable u →
      ∫⁻ p, ‖ten3Of (symOuter (w p) (u p))‖ₑ ^ (2 : ℝ) ∂ν ≤
        ENNReal.ofReal K * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2))
    (u : Hsp c) :
    ((multOp ν hν hw hK hbd u : Lp Ten3 2 ν) : Chart → Ten3)
      =ᵐ[ν] fun p => ten3Of (symOuter (w p) (u p)) :=
  MemLp.coeFn_toLp (memLp_mul ν hν hw hK hbd u)

/-! ## The two concrete multipliers -/

theorem hbd_z1 {c : ℝ} (hc : 0 < c) (mZ B₁ : ℝ) {w₁ : Chart → Merid} (hw₁ : Measurable w₁)
    (hA : ∀ p : Chart, 0 < p.1 → Real.sqrt p.1 * transWeight mZ p * ‖w₁ p‖ ≤ B₁) :
    ∀ u : Chart → Merid, Measurable u →
      ∫⁻ p, ‖ten3Of (symOuter (w₁ p) (u p))‖ₑ ^ (2 : ℝ) ∂z1Measure c mZ ≤
        ENNReal.ofReal (4 * B₁ ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
  intro u hu
  have hG : Measurable fun p => ‖ten3Of (symOuter (w₁ p) (u p))‖ₑ ^ (2 : ℝ) :=
    ((measurable_ten3_symOuter hw₁ hu).enorm).pow_const _
  have hWm : Measurable fun p : Chart => ENNReal.ofReal (transWeight mZ p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_transWeight' mZ).pow_const 2)
  have hsm : Measurable fun p : Chart => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have step1 : ∫⁻ p, ‖ten3Of (symOuter (w₁ p) (u p))‖ₑ ^ (2 : ℝ) ∂z1Measure c mZ
      = ∫⁻ p, ENNReal.ofReal (transWeight mZ p ^ 2) * ‖ten3Of (symOuter (w₁ p) (u p))‖ₑ ^ (2 : ℝ)
          ∂ageμ c (-1 / 2) :=
    lintegral_withDensity_eq_lintegral_mul _ hWm hG
  have step2 : ∫⁻ p, ENNReal.ofReal (transWeight mZ p ^ 2) * ‖ten3Of (symOuter (w₁ p) (u p))‖ₑ ^ (2 : ℝ)
        ∂ageμ c (-1 / 2)
      = ∫⁻ p, ENNReal.ofReal p.1 * (ENNReal.ofReal (transWeight mZ p ^ 2)
          * ‖ten3Of (symOuter (w₁ p) (u p))‖ₑ ^ (2 : ℝ)) ∂ageμ c (-3 / 2) := by
    rw [ageμ_half hc]
    exact lintegral_withDensity_eq_lintegral_mul _ hsm (hWm.mul hG)
  rw [step1, step2]
  calc _ ≤ ∫⁻ p, ENNReal.ofReal (4 * B₁ ^ 2) * ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
        lintegral_mono fun p => pt_z1 p mZ B₁ (w₁ p) (u p) (fun hs => hA p hs)
    _ = ENNReal.ofReal (4 * B₁ ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
        lintegral_const_mul _ (hu.enorm.pow_const _)

theorem hbd_ht {c : ℝ} (hc : 0 < c) (ρb B₂ : ℝ) (hρ : 0 < ρb) {w₂ : Chart → Merid}
    (hw₂ : Measurable w₂)
    (hB : ∀ᵐ p ∂ageμ c (-1 / 2), Real.sqrt p.1 * ‖w₂ p‖ ≤ B₂) :
    ∀ u : Chart → Merid, Measurable u →
      ∫⁻ p, ‖ten3Of (symOuter (w₂ p) (u p))‖ₑ ^ (2 : ℝ) ∂htRhoMeasure c ρb ≤
        ENNReal.ofReal (ρb⁻¹ * (4 * B₂ ^ 2)) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
  intro u hu
  have hG : Measurable fun p => ‖ten3Of (symOuter (w₂ p) (u p))‖ₑ ^ (2 : ℝ) :=
    ((measurable_ten3_symOuter hw₂ hu).enorm).pow_const _
  have hsm : Measurable fun p : Chart => ENNReal.ofReal p.1 :=
    ENNReal.measurable_ofReal.comp measurable_fst
  have hB' : ∀ᵐ p ∂ageμ c (-3 / 2), ENNReal.ofReal p.1 ≠ 0 → Real.sqrt p.1 * ‖w₂ p‖ ≤ B₂ := by
    rw [ageμ_half hc] at hB
    exact (ae_withDensity_iff hsm).1 hB
  have hinv : (0 : ℝ) ≤ ρb⁻¹ := inv_nonneg.2 hρ.le
  unfold htRhoMeasure
  rw [lintegral_smul_measure, ageμ_half hc, lintegral_withDensity_eq_lintegral_mul _ hsm hG]
  simp only [Pi.mul_apply]
  calc _ ≤ ENNReal.ofReal ρb⁻¹ *
        ∫⁻ p, ENNReal.ofReal (4 * B₂ ^ 2) * ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_ae (hB'.mono fun p hp =>
          pt_ht p B₂ (w₂ p) (u p) fun hs => hp (ENNReal.ofReal_pos.2 hs).ne')) (by positivity)
    _ = ENNReal.ofReal (ρb⁻¹ * (4 * B₂ ^ 2)) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
        rw [lintegral_const_mul _ (hu.enorm.pow_const _), ENNReal.ofReal_mul hinv, mul_assoc]

end UnforcedLeray.Short.PartIIIb.NearInst.CoeffMult

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIIa CoeffMult

/-- **Coefficient multipliers** (source 2764-2775): see `NearInst/Targets.lean`, `CoeffMultExists`. -/
theorem coeffMultExists : CoeffMultExists := by
  intro c mZ ρb B₁ B₂ w₁ w₂ hc hρ hw₁ hw₂ hA hB
  let M₁ : Hsp c →L[ℝ] Z1sp c mZ :=
    multOp (z1Measure c mZ) (z1_ac hc mZ) hw₁ (K := 4 * B₁ ^ 2) (by positivity)
      (hbd_z1 hc mZ B₁ hw₁ hA)
  let M₂ : Hsp c →L[ℝ] HTrho c ρb :=
    multOp (htRhoMeasure c ρb) (htRho_ac hc ρb) hw₂ (K := ρb⁻¹ * (4 * B₂ ^ 2))
      (mul_nonneg (inv_nonneg.2 hρ.le) (by positivity)) (hbd_ht hc ρb B₂ hρ hw₂ hB)
  refine ⟨(WithLp.prodContinuousLinearEquiv 1 ℝ (Z1sp c mZ) (HTrho c ρb)).symm.toContinuousLinearMap.comp
    (M₁.prod M₂), fun u => ⟨?_, ?_⟩⟩
  · exact multOp_ae (z1Measure c mZ) (z1_ac hc mZ) hw₁ (K := 4 * B₁ ^ 2) (by positivity)
      (hbd_z1 hc mZ B₁ hw₁ hA) u
  · exact multOp_ae (htRhoMeasure c ρb) (htRho_ac hc ρb) hw₂ (K := ρb⁻¹ * (4 * B₂ ^ 2))
      (mul_nonneg (inv_nonneg.2 hρ.le) (by positivity)) (hbd_ht hc ρb B₂ hρ hw₂ hB) u

end UnforcedLeray.Short.PartIIIb.NearInst
