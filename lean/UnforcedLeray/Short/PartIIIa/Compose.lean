import UnforcedLeray.Short.PartIIIa.StressSpaces
import UnforcedLeray.Short.PartIIIa.SeparatedKernels
import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartIIIa.ComposeCorollary
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateL4

/-!
# Part III-a: composed results

Proofs, from the `Prop`s of the statement files, of the parts of this scope that are short
combinations of them:

1. `stress_multiplier_bound`: `stress-short:multiplier` from the coefficient bounds
   (SP 2758-2776): `‖𝓜_Ub‖_Z ≤ (2A + 2√ρ_b)‖b‖_H`, `‖(𝓜_Ub)_2‖_{ρ_b^{-1/2}H_T} ≤ 2√ρ_b‖b‖_H`
   (the coefficients need not be measurable: `z1_symOuter_le`, `repair_entry_le`,
   `zNorm_symOuter_le`).
2. `sepRepair_of_young`: `sep:repair-point`, `sep:repair-global`, `sep:repair-energy` from `sep:young` and its pointwise
   form with `p = 22/19` (SP 3648-3668).
3. (in the imported `ComposeCorollary.lean`) `causal_free_reduction` and
   `polyStressCorollary_of_polyCausal`: `cor:short-polynomial-stress` from
   `prop:short-polynomial-causal` (SP 3560-3581): `b = S_lin F` solves the free equation with
   tensor `F - M₀b`, and the norm bound.
4. `stressMultiplier_of`: `StressCoefficients → StressMultiplier`, the concrete
   `stress-short:multiplier` over `IIb.ExactSplitII` (SP 2703-2778), with the old/young thin
   restrictions and a common positive age weight; the repair bound `√s|v_b| ≤ ρ_b` is
   `repair_coeff_bound` (continuity of `r_b = p.corr z` for `P ≤ 1`, `corr_continuous`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## 1. The split multiplier -/

/-- Raising the age exponent by one multiplies the density by `s`. -/
theorem lintegral_ageμ_succ {c : ℝ} (hc : 0 < c) (a : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ≥0∞}
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

/-- `|a ⊗ b + b ⊗ a|_F² ≤ 4|a|²|b|²` for meridional vectors. -/
theorem frobSq_symOuter_le (a b : Merid) : frobSq (symOuter a b) ≤ 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have ha : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  have hb : ‖b‖ ^ 2 = b 0 ^ 2 + b 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  simp only [frobSq, symOuter, embedMerid, Fin.sum_univ_three, ha, hb]
  simp
  nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0)]

theorem enorm_rpow_two (x : Merid) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_num

theorem measurable_frobSq_symOuter {v b : ℝ × (ℝ × ℝ) → Merid} (hv : Measurable v)
    (hb : Measurable b) : Measurable fun p => frobSq (symOuter (v p) (b p)) := by
  have hv0 : Measurable fun p => v p 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable.comp hv
  have hv1 : Measurable fun p => v p 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable.comp hv
  have hb0 : Measurable fun p => b p 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable.comp hb
  have hb1 : Measurable fun p => b p 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable.comp hb
  simp only [frobSq, symOuter, embedMerid, Fin.sum_univ_three]
  simp
  fun_prop

theorem measurable_transWeight (mZ : ℝ) : Measurable (transWeight mZ) := by
  unfold transWeight
  fun_prop

/-- The change of density: if `s·G ≤ K‖b‖²` pointwise on `s > 0`, then
`∫ G dageμ(-1/2) ≤ K ∫‖b‖² dageμ(-3/2)`. -/
theorem core_bound {c : ℝ} (hc : 0 < c) {G : ℝ × (ℝ × ℝ) → ℝ≥0∞} (hG : Measurable G)
    {b : ℝ × (ℝ × ℝ) → Merid} (K : ℝ)
    (h : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 →
      ENNReal.ofReal p.1 * G p ≤ ENNReal.ofReal K * ‖b p‖ₑ ^ (2 : ℝ)) :
    ∫⁻ p, G p ∂ageμ c (-1 / 2) ≤ ENNReal.ofReal K * hNormSq c b := by
  have e : (-1 / 2 : ℝ) = -3 / 2 + 1 := by norm_num
  rw [e, lintegral_ageμ_succ hc _ hG, hNormSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun p => ?_
  by_cases hp : 0 < p.1
  · exact h p hp
  · have : ENNReal.ofReal p.1 = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hp)
    simp [this]

/-- `ageμ`-almost every chart point has positive age. -/
theorem ae_pos_ageμ (c a : ℝ) : ∀ᵐ p ∂ageμ c a, 0 < p.1 := by
  have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a)), 0 < s :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  unfold ageμ
  exact Measure.quasiMeasurePreserving_fst.ae h1

/-- `core_bound` for an arbitrary (not necessarily measurable) integrand `G`. -/
theorem core_bound_of_le {c : ℝ} (hc : 0 < c) {G : ℝ × (ℝ × ℝ) → ℝ≥0∞}
    {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b) (K : ℝ)
    (h : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 →
      ENNReal.ofReal p.1 * G p ≤ ENNReal.ofReal K * ‖b p‖ₑ ^ (2 : ℝ)) :
    ∫⁻ p, G p ∂ageμ c (-1 / 2) ≤ ENNReal.ofReal K * hNormSq c b := by
  have hH : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal p.1⁻¹ * (ENNReal.ofReal K * ‖b p‖ₑ ^ (2 : ℝ)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.inv).mul
      (measurable_const.mul (hb.enorm.pow_const _))
  have hGH : ∀ᵐ p ∂ageμ c (-1 / 2),
      G p ≤ ENNReal.ofReal p.1⁻¹ * (ENNReal.ofReal K * ‖b p‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [ae_pos_ageμ c (-1 / 2)] with p hp
    calc G p = ENNReal.ofReal p.1⁻¹ * (ENNReal.ofReal p.1 * G p) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hp.le), inv_mul_cancel₀ hp.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ _ := mul_le_mul_right (h p hp) _
  refine (lintegral_mono_ae hGH).trans (core_bound hc hH K fun p hp => ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one,
    one_mul]

theorem ofReal_sq_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (x ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hx]

/-- The thin entry (SP 2773-2774): if `√s W|v| ≤ A` then `‖v⊗b + b⊗v‖_{Z₁} ≤ 2A‖b‖_H` (the
coefficient `v` need not be measurable). -/
theorem z1_symOuter_le {c mZ A : ℝ} (hc : 0 < c) (hA0 : 0 ≤ A) {v b : ℝ × (ℝ × ℝ) → Merid}
    (hb : Measurable b)
    (hA : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * transWeight mZ p * ‖v p‖ ≤ A) :
    z1NormSq c mZ (fun p => symOuter (v p) (b p)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * A) * hNormSq c b ^ (1 / 2 : ℝ) := by
  have h1 : z1NormSq c mZ (fun p => symOuter (v p) (b p)) ≤
      ENNReal.ofReal ((2 * A) ^ 2) * hNormSq c b := by
    refine core_bound_of_le hc hb _ fun p hp => ?_
    have hs : 0 < p.1 := hp
    have hW : 0 ≤ transWeight mZ p := by unfold transWeight; positivity
    have hF := frobSq_symOuter_le (v p) (b p)
    have hA' := hA p hs
    have hAA : (Real.sqrt p.1 * transWeight mZ p * ‖v p‖) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by positivity) hA' 2
    have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hs.le
    rw [← ENNReal.ofReal_mul hs.le, enorm_rpow_two, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : p.1 * (transWeight mZ p ^ 2 * frobSq (symOuter (v p) (b p))) ≤
        p.1 * (transWeight mZ p ^ 2 * (4 * ‖v p‖ ^ 2 * ‖b p‖ ^ 2)) := by
      gcongr
    calc p.1 * (transWeight mZ p ^ 2 * frobSq (symOuter (v p) (b p)))
        ≤ p.1 * (transWeight mZ p ^ 2 * (4 * ‖v p‖ ^ 2 * ‖b p‖ ^ 2)) := this
      _ = 4 * (Real.sqrt p.1 * transWeight mZ p * ‖v p‖) ^ 2 * ‖b p‖ ^ 2 := by
        rw [mul_pow, mul_pow, hss]; ring
      _ ≤ 4 * A ^ 2 * ‖b p‖ ^ 2 := by gcongr
      _ = (2 * A) ^ 2 * ‖b p‖ ^ 2 := by ring
  calc _ ≤ (ENNReal.ofReal ((2 * A) ^ 2) * hNormSq c b) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_sq_rpow_half (by positivity)]

/-- The repair entry (SP 2775-2776): if `√s|v_b| ≤ ρ` then `‖v_b⊗b + b⊗v_b‖_{H_T} ≤ 2ρ‖b‖_H`
(the coefficient `v_b` need not be measurable). -/
theorem ht_symOuter_le {c ρ : ℝ} (hc : 0 < c) (hρ0 : 0 ≤ ρ) {vb b : ℝ × (ℝ × ℝ) → Merid}
    (hb : Measurable b)
    (hR : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * ‖vb p‖ ≤ ρ) :
    htNormSq c (fun p => symOuter (vb p) (b p)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * ρ) * hNormSq c b ^ (1 / 2 : ℝ) := by
  have h2 : htNormSq c (fun p => symOuter (vb p) (b p)) ≤
      ENNReal.ofReal ((2 * ρ) ^ 2) * hNormSq c b := by
    refine core_bound_of_le hc hb _ fun p hp => ?_
    have hs : 0 < p.1 := hp
    have hF := frobSq_symOuter_le (vb p) (b p)
    have hR' := hR p hs
    have hRR : (Real.sqrt p.1 * ‖vb p‖) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by positivity) hR' 2
    have hss : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hs.le
    rw [← ENNReal.ofReal_mul hs.le, enorm_rpow_two, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc p.1 * frobSq (symOuter (vb p) (b p))
        ≤ p.1 * (4 * ‖vb p‖ ^ 2 * ‖b p‖ ^ 2) := by gcongr
      _ = 4 * (Real.sqrt p.1 * ‖vb p‖) ^ 2 * ‖b p‖ ^ 2 := by rw [mul_pow, hss]; ring
      _ ≤ 4 * ρ ^ 2 * ‖b p‖ ^ 2 := by gcongr
      _ = (2 * ρ) ^ 2 * ‖b p‖ ^ 2 := by ring
  calc _ ≤ (ENNReal.ofReal ((2 * ρ) ^ 2) * hNormSq c b) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_sq_rpow_half (by positivity)]

theorem rpow_neg_half_mul_two {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (-1 / 2 : ℝ) * (2 * ρ) = 2 * ρ ^ (1 / 2 : ℝ) := by
  have : ρ ^ (1 / 2 : ℝ) = ρ ^ (-1 / 2 : ℝ) * ρ := by
    conv_lhs => rw [show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num]
    rw [Real.rpow_add hρ, Real.rpow_one]
  rw [this]; ring

/-- The second estimate of `stress-short:multiplier` (SP 2766-2769, 2775-2776):
`‖(𝓜_Ub)_2‖_{ρ_b^{-1/2}H_T} ≤ 2√ρ_b‖b‖_H` when `√s|v_b| ≤ ρ_b`. -/
theorem repair_entry_le {c ρb : ℝ} (hc : 0 < c) (hρ : 0 < ρb) {vb b : ℝ × (ℝ × ℝ) → Merid}
    (hb : Measurable b)
    (hR : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * ‖vb p‖ ≤ ρb) :
    ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) *
        htNormSq c (fun p => symOuter (vb p) (b p)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * ρb ^ (1 / 2 : ℝ)) * hNormSq c b ^ (1 / 2 : ℝ) := by
  calc _ ≤ ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal (2 * ρb) * hNormSq c b ^ (1 / 2 : ℝ)) := by
        gcongr
        exact ht_symOuter_le hc hρ.le hb hR
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), rpow_neg_half_mul_two hρ]

/-- The first estimate of `stress-short:multiplier` with explicit constant:
`‖𝓜_Ub‖_Z ≤ (2A + 2√ρ_b)‖b‖_H` (the coefficients need not be measurable). -/
theorem zNorm_symOuter_le {c mZ ρb A : ℝ} (hc : 0 < c) (hρ : 0 < ρb) (hA0 : 0 ≤ A)
    {v vb b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b)
    (hA : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * transWeight mZ p * ‖v p‖ ≤ A)
    (hR : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * ‖vb p‖ ≤ ρb) :
    zNorm c mZ ρb (fun p => symOuter (v p) (b p)) (fun p => symOuter (vb p) (b p)) ≤
      ENNReal.ofReal (2 * A + 2 * ρb ^ (1 / 2 : ℝ)) * hNormSq c b ^ (1 / 2 : ℝ) := by
  unfold zNorm
  calc _ ≤ ENNReal.ofReal (2 * A) * hNormSq c b ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (2 * ρb ^ (1 / 2 : ℝ)) * hNormSq c b ^ (1 / 2 : ℝ) :=
        add_le_add (z1_symOuter_le hc hA0 hb hA) (repair_entry_le hc hρ hb hR)
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **`stress-short:multiplier`** (SP 2758-2776), coefficient form. If `√s W|v| ≤ A` and
`√s|v_b| ≤ ρ_b` (`√s v_b = r_b`, `‖r_b‖_∞ ≤ ρ_b`), then for every measurable `b`
`‖v⊗b + b⊗v‖_{Z₁} ≤ 2A‖b‖_H`, `‖v_b⊗b + b⊗v_b‖_{H_T} ≤ 2ρ_b‖b‖_H` and
`‖𝓜_Ub‖_Z ≤ (2A + 2√ρ_b)‖b‖_H`.  The concrete form over `IIb.ExactSplitII` is
`stressMultiplier_of` below. -/
theorem stress_multiplier_bound {c mZ ρb A : ℝ} (hc : 0 < c) (hρ : 0 < ρb) (hA0 : 0 ≤ A)
    {v vb b : ℝ × (ℝ × ℝ) → Merid} (hv : Measurable v) (hvb : Measurable vb) (hb : Measurable b)
    (hA : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * transWeight mZ p * ‖v p‖ ≤ A)
    (hR : ∀ p : ℝ × (ℝ × ℝ), 0 < p.1 → Real.sqrt p.1 * ‖vb p‖ ≤ ρb) :
    z1NormSq c mZ (fun p => symOuter (v p) (b p)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (2 * A) * hNormSq c b ^ (1 / 2 : ℝ) ∧
      htNormSq c (fun p => symOuter (vb p) (b p)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (2 * ρb) * hNormSq c b ^ (1 / 2 : ℝ) ∧
      zNorm c mZ ρb (fun p => symOuter (v p) (b p)) (fun p => symOuter (vb p) (b p)) ≤
        ENNReal.ofReal (2 * A + 2 * ρb ^ (1 / 2 : ℝ)) * hNormSq c b ^ (1 / 2 : ℝ) :=
  ⟨z1_symOuter_le hc hA0 hb hA, ht_symOuter_le hc hρ.le hb hR,
    zNorm_symOuter_le hc hρ hA0 hb hA hR⟩

/-! ## 2. The repair estimates from `sep:young` -/

/-- **`sep:repair-point`, `sep:repair-global`, `sep:repair-energy`** (SP 3648-3668) are the
instances `p = 22/19` of `sep:young` and its pointwise version (the condition
`inf_K(2Re μ + 3/p) > 0` holds with `δ = 23/11` since `Re μ > -1/4`). -/
theorem sepRepair_of_young (hY : SepYoung) (hP : SepYoungPointwise) : SepRepair := by
  intro K hK hRe
  have hδ : ∀ μ ∈ K, (23 / 11 : ℝ) ≤ 2 * μ.re + 3 / (22 / 19 : ℝ) := by
    intro μ hμ
    have := hRe μ hμ
    norm_num
    linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hP K hK hRe 1 (22 / 19) (22 / 3) (by norm_num) (by norm_num)
      (by norm_num) ⟨23 / 11, by norm_num, hδ⟩
    refine ⟨C, hC0, fun ν hν μ hμ rOut rIn P h0 hlt hP0 T hT y hy => ?_⟩
    have h := hC ν hν μ hμ rOut rIn P h0 hlt hP0 T hT y hy
    have e : (-4 - ((1 : ℕ) : ℝ) + 3 / (22 / 3) : ℝ) = -(101 / 22) := by norm_num
    rwa [e] at h
  · obtain ⟨C, hC0, hC⟩ := hY K hK hRe 1 (22 / 19) (22 / 3) (11 / 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ⟨23 / 11, by norm_num, hδ⟩
    refine ⟨C, hC0, fun ν hν μ hμ rOut rIn P h0 hlt hP0 T hT => ?_⟩
    have h := hC ν hν μ hμ rOut rIn P h0 hlt hP0 T hT
    have e : (-4 - ((1 : ℕ) : ℝ) + 3 / (11 / 3) : ℝ) = -(46 / 11) := by norm_num
    rwa [e] at h
  · intro j
    obtain ⟨C, hC0, hC⟩ := hY K hK hRe j (22 / 19) 2 (11 / 7) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ⟨23 / 11, by norm_num, hδ⟩
    refine ⟨C, hC0, fun ν hν μ hμ rOut rIn P h0 hlt hP0 T hT => ?_⟩
    have h := hC ν hν μ hμ rOut rIn P h0 hlt hP0 T hT
    have e : (-4 - (j : ℝ) + 3 / (11 / 7) : ℝ) = -(23 / 11 : ℝ) - (j : ℝ) := by norm_num; ring
    rwa [e] at h

/-! ## 3. The lifts -/

/-- **`stress-short:lifts`** (SP 2683-2688) from `Axi.lintegral_Nv_rpow` and
`Axi.lintegral_NT_sq`. -/
theorem stressLifts : StressLifts := by
  refine ⟨fun R c P hR hc hP b hb hper => ?_, fun R c P hR hc hP T hT hTm hper => ?_⟩
  · have h := lintegral_Nv_rpow (q := 2) hR hc hP (by norm_num) hb hper
    have e : (2 / 2 - 5 / 2 : ℝ) = -3 / 2 := by norm_num
    rw [e] at h
    exact h
  · exact lintegral_NT_sq hR hc hP hT hTm hper

/-! ## 4. `stress-short:multiplier` over the concrete exact split -/

section ConcreteMultiplier

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.IIb UnforcedLeray.B0412
  UnforcedLeray.B0449

/-- `a ⊗ (tb) + (tb) ⊗ a = t(a ⊗ b + b ⊗ a)`. -/
theorem symOuter_smul_right (a b : Merid) (t : ℝ) : symOuter a (t • b) = t • symOuter a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symOuter, embedMerid] <;> ring

theorem symOuter_zero_right (a : Merid) : symOuter a 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symOuter, embedMerid]

/-- The meridional part `(x_0, x_2)` of a vector at a point of the half-plane `φ = 0`. -/
theorem norm_meridPart_le (x : EuclideanSpace ℝ (Fin 3)) :
    ‖(!₂[x 0, x 2] : Merid)‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [Fin.sum_univ_two, Fin.sum_univ_three] <;> nlinarith [sq_nonneg (x 1)]

/-- `√s |s^{-1/2}V| ≤ |V|` at the chart point (SP 2711, 2775: `√s v_b = r_b`). -/
theorem sqrt_mul_norm_chartCoeff (R : ℝ)
    (V : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (pt : ℝ × (ℝ × ℝ))
    (hpt : 0 < pt.1) :
    Real.sqrt pt.1 * ‖chartCoeff R V pt‖ ≤
      ‖V (2 * pt.2.1 / R + Real.log pt.1)
        (!₂[R / Real.sqrt pt.1, 0, pt.2.2 / Real.sqrt pt.1])‖ := by
  have hs : 0 < Real.sqrt pt.1 := Real.sqrt_pos.2 hpt
  rw [chartCoeff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, ← mul_assoc,
    mul_inv_cancel₀ hs.ne', one_mul]
  exact norm_meridPart_le _

/-- The period `P = 2εc ≤ 1` once `ν ≤ d₋³/12` (`ε = e^{-d/ν}`, `c = ν⁻²`, `e^x ≥ x³/6`). -/
theorem period_le_one_of_small {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (hν : p.ν ≤ dm ^ 3 / 12) : p.period ≤ 1 := by
  have hν0 := p.ν_pos
  have hdm := hreg.dm_pos
  have hd : 0 < d := lt_of_lt_of_le hdm hreg.dm_le
  have hx : 0 ≤ d / p.ν := by positivity
  have he := Real.pow_div_factorial_le_exp (d / p.ν) hx 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at he
  have hd3 : dm ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hdm.le hreg.dm_le 3
  have hνne : p.ν ≠ 0 := hν0.ne'
  have key : (d / p.ν) ^ 3 / 6 * p.ν ^ 2 = d ^ 3 / (6 * p.ν) := by
    field_simp <;> ring
  have h2 : 2 ≤ d ^ 3 / (6 * p.ν) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hE : 0 < Real.exp (d / p.ν) := Real.exp_pos _
  have hEν : 2 ≤ Real.exp (d / p.ν) * p.ν ^ 2 :=
    calc (2 : ℝ) ≤ d ^ 3 / (6 * p.ν) := h2
      _ = (d / p.ν) ^ 3 / 6 * p.ν ^ 2 := key.symm
      _ ≤ Real.exp (d / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right he (by positivity)
  unfold Params.period
  rw [hreg.eps_eq, hreg.c_eq, neg_div, Real.exp_neg]
  rw [show 2 * (Real.exp (d / p.ν))⁻¹ * (p.ν ^ 2)⁻¹ = 2 / (Real.exp (d / p.ν) * p.ν ^ 2) by
    rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv]]
  rw [div_le_one (by positivity)]
  exact hEν

local instance fact_one_le_q0_stressMultiplier : Fact (1 ≤ ENNReal.ofReal UnforcedLeray.B0281.q0) :=
  ⟨by norm_num [UnforcedLeray.B0281.q0]⟩

/-- The energy repair `r_b = p.corr z` of a state is jointly continuous when `P ≤ 1` (the B0449
continuous chart representative agrees with the selected `contRep` everywhere,
`Params.graph_globalRep_eq_corr`). -/
theorem corr_continuous (p : Params) (hP1 : p.period ≤ 1) (z : p.Z) :
    Continuous (fun x : ℝ × Space => p.corr z x.1 x.2) := by
  have hq : UnforcedLeray.B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
    rw [UnforcedLeray.B0281.q0_eq]
    exact UnforcedLeray.B0276.holderConjugate
  have hq' : 5 / 2 < UnforcedLeray.B0281.q0 := by norm_num [UnforcedLeray.B0281.q0]
  refine (continuous_globalRealChartRep hP1 hq hq' p.ν_pos (hasPhaseOp_T0X (p.graphX z))
    (hasPhaseOp_nuLapX (p.graphX z))).congr ?_
  intro x
  exact p.graph_globalRep_eq_corr hP1 z x.1 x.2

/-- For a continuous field an `L^∞` bound holds at every point. -/
theorem norm_le_of_continuous_eLpNorm_top {f : Space → Space} (hf : Continuous f) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (h : eLpNorm f ⊤ volume ≤ ENNReal.ofReal ρ) (y : Space) : ‖f y‖ ≤ ρ := by
  have hae : ∀ᵐ y ∂(volume : Measure Space), ‖f y‖ ≤ ρ := by
    filter_upwards [ae_le_eLpNormEssSup (μ := (volume : Measure Space)) (f := f)] with y hy
    rw [eLpNorm_exponent_top] at h
    have h' := hy.trans h
    rw [← ofReal_norm] at h'
    exact (ENNReal.ofReal_le_ofReal_iff hρ).1 h'
  have hd := Measure.dense_of_ae hae
  have hcl : IsClosed {y | ‖f y‖ ≤ ρ} := isClosed_le (continuous_norm.comp hf) continuous_const
  have huniv : {y | ‖f y‖ ≤ ρ} = univ := by
    rw [← hcl.closure_eq]
    exact hd.closure_eq
  have hy : y ∈ {y | ‖f y‖ ≤ ρ} := huniv ▸ mem_univ y
  exact hy

/-- **The repair coefficient** (SP 2703-2711, 2775): for an exact split, `√s|v_b| ≤ ρ_b` at
every chart point with `s > 0`, `v_b = chartCoeff p.R r_b` (`r_b = p.corr z` is continuous for
`P ≤ 1`, so the `L^∞` bound of `ExactSplitII.energy` holds pointwise). -/
theorem repair_coeff_bound {p : Params} {ρb S_in : ℝ} {V rb : ℝ → SpatialField}
    (hP1 : p.period ≤ 1) (hρ : 0 ≤ ρb) (hs : ExactSplitII p ρb S_in V rb)
    (pt : ℝ × (ℝ × ℝ)) (hpt : 0 < pt.1) :
    Real.sqrt pt.1 * ‖chartCoeff p.R rb pt‖ ≤ ρb := by
  obtain ⟨z, -, -, hrb, -⟩ := hs.state
  refine (sqrt_mul_norm_chartCoeff p.R rb pt hpt).trans ?_
  have hcont : Continuous fun y => rb (2 * pt.2.1 / p.R + Real.log pt.1) y := by
    rw [hrb]
    exact (corr_continuous p hP1 z).comp (continuous_const.prodMk continuous_id)
  have htop : eLpNorm (rb (2 * pt.2.1 / p.R + Real.log pt.1)) ⊤ volume ≤ ENNReal.ofReal ρb :=
    le_trans le_add_self (hs.energy _)
  exact norm_le_of_continuous_eLpNorm_top hcont hρ htop _

/-- **`stress-short:multiplier`** (SP 2758-2778) over the concrete exact split, from
`stress-short:coefficients` (SP 2711-2723) and the repair bound `‖r_b‖_∞ ≤ ρ_b` of
`IIb.ExactSplitII` (SP 2703-2709): `P_ν = (2|C| + 2 + 2C₀)ν^{-(k+k₀)}` absorbs `2Cν^{-k}` and
`2√ρ_b ≤ 2 + 2C₀ν^{-k₀}` (`e^{m₀/ν}ε^{3/11} ≤ 1` since `m₀ ≤ 3d/11`). The slow data `(Σ, λ, q)`
of the inlet are passed through unchanged. -/
theorem stressMultiplier_of (hC : StressCoefficients) : StressMultiplier := by
  intro dm dp hdm m0 C0 k0 hm0 hm0le hC0 mZ hmZ Sig lam q hSig hq
  obtain ⟨C, k, ν₀, hν₀, hcoef⟩ := hC dm dp hdm m0 C0 k0 hm0 hm0le mZ hmZ Sig lam q hSig hq
  refine ⟨2 * |C| + 2 + 2 * C0, k + k0, min ν₀ (min 1 (dm ^ 3 / 12)),
    lt_min hν₀ (lt_min one_pos (by positivity)), ?_⟩
  intro p d hreg hν hSg hmode S_in V rb hsplit w hw _hwpos b hb v vb ρb wb
  have hνpos := p.ν_pos
  have hνν₀ : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνdm : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 := period_le_one_of_small hreg hνdm
  obtain ⟨hc1, hc2, hc3, -⟩ := hcoef p d hreg hνν₀ hSg hmode S_in V rb hsplit
  have hx1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
  have hA0 : 0 ≤ C * (p.ν⁻¹) ^ k := by
    have h := hc1 ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) one_pos
    have hW : 0 ≤ transWeight mZ ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
      unfold transWeight; positivity
    exact le_trans (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hW) (norm_nonneg _)) h
  have hρpos : 0 < ρb := by
    show 0 < rhoB p m0 C0 k0
    unfold rhoB
    have := p.ε_pos
    positivity
  have hρle : ρb ≤ C0 * (p.ν⁻¹) ^ k0 := by
    show rhoB p m0 C0 k0 ≤ _
    unfold rhoB
    have hεe : p.ε ^ (3 / 11 : ℝ) = Real.exp (-d / p.ν * (3 / 11)) := by
      rw [hreg.eps_eq, ← Real.exp_mul]
    have hexp : Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ) ≤ 1 := by
      rw [hεe, ← Real.exp_add]
      apply Real.exp_le_one_iff.2
      have hm : m0 ≤ 3 * d / 11 := hm0le.trans (by have := hreg.dm_le; linarith)
      have he : m0 / p.ν + -d / p.ν * (3 / 11) = (m0 - 3 * d / 11) / p.ν := by ring
      rw [he]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hνpos.le
    rw [inv_pow]
    have hk0 : 0 ≤ C0 * (p.ν ^ k0)⁻¹ := by positivity
    calc C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ)
        = C0 * (p.ν ^ k0)⁻¹ * (Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ)) := by ring
      _ ≤ C0 * (p.ν ^ k0)⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hk0
      _ = C0 * (p.ν ^ k0)⁻¹ := mul_one _
  have hxk : (p.ν⁻¹) ^ k ≤ (p.ν⁻¹) ^ (k + k0) := pow_le_pow_right₀ hx1 (Nat.le_add_right _ _)
  have hxk0 : (p.ν⁻¹) ^ k0 ≤ (p.ν⁻¹) ^ (k + k0) := pow_le_pow_right₀ hx1 (Nat.le_add_left _ _)
  have hxK1 : 1 ≤ (p.ν⁻¹) ^ (k + k0) := one_le_pow₀ hx1
  have hCabs : C * (p.ν⁻¹) ^ k ≤ |C| * (p.ν⁻¹) ^ (k + k0) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hxk (abs_nonneg C))
  have hC0K : C0 * (p.ν⁻¹) ^ k0 ≤ C0 * (p.ν⁻¹) ^ (k + k0) :=
    mul_le_mul_of_nonneg_left hxk0 hC0.le
  have hsqrtρ : ρb ^ (1 / 2 : ℝ) ≤ 1 + ρb := by
    calc ρb ^ (1 / 2 : ℝ) = Real.sqrt ρb := (Real.sqrt_eq_rpow ρb).symm
      _ ≤ Real.sqrt ((1 + ρb) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + ρb := Real.sqrt_sq (by linarith)
  have hsqrt0 : 0 ≤ ρb ^ (1 / 2 : ℝ) := by positivity
  have hpoly : 2 * (C * (p.ν⁻¹) ^ k) + 2 * ρb ^ (1 / 2 : ℝ) ≤
      (2 * |C| + 2 + 2 * C0) * (p.ν⁻¹) ^ (k + k0) := by
    nlinarith
  have h2A : 2 * (C * (p.ν⁻¹) ^ k) ≤ (2 * |C| + 2 + 2 * C0) * (p.ν⁻¹) ^ (k + k0) := by
    linarith
  have hR : ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → Real.sqrt pt.1 * ‖vb pt‖ ≤ ρb :=
    fun pt hpt => repair_coeff_bound hP1 hρpos.le hsplit pt hpt
  have hwb : Measurable wb := (hw.comp measurable_fst).smul hb
  have hfun1 : (fun pt : ℝ × (ℝ × ℝ) => w pt.1 • symOuter (v pt) (b pt)) =
      fun pt => symOuter (v pt) (wb pt) := by
    funext pt
    exact (symOuter_smul_right _ _ _).symm
  have hfun2 : (fun pt : ℝ × (ℝ × ℝ) => w pt.1 • symOuter (vb pt) (b pt)) =
      fun pt => symOuter (vb pt) (wb pt) := by
    funext pt
    exact (symOuter_smul_right _ _ _).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun1, hfun2]
    refine (zNorm_symOuter_le p.c_pos hρpos hA0 hwb hc1 hR).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hpoly) _
  · rw [hfun2]
    exact repair_entry_le p.c_pos hρpos hwb hR
  · intro S hS hS0
    have hX : 0 ≤ S ^ (-1 / 2 : ℝ) + p.ε := by
      have := p.ε_pos
      positivity
    have hfun : (fun pt : ℝ × (ℝ × ℝ) =>
        if S < pt.1 then w pt.1 • symOuter (v pt) (b pt) else 0) =
        fun pt => symOuter (if S < pt.1 then v pt else 0) (if S < pt.1 then wb pt else 0) := by
      funext pt
      by_cases h : S < pt.1
      · rw [if_pos h, if_pos h, if_pos h]
        exact (symOuter_smul_right _ _ _).symm
      · rw [if_neg h, if_neg h, if_neg h]
        exact (symOuter_zero_right _).symm
    have hA' : ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → Real.sqrt pt.1 * transWeight mZ pt *
        ‖(if S < pt.1 then v pt else 0)‖ ≤ C * (p.ν⁻¹) ^ k * (S ^ (-1 / 2 : ℝ) + p.ε) := by
      intro pt hpt
      by_cases h : S < pt.1
      · rw [if_pos h]
        exact hc2 S hS hS0 pt h
      · rw [if_neg h, norm_zero, mul_zero]
        exact mul_nonneg hA0 hX
    have hmeas : Measurable fun pt : ℝ × (ℝ × ℝ) => if S < pt.1 then wb pt else 0 :=
      Measurable.ite (measurableSet_lt measurable_const measurable_fst) hwb measurable_const
    rw [hfun]
    refine (z1_symOuter_le (v := fun pt => if S < pt.1 then v pt else 0) p.c_pos
      (mul_nonneg hA0 hX) hmeas hA').trans ?_
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    calc 2 * (C * (p.ν⁻¹) ^ k * (S ^ (-1 / 2 : ℝ) + p.ε))
        = 2 * (C * (p.ν⁻¹) ^ k) * (S ^ (-1 / 2 : ℝ) + p.ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2A hX
  · intro σ hσ hσ1
    have hX : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
    have hfun : (fun pt : ℝ × (ℝ × ℝ) =>
        if pt.1 < σ then w pt.1 • symOuter (v pt) (b pt) else 0) =
        fun pt => symOuter (if pt.1 < σ then v pt else 0) (if pt.1 < σ then wb pt else 0) := by
      funext pt
      by_cases h : pt.1 < σ
      · rw [if_pos h, if_pos h, if_pos h]
        exact (symOuter_smul_right _ _ _).symm
      · rw [if_neg h, if_neg h, if_neg h]
        exact (symOuter_zero_right _).symm
    have hA' : ∀ pt : ℝ × (ℝ × ℝ), 0 < pt.1 → Real.sqrt pt.1 * transWeight mZ pt *
        ‖(if pt.1 < σ then v pt else 0)‖ ≤ C * (p.ν⁻¹) ^ k * Real.sqrt σ := by
      intro pt hpt
      by_cases h : pt.1 < σ
      · rw [if_pos h]
        exact hc3 σ hσ hσ1 pt hpt h
      · rw [if_neg h, norm_zero, mul_zero]
        exact mul_nonneg hA0 hX
    have hmeas : Measurable fun pt : ℝ × (ℝ × ℝ) => if pt.1 < σ then wb pt else 0 :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_const) hwb measurable_const
    rw [hfun]
    refine (z1_symOuter_le (v := fun pt => if pt.1 < σ then v pt else 0) p.c_pos
      (mul_nonneg hA0 hX) hmeas hA').trans ?_
    apply mul_le_mul_left
    apply ENNReal.ofReal_le_ofReal
    calc 2 * (C * (p.ν⁻¹) ^ k * Real.sqrt σ)
        = 2 * (C * (p.ν⁻¹) ^ k) * Real.sqrt σ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2A hX

end ConcreteMultiplier

end UnforcedLeray.Short.IIIa
