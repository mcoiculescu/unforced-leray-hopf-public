import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# `PartI:T18` (`TrainStrainIntegralProof.lean`): the integrated train strain estimate

Source of record: `the November 2 reference manuscript`, lines 318-319, 425-436:
whenever `a(s₀) ≤ c²` (`s₀ = σ₀ / ν`, `a(s₀) = 1 + σ₀`),
`∫_{s₀}^∞ ∑_{j=1}^{k+1} ‖D^j v(s)‖_∞ ds ≤ C_k / (ν a(s₀)) + C_k e_c`
(`B0278.TrainStrainEstimate k Ck ν c σ₀ tr.v`).

Route:
1. For each `j ≥ 1`, before overlap (`0 ≤ s ≤ s_c`, `1 ≤ width ν s ≤ c²`), decompose
   `tr.v s = (tr.v s - Vc ν c s) + Vc ν c s` in `B0277.supNormD j`. Using `Train.Vc_bounds j 0`,
   `trainComparison_proof` (`PartI:T10`), and `a^{-(5+j)/2} e^{-b c²/a} ≤ b⁻¹ c⁻² a⁻²` for
   `a ≥ 1`, `j ≥ 1`, we obtain `B0277.supNormD j (tr.v s) ≤ ofReal (C_j * (width ν s ^ 2)⁻¹)`.
2. For each `j ≥ 1`, after overlap (`s ≥ s_c`, `T = ν (s - s_c) / c² ≥ 0`), rescale
   `tr.v s = scaleField c⁻¹ (U T)` (`U = overlapField ν c tr.v`), decompose
   `U T = M + hfluct 1 (U T)` where `M y = hmean 1 (U T) y.2`, and use `hOv : TrainOverlap` to
   bound `B0277.supNormD j (tr.v s) ≤ ofReal (C_j * (c ^ 4)⁻¹ * (1 + T) ^ (-3/2))`.
3. Summing over `j ∈ Icc 1 (k + 1)` and splitting `∫⁻ s in Ioi (σ₀ / ν)` at `s_c` into
   `Ioc (σ₀ / ν) s_c` and `Ioi s_c`, the pre-overlap integral of `(1 + ν s)⁻²` gives
   `≤ K / (ν (1 + σ₀))` and the post-overlap integral of `(c ^ 4)⁻¹ (1 + ν (s - s_c) / c²)^{-3/2}`
   gives `2 K / (ν c²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1. `supNormD` helpers: triangle inequality, `Vc` bound, and vertical profile bound -/

/-- Triangle inequality for `B0277.supNormD j` on smooth vector fields. -/
theorem supNormD_add_le (j : ℕ) {f g : Plane → Vec}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    B0277.supNormD j (fun z => f z + g z) ≤ B0277.supNormD j f + B0277.supNormD j g := by
  have hj_top : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  unfold B0277.supNormD
  apply iSup_le
  intro z
  have hadd : iteratedFDeriv ℝ j (fun w => f w + g w) z =
      iteratedFDeriv ℝ j f z + iteratedFDeriv ℝ j g z :=
    iteratedFDeriv_add_apply (hf.contDiffAt.of_le hj_top) (hg.contDiffAt.of_le hj_top)
  rw [hadd]
  calc ‖iteratedFDeriv ℝ j f z + iteratedFDeriv ℝ j g z‖ₑ
      ≤ ‖iteratedFDeriv ℝ j f z‖ₑ + ‖iteratedFDeriv ℝ j g z‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ (⨆ w, ‖iteratedFDeriv ℝ j f w‖ₑ) + (⨆ w, ‖iteratedFDeriv ℝ j g w‖ₑ) :=
        add_le_add (le_iSup (fun w => ‖iteratedFDeriv ℝ j f w‖ₑ) z)
          (le_iSup (fun w => ‖iteratedFDeriv ℝ j g w‖ₑ) z)

/-- Pre-overlap `B0277.supNormD j` bound for `Vc ν c s` at order `j ≥ 1`:
`B0277.supNormD j (Vc ν c s) ≤ ENNReal.ofReal (CV * (width ν s ^ 2)⁻¹)` for `1 ≤ width ν s ≤ c²`. -/
theorem preOverlap_Vc_supNormD_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ CV : ℝ, 0 < CV ∧
      ∀ ν c s : ℝ, 0 < c → 1 ≤ width ν s → width ν s ≤ c ^ 2 →
        B0277.supNormD j (Vc ν c s) ≤ ENNReal.ofReal (CV * (width ν s ^ 2)⁻¹) := by
  obtain ⟨C, _, hC, _, hVc⟩ := Train.Vc_bounds j 0
  let K : ℝ := 2 * 2 ^ j * C
  have hK_nn : 0 ≤ K := by positivity
  refine ⟨1 + K, by positivity, fun ν c s hc ha1 hac => ?_⟩
  have ha0 : 0 < width ν s := zero_lt_one.trans_le ha1
  have hV_sm : ContDiff ℝ ∞ (Vc ν c s) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc ha0
  apply B0277.supNormD_le_ofReal
  intro z
  have hword : ∀ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
      |wordComp i.1 (Vc ν c s) i.2 z| ≤ C * (width ν s) ^ (-(3 + (j : ℝ)) / 2) := by
    intro i hi
    rw [Finset.mem_product] at hi
    have hlen : i.1.length = j := by
      unfold wordsOfLength at hi
      rcases Finset.mem_image.1 hi.1 with ⟨u, _, hiu⟩
      rw [← hiu]
      simp
    have hz := (hVc ν c s hc ha1 hac).1 i.1 hlen i.2 z
    rw [pow_zero, one_mul] at hz
    exact hz
  have hcard : ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) ≤ 2 * 2 ^ j := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hW : (wordsOfLength j).card ≤ 2 ^ j := by
      unfold wordsOfLength
      calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
        _ = 2 ^ j := by simp
    have hW' : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by exact_mod_cast hW
    push_cast; linarith
  have hrpow : (width ν s) ^ (-(3 + (j : ℝ)) / 2) ≤ (width ν s ^ 2)⁻¹ := by
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hexp : -(3 + (j : ℝ)) / 2 ≤ (-2 : ℝ) := by linarith
    calc (width ν s) ^ (-(3 + (j : ℝ)) / 2)
        ≤ (width ν s) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hexp
      _ = (width ν s ^ 2)⁻¹ := by rw [Real.rpow_neg ha0.le, Real.rpow_two]
  calc ‖iteratedFDeriv ℝ j (Vc ν c s) z‖
      ≤ ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
          |wordComp i.1 (Vc ν c s) i.2 z| := jl2_pointwise j (Vc ν c s) hV_sm z
    _ ≤ ∑ _i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
          C * (width ν s) ^ (-(3 + (j : ℝ)) / 2) := Finset.sum_le_sum hword
    _ = ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) *
          (C * (width ν s) ^ (-(3 + (j : ℝ)) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * 2 ^ j) * (C * (width ν s) ^ (-(3 + (j : ℝ)) / 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K * (width ν s) ^ (-(3 + (j : ℝ)) / 2) := by ring
    _ ≤ K * (width ν s ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hrpow hK_nn
    _ ≤ (1 + K) * (width ν s ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- A continuous real function bounded a.e. by `B` is bounded everywhere by `B`. -/
private theorem pw_of_ae_le {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ≥0∞}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ₑ ≤ B) (x : ℝ) : ‖f x‖ₑ ≤ B := by
  by_contra hx
  simp only [not_le] at hx
  have hU : IsOpen {y : ℝ | B < ‖f y‖ₑ} := isOpen_lt continuous_const hf.enorm
  have hpos : 0 < (volume : Measure ℝ) {y : ℝ | B < ‖f y‖ₑ} := hU.measure_pos volume ⟨x, hx⟩
  have hae : (volume : Measure ℝ) {y : ℝ | ¬ (‖f y‖ₑ ≤ B)} = 0 := ae_iff.1 h
  have hset : {y : ℝ | ¬ (‖f y‖ₑ ≤ B)} = {y : ℝ | B < ‖f y‖ₑ} := by
    ext y
    simp [not_le]
  rw [hset] at hae
  exact absurd hae (ne_of_gt hpos)

/-- An `eLpNorm ⊤` bound by `ofReal B` gives the pointwise real bound, for continuous `f`. -/
private theorem norm_le_of_eLpNorm_top {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f ⊤ (volume : Measure ℝ) ≤ ENNReal.ofReal B) (x : ℝ) : ‖f x‖ ≤ B := by
  have h1 : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ₑ ≤ ENNReal.ofReal B := by
    have h0 := enorm_ae_le_eLpNormEssSup f (volume : Measure ℝ)
    rw [← eLpNorm_exponent_top] at h0
    filter_upwards [h0] with y hy
    exact hy.trans h
  have h2 := pw_of_ae_le hf h1 x
  rw [Real.enorm_eq_ofReal_abs] at h2
  rw [Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h2

/-- For a smooth vertical profile `b : ℝ → ℝ` and a vector field `M : Plane → Vec` with
`M y 0 = b y.2` and `M y 1 = 0`, `M` is smooth and `B0277.supNormD j M ≤ ENNReal.ofReal B`
whenever `eLpNorm (iteratedDeriv j b) ⊤ volume ≤ ENNReal.ofReal B` (`0 ≤ B`). -/
theorem supNormD_vert_le_of_eLpNorm_top {M : Plane → Vec} {b : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hM0 : ∀ y : Plane, M y 0 = b y.2) (hM1 : ∀ y : Plane, M y 1 = 0)
    (j : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (htop : eLpNorm (iteratedDeriv j b) ⊤ volume ≤ ENNReal.ofReal B) :
    ContDiff ℝ ∞ M ∧ B0277.supNormD j M ≤ ENNReal.ofReal B := by
  let e₀ : Vec := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  let L₁ : ℝ →L[ℝ] Vec := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e₀
  let L₂ : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hM_eq : M = L₁ ∘ (b ∘ L₂) := by
    funext y
    ext i
    fin_cases i
    · simpa [L₁, L₂, e₀] using hM0 y
    · simpa [L₁, L₂, e₀] using hM1 y
  have hbL₂_sm : ContDiff ℝ ∞ (b ∘ L₂) := hb.comp L₂.contDiff
  have hM_sm : ContDiff ℝ ∞ M := by
    rw [hM_eq]
    exact L₁.contDiff.comp hbL₂_sm
  refine ⟨hM_sm, B0277.supNormD_le_ofReal fun y => ?_⟩
  have he₀ : ‖e₀‖ = 1 := by
    dsimp [e₀]
    rw [PiLp.norm_single, norm_one]
  have hL₁_norm : ‖L₁‖ ≤ 1 := by
    refine L₁.opNorm_le_bound zero_le_one fun r => ?_
    simp [L₁, norm_smul, he₀]
  have hL₂_norm : ‖L₂‖ ≤ 1 := by
    refine L₂.opNorm_le_bound zero_le_one fun z => ?_
    rw [one_mul]
    exact norm_snd_le z
  have hprod_L₂ : ∏ _i : Fin j, ‖L₂‖ ≤ 1 := by
    calc ∏ _i : Fin j, ‖L₂‖
        ≤ ∏ _i : Fin j, (1 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hL₂_norm)
      _ = 1 := Finset.prod_const_one
  have hcomp1 : ‖iteratedFDeriv ℝ j M y‖ ≤ ‖iteratedFDeriv ℝ j (b ∘ L₂) y‖ := by
    rw [hM_eq]
    have h1 := L₁.norm_iteratedFDeriv_comp_left (f := b ∘ L₂) (x := y)
      (N := (∞ : WithTop ℕ∞)) (n := j) hbL₂_sm.contDiffAt (mod_cast le_top)
    calc ‖iteratedFDeriv ℝ j (L₁ ∘ (b ∘ L₂)) y‖
        ≤ ‖L₁‖ * ‖iteratedFDeriv ℝ j (b ∘ L₂) y‖ := h1
      _ ≤ 1 * ‖iteratedFDeriv ℝ j (b ∘ L₂) y‖ :=
          mul_le_mul_of_nonneg_right hL₁_norm (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ j (b ∘ L₂) y‖ := one_mul _
  have hcomp2 : ‖iteratedFDeriv ℝ j (b ∘ L₂) y‖ ≤ ‖iteratedDeriv j b y.2‖ := by
    rw [L₂.iteratedFDeriv_comp_right hb y (mod_cast le_top)]
    calc ‖(iteratedFDeriv ℝ j b (L₂ y)).compContinuousLinearMap fun _ => L₂‖
        ≤ ‖iteratedFDeriv ℝ j b (L₂ y)‖ * ∏ _i : Fin j, ‖L₂‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ j b (L₂ y)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod_L₂ (norm_nonneg _)
      _ = ‖iteratedDeriv j b y.2‖ := by
          rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          rfl
  have hcont_deriv : Continuous (iteratedDeriv j b) :=
    (hb.of_le (by simp)).continuous_iteratedDeriv' j
  have hpt_b : ‖iteratedDeriv j b y.2‖ ≤ B :=
    norm_le_of_eLpNorm_top hcont_deriv hB htop y.2
  exact (hcomp1.trans hcomp2).trans hpt_b

/-! ### 2. Elementary exponential and power inequalities for `j ≥ 1` -/

/-- For `x ≥ 0`, `x * exp(-x) ≤ 1`. -/
private theorem mul_exp_neg_le_one {x : ℝ} (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 1 := by
  have h1 : x ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  calc x * Real.exp (-x)
      ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- For `j ≥ 1`, `1 ≤ ν * c²`, `1 ≤ a`, and `0 < b`,
`ν⁻¹ * a ^ (-((5 + j) / 2)) * exp(-(b * c² / a)) ≤ b⁻¹ * (a²)⁻¹`. -/
private theorem preOverlap_err_sup_factor_le {j : ℕ} (hj : 1 ≤ j) {ν c a b : ℝ}
    (hν : 0 < ν) (hc : 0 < c) (ha1 : 1 ≤ a) (hb : 0 < b) (hνc2 : 1 ≤ ν * c ^ 2) :
    ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * Real.exp (-(b * c ^ 2 / a)) ≤ b⁻¹ * (a ^ 2)⁻¹ := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha1
  have hν_inv_le : ν⁻¹ ≤ c ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hν]
    linarith
  have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hexp_le : -((5 + (j : ℝ)) / 2) ≤ (-3 : ℝ) := by linarith
  have hrpow : a ^ (-((5 + (j : ℝ)) / 2)) ≤ a⁻¹ * (a ^ 2)⁻¹ := by
    calc a ^ (-((5 + (j : ℝ)) / 2))
        ≤ a ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hexp_le
      _ = a⁻¹ * (a ^ 2)⁻¹ := by
          have h3 : (-3 : ℝ) = -((1 + 2 : ℕ) : ℝ) := by norm_num
          rw [h3, Real.rpow_neg ha0.le, Real.rpow_natCast, pow_add, pow_one, mul_inv]
  have hx_nn : 0 ≤ b * c ^ 2 / a := by positivity
  have h_exp := mul_exp_neg_le_one hx_nn
  have h_ca : c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a)) ≤ b⁻¹ := by
    calc c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a))
        = b⁻¹ * ((b * c ^ 2 / a) * Real.exp (-(b * c ^ 2 / a))) := by
          have hb_ne : b ≠ 0 := hb.ne'
          field_simp
      _ ≤ b⁻¹ * 1 := mul_le_mul_of_nonneg_left h_exp (inv_nonneg.2 hb.le)
      _ = b⁻¹ := mul_one _
  calc ν⁻¹ * a ^ (-((5 + (j : ℝ)) / 2)) * Real.exp (-(b * c ^ 2 / a))
      ≤ c ^ 2 * (a⁻¹ * (a ^ 2)⁻¹) * Real.exp (-(b * c ^ 2 / a)) := by
        gcongr
    _ = (c ^ 2 * a⁻¹ * Real.exp (-(b * c ^ 2 / a))) * (a ^ 2)⁻¹ := by ring
    _ ≤ b⁻¹ * (a ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h_ca (by positivity)

/-- For `T ≥ 0` and `lam > 0`, `exp(-(lam * T)) ≤ (1 + 2 * lam⁻¹)² * (1 + T) ^ (-3/2)`. -/
private theorem exp_neg_le_rpow_neg_three_halves {lam T : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) :
    Real.exp (-(lam * T)) ≤ (1 + 2 * lam⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ)) := by
  have h1T_pos : 0 < 1 + T := by linarith
  have h1T_ge1 : 1 ≤ 1 + T := by linarith
  let μ : ℝ := lam / 2
  have hμ_pos : 0 < μ := half_pos hlam
  have hexp_le1 : Real.exp (-(μ * T)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have hT_exp : T * Real.exp (-(μ * T)) ≤ 2 * lam⁻¹ := by
    have hx := mul_exp_neg_le_one (mul_nonneg hμ_pos.le hT)
    calc T * Real.exp (-(μ * T))
        = μ⁻¹ * ((μ * T) * Real.exp (-(μ * T))) := by
          have hμ_ne : μ ≠ 0 := hμ_pos.ne'
          field_simp
      _ ≤ μ⁻¹ * 1 := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hμ_pos.le)
      _ = 2 * lam⁻¹ := by dsimp [μ]; ring
  have hprod1 : (1 + T) * Real.exp (-(μ * T)) ≤ 1 + 2 * lam⁻¹ := by
    calc (1 + T) * Real.exp (-(μ * T))
        = Real.exp (-(μ * T)) + T * Real.exp (-(μ * T)) := by ring
      _ ≤ 1 + 2 * lam⁻¹ := add_le_add hexp_le1 hT_exp
  have hprod2 : (1 + T) ^ 2 * Real.exp (-(lam * T)) ≤ (1 + 2 * lam⁻¹) ^ 2 := by
    have hsq : (1 + T) ^ 2 * Real.exp (-(lam * T)) =
        ((1 + T) * Real.exp (-(μ * T))) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      dsimp [μ]; ring
    rw [hsq]
    exact pow_le_pow_left₀ (by positivity) hprod1 2
  have hinv_le : ((1 + T) ^ 2)⁻¹ ≤ (1 + T) ^ (-(3 / 2 : ℝ)) := by
    have h2 : ((1 + T) ^ 2)⁻¹ = (1 + T) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg h1T_pos.le, Real.rpow_two]
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le h1T_ge1 (by norm_num)
  calc Real.exp (-(lam * T))
      = ((1 + T) ^ 2 * Real.exp (-(lam * T))) * ((1 + T) ^ 2)⁻¹ := by
        rw [mul_comm ((1 + T) ^ 2), mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero 2 h1T_pos.ne'), mul_one]
    _ ≤ (1 + 2 * lam⁻¹) ^ 2 * ((1 + T) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hprod2 (by positivity)
    _ ≤ (1 + 2 * lam⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv_le (by positivity)

/-! ### 3. Single-order `j` and finite-sum pointwise `supNormD` bounds -/

/-- Pointwise in `s ≥ 0` bound on `B0277.supNormD j (tr.v s)` for a single order `j ≥ 1`,
in both the pre-overlap (`s ≤ s_c`) and post-overlap (`s_c ≤ s`) regimes. -/
theorem supNormD_pointwise_bound_j (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj ν₀ : ℝ, 0 < Cj ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
          let c := trainPeriod ρ ν
          let s_c := B0146.overlapAge ν c
          (s ≤ s_c →
            B0277.supNormD j (tr.v s) ≤ ENNReal.ofReal (Cj * (width ν s ^ 2)⁻¹)) ∧
          (s_c ≤ s →
            B0277.supNormD j (tr.v s) ≤
              ENNReal.ofReal (Cj * (c ^ 4)⁻¹ *
                (1 + ν * (s - s_c) / c ^ 2) ^ (-(3 / 2 : ℝ)))) := by
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ j
  obtain ⟨CV, hCV, hVc⟩ := preOverlap_Vc_supNormD_bound j hj
  obtain ⟨C_ov, lam, ν_ov, hC_ov, hlam, hν_ov, hov⟩ := hOv ρ hρ j
  obtain ⟨νp, hνp, _, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  let C_pre : ℝ := Ce * be⁻¹ + CV
  let C_post : ℝ := C_ov * (1 + (1 + 2 * lam⁻¹) ^ 2)
  have hC_pre : 0 < C_pre := by positivity
  have hC_post : 0 < C_post := by positivity
  refine ⟨max C_pre C_post, min νe (min ν_ov νp), lt_max_of_lt_left hC_pre,
    lt_min hνe (lt_min hν_ov hνp), ?_⟩
  intro ν hν hν_le tr htr s hs
  have hν_e : ν ≤ νe := hν_le.trans (min_le_left _ _)
  have hν_ov_le : ν ≤ ν_ov := hν_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_p : ν ≤ νp := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hc1, hνc2⟩ := hp ν hν hν_p
  let c := trainPeriod ρ ν
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hνc2_ge1 : 1 ≤ ν * c ^ 2 := by linarith
  let s_c := B0146.overlapAge ν c
  have hv_sm : ContDiff ℝ ∞ (tr.v s) := by
    have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
      (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
    exact contDiffOn_univ.1 h
  refine ⟨?_, ?_⟩
  · -- Pre-overlap (`s ≤ s_c`)
    intro hs_le
    have hw_ge1 : 1 ≤ width ν s := by
      unfold width
      nlinarith
    have hw_le_c2 : width ν s ≤ c ^ 2 := by
      have hw_sc : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
      have hmono : width ν s ≤ width ν s_c := by
        unfold width
        nlinarith
      exact hmono.trans_eq hw_sc
    have ha0 : 0 < width ν s := zero_lt_one.trans_le hw_ge1
    obtain ⟨_, hSup_err⟩ := hcomp ν hν hν_e tr htr s hs hw_le_c2
    have hSup_Vc := hVc ν c s hc0 hw_ge1 hw_le_c2
    have hV_sm : ContDiff ℝ ∞ (Vc ν c s) :=
      UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 ha0
    let err : Plane → Vec := fun z => tr.v s z - Vc ν c s z
    have herr_sm : ContDiff ℝ ∞ err := hv_sm.sub hV_sm
    have hv_decomp : tr.v s = fun z => err z + Vc ν c s z := by
      funext z
      simp [err, sub_add_cancel]
    have htri : B0277.supNormD j (tr.v s) ≤ B0277.supNormD j err + B0277.supNormD j (Vc ν c s) := by
      rw [hv_decomp]
      exact supNormD_add_le j herr_sm hV_sm
    have herr_le : B0277.supNormD j err ≤ ENNReal.ofReal (Ce * be⁻¹ * (width ν s ^ 2)⁻¹) := by
      refine hSup_err.trans (ENNReal.ofReal_le_ofReal ?_)
      have hfac := preOverlap_err_sup_factor_le hj hν hc0 hw_ge1 hbe hνc2_ge1
      calc Ce * ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) * Real.exp (-(be * c ^ 2 / width ν s))
          = Ce * (ν⁻¹ * width ν s ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s))) := by ring
        _ ≤ Ce * (be⁻¹ * (width ν s ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hfac hCe.le
        _ = Ce * be⁻¹ * (width ν s ^ 2)⁻¹ := by ring
    calc B0277.supNormD j (tr.v s)
        ≤ ENNReal.ofReal (Ce * be⁻¹ * (width ν s ^ 2)⁻¹) +
            ENNReal.ofReal (CV * (width ν s ^ 2)⁻¹) :=
          htri.trans (add_le_add herr_le hSup_Vc)
      _ = ENNReal.ofReal (C_pre * (width ν s ^ 2)⁻¹) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [C_pre]; ring
      _ ≤ ENNReal.ofReal (max C_pre C_post * (width ν s ^ 2)⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- Post-overlap (`s_c ≤ s`)
    intro hs_ge
    let T : ℝ := ν * (s - s_c) / c ^ 2
    have hT_nn : 0 ≤ T := by
      dsimp [T]
      have : 0 ≤ s - s_c := sub_nonneg.2 hs_ge
      positivity
    have hs_eq : s_c + c ^ 2 * T / ν = s := by
      dsimp [T]
      have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
      have hν_ne : ν ≠ 0 := hν.ne'
      field_simp
      ring
    let U := overlapField ν c tr.v T
    have hU_scale : U = scaleField c (tr.v s) := by
      funext y
      dsimp [U, overlapField, scaleField]
      rw [show B0146.overlapAge ν c + c ^ 2 * T / ν = s from hs_eq]
    have hv_scale : tr.v s = scaleField c⁻¹ U := by
      funext z
      rw [hU_scale]
      dsimp [scaleField]
      have hc_ne : c ≠ 0 := hc0.ne'
      have hcz : c • (c⁻¹ • z) = z := smul_inv_smul₀ hc_ne z
      rw [hcz, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hc_ne), one_smul]
    have hU_sm : ContDiff ℝ ∞ U := by
      rw [hU_scale]
      exact (hv_sm.comp (contDiff_id.const_smul c)).const_smul (c ^ 3)
    obtain ⟨hU1, hb_sm, _, hb_top, _, hW_sup⟩ := hov ν hν hν_ov_le tr htr T hT_nn
    let b : ℝ → ℝ := fun Y => hmean 1 U Y 0
    let M : Plane → Vec := fun y => hmean 1 U y.2
    have hM0 : ∀ y : Plane, M y 0 = b y.2 := fun _ => rfl
    have hM1 : ∀ y : Plane, M y 1 = 0 := fun y => hU1 y.2
    have h1T_pos : 0 < 1 + T := by linarith
    have h1T_ge1 : 1 ≤ 1 + T := by linarith
    have hb_B_nn : 0 ≤ C_ov * (1 + T) ^ (-1 - (j : ℝ) / 2) := by positivity
    obtain ⟨hM_sm, hM_sup⟩ :=
      supNormD_vert_le_of_eLpNorm_top hb_sm hM0 hM1 j hb_B_nn hb_top
    have hW_sm : ContDiff ℝ ∞ (hfluct 1 U) := hU_sm.sub hM_sm
    have hU_decomp : U = fun y => M y + hfluct 1 U y := by
      funext y
      simp [M, hfluct]
    have hU_tri : B0277.supNormD j U ≤ B0277.supNormD j M + B0277.supNormD j (hfluct 1 U) := by
      conv_lhs => rw [hU_decomp]
      exact supNormD_add_le j hM_sm hW_sm
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hexp_j : -1 - (j : ℝ) / 2 ≤ -(3 / 2 : ℝ) := by linarith
    have hM_rpow : B0277.supNormD j M ≤
        ENNReal.ofReal (C_ov * (1 + T) ^ (-(3 / 2 : ℝ))) := by
      refine hM_sup.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h1T_ge1 hexp_j) hC_ov.le
    have hW_rpow : B0277.supNormD j (hfluct 1 U) ≤
        ENNReal.ofReal (C_ov * (1 + 2 * lam⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ))) := by
      refine hW_sup.trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp := exp_neg_le_rpow_neg_three_halves hlam hT_nn
      calc C_ov * Real.exp (-(lam * T))
          ≤ C_ov * ((1 + 2 * lam⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hexp hC_ov.le
        _ = C_ov * (1 + 2 * lam⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ)) := by ring
    have hU_sup : B0277.supNormD j U ≤
        ENNReal.ofReal (C_post * (1 + T) ^ (-(3 / 2 : ℝ))) := by
      calc B0277.supNormD j U
          ≤ ENNReal.ofReal (C_ov * (1 + T) ^ (-(3 / 2 : ℝ))) +
              ENNReal.ofReal (C_ov * (1 + 2 * lam⁻¹) ^ 2 * (1 + T) ^ (-(3 / 2 : ℝ))) :=
            hU_tri.trans (add_le_add hM_rpow hW_rpow)
        _ = ENNReal.ofReal (C_post * (1 + T) ^ (-(3 / 2 : ℝ))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            dsimp [C_post]; ring
    have hc_inv_le : (c⁻¹) ^ 3 * (c⁻¹) ^ j ≤ (c ^ 4)⁻¹ := by
      have hcinv1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      have hcinv_nn : 0 ≤ c⁻¹ := inv_nonneg.2 hc0.le
      have hj_pow : (c⁻¹) ^ j ≤ (c⁻¹) ^ 1 := pow_le_pow_of_le_one hcinv_nn hcinv1 hj
      calc (c⁻¹) ^ 3 * (c⁻¹) ^ j
          ≤ (c⁻¹) ^ 3 * (c⁻¹) ^ 1 := mul_le_mul_of_nonneg_left hj_pow (by positivity)
        _ = (c ^ 4)⁻¹ := by rw [← pow_add, inv_pow]
    calc B0277.supNormD j (tr.v s)
        = B0277.supNormD j (scaleField c⁻¹ U) := by rw [← hv_scale]
      _ ≤ ENNReal.ofReal ((c⁻¹) ^ 3 * (c⁻¹) ^ j) * B0277.supNormD j U :=
          supNormD_scaleField_le (inv_nonneg.2 hc0.le) j U
      _ ≤ ENNReal.ofReal ((c ^ 4)⁻¹) *
            ENNReal.ofReal (C_post * (1 + T) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = ENNReal.ofReal ((c ^ 4)⁻¹ * (C_post * (1 + T) ^ (-(3 / 2 : ℝ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (max C_pre C_post * (c ^ 4)⁻¹ *
            (1 + T) ^ (-(3 / 2 : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hC_le : C_post ≤ max C_pre C_post := le_max_right _ _
          calc (c ^ 4)⁻¹ * (C_post * (1 + T) ^ (-(3 / 2 : ℝ)))
              = C_post * ((c ^ 4)⁻¹ * (1 + T) ^ (-(3 / 2 : ℝ))) := by ring
            _ ≤ max C_pre C_post * ((c ^ 4)⁻¹ * (1 + T) ^ (-(3 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_right hC_le (by positivity)
            _ = max C_pre C_post * (c ^ 4)⁻¹ * (1 + T) ^ (-(3 / 2 : ℝ)) := by ring

/-- Pointwise bound on the finite sum `∑ j ∈ Icc 1 (k + 1), B0277.supNormD j (tr.v s)`. -/
theorem supNormD_sum_bound (hOv : TrainOverlap) (ρ : ℝ) (hρ : 1 / 2 < ρ) (k : ℕ) :
    ∃ K ν₀ : ℝ, 0 < K ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 ≤ s →
          let c := trainPeriod ρ ν
          let s_c := B0146.overlapAge ν c
          (s ≤ s_c →
            ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s) ≤
              ENNReal.ofReal (K * (width ν s ^ 2)⁻¹)) ∧
          (s_c ≤ s →
            ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s) ≤
              ENNReal.ofReal (K * (c ^ 4)⁻¹ *
                (1 + ν * (s - s_c) / c ^ 2) ^ (-(3 / 2 : ℝ)))) := by
  induction k with
  | zero =>
    obtain ⟨C₁, ν₁, hC₁, hν₁, h1⟩ := supNormD_pointwise_bound_j hOv ρ hρ 1 le_rfl
    refine ⟨C₁, ν₁, hC₁, hν₁, fun ν hν hν_le tr htr s hs => ?_⟩
    simp only [zero_add, Finset.Icc_self, Finset.sum_singleton]
    exact h1 ν hν hν_le tr htr s hs
  | succ k ih =>
    obtain ⟨Kk, νk, hKk, hνk, hk⟩ := ih
    obtain ⟨C₁, ν₁, hC₁, hν₁, h1⟩ :=
      supNormD_pointwise_bound_j hOv ρ hρ (k + 2) (by omega)
    refine ⟨Kk + C₁, min νk ν₁, add_pos hKk hC₁, lt_min hνk hν₁,
      fun ν hν hν_le tr htr s hs => ?_⟩
    have hν_k : ν ≤ νk := hν_le.trans (min_le_left _ _)
    have hν_1 : ν ≤ ν₁ := hν_le.trans (min_le_right _ _)
    obtain ⟨hpre_k, hpost_k⟩ := hk ν hν hν_k tr htr s hs
    obtain ⟨hpre_1, hpost_1⟩ := h1 ν hν hν_1 tr htr s hs
    have hIcc : Finset.Icc 1 (k + 1 + 1) = insert (k + 2) (Finset.Icc 1 (k + 1)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : k + 2 ∉ Finset.Icc 1 (k + 1) := by
      simp only [Finset.mem_Icc]
      omega
    let c := trainPeriod ρ ν
    let s_c := B0146.overlapAge ν c
    refine ⟨fun hs_le => ?_, fun hs_ge => ?_⟩
    · rw [hIcc, Finset.sum_insert hnotmem]
      calc B0277.supNormD (k + 2) (tr.v s) +
              ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)
          ≤ ENNReal.ofReal (C₁ * (width ν s ^ 2)⁻¹) +
              ENNReal.ofReal (Kk * (width ν s ^ 2)⁻¹) :=
            add_le_add (hpre_1 hs_le) (hpre_k hs_le)
        _ = ENNReal.ofReal ((Kk + C₁) * (width ν s ^ 2)⁻¹) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
    · rw [hIcc, Finset.sum_insert hnotmem]
      have hT_nn : 0 ≤ 1 + ν * (s - s_c) / c ^ 2 := by
        have : 0 ≤ s - s_c := sub_nonneg.2 hs_ge
        positivity
      calc B0277.supNormD (k + 2) (tr.v s) +
              ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)
          ≤ ENNReal.ofReal (C₁ * (c ^ 4)⁻¹ *
                (1 + ν * (s - s_c) / c ^ 2) ^ (-(3 / 2 : ℝ))) +
              ENNReal.ofReal (Kk * (c ^ 4)⁻¹ *
                (1 + ν * (s - s_c) / c ^ 2) ^ (-(3 / 2 : ℝ))) :=
            add_le_add (hpost_1 hs_ge) (hpost_k hs_ge)
        _ = ENNReal.ofReal ((Kk + C₁) * (c ^ 4)⁻¹ *
              (1 + ν * (s - s_c) / c ^ 2) ^ (-(3 / 2 : ℝ))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring

/-! ### 4. Pre-overlap and post-overlap 1D integrals and `trainStrainIntegral_proof` -/

/-- Pre-overlap integral of `K * (width ν s ^ 2)⁻¹` over `s ∈ Ioc (σ₀ / ν) s_c`:
bounded above by `ENNReal.ofReal (K / (ν * (1 + σ₀)))`. -/
theorem lintegral_preOverlap_inv_width_sq {K ν c σ₀ : ℝ} (hK : 0 ≤ K) (hν : 0 < ν)
    (hσ₀ : 0 ≤ σ₀) (hσc : 1 + σ₀ ≤ c ^ 2) :
    ∫⁻ s in Ioc (σ₀ / ν) (B0146.overlapAge ν c), ENNReal.ofReal (K * (width ν s ^ 2)⁻¹) ≤
      ENNReal.ofReal (K / (ν * (1 + σ₀))) := by
  set s₀ := σ₀ / ν
  set s_c := B0146.overlapAge ν c
  have hs₀_nn : 0 ≤ s₀ := div_nonneg hσ₀ hν.le
  have hs₀_le_sc : s₀ ≤ s_c := by
    dsimp [s₀, s_c, B0146.overlapAge]
    exact div_le_div_of_nonneg_right (by linarith) hν.le
  set f : ℝ → ℝ := fun s => K * (width ν s ^ 2)⁻¹
  set F : ℝ → ℝ := fun s => -(K * ν⁻¹ * (1 + ν * s)⁻¹)
  have hf_pos : ∀ s ∈ uIcc s₀ s_c, 0 < 1 + ν * s := by
    intro s hs
    rw [uIcc_of_le hs₀_le_sc] at hs
    have hs_nn : 0 ≤ s := hs₀_nn.trans hs.1
    nlinarith
  have hf_cont : ContinuousOn f (uIcc s₀ s_c) := by
    refine continuousOn_const.mul (ContinuousOn.inv₀ ?_ (fun s hs => pow_ne_zero 2 (hf_pos s hs).ne'))
    exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2
  have hderiv : ∀ s ∈ uIcc s₀ s_c, HasDerivAt F (f s) s := by
    intro s hs
    have hw_pos : 0 < 1 + ν * s := hf_pos s hs
    have hd1 : HasDerivAt (fun r : ℝ => 1 + ν * r) ν s := by
      simpa using ((hasDerivAt_id s).const_mul ν).const_add 1
    have hd2 : HasDerivAt (fun r : ℝ => (1 + ν * r)⁻¹) (-ν / (1 + ν * s) ^ 2) s :=
      hd1.inv hw_pos.ne'
    have hd3 : HasDerivAt F (-(K * ν⁻¹ * (-ν / (1 + ν * s) ^ 2))) s :=
      (hd2.const_mul (K * ν⁻¹)).neg
    have heq : -(K * ν⁻¹ * (-ν / (1 + ν * s) ^ 2)) = f s := by
      dsimp [f, width]
      have hν0 : ν ≠ 0 := hν.ne'
      field_simp
    rwa [heq] at hd3
  have hint_Ioc : IntegrableOn f (Ioc s₀ s_c) volume := by
    rw [uIcc_of_le hs₀_le_sc] at hf_cont
    exact hf_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hf_nn : 0 ≤ᵐ[volume.restrict (Ioc s₀ s_c)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s _
    dsimp [f]
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint_Ioc hf_nn,
    ← intervalIntegral.integral_of_le hs₀_le_sc,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hf_cont.intervalIntegrable)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : 1 + ν * s_c = c ^ 2 := width_overlapAge hν.ne'
  have h2 : 1 + ν * s₀ = 1 + σ₀ := by
    dsimp [s₀]
    have hν0 : ν ≠ 0 := hν.ne'
    field_simp
  have hc2_pos : 0 < c ^ 2 := by linarith
  have hterm_nn : 0 ≤ K * ν⁻¹ * (c ^ 2)⁻¹ := by positivity
  dsimp [F]
  rw [h1, h2]
  have heq : -(K * ν⁻¹ * (c ^ 2)⁻¹) - -(K * ν⁻¹ * (1 + σ₀)⁻¹) =
      K / (ν * (1 + σ₀)) - K * ν⁻¹ * (c ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  linarith

/-- Post-overlap integral of `K * (c ^ 4)⁻¹ * (1 + ν * (s - s_c) / c²) ^ (-3/2)` over `s ∈ Ioi s_c`:
equals `ENNReal.ofReal ((2 * K) / (ν * c²))`. -/
theorem lintegral_postOverlap_rpow {K ν c : ℝ} (hK : 0 ≤ K) (hν : 0 < ν) (hc : 0 < c) :
    ∫⁻ s in Ioi (B0146.overlapAge ν c),
        ENNReal.ofReal (K * (c ^ 4)⁻¹ *
          (1 + ν * (s - B0146.overlapAge ν c) / c ^ 2) ^ (-(3 / 2 : ℝ))) =
      ENNReal.ofReal ((2 * K) / (ν * c ^ 2)) := by
  set s_c := B0146.overlapAge ν c
  let u : ℝ → ℝ := fun s => 1 + ν * (s - s_c) / c ^ 2
  let f : ℝ → ℝ := fun s => K * (c ^ 4)⁻¹ * u s ^ (-(3 / 2 : ℝ))
  let F : ℝ → ℝ := fun s => -(2 * K * (ν * c ^ 2)⁻¹) * u s ^ (-(1 / 2 : ℝ))
  have hu_pos : ∀ s ∈ Ici s_c, 0 < u s := by
    intro s hs
    dsimp [u]
    have : 0 ≤ s - s_c := sub_nonneg.2 hs
    positivity
  have hderiv : ∀ s ∈ Ici s_c, HasDerivAt F (f s) s := by
    intro s hs
    have hup : 0 < u s := hu_pos s hs
    have hdu : HasDerivAt u (ν / c ^ 2) s := by
      have h1 : HasDerivAt (fun r : ℝ => (r - s_c) * (ν / c ^ 2)) (1 * (ν / c ^ 2)) s :=
        ((hasDerivAt_id s).sub_const s_c).mul_const (ν / c ^ 2)
      have h2 := h1.const_add 1
      have hfun : (fun r : ℝ => 1 + (r - s_c) * (ν / c ^ 2)) = u := by
        funext r; dsimp [u]; ring
      rw [hfun, one_mul] at h2
      exact h2
    have hdrpow : HasDerivAt (fun r : ℝ => u r ^ (-(1 / 2 : ℝ)))
        (ν / c ^ 2 * -(1 / 2 : ℝ) * u s ^ (-(1 / 2 : ℝ) - 1)) s :=
      hdu.rpow_const (Or.inl hup.ne')
    have hdF := hdrpow.const_mul (-(2 * K * (ν * c ^ 2)⁻¹))
    have heq : -(2 * K * (ν * c ^ 2)⁻¹) *
        (ν / c ^ 2 * -(1 / 2 : ℝ) * u s ^ (-(1 / 2 : ℝ) - 1)) = f s := by
      dsimp [f]
      rw [show (-(1 / 2 : ℝ) - 1 : ℝ) = -(3 / 2 : ℝ) by norm_num]
      have hν0 : ν ≠ 0 := hν.ne'
      have hc0 : c ≠ 0 := hc.ne'
      field_simp
    rwa [heq] at hdF
  have hf_pos : ∀ s ∈ Ioi s_c, 0 ≤ f s := by
    intro s hs
    dsimp [f]
    have hup : 0 < u s := hu_pos s (mem_Ici.2 hs.out.le)
    positivity
  have hF_tendsto : Tendsto F atTop (𝓝 0) := by
    have hu_atTop : Tendsto u atTop atTop := by
      have h1 : Tendsto (fun s : ℝ => s - s_c) atTop atTop :=
        tendsto_atTop_add_const_right atTop (-s_c) tendsto_id
      have h2 : Tendsto (fun s : ℝ => (ν / c ^ 2) * (s - s_c)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity) h1
      have h3 : Tendsto (fun s : ℝ => 1 + (ν / c ^ 2) * (s - s_c)) atTop atTop :=
        tendsto_atTop_add_const_left atTop 1 h2
      refine h3.congr fun s => ?_
      dsimp [u]; ring
    have hrpow_0 : Tendsto (fun s : ℝ => u s ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hu_atTop
    have h0 : -(2 * K * (ν * c ^ 2)⁻¹) * (0 : ℝ) = 0 := mul_zero _
    rw [← h0]
    exact hrpow_0.const_mul (-(2 * K * (ν * c ^ 2)⁻¹))
  have hint : IntegrableOn f (Ioi s_c) volume :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hf_pos hF_tendsto
  have hf_nn : 0 ≤ᵐ[volume.restrict (Ioi s_c)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hf_pos s hs
  rw [← ofReal_integral_eq_lintegral_ofReal hint hf_nn,
    integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hf_pos hF_tendsto]
  congr 1
  have hu_sc : u s_c = 1 := by dsimp [u]; ring
  dsimp [F]
  rw [hu_sc, Real.one_rpow]
  ring

/-- **`PartI:T18` (`trainStrainIntegral_proof`)** (source lines 318-319, 425-436):
proves `TrainStrainIntegral` from `trainComparison_proof` (`PartI:T10`) and `hOv : TrainOverlap`. -/
theorem trainStrainIntegral_proof (hOv : TrainOverlap) : TrainStrainIntegral := by
  intro ρ hρ k
  obtain ⟨K, ν₀, hK, hν₀, hsum⟩ := supNormD_sum_bound hOv ρ hρ k
  refine ⟨2 * K, min ν₀ (1 / 2), by positivity, lt_min hν₀ (by norm_num), ?_⟩
  intro ν hν hν_le tr htr σ₀ hσ₀ hσc
  have hν_0 : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc1 : 1 < c := by
    unfold c trainPeriod
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
  have hc0 : 0 < c := zero_lt_one.trans hc1
  set s₀ := σ₀ / ν
  set s_c := B0146.overlapAge ν c
  have hs₀_nn : 0 ≤ s₀ := div_nonneg hσ₀ hν.le
  have hs₀_le_sc : s₀ ≤ s_c := by
    dsimp [s₀, s_c, B0146.overlapAge]
    exact div_le_div_of_nonneg_right (by linarith) hν.le
  have hsc_nn : 0 ≤ s_c := hs₀_nn.trans hs₀_le_sc
  unfold B0278.TrainStrainEstimate
  have hunion : Ioi s₀ = Ioc s₀ s_c ∪ Ioi s_c :=
    (Ioc_union_Ioi_eq_Ioi hs₀_le_sc).symm
  have hsplit : ∫⁻ s in Ioi s₀, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s) ≤
      (∫⁻ s in Ioc s₀ s_c, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)) +
        (∫⁻ s in Ioi s_c, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)) := by
    conv_lhs => rw [hunion]
    exact lintegral_union_le _ _ _
  have hpre : ∫⁻ s in Ioc s₀ s_c, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s) ≤
      ENNReal.ofReal (K / (ν * (1 + σ₀))) := by
    refine (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_).trans
      (lintegral_preOverlap_inv_width_sq hK.le hν hσ₀ hσc)
    have hs_nn : 0 ≤ s := hs₀_nn.trans hs.1.le
    exact (hsum ν hν hν_0 tr htr s hs_nn).1 hs.2
  have hpost : ∫⁻ s in Ioi s_c, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s) ≤
      ENNReal.ofReal ((2 * K) / (ν * c ^ 2)) := by
    rw [← lintegral_postOverlap_rpow hK.le hν hc0]
    refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
    have hs_ge : s_c ≤ s := hs.le
    have hs_nn : 0 ≤ s := hsc_nn.trans hs_ge
    exact (hsum ν hν hν_0 tr htr s hs_nn).2 hs_ge
  calc ∫⁻ s in Ioi s₀, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)
      ≤ (∫⁻ s in Ioc s₀ s_c, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)) +
          (∫⁻ s in Ioi s_c, ∑ j ∈ Finset.Icc 1 (k + 1), B0277.supNormD j (tr.v s)) := hsplit
    _ ≤ ENNReal.ofReal (K / (ν * (1 + σ₀))) + ENNReal.ofReal ((2 * K) / (ν * c ^ 2)) :=
        add_le_add hpre hpost
    _ = ENNReal.ofReal (K / (ν * (1 + σ₀)) + (2 * K) / (ν * c ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((2 * K) / (ν * (1 + σ₀)) + (2 * K) / (ν * c ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have : K / (ν * (1 + σ₀)) ≤ (2 * K) / (ν * (1 + σ₀)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith

end UnforcedLeray.Short.PartI
