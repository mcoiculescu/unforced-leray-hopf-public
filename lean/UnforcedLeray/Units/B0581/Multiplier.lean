import UnforcedLeray.Units.B0581.Modes
import Mathlib.Analysis.Fourier.LpSpace

/-!
# B0581 helper: the Biot–Savart multiplier of a nonzero horizontal mode

Blueprint unit **B0581**, `paper/main.tex` lines 9410–9411: "For `k ≠ 0`, the Biot–Savart
multiplier has modulus at most `|k|^{-1} ≤ c/(2π)`".

Conventions. The cylinder Biot–Savart law is `u = K_c ω = ∇^⊥ Δ^{-1} ω` with
`∇^⊥ = (-∂_η, ∂_q)` (the planar convention of `paper/main.tex:662`, `K = ∇^⊥Δ^{-1}`, on the
cylinder). On the Fourier side, with horizontal frequency `κ ∈ (2π/c)ℤ` (the manuscript's `k`)
and vertical frequency `ζ`, `∂_q ↦ iκ`, `∂_η ↦ iζ`, `Δ ↦ -(κ² + ζ²)`, so
`û = bsSym κ ζ · ω̂` with `bsSym κ ζ = (iζ, -iκ)/(κ² + ζ²) ∈ ℂ²` (`bsSym`). Mathlib's Fourier
transform on `ℝ` is `𝓕 f(ξ) = ∫ e^{-2πixξ} f(x) dx`, so `∂_η ↦ 2πiξ` and the symbol of mode `k`
at Mathlib frequency `ξ` is `bsSymbol c k ξ = bsSym (2πk/c) (2πξ)`.

* `norm_bsSym_le`: `|bsSym κ ζ| ≤ |κ|⁻¹` for `κ ≠ 0` (exactly `(κ² + ζ²)^{-1/2}`,
  `norm_sq_bsSym`).
* `norm_bsSymbol_le`: for `k ≠ 0` and `c > 0`, `|bsSymbol c k ξ| ≤ |2πk/c|⁻¹ ≤ c/(2π)`.
* `bsModeCLM c k : L²(ℝ; ℂ) →L L²(ℝ; ℂ²)`, `g ↦ 𝓕⁻¹(bsSymbol c k · 𝓕 g)` for `k ≠ 0` (and `0` for
  `k = 0`, the velocity of the nonzero-mode part), with `‖bsModeCLM c k‖ ≤ c/(2π)`.
* `velModes c : ℓ²(ℤ; L²(ℝ; ℂ)) →L ℓ²(ℤ; L²(ℝ; ℂ²))`, the mode-wise multiplier.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex FourierTransform
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0581

/-- Velocity values: `ℂ²` with the Euclidean norm. -/
abbrev Vel : Type := EuclideanSpace ℂ (Fin 2)

/-- The horizontal frequency `κ_k = 2πk/c ∈ (2π/c)ℤ` of the mode `e_k`. -/
def kappa (c : ℝ) (k : ℤ) : ℝ := 2 * π * k / c

theorem two_pi_div_le_abs_kappa {c : ℝ} (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) :
    2 * π / c ≤ |kappa c k| := by
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  rw [kappa, abs_div, abs_mul, abs_of_pos hc, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  apply div_le_div_of_nonneg_right _ hc.le
  nlinarith [Real.pi_pos]

theorem kappa_ne_zero {c : ℝ} (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) : kappa c k ≠ 0 := by
  intro h
  have := two_pi_div_le_abs_kappa hc hk
  rw [h, abs_zero] at this
  have : 0 < 2 * π / c := by positivity
  linarith

/-- `|κ|⁻¹ ≤ c/(2π)` for `κ ∈ (2π/c)ℤ \ {0}` (`paper/main.tex:9411`). -/
theorem inv_abs_kappa_le {c : ℝ} (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) :
    |kappa c k|⁻¹ ≤ c / (2 * π) := by
  have h := two_pi_div_le_abs_kappa hc hk
  have h0 : 0 < 2 * π / c := by positivity
  calc |kappa c k|⁻¹ ≤ (2 * π / c)⁻¹ := inv_anti₀ h0 h
    _ = c / (2 * π) := inv_div _ _

/-- The Biot–Savart symbol `(iζ, -iκ)/(κ² + ζ²)` of `∇^⊥Δ^{-1}` at frequency `(κ, ζ)`. -/
def bsSym (κ ζ : ℝ) : Vel :=
  !₂[((ζ / (κ ^ 2 + ζ ^ 2) : ℝ) : ℂ) * I, -(((κ / (κ ^ 2 + ζ ^ 2) : ℝ) : ℂ) * I)]

theorem norm_sq_bsSym {κ ζ : ℝ} (h : κ ^ 2 + ζ ^ 2 ≠ 0) :
    ‖bsSym κ ζ‖ ^ 2 = (κ ^ 2 + ζ ^ 2)⁻¹ := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [bsSym, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- **The Biot–Savart multiplier has modulus at most `|κ|⁻¹`** (`paper/main.tex:9410-9411`). -/
theorem norm_bsSym_le {κ : ℝ} (hκ : κ ≠ 0) (ζ : ℝ) : ‖bsSym κ ζ‖ ≤ |κ|⁻¹ := by
  have hpos : 0 < κ ^ 2 := by positivity
  have h1 : ‖bsSym κ ζ‖ ^ 2 ≤ (|κ|⁻¹) ^ 2 := by
    rw [norm_sq_bsSym (by positivity), inv_pow, sq_abs]
    exact inv_anti₀ hpos (by nlinarith [sq_nonneg ζ])
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

/-- Order zero: the symbols `iκ · bsSym κ ζ` and `iζ · bsSym κ ζ` of `∂_q K_c` and `∂_η K_c` have
modulus at most `1` (the multiplier remark of `paper/main.tex:9425-9426`, symbol level only). -/
theorem norm_smul_bsSym_le {κ ζ : ℝ} (h : κ ^ 2 + ζ ^ 2 ≠ 0) :
    ‖(κ : ℂ) • bsSym κ ζ‖ ≤ 1 ∧ ‖(ζ : ℂ) • bsSym κ ζ‖ ≤ 1 := by
  have hpos : 0 < κ ^ 2 + ζ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
  have key : ∀ a : ℝ, a ^ 2 ≤ κ ^ 2 + ζ ^ 2 → ‖(a : ℂ) • bsSym κ ζ‖ ≤ 1 := by
    intro a ha
    have h1 : ‖(a : ℂ) • bsSym κ ζ‖ ^ 2 ≤ 1 ^ 2 := by
      rw [norm_smul, mul_pow, norm_sq_bsSym h, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        one_pow, ← div_eq_mul_inv, div_le_one hpos]
      exact ha
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h1
  exact ⟨key κ (by nlinarith [sq_nonneg ζ]), key ζ (by nlinarith [sq_nonneg κ])⟩

theorem continuous_bsSym {κ : ℝ} (hκ : κ ≠ 0) : Continuous (bsSym κ) := by
  have hd : ∀ ζ : ℝ, κ ^ 2 + ζ ^ 2 ≠ 0 := fun ζ => by positivity
  have h1 : Continuous fun ζ : ℝ => ζ / (κ ^ 2 + ζ ^ 2) :=
    continuous_id.div (by fun_prop) hd
  have h2 : Continuous fun ζ : ℝ => κ / (κ ^ 2 + ζ ^ 2) :=
    continuous_const.div (by fun_prop) hd
  unfold bsSym
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    exact (continuous_ofReal.comp h1).mul continuous_const
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
    exact ((continuous_ofReal.comp h2).mul continuous_const).neg

/-- The Biot–Savart symbol of the horizontal mode `k` at Mathlib frequency `ξ`
(`∂_η ↦ 2πiξ`): `bsSym (2πk/c) (2πξ)`. -/
def bsSymbol (c : ℝ) (k : ℤ) (ξ : ℝ) : Vel := bsSym (kappa c k) (2 * π * ξ)

/-- **Nonzero modes**: `|bsSymbol c k ξ| ≤ |2πk/c|⁻¹ ≤ c/(2π)` (`paper/main.tex:9410-9411`). -/
theorem norm_bsSymbol_le {c : ℝ} (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) (ξ : ℝ) :
    ‖bsSymbol c k ξ‖ ≤ |kappa c k|⁻¹ ∧ |kappa c k|⁻¹ ≤ c / (2 * π) :=
  ⟨norm_bsSym_le (kappa_ne_zero hc hk) _, inv_abs_kappa_le hc hk⟩

theorem norm_bsSymbol_le' {c : ℝ} (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) (ξ : ℝ) :
    ‖bsSymbol c k ξ‖ ≤ c / (2 * π) :=
  (norm_bsSymbol_le hc hk ξ).1.trans (norm_bsSymbol_le hc hk ξ).2

theorem continuous_bsSymbol {c : ℝ} (hc : 0 < c) {k : ℤ} (hk : k ≠ 0) :
    Continuous (bsSymbol c k) :=
  (continuous_bsSym (kappa_ne_zero hc hk)).comp (continuous_const.mul continuous_id)

/-! ### Bounded multipliers on `L²(ℝ)` -/

section SymMul

variable {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem memLp_symMul {m : ℝ → G} (hm : Continuous m) {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun ξ => (f : ℝ → ℂ) ξ • m ξ) 2 volume :=
  (Lp.memLp f).of_le_mul ((Lp.aestronglyMeasurable f).smul hm.aestronglyMeasurable)
    (Eventually.of_forall fun ξ => by
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

/-- Multiplication `f ↦ f · m` by a bounded continuous symbol `m : ℝ → G`. -/
def symMulLM (m : ℝ → G) (hm : Continuous m) (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp G 2 (volume : Measure ℝ) where
  toFun f := (memLp_symMul hm hC f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add f g] with ξ h
    rw [h, Pi.add_apply, Pi.add_apply, add_smul]
  map_smul' a f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul a f] with ξ h
    rw [h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_smul]

theorem coeFn_symMulLM (m : ℝ → G) (hm : Continuous m) (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    symMulLM m hm C hC f =ᵐ[volume] fun ξ => (f : ℝ → ℂ) ξ • m ξ :=
  MemLp.coeFn_toLp (memLp_symMul hm hC f)

/-- The bounded multiplier `f ↦ f · m`, of norm at most `sup |m|`. -/
def symMulCLM (m : ℝ → G) (hm : Continuous m) (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp G 2 (volume : Measure ℝ) :=
  (symMulLM m hm C hC).mkContinuous C fun f => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_symMulLM m hm C hC f] with ξ h
    rw [h, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

theorem coeFn_symMulCLM (m : ℝ → G) (hm : Continuous m) (C : ℝ) (hC : ∀ ξ, ‖m ξ‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    symMulCLM m hm C hC f =ᵐ[volume] fun ξ => (f : ℝ → ℂ) ξ • m ξ :=
  coeFn_symMulLM m hm C hC f

end SymMul

/-! ### The velocity of one nonzero horizontal mode -/

/-- The `L²` Fourier transform on `ℝ`, as a continuous linear map. -/
def fourierL2 (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] :
    Lp G 2 (volume : Measure ℝ) →L[ℂ] Lp G 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ G).toLinearIsometry.toContinuousLinearMap

/-- The inverse `L²` Fourier transform on `ℝ`, as a continuous linear map. -/
def fourierInvL2 (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] :
    Lp G 2 (volume : Measure ℝ) →L[ℂ] Lp G 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ G).symm.toLinearIsometry.toContinuousLinearMap

theorem fourierL2_apply (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (f : Lp G 2 (volume : Measure ℝ)) : fourierL2 G f = 𝓕 f := rfl

theorem fourierInvL2_apply (G : Type) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (f : Lp G 2 (volume : Measure ℝ)) : fourierInvL2 G f = 𝓕⁻ f := rfl

/-- **Velocity of the horizontal mode `k`.** For `k ≠ 0`, the Fourier multiplier
`g ↦ 𝓕⁻¹(bsSymbol c k · 𝓕 g)`, `L²(ℝ; ℂ) → L²(ℝ; ℂ²)`; for `k = 0` it is `0` (this operator
builds the velocity of the nonzero-mode part only). -/
def bsModeCLM (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp Vel 2 (volume : Measure ℝ) :=
  if hk : k = 0 then 0 else
    fourierInvL2 Vel ∘L
      symMulCLM (bsSymbol c k) (continuous_bsSymbol hc.out hk) (c / (2 * π))
        (norm_bsSymbol_le' hc.out hk) ∘L fourierL2 ℂ

theorem bsModeCLM_zero (c : ℝ) [Fact (0 < c)] : bsModeCLM c 0 = 0 := by
  simp [bsModeCLM]

/-- For `k ≠ 0`, the Fourier transform of the velocity mode is the Biot–Savart symbol times the
Fourier transform of the vorticity mode. -/
theorem fourier_bsModeCLM (c : ℝ) [hc : Fact (0 < c)] {k : ℤ} (hk : k ≠ 0)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((𝓕 (bsModeCLM c k g) : Lp Vel 2 (volume : Measure ℝ)) : ℝ → Vel) =ᵐ[volume]
      fun ξ => ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ • bsSymbol c k ξ := by
  have h : (𝓕 (bsModeCLM c k g) : Lp Vel 2 (volume : Measure ℝ)) =
      symMulCLM (bsSymbol c k) (continuous_bsSymbol hc.out hk) (c / (2 * π))
        (norm_bsSymbol_le' hc.out hk) (𝓕 g) := by
    simp only [bsModeCLM, dif_neg hk, ContinuousLinearMap.comp_apply, fourierInvL2_apply,
      fourierL2_apply]
    exact FourierTransform.fourier_fourierInv_eq _
  rw [h]
  exact coeFn_symMulCLM _ _ _ _ _

theorem norm_bsModeCLM_apply_le (c : ℝ) [hc : Fact (0 < c)] (k : ℤ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖bsModeCLM c k g‖ ≤ c / (2 * π) * ‖g‖ := by
  have hC : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  by_cases hk : k = 0
  · subst hk
    rw [bsModeCLM_zero, ContinuousLinearMap.zero_apply, norm_zero]
    positivity
  · simp only [bsModeCLM, dif_neg hk, ContinuousLinearMap.comp_apply, fourierInvL2,
      fourierL2, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.norm_map]
    calc ‖symMulCLM (bsSymbol c k) (continuous_bsSymbol hc.out hk) (c / (2 * π))
          (norm_bsSymbol_le' hc.out hk) ((Lp.fourierTransformₗᵢ ℝ ℂ) g)‖
        ≤ c / (2 * π) * ‖(Lp.fourierTransformₗᵢ ℝ ℂ) g‖ := by
          refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
          filter_upwards [coeFn_symMulCLM (bsSymbol c k) (continuous_bsSymbol hc.out hk)
            (c / (2 * π)) (norm_bsSymbol_le' hc.out hk) ((Lp.fourierTransformₗᵢ ℝ ℂ) g)]
            with ξ h
          rw [h, norm_smul, mul_comm]
          exact mul_le_mul_of_nonneg_right (norm_bsSymbol_le' hc.out hk ξ) (norm_nonneg _)
      _ = c / (2 * π) * ‖g‖ := by rw [LinearIsometryEquiv.norm_map]

theorem norm_bsModeCLM_le (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) :
    ‖bsModeCLM c k‖ ≤ c / (2 * π) := by
  have hC : 0 ≤ c / (2 * π) := by have := hc.out; positivity
  exact ContinuousLinearMap.opNorm_le_bound _ hC (norm_bsModeCLM_apply_le c k)

/-! ### Diagonal operators on `ℓ²(ℤ; ·)` -/

section Diag

variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem memℓp_diag (T : ℤ → A →L[ℂ] B) {C : ℝ} (hT : ∀ k a, ‖T k a‖ ≤ C * ‖a‖)
    (g : lp (fun _ : ℤ => A) 2) : Memℓp (fun k => T k (g k)) 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine memℓp_gen ?_
  have hs := (lp.memℓp g).summable hp
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_) (hs.mul_left (C ^ 2))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc ‖T k (g k)‖ ^ 2 ≤ (C * ‖g k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hT k (g k)) 2
    _ = C ^ 2 * ‖g k‖ ^ 2 := by ring

/-- The sequence `(T_k g_k)_k`. -/
def diagFun (T : ℤ → A →L[ℂ] B) {C : ℝ} (hT : ∀ k a, ‖T k a‖ ≤ C * ‖a‖)
    (g : lp (fun _ : ℤ => A) 2) : lp (fun _ : ℤ => B) 2 :=
  ⟨fun k => T k (g k), memℓp_diag T hT g⟩

theorem norm_diagFun_le (T : ℤ → A →L[ℂ] B) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ k a, ‖T k a‖ ≤ C * ‖a‖) (g : lp (fun _ : ℤ => A) 2) :
    ‖diagFun T hT g‖ ≤ C * ‖g‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (by positivity) ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hs := (lp.memℓp g).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have hs' := (memℓp_diag T hT g).summable hp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs'
  have hn := lp.norm_rpow_eq_tsum hp g
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  calc ∑' k, ‖(diagFun T hT g : lp (fun _ : ℤ => B) 2) k‖ ^ 2
        ≤ ∑' k, C ^ 2 * ‖g k‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun k => ?_) hs' (hs.mul_left _)
        calc ‖T k (g k)‖ ^ 2 ≤ (C * ‖g k‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hT k (g k)) 2
          _ = C ^ 2 * ‖g k‖ ^ 2 := by ring
    _ = (C * ‖g‖) ^ 2 := by rw [tsum_mul_left, ← hn]; ring

/-- The diagonal operator `(g_k) ↦ (T_k g_k)` for uniformly bounded `T_k`. -/
def diagCLM (T : ℤ → A →L[ℂ] B) (C : ℝ) (hC : 0 ≤ C) (hT : ∀ k a, ‖T k a‖ ≤ C * ‖a‖) :
    lp (fun _ : ℤ => A) 2 →L[ℂ] lp (fun _ : ℤ => B) 2 :=
  LinearMap.mkContinuous
    { toFun := diagFun T hT
      map_add' := fun f g => by
        ext1
        funext k
        exact (T k).map_add (f k) (g k)
      map_smul' := fun a g => by
        ext1
        funext k
        simp [diagFun, lp.coeFn_smul, Pi.smul_apply] }
    C (norm_diagFun_le T hC hT)

theorem diagCLM_apply (T : ℤ → A →L[ℂ] B) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ k a, ‖T k a‖ ≤ C * ‖a‖) (g : lp (fun _ : ℤ => A) 2) (k : ℤ) :
    (diagCLM T C hC hT g : lp (fun _ : ℤ => B) 2) k = T k (g k) := rfl

theorem norm_diagCLM_apply_le (T : ℤ → A →L[ℂ] B) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ k a, ‖T k a‖ ≤ C * ‖a‖) (g : lp (fun _ : ℤ => A) 2) :
    ‖diagCLM T C hC hT g‖ ≤ C * ‖g‖ :=
  norm_diagFun_le T hC hT g

end Diag

/-- The mode-wise Biot–Savart multiplier `(ω_k)_k ↦ (u_k)_k`, `u_0 = 0`,
`u_k = 𝓕⁻¹(bsSymbol c k · 𝓕 ω_k)` (`k ≠ 0`); bounded by `c/(2π)`. -/
def velModes (c : ℝ) [hc : Fact (0 < c)] : ModeSeq ℂ →L[ℂ] ModeSeq Vel :=
  diagCLM (bsModeCLM c) (c / (2 * π)) (by have := hc.out; positivity)
    (norm_bsModeCLM_apply_le c)

theorem velModes_apply (c : ℝ) [Fact (0 < c)] (g : ModeSeq ℂ) (k : ℤ) :
    (velModes c g : ModeSeq Vel) k = bsModeCLM c k (g k) := rfl

theorem norm_velModes_apply_le (c : ℝ) [hc : Fact (0 < c)] (g : ModeSeq ℂ) :
    ‖velModes c g‖ ≤ c / (2 * π) * ‖g‖ :=
  norm_diagCLM_apply_le _ _ _ _ g

end UnforcedLeray.B0581
