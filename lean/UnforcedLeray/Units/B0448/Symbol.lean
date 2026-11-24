import UnforcedLeray.Units.B0448.Norm
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# B0448, part 2: the operator `∂_t − Δ_z + 1` and its symbol (tex 7677–7679)

Manuscript `paper/main.tex` lines 7677–7679 (blueprint unit B0448): "The identity `H = K*F` is
distributionally valid. Its uniqueness follows, for example, because the Fourier symbol
`iω + |ξ|² + 1` has no real zero."

Space-time is `ST = WithLp 2 (ℝ × ℝ³)` (time first), the Euclidean structure on `ℝ × ℝ³` that
Mathlib's tempered distributions `𝓢'(ST, F)` need. Here:

* `timeDir`, `spaceDir i`: the unit vectors `e_t`, `e_{z_i}`;
* `resolventOp T = ∂_t T − Δ_z T + T` and its transpose `resolventOpT φ = −∂_t φ − Δ_z φ + φ`,
  for any space with directional derivatives (Schwartz functions, tempered distributions);
* `resolventOp_apply`: `(L T)(φ) = T(Lᵗ φ)` for tempered distributions;
* `symbolT ξ = 1 + 4π² |ξ_z|² − 2πi ξ_t` (Mathlib's Fourier normalisation of the symbol
  `iω + |ξ|² + 1` of `Lᵗ`): `fourier_resolventOpT`, and `one_le_re_symbolT` (no real zero);
* `hasTemperateGrowth_inv_of_one_le_re`: `1/f` has temperate growth if `f` has and `Re f ≥ 1`;
* `resolventOpT_surjective` (`Lᵗ` is onto `𝓢`), hence `resolventOp_injective` on `𝓢'`:
  the uniqueness of tempered solutions of `(∂_t − Δ_z + 1)H = F`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0448

open MeasureTheory SchwartzMap LineDeriv FourierTransform Complex
open scoped SchwartzMap Real ENNReal

/-- Space-time `ℝ × ℝ³` with its Euclidean inner product (time first). -/
abbrev ST := WithLp 2 (ℝ × Space)

/-- The time unit vector `e_t = (1, 0)`. -/
def timeDir : ST := WithLp.toLp 2 ((1 : ℝ), (0 : Space))

/-- The spatial unit vector `e_{z_i} = (0, e_i)`. -/
def spaceDir (i : Fin 3) : ST := WithLp.toLp 2 ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))

section Ops

variable {V : Type*} [AddCommGroup V] [LineDeriv ST V V]

/-- The operator `L = ∂_t − Δ_z + 1` (tex 7663, `F = (∂_t − Δ_z + 1)H`), with
`Δ_z = Σ_i ∂_{z_i}²`. -/
def resolventOp (T : V) : V :=
  ∂_{timeDir} T - ∑ i : Fin 3, ∂_{spaceDir i} (∂_{spaceDir i} T) + T

/-- The formal transpose `Lᵗ = −∂_t − Δ_z + 1`. -/
def resolventOpT (T : V) : V :=
  -∂_{timeDir} T - ∑ i : Fin 3, ∂_{spaceDir i} (∂_{spaceDir i} T) + T

end Ops

/-- Distributional `L`: `(L T)(φ) = T(Lᵗ φ)`. -/
theorem resolventOp_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : 𝓢'(ST, F)) (φ : 𝓢(ST, ℂ)) : resolventOp T φ = T (resolventOpT φ) := by
  simp [resolventOp, resolventOpT, map_add, map_sub, map_neg, map_sum, sum_apply,
    TemperedDistribution.lineDerivOp_apply_apply, lineDerivOp_neg]
  done

/-- The symbol of `Lᵗ` in Mathlib's normalisation `𝓕 f(ξ) = ∫ e^{-2πi⟨x,ξ⟩} f(x) dx`:
`1 − 2πi ξ_t + 4π² Σ_i ξ_{z_i}²`. It is the manuscript's `iω + |ξ|² + 1` up to the scalings
`ω ↦ −2πω`, `ξ ↦ 2πξ`. -/
def symbolT (ξ : ST) : ℂ :=
  1 - 2 * π * I * ((inner ℝ ξ timeDir : ℝ) : ℂ) +
    4 * π ^ 2 * ∑ i : Fin 3, ((inner ℝ ξ (spaceDir i) : ℝ) : ℂ) ^ 2

theorem re_symbolT (ξ : ST) :
    (symbolT ξ).re = 1 + 4 * π ^ 2 * ∑ i : Fin 3, (inner ℝ ξ (spaceDir i)) ^ 2 := by
  simp only [symbolT, add_re, sub_re, one_re, mul_re, re_sum, ofReal_re, ofReal_im, I_re, I_im]
  simp [sq, ← ofReal_ofNat, ← ofReal_mul]

/-- **No real zero (tex 7678–7679).** `Re symbolT ≥ 1`. -/
theorem one_le_re_symbolT (ξ : ST) : 1 ≤ (symbolT ξ).re := by
  rw [re_symbolT]
  have : 0 ≤ ∑ i : Fin 3, (inner ℝ ξ (spaceDir i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [Real.pi_pos, sq_nonneg π]

theorem symbolT_ne_zero (ξ : ST) : symbolT ξ ≠ 0 := by
  intro h
  have := one_le_re_symbolT ξ
  rw [h, zero_re] at this
  linarith

theorem hasTemperateGrowth_symbolT : symbolT.HasTemperateGrowth := by
  unfold symbolT
  fun_prop

/-- If `f` has temperate growth and `Re f ≥ 1`, then `1/f` has temperate growth. -/
theorem hasTemperateGrowth_inv_of_one_le_re {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : f.HasTemperateGrowth) (h : ∀ x, 1 ≤ (f x).re) :
    (fun x => (f x)⁻¹).HasTemperateGrowth := by
  set t : Set ℂ := {z : ℂ | 1 ≤ z.re} with ht_def
  have ht : Set.range f ⊆ t := by rintro _ ⟨x, rfl⟩; exact h x
  have hint : (interior t).Nonempty := by
    refine ⟨2, ?_⟩
    have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine interior_maximal (fun (z : ℂ) (hz : 1 < z.re) => le_of_lt hz) ho ?_
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hu : UniqueDiffOn ℝ t := uniqueDiffOn_convex (convex_halfSpace_re_ge 1) hint
  have hne : ∀ z ∈ t, z ≠ 0 := by
    intro z hz h0
    simp only [ht_def, Set.mem_ofPred_eq, h0, zero_re] at hz
    linarith
  have hnorm : ∀ z ∈ t, 1 ≤ ‖z‖ := fun z hz => le_trans hz (re_le_norm z)
  refine Function.HasTemperateGrowth.comp' (g := Inv.inv) ht hu ?_ ?_ hf
  · intro z hz; exact (contDiffAt_inv ℝ (hne z hz)).contDiffWithinAt
  · intro N
    refine ⟨0, ∑ n ∈ Finset.range (N + 1), (Nat.factorial n : ℝ), by positivity, fun n hn z hz => ?_⟩
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu (contDiffAt_inv ℝ (hne z hz)) hz,
      ← (contDiffAt_inv ℂ (hne z hz) (n := (n : WithTop ℕ∞))).restrictScalars_iteratedFDeriv
        (𝕜 := ℝ)]
    simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
    have hz1 := hnorm z hz
    have hzp : ‖z ^ (-1 - n : ℤ)‖ ≤ 1 := by
      rw [norm_zpow]; exact zpow_le_one_of_nonpos₀ hz1 (by omega)
    calc ‖(-1) ^ n * (Nat.factorial n : ℂ) * z ^ (-1 - n : ℤ)‖
        = (Nat.factorial n : ℝ) * ‖z ^ (-1 - n : ℤ)‖ := by simp
      _ ≤ (Nat.factorial n : ℝ) * 1 := by gcongr
      _ ≤ ∑ m ∈ Finset.range (N + 1), (Nat.factorial m : ℝ) := by
          rw [mul_one]
          exact Finset.single_le_sum (f := fun m => (Nat.factorial m : ℝ)) (fun _ _ => by positivity)
            (Finset.mem_range.2 (by omega))
      _ = _ := by simp

theorem hasTemperateGrowth_inv_symbolT : (fun ξ => (symbolT ξ)⁻¹).HasTemperateGrowth :=
  hasTemperateGrowth_inv_of_one_le_re hasTemperateGrowth_symbolT one_le_re_symbolT

/-- `𝓕(∂_m f)(ξ) = 2πi ⟨ξ, m⟩ 𝓕 f(ξ)`. -/
theorem fourier_lineDerivOp_apply (f : 𝓢(ST, ℂ)) (m ξ : ST) :
    𝓕 (∂_{m} f) ξ = 2 * π * I * ((inner ℝ ξ m : ℝ) : ℂ) * 𝓕 f ξ := by
  have hm : (inner ℝ · m : ST → ℝ).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq]
  simp only [smul_apply, smulLeftCLM_apply_apply hm, Complex.real_smul, smul_eq_mul]
  ring

/-- `𝓕(Lᵗ ψ) = symbolT · 𝓕 ψ` on Schwartz functions. -/
theorem fourier_resolventOpT (ψ : 𝓢(ST, ℂ)) (ξ : ST) :
    𝓕 (resolventOpT ψ) ξ = symbolT ξ * 𝓕 ψ ξ := by
  simp only [resolventOpT, sub_eq_add_neg, FourierAdd.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_sum, add_apply, neg_apply, sum_apply, fourier_lineDerivOp_apply]
  rw [symbolT]
  have h : ∀ i : Fin 3, 2 * π * I * ((inner ℝ ξ (spaceDir i) : ℝ) : ℂ) *
      (2 * π * I * ((inner ℝ ξ (spaceDir i) : ℝ) : ℂ) * 𝓕 ψ ξ) =
      -(4 * π ^ 2 * ((inner ℝ ξ (spaceDir i) : ℝ) : ℂ) ^ 2 * 𝓕 ψ ξ) := fun i => by
    ring_nf; rw [I_sq]; ring
  simp only [h, Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The inverse of `Lᵗ` on Schwartz functions: the Fourier multiplier `1/symbolT`. -/
def resolventInvT (φ : 𝓢(ST, ℂ)) : 𝓢(ST, ℂ) :=
  𝓕⁻ (smulLeftCLM ℂ (fun ξ => (symbolT ξ)⁻¹) (𝓕 φ))

/-- `Lᵗ (resolventInvT φ) = φ`: the transpose `−∂_t − Δ_z + 1` maps `𝓢` onto `𝓢`. -/
theorem resolventOpT_resolventInvT (φ : 𝓢(ST, ℂ)) : resolventOpT (resolventInvT φ) = φ := by
  have h : 𝓕 (resolventOpT (resolventInvT φ)) = 𝓕 φ := by
    ext ξ
    rw [fourier_resolventOpT, resolventInvT, fourier_fourierInv_eq,
      smulLeftCLM_apply_apply hasTemperateGrowth_inv_symbolT, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (symbolT_ne_zero ξ), one_mul]
  have h' := congrArg (fun f : 𝓢(ST, ℂ) => 𝓕⁻ f) h
  simpa using h'

theorem resolventOpT_surjective :
    Function.Surjective (resolventOpT : 𝓢(ST, ℂ) → 𝓢(ST, ℂ)) :=
  fun φ => ⟨resolventInvT φ, resolventOpT_resolventInvT φ⟩

/-- **Uniqueness (tex 7677–7679).** `∂_t − Δ_z + 1` is injective on tempered distributions,
because its symbol has no real zero: a tempered solution of `(∂_t − Δ_z + 1)H = F` is unique. -/
theorem resolventOp_injective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] :
    Function.Injective (resolventOp : 𝓢'(ST, F) → 𝓢'(ST, F)) := by
  intro T₁ T₂ h
  ext φ
  have h1 := resolventOp_apply T₁ (resolventInvT φ)
  have h2 := resolventOp_apply T₂ (resolventInvT φ)
  rw [resolventOpT_resolventInvT] at h1 h2
  rw [← h1, ← h2, h]

/-- **Uniqueness among `L^q` functions.** If `H₁, H₂ ∈ L^q(ℝ × ℝ³)` (`1 ≤ q ≤ ∞`) satisfy
`(∂_t − Δ_z + 1)H₁ = (∂_t − Δ_z + 1)H₂` in `𝓢'`, then `H₁ = H₂`. -/
theorem eq_of_resolventOp_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] {H₁ H₂ : Lp ℂ q (volume : Measure ST)}
    (h : resolventOp (H₁ : 𝓢'(ST, ℂ)) = resolventOp (H₂ : 𝓢'(ST, ℂ))) : H₁ = H₂ := by
  have h' : (H₁ : 𝓢'(ST, ℂ)) = (H₂ : 𝓢'(ST, ℂ)) := resolventOp_injective h
  have hk := MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
    (μ := (volume : Measure ST)) (p := q)
  rw [LinearMap.ker_eq_bot] at hk
  exact hk h'

end UnforcedLeray.B0448
