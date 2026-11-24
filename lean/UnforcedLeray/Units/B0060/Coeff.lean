import UnforcedLeray.Units.B0008
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# B0060 helper: weighted coefficient seminorms of a Schwartz function

Helper for blueprint unit **B0060** (`paper/main.tex:1215–1220`, `eq:st18-t00049`): the proof
(tex 1219–1220) uses, for a Schwartz coefficient `b`, the *weighted `L^∞` coefficient bounds*
`sup_y ⟨y⟩^M |∂^β b(y)|` and the *weighted `L²` coefficient bounds* `‖⟨y⟩^M ∂^β b‖₂`, for the
finitely many `β` with `|β| ≤ j + 1`. Both are finite for `b ∈ 𝓢(ℝ²)`:

* `schwartzIter`, `coe_schwartzIter`: `∂^β b` is again a Schwartz function (Mathlib's
  `LineDeriv` instance on `𝓢`), so it suffices to treat `β = 0`;
* `exists_weighted_sup`: `⟨y⟩^M |g(y)| ≤ A` (Mathlib `SchwartzMap.one_add_le_sup_seminorm_apply`
  with `⟨y⟩ ≤ 1 + |y|`);
* `memLp_weighted`: `⟨y⟩^M g ∈ L²` (from the sup bound with `M + 2` and
  `∫ ⟨y⟩^{-4} < ∞`, B0008's `integrable_inv_weight`);
* `exists_coeff_bounds`: common bounds `A`, `B` over a finite set of multi-indices.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal ContDiff

namespace UnforcedLeray.B0060

open NonUniqueEuler.Sob UnforcedLeray.B0008

/-- The iterated directional derivative `∂_{v₁} ⋯ ∂_{vₙ} g` of a Schwartz function, as a Schwartz
function. -/
def schwartzIter : List ℂ → 𝓢(ℂ, ℂ) → 𝓢(ℂ, ℂ)
  | [], g => g
  | v :: vs, g => LineDeriv.lineDerivOp v (schwartzIter vs g)

theorem coe_schwartzIter (vs : List ℂ) (g : 𝓢(ℂ, ℂ)) :
    ⇑(schwartzIter vs g) = iterDirDeriv vs (g : ℂ → ℂ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [schwartzIter, iterDirDeriv_cons, dirDeriv]
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, ih]

/-- `∂^β b` of a Schwartz function `b` is the Schwartz function `schwartzIter (pdList β) b`. -/
theorem partialD_eq_schwartzIter (β : ℕ × ℕ) (b : 𝓢(ℂ, ℂ)) :
    partialD β (b : ℂ → ℂ) = ⇑(schwartzIter (pdList β) b) := by
  rw [coe_schwartzIter]
  rfl

theorem one_le_bracket' (y : ℂ) : 1 ≤ bracket y := by
  rw [bracket]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖y‖])

theorem bracket_le_one_add_norm (y : ℂ) : bracket y ≤ 1 + ‖y‖ := by
  rw [bracket, Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith [norm_nonneg y]⟩

/-- `⟨y⟩^M ≤ (1 + |y|)^{⌈M⌉}`. -/
theorem bracket_rpow_le (M : ℝ) (y : ℂ) : bracket y ^ M ≤ (1 + ‖y‖) ^ ⌈M⌉₊ := by
  calc bracket y ^ M ≤ bracket y ^ (⌈M⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_bracket' y) (Nat.le_ceil M)
    _ = bracket y ^ ⌈M⌉₊ := Real.rpow_natCast _ _
    _ ≤ (1 + ‖y‖) ^ ⌈M⌉₊ := pow_le_pow_left₀ (bracket_pos y).le (bracket_le_one_add_norm y) _

/-- **Weighted `L^∞` bound of a Schwartz function**: `⟨y⟩^M |g(y)| ≤ A` for some `A ≥ 0`. -/
theorem exists_weighted_sup (g : 𝓢(ℂ, ℂ)) (M : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y, bracket y ^ M * ‖g y‖ ≤ A := by
  have hb : ∀ y, bracket y ^ M * ‖g y‖ ≤ 2 ^ ⌈M⌉₊ *
      ((Finset.Iic (⌈M⌉₊, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g := by
    intro y
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (⌈M⌉₊, 0))
      (k := ⌈M⌉₊) (n := 0) le_rfl le_rfl g y
    rw [norm_iteratedFDeriv_zero] at h
    exact (mul_le_mul_of_nonneg_right (bracket_rpow_le M y) (norm_nonneg _)).trans h
  exact ⟨_, le_trans (mul_nonneg (Real.rpow_nonneg (bracket_pos 0).le M) (norm_nonneg _)) (hb 0),
    hb⟩

theorem bracket_rpow_two (y : ℂ) : bracket y ^ (2 : ℝ) = 1 + ‖y‖ ^ 2 := by
  rw [Real.rpow_two, bracket, Real.sq_sqrt (one_add_norm_sq_pos y).le]

/-- **Weighted `L²` membership of a Schwartz function**: `⟨y⟩^M g ∈ L²(ℝ²)`. -/
theorem memLp_weighted (g : 𝓢(ℂ, ℂ)) (M : ℝ) :
    MemLp (fun y => bracket y ^ M • g y) 2 volume := by
  obtain ⟨A, hA0, hA⟩ := exists_weighted_sup g (M + 2)
  have hmeas : AEStronglyMeasurable (fun y => bracket y ^ M • g y) volume :=
    ((continuous_bracket_rpow M).smul g.continuous).aestronglyMeasurable
  have hP : ∀ y : ℂ, 0 < 1 + ‖y‖ ^ 2 := one_add_norm_sq_pos
  have hcP : Continuous fun y : ℂ => (1 + ‖y‖ ^ 2)⁻¹ :=
    (continuous_const.add (continuous_norm.pow 2)).inv₀ fun y => (hP y).ne'
  have hdom : MemLp (fun y : ℂ => A * (1 + ‖y‖ ^ 2)⁻¹) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm
      (continuous_const.mul hcP).aestronglyMeasurable).2 ?_
    have hi := (integrable_inv_weight (M := 2) (by norm_num)).const_mul (A ^ 2)
    refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
    show A ^ 2 * (1 + ‖y‖ ^ 2) ^ (-(2 : ℝ)) = ‖A * (1 + ‖y‖ ^ 2)⁻¹‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.rpow_neg (hP y).le, Real.rpow_two, inv_pow]
  refine hdom.of_le hmeas (Filter.Eventually.of_forall fun y => ?_)
  have hy := hA y
  rw [Real.rpow_add (bracket_pos y), bracket_rpow_two] at hy
  have hb0 : 0 ≤ bracket y ^ M := Real.rpow_nonneg (bracket_pos y).le M
  rw [norm_smul, Real.norm_of_nonneg hb0,
    Real.norm_of_nonneg (mul_nonneg hA0 (inv_nonneg.2 (hP y).le))]
  rw [le_mul_inv_iff₀ (hP y)]
  calc bracket y ^ M * ‖g y‖ * (1 + ‖y‖ ^ 2) = bracket y ^ M * (1 + ‖y‖ ^ 2) * ‖g y‖ := by ring
    _ ≤ A := hy

/-- **The weighted coefficient bounds of a Schwartz coefficient** (tex 1219–1220): for every
finite set `s` of multi-indices there are `A, B ≥ 0` with `⟨y⟩^M |∂^β b(y)| ≤ A` for all `y` and
`‖⟨y⟩^M ∂^β b‖₂ ≤ B`, for all `β ∈ s`. -/
theorem exists_coeff_bounds (b : 𝓢(ℂ, ℂ)) (M : ℝ) (s : Finset (ℕ × ℕ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ β ∈ s, ∀ y, bracket y ^ M * ‖partialD β (b : ℂ → ℂ) y‖ ≤ A) ∧
      (∀ β ∈ s, eLpNorm (fun y => bracket y ^ M • partialD β (b : ℂ → ℂ) y) 2 volume ≤
        ENNReal.ofReal B) := by
  classical
  have hA : ∀ β : ℕ × ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ y, bracket y ^ M * ‖partialD β (b : ℂ → ℂ) y‖ ≤ A := fun β => by
    rw [partialD_eq_schwartzIter]
    exact exists_weighted_sup _ M
  choose A hA0 hA using hA
  let B : ℕ × ℕ → ℝ := fun β =>
    (eLpNorm (fun y => bracket y ^ M • partialD β (b : ℂ → ℂ) y) 2 volume).toReal
  refine ⟨∑ β ∈ s, A β, ∑ β ∈ s, B β, Finset.sum_nonneg fun β _ => hA0 β,
    Finset.sum_nonneg fun β _ => ENNReal.toReal_nonneg,
    fun β hβ y => (hA β y).trans (Finset.single_le_sum (fun β _ => hA0 β) hβ), fun β hβ => ?_⟩
  have hm : MemLp (fun y => bracket y ^ M • partialD β (b : ℂ → ℂ) y) 2 volume := by
    rw [partialD_eq_schwartzIter]
    exact memLp_weighted _ M
  calc eLpNorm (fun y => bracket y ^ M • partialD β (b : ℂ → ℂ) y) 2 volume
      = ENNReal.ofReal (B β) := (ENNReal.ofReal_toReal hm.2.ne).symm
    _ ≤ ENNReal.ofReal (∑ β ∈ s, B β) :=
        ENNReal.ofReal_le_ofReal
          (Finset.single_le_sum (f := B) (fun β _ => ENNReal.toReal_nonneg) hβ)

end UnforcedLeray.B0060
