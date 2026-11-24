import UnforcedLeray.Infra.RieszProjection.Bounds

/-!
# Riesz projections, IV: the operator on the two spectral subspaces

Let `X` be a complex Banach space, `T : X →L[ℂ] X`, `r > 0` with the circle `|z| = r` in the
resolvent set, `P = rieszProj T r`, `Q = 1 - P` and `S = rieszOuterInv T r`. The two spectral
subspaces are the closed subspaces

* `innerSubspace T r = ker (1 - P) = range P` (`range_rieszProj`),
* `outerSubspace T r = ker P = range (1 - P)` (`range_one_sub_rieszProj`),

both invariant under every operator commuting with `T`. On them we consider

* `innerPart T r`, the restriction `T|_{range P}`;
* `outerPart T r`, the restriction `T|_{range Q}`, and `outerPartInv T r = S|_{range Q}`.

Main results:

* `outerPart_mul_outerPartInv`, `outerPartInv_mul_outerPart`, `isUnit_outerPart`,
  `ringInverse_outerPart`: `T|_{range Q}` is invertible with inverse `S|_{range Q}`;
* `exists_rates_parts`: `‖(T|_{range P}) ^ n‖ ≤ C ρ ^ n` and `‖(T|_{range Q})^{-n}‖ ≤ C R⁻¹ ^ n`
  for some `0 < ρ < r < R` and `C ≥ 1`;
* `spectrum_innerPart_subset_ball`: `spectrum (T|_{range P}) ⊆ {|z| < r}`;
* `spectrum_outerPart_subset`: `spectrum (T|_{range Q}) ⊆ {|z| > r}`.

This is the splitting `X = P_-X ⊕ P_+X`, `ℳ_+ = ℳ|_{P_+X}` of `paper/main.tex`, lines 359-368
(with `P_- = P`, `P_+ = Q`).
-/

set_option autoImplicit false

noncomputable section

open Metric Complex
open scoped Real

namespace UnforcedLeray.Infra.RieszProjection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-! ### Restrictions of operators to invariant subspaces -/

section Restrict

variable {p : Submodule ℂ X}

omit [CompleteSpace X] in
theorem restrict_pow_apply (A : X →L[ℂ] X) (hA : ∀ x ∈ p, A x ∈ p) (n : ℕ) (x : p) :
    (((A.restrict hA) ^ n) x : X) = (A ^ n) x := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
      ContinuousLinearMap.coe_restrict_apply, ih]

omit [CompleteSpace X] in
/-- The restriction to an invariant subspace does not increase the norm of the powers. -/
theorem norm_restrict_pow_le (A : X →L[ℂ] X) (hA : ∀ x ∈ p, A x ∈ p) (n : ℕ) :
    ‖(A.restrict hA) ^ n‖ ≤ ‖A ^ n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  rw [Submodule.coe_norm, restrict_pow_apply, Submodule.coe_norm]
  exact (A ^ n).le_opNorm x

end Restrict

/-! ### The spectral subspaces -/

section Subspaces

/-- The range of the Riesz projection `P`, written as the (closed) kernel of `1 - P`. -/
abbrev innerSubspace (T : X →L[ℂ] X) (r : ℝ) : Submodule ℂ X :=
  (1 - rieszProj T r).ker

/-- The range of `1 - P`, written as the (closed) kernel of the Riesz projection `P`. -/
abbrev outerSubspace (T : X →L[ℂ] X) (r : ℝ) : Submodule ℂ X :=
  (rieszProj T r).ker

variable {T : X →L[ℂ] X} {r : ℝ}

omit [CompleteSpace X] in
theorem mem_innerSubspace {x : X} : x ∈ innerSubspace T r ↔ rieszProj T r x = x := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
    one_apply_eq_self, sub_eq_zero, eq_comm]

omit [CompleteSpace X] in
theorem mem_outerSubspace {x : X} : x ∈ outerSubspace T r ↔ rieszProj T r x = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

/-- `P x` lies in the range of `P`. -/
theorem rieszProj_apply_mem (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) (x : X) :
    rieszProj T r x ∈ innerSubspace T r := by
  rw [mem_innerSubspace, ← mul_apply_eq_comp, rieszProj_mul_self hr hT]

/-- `(1 - P) x` lies in the kernel of `P`. -/
theorem one_sub_rieszProj_apply_mem (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T)
    (x : X) : (1 - rieszProj T r) x ∈ outerSubspace T r := by
  rw [mem_outerSubspace, ← mul_apply_eq_comp, rieszProj_mul_one_sub hr hT,
    zero_apply]

/-- `range P = ker (1 - P)`. -/
theorem range_rieszProj (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    LinearMap.range (rieszProj T r : X →ₗ[ℂ] X) = innerSubspace T r := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact rieszProj_apply_mem hr hT y
  · intro hx
    exact ⟨x, mem_innerSubspace.1 hx⟩

/-- `range (1 - P) = ker P`. -/
theorem range_one_sub_rieszProj (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    LinearMap.range ((1 - rieszProj T r : X →L[ℂ] X) : X →ₗ[ℂ] X) = outerSubspace T r := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact one_sub_rieszProj_apply_mem hr hT y
  · intro hx
    refine ⟨x, ?_⟩
    rw [ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self,
      mem_outerSubspace.1 hx, sub_zero]

omit [CompleteSpace X] in
/-- Every `x` splits as `P x + (1 - P) x`. -/
theorem rieszProj_add_one_sub (x : X) : rieszProj T r x + (1 - rieszProj T r) x = x := by
  rw [sub_apply, one_apply_eq_self, add_sub_cancel]

/-- The range of `P` is invariant under every operator commuting with `T`. -/
theorem mapsTo_innerSubspace {B : X →L[ℂ] X} (hB : Commute B T) :
    ∀ x ∈ innerSubspace T r, B x ∈ innerSubspace T r := by
  intro x hx
  rw [mem_innerSubspace] at hx ⊢
  rw [← mul_apply_eq_comp, ← (commute_rieszProj_of_commute hB r).eq, mul_apply_eq_comp, hx]

/-- The kernel of `P` is invariant under every operator commuting with `T`. -/
theorem mapsTo_outerSubspace {B : X →L[ℂ] X} (hB : Commute B T) :
    ∀ x ∈ outerSubspace T r, B x ∈ outerSubspace T r := by
  intro x hx
  rw [mem_outerSubspace] at hx ⊢
  rw [← mul_apply_eq_comp, ← (commute_rieszProj_of_commute hB r).eq, mul_apply_eq_comp, hx,
    map_zero]

end Subspaces

/-! ### The restricted operators -/

section Parts

/-- `T` restricted to the range of its Riesz projection (`ℳ|_{P_-X}`). -/
def innerPart (T : X →L[ℂ] X) (r : ℝ) : innerSubspace T r →L[ℂ] innerSubspace T r :=
  T.restrict (mapsTo_innerSubspace (Commute.refl T))

/-- `T` restricted to the range of `1 - P` (`ℳ_+ = ℳ|_{P_+X}`). -/
def outerPart (T : X →L[ℂ] X) (r : ℝ) : outerSubspace T r →L[ℂ] outerSubspace T r :=
  T.restrict (mapsTo_outerSubspace (Commute.refl T))

/-- The outer inverse restricted to the range of `1 - P` (`ℳ_+⁻¹`). -/
def outerPartInv (T : X →L[ℂ] X) (r : ℝ) : outerSubspace T r →L[ℂ] outerSubspace T r :=
  (rieszOuterInv T r).restrict
    (mapsTo_outerSubspace (commute_rieszOuterInv_of_commute (Commute.refl T) r).symm)

variable {T : X →L[ℂ] X} {r : ℝ}

@[simp] theorem innerPart_apply (x : innerSubspace T r) : (innerPart T r x : X) = T x := rfl

@[simp] theorem outerPart_apply (x : outerSubspace T r) : (outerPart T r x : X) = T x := rfl

@[simp] theorem outerPartInv_apply (x : outerSubspace T r) :
    (outerPartInv T r x : X) = rieszOuterInv T r x := rfl

/-- `T|_{range Q} ∘ S|_{range Q} = 1`. -/
theorem outerPart_mul_outerPartInv (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    outerPart T r * outerPartInv T r = 1 := by
  ext x
  rw [mul_apply_eq_comp, outerPart_apply, outerPartInv_apply, one_apply_eq_self,
    ← mul_apply_eq_comp, mul_rieszOuterInv hr hT, sub_apply,
    one_apply_eq_self, mem_outerSubspace.1 x.2, sub_zero]

/-- `S|_{range Q} ∘ T|_{range Q} = 1`. -/
theorem outerPartInv_mul_outerPart (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    outerPartInv T r * outerPart T r = 1 := by
  ext x
  rw [mul_apply_eq_comp, outerPartInv_apply, outerPart_apply, one_apply_eq_self,
    ← mul_apply_eq_comp, rieszOuterInv_mul hr hT, sub_apply,
    one_apply_eq_self, mem_outerSubspace.1 x.2, sub_zero]

/-- **`T` is invertible on the range of `1 - P`.** -/
theorem isUnit_outerPart (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    IsUnit (outerPart T r) :=
  ⟨⟨outerPart T r, outerPartInv T r, outerPart_mul_outerPartInv hr hT,
    outerPartInv_mul_outerPart hr hT⟩, rfl⟩

/-- The inverse of `T|_{range Q}` is `S|_{range Q}`. -/
theorem ringInverse_outerPart (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    Ring.inverse (outerPart T r) = outerPartInv T r := by
  let u : (outerSubspace T r →L[ℂ] outerSubspace T r)ˣ :=
    ⟨outerPart T r, outerPartInv T r, outerPart_mul_outerPartInv hr hT,
      outerPartInv_mul_outerPart hr hT⟩
  exact Ring.inverse_unit u

/-- `‖(T|_{range P}) ^ n‖ ≤ ‖T ^ n P‖`. -/
theorem norm_innerPart_pow_le (n : ℕ) : ‖innerPart T r ^ n‖ ≤ ‖T ^ n * rieszProj T r‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  rw [Submodule.coe_norm, innerPart, restrict_pow_apply, Submodule.coe_norm]
  have hx : rieszProj T r x = x := mem_innerSubspace.1 x.2
  calc ‖(T ^ n) (x : X)‖ = ‖(T ^ n * rieszProj T r) (x : X)‖ := by
        rw [mul_apply_eq_comp, hx]
    _ ≤ ‖T ^ n * rieszProj T r‖ * ‖(x : X)‖ := (T ^ n * rieszProj T r).le_opNorm _

/-- `‖(S|_{range Q}) ^ n‖ ≤ ‖S ^ n‖`. -/
theorem norm_outerPartInv_pow_le (n : ℕ) : ‖outerPartInv T r ^ n‖ ≤ ‖rieszOuterInv T r ^ n‖ :=
  norm_restrict_pow_le _ _ n

/-- **The two rates on the spectral subspaces.** For every circle `|z| = r` in the resolvent set
there are `0 < ρ < r < R` and `C ≥ 1` with `‖(T|_{range P}) ^ n‖ ≤ C ρ ^ n` and
`‖(T|_{range Q})^{-n}‖ ≤ C R⁻¹ ^ n` for all `n`. -/
theorem exists_rates_parts (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ ρ R C : ℝ, 0 < ρ ∧ ρ < r ∧ r < R ∧ 1 ≤ C ∧
      (∀ n : ℕ, ‖innerPart T r ^ n‖ ≤ C * ρ ^ n) ∧
      (∀ n : ℕ, ‖outerPartInv T r ^ n‖ ≤ C * R⁻¹ ^ n) := by
  obtain ⟨ρ, R, C, hρ, hρr, hR, hC, h₁, h₂⟩ := exists_rates hr hT
  exact ⟨ρ, R, C, hρ, hρr, hR, hC, fun n => (norm_innerPart_pow_le n).trans (h₁ n),
    fun n => (norm_outerPartInv_pow_le n).trans (h₂ n)⟩

/-- The spectrum of `T|_{range P}` lies in a closed disc of radius `ρ < r`. -/
theorem exists_spectrum_innerPart_subset_closedBall (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ spectrum ℂ (innerPart T r) ⊆ closedBall (0 : ℂ) ρ := by
  obtain ⟨ρ, R, C, hρ, hρr, -, -, h₁, -⟩ := exists_rates_parts hr hT
  refine ⟨ρ, hρ, hρr, ?_⟩
  exact spectrum_subset_closedBall_of_norm_pow_le (innerPart T r) hρ.le h₁

/-- **The spectrum of `T` on the range of `P` lies in `|z| < r`.** -/
theorem spectrum_innerPart_subset_ball (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    spectrum ℂ (innerPart T r) ⊆ ball (0 : ℂ) r := by
  obtain ⟨ρ, -, hρr, h⟩ := exists_spectrum_innerPart_subset_closedBall hr hT
  exact h.trans (closedBall_subset_ball hρr)

/-- The spectrum of `T|_{range Q}` lies in `{|z| ≥ R}` for some `R > r`. -/
theorem exists_spectrum_outerPart_subset (hr : 0 < r)
    (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    ∃ R : ℝ, r < R ∧ spectrum ℂ (outerPart T r) ⊆ {z : ℂ | R ≤ ‖z‖} := by
  obtain ⟨ρ, R, C, -, -, hR, -, -, h₂⟩ := exists_rates_parts hr hT
  refine ⟨R, hR, ?_⟩
  have h1 : outerPart T r * outerPartInv T r = 1 := outerPart_mul_outerPartInv hr hT
  have h2 : outerPartInv T r * outerPart T r = 1 := outerPartInv_mul_outerPart hr hT
  exact spectrum_subset_of_norm_inv_pow_le (a := outerPart T r) (b := outerPartInv T r) h1 h2
    (hr.trans hR) h₂

/-- **The spectrum of `T` on the range of `1 - P` lies in `|z| > r`.** -/
theorem spectrum_outerPart_subset (hr : 0 < r) (hT : sphere (0 : ℂ) r ⊆ resolventSet ℂ T) :
    spectrum ℂ (outerPart T r) ⊆ {z : ℂ | r < ‖z‖} := by
  obtain ⟨R, hR, h⟩ := exists_spectrum_outerPart_subset hr hT
  exact fun z hz => hR.trans_le (h hz)

end Parts

end UnforcedLeray.Infra.RieszProjection
