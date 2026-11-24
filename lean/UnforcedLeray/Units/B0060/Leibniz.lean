import NonUniqueEuler.P.Infra.Sobolev.WeakDeriv
import Mathlib.Data.Nat.Choose.Sum

/-!
# B0060 helper: the weak Leibniz rule with a smooth coefficient on the plane

Helper for blueprint unit **B0060** (`paper/main.tex:1215–1220`, `eq:st18-t00049`, "Leibniz and
this kernel split give"; blueprint infrastructure INF11 "Leibniz rule for weak derivatives").

For `χ ∈ C^∞(ℝ²)` (no boundedness needed) and a family `D δ` of locally integrable functions with
`∂₁ D δ = D (δ + e₁)` and `∂₂ D δ = D (δ + e₂)` weakly (`|δ| < k`), the weak derivative of order
`γ`, `|γ| ≤ k`, of `χ D₀` is `∑_{β ≤ γ} C(γ₁,β₁) C(γ₂,β₂) ∂^β χ · D (γ - β)` (`leibniz_2d`).

Adapted from the NonUniqueEuler reference formalization,
`NonUniqueEuler/lean/NonUniqueEuler/H/Infra/Sobolev/Leibniz/Product.lean`
(`hasWeakDerivOn_sum`, `leibniz_dir`, `leibniz_2d`, `HasWeakDerivOn.of_append`). The reference
treats `C^k` multipliers by mollification; here the coefficient is `C^∞`, so `χ φ` is itself a test
function and the one-direction rule (`hasWeakDerivOn_mul_smooth`) is the direct computation of

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.B0060

open NonUniqueEuler.Sob NonUniqueEuler.Sob.WeakDerivAux

/-- Product rule for directional derivatives of smooth functions. -/
theorem dirDeriv_mul {a c : ℂ → ℂ} (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c) (v x : ℂ) :
    dirDeriv v (fun y => a y * c y) x = dirDeriv v a x * c x + a x * dirDeriv v c x := by
  have hd : HasFDerivAt (fun y => a y * c y) (a x • fderiv ℝ c x + c x • fderiv ℝ a x) x :=
    (ha.differentiable (by simp) x).hasFDerivAt.mul (hc.differentiable (by simp) x).hasFDerivAt
  simp only [dirDeriv]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Leibniz rule in one direction with a smooth coefficient**:
`∂_v (χ u) = (∂_v χ) u + χ ∂_v u` weakly on the plane, for locally integrable `u` with a locally
integrable weak derivative `g = ∂_v u`. -/
theorem hasWeakDerivOn_mul_smooth {χ u g : ℂ → ℂ} {v : ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hu : LocallyIntegrable u) (hg : LocallyIntegrable g) (h : HasWeakDerivOn univ [v] u g) :
    HasWeakDerivOn univ [v] (fun x => χ x * u x)
      (fun x => dirDeriv v χ x * u x + χ x * g x) := by
  intro φ hφ
  have hcφ : IsTestFn univ (fun y => χ y * φ y) :=
    ⟨hχ.mul hφ.smooth, hφ.compact.mul_left, subset_univ _⟩
  have hdcφ : IsTestFn univ (fun y => dirDeriv v χ y * φ y) :=
    ⟨(contDiff_dirDeriv hχ v).mul hφ.smooth, hφ.compact.mul_left, subset_univ _⟩
  have hu' := hu.locallyIntegrableOn univ
  have hg' := hg.locallyIntegrableOn univ
  have e1 := h _ hcφ
  simp only [iterDirDeriv_cons, iterDirDeriv_nil, List.length_singleton, pow_one] at e1 ⊢
  have i1 := integrable_mul_testFn hu' (hcφ.dirDeriv v)
  have i2 := integrable_mul_testFn hu' hdcφ
  have i3 := integrable_mul_testFn hg' hcφ
  calc ∫ y, χ y * u y * dirDeriv v φ y
      = ∫ y, (u y * dirDeriv v (fun y => χ y * φ y) y - u y * (dirDeriv v χ y * φ y)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [dirDeriv_mul hχ hφ.smooth]
        ring
    _ = (-1 : ℂ) * (∫ y, g y * (χ y * φ y)) - ∫ y, u y * (dirDeriv v χ y * φ y) := by
        rw [integral_sub i1 i2, e1]
    _ = -1 * ∫ y, (dirDeriv v χ y * u y + χ y * g y) * φ y := by
        have : ∫ y, (dirDeriv v χ y * u y + χ y * g y) * φ y =
            (∫ y, u y * (dirDeriv v χ y * φ y)) + ∫ y, g y * (χ y * φ y) := by
          rw [← integral_add i2 i3]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only
          ring
        rw [this]
        ring

/-- Peeling off the inner derivatives: if `g = ∂_{ws} f` and `h = ∂_{ws ++ vs} f` weakly, then
`h = ∂_{vs} g` weakly (reference `Leibniz/Product.lean`, `HasWeakDerivOn.of_append`). -/
theorem hasWeakDerivOn_of_append {V : Set ℂ} {ws vs : List ℂ} {f g h : ℂ → ℂ}
    (hfg : HasWeakDerivOn V ws f g) (hfh : HasWeakDerivOn V (ws ++ vs) f h) :
    HasWeakDerivOn V vs g h := by
  intro φ hφ
  have e1 := hfg _ (hφ.iterDirDeriv vs)
  have e2 := hfh φ hφ
  rw [iterDirDeriv_append] at e2
  have e := e1.symm.trans e2
  rw [List.length_append, pow_add, mul_assoc] at e
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) e

theorem hasWeakDerivOn_nil_self {V : Set ℂ} (f : ℂ → ℂ) : HasWeakDerivOn V [] f f := by
  intro φ _
  simp

/-- Linearity for finite combinations on the plane (reference `hasWeakDerivOn_sum`). -/
theorem hasWeakDerivOn_sum {ι : Type*} (s : Finset ι) {vs : List ℂ} (c : ι → ℂ)
    {F G : ι → ℂ → ℂ} (hF : ∀ i ∈ s, LocallyIntegrable (F i))
    (hG : ∀ i ∈ s, LocallyIntegrable (G i)) (h : ∀ i ∈ s, HasWeakDerivOn univ vs (F i) (G i)) :
    HasWeakDerivOn univ vs (fun x => ∑ i ∈ s, c i * F i x) (fun x => ∑ i ∈ s, c i * G i x) := by
  intro φ hφ
  have hd := hφ.iterDirDeriv vs
  have iF : ∀ i ∈ s, Integrable (fun x => c i * (F i x * iterDirDeriv vs φ x)) := fun i hi =>
    (integrable_mul_testFn ((hF i hi).locallyIntegrableOn univ) hd).const_mul _
  have iG : ∀ i ∈ s, Integrable (fun x => c i * (G i x * φ x)) := fun i hi =>
    (integrable_mul_testFn ((hG i hi).locallyIntegrableOn univ) hφ).const_mul _
  calc ∫ x, (∑ i ∈ s, c i * F i x) * iterDirDeriv vs φ x
      = ∫ x, ∑ i ∈ s, c i * (F i x * iterDirDeriv vs φ x) := by
        congr 1
        funext x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ s, ∫ x, c i * (F i x * iterDirDeriv vs φ x) := integral_finsetSum s iF
    _ = ∑ i ∈ s, (-1 : ℂ) ^ vs.length * ∫ x, c i * (G i x * φ x) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_const_mul, integral_const_mul, h i hi φ hφ]
        ring
    _ = (-1 : ℂ) ^ vs.length * ∫ x, ∑ i ∈ s, c i * (G i x * φ x) := by
        rw [integral_finsetSum s iG, Finset.mul_sum]
    _ = (-1 : ℂ) ^ vs.length * ∫ x, (∑ i ∈ s, c i * G i x) * φ x := by
        congr 2
        funext x
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The one-direction Leibniz formula `∂_v^n (χ D₀) = ∑_{j ≤ n} C(n,j) ∂_v^j χ D_{n-j}` for smooth
`χ` (reference `leibniz_dir`). -/
theorem leibniz_dir (v : ℂ) {N : ℕ} {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) {D : ℕ → ℂ → ℂ}
    (hD : ∀ j ≤ N, LocallyIntegrable (D j))
    (hDD : ∀ j < N, HasWeakDerivOn univ [v] (D j) (D (j + 1))) :
    ∀ n ≤ N, HasWeakDerivOn univ (List.replicate n v) (fun x => χ x * D 0 x)
      (fun x => ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (iterDirDeriv (List.replicate j v) χ x * D (n - j) x)) := by
  intro n
  induction n with
  | zero =>
    intro _ φ _
    simp
  | succ n ih =>
    intro hn
    have IH := ih (by omega)
    have hcont : ∀ j, Continuous (iterDirDeriv (List.replicate j v) χ) := fun j =>
      (contDiff_iterDirDeriv hχ _).continuous
    have step := hasWeakDerivOn_sum (Finset.range (n + 1)) (vs := [v])
      (fun j => (n.choose j : ℂ))
      (F := fun j x => iterDirDeriv (List.replicate j v) χ x * D (n - j) x)
      (G := fun j x => iterDirDeriv (List.replicate (j + 1) v) χ x * D (n - j) x +
        iterDirDeriv (List.replicate j v) χ x * D (n - j + 1) x)
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        exact (hD _ (by omega)).continuous_mul (hcont j))
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        exact ((hD _ (by omega)).continuous_mul (hcont (j + 1))).add
          ((hD _ (by omega)).continuous_mul (hcont j)))
      (fun j hj => by
        have hj' := Finset.mem_range.1 hj
        have h1 := hasWeakDerivOn_mul_smooth (contDiff_iterDirDeriv hχ (List.replicate j v))
          (hD _ (by omega)) (hD _ (by omega)) (hDD (n - j) (by omega))
        have e : ∀ x, dirDeriv v (iterDirDeriv (List.replicate j v) χ) x =
            iterDirDeriv (List.replicate (j + 1) v) χ x := fun x => by
          rw [List.replicate_succ, iterDirDeriv_cons]
        simpa only [e] using h1)
    have htr := IH.trans step
    have e1 : [v] ++ List.replicate n v = List.replicate (n + 1) v := rfl
    rw [e1] at htr
    convert htr using 2 with x
    rw [Finset.sum_choose_succ_mul (fun i k => iterDirDeriv (List.replicate i v) χ x * D k x) n]
    rw [add_comm]
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : n + 1 - j = n - j + 1 := by omega
    rw [this]

/-- **The two-dimensional Leibniz formula** for a smooth coefficient and a family of weak
derivatives (reference `leibniz_2d`): for `|γ| ≤ k`,
`∂^γ (χ D₀) = ∑_{β ≤ γ} C(γ₁,β₁) C(γ₂,β₂) ∂^β χ · D (γ - β)` weakly on the plane. -/
theorem leibniz_2d {k : ℕ} {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) {F : ℕ × ℕ → ℂ → ℂ}
    (hF : ∀ δ ∈ multiIdx k, LocallyIntegrable (F δ))
    (h1 : ∀ δ : ℕ × ℕ, δ.1 + δ.2 < k → HasWeakDerivOn univ [1] (F δ) (F (δ.1 + 1, δ.2)))
    (h2 : ∀ δ : ℕ × ℕ, δ.1 + δ.2 < k →
      HasWeakDerivOn univ [Complex.I] (F δ) (F (δ.1, δ.2 + 1)))
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx k) :
    HasWeakDerivOn univ (pdList γ) (fun x => χ x * F (0, 0) x)
      (fun x => ∑ β ∈ leIdx γ, ((γ.1.choose β.1 * γ.2.choose β.2 : ℕ) : ℂ) * partialD β χ x *
        F (γ.1 - β.1, γ.2 - β.2) x) := by
  have hγk := mem_multiIdx.1 hγ
  obtain ⟨a, b⟩ := γ
  simp only at hγk ⊢
  have hFi : ∀ i j, i + j ≤ k → LocallyIntegrable (F (i, j)) := fun i j hij =>
    hF (i, j) (mem_multiIdx.2 hij)
  -- the inner formula, in the direction `I`
  have inner := leibniz_dir Complex.I (N := b) (χ := χ) hχ
    (D := fun j => F (0, j)) (fun j hj => hFi 0 j (by omega))
    (fun j hj => h2 (0, j) (by simp; omega)) b le_rfl
  -- the outer formulas, in the direction `1`
  have hcont : ∀ i j,
      Continuous (iterDirDeriv (List.replicate i 1) (iterDirDeriv (List.replicate j Complex.I) χ)) :=
    fun i j => by
      rw [← iterDirDeriv_append]
      exact (contDiff_iterDirDeriv hχ _).continuous
  have outer := hasWeakDerivOn_sum (Finset.range (b + 1)) (vs := List.replicate a 1)
    (fun j => (b.choose j : ℂ))
    (F := fun j x => iterDirDeriv (List.replicate j Complex.I) χ x * F (0, b - j) x)
    (G := fun j x => ∑ i ∈ Finset.range (a + 1), (a.choose i : ℂ) *
      (iterDirDeriv (List.replicate i 1) (iterDirDeriv (List.replicate j Complex.I) χ) x *
        F (a - i, b - j) x))
    (fun j hj => by
      have hj' := Finset.mem_range.1 hj
      exact (hFi 0 (b - j) (by omega)).continuous_mul
        (contDiff_iterDirDeriv hχ _).continuous)
    (fun j hj => by
      have hj' := Finset.mem_range.1 hj
      refine locallyIntegrable_finsetSum _ fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact ((hFi (a - i) (b - j) (by omega)).continuous_mul
        (hcont i j)).smul ((a.choose i : ℂ)))
    (fun j hj => by
      have hj' := Finset.mem_range.1 hj
      exact leibniz_dir 1 (contDiff_iterDirDeriv hχ _) (D := fun i => F (i, b - j))
        (fun i hi => hFi i (b - j) (by omega))
        (fun i hi => h1 (i, b - j) (by simp; omega)) a le_rfl)
  have htr := inner.trans outer
  have e1 : List.replicate a (1 : ℂ) ++ List.replicate b Complex.I = pdList (a, b) := rfl
  rw [e1] at htr
  convert htr using 2 with x
  rw [leIdx, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [partialD, pdList, iterDirDeriv_append]
  push_cast
  ring

end UnforcedLeray.B0060
