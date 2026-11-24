import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.CutSliceTest

/-!

interpolation.

Source: `the November 2 reference manuscript`, lines 2074-2105.
With `α_k(r) = pou_k(r) (1 - s_k(r))`, `β_k(r) = pou_k(r) s_k(r)`, `s_k(r) = (r - a_k)/h`, the
approximant is the finite combination `Σ_{k<K} (α_k ψ_k + β_k ψ_{k+1})` with `ψ_k = θ_R φ(a_k, ·)`
(constant in the coefficients), each `ψ_k` an `IsCylTest` by `CutSliceTest`. Differentiation in
`x` is linear on such combinations, so `∂_j` and `Δ` pass through the coefficients.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- Coefficient of the left node `a_k` in the age interpolation at age `r`. -/
def interpCAlpha (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  pou t₀ t₁ K k r * (1 - (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K)

/-- Coefficient of the right node `a_{k+1}` in the age interpolation at age `r`. -/
def interpCBeta (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  pou t₀ t₁ K k r * ((r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K)

theorem interpC_sum_identity (t₀ t₁ : ℝ) (K : ℕ) (r : ℝ) (g : ℝ → ℝ) :
    interp1 t₀ t₁ K g r = ∑ k ∈ Finset.range K,
      (interpCAlpha t₀ t₁ K r k * g (gridPt t₀ t₁ K k) +
        interpCBeta t₀ t₁ K r k * g (gridPt t₀ t₁ K (k + 1))) := by
  unfold interp1 interpCAlpha interpCBeta
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Planar derivative of a finite linear combination of differentiable functions. -/
theorem interpC_pd_sum (j : Fin 2) (s : Finset ℕ) (a b : ℕ → ℝ)
    (g : ℕ → B0579.Plane → ℝ)
    (hg : ∀ k ∈ s, Differentiable ℝ (g k) ∧ Differentiable ℝ (g (k + 1)))
    (x : B0579.Plane) :
    B0579.pd j (fun y => ∑ k ∈ s, (a k * g k y + b k * g (k + 1) y)) x =
      ∑ k ∈ s, (a k * B0579.pd j (g k) x + b k * B0579.pd j (g (k + 1)) x) := by
  have hsum : fderiv ℝ (fun y => ∑ k ∈ s, (a k * g k y + b k * g (k + 1) y)) x =
      ∑ k ∈ s, (a k • fderiv ℝ (g k) x + b k • fderiv ℝ (g (k + 1)) x) := by
    rw [fderiv_fun_sum (A := fun k y => a k * g k y + b k * g (k + 1) y)]
    · apply Finset.sum_congr rfl
      intro k hk
      show fderiv ℝ (fun y => a k * g k y + b k * g (k + 1) y) x = _
      rw [fderiv_fun_add (((hg k hk).1 x).const_mul (a k)) (((hg k hk).2 x).const_mul (b k)),
        fderiv_const_mul ((hg k hk).1 x) (a k), fderiv_const_mul ((hg k hk).2 x) (b k)]
    · intro k hk
      exact (((hg k hk).1 x).const_mul (a k)).add (((hg k hk).2 x).const_mul (b k))
  unfold B0579.pd
  rw [hsum]
  simp [sum_apply, add_apply, smul_apply, smul_eq_mul]

theorem interpC_gridPt_mem {t₀ t₁ : ℝ} {K k : ℕ} (ht : t₀ ≤ t₁) (hk : k ≤ K) :
    gridPt t₀ t₁ K k ∈ Icc t₀ t₁ := by
  rw [mem_Icc]
  unfold gridPt gridH
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hk0 : k = 0 := by omega
    subst hk0
    simp [ht]
  · have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hD : 0 ≤ (t₁ - t₀) / K := div_nonneg (by linarith) hKr.le
    have hkr : (k : ℝ) ≤ K := by exact_mod_cast hk
    have hKD : (K : ℝ) * ((t₁ - t₀) / K) = t₁ - t₀ := by
      field_simp
    have h1 : (k : ℝ) * ((t₁ - t₀) / K) ≤ K * ((t₁ - t₀) / K) :=
      mul_le_mul_of_nonneg_right hkr hD
    have h2 : (0 : ℝ) ≤ (k : ℝ) * ((t₁ - t₀) / K) := mul_nonneg (Nat.cast_nonneg k) hD
    constructor <;> linarith

theorem interpCommute : UnforcedLeray.Short.IIb.TdSums.InterpCommute := by
  intro c t₀ t₁ R K φ hR ht hφ r x
  have hcs : CutSliceTest := cutSliceTest
  have hslice : ∀ k, k ≤ K → B0579.IsCylTest c (cutTest R φ (gridPt t₀ t₁ K k)) :=
    fun k hk => hcs c t₀ t₁ R φ hR hφ _ (interpC_gridPt_mem ht hk)
  have hsep : sepApprox t₀ t₁ K R φ r = fun z => ∑ k ∈ Finset.range K,
      (interpCAlpha t₀ t₁ K r k * cutTest R φ (gridPt t₀ t₁ K k) z +
        interpCBeta t₀ t₁ K r k * cutTest R φ (gridPt t₀ t₁ K (k + 1)) z) := by
    funext z
    exact interpC_sum_identity t₀ t₁ K r (fun s => cutTest R φ s z)
  have hdiff : ∀ k ∈ Finset.range K,
      Differentiable ℝ (fun z => cutTest R φ (gridPt t₀ t₁ K k) z) ∧
        Differentiable ℝ (fun z => cutTest R φ (gridPt t₀ t₁ K (k + 1)) z) := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact ⟨(hslice k (by omega)).differentiable, (hslice (k + 1) (by omega)).differentiable⟩
  have hdiffj : ∀ j : Fin 2, ∀ k ∈ Finset.range K,
      Differentiable ℝ (fun z => B0579.pd j (cutTest R φ (gridPt t₀ t₁ K k)) z) ∧
        Differentiable ℝ (fun z => B0579.pd j (cutTest R φ (gridPt t₀ t₁ K (k + 1))) z) := by
    intro j k hk
    rw [Finset.mem_range] at hk
    exact ⟨((hslice k (by omega)).pd j).differentiable,
      ((hslice (k + 1) (by omega)).pd j).differentiable⟩
  have hpart1 : ∀ j : Fin 2, ∀ z : B0579.Plane,
      B0579.pd j (sepApprox t₀ t₁ K R φ r) z = ∑ k ∈ Finset.range K,
        (interpCAlpha t₀ t₁ K r k * B0579.pd j (cutTest R φ (gridPt t₀ t₁ K k)) z +
          interpCBeta t₀ t₁ K r k * B0579.pd j (cutTest R φ (gridPt t₀ t₁ K (k + 1))) z) := by
    intro j z
    rw [hsep]
    exact interpC_pd_sum j (Finset.range K) (interpCAlpha t₀ t₁ K r) (interpCBeta t₀ t₁ K r)
      (fun k z => cutTest R φ (gridPt t₀ t₁ K k) z) hdiff z
  refine ⟨fun j => ?_, ?_⟩
  · rw [hpart1 j x, interpC_sum_identity]
  · unfold lapP
    have e0 : B0579.pd 0 (sepApprox t₀ t₁ K R φ r) = fun z => ∑ k ∈ Finset.range K,
        (interpCAlpha t₀ t₁ K r k * B0579.pd 0 (cutTest R φ (gridPt t₀ t₁ K k)) z +
          interpCBeta t₀ t₁ K r k * B0579.pd 0 (cutTest R φ (gridPt t₀ t₁ K (k + 1))) z) :=
      funext (fun z => hpart1 0 z)
    have e1 : B0579.pd 1 (sepApprox t₀ t₁ K R φ r) = fun z => ∑ k ∈ Finset.range K,
        (interpCAlpha t₀ t₁ K r k * B0579.pd 1 (cutTest R φ (gridPt t₀ t₁ K k)) z +
          interpCBeta t₀ t₁ K r k * B0579.pd 1 (cutTest R φ (gridPt t₀ t₁ K (k + 1))) z) :=
      funext (fun z => hpart1 1 z)
    rw [e0, e1, interpC_pd_sum 0 (Finset.range K) (interpCAlpha t₀ t₁ K r)
      (interpCBeta t₀ t₁ K r) (fun k z => B0579.pd 0 (cutTest R φ (gridPt t₀ t₁ K k)) z)
      (hdiffj 0) x,
      interpC_pd_sum 1 (Finset.range K) (interpCAlpha t₀ t₁ K r) (interpCBeta t₀ t₁ K r)
      (fun k z => B0579.pd 1 (cutTest R φ (gridPt t₀ t₁ K k)) z) (hdiffj 1) x]
    rw [interpC_sum_identity, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
