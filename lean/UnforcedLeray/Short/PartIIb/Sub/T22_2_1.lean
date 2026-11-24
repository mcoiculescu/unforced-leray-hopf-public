import UnforcedLeray.Short.PartIIb.Sub.T22_2

/-!


Source: `the November 2 reference manuscript`,
lines 2074-2105 (weak identity against time-dependent tests).

`CylWeakTimeDep` follows from
* `CylTdSeparated` (time slicing): the identity for finite sums `φ(r,x) = Σ χ_k(r) ψ_k(x)`,
  `χ_k ∈ C¹[t₀,t₁]`, `ψ_k` an `IsCylTest`, from the time-independent `weak` field of `IsFreeCylFlow`
  (Fubini and the product rule);
* `CylTdApprox` (approximation): every `CylEtaTest` is the limit of such sums, with both sides of the
  identity converging (η cut-off, decay against the `m > 8` weight, `strongCont`, `timeIntegrable`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- Finite sums of products of a `C¹` function of age and an `IsCylTest` of the plane. -/
def CylSepSum (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop :=
  ∃ (n : ℕ) (χ : Fin n → ℝ → ℝ) (ψ : Fin n → B0579.Plane → ℝ),
    (∀ k, ContDiffOn ℝ 1 (χ k) (Icc t₀ t₁)) ∧ (∀ k, B0579.IsCylTest c (ψ k)) ∧
      ∀ r x, φ r x = ∑ k, χ k r * ψ k x

/-- Left side of the time-dependent weak identity. -/
def cylTdLhs (c t₀ t₁ : ℝ) (f : B0579.Plane → ℝ) (ω : ℝ → B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ) : ℝ :=
  (∫ x in B0579.cell c, ω t₁ x * φ t₁ x) - ∫ x in B0579.cell c, f x * φ t₀ x

/-- Right side of the time-dependent weak identity. -/
def cylTdRhs {ν c : ℝ} (tr : B0140.TrainSol ν c) (t₀ t₁ : ℝ) (ω : ℝ → B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ) : ℝ :=
  ∫ r in t₀..t₁, ∫ x in B0579.cell c, ω r x *
    (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
      (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))

/-- **Lemma 1** (time slicing; SP 2074-2105). -/
def CylTdSeparated : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ), 0 < c → IsFreeCylFlow m tr t₀ f ω →
    ∀ (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), t₀ ≤ t₁ → CylSepSum c t₀ t₁ φ →
    cylTdLhs c t₀ t₁ f ω φ = cylTdRhs tr t₀ t₁ ω φ

/-- **Lemma 2** (approximation by separated sums; SP 2074-2105). -/
def CylTdApprox : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ), 0 < c → IsFreeCylFlow m tr t₀ f ω →
    ∀ (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), t₀ ≤ t₁ → CylEtaTest c t₀ t₁ φ →
    (∃ M : ℝ, ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    ∃ φs : ℕ → ℝ → B0579.Plane → ℝ, (∀ n, CylSepSum c t₀ t₁ (φs n)) ∧
      Tendsto (fun n => cylTdLhs c t₀ t₁ f ω (φs n)) atTop (𝓝 (cylTdLhs c t₀ t₁ f ω φ)) ∧
      Tendsto (fun n => cylTdRhs tr t₀ t₁ ω (φs n)) atTop (𝓝 (cylTdRhs tr t₀ t₁ ω φ))

theorem cylWeakTimeDep_of (h1 : CylTdSeparated) (h2 : CylTdApprox) : CylWeakTimeDep := by
  intro m hm ν c tr t₀ f ω hc hfl t₁ φ ht hφ hv
  obtain ⟨φs, hs, hl, hr⟩ := h2 m hm ν c tr t₀ f ω hc hfl t₁ φ ht hφ hv
  have heq : ∀ n, cylTdLhs c t₀ t₁ f ω (φs n) = cylTdRhs tr t₀ t₁ ω (φs n) :=
    fun n => h1 m hm ν c tr t₀ f ω hc hfl t₁ (φs n) ht (hs n)
  have hr' : Tendsto (fun n => cylTdLhs c t₀ t₁ f ω (φs n)) atTop
      (𝓝 (cylTdRhs tr t₀ t₁ ω φ)) := by
    simpa only [heq] using hr
  exact tendsto_nhds_unique hl hr'

end UnforcedLeray.Short.IIb
