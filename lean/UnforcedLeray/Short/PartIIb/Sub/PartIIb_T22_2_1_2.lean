import UnforcedLeray.Short.PartIIb.Sub.T22_2_1

/-!


Source: `the November 2 reference manuscript`,
lines 2074-2105 (approximation of a time-dependent test by separated sums).

`CylTdApprox` follows from
* `CylTdApproxSums` : every `CylEtaTest` is the limit of separated sums in the weighted `C¹` sense
  `CylTdConv` (C¹ hat-function interpolation in `r`, smooth `η` cut-off whose error is killed by the
  `(1+η²)^N` decay);
* `CylTdLhsCont` : `CylTdConv` implies convergence of `cylTdLhs` (uses `memX`, `strongCont`, `m > 8`);
* `CylTdRhsCont` : `CylTdConv` and the bounded train velocity imply convergence of `cylTdRhs`
  (dominated convergence in `r`; measurability of the limit is automatic as a pointwise limit).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- Weighted `C¹` convergence `φs n → φ` on `[t₀,t₁] × ℝ²` with weight `(1+η²)^N` for every `N`:
values and planar derivatives on `Icc`, age derivative on `Ioo`. -/
def CylTdConv (c t₀ t₁ : ℝ) (φs : ℕ → ℝ → B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop :=
  ∀ N ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
      (|φs n r x - φ r x| + |B0579.pd 0 (φs n r) x - B0579.pd 0 (φ r) x| +
        |B0579.pd 1 (φs n r) x - B0579.pd 1 (φ r) x| + |lapP (φs n r) x - lapP (φ r) x|) *
        (1 + x.2 ^ 2) ^ N ≤ ε) ∧
    (∀ r ∈ Ioo t₀ t₁, ∀ x : B0579.Plane,
      |deriv (fun r' => φs n r' x) r - deriv (fun r' => φ r' x) r| * (1 + x.2 ^ 2) ^ N ≤ ε)

/-- Approximation by separated sums (SP 2074-2105). -/
def CylTdApproxSums : Prop :=
  ∀ (c t₀ t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ), 0 < c → t₀ ≤ t₁ → CylEtaTest c t₀ t₁ φ →
    ∃ φs : ℕ → ℝ → B0579.Plane → ℝ, (∀ n, CylSepSum c t₀ t₁ (φs n)) ∧ CylTdConv c t₀ t₁ φs φ

/-- Continuity of the left side under `CylTdConv`. The hypothesis `∀ n, CylSepSum ... (φs n)` supplies
measurability of `φs n r` (without it the Bochner integrals could be `0` by non-integrability). -/
def CylTdLhsCont : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ), 0 < c → IsFreeCylFlow m tr t₀ f ω →
    ∀ (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ) (φs : ℕ → ℝ → B0579.Plane → ℝ), t₀ ≤ t₁ →
    CylEtaTest c t₀ t₁ φ → (∀ n, CylSepSum c t₀ t₁ (φs n)) → CylTdConv c t₀ t₁ φs φ →
    Tendsto (fun n => cylTdLhs c t₀ t₁ f ω (φs n)) atTop (𝓝 (cylTdLhs c t₀ t₁ f ω φ))

/-- Continuity of the right side under `CylTdConv` (bounded train velocity). -/
def CylTdRhsCont : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ), 0 < c → IsFreeCylFlow m tr t₀ f ω →
    ∀ (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ) (φs : ℕ → ℝ → B0579.Plane → ℝ), t₀ ≤ t₁ →
    CylEtaTest c t₀ t₁ φ → (∀ n, CylSepSum c t₀ t₁ (φs n)) → CylTdConv c t₀ t₁ φs φ →
    (∃ M : ℝ, ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M) →
    Tendsto (fun n => cylTdRhs tr t₀ t₁ ω (φs n)) atTop (𝓝 (cylTdRhs tr t₀ t₁ ω φ))

theorem cylTdApprox_of (h1 : CylTdApproxSums) (h2 : CylTdLhsCont) (h3 : CylTdRhsCont) :
    CylTdApprox := by
  intro m hm ν c tr t₀ f ω hc hfl t₁ φ ht hφ hv
  obtain ⟨φs, hs, hconv⟩ := h1 c t₀ t₁ φ hc ht hφ
  exact ⟨φs, hs, h2 m hm ν c tr t₀ f ω hc hfl t₁ φ φs ht hφ hs hconv,
    h3 m hm ν c tr t₀ f ω hc hfl t₁ φ φs ht hφ hs hconv hv⟩

end UnforcedLeray.Short.IIb
