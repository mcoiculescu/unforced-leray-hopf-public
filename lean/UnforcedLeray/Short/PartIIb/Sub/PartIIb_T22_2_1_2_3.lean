import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2

/-!


Source: `the November 2 reference manuscript`,
lines 2074-2105 (time-dependent weak identity; right side continuous under `CylTdConv`).

`CylTdRhsCont` follows by interval dominated convergence from
* `CylTdRhsMeas`: each `r ↦ ∫_cell ω r (…)` for a separated sum is a.e.-strongly measurable
  (from `CylSepSum` and `IsFreeCylFlow.timeIntegrable`, `strongCont`);
* `CylTdRhsPointwise`: pointwise convergence for `r ∈ (t₀,t₁)` (weighted `L²` Cauchy–Schwarz,
  `CylPairBound`, using `memX`, and `CylTdConv` with `N = 0`);
* `CylTdRhsBound`: a uniform bound for large `n` (`CylFlowNormBound` and `CylPairBound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- The inner integral of `cylTdRhs` at age `r`. -/
def cylTdInner {ν c : ℝ} (tr : B0140.TrainSol ν c) (ω : ℝ → B0579.Plane → ℝ)
    (φ : ℝ → B0579.Plane → ℝ) (r : ℝ) : ℝ :=
  ∫ x in B0579.cell c, ω r x *
    (deriv (fun r' => φ r' x) r + ν * lapP (φ r) x +
      (tr.v r x 0 * B0579.pd 0 (φ r) x + tr.v r x 1 * B0579.pd 1 (φ r) x))

theorem cylTdRhs_eq_integral_inner {ν c : ℝ} (tr : B0140.TrainSol ν c) (t₀ t₁ : ℝ)
    (ω φ : ℝ → B0579.Plane → ℝ) :
    cylTdRhs tr t₀ t₁ ω φ = ∫ r in t₀..t₁, cylTdInner tr ω φ r := rfl

/-- The hypotheses of `CylTdRhsCont`, bundled. -/
def CylRhsHyp (m : ℝ) {ν c : ℝ} (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ) (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (φs : ℕ → ℝ → B0579.Plane → ℝ) (M : ℝ) : Prop :=
  8 < m ∧ 0 < c ∧ IsFreeCylFlow m tr t₀ f ω ∧ t₀ ≤ t₁ ∧ CylEtaTest c t₀ t₁ φ ∧
    (∀ n, CylSepSum c t₀ t₁ (φs n)) ∧ CylTdConv c t₀ t₁ φs φ ∧
    ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, |tr.v r x 0| + |tr.v r x 1| ≤ M

/-- Generic weighted pairing estimate (Cauchy–Schwarz against `⟨x⟩^{-m}` on the cell; SP 2074-2105):
for `m > 8` and `c > 0` there is `K` with `|∫_cell ω g| ≤ K A ‖ω‖_{L²(cellMeasure c m)}` whenever
`|g| ≤ A` on the cell. -/
def CylPairBound : Prop :=
  ∀ m : ℝ, 8 < m → ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (ω g : B0579.Plane → ℝ) (A : ℝ), MemLp ω 2 (B0579.cellMeasure c m) →
      AEStronglyMeasurable g (volume.restrict (B0579.cell c)) →
      (∀ x ∈ B0579.cell c, |g x| ≤ A) →
      |∫ x in B0579.cell c, ω x * g x| ≤ K * A * (eLpNorm ω 2 (B0579.cellMeasure c m)).toReal

/-- The weighted norm of a free cylinder flow is bounded on `[t₀,t₁]` (continuity from `strongCont`
and compactness). -/
def CylFlowNormBound : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ), IsFreeCylFlow m tr t₀ f ω → ∀ t₁ : ℝ, t₀ ≤ t₁ →
    ∃ B : ℝ, ∀ r ∈ Icc t₀ t₁, (eLpNorm (ω r) 2 (B0579.cellMeasure c m)).toReal ≤ B

/-- Measurability in age of the inner integral for separated sums. -/
def CylTdRhsMeas : Prop :=
  ∀ (m : ℝ) (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ) (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (φs : ℕ → ℝ → B0579.Plane → ℝ) (M : ℝ), CylRhsHyp m tr t₀ f ω t₁ φ φs M →
    ∀ n, AEStronglyMeasurable (cylTdInner tr ω (φs n)) (volume.restrict (Ioc t₀ t₁))

/-- Pointwise convergence of the inner integrals for `r ∈ (t₀,t₁)`. -/
def CylTdRhsPointwise : Prop :=
  ∀ (m : ℝ) (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ) (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (φs : ℕ → ℝ → B0579.Plane → ℝ) (M : ℝ), CylRhsHyp m tr t₀ f ω t₁ φ φs M →
    ∀ r ∈ Ioo t₀ t₁, Tendsto (fun n => cylTdInner tr ω (φs n) r) atTop (𝓝 (cylTdInner tr ω φ r))

/-- Uniform bound of the inner integrals for large `n` and `r ∈ (t₀,t₁)`. -/
def CylTdRhsBound : Prop :=
  ∀ (m : ℝ) (ν c : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ) (f : B0579.Plane → ℝ)
    (ω : ℝ → B0579.Plane → ℝ) (t₁ : ℝ) (φ : ℝ → B0579.Plane → ℝ)
    (φs : ℕ → ℝ → B0579.Plane → ℝ) (M : ℝ), CylRhsHyp m tr t₀ f ω t₁ φ φs M →
    ∃ (B : ℝ) (n₀ : ℕ), ∀ n, n₀ ≤ n → ∀ r ∈ Ioo t₀ t₁, |cylTdInner tr ω (φs n) r| ≤ B

theorem cylTdRhsCont_of (h1 : CylTdRhsMeas) (h2 : CylTdRhsPointwise) (h3 : CylTdRhsBound) :
    CylTdRhsCont := by
  intro m hm ν c tr t₀ f ω hc hfl t₁ φ φs ht hφ hsep hconv ⟨M, hM⟩
  have H : CylRhsHyp m tr t₀ f ω t₁ φ φs M := ⟨hm, hc, hfl, ht, hφ, hsep, hconv, hM⟩
  obtain ⟨B, n₀, hB⟩ := h3 m ν c tr t₀ f ω t₁ φ φs M H
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t₁ := by
    have : (volume : Measure ℝ) {t₁} = 0 := Real.volume_singleton
    simpa [ae_iff] using this
  have hI : Ι t₀ t₁ = Ioc t₀ t₁ := uIoc_of_le ht
  change Tendsto (fun n => ∫ r in t₀..t₁, cylTdInner tr ω (φs n) r) atTop
    (𝓝 (∫ r in t₀..t₁, cylTdInner tr ω φ r))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
    intervalIntegrable_const ?_
  · refine Eventually.of_forall fun n => ?_
    rw [hI]
    exact h1 m ν c tr t₀ f ω t₁ φ φs M H n
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    filter_upwards [hne] with r hr hrI
    rw [hI] at hrI
    have hr' : r ∈ Ioo t₀ t₁ := ⟨hrI.1, lt_of_le_of_ne hrI.2 hr⟩
    simpa [Real.norm_eq_abs] using hB n hn r hr'
  · filter_upwards [hne] with r hr hrI
    rw [hI] at hrI
    exact h2 m ν c tr t₀ f ω t₁ φ φs M H r ⟨hrI.1, lt_of_le_of_ne hrI.2 hr⟩

end UnforcedLeray.Short.IIb
