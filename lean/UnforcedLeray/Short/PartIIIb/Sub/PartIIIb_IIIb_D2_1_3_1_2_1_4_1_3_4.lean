import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3

/-!
# `selLimit`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`Y_2`-convergence gives a subsequence with a.e.-`τ` slice `L²(ℝ³)` convergence (on one period,
then on all `τ` by periodicity); at such a `τ` the weak-derivative identity passes to the limit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- (1) Subsequence with a.e.-slice `L²` convergence on one period (source 1341-1344): from
`phaseLpNorm P 2 (Ψ n - Φ) → 0` the period integral `∫⁻_{(0,P]} s_n(τ) → 0` where
`s_n(τ) = ∫⁻_y ‖(Ψ n - Φ)(τ,y)‖ₑ²` (constant `P⁻¹` positive); pick `φ` strictly monotone with
`∫⁻ (s_{φ k} + t_{φ k}) ≤ 2^{-k}`, so `∑ₖ (s_{φ k} + t_{φ k}) < ∞` a.e. (`lintegral_tsum`,
slice integrals are a.e.-measurable by `AEMeasurable.lintegral_prod_right'`) and the terms tend to
`0` a.e. -/
def SelSubseq : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ F : ℝ × Space → CVec3) (Ψ D : ℕ → ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 F →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (Ψ n)) →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (D n)) →
    YConv P Ψ Φ → YConv P D F →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ᵐ τ : ℝ, τ ∈ Ioc (0 : ℝ) P →
          Tendsto (fun k => ∫⁻ y : Space, ‖Ψ (φ k) (τ, y) - Φ (τ, y)‖ₑ ^ (2 : ℝ))
            atTop (nhds 0)) ∧
        (∀ᵐ τ : ℝ, τ ∈ Ioc (0 : ℝ) P →
          Tendsto (fun k => ∫⁻ y : Space, ‖D (φ k) (τ, y) - F (τ, y)‖ₑ ^ (2 : ℝ))
            atTop (nhds 0))

/-- (2) Periodic transfer of slice `L²` limits from one period to all `τ` (source 1334-1337).
For a.e.-periodic `g k`, `∀ᵐ x, g k (x.1+P, x.2) = g k x`, `Measure.ae_ae_of_ae_prod` gives
`∀ᵐ τ, ∀ᵐ y, g k (τ+P, y) = g k (τ, y)`; with `ae_all_iff` over `k` and over translates
`τ ↦ τ + m P` (`m : ℤ`, null sets are translation invariant, `measure_preimage_add_right`) the slice
integrals satisfy `s_k (τ + m P) = s_k τ` a.e. (`lintegral_congr_ae`); every `τ` is
`τ₀ + m P` with `τ₀ ∈ (0,P]`, `m = ⌈τ/P⌉ - 1`. -/
def SelAeSliceLimits : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℕ → ℝ × Space → CVec3,
    (∀ k, ∀ᵐ x : ℝ × Space, g k (x.1 + P, x.2) = g k x) →
    (∀ᵐ τ : ℝ, τ ∈ Ioc (0 : ℝ) P →
      Tendsto (fun k => ∫⁻ y : Space, ‖g k (τ, y)‖ₑ ^ (2 : ℝ)) atTop (nhds 0)) →
    ∀ᵐ τ : ℝ, Tendsto (fun k => ∫⁻ y : Space, ‖g k (τ, y)‖ₑ ^ (2 : ℝ)) atTop (nhds 0)

/-- (3) Slices of a member of `Y_2` are measurable with finite `L²` norm, for a.e. `τ ∈ ℝ`
(source 1341-1344).  Measurability: `AEStronglyMeasurable.prodMk_left`.  Finiteness on `(0,P]`: the
period integral `∫⁻_{(0,P]} ∫⁻_y ‖g‖ₑ²` is finite (`IsInYr.finite`, `P⁻¹` positive) so the inner
integral is finite a.e. (`ae_lt_top'`, slice integral a.e.-measurable); then transfer to all `τ` by
periodicity as in `SelAeSliceLimits` (finiteness and a.e.-strong measurability of a slice are
invariant under a.e. equality of slices). -/
def SelAeSliceL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
    ∀ᵐ τ : ℝ, AEStronglyMeasurable (fun y : Space => g (τ, y)) volume ∧
      ∫⁻ y : Space, ‖g (τ, y)‖ₑ ^ (2 : ℝ) < ⊤

/-- (4) Passage to the limit in the weak-derivative identity on one fixed slice (source 1351-1362):
for each smooth compactly supported `θ`, `‖∫ (ψ k - φ0) · ∂ⱼθ‖ ≤ ‖ψ k - φ0‖_{L²} ‖∂ⱼθ‖_{L²}` and
`‖∫ (d k - f0) · θ‖ ≤ ‖d k - f0‖_{L²} ‖θ‖_{L²}` (Cauchy–Schwarz, `integral_mul_le_Lp_mul_Lq`-type
or `MeasureTheory.L2.inner_le`-type bounds; `θ`, `∂ⱼθ` are continuous with compact support hence in
`L²`; the integrands are integrable since `ψ k`, `φ0`, `d k`, `f0` are `L²`), so both sides of
`-(∫ ψ k ∂ⱼθ) = ∫ d k θ` converge to those for `(φ0, f0)`; uniqueness of limits. -/
def SelWeakPass : Prop :=
  ∀ (ψ d : ℕ → Space → CVec3) (φ0 f0 : Space → CVec3) (j : Fin 3),
    (∀ k, AEStronglyMeasurable (ψ k) volume ∧ ∫⁻ y : Space, ‖ψ k y‖ₑ ^ (2 : ℝ) < ⊤) →
    (∀ k, AEStronglyMeasurable (d k) volume ∧ ∫⁻ y : Space, ‖d k y‖ₑ ^ (2 : ℝ) < ⊤) →
    (AEStronglyMeasurable φ0 volume ∧ ∫⁻ y : Space, ‖φ0 y‖ₑ ^ (2 : ℝ) < ⊤) →
    (AEStronglyMeasurable f0 volume ∧ ∫⁻ y : Space, ‖f0 y‖ₑ ^ (2 : ℝ) < ⊤) →
    Tendsto (fun k => ∫⁻ y : Space, ‖ψ k y - φ0 y‖ₑ ^ (2 : ℝ)) atTop (nhds 0) →
    Tendsto (fun k => ∫⁻ y : Space, ‖d k y - f0 y‖ₑ ^ (2 : ℝ)) atTop (nhds 0) →
    (∀ k, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      -(∫ y : Space, ∑ i : Fin 3,
          ψ k y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        = ∫ y : Space, ∑ i : Fin 3, d k y i * θ y i) →
    ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      -(∫ y : Space, ∑ i : Fin 3,
          φ0 y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        = ∫ y : Space, ∑ i : Fin 3, f0 y i * θ y i

theorem selLimit_of (h1 : SelSubseq) (h2 : SelAeSliceLimits) (h3 : SelAeSliceL2)
    (h4 : SelWeakPass) : SelLimit := by
  intro P hP Φ F Ψ D j hΦ hF hΨ hD hΨΦ hDF hwk
  obtain ⟨φ, _, hs1, hs2⟩ := h1 P hP Φ F Ψ D hΦ hF hΨ hD hΨΦ hDF
  have hg1 : ∀ᵐ τ : ℝ, Tendsto
      (fun k => ∫⁻ y : Space, ‖Ψ (φ k) (τ, y) - Φ (τ, y)‖ₑ ^ (2 : ℝ)) atTop (nhds 0) :=
    h2 P hP (fun k x => Ψ (φ k) x - Φ x)
      (fun k => by
        filter_upwards [(hΨ (φ k)).periodic, hΦ.periodic] with x hx1 hx2
        simp [hx1, hx2]) hs1
  have hg2 : ∀ᵐ τ : ℝ, Tendsto
      (fun k => ∫⁻ y : Space, ‖D (φ k) (τ, y) - F (τ, y)‖ₑ ^ (2 : ℝ)) atTop (nhds 0) :=
    h2 P hP (fun k x => D (φ k) x - F x)
      (fun k => by
        filter_upwards [(hD (φ k)).periodic, hF.periodic] with x hx1 hx2
        simp [hx1, hx2]) hs2
  have a1 := ae_all_iff.2 (fun n => h3 P hP (Ψ n) (hΨ n))
  have a2 := ae_all_iff.2 (fun n => h3 P hP (D n) (hD n))
  unfold SliceWeakD at hwk ⊢
  have a5 := ae_all_iff.2 hwk
  filter_upwards [hg1, hg2, a1, a2, h3 P hP Φ hΦ, h3 P hP F hF, a5]
    with τ t1 t2 b1 b2 b3 b4 b5
  intro θ hθ hc
  exact h4 (fun k y => Ψ (φ k) (τ, y)) (fun k y => D (φ k) (τ, y))
    (fun y => Φ (τ, y)) (fun y => F (τ, y)) j (fun k => b1 (φ k)) (fun k => b2 (φ k)) b3 b4
    t1 t2 (fun k θ hθ hc => b5 (φ k) θ hθ hc) θ hθ hc

end UnforcedLeray.Short.PartIIIb.Concrete
