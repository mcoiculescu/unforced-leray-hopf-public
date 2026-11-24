import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3.BandVanish
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4.VtvDerivCyl

/-!
# Decomposition of `VtvTestBounds` (source 270-288, 4610)

Source of record: `the November 2 reference manuscript`.

Four leaves: `VtvEtaJet` (compactness: jets of a stream test are bounded on an age band),
`VtvFlowCyl` (`νΔφ + v·∇φ` is a cylinder test: smoothness of `v(s)` for `s > 0`, periodicity,
band), `VtvFlowJet` (the third-order jet bound of `νΔφ+v·∇φ` linear in the jet of `φ`, from the
BUC bounds on `v`), `VtvEcJet` (`∇E`, `E = curl v`, bounded by the order-2 BUC bound).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Jets of a stream test** (joint smoothness, support in `[a₁,a₂] × {|η| ≤ R}`, periodicity in
`q` reduce to a compact set): on any age interval `[s₁,s₂]`, `∂_sη(s)`, `η(s)` and the derivatives
of `η(s)` up to order `3` are bounded by one constant.  The period is positive (source 246-252:
`c = ν^{-ρ} > 0`); for `c = 0` periodicity is vacuous and the bound fails. -/
def VtvEtaJet : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (η : ℝ → ℝ × ℝ → ℝ), IsStreamTest c η → ∀ s₁ s₂ : ℝ, ∃ K : ℝ,
    ∀ s ∈ Icc s₁ s₂,
    (∀ x j, |B0579.pd j (fun x => deriv (fun s' => η s' x) s) x| ≤ K) ∧
    (∀ x j, |B0579.pd j (η s) x| ≤ K) ∧
    (∀ x, ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k (η s) x‖ ≤ K)

/-- **`νΔφ + v·∇φ` is a cylinder test** for `s > 0` (smooth since `tr.v s` is smooth by
`IsTrain.smooth_v` on the open set `Ioi 0 ×ˢ univ`, periodic by `periodic_v`, vanishing in the
band of `φ`). -/
def VtvFlowCyl : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ), 0 < s →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → B0579.IsCylTest c (vtvFlowTest tr s φ)

/-- **Gradient of `νΔφ+v·∇φ` from the jet of `φ`** (BUC train: `v(s)` and its derivatives of
orders `≤ 1`, `2` bounded on `[s₁,s₂]`): `∂_j(νΔφ + v·∇φ)` is a combination of `∂³φ`, `∂²φ`, `∂φ`
with coefficients `ν`, `v`, `∇v`, so `|∂_j(·)| ≤ A M` when all derivatives of `φ` of orders `≤ 3`
are bounded by `M`. -/
def VtvFlowJet : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → ∃ A : ℝ, 0 ≤ A ∧ ∀ s ∈ Icc s₁ s₂, ∀ φ : ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ φ → ∀ M : ℝ, (∀ x, ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k φ x‖ ≤ M) →
        ∀ x j, |B0579.pd j (vtvFlowTest tr s φ) x| ≤ A * M

/-- **`∇E` bounded** (`E = Ec tr s = curl (tr.v s)`, so `∂_jE` is a combination of second
derivatives of `v(s)`; `IsBUCTrain` at order `2`, `s ∈ [s₁,s₂]`, `s₁ > 0`). -/
def VtvEcJet : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → ∃ K : ℝ, ∀ s ∈ Icc s₁ s₂, ∀ x j,
      |B0579.pd j (UnforcedLeray.B0238.Ec tr s) x| ≤ K

theorem vtvTestBounds_of (hA : VtvEtaJet) (hB : VtvFlowCyl) (hC : VtvFlowJet) (hD : VtvEcJet) :
    VtvTestBounds := by
  intro ν c hc tr hBUC η hη s₁ s₂ hs₁
  obtain ⟨KA, hKA⟩ := hA c hc η hη s₁ s₂
  obtain ⟨A, hA0, hAb⟩ := hC ν c tr hBUC s₁ s₂ hs₁
  obtain ⟨KD, hKD⟩ := hD ν c tr hBUC s₁ s₂ hs₁
  obtain ⟨_a, _b, R, _h, hRz⟩ := hη.2.2
  have hRη : ∀ s (x : ℝ × ℝ), R < |x.2| → η s x = 0 := fun s x hx => hRz s x (Or.inr (Or.inr hx))
  refine ⟨max (max KA (A * KA)) (max KD 0), R,
    le_trans (le_refl _) (le_max_right _ _) |>.trans' (le_max_right _ _), ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
  obtain ⟨h1, h2, h3⟩ := hKA s hs
  have hcyl : B0579.IsCylTest c (η s) := hη.2.1 s
  have hflowcyl := hB ν c tr s hs0 (η s) hcyl
  have hsm : ContDiff ℝ ∞ (η s) := hcyl.smooth
  have hflow := hAb s hs (η s) hsm KA h3
  refine ⟨vtvDerivCyl c η hη s, hflowcyl, ?_, ?_, ?_, ?_, ?_, deriv_age_vanish hRη s,
    fun x hx => hRη s x hx⟩
  · intro x j
    exact (h1 x j).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro x
    have := h3 x 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro x j
    exact (h2 x j).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro x j
    exact (hflow x j).trans ((le_max_right _ _).trans (le_max_left _ _))
  · intro x j
    exact (hKD s hs x j).trans ((le_max_left _ _).trans (le_max_right _ _))

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
