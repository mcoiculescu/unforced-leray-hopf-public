import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3

/-!
# Decomposition of `VtvTimeIntegrable` (source 4610, 3511-3514)

Source of record: `the November 2 reference manuscript`
(lines 4610 for the integrated Duhamel identity, 3511-3514 and 4464-4467 for the pairing).

For a stream test `η` with age band `[s₁,s₂]`, `s₁ > 0`, both `Y(s,∂_sη(s))` and `R(s,η(s))`
vanish for `s ∉ [s₁,s₂]`, so integrability on `(0,∞)` is integrability on `Icc s₁ s₂`.  There
both are bounded by `C · (dB(s) + dF(s))`, `dB(s) = ∫_cell (|b₀|+|b₁|)(s,·)`, `dF` likewise for `f`,
with `dB + dF` integrable on the band by `energyLoc` and the band-`L²` hypothesis on `f`.  The
bound: `⟨ω(s),ψ⟩ = ∫ b₀∂_ηψ - b₁∂_qψ` for a cylinder test `ψ` (third clause of `IsBiotSavart`),
applied to `ψ = ∂_sη(s)` (for `Y`), and to `ψ = νΔη+v·∇η` (for the `ω` part of `flowIntegrand`);
the `g` part is `∫ f₀∂_ηη - f₁∂_qη` (curl clause of `VtvHyps`); the last part of `flowIntegrand` is
bounded by `‖∇E‖_∞ ‖η‖_∞ dB`.

Leaves (Props below): `VtvTimeSupport`, `VtvBandL1`, `VtvFSlice`, `VtvTestBounds`,
`VtvYPairBound`, `VtvRPairBound`, `VtvYRMeas`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel lapP)

/-- The finite-measure box `cell c ∩ {|η| ≤ R}` (the cell itself has infinite measure; `b(s,·)`,
`f(s,·)` are only `L²` on it, so `L¹` norms are taken on boxes, where the tests live). -/
def vtvBox (c R : ℝ) : Set (ℝ × ℝ) := B0579.cell c ∩ {x | |x.2| ≤ R}

/-- `dB_R(s) = ∫_{box} (‖b₀‖+‖b₁‖)(s,·)`. -/
def vtvDB (c R : ℝ) (b : Chart → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in vtvBox c R, (‖b (s, x) 0‖ + ‖b (s, x) 1‖)

/-- `dF_R(s) = ∫_{box} (‖f₀‖+‖f₁‖)(s,·)`. -/
def vtvDF (c R : ℝ) (f : Chart → Fin 2 → ℂ) (s : ℝ) : ℝ :=
  ∫ x in vtvBox c R, (‖f (s, x) 0‖ + ‖f (s, x) 1‖)

/-- The test `νΔφ + v·∇φ` paired with `ω` inside `flowIntegrand` (source 3420-3426). -/
def vtvFlowTest {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (φ : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ :=
  fun x => ν * lapP φ x + (tr.v s x 0 * B0579.pd 0 φ x + tr.v s x 1 * B0579.pd 1 φ x)

/-- **Band support** (stream test `η` with `η = 0` for `s < s₁` or `s > s₂`): both integrands vanish
outside `[s₁,s₂]` (`∂_sη(s) = 0` there as `η` vanishes on an open set of ages; `R(s,0) = 0`). -/
def VtvTimeSupport : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ ∀ s, (s < s₁ ∨ s₂ < s) →
        vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s) = 0 ∧
        vtvR μ tr ω g b s (η s) = 0

/-- **`L¹` of the densities on a band** (`energyLoc` gives `b ∈ L²(Icc s₁ s₂ × cell)`, hence `L¹`
on a finite-measure set, and Fubini gives integrability of the slice integral; the same for `f`
from the sixth clause of `VtvHyps`). -/
def VtvBandL1 : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ s₁ s₂ R : ℝ, 0 < s₁ →
      IntegrableOn (fun s => vtvDB c R b s + vtvDF c R f s) (Icc s₁ s₂)

/-- **Almost every slice of `f` is integrable on every box** (Fubini from the band-`L²` clause: a.e.
slice is `L²` on the cell, hence `L¹` on the finite-measure boxes). -/
def VtvFSlice : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ s₁ s₂ : ℝ, 0 < s₁ →
      ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), ∀ (R : ℝ) (i : Fin 2),
        IntegrableOn (fun x => f (s, x) i) (vtvBox c R)

/-- **Uniform test bounds** (BUC train: all derivatives of `v` bounded on `[0,s₂]`; joint
smoothness of `η` and its support in `[s₁,s₂] × {|η| ≤ R}`, periodicity of `η`, `v`): for `s` in the
band, `∂_sη(s)` and `νΔη(s)+v·∇η(s)` are cylinder tests and all of `|∂_sη|, |η|, |∇∂_sη|,
|∇(νΔη+v·∇η)|, |∇E|` (`E = curl v`) are bounded by one constant `K`.  The period is positive
(source 246-252: `c = ν^{-ρ} > 0`; the second clause of `VtvHyps`). -/
def VtvTestBounds : Prop :=
  ∀ (ν c : ℝ), 0 < c → ∀ (tr : UnforcedLeray.B0140.TrainSol ν c),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η → ∀ s₁ s₂ : ℝ, 0 < s₁ →
      ∃ K R : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc s₁ s₂,
        B0579.IsCylTest c (fun x => deriv (fun s' => η s' x) s) ∧
        B0579.IsCylTest c (vtvFlowTest tr s (η s)) ∧
        (∀ x j, |B0579.pd j (fun x => deriv (fun s' => η s' x) s) x| ≤ K) ∧
        (∀ x, |η s x| ≤ K) ∧
        (∀ x j, |B0579.pd j (η s) x| ≤ K) ∧
        (∀ x j, |B0579.pd j (vtvFlowTest tr s (η s)) x| ≤ K) ∧
        (∀ x j, |B0579.pd j (UnforcedLeray.B0238.Ec tr s) x| ≤ K) ∧
        (∀ x : ℝ × ℝ, R < |x.2| → deriv (fun s' => η s' x) s = 0) ∧
        (∀ x : ℝ × ℝ, R < |x.2| → η s x = 0)

/-- **Pairing bound for `Y`** (third clause of `IsBiotSavart`): for `s > 0`, a cylinder test `φ`
vanishing for `|η| > R` with `|∇φ| ≤ K`: `‖Y(s,φ)‖ ≤ ‖s^μ‖ K dB_R(s)`.  (The integrand
`b₀∂_ηφ - b₁∂_qφ` vanishes outside the box, `∂φ` vanishes on the open set where `φ` does
(`pd_vanish`), and `b(s,·) ∈ L²(cell)` is `L¹` on the finite-measure box.) -/
def VtvYPairBound : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ (R s : ℝ), 0 < s → ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
      (∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) →
      ∀ K : ℝ, (∀ x j, |B0579.pd j φ x| ≤ K) →
        ‖vtvY μ c ω s φ‖ ≤ ‖(s : ℂ) ^ (μ : ℂ)‖ * K * vtvDB c R b s

/-- **Pairing bound for `R`**: for `s > 0` with the slices `f(s,·)` integrable on the box, `φ` a
cylinder test vanishing for `|η| > R` with `νΔφ+v·∇φ` a cylinder test (it vanishes for `|η| > R`
too, `vtvFlowTest_vanish`), and `|φ|, |∇φ|, |∇(νΔφ+v·∇φ)|, |∇E| ≤ K`:
`‖R(s,φ)‖ ≤ ‖s^μ‖ (K+K²)(dB_R(s)+dF_R(s))`.  Route: `∫ g φ = ∫ f₀∂_ηφ - f₁∂_qφ` (curl clause of
`VtvHyps`); `∫ ω·w = ∫ b₀∂_ηw - b₁∂_qw` (`IsBiotSavart`, `w = νΔφ+v·∇φ`); the integrand
splitting uses the last clause of `VtvHyps` for `ω·w` and `b ∈ L²(cell) ⊂ L¹(cell)`. -/
def VtvRPairBound : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ (R s : ℝ), 0 < s →
      (∀ i : Fin 2, IntegrableOn (fun x => f (s, x) i) (vtvBox c R)) →
      ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → B0579.IsCylTest c (vtvFlowTest tr s φ) →
      (∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) →
      ∀ K : ℝ, (∀ x, |φ x| ≤ K) → (∀ x j, |B0579.pd j φ x| ≤ K) →
        (∀ x j, |B0579.pd j (vtvFlowTest tr s φ) x| ≤ K) →
        (∀ x j, |B0579.pd j (UnforcedLeray.B0238.Ec tr s) x| ≤ K) →
        ‖vtvR μ tr ω g b s φ‖ ≤ ‖(s : ℂ) ^ (μ : ℂ)‖ * (K + K * K) * (vtvDB c R b s + vtvDF c R f s)

/-- **Measurability in the age** of the two integrands on the band (through
`⟨ω(s),ψ_s⟩ = ∫ b·∇^⊥ψ_s` for `s > 0`, joint measurability of `b`, joint continuity of the test
derivatives, `Measurable.integral_prod_right'`-type measurability of parametric integrals). -/
def VtvYRMeas : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η → ∀ s₁ s₂ : ℝ, 0 < s₁ →
      AEStronglyMeasurable (fun s => vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s))
        (volume.restrict (Icc s₁ s₂)) ∧
      AEStronglyMeasurable (fun s => vtvR μ tr ω g b s (η s)) (volume.restrict (Icc s₁ s₂))

/-- Compact bound on the complex power. -/
theorem vtv_pow_bound (μ s₁ s₂ : ℝ) (h : 0 < s₁) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ s ∈ Icc s₁ s₂, ‖(s : ℂ) ^ (μ : ℂ)‖ ≤ P := by
  have hc : ContinuousOn (fun s : ℝ => (s : ℂ) ^ (μ : ℂ)) (Icc s₁ s₂) := by
    refine ContinuousOn.cpow (Complex.continuous_ofReal.continuousOn) continuousOn_const ?_
    intro s hs
    exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le h hs.1)
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max P 0, le_max_right _ _, fun s hs => (hP s hs).trans (le_max_left _ _)⟩

/-- Y integrable on a band from the leaves. -/
theorem vtvYBand_of (hL1 : VtvBandL1) (hT : VtvTestBounds) (hY : VtvYPairBound)
    (hM : VtvYRMeas) :
    ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η → ∀ s₁ s₂ : ℝ, 0 < s₁ →
      IntegrableOn (fun s => vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s)) (Icc s₁ s₂) := by
  intro ν c μ tr ω g b G f H η hη s₁ s₂ hs₁
  have hBUC := H.2.2.1
  obtain ⟨K, R, hK0, hK⟩ := hT ν c H.2.1 tr hBUC η hη s₁ s₂ hs₁
  obtain ⟨P, hP0, hP⟩ := vtv_pow_bound μ s₁ s₂ hs₁
  have hd := hL1 ν c μ tr ω g b G f H s₁ s₂ R hs₁
  have hBnn : ∀ s, 0 ≤ vtvDB c R b s := fun s =>
    integral_nonneg fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hFnn : ∀ s, 0 ≤ vtvDF c R f s := fun s =>
    integral_nonneg fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine Integrable.mono' (hd.const_mul (P * K)) (hM ν c μ tr ω g b G f H η hη s₁ s₂ hs₁).1 ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
  obtain ⟨h1, -, h3, -, -, -, -, hz, -⟩ := hK s hs
  have := hY ν c μ tr ω g b G f H R s hs0 _ h1 hz K h3
  calc ‖vtvY μ c ω s (fun x => deriv (fun s' => η s' x) s)‖
      ≤ ‖(s : ℂ) ^ (μ : ℂ)‖ * K * vtvDB c R b s := this
    _ ≤ P * K * vtvDB c R b s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hP s hs) hK0) (hBnn s)
    _ ≤ P * K * (vtvDB c R b s + vtvDF c R f s) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hFnn s)) (mul_nonneg hP0 hK0)

/-- R integrable on a band from the leaves. -/
theorem vtvRBand_of (hL1 : VtvBandL1) (hF : VtvFSlice) (hT : VtvTestBounds)
    (hR : VtvRPairBound) (hM : VtvYRMeas) :
    ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η → ∀ s₁ s₂ : ℝ, 0 < s₁ →
      IntegrableOn (fun s => vtvR μ tr ω g b s (η s)) (Icc s₁ s₂) := by
  intro ν c μ tr ω g b G f H η hη s₁ s₂ hs₁
  have hBUC := H.2.2.1
  obtain ⟨K, R, hK0, hK⟩ := hT ν c H.2.1 tr hBUC η hη s₁ s₂ hs₁
  obtain ⟨P, hP0, hP⟩ := vtv_pow_bound μ s₁ s₂ hs₁
  have hd := hL1 ν c μ tr ω g b G f H s₁ s₂ R hs₁
  have hBnn : ∀ s, 0 ≤ vtvDB c R b s := fun s =>
    integral_nonneg fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hFnn : ∀ s, 0 ≤ vtvDF c R f s := fun s =>
    integral_nonneg fun x => add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine Integrable.mono' (hd.const_mul (P * (K + K * K)))
    (hM ν c μ tr ω g b G f H η hη s₁ s₂ hs₁).2 ?_
  have hsl := hF ν c μ tr ω g b G f H s₁ s₂ hs₁
  filter_upwards [hsl, ae_restrict_mem measurableSet_Icc] with s hsl hs
  have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
  obtain ⟨-, h2, -, h4, h3, h5, h6, -, hz⟩ := hK s hs
  have hηc : B0579.IsCylTest c (η s) := hη.2.1 s
  have := hR ν c μ tr ω g b G f H R s hs0 (hsl R) (η s) hηc h2 hz K h4 h3 h5 h6
  have hKK : 0 ≤ K + K * K := by positivity
  calc ‖vtvR μ tr ω g b s (η s)‖
      ≤ ‖(s : ℂ) ^ (μ : ℂ)‖ * (K + K * K) * (vtvDB c R b s + vtvDF c R f s) := this
    _ ≤ P * (K + K * K) * (vtvDB c R b s + vtvDF c R f s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hP s hs) hKK)
          (add_nonneg (hBnn s) (hFnn s))

/-- Reduction of `VtvTimeIntegrable` to the leaves. -/
theorem vtvTimeIntegrable_of (h0 : VtvTimeSupport) (hL1 : VtvBandL1) (hF : VtvFSlice)
    (hT : VtvTestBounds) (hY : VtvYPairBound) (hR : VtvRPairBound) (hM : VtvYRMeas) :
    VtvTimeIntegrable := by
  intro ν c μ tr ω g b G f H η hη
  obtain ⟨s₁, s₂, hs₁, hz⟩ := h0 ν c μ tr ω g b G f H η hη
  have hYb := vtvYBand_of hL1 hT hY hM ν c μ tr ω g b G f H η hη s₁ s₂ hs₁
  have hRb := vtvRBand_of hL1 hF hT hR hM ν c μ tr ω g b G f H η hη s₁ s₂ hs₁
  have key : ∀ {F : ℝ → ℂ}, IntegrableOn F (Icc s₁ s₂) → (∀ s, (s < s₁ ∨ s₂ < s) → F s = 0) →
      IntegrableOn F (Ioi (0 : ℝ)) := by
    intro F hF1 hF0
    refine hF1.of_forall_diff_eq_zero measurableSet_Ioi fun s hs => hF0 s ?_
    have : ¬ (s₁ ≤ s ∧ s ≤ s₂) := fun h => hs.2 h
    by_contra hcon
    push_neg at hcon
    exact this ⟨hcon.1, hcon.2⟩
  exact ⟨key hYb fun s h => (hz s h).1, key hRb fun s h => (hz s h).2⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
