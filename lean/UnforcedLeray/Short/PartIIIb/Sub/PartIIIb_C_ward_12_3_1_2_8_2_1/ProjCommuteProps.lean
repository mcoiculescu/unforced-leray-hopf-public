import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1.ProjSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1`: commutation of `L₀ᵗ` with the Leray projection

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  This file replaces the ill-posed `L0TProjCommute` (which applied
`L0T` to the `L^p` representative `projTest P Φ`) by the statement `L0TProjSmoothCommute` over the
smooth representative `projSmooth Φ = Φ + ∇π` (`ProjSmooth.lean`).  The statement is reduced to
three Prop lemmas: `L0TGradAdd` (`L₀ᵗ` commutes with adding a gradient, up to a gradient),
`ProjGradSliceTest` (the resulting gradient is an `L^{q₀'}` slice test) and `GradPairingVanish`
(it pairs to zero with solenoidal `v`, a cutoff-limit argument for non-compact gradients).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (IsSolTest)

/-- The scalar potential of `L₀ᵗ∇ψ`:
`L₀ᵗ(∇ψ) = ∇(-∂_τψ + ½ y·∇ψ + ½ψ - νΔψ)`, since `y·∇(∂ₖψ) = ∂ₖ(y·∇ψ) - ∂ₖψ`,
`driftT Φ = -∂_τΦ + ½ y·∇Φ + (3/2)Φ` and `Δ`, `∂_τ` commute with `∂ₖ`. -/
def L0Tscal (ν : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ) : ℝ × UnforcedLeray.Space → ℂ :=
  fun p => -dτ ψ p + (1 / 2 : ℝ) • radialT ψ p + (1 / 2 : ℝ) • ψ p - ν • lapT ψ p

/-- **(a) `L₀ᵗ` and gradients.**  For smooth `Φ` and smooth scalar `ψ`:
`L₀ᵗ(Φ + ∇ψ) = L₀ᵗΦ + ∇(L0Tscal ν ψ)` (linearity of `L₀ᵗ` on smooth fields, and the commutation
`L₀ᵗ∇ψ = ∇ L0Tscal ν ψ` of the docstring of `L0Tscal`; needs symmetry of second derivatives). -/
def L0TGradAdd : Prop :=
  ∀ (ν : ℝ) (Φ : ℝ × UnforcedLeray.Space → CVec3) (ψ : ℝ × UnforcedLeray.Space → ℂ),
    ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ ψ →
    L0T ν (Φ + gradT ψ) = L0T ν Φ + gradT (L0Tscal ν ψ)

/-- **(b) The correction gradient is an `L^{q₀'}` slice test.**  `π = projPot Φ` is the Newton
potential of `div Φ` (zero mean, so `π = O(|y|^{-2})`, `∇π = O(|y|^{-3})`, and every derivative
gains one more power); hence `∇ L0Tscal ν π = L₀ᵗ(𝔓Φ) - L₀ᵗΦ` is smooth, `P`-periodic and
`O(|y|^{-3})`, which lies in `L^{11/7}(ℝ³)` since `3 · 11/7 > 3`; slice-continuity into `L^{11/7}`
follows by dominated convergence. -/
def ProjGradSliceTest : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Φ →
    IsSliceTest P (conjExp UnforcedLeray.B0412.q0E) (gradT (L0Tscal ν (projPot Φ)))

/-- **(c) Pairing of a non-compact correction gradient with solenoidal `v` vanishes.**  With
`σ = L0Tscal ν (projPot Φ)` (`σ = O(|y|^{-2})`, `∇σ = O(|y|^{-3})`): for `χ_R` a cutoff,
`⟪∇(χ_R σ), v⟫ = 0` by `IsPhaseSolenoidal` (compactly supported scalar), and
`∇(χ_Rσ) → ∇σ` in `L^{11/7}` (tail of `|y|^{-3}`) while the cross term `σ∇χ_R = O(R^{-3})` on a
shell of volume `R³` has `L^{11/7}` norm `O(R^{-3+21/11}) → 0`.  Compare
`pairF_projectedNewtonCorrection_eq_zero_of_phaseSolenoidal` (same argument for `∇π` itself). -/
def GradPairingVanish : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Φ →
    ∀ v : Yq P UnforcedLeray.B0412.q0E, IsPhaseSolenoidal v →
      phasePair P UnforcedLeray.B0412.q0E (gradT (L0Tscal ν (projPot Φ))) v = 0

/-- **Commutation of `L₀ᵗ` with the Leray projection on solenoidal pairings**, over the smooth
representative `projSmooth Φ` of `𝔓Φ` (a.e. equal to `projTest P Φ` slice by slice,
`projSmooth_slice_ae`): `⟪L₀ᵗΦ, v⟫ = ⟪L₀ᵗ(𝔓Φ), v⟫` for solenoidal `v`. -/
def L0TProjSmoothCommute : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ v : Yq P UnforcedLeray.B0412.q0E,
    v ∈ Ysigma P UnforcedLeray.B0412.q0E →
    ∀ Φ : ℝ × UnforcedLeray.Space → CVec3, IsPhaseTest P Φ →
      phasePair P UnforcedLeray.B0412.q0E (L0T ν Φ) v =
        phasePair P UnforcedLeray.B0412.q0E (L0T ν (projSmooth Φ)) v

theorem l0TProjSmoothCommute_of (ha : L0TGradAdd) (hb : ProjGradSliceTest)
    (hc : GradPairingVanish) : L0TProjSmoothCommute := by
  intro P _ ν _ v hv Φ hΦ
  have hsm : L0T ν (projSmooth Φ) = L0T ν Φ + gradT (L0Tscal ν (projPot Φ)) :=
    ha ν Φ (projPot Φ) hΦ.smooth (contDiff_projPot hΦ)
  have hA : IsSliceTest P (conjExp UnforcedLeray.B0412.q0E) (L0T ν Φ) :=
    (isPhaseTest_L0T hΦ ν).isSliceTest _
  have hB := hb P ν Φ hΦ
  rw [hsm]
  show _ = phasePairing P _ (testElem P _ (L0T ν Φ + gradT (L0Tscal ν (projPot Φ)))) v
  rw [testElem_add hA hB, map_add, add_apply]
  have h0 := hc P ν Φ hΦ v hv
  have h0' : phasePairing P _ (testElem P _ (gradT (L0Tscal ν (projPot Φ)))) v = 0 := h0
  rw [h0', add_zero]
  rfl

/-! ### Splitting `L0TGradAdd`, `ProjGradSliceTest`, `GradPairingVanish` -/

/-- `L₀ᵗ` is additive on smooth fields (`dτ`, `dy`, `lapT`, `radialT` are linear on `C¹`/`C²`
functions: `fderiv_add`). -/
def L0TAddSmooth : Prop :=
  ∀ (ν : ℝ) (A B : ℝ × UnforcedLeray.Space → CVec3), ContDiff ℝ ∞ A → ContDiff ℝ ∞ B →
    L0T ν (A + B) = L0T ν A + L0T ν B

/-- `L₀ᵗ∇ψ = ∇(L0Tscal ν ψ)` for smooth scalar `ψ` (symmetry of second derivatives,
`y·∇(∂ₖψ) = ∂ₖ(y·∇ψ) - ∂ₖψ`, `∂ₖΔ = Δ∂ₖ`, `∂ₖ∂_τ = ∂_τ∂ₖ`). -/
def L0TGradComm : Prop :=
  ∀ (ν : ℝ) (ψ : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ ψ →
    L0T ν (gradT ψ) = gradT (L0Tscal ν ψ)

theorem l0TGradAdd_of (h1 : L0TAddSmooth) (h2 : L0TGradComm) : L0TGradAdd := by
  intro ν Φ ψ hΦ hψ
  rw [h1 ν Φ (gradT ψ) hΦ (UnforcedLeray.Short.PartIIIb.Concrete.contDiff_gradT hψ), h2 ν ψ hψ]

/-- **Decay and regularity of the correction potential.**  For a phase test `Φ`, the scalar
`σ = L0Tscal ν (projPot Φ)` is smooth, `P`-periodic, and uniformly in `τ`:
`|σ| ≤ C (1+|y|)^{-2}`, `|∇σ| ≤ C (1+|y|)^{-3}`.  (`π = projPot Φ` is the Newton potential of
`-div Φ` with `∫ div Φ = 0`, so `π = O(|y|^{-2})`, `∇π = O(|y|^{-3})`, `∇²π = O(|y|^{-4})`;
`σ` combines `∂_τπ`, `½ y·∇π`, `½π`, `νΔπ`; `∂_τ` commutes with the Newton convolution.) -/
def SigmaDecay : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (Φ : ℝ × UnforcedLeray.Space → CVec3), IsPhaseTest P Φ →
    ContDiff ℝ ∞ (L0Tscal ν (projPot Φ)) ∧
    (∀ τ y, L0Tscal ν (projPot Φ) (τ + P, y) = L0Tscal ν (projPot Φ) (τ, y)) ∧
    ∃ C : ℝ, ∀ τ y, ‖L0Tscal ν (projPot Φ) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) ∧
      ‖gradT (L0Tscal ν (projPot Φ)) (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-3 : ℝ)

/-- **General cutoff-limit lemma.**  A smooth `P`-periodic scalar `σ` with `|σ| ≤ C(1+|y|)^{-2}`
and `|∇σ| ≤ C(1+|y|)^{-3}` has `∇σ` an `L^{q₀'}` slice test (`3 · 11/7 > 3`), and
`⟪∇σ, v⟫ = 0` for every `IsPhaseSolenoidal v ∈ Y_{q₀}`: with `χ_R` the cutoff,
`⟪∇(χ_Rσ), v⟫ = 0` (compactly supported scalar), `χ_R∇σ → ∇σ` in `L^{11/7}` (dominated
convergence), and `σ∇χ_R = O(R^{-3})` on a shell of volume `R³` has `L^{11/7}` norm
`O(R^{-3+21/11}) → 0`; then `phasePair` is continuous (`Hölder`).  Compare
`pairF_projectedNewtonCorrection_eq_zero_of_phaseSolenoidal` (same argument for `∇π`). -/
def GradPairingGeneral : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (σ : ℝ × UnforcedLeray.Space → ℂ), ContDiff ℝ ∞ σ →
    (∀ τ y, σ (τ + P, y) = σ (τ, y)) →
    (∃ C : ℝ, ∀ τ y, ‖σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) ∧
      ‖gradT σ (τ, y)‖ ≤ C * (1 + ‖y‖) ^ (-3 : ℝ)) →
    IsSliceTest P (conjExp UnforcedLeray.B0412.q0E) (gradT σ) ∧
    ∀ v : Yq P UnforcedLeray.B0412.q0E, IsPhaseSolenoidal v →
      phasePair P UnforcedLeray.B0412.q0E (gradT σ) v = 0

theorem projGradSliceTest_of (hd : SigmaDecay) (hg : GradPairingGeneral) : ProjGradSliceTest := by
  intro P _ ν Φ hΦ
  obtain ⟨h1, h2, h3⟩ := hd P ν Φ hΦ
  exact (hg P _ h1 h2 h3).1

theorem gradPairingVanish_of (hd : SigmaDecay) (hg : GradPairingGeneral) : GradPairingVanish := by
  intro P _ ν Φ hΦ v hv
  obtain ⟨h1, h2, h3⟩ := hd P ν Φ hΦ
  exact (hg P _ h1 h2 h3).2 v hv

end UnforcedLeray.Short.PartIIIb.Concrete
