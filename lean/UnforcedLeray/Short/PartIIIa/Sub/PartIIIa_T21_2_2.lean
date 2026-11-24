import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# Part III-a, `PartIII-a:T21/2/2`: the adjoint energy inequalities, decomposed

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(`E_0' + β_min E_1 ≤ C_b E_0`, `E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`), with the moving equation
2854-2865 and the Reynolds seam cancellation 2945-2957.

`AdjointEnergyIneqs m` is the conjunction of three statements in one common regime
(`AdjointEnergyCase`): continuity of `E_0` on `[0, Δz]` and `E_1` on `(0, Δz]` (`AdjQCont`), the
`E_0` differential inequality (`AdjQE0`) and the `E_1` differential inequality (`AdjQE1`).
`adjointEnergyIneqs_of` assembles them (constants `max`, `ν₀` `min`, `b₀` `max`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Continuity of `E_0` on `[0, Δz]` and of `E_1` on `(0, Δz]` (SP 3060-3071). -/
def AdjQCont (m ν : ℝ) (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ContinuousOn (revE0 ν (ν ^ (-2 : ℝ)) m φ s) (Icc 0 (deltaZ ν t s)) ∧
    ContinuousOn (revE1 ν (ν ^ (-2 : ℝ)) m φ s) (Ioc 0 (deltaZ ν t s))

/-- The `E_0` differential inequality `E_0' + β_min E_1 ≤ C E_0` on `(0, Δz)` (SP 3061-3066). -/
def AdjQE0 (m C ν : ℝ) (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∃ D : ℝ,
    HasDerivAt (revE0 ν (ν ^ (-2 : ℝ)) m φ s) D ζ ∧
    D + betaMin ν t * revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ ≤
      C * revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ

/-- The `E_1` differential inequality `E_1' + β_min E_2 ≤ C (E_1 + E_0)` on `(0, Δz)`
(SP 3067-3071). -/
def AdjQE1 (m C ν : ℝ) (t s : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ ζ ∈ Ioo 0 (deltaZ ν t s), ∃ D : ℝ,
    HasDerivAt (revE1 ν (ν ^ (-2 : ℝ)) m φ s) D ζ ∧
    D + betaMin ν t * revE2 ν (ν ^ (-2 : ℝ)) m φ s ζ ≤
      C * (revE1 ν (ν ^ (-2 : ℝ)) m φ s ζ + revE0 ν (ν ^ (-2 : ℝ)) m φ s ζ)

/-- The common regime of `AdjointEnergyIneqs` (SP 3060): for `b` large and `ν` small, on
`0 < s - t ≤ 1`, `θ(s) ≥ b`, for the moving adjoint of any terminal datum `G ∈ X_{-m,d_s}`,
a property `Q C ν t s φ` holds with a constant `C ≥ 0`.  The train is in the BUC class
`PartI.IsBUCTrain` (SP 270-288), as in `AdjointEnergyIneqs`. -/
def AdjointEnergyCase (m : ℝ) (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ × ℝ → ℂ) → Prop) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t s : ℝ, 0 ≤ t → t < s → s - t ≤ 1 → b ≤ clockTheta ν s →
        ∀ G : ℝ × ℝ → ℂ,
          MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
          ∀ φ : ℝ → ℝ × ℝ → ℂ,
            IsAdjointFlow ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
            Q C ν t s φ

/-- Leaf 1: continuity (needs only `IsAdjointFlow.strongCont`, `jointSmooth`, the terminal
datum; SP 3060-3071). -/
def AdjointEnergyCont (m : ℝ) : Prop :=
  AdjointEnergyCase m (fun _ ν t s φ => AdjQCont m ν t s φ)

/-- Leaf 2: the `E_0` inequality (SP 3061-3066; hypotheses `PeriodicWeightLogBounds`,
`RescaledTrainBounds m`, `AdjointLocalizedBound m`). -/
def AdjointE0Ineq (m : ℝ) : Prop :=
  AdjointEnergyCase m (fun C ν t s φ => AdjQE0 m C ν t s φ)

/-- Leaf 3: the `E_1` inequality (SP 3067-3071; same hypotheses). -/
def AdjointE1Ineq (m : ℝ) : Prop :=
  AdjointEnergyCase m (fun C ν t s φ => AdjQE1 m C ν t s φ)

theorem adjQE0_mono {m C C' ν t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (h : C ≤ C')
    (hq : AdjQE0 m C ν t s φ) : AdjQE0 m C' ν t s φ := by
  intro ζ hζ
  obtain ⟨D, hD, hle⟩ := hq ζ hζ
  refine ⟨D, hD, hle.trans ?_⟩
  exact mul_le_mul_of_nonneg_right h (adjE0_nonneg _ _ _)

theorem adjQE1_mono {m C C' ν t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ} (h : C ≤ C')
    (hq : AdjQE1 m C ν t s φ) : AdjQE1 m C' ν t s φ := by
  intro ζ hζ
  obtain ⟨D, hD, hle⟩ := hq ζ hζ
  refine ⟨D, hD, hle.trans ?_⟩
  exact mul_le_mul_of_nonneg_right h (add_nonneg (adjE1_nonneg _ _ _) (adjE0_nonneg _ _ _))

theorem adjointEnergyIneqs_of (m : ℝ) (hc : AdjointEnergyCont m) (h0 : AdjointE0Ineq m)
    (h1 : AdjointE1Ineq m) : AdjointEnergyIneqs m := by
  obtain ⟨bc, hc⟩ := hc
  obtain ⟨b0, h0⟩ := h0
  obtain ⟨b1, h1⟩ := h1
  refine ⟨max bc (max b0 b1), fun b hb => ?_⟩
  obtain ⟨Cc, νc, hCc, hνc, hc'⟩ := hc b (le_trans (le_max_left _ _) hb)
  obtain ⟨C0, ν0, hC0, hν0, h0'⟩ :=
    h0 b (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb)
  obtain ⟨C1, ν1, hC1, hν1, h1'⟩ :=
    h1 b (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hb)
  refine ⟨max C0 C1, min νc (min ν0 ν1), le_trans hC0 (le_max_left _ _),
    lt_min hνc (lt_min hν0 hν1), ?_⟩
  intro ν hν tr htr t s ht hts hst hb' G hG φ hφ
  have hνc' : ν ∈ Ioc 0 νc := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν0' : ν ∈ Ioc 0 ν0 :=
    ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν1' : ν ∈ Ioc 0 ν1 :=
    ⟨hν.1, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨hk0, hk1⟩ := hc' ν hνc' tr htr t s ht hts hst hb' G hG φ hφ
  exact ⟨hk0, hk1,
    adjQE0_mono (le_max_left _ _) (h0' ν hν0' tr htr t s ht hts hst hb' G hG φ hφ),
    adjQE1_mono (le_max_right _ _) (h1' ν hν1' tr htr t s ht hts hst hb' G hG φ hφ)⟩

end UnforcedLeray.Short.IIIa
