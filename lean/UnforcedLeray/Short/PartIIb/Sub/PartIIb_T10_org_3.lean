import UnforcedLeray.Short.PartIIb.Bridge.Adjoint
import UnforcedLeray.Units.B0427

/-!
# `PartII-b:T10/org/3`: decomposition of `AdjSolSolenoidal`

Source `the November 2 reference manuscript` lines 1359-1361, 1426-1440, 1498-1500.
`AdjSolSolenoidal` follows from `CommonBodyAdjoint` (uniqueness from the `r = 2` graph bound with
datum `0`) together with the two facts below.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open Set MeasureTheory Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Short.PartIIa

/-- **Leray projection commutes with the `r = 2` adjoint** (lines 1359-1361, 1498-1500): if
`(μ̄ + L₀)ᵗ`-pairing equation `W ↦ F` holds in `Y_2`, then it holds for `(𝐏W, 𝐏F)`. -/
def AdjointLerayCommute : Prop :=
  ∀ (P ν μ : ℝ) [Fact (0 < P)], P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 → ∀ Fq Wq : Yq P 2,
    HasPhaseOp (fun Φ => (starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ) Wq Fq →
      HasPhaseOp (fun Φ => (starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top Wq)
        (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top Fq)

/-- **Distributionally solenoidal fields of `Y_2` are fixed by `𝐏`** (line 1358-1361, 1498-1500:
`Y_{2,σ}` is the range of `𝐏`; the converse of `lerayY_isPhaseSolenoidal` at `q = 2`). -/
def YsigmaFixedByLeray : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (F : Yq P 2), F ∈ Ysigma P 2 →
    lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top F = F

theorem adjSolSolenoidal_of (hAdj : CommonBodyAdjoint) (hC : AdjointLerayCommute)
    (hFix : YsigmaFixedByLeray) : AdjSolSolenoidal := by
  intro P ν μ _ hP1 hν hμ Fq Wq hFs h
  set V := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top Wq with hV
  have hV' := hC P ν μ hP1 hν hμ Fq Wq h
  rw [hFix P Fq hFs] at hV'
  have hd : HasPhaseOp (fun Φ => (starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ) (Wq + (-1 : ℂ) • V)
      (Fq + (-1 : ℂ) • Fq) := h.add (hV'.smul (-1))
  have h0 : Fq + (-1 : ℂ) • Fq = 0 := by simp
  rw [h0] at hd
  obtain ⟨C, -, hb⟩ := hAdj
  obtain ⟨-, hmax⟩ := hb P hP1 ν hν (μ : ℂ) (by simpa using hμ) 0
  obtain ⟨hw, g, -, hle⟩ := hmax _ hd
  have hg : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have h1 : graphNormD (⟨_, hw⟩ : D P ν 2) = 0 := by
    have : 0 ≤ graphNormD (⟨_, hw⟩ : D P ν 2) := by
      unfold graphNormD; positivity
    simp only [norm_zero, mul_zero] at hle
    linarith
  have h2 := (UnforcedLeray.B0427.graphNormD_eq_zero_iff _).1 h1
  have h3 : Wq + (-1 : ℂ) • V = 0 := congrArg Subtype.val h2
  have h4 : Wq = V := by
    have : Wq = Wq + (-1 : ℂ) • V + V := by simp
    rw [this, h3]; simp
  rw [h4]
  exact lerayY_isPhaseSolenoidal ENNReal.one_lt_two ENNReal.ofNat_ne_top Wq

theorem adjSolSolenoidal_of_leaves (hAdj : CommonBodyAdjoint) (hC : AdjointLerayCommute)
    (hFix : YsigmaFixedByLeray) : AdjSolSolenoidal := adjSolSolenoidal_of hAdj hC hFix

end UnforcedLeray.Short.IIb
