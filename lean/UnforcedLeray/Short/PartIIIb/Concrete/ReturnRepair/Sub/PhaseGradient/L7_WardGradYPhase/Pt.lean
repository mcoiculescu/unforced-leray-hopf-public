import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.WreCut
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L7_WardGradYPhase.Comm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L6_SepX0FreeEq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff.Comm
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# `PartIII-b:C/rep/2/7`, the pointwise bound for `DY`

Source `the November 2 reference manuscript` 4171, 4192-4200, 4203-4214, 5212-5223.
Off the axis `Y = 𝒞_y Re W_μ + tcComm(X₀)` (free equation `D_{μ+1}X₀ = Re W_μ` on the young region
and `sepComm = tcComm`), so `DY` is bounded by the cut-field bound `wgyCutPointwise` plus the bound
`wgy_comm_fderiv_bound` of the explicit commutator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `Y = 𝒞_y Re W_μ + tcComm(X₀)` at every point off the axis. -/
theorem wgy_Y_eq {σ₁ σ₂ ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hσ : -(1 / 4) < σ₁) (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R) (hP : 0 < P)
    (hμ : μ ∈ Icc σ₁ σ₂) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    sepWY ν μ R χy T τ y =
      wardStreamCut ν R χy (sepWre ν μ T) τ y + tcComm ν R χy (sepX0 ν μ T) τ y := by
  have hR : 0 < R := by linarith
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have h1 : sepWY ν μ R χy T τ y =
      sepComm ν μ R χy T τ y +
        wardStreamCut ν R χy (physDmu ν (μ + 1) (sepX0 ν μ T)) τ y := by
    unfold sepComm sepWY
    abel
  have h2 : wardStreamCut ν R χy (physDmu ν (μ + 1) (sepX0 ν μ T)) τ y =
      wardStreamCut ν R χy (sepWre ν μ T) τ y := by
    refine wardStreamCut_congr hχ hν.le ?_ τ hy
    intro τ' z hz hage
    refine sepX0FreeEq ν μ _ P hν hμ' hr0 hP T hT hM τ' z ?_
    have hz2 : ν * R ^ 2 ≤ ϱ z ^ 2 := by
      have : ν * (R ^ 2 / ϱ z ^ 2) ≤ 1 := hage
      rw [← mul_div_assoc, div_le_one (by positivity)] at this
      exact this
    have hs : (R * Real.sqrt (5 * ν / 6)) ^ 2 < ϱ z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith [mul_pos hν (pow_pos hR 2)]
    exact lt_of_pow_lt_pow_left₀ 2 hz.le hs
  rw [h1, h2, Sub8_1_1_2_3.sepComm_eq_tcComm hχ hσ hν hν1 hR1 hP hμ hT hM hA τ hy]
  abel

lemma wgy_ofReal5 (C s a b c d e : ℝ) (hC : 0 ≤ C) (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) :
    ENNReal.ofReal (C * (s * a + b + s * c + s ^ 2 * b + s ^ 3 * e)) =
      ENNReal.ofReal C * (ENNReal.ofReal s * ENNReal.ofReal a + ENNReal.ofReal b +
        ENNReal.ofReal s * ENNReal.ofReal c + ENNReal.ofReal (s ^ 2) * ENNReal.ofReal b +
        ENNReal.ofReal (s ^ 3) * ENNReal.ofReal e) := by
  have p2 : 0 ≤ s ^ 2 := by positivity
  have p3 : 0 ≤ s ^ 3 := by positivity
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul hs, ENNReal.ofReal_mul hs, ENNReal.ofReal_mul p2, ENNReal.ofReal_mul p3]

/-- The pointwise bound for `DY` (source 4192-4200, 4203-4214). -/
def WGYPointwise : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → P ≤ 1 → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
          ENNReal.ofReal ‖fderiv ℝ (sepWY ν μ R χy T τ) y‖ ≤
            (wgyWJet 1 ν μ (R * Real.sqrt ν) T τ y +
              ENNReal.ofReal (C₁ * (R * Real.sqrt ν) ^ (-1 : ℝ)) *
                wgyWJet 0 ν μ (R * Real.sqrt ν) T τ y +
              ENNReal.ofReal (C₁ * (R * Real.sqrt ν) ^ (-3 : ℝ)) * wgyWPsi ν μ R T τ y) +
            ENNReal.ofReal C₂ *
              (ENNReal.ofReal (R * Real.sqrt ν)⁻¹ * wgxJet 0 ν μ (R * Real.sqrt ν) T τ y +
                wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
                ENNReal.ofReal (R * Real.sqrt ν)⁻¹ * wgxJet 2 ν μ (R * Real.sqrt ν) T τ y +
                ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 2) * wgxJet 1 ν μ (R * Real.sqrt ν) T τ y +
                ENNReal.ofReal ((R * Real.sqrt ν)⁻¹ ^ 3) * wgxPsi ν μ R T τ y)

end UnforcedLeray.Short.PartIIIb.Concrete

end
