import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Reg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Time
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Int
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Lap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Rad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.GradParts
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Coeff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Relaxed `TransCommPoint` (arbitrary `ν, R > 0`; the constant depends on `ν, R` and `χ_y`). -/
theorem sepCommBoundW (ν μ R : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℝ), 0 < P →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), y ∈ streamAnn ν R →
          ‖sepComm ν μ R χy T τ y‖ₑ ≤ ENNReal.ofReal C *
            (‖sepX0 ν μ T τ y‖ₑ + ENNReal.ofReal (R * Real.sqrt ν)⁻¹ * ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ +
              ENNReal.ofReal (((R * Real.sqrt ν)⁻¹) ^ 2) *
                ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|) := by
  obtain ⟨M, hM1, hB⟩ := tcCoeffW χy hχ
  have hL0 : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  set W : ℝ := ν * ((R * Real.sqrt ν)⁻¹) ^ 2 with hWdef
  have hW0 : 0 ≤ W := by positivity
  set C0 : ℝ := 100 * M * (1 + W + ν) with hC0def
  have hC0 : 0 ≤ C0 := by positivity
  refine ⟨2 * C0, by positivity, ?_⟩
  intro P hP T hT hM hA τ y hy
  have hctx : TCCtxW μ μ ν μ R P T y :=
    ⟨hμ, hν, trivial, hR, hP, ⟨le_rfl, le_rfl⟩, hT, hM, hA, hy⟩
  have hϱ0 : 0 < ϱ y := lt_of_lt_of_le hL0 hy.1
  obtain ⟨r1, r2, r3, r4⟩ := tcRegW μ μ ν μ R P T τ y hctx
  obtain ⟨i1, i2, i3, i4⟩ := tcIntW μ μ ν μ R P T τ y hctx
  have key := tcLeibniz ν μ R χy hχ hν hR (sepX0 ν μ T) τ y hϱ0 r1 r2 r3 r4 i1 i2 i3 i4
    (tcTimeW μ μ ν μ R P T τ y hctx) (tcGrad_of_partsW tcGradX0StructW tcGradX0DecayW μ μ ν μ R P T τ y hctx)
    (tcLapW μ μ ν μ R P T τ y hctx) (tcRadW μ μ ν μ R P T τ y hctx) (μ + 1)
  have e : sepComm ν μ R χy T τ y = tcComm ν R χy (sepX0 ν μ T) τ y := key
  rw [e]
  unfold tcComm
  obtain ⟨b1, b2, b3, b4⟩ := hB ν R hν hR (ϱ y) hy.1 hy.2
  have hLi : 0 ≤ (R * Real.sqrt ν)⁻¹ := inv_nonneg.2 hL0.le
  have c1 : |tcA1 ν R χy (ϱ y)| ≤ C0 := by
    refine b1.trans ?_
    rw [hC0def]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M) hν.le]
  have c2 : |tcA2 ν R χy (ϱ y)| ≤ C0 * (R * Real.sqrt ν)⁻¹ := by
    refine b2.trans ?_
    rw [hC0def]
    have : 0 ≤ M * W := mul_nonneg (by linarith) hW0
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) (by linarith : (0 : ℝ) ≤ 1 + W)) hLi,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ M) hW0) hLi]
  have c3 : |tcB1 ν R χy (ϱ y)| ≤ C0 * ((R * Real.sqrt ν)⁻¹) ^ 2 := by
    refine b3.trans ?_
    rw [hC0def]
    have h2 : 0 ≤ ((R * Real.sqrt ν)⁻¹) ^ 2 := sq_nonneg _
    have : 0 ≤ M * ν * ((R * Real.sqrt ν)⁻¹) ^ 2 :=
      mul_nonneg (mul_nonneg (by linarith) hν.le) h2
    nlinarith
  have c4 : |tcB2 ν R χy (ϱ y)| ≤ C0 := by
    refine b4.trans ?_
    rw [hC0def]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M) hν.le]
  have hG' : ‖fderiv ℝ (sepX0 ν μ T τ) y (radialUnit y)‖ₑ ≤ ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖fderiv ℝ (sepX0 ν μ T τ) y (radialUnit y)‖
        ≤ ‖fderiv ℝ (sepX0 ν μ T τ) y‖ * ‖radialUnit y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (sepX0 ν μ T τ) y‖ * 1 :=
          mul_le_mul_of_nonneg_left (tc_radialUnit_norm hϱ0) (norm_nonneg _)
      _ = _ := mul_one _
  exact tc_expr_bound (L := R * Real.sqrt ν) hC0 c1 c2 c3 c4 (sepX0 ν μ T τ y)
    (fderiv ℝ (sepX0 ν μ T τ) y (radialUnit y)) ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ hG'
    (ψ := outPrim (sepX0 ν μ T) τ (ϱ y) (y 2))

end UnforcedLeray.Short.PartIIIb.Concrete

end
