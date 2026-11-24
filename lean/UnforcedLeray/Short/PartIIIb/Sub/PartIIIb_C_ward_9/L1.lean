import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent

/-!
# `PartIII-b:C/ward/9/1`: the shifted resolvent identity for all old `L²` data

Source `the November 2 reference manuscript` 4196-4201 (`ward:shifted-resolvent`),
4163-4168 (old source supported in `s ≥ 1.2/ν`).

The separated source attached to any old `L²` datum `g` (`thinSepBridge`, `ShiftedResolvent.lean`)
has the same `sep` kernels as `oldPhys R c g`; on the young region `ϱ > R√(5ν/6)` the identity
`D_{μ+1}X₀ = W_μ` is then the separated identity `SepX0FreeEq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`WardYShiftedRes`** (`ward:shifted-resolvent`, source 4196-4201) for all old `L²` data. -/
theorem wardYShiftedRes_proved : WardYShiftedRes := by
  intro ν μ R c g hν hR hc hμ hg
  have hε : 0 < R⁻¹ := inv_pos.2 hR
  have hM : ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤ := by
    have h := MeasureTheory.MemLp.eLpNorm_lt_top hg.memLp
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top] at h
    simpa [ENNReal.rpow_two] using h
  obtain ⟨S, hS1, hS2, -, hresp⟩ :=
    thinSepBridge c ν R⁻¹ hc hν hε g hg.measurable hg.old hM
  simp only [inv_inv] at hS1 hresp
  have hsep : ∀ (μ' : ℂ) (τ : ℝ) (y : Space),
      UnforcedLeray.Short.IIIa.sepW ν μ' (oldPhys R c g) y τ =
        UnforcedLeray.Short.IIIa.sepW ν μ' S y τ :=
    fun μ' τ y => hresp μ' y τ
  have hX0 : wardX0 ν μ R c g = sepX0 ν μ S := by
    funext τ y
    simp only [wardX0, sepX0, hsep]
  have hW : ∀ τ y, wardW ν μ R c g τ y = sepWre ν μ S τ y := by
    intro τ y
    simp only [wardW, sepWre, hsep]
  unfold ShiftedResolventYoung
  intro τ y hy hage
  rw [hX0, hW]
  have hϱ2 : ν * R ^ 2 ≤ ϱ y ^ 2 := by
    unfold age at hage
    rw [mul_div_assoc', div_le_one (pow_pos hy 2)] at hage
    exact hage
  have hs : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpos : 0 ≤ R * Real.sqrt (5 * ν / 6) := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hνR : 0 < ν * R ^ 2 := mul_pos hν (pow_pos hR 2)
  have hr : R * Real.sqrt (5 * ν / 6) < ϱ y := by
    by_contra h
    have h' : ϱ y ≤ R * Real.sqrt (5 * ν / 6) := not_lt.mp h
    nlinarith [hs, hϱ2, hνR, hy, hpos, h']
  exact (sepX0FreeEq_of sepWHRep sepKerPDE sepX0Comb) ν μ (R * Real.sqrt (5 * ν / 6))
    (2 * R⁻¹ * c) hν hμ hpos (by positivity) S hS1 hS2 τ y hr

end UnforcedLeray.Short.PartIIIb.Concrete
