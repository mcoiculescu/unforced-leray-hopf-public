import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2

/-!
# `WardXrAxiOfX0` (`PartIII-b:IIIb-D2/3/2/11/2/7`, source 121-124, 4171-4178)

Symmetry without swirl of `wardXr` from that of `X₀` on the young region. Off the axis and inside
the young cylinder `wardXr = χy(ν·age) X₀ + (…) e₃`; the scalars are invariant under linear
isometries `g` fixing the axis, `e₃` is fixed, and `X₀` is equivariant by its frame form
(`AxiNoSwirlOn`, `frameL`, `meridPt`). Outside the young cylinder `wardXr` vanishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`WardXrAxiOfX0`** (source 121-124, 4171-4178): the regularized Ward displacement is axisymmetric
without swirl pointwise, given that `X₀` is on the young region. -/
theorem wardXrAxiOfX0_proved : WardXrAxiOfX0 := by
  intro ν μ R c χy gc hν hR hχy hA τ g hg x
  have he3 : g (coordinateVector 2) = coordinateVector 2 := hg
  have he3' : g e3 = e3 := hg
  have hmp : meridPt (g.symm x) = meridPt x := by
    simp only [meridPt, ϱ_symm_apply g hg, symm_apply_two g hg]
  by_cases hax : x ∈ axis
  · have hx0 : ϱ x = 0 := (mem_axis_iff x).1 hax
    have hsax : g.symm x ∈ axis := (mem_axis_iff _).2 (by rw [ϱ_symm_apply g hg, hx0])
    rw [wardXr_of_mem ν μ R c χy gc τ hax, wardXr_of_mem ν μ R c χy gc τ hsax, map_zero]
  · by_cases hY : R * Real.sqrt (5 * ν / 6) < ϱ x
    · have hsax : g.symm x ∉ axis := by
        intro h
        have h0 : ϱ (g.symm x) = 0 := (mem_axis_iff _).1 h
        rw [ϱ_symm_apply g hg] at h0
        have hpos : 0 < ϱ x := lt_of_le_of_lt (mul_nonneg hR.le (Real.sqrt_nonneg _)) hY
        linarith
      have hxY : x ∈ youngOpen ν R := hY
      have hsY : g.symm x ∈ youngOpen ν R := by
        show R * Real.sqrt (5 * ν / 6) < ϱ (g.symm x)
        rw [ϱ_symm_apply g hg]
        exact hY
      have hZ : g (wardX0 ν μ R c gc τ (g.symm x)) = wardX0 ν μ R c gc τ x := by
        have h1 := hA τ (g.symm x) hsY hsax
        have h2 := hA τ x hxY hax
        rw [h1, h2, hmp]
        simp only [frameL_apply, map_add, map_smul, map_eR_symm g hg, he3']
      have hage : age R (g.symm x) = age R x := by
        unfold age
        rw [ϱ_symm_apply g hg]
      rw [wardXr_of_not_mem ν μ R c χy gc τ hsax, wardXr_of_not_mem ν μ R c χy gc τ hax]
      simp only [wardX, wardStreamCut, hage, ϱ_symm_apply g hg, symm_apply_two g hg]
      rw [map_add, map_smul, map_smul, he3, hZ]
    · have hsq : ϱ x ^ 2 ≤ ν * R ^ 2 := by
        have h0 : 0 ≤ ϱ x := ϱ_nonneg x
        have hle : ϱ x ≤ R * Real.sqrt (5 * ν / 6) := not_lt.1 hY
        have hs2 : Real.sqrt (5 * ν / 6) ^ 2 = 5 * ν / 6 := Real.sq_sqrt (by linarith)
        have hm := mul_le_mul hle hle h0 (mul_nonneg hR.le (Real.sqrt_nonneg _))
        have he : (R * Real.sqrt (5 * ν / 6)) * (R * Real.sqrt (5 * ν / 6)) = R ^ 2 * (5 * ν / 6) := by
          rw [show (R * Real.sqrt (5 * ν / 6)) * (R * Real.sqrt (5 * ν / 6))
            = R ^ 2 * Real.sqrt (5 * ν / 6) ^ 2 by ring, hs2]
        nlinarith [hm, he, mul_nonneg hν.le (sq_nonneg R)]
      have hsq2 : ϱ (g.symm x) ^ 2 ≤ ν * R ^ 2 := by
        rw [ϱ_symm_apply g hg]
        exact hsq
      rw [wardXr_eq_zero_of_sq_le (ν := ν) (μ := μ) (R := R) (c := c) hχy gc τ hsq,
        wardXr_eq_zero_of_sq_le (ν := ν) (μ := μ) (R := R) (c := c) hχy gc τ hsq2, map_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
