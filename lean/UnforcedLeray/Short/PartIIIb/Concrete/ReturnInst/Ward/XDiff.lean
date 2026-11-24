import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Main
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XAdd.Reg
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L3

/-!
# `WardXDiff`: regularity of the Ward displacement off the axis
(source 4187-4201, 3603-3713)

Source of record: `the November 2 reference manuscript` (73 pages).

For old `L²` data `g`, `oldPhys R c g` agrees a.e. with the separated source
`T' = oldCutSrc R c (R√(5ν/6)) g` (`xa_oldReg`), `sepW` does not see the null set, so
`X₀ = wardX0 g = sepX0 T'`, and `X = 𝒞_y X₀` is the cut displacement of a separated source with
finite `Y₂` moment: `xd_main` gives the three clauses.  The axisymmetry of `X₀` on the young
region is `wardX0Axi_all`, with the integrability of `sepW` at the trace point from
`xa_sepIntegrable`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wardXDiff_proved : WardXDiff := by
  intro ν μ R c χy hχy hν hR hc hμ g hg τ
  obtain ⟨hS, hM, hae⟩ := xa_oldReg hc hν hR hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  have hP : 0 < 2 * c / R := by positivity
  set T' := oldCutSrc R c r0 g with hT'
  have hSW : ∀ (μ' : ℂ) (y : Space) (τ' : ℝ),
      IIIa.sepW ν μ' (oldPhys R c g) y τ' = IIIa.sepW ν μ' T' y τ' :=
    fun μ' y τ' => sepWCongrAE ν μ' _ _ hae y τ'
  have hZeq : wardX0 ν μ R c g = sepX0 ν μ T' := by
    funext t y
    simp only [wardX0, sepX0, hSW]
  have hX : wardX ν μ R c χy g = wardStreamCut ν R χy (sepX0 ν μ T') := by
    unfold wardX
    rw [hZeq]
  have haxi : AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T') := by
    intro t y hy hyax
    have hmer : r0 < ϱ (meridPt y) := by
      rw [varrho_meridPt]; exact hy
    have h1 := xa_sepIntegrable hc hν hR hg (μ : ℂ) (by simpa using hμ) t (meridPt y) hmer
    have h2 := xa_sepIntegrable hc hν hR hg ((μ : ℂ) + 1) (by simp; linarith) t (meridPt y) hmer
    rw [← hZeq]
    exact wardX0Axi_all ν μ R c g t y hyax h1 h2
  rw [hX]
  exact xd_main hχy hν hμ hR hP hS hM haxi τ

end UnforcedLeray.Short.PartIIIb.Concrete
