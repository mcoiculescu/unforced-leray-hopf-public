import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Reg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcRegW : TCRegW := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := hctx
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hR : 0 < R := by linarith
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hrr : R * Real.sqrt (5 * ν / 6) < ϱ y := by
    have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    have h2 : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := mul_lt_mul_of_pos_left h1 hR
    exact lt_of_lt_of_le h2 hy.1
  have hcdOn : ContDiffOn ℝ 2 (sepX0 ν μ T τ) (youngOpen ν R) :=
    tcd_X0_cdOn hν hμ' hr0 hP hT hM τ
  have hdec := tcr_streamDecay hν hμ' hR hP hT hM τ
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hdiv : ∀ y' ∈ youngOpen ν R, ∑ j : Fin 3, physPd (sepX0 ν μ T τ) j y' j = 0 :=
    fun y' hy' => tcr_divFree hν hμ' hr0 hP hT hM τ hy'
  have haxi : AxiNoSwirlOn (youngOpen ν R) (sepX0 ν μ T) := fun τ' y' hy' _ =>
    tcr_axi hν hμ' hr0 hP hT hM hA τ' hy'
  have hdr : ∀ r z, R * Real.sqrt (5 * ν / 6) < r →
      HasDerivAt (fun r' => outPrim (sepX0 ν μ T) τ r' z)
        (r * sepX0 ν μ T τ !₂[r, 0, z] 2) r ∧
      HasDerivAt (fun z' => outPrim (sepX0 ν μ T) τ r z')
        (-(r * sepX0 ν μ T τ !₂[r, 0, z] 0)) z := fun r z hr =>
    ⟨outPrimDerivR ν R (sepX0 ν μ T) τ hcdOn hdec r z hr,
      outPrimDerivZ ν R (sepX0 ν μ T) τ hcdOn hdiv haxi hdec r z hr⟩
  have hO := t9_outPrim_c2 hν hR hcdOn hdr
  refine ⟨tcd_X0_cd hν hμ' hr0 hP hT hM τ hrr, ?_, ?_, ?_⟩
  · exact (tcr_hasDerivAt_tau hν hμ' hr0 hP hT hM τ hrr).differentiableAt
  · have h1 : ContDiffAt ℝ 2 (fun y' : Space => outPrim (sepX0 ν μ T) τ (ϱ y') (y' 2)) y :=
      hO.contDiffAt (hopen.mem_nhds hrr)
    exact h1.smul contDiffAt_const
  · exact (tcr_psi_tau hν hμ' hr0 hP hT hM τ hrr).differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete

end
