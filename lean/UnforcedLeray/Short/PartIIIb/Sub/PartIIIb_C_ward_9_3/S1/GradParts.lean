import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.GradStruct
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.GradDecay

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcGrad_of_partsW (hS : TCGradX0StructW) (hD : TCGradX0DecayW) : TCGradW := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := hctx
  have hctx : TCCtxW σ₁ σ₂ ν μ R P T y := ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩
  have hR : 0 < R := by linarith
  have hyy : y ∈ youngOpen ν R := by
    show R * Real.sqrt (5 * ν / 6) < ϱ y
    refine lt_of_lt_of_le ?_ hy.1
    exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  obtain ⟨h1, h2, h3⟩ := hS σ₁ σ₂ ν μ R P T τ y hctx
  obtain ⟨h4, h5⟩ := hD σ₁ σ₂ ν μ R P T τ y hctx
  exact tcg_generic hν hR hyy h1 h2 h3 h4 h5

end UnforcedLeray.Short.PartIIIb.Concrete

end
