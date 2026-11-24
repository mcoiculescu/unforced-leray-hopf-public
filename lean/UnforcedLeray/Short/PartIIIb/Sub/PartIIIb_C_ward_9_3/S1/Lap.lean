import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Rad.Basic

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem tcb_of_ctxW {σ₁ σ₂ ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {y : Space}
    (h : TCCtxW σ₁ σ₂ ν μ R P T y) : TCH ν R μ P T := by
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := h
  exact ⟨hν, hR1, by linarith [hμ.1], hP, hT, hM, hA⟩

theorem tcb_ann_gtW {σ₁ σ₂ ν μ R P : ℝ} {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {y : Space}
    (h : TCCtxW σ₁ σ₂ ν μ R P T y) : R * Real.sqrt (5 * ν / 6) < ϱ y := by
  obtain ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hy⟩ := h
  have h1 : Real.sqrt (5 * ν / 6) < Real.sqrt ν :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have := mul_lt_mul_of_pos_left h1 hR1
  exact lt_of_lt_of_le this hy.1

theorem tcLapW : TCLapW := by
  intro σ₁ σ₂ ν μ R P T τ y hctx
  have H := tcb_of_ctxW hctx
  have hy := tcb_ann_gtW hctx
  have hlap := tcl_lapPsi H τ hy
  have hint := tcl_integral H τ (y 2) hy
  have hpsi : psiFld (fun t y' => physLap (sepX0 ν μ T t) y') τ y =
      (-∫ ρ in Ioi (ϱ y), ρ * physLap (sepX0 ν μ T τ) (!₂[ρ, 0, y 2]) 2) •
        (coordinateVector 2 : Space) := rfl
  rw [hpsi, hint, hlap]
  rw [← sub_smul]
  congr 1
  ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
