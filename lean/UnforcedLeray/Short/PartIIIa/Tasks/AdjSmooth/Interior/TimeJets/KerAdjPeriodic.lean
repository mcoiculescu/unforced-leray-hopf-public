import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **(17) The kernel adjoint is `d`-periodic** (`KerNearFar`: `K_d` is `d`-periodic). -/
theorem kerAdjPeriodic : KerAdjPeriodic := by
  intro d hd F y
  unfold kerAdj
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro j _
  have h2 : kerD d ((x - y).1 - d, (x - y).2) j = kerD d (x - y) j := by
    obtain ⟨C, _, hp⟩ := kerNearFar
    have hper := (hp d hd).2.1 ((x - y).1 - d, (x - y).2) j
    rw [sub_add_cancel] at hper
    exact hper.symm
  have h : x - (y.1 + d, y.2) = ((x - y).1 - d, (x - y).2) := by
    ext <;> simp <;> ring
  rw [h, h2]

end UnforcedLeray.Short.IIIa
