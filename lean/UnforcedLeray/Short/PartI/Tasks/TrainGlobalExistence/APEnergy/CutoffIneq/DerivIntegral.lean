import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.HasDeriv

/-!
# Part I, task `PartI:T04/5/1/2/1`: `APEnergyDerivIntegral` (differentiation under the integral)

Source of record: `the November 2 reference manuscript`, lines 278-286.

Route: `ccEH_generic` (proved, `Tasks/ClassicalOdd/ClassicalCutoffEnergyIneq/HasDeriv.lean`) applied to
`W x = v x.1 x.2` on `Ioo 0 T ×ˢ univ`, followed by the identification
`deriv (fun t => v t z) s = fderiv W (s,z) (1,0)` (chain rule along `t ↦ (t,z)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **Task `PartI:T04/5/1/2/1`**: differentiation under the integral sign for the cutoff energy. -/
theorem apEnergyDerivIntegral : APEnergyDerivIntegral := by
  intro ν c T v p hν hc hcls R hR s hs
  have hcc : 0 < c := by linarith [hcls.pos]
  have hR0 : 0 < R := by linarith
  have hW : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Ioo 0 T ×ˢ univ) :=
    hcls.classical.smooth_v.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hH := ccEH_generic hW c R hcc hR0 s hs.1 hs.2
  have hfd : ∀ z : Plane, deriv (fun t => v t z) s =
      fderiv ℝ (fun x : ℝ × Plane => v x.1 x.2) (s, z) ((1 : ℝ), (0 : Plane)) := by
    intro z
    have hdiff : DifferentiableAt ℝ (fun x : ℝ × Plane => v x.1 x.2) (s, z) :=
      (hW.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ z⟩)).differentiableAt
        (by simp)
    have hline : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × Plane)) ((1 : ℝ), (0 : Plane)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt s hline).deriv
  have hint : (∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * inner ℝ (v s z) (deriv (fun t => v t z) s))) =
      ∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ ((fun x : ℝ × Plane => v x.1 x.2) (s, z))
          (fderiv ℝ (fun x : ℝ × Plane => v x.1 x.2) (s, z) ((1 : ℝ), (0 : Plane)))) := by
    congr 1
    funext z
    rw [hfd z]
  rw [hint]
  exact hH

end UnforcedLeray.Short.PartI
