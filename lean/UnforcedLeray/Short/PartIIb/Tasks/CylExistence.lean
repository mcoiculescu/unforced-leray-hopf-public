import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T23
import UnforcedLeray.Short.PartIIb.Tasks.CylExistence.FreeCylSmoothExists
import UnforcedLeray.Short.PartIIb.Tasks.CylExistence.FreeCylApproxLimit

/-!
# `PartII-b:T23` (`CylExistence.lean`): existence and uniqueness of the weak free cylinder flow

Source of record: `the November 2 reference manuscript`, lines 2100-2118.

All proved BUC train regularity, backward solver, duality uniqueness (`free_cyl_unique`,
`free_cyl_unique_of_trainClose`), and weighted `L²` test density (`free_cyl_test_approx`)
results for `PartII-b:T23`, together with the leaf propositions `FreeCylSmoothExists`
(`PartII-b:T23/1`) and `FreeCylApproxLimit` (`PartII-b:T23/2`) and the conditional derivations
`free_cyl_exists_approx_of` and `free_cyl_exists_unique_of`, are in
`UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_T23»`.

Once `PartII-b:T23/1` and `PartII-b:T23/2` are proved, the unconditional theorem
`free_cyl_exists_unique` is obtained by applying
`free_cyl_exists_unique_of freeCylSmoothExists_proof freeCylApproxLimit_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

theorem free_cyl_exists_approx
    (m ν c : ℝ) (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (s : ℝ) (hs : 0 ≤ s) (f : B0579.Plane → ℝ) (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    ∃ (w : ℝ → B0579.Plane → ℝ) (fn : ℕ → B0579.Plane → ℝ) (ωn : ℕ → ℝ → B0579.Plane → ℝ),
      IsFreeCylFlow m tr s f w ∧
      (∀ n, B0579.IsCylTest c (fn n)) ∧
      Tendsto (fun n => eLpNorm (fn n - f) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) ∧
      (∀ n, IsFreeCylFlow m tr s (fn n) (ωn n)) ∧
      (∀ t : ℝ, s ≤ t →
        Tendsto (fun n => eLpNorm (ωn n t - w t) 2 (B0579.cellMeasure c m)) atTop (𝓝 0)) :=
  free_cyl_exists_approx_of freeCylSmoothExists_proof freeCylApproxLimit_proof
    m ν c hm hν hc tr hbu s hs f hf

theorem free_cyl_exists_unique : UnforcedLeray.Short.IIb.FreeCylExistsUnique :=
  free_cyl_exists_unique_of freeCylSmoothExists_proof freeCylApproxLimit_proof

end UnforcedLeray.Short.IIb

end
