import UnforcedLeray.Short.Spine.PlanarFromC01
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Small bridges of the Spine

* `partIOutput_of_canonical`: `PartIOutput` from the canonical branch (G3b) and the train existence
  in the BUC class (`TrainBUCExistence`).
* `trainBUCExistence_of_global`: the Part I area's `TrainGlobalExistence` (lines 270-288,
  Gallay-Slijepcevic for `ν > 0`, `c ≥ 1`, in the BUC class) gives `TrainBUCExistence`
  (`c = ν^{-2} ≥ 1` for `ν ≤ 1`); `trainExistence_of_global` forgets the class and gives the
  library's `B0140.TrainExistence`.
* `shortPeriod_eq_period`: the period `2εc` of `IsShortBackground` is the draft record's
  `R.base.period n`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint
open UnforcedLeray.Cons.Data

theorem partIOutput_of_canonical (hcan : Cons.C01.CanonicalBranchHyp)
    (htrain : TrainBUCExistence) : PartIOutput :=
  ⟨gaussianInstability_of_canonicalBranch hcan, htrain⟩

theorem trainBUCExistence_of_global (h : Short.PartI.TrainGlobalExistence) :
    TrainBUCExistence :=
  ⟨1, one_pos, fun ν hν => h ν (Train.per ν) hν.1 (Train.one_le_per hν.1 hν.2)⟩

theorem trainExistence_of_global (h : Short.PartI.TrainGlobalExistence) :
    B0140.TrainExistence := by
  obtain ⟨ν₀, hν₀, H⟩ := trainBUCExistence_of_global h
  exact ⟨ν₀, hν₀, fun ν hν => (H ν hν).elim fun tr _ => ⟨tr⟩⟩

theorem shortPeriod_eq_period (R : Reference) (n : ℕ) :
    shortPeriod (nuSeq R n) (epsSeq R n) = R.base.period n := by
  simp only [shortPeriod, Train.per, nuSeq, epsSeq, ConstructionData.period,
    ConstructionData.spacing, inv_pow]

end UnforcedLeray.Short.Spine
