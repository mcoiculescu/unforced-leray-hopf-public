import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges

/-!
# Bridge 3b: the advection of a smooth `c`-periodic field is continuous and `Q`-periodic

Source: `the November 2 reference manuscript`,
lines 261-288. `Train.advection w` is built from the classical partials `Cyl.partialQ`,
`Cyl.partialEta` of the two components of `w`. Those partials of a `c`-periodic function are
`c`-periodic (`Cyl.IsPeriodic.partialQ`, `Cyl.IsPeriodic.partialEta`), and those of a `C^∞`
function are continuous (`Cyl.contDiff_partialQ`, `Cyl.contDiff_partialEta`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

/-- Component `i` of a smooth vector field is smooth. -/
theorem advComp_contDiff {w : Plane → Vec} (hw : ContDiff ℝ ∞ w) (i : Fin 2) :
    ContDiff ℝ ∞ (fun z => w z i) := by
  have h : ContDiff ℝ ∞ (fun z => (EuclideanSpace.proj i : StrongDual ℝ Vec) (w z)) :=
    (EuclideanSpace.proj i : StrongDual ℝ Vec).contDiff.comp hw
  exact h

theorem advectionPeriodicContinuous : AdvectionPeriodicContinuous := by
  intro c w hw hper
  have hper0 : Cyl.IsPeriodic c (fun z => w z 0) := fun z => by dsimp only; rw [hper z]
  have hper1 : Cyl.IsPeriodic c (fun z => w z 1) := fun z => by dsimp only; rw [hper z]
  have hQ0 := Cyl.IsPeriodic.partialQ hper0
  have hQ1 := Cyl.IsPeriodic.partialQ hper1
  have hE0 := Cyl.IsPeriodic.partialEta hper0
  have hE1 := Cyl.IsPeriodic.partialEta hper1
  have hs0 := advComp_contDiff hw 0
  have hs1 := advComp_contDiff hw 1
  have hcont0 : Continuous (fun z => w z 0) := hs0.continuous
  have hcont1 : Continuous (fun z => w z 1) := hs1.continuous
  have hdQ0 : Continuous (Cyl.partialQ fun z => w z 0) :=
    (Cyl.contDiff_partialQ (n := 0) (h := fun z => w z 0) (hs0.of_le (by simp))).continuous
  have hdQ1 : Continuous (Cyl.partialQ fun z => w z 1) :=
    (Cyl.contDiff_partialQ (n := 0) (h := fun z => w z 1) (hs1.of_le (by simp))).continuous
  have hdE0 : Continuous (Cyl.partialEta fun z => w z 0) :=
    (Cyl.contDiff_partialEta (n := 0) (h := fun z => w z 0) (hs0.of_le (by simp))).continuous
  have hdE1 : Continuous (Cyl.partialEta fun z => w z 1) :=
    (Cyl.contDiff_partialEta (n := 0) (h := fun z => w z 1) (hs1.of_le (by simp))).continuous
  constructor
  · intro z
    have e0 := hQ0 z
    have e1 := hE0 z
    have e2 := hQ1 z
    have e3 := hE1 z
    unfold Train.advection
    simp only [hper z, e0, e1, e2, e3]
  · unfold Train.advection
    exact Train.toVecL.continuous.comp (by fun_prop)

end UnforcedLeray.Short.PartI
