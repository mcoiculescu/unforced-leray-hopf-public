import UnforcedLeray.Short.PartI.Sub.T02_1_4
import UnforcedLeray.Lib.TrainB.ProjectedInitialDatum
import UnforcedLeray.Lib.TrainB.P0CompactMildInitialTrace
import UnforcedLeray.Units.B0169

/-!
# Part I, task `PartI:T02/1/4/2`: the initial trace of the spatial representative (`RepInitial`)

Source of record: `the November 2 reference manuscript`, lines 261-285.  The
datum `trainDatum c = Train.datum c` is the initial value of the mild solution.

Proof.  The third conjunct of `IsMildTrain` gives `u (compactEvolutionZero hT) =
projectedInitialDatumH3 hc`.  The `represents` field of `IsSpatialRepOn` at that point with the
zero word identifies `w 0` almost everywhere on the cell with the `L²` class of
`projectedInitialDatumH3 hc`, which is the class of `Train.datum c` by
`projectedInitialDatumH3_value`.  Both `w 0` and `Train.datum c` are continuous, so a.e. equality
on `cell c` gives equality on `cell c` (the cell lies in the closure of its interior).  Finally
both functions are `c`-periodic in the first coordinate, so every point is moved into the cell.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)
open UnforcedLeray.TrainB

/-- **Leaf 2** (source lines 261-285): the spatial representative of the mild solution takes the
datum `trainDatum c` at time `0`. -/
theorem repInitial : RepInitial := by
  intro ν c T hν hc hc1 hT u hu w hw
  obtain ⟨-, -, hzero⟩ := hu
  have hcne : c ≠ 0 := hc.ne'
  have hz0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  -- the `L²` value of `w 0` on the cell is the class of the projected datum
  have hae := hw.represents (compactEvolutionZero hT) Sob.Idx.zero
  rw [hzero, projectedInitialDatumH3_value hc] at hae
  have hcoe : ((compactEvolutionZero hT : Icc (0 : ℝ) T) : ℝ) = 0 := rfl
  rw [hcoe] at hae
  have hid : ∀ f : Plane → Vec,
      Sob.iterD ((Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 3)) f = f :=
    fun f => rfl
  rw [hid] at hae
  have hcoe2 : ((memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) :
      Plane → Vec) =ᵐ[Cyl.cellμ c] Train.datum c :=
    MemLp.coeFn_toLp (memLp_datum_word_derivative hc Sob.Idx.zero)
  have hae0 : Train.datum c =ᵐ[Cyl.cellμ c] w 0 := hcoe2.symm.trans hae
  have hae1 : w 0 =ᵐ[volume.restrict (Cyl.cell c)] Train.datum c := hae0.symm
  -- continuity of both sides
  have hf0 : Continuous (w 0) := (hw.smooth 0 hz0).continuous
  have hg : Continuous (Train.datum c) := (Train.datum_contDiff hcne).continuous
  have hper : Cyl.IsPeriodic c (w 0) := hw.periodic 0 hz0
  -- a.e. equality on the cell gives equality on the cell
  have hne : -c / 2 ≠ c / 2 := by
    intro h
    linarith
  have hU : Cyl.cell c ⊆ closure (interior (Cyl.cell c)) := by
    unfold Cyl.cell
    rw [interior_prod_eq, interior_univ, interior_Ico, closure_prod_eq, closure_univ,
      closure_Ioo hne]
    exact Set.prod_mono Set.Ico_subset_Icc_self Set.Subset.rfl
  have hEq : EqOn (w 0) (Train.datum c) (Cyl.cell c) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae1 hf0.continuousOn hg.continuousOn hU
  -- every point is moved into the cell by periodicity in the first coordinate
  have hall : ∀ z : Plane, w 0 z = Train.datum c z := by
    intro z
    let φ : ℝ → Vec := fun x => w 0 (x, z.2) - Train.datum c (x, z.2)
    have hφ : Function.Periodic φ c := by
      intro x
      have h1 : w 0 (x + c, z.2) = w 0 (x, z.2) := hper (x, z.2)
      have h2 : Train.datum c (x + c, z.2) = Train.datum c (x, z.2) :=
        Train.datum_periodic c (x, z.2)
      show w 0 (x + c, z.2) - Train.datum c (x + c, z.2) =
        w 0 (x, z.2) - Train.datum c (x, z.2)
      rw [h1, h2]
    obtain ⟨y, hy, hyeq⟩ := hφ.exists_mem_Ico hc z.1 (-c / 2)
    have hyc : y ∈ Ico (-c / 2) (c / 2) := ⟨hy.1, by linarith [hy.2]⟩
    have hy0 : φ y = 0 := by
      have hmem : (y, z.2) ∈ Cyl.cell c := Set.mk_mem_prod hyc (Set.mem_univ _)
      show w 0 (y, z.2) - Train.datum c (y, z.2) = 0
      exact sub_eq_zero.mpr (hEq hmem)
    have hz : φ z.1 = 0 := hyeq.trans hy0
    exact sub_eq_zero.mp hz
  rw [UnforcedLeray.B0169.trainDatum_eq_datum c]
  exact funext hall

end UnforcedLeray.Short.PartI
