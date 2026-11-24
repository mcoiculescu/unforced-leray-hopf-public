import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:T05`: uniqueness of the train in the BUC class (conditional)

Source of record: `the November 2 reference manuscript`, lines 276-288 ("It gives a
unique global mild solution in `BUC` ... It is also the finite-energy solution ... Uniqueness gives
`v(-q,-η,s) = -v(q,η,s)`").

`TrainUniqueness` (`StatementsTrain.lean`) is forward uniqueness within the class `IsBUCTrain`
(`TrainClass.lean`).  For `ν > 0`, `c ≥ 1` and two trains of the class, restrict both to
`[0, T]`, `T = s + 1`: they are classical solutions (`trainSol_isClassicalOn`) with bounded
derivatives (`IsBUCTrain`) and decaying pressure (`trainSol_pressureDecayOn`).  The classical-class
machinery of `Sub/T02_3.lean` (`ClassicalPressureBound`, `ClassicalEnergyBound`,
`ClassicalUniquenessBounded`) then gives uniform bounds on `v`, `p`, cell energy for each, and
uniqueness of bounded classical solutions with the same datum `trainDatum c`.

The conditional theorem `trainUniqueness_of` is the whole proof; the three hypotheses are the
`Prop`s of `Sub/T02_3.lean`, each with its own proof task (`PartI:T02/3/*`), also needed for
the oddness of the local train (`ClassicalOdd`).  This route does not use the earlier leaves of
`Sub/T05.lean` (`TrainLocalBounds` etc.), which are not derivable from `IsTrain`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`PartI:T05`, conditional form**: forward uniqueness of the train in the BUC class from the
three classical-class leaves of `Sub/T02_3.lean`. -/
theorem trainUniqueness_of (hP : ClassicalPressureBound) (hE : ClassicalEnergyBound)
    (hU : ClassicalUniquenessBounded) : TrainUniqueness := by
  intro ν c hν hc tr tr' hb hb' s hs
  set T : ℝ := s + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, by rw [hTdef]; linarith⟩
  have hcl := trainSol_isClassicalOn tr T
  have hcl' := trainSol_isClassicalOn tr' T
  have hbd : HasBoundedDerivsOn T tr.v := hb T hT.le
  have hbd' : HasBoundedDerivsOn T tr'.v := hb' T hT.le
  obtain ⟨Mp, hMp⟩ := hP ν c T tr.v tr.p hν hc hT hcl hbd (trainSol_pressureDecayOn tr T)
  obtain ⟨Mp', hMp'⟩ := hP ν c T tr'.v tr'.p hν hc hT hcl' hbd' (trainSol_pressureDecayOn tr' T)
  obtain ⟨Me, hMe⟩ := hE ν c T Mp tr.v tr.p hν hc hT hcl hbd hMp
  obtain ⟨Me', hMe'⟩ := hE ν c T Mp' tr'.v tr'.p hν hc hT hcl' hbd' hMp'
  obtain ⟨Mv, hMv⟩ := exists_sup_bound_of_hasBoundedDerivsOn hbd
  obtain ⟨Mv', hMv'⟩ := exists_sup_bound_of_hasBoundedDerivsOn hbd'
  set M : ℝ := max (max Mv Mv') (max (max Mp Mp') (max Me Me')) with hM
  have hB : ClassicalBoundedBy c T M tr.v tr.p := fun r hr =>
    ⟨fun w => (hMv r hr w).trans (by simp [hM]), fun w => (hMp r hr w).trans (by simp [hM]),
      (hMe r hr).trans (by simp [hM])⟩
  have hB' : ClassicalBoundedBy c T M tr'.v tr'.p := fun r hr =>
    ⟨fun w => (hMv' r hr w).trans (by simp [hM]), fun w => (hMp' r hr w).trans (by simp [hM]),
      (hMe' r hr).trans (by simp [hM])⟩
  exact hU ν c T M tr.v tr'.v tr.p tr'.p hν hc hT hcl hcl' hbd hbd' hB hB' s hsT

/-- **Time-local bounds of a train of the BUC class** (source lines 276-282: velocity and pressure
bounded, finite energy bounded on every `[0, S]`).  This is the statement `TrainLocalBounds` of
`Sub/T05.lean`, which is not derivable for an arbitrary `B0140.TrainSol`, restricted to the BUC
class; it is *derived* from the classical-class leaves `ClassicalPressureBound` (bounded periodic
pressure, from `Δp = -∂_iv_j∂_jv_i` and the decay of `p`) and `ClassicalEnergyBound` (cutoff energy
estimate). -/
def TrainLocalBoundsBUC : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ S : ℝ, 0 ≤ S →
    ∃ M : ℝ, TrainBoundedBy tr S M

/-- `TrainLocalBoundsBUC` from the pressure and energy leaves of `Sub/T02_3.lean`. -/
theorem trainLocalBoundsBUC_of (hP : ClassicalPressureBound) (hE : ClassicalEnergyBound) :
    TrainLocalBoundsBUC := by
  intro ν c hν hc tr hb S hS
  set T : ℝ := S + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hcl := trainSol_isClassicalOn tr T
  have hbd : HasBoundedDerivsOn T tr.v := hb T hT.le
  obtain ⟨Mp, hMp⟩ := hP ν c T tr.v tr.p hν hc hT hcl hbd (trainSol_pressureDecayOn tr T)
  obtain ⟨Me, hMe⟩ := hE ν c T Mp tr.v tr.p hν hc hT hcl hbd hMp
  obtain ⟨Mv, hMv⟩ := exists_sup_bound_of_hasBoundedDerivsOn hbd
  refine ⟨max (max Mv Mp) Me, fun s hs => ?_⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans (by rw [hTdef]; linarith)⟩
  exact ⟨fun z => (hMv s hsT z).trans (by simp), fun z => (hMp s hsT z).trans (by simp),
    (hMe s hsT).trans (by simp)⟩

end UnforcedLeray.Short.PartI
