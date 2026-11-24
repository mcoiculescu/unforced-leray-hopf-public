import UnforcedLeray.Short.PartIIa.StatementsRing

/-!
# Part II-a, `seed-train/ring-lift.tex`: composition

Proposition `sct:lift` (source lines 1204-1239) follows from its step statements:
* the exactly solenoidal stream lift (lines 1243-1246) and the discrete self-similarity
  (line 1316-1318) are *proved here* from the compiled units `B0185`, `B0190`;
* the residual bound (`sct:residual-bound`) follows from the late residual table, the bounded
  early coefficients and the similarity integration step (`RingResidualFromTable`);
* axis smoothness, bounded derivatives and the inlet are the remaining step statements.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190

/-- **Exact solenoidality of the lift** (lines 1243-1246): proved from `B0185`. -/
theorem ringSolenoidal : RingSolenoidal := by
  intro R hR ψ r z t hr hψ
  exact cylDivergence_lift_eq_zero R (ne_of_gt (by linarith)) ψ z t hr hψ

/-- **Discrete self-similarity and period `2c/R`** (lines 1215-1217, 1316-1318): proved from
`B0190`. -/
theorem ringDSS : RingDSS := by
  intro R c ψ p hR hψ hp
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  exact ⟨fun t ht y => liftVelocity_dss hR0 hψ ht y, fun t ht y => liftPressure_dss hR0 hp ht y,
    fun τ => simProfile_liftVelocity_periodic hR0 hψ τ,
    fun τ => simProfile_liftPressure_periodic hR0 hp τ⟩

/-- The residual bound follows from the table, the early bound and the integration step. -/
theorem ringResidualBound_of_table (hl : RingLateTable) (he : RingEarlyBound)
    (hint : RingResidualFromTable) : RingResidualBound :=
  hint hl he

/-- **Proposition `sct:lift`** from its step statements (lines 1204-1239): everything except
solenoidality and discrete scaling is supplied by the remaining step statements. -/
theorem ringLiftProposition_of_parts (hax : RingAxisSmooth) (hbd : RingBoundedDerivs)
    (hres : RingResidualBound) (hin : RingInlet) : RingLiftProposition :=
  ⟨ringSolenoidal, ringDSS, hax, hbd, hres, hin⟩

/-- **Proposition `sct:lift`** from the table, the early bound, the integration step and the
remaining step statements. -/
theorem ringLiftProposition_of_table (hl : RingLateTable) (he : RingEarlyBound)
    (hint : RingResidualFromTable) (hax : RingAxisSmooth) (hbd : RingBoundedDerivs)
    (hin : RingInlet) : RingLiftProposition :=
  ringLiftProposition_of_parts hax hbd (ringResidualBound_of_table hl he hint) hin

end UnforcedLeray.Short.PartIIa
