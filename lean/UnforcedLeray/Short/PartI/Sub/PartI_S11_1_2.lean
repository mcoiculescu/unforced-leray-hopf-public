import UnforcedLeray.Short.PartI.Sub.PartI_S11_1
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Zero

/-!
# Part I, task `PartI:S11/1/2`: `smoothSectorSumsDense` reduced to two analytic leaves (conditional)

Source of record: `the November 2 reference manuscript`, lines 841-889
(sector decomposition of `L²_M`, radial profiles on `(0,∞)`).

`SmoothSectorSumsDense` (`Sub/PartI_S11_1.lean`) says that the elements of `H^0_M` whose value is a
finite sum `∑_{m∈F} w_m(r) e^{imϑ}` with `w_m` smooth and compactly supported in `(0,∞)` are dense.
Split:

* `SmoothProfDense` (leaf `PartI:S11/1/2/1`): `C_c^∞((0,∞))` is dense in the radial profile space
  `ProfL2 M = L²((0,∞), profileMeasure M)`;
* `SmoothSectorSumsDenseL2` (leaf `PartI:S11/1/2/2`, uses the first): the finite smooth sector sums
  are dense in `L²_M` (finite truncation of `Planar.hasSum_secEmb_secProf` and the isometries
  `Planar.secEmb`);
* the transport to `H^0_M` through the isometry `value`/`ofL2` is proved here:
  `smoothSectorSumsDense_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Leaf `PartI:S11/1/2/1`** (source lines 841-889): smooth compactly supported profiles in
`(0,∞)` are dense in `ProfL2 M`, `1 < M`.  Proof: `profileMeasure M` is `withDensity` of
`volume.restrict (Ioi 0)` with a locally bounded density, hence a Borel measure finite on
compacts of `(0,∞)`; continuous compactly supported functions in `(0,∞)` are dense
(`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`, `Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`,
after cutting off near `0` and `∞` by dominated convergence, finite total mass being not needed). -/
def SmoothProfDense : Prop :=
  ∀ {M : ℝ}, 1 < M → Dense {h : Planar.ProfL2 M | IsSmoothCptProfile M h}

/-- **Leaf `PartI:S11/1/2/2`** (source lines 841-889): finite smooth sector sums are dense in
`L²_M`.  Proof: for `g ∈ L²_M` the finite sector truncation `∑_{m∈F} secEmb m (secProf m g)` tends
to `g` along finsets (`Planar.hasSum_secEmb_secProf`); approximate each `secProf m g` by a smooth
compact profile (`SmoothProfDense`) and use that `secEmb m` is a linear isometry. -/
def SmoothSectorSumsDenseL2 : Prop :=
  ∀ {M : ℝ}, 1 < M → Dense (SmoothSectorSums M)

/-- The density in `H^0_M` (`SmoothSectorSumsDense`) from the density in `L²_M`: `H^0_M ≅ L²_M`
through `value` / `ofL2`. -/
theorem smoothSectorSumsDense_of (h : SmoothSectorSumsDenseL2) : SmoothSectorSumsDense := by
  intro M hM
  have hd := h hM
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨s, hs, hsm⟩ := (Metric.dense_iff.1 hd) f.value r hr
  refine ⟨TransportGroupHjMZero.ofL2 M s, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, TransportGroupHjMZero.norm_eq_value_zero]
    have : (TransportGroupHjMZero.ofL2 M s - f).value = s - (show Planar.L2w M from f.value) := rfl
    rw [this]
    exact lt_of_eq_of_lt (dist_eq_norm s _).symm hs
  · show (TransportGroupHjMZero.ofL2 M s).value ∈ SmoothSectorSums M
    exact hsm

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.smoothSectorSumsDense_of
