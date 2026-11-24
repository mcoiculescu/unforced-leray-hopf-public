import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.EtaQSupSeq

/-!
# `PartIII-b:C/rep/4/1/org/2/1`: the box leaf of the thin-source/thin-receiver far column

Source `the November 2 reference manuscript` 5342-5355, 5573-5594, 5303-5311,
3902-3920.

The proof is in `Box/`:

* `Box/Minkowski.lean`: Minkowski over the atoms `(λ, z)` of the separated kernel and the
  translation invariance of the periodic `L²_τ` norm (`minkowski_shift_disk`);
* `Box/Slice.lean`: phase average = cell average (`slice_avg`), the disk integral
  `∫_D s‖g(s,·,η)‖_{L²_q} dz = πR²N₀(a)` (`disk_mass`);
* `Box/Pointwise.lean`: the separated pointwise velocity
  `farPt ≤ 18|C|((1-θ)R/√s)^{-4}πR²N₀(e^δ s)` (`farPt_le`), from `fpd_sepWfar_le`;
* `Box/AgeIntegral.lean`: `∫_0^S s^{-3/2}E²(Ks²(a^{-3/4}+a^{-1/2})Z)² ≤ 4E²K²S^{5/2}Z²`;
* `Box/Assembly.lean`: `farThinThinBox_of`, `FarThinThinBox` (`k₀ = 2`) from the coefficient bound
  `EtaQSupSeq` of `stress-short:coefficients` (source 2713-2721), via the thin multiplier
  `frk_thinMultUng_level`, `farOutChartQ`, `farPt_le`, `thinMassBoundSlice` and `age_integral`.

The only input not proved here is `EtaQSupSeq dm dp` (task `PartIII-b:C/rep/4/4/1/org/7/1/8`,
`theorem etaQSupSeq (dm dp : ℝ) : EtaQSupSeq dm dp`), the fourth clause of
`IIIa.StressCoefficients` at the actual levels.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **The box leaf, given the coefficient bound** (source 5342-5355, 5573-5594, 2713-2721):
`farThinThinBox Pl σ₀ mZ dm dp` is `farThinThinBox_of Pl σ₀ mZ dm dp (etaQSupSeq dm dp)`. -/
theorem farThinThinBox_of_etaQSupSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hE : EtaQSupSeq dm dp) : FarThinThinBox Pl σ₀ mZ dm dp :=
  farThinThinBox_of Pl σ₀ mZ dm dp hE

/-- **The box leaf** (source 5342-5355, 5573-5594, 2713-2721). -/
theorem farThinThinBox (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarThinThinBox Pl σ₀ mZ dm dp :=
  farThinThinBox_of_etaQSupSeq Pl σ₀ mZ dm dp (etaQSupSeq dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete

end
