import UnforcedLeray.Short.PartIIb.Sub.T12_2_6
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.QDecomposition

/-!
# Part II-b, task `PartII-b:T12/2/6/1`: the `H_r` norm only sees `s > 0`

Source of record: `the November 2 reference manuscript`, lines 1901-1903 and 1923-1926.

Target: `hrAeTransfer_proof : UnforcedLeray.Short.IIb.LerayLiftSub.HrAeTransfer`
(the Prop is in `Sub/T12_2_6.lean`, not changed here).

Proof: `hMeas c r = Axi.ageμ c (r/2 - 5/2)` is absolutely continuous with respect to Lebesgue measure
(`qd_ageμ_ac`), so the Lebesgue-a.e. hypothesis transfers to `ageμ`-a.e.; `ageμ` is carried by
`{s > 0}` (`Axi.ae_ageμ_mem`), so `F = F'` holds `ageμ`-a.e. and `eLpNorm_congr_ae` closes the goal.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem hrAeTransfer_proof : UnforcedLeray.Short.IIb.LerayLiftSub.HrAeTransfer := by
  intro c r F F' hc hFF'
  have hac : hMeas c r ≪ (volume : Measure Coord) := qd_ageμ_ac c (r / 2 - 5 / 2)
  have hae : ∀ᵐ x ∂(hMeas c r), 0 < x.1 → F x = F' x := hac.ae_le hFF'
  have hpos : ∀ᵐ x ∂(hMeas c r), x ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.Axi.qCell c :=
    Axi.ae_ageμ_mem hc (r / 2 - 5 / 2)
  have hEq : F' =ᵐ[hMeas c r] F := by
    filter_upwards [hae, hpos] with x hx1 hx2
    exact (hx1 hx2.1).symm
  unfold hNorm
  exact eLpNorm_congr_ae hEq

end UnforcedLeray.Short.IIb
