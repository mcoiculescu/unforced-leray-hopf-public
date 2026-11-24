import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels

/-!
# `PartIII-b:C/rep/8/2/2/3`: the smoothness `MeanSmooth` of the mean Newton field

Source `the November 2 reference manuscript`
5438-5448 (the mean field `X^mt` is `C^4` at every young receiver `y = (R/√s, 0, η/√s)`).

`X^mt` is `C^7` on `ℝ³` for old tensors with finite `N₀` (`xmtSmooth`, `SourceL/XmtSmooth.lean`);
the finiteness `OldThinFinite c ν (thinRep T)` comes from `sourceLN0` (`SourceL/N0.lean`), and the
standing hypotheses `LHyp` at the levels come from `SeqData.eventually_lHyp`
(`ReturnInst/AffineSource/Levels.lean`), with `RepairStanding` supplying its inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Smoothness of the mean Newton field at the young receivers** (source 5438-5448): the mean
field `X^mt` is `C^4` at every young receiver point, for large `n` and every `z ∈ [-1,1]`. -/
theorem meanSmooth (D : SeqData) {dm dp : ℝ} : D.MeanSmoothSeq dm dp := by
  intro hst
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY] with n hn
  intro z hz
  have h := hn z hz
  obtain ⟨C, k, hC⟩ := sourceLN0 D.K.mZ (gRate D.Pl) hst.mZ_gt hst.gamma_pos
  intro T p _ _
  have hfin := (hC (cOf (D.level n).ν) (D.level n).ν ((D.level n).ρb D.Pl D.K) h.c_pos
    h.nu_pos h.nu_le T).1
  have hX := xmtSmooth _ _ _ _ _ _ h (thinRep T) hfin
  exact hX.contDiffAt.of_le (by norm_num)

end UnforcedLeray.Short.PartIIIb.Concrete
end
