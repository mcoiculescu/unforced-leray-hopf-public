import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.GaussMul
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.HpASum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.GhpAEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_5.PhpAGrowth

/-!
# `PartIII-b:C/asrc/ra/5/5` : joint `C²` regularity of `h^p_A` (target `hpAC2`)

Source 4973, 4978, 5076-5079.  Closes the target `hpAC2` by applying the reduction `hpAC2_of`
(in `PartIII-b_C_asrc_ra_5_5`) to the four sub-results: the lattice-sum form `hpASum_proof`,
the Gaussian-factor identity `ghpA_eq_proof`, the polynomial growth `phpA_growth_proof`, and the
Gaussian multiplier bound `gaussMulHbd_proof 2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Joint `C²` regularity of `h^p_A`** on `s > 0` (source 4973, 4978, 5076-5079). -/
theorem hpAC2 (as : ℝ) (χf : ℝ → ℝ) : HpAC2 as χf :=
  hpAC2_of as χf hpASum_proof ghpA_eq_proof (phpA_growth_proof as χf) (gaussMulHbd_proof 2)

end UnforcedLeray.Short.PartIIIb.Concrete
