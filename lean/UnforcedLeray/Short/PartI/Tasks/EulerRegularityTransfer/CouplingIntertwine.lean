import UnforcedLeray.Short.PartI.Sub.PartI_S13c_1
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE
import UnforcedLeray.Short.PartI.Tasks.TransportGroupHjM.Zero

/-!
# Part I, task `PartI:S13c/1/3`: the interaction on `H^j_M` intertwines `-couplingW`

Source of record: `the November 2 reference manuscript`,
lines 853-857.

The operator `Planar.couplingW` is the sector form of `A_E = -(Kf)·∇E₀`; the interaction
`B0009.perturbation f = (Kf)·∇E₀` is therefore `-couplingW f` (sign checked against `secProfAE`).
The statement `CouplingIntertwineHjM` was corrected accordingly (it had `+couplingW`, which is
false).  Proof: `perturbation g` is a.e. the value of `AEj 0 (ofL2 g)`, whose sector profiles are
`-couplingSec` of those of `g` (`secProfAE`); conclude with `Planar.eq_of_secProf`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem aeZero_neg_couplingW {M : ℝ} (hM : 1 < M) (g : Planar.L2w M) :
    (B0061.AEj 0 hM (TransportGroupHjMZero.ofL2 M g)).value = -Planar.couplingW hM g := by
  apply Planar.eq_of_secProf
  intro n
  rw [secProfAE hM n, map_neg, Planar.secProf_couplingW, TransportGroupHjMZero.value_ofL2]

theorem coupling_intertwine_HjM (j : ℕ) {M : ℝ} (hM : 1 < M) : CouplingIntertwineHjM j hM := by
  intro T₀ hT₀ F
  apply UnforcedLeray.B0062.L2w_eq_of_ae
  have h1 : ((B0061.AEj 0 hM (TransportGroupHjMZero.ofL2 M F.value)).value : ℂ → ℂ) =ᵐ[volume]
      B0009.perturbation (F.value : ℂ → ℂ) :=
    B0061.AEj_value_ae hM (TransportGroupHjMZero.ofL2 M F.value)
  have h2 := aeZero_neg_couplingW hM F.value
  filter_upwards [hT₀ F, h1] with y e1 e2
  rw [e1, ← e2, h2]

end UnforcedLeray.Short.PartI

end
