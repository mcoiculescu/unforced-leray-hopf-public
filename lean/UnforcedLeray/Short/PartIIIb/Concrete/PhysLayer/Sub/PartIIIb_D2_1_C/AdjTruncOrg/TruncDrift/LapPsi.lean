import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_2

/-!
# `LapPsi`: weak Laplacian of the stream potential, `Δψ = -curl Φ`

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
The identity is the `ν`-scaled statement `WeakLapPsi` (proved in
`Sub/PartIII-b_IIIb-D2_1_3_1_2_1_11_2.lean` as `weakLapPsi`): `ν ⟪ΔΘ, ψ⟫ = -ν ⟪Θ, curl Φ⟫`.
Dividing by `ν > 0` (the pairing of `nuLapT ν` with `ψ` is `ν` times the pairing of `lapT`)
gives `LapPsi`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- **Weak Laplacian of the stream potential** (source 1351-1362): `Δψ = -curl Φ` weakly,
with `curlD D = ∑ₖ eₖ × ∂ₖΦ` (see `Sub/PartIII-b_IIIb-D2_1_3_1_2_1_12.lean`). -/
theorem lapPsi : LapPsi := by
  intro P ν μ hP hP1 hν hμ D hD Θ hΘ
  have h2 : pairF P (nuLapT ν Θ) D.ψ = pairF P Θ (fun x => -ν • curlD D x) :=
    weakLapPsi P ν μ D hD Θ hΘ
  have hLHS : pairF P (nuLapT ν Θ) D.ψ = (ν : ℂ) * pairF P (lapT Θ) D.ψ :=
    wlp_pairF_const_smul P ν (lapT Θ) D.ψ
  have hR : pairF P Θ (fun x => -ν • curlD D x) = ((-ν : ℝ) : ℂ) * pairF P Θ (curlD D) :=
    wlp_pairF_const_smul_right P (-ν) Θ (curlD D)
  have hν' : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hν.ne'
  have key : (ν : ℂ) * pairF P (lapT Θ) D.ψ = (ν : ℂ) * (-pairF P Θ (curlD D)) := by
    rw [← hLHS, h2, hR]
    push_cast
    ring
  exact mul_left_cancel₀ hν' key

end UnforcedLeray.Short.PartIIIb.Concrete
