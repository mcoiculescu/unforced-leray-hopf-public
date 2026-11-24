import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- `nsSym` is a function of `tv4`: the four components `(T_rr, T_rz, T_zz, T_φφ)` determine
`nsSym T` (`symRZ` is read off the `rz` entry of `tv4`). -/
theorem nsSym_eq_of_tv4 (T T' : Ten3) (h : tv4 T = tv4 T') : nsSym T = nsSym T' := by
  have h0 := congrArg (fun v => v 0) h
  have h1 := congrArg (fun v => v 1) h
  have h2 := congrArg (fun v => v 2) h
  have h3 := congrArg (fun v => v 3) h
  simp only [tv4, PiLp.toLp_apply] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  have e00 : T (0, 0) = T' (0, 0) := h0
  have erz : symRZ T = symRZ T' := h1
  have e22 : T (2, 2) = T' (2, 2) := h2
  have e11 : T (1, 1) = T' (1, 1) := h3
  unfold nsSym
  rw [e00, e11, e22, erz]

/-- **Leaf 1** (source 1645-1646, 2675, 2683): the stress pairing depends on `g` only through
`tv4`, a.e. for `ageμ c (-1/2)`. -/
theorem swStrTv4 : SWStrTv4 := by
  intro c ε hc hε g g' hg Φ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {p | tv4 (g p) ≠ tv4 (g' p)}) (μ := ageμ c (-1 / 2)) (ae_iff.1 hg)
  have hN5 : ageμ c (-5 / 2) N = 0 := ageμ_absCont c (-5 / 2) (-1 / 2) hN0
  have hnull := stressPairAE_null ε⁻¹ c (2 * ε * c) hR hc hP N hNm hN5
  have hae := Measure.ae_ae_of_ae_prod hnull
  unfold stressPair phaseInt
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  have hgg : tv4 (g (chartOf ε⁻¹ c y t)) = tv4 (g' (chartOf ε⁻¹ c y t)) := by
    by_contra h
    exact hy (hsub h)
  have : strPhys ε⁻¹ c g (t, y) = strPhys ε⁻¹ c g' (t, y) := by
    simp only [strPhys, cartLift]
    rw [nsSym_eq_of_tv4 _ _ hgg]
  simp only [this]

end UnforcedLeray.Short.PartIIIb.NearInst
