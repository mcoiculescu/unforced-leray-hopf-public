import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/3/8`: the transport integration by parts for `E_1`

Source: `the November 2 reference manuscript`, lines 2954-2956 (transport preserves
the weight up to bounded errors) and 3068-3069. The helpers are in
`Sub/PartIIIa_T21_2_2_3_8.lean`: the field `G_j = w V_j |∂_kΦ|²` is `C¹` and `d`-periodic in `y₁`,
`div G = (V·∇w + w div V)|Φ_k|² + 2 w Re(conj Φ_k V·∇Φ_k)` has zero cell integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem e1TransportIBP (m : ℝ) (hm : 8 < m) (hW : UnforcedLeray.Short.IIIa.PeriodicWeightLogBounds) :
    UnforcedLeray.Short.IIIa.AdjE1.E1TransportIBP m := by
  intro d CV V Φ hd hV hVp hVb hlo hhi k
  obtain ⟨CW, hCW⟩ := hW (-m)
  have hb := (hCW d hd).1
  exact transport_ibp_gen d hd (periodicWeight (-m) d) CW CV V (pdCx k Φ)
    ((pw_contDiff _ _).of_le (by exact_mod_cast le_top)) (pw_periodic _ _ hd.ne')
    (fun y => (pw_pos _ _ y).le) (fun y l => pw_pd_abs_le (-m) d CW hb l y) hV hVp hVb
    (pdCx_contDiff hlo.smooth k) (pdCx_periodic d hlo.periodic k) (hlo.int1 k)
    (fun l => hhi.int2 l k)

end UnforcedLeray.Short.IIIa.AdjE1
