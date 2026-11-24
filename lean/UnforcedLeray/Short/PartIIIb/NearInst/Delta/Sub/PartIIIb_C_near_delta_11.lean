import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_10

/-!
# Decomposition of `oldEndResponse_of` (item `PartIII-b:C/near/delta/11`)

Source of record `the November 2 reference manuscript`,
4015-4020.  The output region `s ≥ S = ε^{-b}` of `g⁻¹(S_N - S₀)g` is the `S_N` part, which is
exactly `Masked.MaskedUpperPiece` (`S_far = 0` there, gain ratio `exp{γ/[ν(1+νS)]}`, free energy),
plus the `S₀` part, bounded by `FlatFreeGainBound` (3420-3440) since `1_A` commutes with `g⁻¹` and
has norm `≤ 1` (`gainRestrS_norm_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The old end from the upper `S_N` piece and the flat free gain bound. -/
theorem oldEndResponse_of_pieces (hF : FlatFreeGainBound)
    (hU : UnforcedLeray.Short.PartIIIb.NearInst.Masked.MaskedUpperPiece) : OldEndResponse := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hU P hP Kset hK hKs mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C2, k2, ν2, hν2, h2⟩ := hF P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨|C1| + |C2|, k1 + k2, min (min ν1 ν2) 1, lt_min (lt_min hν1 hν2) one_pos, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ SN S0 hSN hS0
  have hν1' : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2' : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  exact gainRestrS_combine p.c mZ ρb P.eigenvalue.re p.ν_pos hν3 (measurableSet_ageAbove _) SN S0
    (h1 p d hreg hν1' ρb hρ hρ1 μ hμ SN hSN) (h2 p d hreg hν2' ρb hρ hρ1 μ hμ S0 hS0)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
