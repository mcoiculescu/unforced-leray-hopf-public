import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.U
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Du
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu

/-!
# `GEQMem`: assembly of the three clauses (source 1515-1531, 2385-2387, 2531)

`GEQMem` is the conjunction of `gEQMem_u` (`u ∈ L^{2q₀}_loc`), `gEQMem_du` (`D u ∈ L^{2q₀}_loc`)
and `gEQMem_ddu` (`D²u ∈ L^{q₀}_loc`).  Each is a `GERegime` statement; the three small
thresholds are combined by taking the minimum.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Integrability** (source 2531, 1515-1531, 2385-2387): `u ∈ L^{2q₀}` on the cell (indeed
`L^∞` by `PartIIa.graphSupEmbedding`/`commonBodyGraphBound`, `cw_mem_X`, `X_le_D`, plus the
bounded inlet), `D u ∈ L^{2q₀}`, and `D²u ∈ L^{q₀}` on the cell. -/
theorem gEQMem : GEQMem := by
  intro lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := gEQMem_u lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := gEQMem_du lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := gEQMem_ddu lam q hq dm dp hdm
  refine ⟨min n1 (min n2 n3), lt_min hn1 (lt_min hn2 hn3), ?_⟩
  intro p d hreg hν hmode z g hd h hh
  have e1 : p.ν ≤ n1 := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ n2 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ n3 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨H1 p d hreg e1 hmode z g hd h hh, H2 p d hreg e2 hmode z g hd h hh,
    H3 p d hreg e3 hmode z g hd h hh⟩

end UnforcedLeray.Short.PartIIIb.Concrete
