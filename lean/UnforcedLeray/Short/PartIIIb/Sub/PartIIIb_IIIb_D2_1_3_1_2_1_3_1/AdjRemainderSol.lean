import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1.AdjRemainderSolMem

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem adjRemainderSol : AdjRemainderSol := by
  intro P ν μ hP _ hν hμ Φ g a b hdom ha_mem hb_mem ha hb
  exact adjRemainderSol_of_mem P ν μ hP Φ g a b hdom ha_mem hb_mem ha hb

end UnforcedLeray.Short.PartIIIb.Concrete
