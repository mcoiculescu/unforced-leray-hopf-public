import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.IntegratedH1
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.H1Gronwall

/-!
# `PartIII-a:T21/2/7/2/2`: `AdjointWeakH1` from the integrated energy and the Gronwall step

Source: `the November 2 reference manuscript` (SP) lines 3060-3071.
Assembly of `adjointWeakH1_of` (`Sub/PartIII-a_T21_2_7_2_2.lean`) from `adjointIntegratedH1`
(`Tasks/AdjSmooth/IntegratedH1.lean`) and `adjointH1Gronwall` (`Tasks/AdjSmooth/H1Gronwall.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjointWeakH1 (m : ℝ) (hm : 8 < m) : AdjointWeakH1 m :=
  adjointWeakH1_of m (adjointIntegratedH1 m hm) (adjointH1Gronwall m hm)

end UnforcedLeray.Short.IIIa
