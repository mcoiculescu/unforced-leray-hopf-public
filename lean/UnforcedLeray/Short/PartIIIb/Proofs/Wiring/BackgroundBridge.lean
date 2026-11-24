import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Sub.PartIIIb_IIIb_D5_bridge_1
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.BackgroundBridge.PoincareSmooth
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.BackgroundBridge.PoincareGradAndConst
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.BackgroundBridge.SliceWeakGradAndDiv

/-!
# Part III-b, task `PartIII-b:IIIb-D5/bridge` — Assembly of `Wiring.backgroundBridge`

Source of record: `the November 2 reference manuscript`, lines 117-118,
2026-2037, 2316-2318, 2505-2561, 2607-2612, 2641-2642, 2664-2713, 4139-4141, 5134-5139.

Assembles `backgroundBridge` from `backgroundBridge_of`, `shortBgExactProfile_of`, and the three
proved leaves `poincareIntervalSmooth_proof`, `weakGradPoincareRecovery_proof`, and
`smoothSolenoidalAndStressGrad_proof`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring

theorem backgroundBridge : UnforcedLeray.Short.PartIIIb.Concrete.Wiring.BackgroundBridge :=
  backgroundBridge_of
    (shortBgExactProfile_of
      poincareIntervalSmooth_proof
      weakGradPoincareRecovery_proof
      smoothSolenoidalAndStressGrad_proof)

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring
