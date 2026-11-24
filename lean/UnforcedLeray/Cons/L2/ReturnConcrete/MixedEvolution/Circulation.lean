import UnforcedLeray.Units.B0610

/-!
# The actual zero-circulation state space

This file defines the closed linear subspace of the weighted vorticity pivot on which the
B0583 cylinder Biot–Savart reconstruction is defined. Circulation is the pairing with the actual
constant test `oneH1`; via B0610 this is exactly the integral over the centered cell.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579

/-- The continuous circulation functional on the real weighted pivot `X_m`. -/
def circulationCLM {c m : ℝ} (hm : 1 / 2 < m) : X c m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (UnforcedLeray.B0610.oneH1 c m hm)).comp
    (UnforcedLeray.B0579.sourceCLM c m)

@[simp] theorem circulationCLM_apply {c m : ℝ} (hm : 1 / 2 < m) (w : X c m) :
    circulationCLM hm w = ∫ x in cell c, w x := by
  exact UnforcedLeray.B0610.sourceCLM_oneH1 hm w

/-- The physical zero-circulation state space, as the kernel of the actual circulation CLM. -/
def zeroCirculationSubmodule {c m : ℝ} (hm : 1 / 2 < m) : Submodule ℝ (X c m) :=
  (circulationCLM hm).toLinearMap.ker

/-- Membership in the state subspace is exactly vanishing of the physical cell integral. -/
theorem mem_zeroCirculationSubmodule_iff {c m : ℝ} (hm : 1 / 2 < m) (w : X c m) :
    w ∈ zeroCirculationSubmodule hm ↔ ∫ x in cell c, w x = 0 := by
  change circulationCLM hm w = 0 ↔ ∫ x in cell c, w x = 0
  rw [circulationCLM_apply]

/-- The kernel of circulation is a closed real subspace of `X_m`. -/
theorem isClosed_zeroCirculationSubmodule {c m : ℝ} (hm : 1 / 2 < m) :
    IsClosed ((zeroCirculationSubmodule hm : Submodule ℝ (X c m)) : Set (X c m)) := by
  change IsClosed {w : X c m | circulationCLM hm w = 0}
  exact isClosed_singleton.preimage (circulationCLM hm).continuous

#print axioms circulationCLM_apply
#print axioms isClosed_zeroCirculationSubmodule

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
