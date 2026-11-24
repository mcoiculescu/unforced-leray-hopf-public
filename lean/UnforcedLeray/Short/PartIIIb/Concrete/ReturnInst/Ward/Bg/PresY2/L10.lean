import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The Leray complement is a contraction on `L²` (source 5246-5247)

`I - 𝐏` is the orthogonal projection onto the orthogonal complement of the solenoidal subspace,
so it has norm at most one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`I - 𝐏` is a contraction on `L²`** (`lerayComplNormLe_proved`). -/
theorem lerayComplNormLe_proved : LerayComplNormLe := by
  intro F
  have hperp : Submodule.starProjection
      (Submodule.orthogonal UnforcedLeray.Leray.solenoidalSubspace) F =
      F - Submodule.starProjection UnforcedLeray.Leray.solenoidalSubspace F :=
    Submodule.starProjection_orthogonal_val (K := UnforcedLeray.Leray.solenoidalSubspace) F
  have hle : ‖Submodule.starProjection
      (Submodule.orthogonal UnforcedLeray.Leray.solenoidalSubspace) F‖ ≤ ‖F‖ :=
    Submodule.norm_starProjection_apply_le
      (K := Submodule.orthogonal UnforcedLeray.Leray.solenoidalSubspace) F
  rw [hperp] at hle
  exact hle

end UnforcedLeray.Short.PartIIIb.Concrete
