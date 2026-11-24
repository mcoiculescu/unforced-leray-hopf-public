import UnforcedLeray.Blueprint.Package
import UnforcedLeray.MainReduction

/-!
# The two independent halves of the proof of Theorem A (final interface)

`paper/main.tex` proves Theorem A (lines 74–105) from
* `prop:unstable-background` (lines 150–191; blueprint B1034), proved in the completion
  section (lines 13714–13745; B1033);
* `thm:localization` (statement lines 232–260, proof lines 262–592; B1035);
* the viscosity transport `eq:viscosity-one-transport` (lines 597–617; B1036), compiled as
  `UnforcedLeray.mainClaim_of_viscosityMainClaim` in `MainReduction.lean`.

`LocalizationClaim` takes the background package as its hypothesis and
concludes `ViscosityMainClaim`. `ConstructionClaim` supplies that package.
The viscosity transport then gives `MainClaim`.



The root module contains the unconditional theorem.
-/

set_option autoImplicit false

namespace UnforcedLeray.Blueprint

/-- `thm:localization` (lines 232–260) for every package, concluding `ViscosityMainClaim`. -/
def LocalizationClaim : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ViscosityMainClaim

/-- `prop:unstable-background` (lines 150–191). -/
def ConstructionClaim : Prop :=
  ∃ D : BackgroundData, IsUnstableBackground D

/-- Theorem A from the two halves and the compiled viscosity transport (lines 614–617,
13741–13745). -/
theorem mainClaim_of_localization_construction (hL : LocalizationClaim)
    (hC : ConstructionClaim) : MainClaim := by
  obtain ⟨D, hD⟩ := hC
  exact mainClaim_of_viscosityMainClaim (hL D hD)

end UnforcedLeray.Blueprint
