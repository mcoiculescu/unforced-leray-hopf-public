import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.RegularOfSmooth

/-!
# `PartIII-a:T21/c3/3/1/1/2/2/2/1`: `FreeAdjExists` from `FreeSpSmoothRep` and `FreePointwisePde`

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958,
3036-3037, and 3060-3073.

Assembles `Leaf2DualityNeeded.FreeAdjExists` for all `0 < ν` and `8 < m` from the two focused
parabolic leaves:
* `FreeSpSmoothRep` (`PartIII-a:T21/c3/3/1/1/2/2/2/1/1`): spatially `C^∞` `c`-periodic
  representative on `[t, s)` with jointly continuous spatial partials from all-order `AdjHkOn`
  (via `cellMollTendsto`, `adjSpatial_cellMoll_jet`, and `supBddByXNorm`);
* `FreePointwisePde` (`PartIII-a:T21/c3/3/1/1/2/2/2/1/2`): pointwise backward free PDE within
  `[t, b]` (`b ∈ (t, s)`) for that representative (via `cellIBP`, `tr.isTrain.solenoidal`, FTC,
  and `wkPeriodize`).

Weak Volterra existence (`freeAdjWeak_exists`), endpoint case (`freeAdjExists_eq`), differentiated
weak pairing (`freeTestedDeriv`), all-order spatial Sobolev bootstrap (`freeHkAllOrders`),
joint `C^∞` upgrade (`freeJointSmooth_of_spPde` via `BwdRoute.fwdJointSmooth_proved`), and
regular flow assembly (`freeAdjointFlow_of_smooth` via `smoothAeJet`) are all proved unconditionally
for all `0 < ν` in `FreeAdjExists/{Weak,HkStep,RegularOfSmooth}.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded

/-- **Conditional assembly of `FreeAdjExists`** (`PartIII-a:T21/c3/3/1/1/2/2/2/1`, SP 2937-2958,
3060-3073) from `FreeSpSmoothRep` and `FreePointwisePde`. -/
theorem freeAdjExists_of (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ)
    (h1 : ∀ s, FreeSpSmoothRep (ν ^ (-2 : ℝ)) m t₁ s)
    (h2 : ∀ s, FreePointwisePde ν m tr t₁ s) :
    FreeAdjExists ν m tr t₁ t₂ :=
  freeAdjExists_of_spPde ν m tr t₁ t₂ (fun s _ => h1 s) (fun s _ => h2 s)

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded
