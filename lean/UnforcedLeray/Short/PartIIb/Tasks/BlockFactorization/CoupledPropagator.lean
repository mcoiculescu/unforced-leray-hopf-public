import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.MildDuhamel
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.ZeroCirculation
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CoupledPropagator.WeakDuhamel

/-!
# PartII-b:F2/2 — Coupled Cylinder Propagator Existence &Norm Bounds

The shared infrastructure and the reduction of `CoupledPropagatorStep` to three leaf propositions
are in `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_F2_2»`:
- `MildDuhamelEvolutionStep` (`PartII-b:F2/2/1`)
- `FreeAndInteractionZeroCircStep` (`PartII-b:F2/2/2`)
- `MildDuhamelWeakStep` (`PartII-b:F2/2/3`)
-/

theorem coupledPropagatorStep_proof : UnforcedLeray.Short.IIb.CoupledPropagatorStep :=
  UnforcedLeray.Short.IIb.coupledPropagatorStep_of
    mildDuhamelEvolutionStep_proof
    freeAndInteractionZeroCircStep_proof
    mildDuhamelWeakStep_proof
