import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_4
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.Polar
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.BInt
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.SigmaL1.Pointwise

/-!
# `sigmaM_l1` (source 4766-4775, 4924-4927)

The four sub-statements `SigmaMeas`, `SigmaPointwise`, `PlanePolar`, `PhaseBInt` are proved in the
helper modules `SigmaL1/{Meas,Pointwise,Polar,BInt}`; this file concludes by `sigmaM_l1_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sigmaM_l1 (c ν : ℝ) (χo : ℝ → ℝ) (hc : 0 < c) (hν : 0 < ν) (hχ : IsOutwardCutoff χo) (M : Chart → Mat3) (hM : OldThinFinite c ν M) : (∀ x' : ℝ × ℝ, ν * (5 / 6) < x'.1 ^ 2 + x'.2 ^ 2 → sigmaM c ν χo M x' = 0) ∧ Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x') ∧ ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') ≤ Real.pi * oldN0 c ν M :=
  sigmaM_l1_of sigmaMeas sigmaPointwise planePolar phaseBInt c ν χo hc hν hχ M hM

end UnforcedLeray.Short.PartIIIb.Concrete
