import UnforcedLeray.Short.PartI.Sub.PartI_S15
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.SectorOne
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.GrowProjAgree
import UnforcedLeray.Short.PartI.Tasks.EulerComplementJ0.XjM0Bridge

/-!
# Part I, task `PartI:S15` (`SeedEulerComplement`, `j = 0`)

Assembly of the three leaves `PartI:S15/1` (`sectorOneStableAll`), `PartI:S15/2`
(`seedGrowProjAgree`) and `PartI:S15/3` (`xjM0Bridge`) through `seedEulerComplement_zero_of`
(Sub/PartI_S15.lean).  Source of record: `the November 2 reference manuscript`
lines 612-615 and 841-889.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **Target.** `SeedEulerComplement` at `j = 0`: the first complement estimate on `H^0_M = 𝒳_{0,M}`. -/
theorem seedEulerComplement_zero :
    ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M) (η : ℝ), 0 < η →
        ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ f : B0008.XjM 0 M,
          ∃ (u : Planar.L2w M) (g : B0008.XjM 0 M),
            (⇑u =ᵐ[volume] fun y => xValue f y - seedProjFun h (xValue f) y) ∧
            xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hM t u) ∧
            ‖g‖ ≤ C * Real.exp (η * t) * ‖f‖ :=
  seedEulerComplement_zero_of sectorOneStableAll seedGrowProjAgree xjM0Bridge

end UnforcedLeray.Short.PartI
