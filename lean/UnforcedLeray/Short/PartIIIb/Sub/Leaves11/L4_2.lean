import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.PsiRingSmooth

/-!
# `PartIII-b:C/inst/11/4` leaf 2: `PsipAContOn`

`ψ^p_A` is jointly `C²` on `{s > 0}` (`psiRingSmooth_proof`), hence continuous there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `PsipAContOn`: `ψ^p_A` is continuous on `{s > 0}`. -/
theorem psipAContOn (as : ℝ) (χf : ℝ → ℝ) : PsipAContOn as χf := by
  intro hχ ν hν A hA
  have hC : ContDiffOn ℝ 2 (psiRing ν χf A) (Ioi 0 ×ˢ univ) :=
    psiRingSmooth_proof as χf hχ ν hν A hA
  have hc : ContinuousOn (psiRing ν χf A) (Ioi 0 ×ˢ univ) := hC.continuousOn
  exact hc.mono fun p hp => ⟨Set.mem_Ioi.2 hp, Set.mem_univ _⟩

end UnforcedLeray.Short.PartIIIb.Concrete
