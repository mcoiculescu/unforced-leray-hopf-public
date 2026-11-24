import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2.HeatKTop
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_1_2_3.L2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.OrderClosed

/-!
# Joint smoothness of the heat-Leray kernel (`PartIII-b:IIIb-D2/3/2/11/2/2/2/3/1`)

Source of record: `the November 2 reference manuscript`
3597-3610.  `K_t(x) = t^{-3/2} K_1(t^{-1/2} x)` for `t > 0` (`HeatLerayScale`), and `K_1` is `C^∞`
(`heatLerayKSmoothTop`), so `(t,x) ↦ K_t(x)` is `C^∞` on `t > 0` (`HeatLerayKJointSmoothTop`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Target** `PartIII-b:IIIb-D2/3/2/11/2/2/2/3/1`: `(t,x) ↦ (K_t)_{ij}(x)` is jointly `C^∞` on
`t > 0`. -/
theorem heatLerayKJointSmoothTop : HeatLerayKJointSmoothTop := by
  intro i j q hq
  have hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => IIIa.heatLerayK 1 i j x) :=
    heatLerayKSmoothTop 1 one_pos i j
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ × Space => r.1 ^ (-(3 / 2 : ℝ))) q :=
    ContDiffAt.rpow_const_of_ne contDiffAt_fst hq.ne'
  have hs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ × Space => (Real.sqrt r.1)⁻¹ • r.2) q :=
    ((contDiffAt_fst.sqrt hq.ne').inv (Real.sqrt_pos.2 hq).ne').smul contDiffAt_snd
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ × Space => IIIa.heatLerayK 1 i j ((Real.sqrt r.1)⁻¹ • r.2)) q :=
    hK.contDiffAt.comp q hs
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ × Space => r.1 ^ (-(3 / 2 : ℝ)) * IIIa.heatLerayK 1 i j ((Real.sqrt r.1)⁻¹ • r.2)) q :=
    hA.mul hB
  have hopen : IsOpen {r : ℝ × Space | 0 < r.1} := isOpen_lt continuous_const continuous_fst
  have hEv : (fun r : ℝ × Space => IIIa.heatLerayK r.1 i j r.2) =ᶠ[𝓝 q]
      (fun r : ℝ × Space => r.1 ^ (-(3 / 2 : ℝ)) * IIIa.heatLerayK 1 i j ((Real.sqrt r.1)⁻¹ • r.2)) := by
    filter_upwards [hopen.mem_nhds hq] with r hr
    exact heatLerayScale_of heatGTailScale r.1 hr i j r.2
  exact hG.congr_of_eventuallyEq hEv

end UnforcedLeray.Short.PartIIIb.Concrete
