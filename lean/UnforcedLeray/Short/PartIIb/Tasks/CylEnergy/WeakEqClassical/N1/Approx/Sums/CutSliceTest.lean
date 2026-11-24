import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.EtaCutProps

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

theorem cutSliceTest : UnforcedLeray.Short.IIb.TdSums.CutSliceTest := by
  intro c t₀ t₁ R φ hR hφ r hr
  have hE : EtaCutProps := etaCutProps
  obtain ⟨C, -, hEc⟩ := hE
  obtain ⟨hEsm, hEx⟩ := hEc R hR
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : B0579.Plane => ((r, x) : ℝ × B0579.Plane)) :=
    contDiff_const.prodMk contDiff_id
  have hpairOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : B0579.Plane => ((r, x) : ℝ × B0579.Plane)) univ := hpair.contDiffOn
  have hslice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : B0579.Plane => φ r x) := by
    have hc := hφ.smooth.comp hpairOn
      (fun x _ => (⟨hr, mem_univ x⟩ : (r, x) ∈ Icc t₀ t₁ ×ˢ (univ : Set B0579.Plane)))
    exact contDiffOn_univ.1 hc
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutTest R φ r) := by
    unfold cutTest
    exact hEsm.mul hslice
  have hper : ∀ x : B0579.Plane, cutTest R φ r (x.1 + c, x.2) = cutTest R φ r x := by
    intro x
    unfold cutTest
    rw [(hEx x).2.2.2.2.1 (x.1 + c), hφ.periodic r hr x]
  have hband : ∃ R' : ℝ, ∀ x : B0579.Plane, R' < |x.2| → cutTest R φ r x = 0 := by
    refine ⟨2 * R, fun x hx => ?_⟩
    unfold cutTest
    rw [(hEx x).2.2.2.1 hx.le, zero_mul]
  exact { smooth := hsm, periodic := hper, band := hband }

end TdSums

end UnforcedLeray.Short.IIb
