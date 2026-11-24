import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2

/-!
# Part II-b, task `PartII-b:T22/2/2/1`: slices of a test are `CylSmoothDecay` (`rtdSlice`)

Source of record: `the November 2 reference manuscript`, lines 2100-2105.
The slice `y ↦ φ r y` is the composition of the joint smoothness on `Icc t₀ t₁ ×ˢ univ` with
`y ↦ (r, y)`, which maps `univ` into that set for `r ∈ Icc t₀ t₁`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem rtdSlice : UnforcedLeray.Short.IIb.RtdSlice := by
  intro c t₀ t₁ φ hφ r hr
  have hmap : MapsTo (fun y : B0579.Plane => (r, y)) univ (Icc t₀ t₁ ×ˢ univ) :=
    fun y _ => ⟨hr, mem_univ _⟩
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : B0579.Plane => (r, y)) :=
    contDiff_const.prodMk contDiff_id
  have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : B0579.Plane => φ r y) univ :=
    hφ.smooth.comp h2.contDiffOn hmap
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ r) := contDiffOn_univ.1 hcomp
  refine ⟨hc.of_le (by first | exact_mod_cast (le_top : (2:ℕ∞) ≤ ⊤) | simp | norm_num), fun x => hφ.periodic r hr x, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hφ.decay N
  exact ⟨C, fun x => hC r hr x⟩

end UnforcedLeray.Short.IIb
