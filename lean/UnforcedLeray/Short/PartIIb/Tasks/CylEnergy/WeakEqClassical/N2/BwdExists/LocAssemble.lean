import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route

/-!
# Part II-b, task `PartII-b:T22/2/3/1/5` (`LocAssemble`): local regularity gives spatial smoothness

Source: `the November 2 reference manuscript` lines 2100-2105.  Pure topology: the
bands `band ρ = {|η| < ρ}` are open and every point lies in one of them with `ρ = |η| + 1`.  Local
`C^k` on that band gives `C^k` at the point, and local continuity of the iterated partials on
`[0, T] × band ρ` gives continuity on `[0, T] × ℝ²` (continuity within the product set at each
point, through the relative neighbourhood `[0, T] × ℝ²` of `(σ, x)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.BwdRoute

open CylPDE

/-- **Leaf `T22/2/3/1/5`**: local regularity of every order on every band gives spatial
smoothness (the bands are open and cover the plane). -/
theorem locAssemble : UnforcedLeray.Short.IIb.BwdRoute.LocAssemble := by
  intro T u h
  have hopen : ∀ ρ : ℝ, IsOpen (band ρ) := fun ρ => by
    unfold band
    exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  refine ⟨fun σ hσ => ?_, fun l => ?_⟩
  · rw [contDiff_infty]
    intro n
    rw [contDiff_iff_contDiffAt]
    intro x
    have hxb : x ∈ band (|x.2| + 1) := by
      show |x.2| < |x.2| + 1
      linarith
    have hk := (h (n + 2) (by omega) (|x.2| + 1)).slice σ hσ
    have hA := hk.contDiffAt ((hopen (|x.2| + 1)).mem_nhds hxb)
    exact hA.of_le (by exact_mod_cast (show n ≤ n + 2 by omega))
  · intro z hz
    have hzb : z.2 ∈ band (|z.2.2| + 1) := by
      show |z.2.2| < |z.2.2| + 1
      linarith
    have hk := (h (l.length + 2) (by omega) (|z.2.2| + 1)).cont l (by omega)
    have hw := hk z ⟨hz.1, hzb⟩
    refine hw.mono_of_mem_nhdsWithin ?_
    have hopenP : IsOpen (univ ×ˢ band (|z.2.2| + 1) : Set (ℝ × Pl)) :=
      isOpen_univ.prod (hopen _)
    have hzP : z ∈ (univ ×ˢ band (|z.2.2| + 1) : Set (ℝ × Pl)) := ⟨mem_univ _, hzb⟩
    have hnhds := inter_mem_nhdsWithin (Icc 0 T ×ˢ univ : Set (ℝ × Pl)) (hopenP.mem_nhds hzP)
    exact Filter.mem_of_superset hnhds (fun w hw' => ⟨hw'.1.1, hw'.2.2⟩)

end UnforcedLeray.Short.IIb.BwdRoute
