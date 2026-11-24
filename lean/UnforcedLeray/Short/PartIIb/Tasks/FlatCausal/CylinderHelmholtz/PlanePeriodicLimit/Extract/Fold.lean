import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.WeakLimit
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Group.Measure

/-!
# Part II-b, leaf `PartII-b:T12/1/4/2/4` (`PPLFold`): periodic fold

Source of record: `the November 2 reference manuscript` lines 1933-1935.
`Gp z = G (toIcoMod c 0 z.1, z.2)` is `c`-periodic; the exceptional set of `Gp ≠ G` is contained in
a countable union of translates of the null set `{G(· + c) ≠ G}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem pplFold : PPLFold := by
  unfold PPLFold
  intro c G hc hper
  set P : Set (ℝ × ℝ) := {z | G (z.1 + c, z.2) ≠ G z} with hPdef
  have hP : volume P = 0 := by
    have hN : ∀ M : ℕ, volume {z : ℝ × ℝ | ¬ (z ∈ ppWindow c M → G (z.1 + c, z.2) = G z)} = 0 := by
      intro M
      have h' : ∀ᵐ z ∂(volume.restrict (ppWindow c M)), G (z.1 + c, z.2) = G z := hper M
      rw [ae_restrict_iff' (measurableSet_ppWindow c M)] at h'
      exact ae_iff.1 h'
    refine measure_mono_null ?_ (measure_iUnion_null hN)
    intro z hz
    have hz' : z ∈ ⋃ M : ℕ, ppWindow c M := by
      rw [iUnion_ppWindow hc]; exact mem_univ z
    obtain ⟨M, hM⟩ := mem_iUnion.1 hz'
    exact mem_iUnion.2 ⟨M, fun h => hz (h hM)⟩
  have hQ : ∀ k : ℤ, volume {z : ℝ × ℝ | G (z.1 + k • c, z.2) ≠ G z} = 0 := by
    have hT : ∀ k : ℤ, volume ((fun z : ℝ × ℝ => z + (k • c, 0)) ⁻¹' P) = 0 := fun k => by
      rw [measure_preimage_add_right]; exact hP
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih =>
      refine measure_mono_null ?_ (measure_union_null ih (hT (i : ℤ)))
      intro z hz
      have hzt : ∀ k : ℤ, z + (k • c, 0) = (z.1 + k • c, z.2) := fun k => by ext <;> simp
      by_cases h : G (z.1 + (i : ℤ) • c, z.2) = G z
      · right
        show G ((z + ((i : ℤ) • c, 0)).1 + c, (z + ((i : ℤ) • c, 0)).2) ≠
          G (z + ((i : ℤ) • c, 0))
        rw [hzt]
        dsimp only
        have e : z.1 + ((i : ℤ) + 1 : ℤ) • c = z.1 + (i : ℤ) • c + c := by
          rw [add_smul, one_smul]; ring
        have hz2 : G (z.1 + ((i : ℤ) + 1 : ℤ) • c, z.2) ≠ G z := hz
        rw [e] at hz2
        intro h2
        exact hz2 (h2.trans h)
      · exact Or.inl h
    | pred i ih =>
      refine measure_mono_null ?_ (measure_union_null ih (hT (-(i : ℤ) - 1)))
      intro z hz
      have hzt : ∀ k : ℤ, z + (k • c, 0) = (z.1 + k • c, z.2) := fun k => by ext <;> simp
      by_cases h : G (z.1 + (-(i : ℤ)) • c, z.2) = G z
      · right
        show G ((z + ((-(i : ℤ) - 1) • c, 0)).1 + c, (z + ((-(i : ℤ) - 1) • c, 0)).2) ≠
          G (z + ((-(i : ℤ) - 1) • c, 0))
        rw [hzt]
        dsimp only
        have e : z.1 + (-(i : ℤ) - 1 : ℤ) • c + c = z.1 + (-(i : ℤ)) • c := by
          rw [sub_smul, one_smul]; ring
        have hz2 : G (z.1 + (-(i : ℤ) - 1 : ℤ) • c, z.2) ≠ G z := hz
        intro h2
        rw [e] at h2
        exact hz2 (h2.symm.trans h)
      · exact Or.inl h
  refine ⟨fun z => G (toIcoMod hc 0 z.1, z.2), ?_, ?_⟩
  · intro z
    simp only [toIcoMod_add_right]
  · have hsub : {z : ℝ × ℝ | (fun z : ℝ × ℝ => G (toIcoMod hc 0 z.1, z.2)) z ≠ G z} ⊆
        ⋃ k : ℤ, {z : ℝ × ℝ | G (z.1 + k • c, z.2) ≠ G z} := by
      intro z hz
      refine mem_iUnion.2 ⟨-(toIcoDiv hc 0 z.1), ?_⟩
      have e : toIcoMod hc 0 z.1 = z.1 + (-(toIcoDiv hc 0 z.1)) • c := by
        rw [neg_smul, ← sub_eq_add_neg, self_sub_toIcoDiv_zsmul]
      have hz2 : G (toIcoMod hc 0 z.1, z.2) ≠ G z := hz
      rw [e] at hz2
      exact hz2
    have hE : volume {z : ℝ × ℝ | (fun z : ℝ × ℝ => G (toIcoMod hc 0 z.1, z.2)) z ≠ G z} = 0 :=
      measure_mono_null hsub (measure_iUnion_null hQ)
    intro M
    exact ae_restrict_of_ae (ae_iff.2 hE)

end UnforcedLeray.Short.IIb
