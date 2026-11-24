import UnforcedLeray.Short.PartIIb.Sub.T12_2_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePerCylTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePerFDeriv

/-!
# Part II-b, task `PartII-b:T12/2/6/2`: the periodized planar test is a cell solenoidal test

Source of record: `the November 2 reference manuscript` (SP 1923-1926). Proves the Prop
`SlicePerSolTest` of `Sub/T12_2_6.lean`. Each component is a cell test by `SlicePerCylTest`; the
divergence of the periodized field is the periodization of `∂_qΨ_0 + ∂_ηΨ_1 = 0` by `SlicePerFDeriv`,
and the two periodization series are finitely supported, so they add termwise.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

/-- The `q`-periodization series of a compactly supported function is summable (finitely many
nonzero terms): the nonzero terms have `|n| c` bounded by `R + |x.2.1|`. -/
theorem slicePer_summable {c : ℝ} (hc : 0 < c) {ζ : Coord → ℝ} (hcs : HasCompactSupport ζ)
    (x : Coord) : Summable (fun n : ℤ => ζ (x.1, (x.2.1 - n * c, x.2.2))) := by
  obtain ⟨R, hR⟩ := pcell_bound_gen hcs (fun y : Coord => y.2.1) (by fun_prop)
  apply summable_of_ne_finset_zero (s := Finset.Icc (-⌈(R + |x.2.1|) / c⌉) ⌈(R + |x.2.1|) / c⌉)
  intro n hn
  by_contra hne
  apply hn
  have h1 : |x.2.1 - (n : ℝ) * c| ≤ R := hR _ hne
  have h2 := abs_sub_abs_le_abs_sub ((n : ℝ) * c) x.2.1
  have h3 : |x.2.1 - (n : ℝ) * c| = |(n : ℝ) * c - x.2.1| := abs_sub_comm _ _
  rw [abs_mul, abs_of_pos hc] at h2
  have h4 : |(n : ℝ)| * c ≤ R + |x.2.1| := by linarith
  exact pcell_mem_window hc h4

theorem slicePerSolTest_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SlicePerSolTest := by
  intro c Ψ hc hΨ s
  refine ⟨fun i => slicePerCylTest_proof c (fun x => Ψ x i) hc (hΨ.smooth i).smooth
    (hΨ.smooth i).compact s, ?_⟩
  intro z
  have hd0 := slicePerFDeriv_proof c (fun x => Ψ x 0) hc (hΨ.smooth 0).smooth
    (hΨ.smooth 0).compact s z (1, 0)
  have hd1 := slicePerFDeriv_proof c (fun x => Ψ x 1) hc (hΨ.smooth 1).smooth
    (hΨ.smooth 1).compact s z (0, 1)
  show fderiv ℝ (fun y => pcellPer c (fun x => Ψ x 0) (s, y)) z (1, 0) +
      fderiv ℝ (fun y => pcellPer c (fun x => Ψ x 1) (s, y)) z (0, 1) = 0
  rw [hd0, hd1]
  have hA := slicePer_summable hc (HasCompactSupport.fderiv_apply ℝ (hΨ.smooth 0).compact ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) (s, z)
  have hB := slicePer_summable hc (HasCompactSupport.fderiv_apply ℝ (hΨ.smooth 1).compact ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) (s, z)
  have hT := hA.tsum_add hB
  have hterm : ∀ n : ℤ,
      fderiv ℝ (fun x => Ψ x 0) (s, (z.1 - n * c, z.2)) (0, (1, 0)) +
        fderiv ℝ (fun x => Ψ x 1) (s, (z.1 - n * c, z.2)) (0, (0, 1)) = 0 := by
    intro n
    exact hΨ.div_free (s, (z.1 - n * c, z.2))
  unfold pcellPer
  rw [← hT]
  simp only [hterm, tsum_zero]

end UnforcedLeray.Short.IIb.LerayLiftSub
