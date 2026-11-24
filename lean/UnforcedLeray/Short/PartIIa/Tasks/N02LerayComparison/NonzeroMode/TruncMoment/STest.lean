import UnforcedLeray.Short.PartIIa.Sub.N02_4_10

/-!
# Part II-a, task `PartII-a:N02/4/10/1` (`NtmSTest`): `S = s ∂_s` preserves smooth meridional tests

Target: `ntmSTest : NtmSTest` (`Sub/N02_4_10.lean`). Source of record:
`the November 2 reference manuscript`, lines 1744-1749.

Route: `opS f p = p.1 • fderiv f p (1,0,0)`.
* smoothness: `fderiv` of a smooth map is smooth; apply to a constant vector and multiply by `p.1`;
* periodicity: `fderiv f` is invariant under the shift `p ↦ p + (0, c, 0)` because `f` is;
* band: outside the closed box `[s₀, s₁] × [-L, L]` the map `f` vanishes near `p`, so its
  derivative there is zero.
Iterate with `Function.iterate_succ_apply'`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- `opS` preserves smoothness. -/
theorem stest_opS_smooth {f : Profile → MeridC} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (opS f) := by
  have hD : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ f p) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have h1 : ContDiff ℝ ∞ (fun p : Profile => fderiv ℝ f p (1, 0, 0)) :=
    hD.clm_apply contDiff_const
  exact contDiff_fst.smul h1

/-- `opS` preserves `q`-periodicity. -/
theorem stest_opS_periodic {c : ℝ} {f : Profile → MeridC} (hp : QPeriodic c f) :
    QPeriodic c (opS f) := by
  have hshift : ∀ x : Profile, x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) := by
    intro x
    ext <;> simp
  have hfun : (fun y : Profile => f (y + ((0 : ℝ), c, (0 : ℝ)))) = f := by
    funext y
    rw [hshift]
    exact hp y
  have hd : ∀ x : Profile, fderiv ℝ f (x + ((0 : ℝ), c, (0 : ℝ))) = fderiv ℝ f x := by
    intro x
    have h1 : fderiv ℝ (fun y : Profile => f (y + ((0 : ℝ), c, (0 : ℝ)))) x =
        fderiv ℝ f (x + ((0 : ℝ), c, (0 : ℝ))) := fderiv_comp_add_right _
    rw [hfun] at h1
    exact h1.symm
  intro p
  simp only [opS, pdS]
  rw [← hshift p, hd p]

/-- `opS` preserves the band: outside the closed box the map vanishes near `p`. -/
theorem stest_opS_band {f : Profile → MeridC} (s0 s1 L : ℝ)
    (hb : ∀ p : Profile, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∀ p : Profile, opS f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  intro p hp
  by_contra hnot
  apply hp
  have hBc : IsClosed {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L} := by
    apply IsClosed.inter
    · exact isClosed_Icc.preimage continuous_fst
    · exact isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd))
        continuous_const
  have hopen : IsOpen {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L}ᶜ := hBc.isOpen_compl
  have hev : f =ᶠ[𝓝 p] fun _ => (0 : MeridC) := by
    filter_upwards [hopen.mem_nhds hnot] with q hq
    by_contra hfq
    exact hq (hb q hfq)
  have hderiv : fderiv ℝ f p = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp [opS, pdS, hderiv]

/-- **`NtmSTest` (target).** -/
theorem ntmSTest : NtmSTest := by
  intro c hc f hf a
  induction a with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨s0, s1, L, hs0, hb⟩ := ih.band
    exact ⟨stest_opS_smooth ih.smooth, stest_opS_periodic ih.periodic,
      ⟨s0, s1, L, hs0, stest_opS_band s0 s1 L hb⟩⟩

end UnforcedLeray.Short.PartIIa
