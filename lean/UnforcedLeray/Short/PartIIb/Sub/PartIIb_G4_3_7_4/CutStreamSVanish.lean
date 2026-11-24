import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets

/-!
# Part II-b, task `PartII-b:G4/3/7/4/2` (`CutStreamSVanish`)

Source of record: `the November 2 reference manuscript`, lines 2316-2317, 2360-2366.
On `{m.1 < H/4}` the age cutoff is identically one, so the cut stream agrees with the frozen
stream `ψ_i(m.2)` in a neighbourhood of `x` whenever `x.1 < -(H/2)`; its `s`-derivative at `x`
is then the `s`-derivative of a function independent of `s`, which is zero.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

theorem cutStreamSVanish : UnforcedLeray.Short.IIb.CutStreamSVanish := by
  intro lam q hq p hmode hc1 hH i x hx
  have hopen : IsOpen {m : ℝ × (ℝ × ℝ) | m.1 < p.H / 4} := isOpen_lt continuous_fst continuous_const
  have hmem : x ∈ {m : ℝ × (ℝ × ℝ) | m.1 < p.H / 4} := by
    show x.1 < p.H / 4
    linarith
  have hev : p.cutStream i =ᶠ[𝓝 x] (fun m : ℝ × (ℝ × ℝ) => p.frozenStream i m.2) := by
    filter_upwards [hopen.mem_nhds hmem] with m hm
    have hm' : m.1 ≤ p.H / 4 := le_of_lt hm
    simp only [Params.cutStream, ageCutoff_eq_one hH hm', one_mul]
  rw [hev.fderiv_eq]
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfroCD : ContDiff ℝ ∞ (p.frozenStream i) := cutJets_frozenStream_cd hP hmode i
  have h1 : HasFDerivAt (p.frozenStream i) (fderiv ℝ (p.frozenStream i) x.2) x.2 :=
    ((hfroCD.differentiable (by simp)) x.2).hasFDerivAt
  have hd : HasFDerivAt (fun m : ℝ × (ℝ × ℝ) => p.frozenStream i m.2)
      ((fderiv ℝ (p.frozenStream i) x.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    HasFDerivAt.comp x h1 (hasFDerivAt_snd)
  rw [hd.fderiv]
  exact map_zero (fderiv ℝ (p.frozenStream i) x.2)

end UnforcedLeray.Short.IIb
