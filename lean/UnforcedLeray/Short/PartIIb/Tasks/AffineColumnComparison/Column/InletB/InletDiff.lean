import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# Part II-b, task `PartII-b:G4/3/4/3` (`InletProfileDiffAt`)

Source of record: `the November 2 reference manuscript`, lines 2360-2366.
The inlet profile `p.inletProfile i = ringStreamProfile p.R (p.cutStream i)` is `C^∞` (the same
argument as `inletContDiff`), hence differentiable at every point.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- **Differentiability of the inlet profiles** (`InletProfileDiffAt`): the profile is `C^∞`. -/
theorem inletProfileDiffAt : UnforcedLeray.Short.IIb.InletProfileDiffAt := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, N, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hSig' hmode i m
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ∀ k : Fin 2, ContDiff ℝ ∞ (p.frozenStream k) :=
    fun k => inletCD_frozenStream hP hmode k
  have hH : 0 < p.H := div_pos p.ageCut_pos p.ν_pos
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul ((hfro i).comp contDiff_snd)
  have hB : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact inletCD_ringStreamProfile hcut
  exact hB.differentiable (by simp) m

end UnforcedLeray.Short.IIb
