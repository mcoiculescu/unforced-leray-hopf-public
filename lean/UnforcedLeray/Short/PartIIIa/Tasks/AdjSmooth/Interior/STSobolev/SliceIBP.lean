import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.PerTestCyl
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.PerTestUnfold
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.PeriodicBoxBound

/-!
# `PartIII-a:T21/2/7/2/1/1/7/6`: integration by parts on a slice

Source: `the November 2 reference manuscript` lines 3060-3061.
For `c`-periodic `f, g` in `X_{-m,c}` with `HasWeakCellDerivC c i f g` and `θ ∈ C_c^∞(ℝ²)`,
`∫_{ℝ²} f ∂_iθ = -∫_{ℝ²} g θ`.  The periodization `ψ := perTest c θ` is a cylinder test
(`perTestCyl`), its derivative is the periodization of `∂_iθ`, and the plane integrals unfold to
the cell integrals against `ψ` and `∂_i ψ` (`perTestUnfold`).  Local integrability of `f, g` comes
from `periodicBoxBound` (an `L²` function on a finite-measure box is integrable there).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem sliceIBP : UnforcedLeray.Short.IIIa.SliceIBP := by
  intro c m i f g hc hpf hpg hf hg hW θ hθ hθc
  -- local integrability of a periodic `X_{-m,c}` function on the plane
  have hLI : ∀ u : ℝ × ℝ → ℂ, Periodic1 c u → MemLp u 2 (B0579.cellMeasure c (-m)) →
      LocallyIntegrable u volume := by
    intro u hp hu
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (continuous_fst.continuousOn)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_snd.continuousOn)
    have hsub : K ⊆ sliceBox (max A B) := by
      intro x hx
      have h1 : |x.1| ≤ A := by simpa [Real.norm_eq_abs] using hA x hx
      have h2 : |x.2| ≤ B := by simpa [Real.norm_eq_abs] using hB x hx
      have e1 := abs_le.1 (h1.trans (le_max_left A B))
      have e2 := abs_le.1 (h2.trans (le_max_right A B))
      exact Set.mem_prod.2 ⟨Set.mem_Icc.2 e1, Set.mem_Icc.2 e2⟩
    have hcpt : IsCompact (sliceBox (max A B)) := isCompact_Icc.prod isCompact_Icc
    have : IsFiniteMeasure (volume.restrict (sliceBox (max A B))) :=
      isFiniteMeasure_restrict.2 hcpt.measure_lt_top.ne
    obtain ⟨M, hMtop, hM⟩ := periodicBoxBound c m (max A B) hc
    obtain ⟨hmeasB, hbound⟩ := hM u hp hu.aestronglyMeasurable
    have hXne : xNorm c (-m) u < ⊤ := hu.eLpNorm_lt_top
    have hL2 : MemLp u 2 (volume.restrict (sliceBox (max A B))) :=
      ⟨hmeasB, lt_of_le_of_lt hbound (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hMtop) hXne)⟩
    have hI : IntegrableOn u (sliceBox (max A B)) := hL2.integrable (by norm_num)
    exact hI.mono_set hsub
  -- the derivative of the test function is compactly supported and smooth
  have hpdS : ContDiff ℝ ∞ (B0579.pd i θ) :=
    ((contDiff_infty_iff_fderiv.1 hθ).2).clm_apply contDiff_const
  have hpdC : HasCompactSupport (B0579.pd i θ) := hθc.fderiv_apply ℝ (B0579.dir i)
  -- unfold both plane integrals onto the cell
  obtain ⟨hIf, -, hEf⟩ := perTestUnfold c (B0579.pd i θ) f hc hpdS hpdC hpf (hLI f hpf hf)
  obtain ⟨hIg, -, hEg⟩ := perTestUnfold c θ g hc hθ hθc hpg (hLI g hpg hg)
  obtain ⟨hcyl, hcomm⟩ := perTestCyl c θ hc hθ hθc
  refine ⟨hIf, hIg, ?_⟩
  rw [hEf, hEg, ← hcomm i]
  unfold HasWeakCellDerivC at hW
  exact hW.2 (perTest c θ) hcyl

end UnforcedLeray.Short.IIIa
