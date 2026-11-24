import UnforcedLeray.Short.PartI.Sub.PartI_S18_1

/-!
# `PartI:S18/1/1`: continuous compactly supported functions are dense in `L²_M`

Source `the November 2 reference manuscript`
lines 946-953.  Leaf `L2wCcDense` of `PartI_S18_1`.

Proof: `wMeasure M` is locally finite (`B0008`), hence regular on `ℂ` (σ-compact, pseudometrizable,
Borel), so Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` applies to `F : L²_M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartI

theorem l2wCcDense : L2wCcDense := by
  intro M hM F ε hε
  have hloc : IsLocallyFiniteMeasure (Planar.wMeasure M) :=
    inferInstanceAs (IsLocallyFiniteMeasure (B0008.wMeasure M))
  have : (Planar.wMeasure M).Regular := inferInstance
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  obtain ⟨g, hgc, hgerr, hgcont, hgmem⟩ :=
    (Lp.memLp F).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2:ℝ≥0∞) ≠ ∞) hδ
  refine ⟨hgmem.toLp g, ?_, ?_⟩
  · unfold IsCcRep
    exact ⟨g, hgcont, hgc, hgmem.coeFn_toLp⟩
  · have hae : (⇑(hgmem.toLp g) : ℂ → ℂ) =ᵐ[Planar.wMeasure M] g := hgmem.coeFn_toLp
    have hGF : eLpNorm (⇑(hgmem.toLp g - F)) 2 (Planar.wMeasure M)
        ≤ ENNReal.ofReal (ε / 2) := by
      calc eLpNorm (⇑(hgmem.toLp g - F)) 2 (Planar.wMeasure M)
          = eLpNorm (⇑(hgmem.toLp g) - ⇑F) 2 (Planar.wMeasure M) :=
            eLpNorm_congr_ae (Lp.coeFn_sub _ _)
        _ = eLpNorm (g - ⇑F) 2 (Planar.wMeasure M) :=
            eLpNorm_congr_ae (hae.sub Filter.EventuallyEq.rfl)
        _ = eLpNorm (⇑F - g) 2 (Planar.wMeasure M) := eLpNorm_sub_comm _ _ _ _
        _ ≤ ENNReal.ofReal (ε / 2) := hgerr
    rw [Lp.norm_def]
    exact (ENNReal.toReal_le_of_le_ofReal (by linarith) hGF).trans_lt (by linarith)

end UnforcedLeray.Short.PartI
