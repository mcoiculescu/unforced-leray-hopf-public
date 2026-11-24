import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/15` (`MollLimit`): weighted dominated convergence

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552 (limit `k → ∞` of the mollified energy identity, tested against a compactly supported
weight). Target: `lmWeightedDCT : LMWeightedDCT`.

Route. The support `K = tsupport wt` is compact and lies in `(0,∞)`, so it lies in some
`[s₁, s₂]` with `0 < s₁ < s₂` (its minimum and maximum). On `[s₁, s₂]` the dominating function
`g` is integrable, so `|wt| * g` is integrable there (continuity of `|wt|`), and it vanishes off
`[s₁, s₂]`, hence is integrable on `(0,∞)`. Then dominated convergence on `(0,∞)` applies to
`wt s * f k s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Dominated convergence against a continuous compactly supported weight in `(0,∞)`
(SP 3541-3552, the limit `k → ∞` of the mollified energy identity). -/
theorem lmWeightedDCT : LMWeightedDCT := by
  intro wt hwt hcs hts f f₀ g hmeas hgI hbound hlim
  have hK : IsCompact (tsupport wt) := hcs.isCompact
  obtain ⟨s₁, s₂, h0, h12, hsub⟩ : ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ s₁ < s₂ ∧
      tsupport wt ⊆ Icc s₁ s₂ := by
    rcases (tsupport wt).eq_empty_or_nonempty with he | hne
    · exact ⟨1, 2, one_pos, by norm_num, by rw [he]; exact empty_subset _⟩
    · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne continuousOn_id
      obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne continuousOn_id
      have hab : a ≤ b := isMinOn_iff.1 hmin b hb
      have ha0 : 0 < a := hts ha
      refine ⟨a, b + 1, ha0, by linarith, fun x hx => ⟨?_, ?_⟩⟩
      · have h1 : a ≤ x := isMinOn_iff.1 hmin x hx
        exact h1
      · have h2 : x ≤ b := isMaxOn_iff.1 hmax x hx
        linarith
  have hI : IntegrableOn g (Icc s₁ s₂) := hgI s₁ s₂ h0 h12
  have hbI : IntegrableOn (fun s => |wt s| * g s) (Icc s₁ s₂) :=
    IntegrableOn.continuousOn_mul hwt.abs.continuousOn hI isCompact_Icc
  have hbnd : IntegrableOn (fun s => |wt s| * g s) (Ioi (0 : ℝ)) := by
    refine IntegrableOn.of_forall_sdiff_eq_zero hbI measurableSet_Ioi ?_
    intro x hx
    have hxK : x ∉ tsupport wt := fun h => hx.2 (hsub h)
    show |wt x| * g x = 0
    rw [image_eq_zero_of_notMem_tsupport hxK, abs_zero, zero_mul]
  refine tendsto_integral_of_dominated_convergence (fun s => |wt s| * g s) (fun k => ?_) hbnd
    (fun k => ?_) ?_
  · exact hwt.aestronglyMeasurable.mul (hmeas k)
  · filter_upwards [hbound k] with s hs
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  · filter_upwards [hlim] with s hs
    exact hs.const_mul (wt s)

end UnforcedLeray.Short.IIIa
