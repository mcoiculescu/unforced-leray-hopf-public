import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Every word of length `≤ 4` lies in `budgetWords` (source 5076-5079). -/
theorem mem_budgetWords_of_length_le (w : List (Fin 3)) (h : w.length ≤ 4) :
    w ∈ budgetWords := by
  unfold budgetWords
  refine Finset.mem_biUnion.2 ⟨w.length, Finset.mem_range.2 (by omega), ?_⟩
  exact Finset.mem_image.2 ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

/-- The `s`-derivative, `q`-derivative and `η`-derivative of a chart function along the `η`-axis
of the slice `y ↦ (s, y)` (the `Kop` identity, source 4979). -/
theorem kop_chart_eq (F : Chart → ℝ) (s : ℝ) (x : ℝ × ℝ) (hF : DifferentiableAt ℝ F (s, x)) :
    Kop (fun s' y => F (s', y)) s x
      = x.2 * UnforcedLeray.Axi.dEta F (s, x) + 2 * s * UnforcedLeray.Axi.dS F (s, x) := by
  have hin : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : Chart))
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => F (s, y))
      ((fderiv ℝ F (s, x)).comp ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) x :=
    hF.hasFDerivAt.comp x hin
  have hl : HasDerivAt (fun t : ℝ => ((t, x) : Chart)) ((1 : ℝ), (0 : ℝ × ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h2 : HasDerivAt (fun t : ℝ => F (t, x)) (fderiv ℝ F (s, x) (1, (0 : ℝ × ℝ))) s :=
    hF.hasFDerivAt.comp_hasDerivAt s hl
  have e1 : (fderiv ℝ F (s, x)).comp ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
      (ei 1) = fderiv ℝ F (s, x) (0, (0, 1)) := by
    simp [ei]
  simp only [Kop]
  rw [h1.fderiv, h2.deriv, e1]
  rfl


/-- The meridional norm of `toMer (0, a)` is `|a|` (used for the `Θ` bound). -/
theorem norm_toMer_zero (a : ℝ) : ‖toMer (0, a)‖ = |a| := by
  unfold toMer
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]
  rw [Real.sqrt_sq_eq_abs]

end UnforcedLeray.Short.PartIIIb.Concrete
