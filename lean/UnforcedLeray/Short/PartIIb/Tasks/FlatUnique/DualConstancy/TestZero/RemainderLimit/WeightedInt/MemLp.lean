import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4_2

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/2/2`: `dualG ∈ L^{r'}` of the slab

Source: `the November 2 reference manuscript` lines 1923-1927.
`dualG` is the order-`≤ 3` jet of `g(σ,·) = H(s-σ,·)` cut to `tsupport χ`; the reflection
`(σ,p) ↦ (s-σ,p)` carries `ageμ c 0` on `[a,a']` to `ageμ c 0` on `[s-a',s-a]`, where
`HeatSol.deriv_memLp` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

instance dualMemLp_sfinite (c : ℝ) : SFinite (UnforcedLeray.Cyl.avgμ c) := by
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  infer_instance

/-- `ageμ c 0` on a slab `[a,a'] × ℝ²` with `a > 0` is `dσ|_{[a,a']} ⊗ avgμ c`. -/
theorem dualMemLp_ageμ_restrict (c a a' : ℝ) (ha : 0 < a) :
    (Axi.ageμ c 0).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))) =
      ((volume : Measure ℝ).restrict (Icc a a')).prod (UnforcedLeray.Cyl.avgμ c) := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ).restrict (Ioi 0))
    (ν := UnforcedLeray.Cyl.avgμ c) (Icc a a') univ
  have hI : Icc a a' ∩ Ioi (0 : ℝ) = Icc a a' :=
    inter_eq_left.2 (fun x hx => lt_of_lt_of_le ha hx.1)
  rw [Measure.restrict_univ, Measure.restrict_restrict measurableSet_Icc, hI] at h
  unfold Axi.ageμ
  simp only [Real.rpow_zero, ENNReal.ofReal_one, withDensity_const, one_smul]
  exact h.symm

/-- The reflection `(σ,p) ↦ (s-σ,p)` carries the slab measure on `[a,a']` to that on `[s-a',s-a]`. -/
theorem dualMemLp_reflect (c s a a' : ℝ) (ha : 0 < a) (has : a' < s) (haa : a ≤ a') :
    MeasurePreserving (fun z : Coord => (s - z.1, z.2))
      ((Axi.ageμ c 0).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))))
      ((Axi.ageμ c 0).restrict (Icc (s - a') (s - a) ×ˢ (univ : Set (ℝ × ℝ)))) := by
  have hs : 0 < s - a' := by linarith
  have hsa : 0 < s - a := by linarith
  rw [dualMemLp_ageμ_restrict c a a' ha, dualMemLp_ageμ_restrict c (s - a') (s - a) hs]
  have h1 : MeasurePreserving (fun t : ℝ => s - t) (volume : Measure ℝ) volume :=
    Measure.measurePreserving_sub_left volume s
  have h2 : MeasurePreserving (fun t : ℝ => s - t)
      ((volume : Measure ℝ).restrict (Icc a a'))
      ((volume : Measure ℝ).restrict (Icc (s - a') (s - a))) := by
    have hemb : MeasurableEmbedding (fun t : ℝ => s - t) :=
      (Homeomorph.subLeft s).measurableEmbedding
    have := h1.restrict_preimage_emb hemb (Icc (s - a') (s - a))
    have hp : (fun t : ℝ => s - t) ⁻¹' Icc (s - a') (s - a) = Icc a a' := by
      ext t; simp only [mem_preimage, mem_Icc]; constructor <;> intro h <;> constructor <;>
        linarith [h.1, h.2]
    rwa [hp] at this
  exact h2.prod (MeasurePreserving.id (UnforcedLeray.Cyl.avgμ c))

/-- First-coordinate negation as a linear isometry of `Coord` (sup norm). -/
def dualNegFst : Coord ≃ₗᵢ[ℝ] Coord where
  toFun z := (-z.1, z.2)
  invFun z := (-z.1, z.2)
  map_add' a b := by ext <;> simp <;> ring
  map_smul' k a := by ext <;> simp
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  norm_map' z := by simp [Prod.norm_def]

theorem dualMemLp_norm_eq (H : Coord → ℝ) (s : ℝ) (n : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖ =
      ‖iteratedFDeriv ℝ n H (s - x.1, x.2)‖ := by
  have hf : (fun z : Coord => H (s - z.1, z.2)) =
      (fun w : Coord => H (w + (s, (0 : ℝ × ℝ)))) ∘ dualNegFst := by
    funext z
    show H (s - z.1, z.2) = H ((-z.1, z.2) + (s, (0 : ℝ × ℝ)))
    congr 1
    ext <;> simp [sub_eq_neg_add]
  rw [hf, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, iteratedFDeriv_comp_add_right]
  congr 3
  ext <;> simp [dualNegFst, sub_eq_neg_add]

theorem dualGMemLp : UnforcedLeray.Short.IIb.DualGMemLp := by
  intro c r ν H s χ a a' hc hν hr hs hH hχ ha haa has hsub
  set S : Set Coord := Icc a a' ×ˢ (univ : Set (ℝ × ℝ)) with hS
  have hMP := dualMemLp_reflect c s a a' ha has haa
  have hs' : 0 < s - a' := by linarith
  have hW : MemLp (fun x : Coord => ∑ n ∈ Finset.range 4, ‖iteratedFDeriv ℝ n H x‖)
      (ENNReal.ofReal (r / (r - 1)))
      ((Axi.ageμ c 0).restrict (Icc (s - a') (s - a) ×ˢ (univ : Set (ℝ × ℝ)))) := by
    have := memLp_finsetSum' (Finset.range 4) (fun n hn =>
      (hH.deriv_memLp n (by have := Finset.mem_range.1 hn; omega) (s - a') (s - a) hs'
        (by linarith)).norm)
    simpa [Finset.sum_fn] using this
  have hW2 := hW.comp_measurePreserving hMP
  have hW3 : MemLp (fun x : Coord => ∑ n ∈ Finset.range 4,
        ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖)
      (ENNReal.ofReal (r / (r - 1))) ((Axi.ageμ c 0).restrict S) := by
    refine hW2.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Function.comp, dualMemLp_norm_eq]
  have hind : Measurable fun x : Coord => (tsupport χ).indicator (fun _ => (1 : ℝ)) x.1 :=
    (measurable_const.indicator (isClosed_tsupport χ).measurableSet).comp measurable_fst
  have hmeas : AEStronglyMeasurable (dualG χ H s) ((Axi.ageμ c 0).restrict S) :=
    hind.aestronglyMeasurable.mul hW3.aestronglyMeasurable
  refine hW3.mono hmeas (Eventually.of_forall fun x => ?_)
  have hnn : 0 ≤ ∑ n ∈ Finset.range 4,
      ‖iteratedFDeriv ℝ n (fun z : Coord => H (s - z.1, z.2)) x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold dualG
  by_cases hx : x.1 ∈ tsupport χ
  · simp [hx, abs_of_nonneg hnn]
  · simp [hx]

end UnforcedLeray.Short.IIb
