import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2

/-!
# Leaf 0: `ChartDecomp` (source 1675-1676)

Every `g ∈ H = HSpace c MeridC` splits as `g = g₁ + i g₂` with `g₁, g₂ ∈ H` of real chart form.
The real and imaginary parts of the meridional vector are taken pointwise (both are dominated by
the norm, so they lie in `L²(measureH c)`), and the chart representatives are obtained by the
inverse of the recentring `cellPt c` (`Masked.cellPtInv`).  The measure `measureH c` is carried
by the cell `q ∈ (0, c]`, on which `cellPtInv ∘ cellPt = id`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Axi

/-- Real part of a complex meridional vector, kept complex. -/
private def chReMer (z : MeridC) : MeridC := WithLp.toLp 2 fun i => (((z i).re : ℝ) : ℂ)

/-- Imaginary part of a complex meridional vector, kept complex. -/
private def chImMer (z : MeridC) : MeridC := WithLp.toLp 2 fun i => (((z i).im : ℝ) : ℂ)

private theorem chReMer_continuous : Continuous chReMer := by
  unfold chReMer
  fun_prop

private theorem chImMer_continuous : Continuous chImMer := by
  unfold chImMer
  fun_prop

private theorem chReMer_norm_le (z : MeridC) : ‖chReMer z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h : ‖chReMer z i‖ ≤ ‖z i‖ := by
    simp only [chReMer]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem chImMer_norm_le (z : MeridC) : ‖chImMer z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h : ‖chImMer z i‖ ≤ ‖z i‖ := by
    simp only [chImMer]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- `chReMer z + I • chImMer z = z`. -/
private theorem chReMer_add_chImMer (z : MeridC) :
    chReMer z + Complex.I • chImMer z = z := by
  ext i
  simp only [chReMer, chImMer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp

/-- The measure `measureH c` is carried by the cell `q ∈ (0, c]`. -/
private theorem measureH_cell (c : ℝ) :
    ∀ᵐ q ∂(measureH c), 0 < q.2.1 ∧ q.2.1 ≤ c := by
  have hcell : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    MeasurableSet.prod measurableSet_Ioi
      (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
  have h1 : ∀ᵐ q ∂(UnforcedLeray.B0220.cellMeasure c), q ∈ UnforcedLeray.B0220.cell c :=
    ae_restrict_mem hcell
  have hmeas : Measurable UnforcedLeray.B0220.weightH := by
    unfold UnforcedLeray.B0220.weightH
    fun_prop
  have h2 : ∀ᵐ q ∂(measureH c), q ∈ UnforcedLeray.B0220.cell c := by
    unfold measureH
    rw [ae_withDensity_iff hmeas]
    filter_upwards [h1] with q hq _
    exact hq
  filter_upwards [h2] with q hq
  exact ⟨hq.2.1.1, hq.2.1.2⟩

theorem chartDecomp : ChartDecomp := by
  intro p g
  have hsupp := measureH_cell p.c
  -- real and imaginary parts of `g` in `L²(measureH c)`
  have hF1 : MemLp (fun q => chReMer (g q)) 2 (measureH p.c) :=
    MemLp.of_le (Lp.memLp g)
      (chReMer_continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g))
      (Filter.Eventually.of_forall fun q => chReMer_norm_le _)
  have hF2 : MemLp (fun q => chImMer (g q)) 2 (measureH p.c) :=
    MemLp.of_le (Lp.memLp g)
      (chImMer_continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g))
      (Filter.Eventually.of_forall fun q => chImMer_norm_le _)
  -- chart representatives through the inverse recentring
  let f₁ : Chart → Merid := fun b =>
    WithLp.toLp 2 fun i => ((((g : Profile → MeridC)
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv p.c b)) i).re : ℝ)
  let f₂ : Chart → Merid := fun b =>
    WithLp.toLp 2 fun i => ((((g : Profile → MeridC)
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv p.c b)) i).im : ℝ)
  refine ⟨hF1.toLp _, hF2.toLp _, f₁, f₂, ?_, ?_, ?_⟩
  · unfold ChartRep
    filter_upwards [MemLp.coeFn_toLp hF1, hsupp] with q hq hqs
    have hinv := UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv_cellPt hqs.1 hqs.2
    rw [hq]
    simp only [f₁, merC, chReMer, hinv]
  · unfold ChartRep
    filter_upwards [MemLp.coeFn_toLp hF2, hsupp] with q hq hqs
    have hinv := UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv_cellPt hqs.1 hqs.2
    rw [hq]
    simp only [f₂, merC, chImMer, hinv]
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add (hF1.toLp _) (Complex.I • hF2.toLp _),
      Lp.coeFn_smul Complex.I (hF2.toLp _), MemLp.coeFn_toLp hF1, MemLp.coeFn_toLp hF2]
      with q h_add h_smul h1 h2
    rw [h_add, Pi.add_apply, h_smul, Pi.smul_apply, h1, h2]
    exact (chReMer_add_chImMer (g q)).symm

end UnforcedLeray.Short.PartIIIb.NearInst
