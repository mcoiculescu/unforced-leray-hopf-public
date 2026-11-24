import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1

/-!
# Axisymmetry of the Cartesian slice (`PartIII-b:C/near/masked/14/2/3/1/2`)

Source: `the November 2 reference manuscript`
3996-4011.  `cartSliceOut R δ S l g y` depends on `y` only through `(y₀²+y₁², y₂)`: a reflection
`ρ` in the hyperplane orthogonal to `y - y'` maps `y` to `y'`, preserves `z₂` and `z₀²+z₁²`, and
is measure preserving on `ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal Matrix

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The reflection in the hyperplane orthogonal to `u`, written in coordinates. -/
lemma la_reflection_apply (u z : Space) :
    (Submodule.orthogonal (Submodule.span ℝ {u})).reflection z =
      z - (2 * (inner ℝ u z / ‖u‖ ^ 2)) • u := by
  rw [Submodule.reflection_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton]
  module

/-- The reflection fixes the third coordinate and preserves `z₀² + z₁²` when `u₂ = 0`. -/
lemma la_reflection_coord (u z : Space) (hu2 : u 2 = 0) :
    ((z - (2 * (inner ℝ u z / ‖u‖ ^ 2)) • u) 2 = z 2) ∧
      (z - (2 * (inner ℝ u z / ‖u‖ ^ 2)) • u) 0 ^ 2 +
        (z - (2 * (inner ℝ u z / ‖u‖ ^ 2)) • u) 1 ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  have hN : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, hu2, Real.norm_eq_abs, sq_abs]
  have hi : inner ℝ u z = u 0 * z 0 + u 1 * z 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three, hu2]
    ring
  rw [hN, hi]
  constructor
  · simp [hu2]
  · by_cases h0 : u 0 ^ 2 + u 1 ^ 2 = 0
    · simp [h0]
    · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring

/-- A reflection `ρ` of `ℝ³` with `ρ y = y'`, fixing `z₂` and `z₀² + z₁²`. -/
lemma la_rho (y y' : Space) (hy : y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2) (hy2 : y 2 = y' 2) :
    ∃ ρ : Space ≃ₗᵢ[ℝ] Space, ρ y = y' ∧ (∀ z : Space, ρ z 2 = z 2) ∧
      (∀ z : Space, ρ z 0 ^ 2 + ρ z 1 ^ 2 = z 0 ^ 2 + z 1 ^ 2) := by
  have hn : ‖y‖ = ‖y'‖ := by
    have h1 : ‖y‖ ^ 2 = ‖y'‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
      rw [hy2]
      linarith [hy]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hu2 : (y - y') 2 = 0 := by simp [hy2]
  refine ⟨Submodule.reflection (Submodule.orthogonal (Submodule.span ℝ {y - y'})),
    Submodule.reflection_sub hn, fun z => ?_, fun z => ?_⟩
  · rw [la_reflection_apply]; exact (la_reflection_coord (y - y') z hu2).1
  · rw [la_reflection_apply]; exact (la_reflection_coord (y - y') z hu2).2

/-- The integrand of the slice at input `w` with age parameter `a`. -/
def laSliceJ (R δ l a : ℝ) (g : Space → ℝ) (w z : Space) : ℝ≥0∞ :=
  if Real.exp δ * a < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
    ENNReal.ofReal (‖w - l • z‖ ^ (-4 : ℝ) * g z)
  else 0

theorem sliceAxisym : UnforcedLeray.Short.PartIIIb.NearInst.Masked.SliceAxisym := by
  intro R δ S l g hg y y' hy hy2
  obtain ⟨ρ, hρy, hρ2, hρ01⟩ := la_rho y y' hy hy2
  have hg' : ∀ z, g (ρ z) = g z := fun z => hg (ρ z) z (hρ01 z) (hρ2 z)
  have hme : MeasurableEmbedding ρ := ρ.toHomeomorph.measurableEmbedding
  have hmp : ∀ G : Space → ℝ≥0∞, ∫⁻ z, G (ρ z) = ∫⁻ z, G z :=
    fun G => ρ.measurePreserving.lintegral_comp_emb hme G
  have hJrho : ∀ (a : ℝ) (w z : Space),
      laSliceJ R δ l a g (ρ w) (ρ z) = laSliceJ R δ l a g w z := by
    intro a w z
    unfold laSliceJ
    rw [hρ01 z]
    have hw : ρ w - l • ρ z = ρ (w - l • z) := by rw [map_sub, map_smul]
    rw [hw, LinearIsometryEquiv.norm_map, hg' z]
  have hJ : ∀ (a : ℝ) (w : Space),
      ∫⁻ z, laSliceJ R δ l a g (ρ w) z = ∫⁻ z, laSliceJ R δ l a g w z := by
    intro a w
    calc ∫⁻ z, laSliceJ R δ l a g (ρ w) z
        = ∫⁻ z, laSliceJ R δ l a g (ρ w) (ρ z) := (hmp _).symm
      _ = ∫⁻ z, laSliceJ R δ l a g w z := lintegral_congr fun z => hJrho a w z
  unfold cartSliceOut
  rw [hy]
  have hint : ∫⁻ z : Space,
      laSliceJ R δ l (R ^ 2 / (y' 0 ^ 2 + y' 1 ^ 2)) g y z =
      ∫⁻ z : Space, laSliceJ R δ l (R ^ 2 / (y' 0 ^ 2 + y' 1 ^ 2)) g y' z := by
    have := hJ (R ^ 2 / (y' 0 ^ 2 + y' 1 ^ 2)) y
    rw [hρy] at this
    exact this.symm
  split_ifs with hc
  · congr 1
  · rfl

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
