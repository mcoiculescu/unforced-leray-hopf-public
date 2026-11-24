import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# Part II-b, task `PartII-b:T10/6/1/6` (`DriftNoSwirl/Leaf6`): `GActInYr`

Source of record: `the November 2 reference manuscript`, lines 1912-1915.

The action `(gAct g f)(t,y) = gC g (f (t, g⁻¹ y))` preserves `Y_r`: the map `(t,y) ↦ (t,g⁻¹ y)`
preserves Lebesgue measure, so a.e. periodicity and measurability transfer; `gC g` is unitary on
`ℂ³`, so the pointwise norm is unchanged and the `y`-integral is invariant.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

namespace GActInYrHelp

/-- `(t, y) ↦ (t, g⁻¹ y)` preserves Lebesgue measure on `ℝ × ℝ³`. -/
lemma mp_fun (g : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (fun x : ℝ × Space => (x.1, g.symm x.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod g.symm.measurePreserving

/-- `‖a realC p + i b realC q‖² = ‖p‖² + ‖q‖²`. -/
lemma sq_decomp (p q : Space) :
    ‖B0412.realC p + Complex.I • B0412.realC q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [B0412.realC_apply, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
  ring

/-- `gC g` is isometric on `ℂ³`. -/
lemma gC_norm (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : ‖B0412.gC g v‖ = ‖v‖ := by
  obtain ⟨a, b, hv⟩ : ∃ a b : Space, v = B0412.realC a + Complex.I • B0412.realC b :=
    ⟨WithLp.toLp 2 (fun i => (v i).re), WithLp.toLp 2 (fun i => (v i).im), by
      ext i
      simp [B0412.realC_apply]
      apply Complex.ext <;> simp⟩
  have h2 : ‖B0412.gC g v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [hv, map_add, map_smul, B0412.gC_realC, B0412.gC_realC, sq_decomp, sq_decomp]
    simp only [LinearIsometryEquiv.norm_map]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

lemma gC_enorm (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) :
    ‖B0412.gC g v‖ₑ = ‖v‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, gC_norm]

/-- The action preserves `Y_r`. -/
lemma gAct_inYr (P r : ℝ) (g : Space ≃ₗᵢ[ℝ] Space) (f : ℝ × Space → CVec3)
    (hf : IsInYr P r f) : IsInYr P r (gAct g f) := by
  refine ⟨?_, ?_, ?_⟩
  · have hq := (mp_fun g).quasiMeasurePreserving.ae hf.periodic
    filter_upwards [hq] with x hx
    have hx' : f (x.1 + P, g.symm x.2) = f (x.1, g.symm x.2) := hx
    show B0412.gC g (f (x.1 + P, g.symm x.2)) = B0412.gC g (f (x.1, g.symm x.2))
    rw [hx']
  · have h1 : AEStronglyMeasurable (fun x : ℝ × Space => f (x.1, g.symm x.2)) volume :=
      hf.meas.comp_quasiMeasurePreserving (mp_fun g).quasiMeasurePreserving
    exact (B0412.gC g).continuous.comp_aestronglyMeasurable h1
  · have key : ∀ t : ℝ, ∫⁻ y, ‖gAct g f (t, y)‖ₑ ^ r = ∫⁻ y, ‖f (t, y)‖ₑ ^ r := by
      intro t
      have hemb : MeasurableEmbedding g.symm := g.symm.toHomeomorph.measurableEmbedding
      have h1 : ∀ y, ‖gAct g f (t, y)‖ₑ ^ r = ‖f (t, g.symm y)‖ₑ ^ r := by
        intro y
        show ‖B0412.gC g (f (t, g.symm y))‖ₑ ^ r = _
        rw [gC_enorm]
      simp_rw [h1]
      exact g.symm.measurePreserving.lintegral_comp_emb hemb (fun y => ‖f (t, y)‖ₑ ^ r)
    have hP : phaseLpNorm P r (gAct g f) = phaseLpNorm P r f := by
      unfold phaseLpNorm
      simp only [key]
    rw [hP]
    exact hf.finite

end GActInYrHelp

/-- **`GActInYr`**: the action `g·` preserves `Y_r`. -/
theorem gActInYr : UnforcedLeray.Short.IIb.GActInYr := by
  intro P r g f _ hf
  exact GActInYrHelp.gAct_inYr P r g f hf

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gActInYr
