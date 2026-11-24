import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs
import UnforcedLeray.Lib.AxisymmetricB.Average

/-!
# Azimuthal reduction of the physical densities (source 121-124, 2681-2688)

For a field `f` that is axisymmetric without swirl in the pointwise sense `AxiNoSwirlPt f`, the
norms of `f`, `Df` and `D²f` are invariant under the rotation about `e₃` that moves a point `y`
into the meridional half plane `{y₁ = 0, y₀ ≥ 0}`, i.e. to `(ϱ y, 0, y₂)`.  The proof uses the
rotation `rotZ θ` with `θ = arg (y₀ + i y₁)`, the identity `f = g ∘ f ∘ g⁻¹` for every `g` fixing
`e₃`, and the chain rule for linear isometry equivalences (no differentiability is needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Postcomposition with a linear isometry equivalence preserves the operator norm. -/
theorem axiDens_norm_left {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (f : E →L[ℝ] F) : ‖(e : F →L[ℝ] G).comp f‖ = ‖f‖ :=
  ContinuousLinearMap.opNorm_linearIsometryEquiv_comp e f

/-- Precomposition with a linear isometry equivalence preserves the operator norm. -/
theorem axiDens_norm_right {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F →L[ℝ] G) (e : E ≃ₗᵢ[ℝ] F) : ‖f.comp (e : E →L[ℝ] F)‖ = ‖f‖ :=
  ContinuousLinearMap.opNorm_comp_linearIsometryEquiv f e

/-- Conjugation `B ↦ g ∘ B ∘ g⁻¹` on continuous linear maps of `Space`, as a linear isometry
equivalence (it preserves the operator norm). -/
def axiDensConj (g : Space ≃ₗᵢ[ℝ] Space) :
    (Space →L[ℝ] Space) ≃ₗᵢ[ℝ] (Space →L[ℝ] Space) where
  toFun B := (g : Space →L[ℝ] Space).comp (B.comp (g.symm : Space →L[ℝ] Space))
  invFun B := (g.symm : Space →L[ℝ] Space).comp (B.comp (g : Space →L[ℝ] Space))
  map_add' B C := by ext x; simp
  map_smul' c B := by ext x; simp
  left_inv B := by ext x; simp
  right_inv B := by ext x; simp
  norm_map' B := (axiDens_norm_left g _).trans (axiDens_norm_right B g.symm)

/-- Chain rule for a conjugation by a linear isometry equivalence on the outside and on the
domain.  No differentiability is assumed: both sides are computed by the equivalence lemmas. -/
theorem axiDens_fderiv_conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : Space ≃ₗᵢ[ℝ] Space) (ψ : V ≃ₗᵢ[ℝ] V) (h : Space → V) (y : Space) :
    fderiv ℝ (fun x => ψ (h (g.symm x))) y =
      (ψ : V →L[ℝ] V).comp ((fderiv ℝ h (g.symm y)).comp (g.symm : Space →L[ℝ] Space)) := by
  have e1 : (fun x => ψ (h (g.symm x))) = (⇑ψ ∘ fun x => h (g.symm x)) := rfl
  have e2 : (fun x => h (g.symm x)) = (h ∘ ⇑(g.symm.toContinuousLinearEquiv)) := by
    ext x; simp
  rw [e1, LinearIsometryEquiv.comp_fderiv, e2, ContinuousLinearEquiv.comp_right_fderiv]
  simp

/-- For every `y` there is a rotation `R_θ` about `e₃` carrying the meridional point
`(ϱ y, 0, y₂)` to `y`. -/
theorem axiDens_exists_rot (y : Space) :
    ∃ θ : ℝ, UnforcedLeray.Axi.rotZ θ (WithLp.toLp 2 ![Axi.ϱ y, 0, y 2]) = y := by
  set z : ℂ := ⟨y 0, y 1⟩ with hz
  have hnorm : ‖z‖ = Axi.ϱ y := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rfl
  have hc : Axi.ϱ y * Real.cos (Complex.arg z) = y 0 := by
    have := Complex.norm_mul_cos_arg z
    rw [hnorm] at this
    exact this
  have hs : Axi.ϱ y * Real.sin (Complex.arg z) = y 1 := by
    have := Complex.norm_mul_sin_arg z
    rw [hnorm] at this
    exact this
  refine ⟨Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · simp [UnforcedLeray.Axi.rotZ_apply, UnforcedLeray.Axi.rotFun_apply_zero]
    linear_combination hc
  · simp [UnforcedLeray.Axi.rotZ_apply, UnforcedLeray.Axi.rotFun_apply_one]
    linear_combination hs
  · simp [UnforcedLeray.Axi.rotZ_apply, UnforcedLeray.Axi.rotFun_apply_two]

theorem axiDens_azimuth {f : Space → Space} (hf : AxiNoSwirlPt f) (y : Space) : ‖f y‖ = ‖f (WithLp.toLp 2 ![Axi.ϱ y, 0, y 2])‖ ∧ ‖fderiv ℝ f y‖ = ‖fderiv ℝ f (WithLp.toLp 2 ![Axi.ϱ y, 0, y 2])‖ ∧ ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖fderiv ℝ (fderiv ℝ f) (WithLp.toLp 2 ![Axi.ϱ y, 0, y 2])‖ := by
  obtain ⟨θ, hθ⟩ := axiDens_exists_rot y
  set g : Space ≃ₗᵢ[ℝ] Space := UnforcedLeray.Axi.rotZ θ with hgdef
  have hfix : FixesAxis g := UnforcedLeray.Axi.fixesAxis_rotZ θ
  set P : Space := WithLp.toLp 2 ![Axi.ϱ y, 0, y 2] with hPdef
  have hgs : g.symm y = P := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    exact hθ.symm
  have hfun : (fun x => g (f (g.symm x))) = f := funext fun x => hf g hfix x
  have hD1 : ∀ x, fderiv ℝ f x =
      (g : Space →L[ℝ] Space).comp ((fderiv ℝ f (g.symm x)).comp (g.symm : Space →L[ℝ] Space)) := by
    intro x
    have key := axiDens_fderiv_conj g g f x
    rw [hfun] at key
    exact key
  have hD2 : (fun x => axiDensConj g (fderiv ℝ f (g.symm x))) = fderiv ℝ f :=
    funext fun x => (hD1 x).symm
  have key2 := axiDens_fderiv_conj g (axiDensConj g) (fderiv ℝ f) y
  rw [hD2] at key2
  refine ⟨?_, ?_, ?_⟩
  · have hf0 := hf g hfix y
    rw [hgs] at hf0
    rw [← hf0, LinearIsometryEquiv.norm_map]
  · rw [hD1 y, hgs]
    exact (axiDens_norm_left g _).trans (axiDens_norm_right _ g.symm)
  · rw [key2, hgs]
    exact (axiDens_norm_left (axiDensConj g) _).trans (axiDens_norm_right _ g.symm)

end UnforcedLeray.Short.PartIIIb.Concrete
