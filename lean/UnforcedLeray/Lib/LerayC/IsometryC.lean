import UnforcedLeray.Lib.LerayC.Isometry
import UnforcedLeray.Lib.LerayC.Phase

/-!
# The complex and phase Leray projections commute with the orthogonal group
(INF01 T16 for `ℂ³` and `Y_p`)

Blueprint: INF01 targets T16 (`lerayLp_fixesAxis`) and T17 (`ℂ³` version, `lerayY`) of


Manuscript: the action `(g·f)(x) = g f(g⁻¹x)` of `𝒪` (`paper/main.tex` lines 112–115), extended
to complex fields componentwise; unit B0440 (`eq:m3-free-graph`, lines 3247–3255: the free
resolvent on `Y_q` "preserves `𝒪`-invariant fields (`P` commutes with `𝒪`)").

* `complexifyIso g : ℂ³ →L[ℝ] ℂ³`, `z ↦ g(Re z) + i g(Im z)`;
* `rotLpC p g`: `F ↦ g F(g⁻¹ ·)` on `L^p(R³;ℂ³)`;
* `lerayC_isometry`: `𝔓 (g·F) = g·(𝔓F)` on `L^p(R³;ℂ³)` for every linear isometry `g`;
* `lerayY_isometry`: the same on `Y_p`, `g` acting slice by slice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

open UnforcedLeray.PhaseSpace (CVec3 Yq)

@[simp] theorem reV_ofImV (x : Space) : reV (ofImV x) = 0 := by ext i; simp
@[simp] theorem imV_ofImV (x : Space) : imV (ofImV x) = x := by ext i; simp

/-- The complexification `z ↦ g(Re z) + i g(Im z)` of a linear isometry `g` of `R³`. -/
def complexifyIso (g : Space ≃ₗᵢ[ℝ] Space) : CVec3 →L[ℝ] CVec3 :=
  ofReV.comp ((g.toLinearIsometry.toContinuousLinearMap).comp reV) +
    ofImV.comp ((g.toLinearIsometry.toContinuousLinearMap).comp imV)

theorem complexifyIso_apply (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) :
    complexifyIso g z = ofReV (g (reV z)) + ofImV (g (imV z)) := rfl

@[simp] theorem reV_complexifyIso (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) :
    reV (complexifyIso g z) = g (reV z) := by
  rw [complexifyIso_apply, map_add, reV_ofReV, reV_ofImV, add_zero]

@[simp] theorem imV_complexifyIso (g : Space ≃ₗᵢ[ℝ] Space) (z : CVec3) :
    imV (complexifyIso g z) = g (imV z) := by
  rw [complexifyIso_apply, map_add, imV_ofReV, imV_ofImV, zero_add]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The action `F ↦ g F(g⁻¹ ·)` of a linear isometry `g` on `L^p(R³;ℂ³)` (componentwise
complexification). -/
def rotLpC (g : Space ≃ₗᵢ[ℝ] Space) :
    Lp CVec3 p (volume : Measure Space) →L[ℝ] Lp CVec3 p (volume : Measure Space) :=
  ((complexifyIso g).compLpL p volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (g.symm : Space → Space)
      g.symm.measurePreserving).toContinuousLinearMap

theorem coeFn_rotLpC (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 p (volume : Measure Space)) :
    (rotLpC p g F : Space → CVec3) =ᵐ[volume] fun x => complexifyIso g (F (g.symm x)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := volume) (p := p) (complexifyIso g)
    (Lp.compMeasurePreserving (g.symm : Space → Space) g.symm.measurePreserving F)
  have h2 := Lp.coeFn_compMeasurePreserving F g.symm.measurePreserving
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [hx, Function.comp_apply]

/-- Real parts of a rotated field: `Re(g·F) = g·(Re F)`. -/
theorem reV_compLpL_rotLpC (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 p (volume : Measure Space)) :
    reV.compLpL p volume (rotLpC p g F) = rotLp p g (reV.compLpL p volume F) := by
  apply Lp.ext
  have h1 := reV.coeFn_compLpL (μ := volume) (p := p) (rotLpC p g F)
  have h2 := coeFn_rotLpC g F
  have h3 := coeFn_rotLp g (reV.compLpL p volume F)
  have h4 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (reV.coeFn_compLpL (μ := volume) (p := p) F)
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  simp only [Function.comp_apply] at e4
  rw [e1, e2, e3, e4, reV_complexifyIso]

theorem imV_compLpL_rotLpC (g : Space ≃ₗᵢ[ℝ] Space) (F : Lp CVec3 p (volume : Measure Space)) :
    imV.compLpL p volume (rotLpC p g F) = rotLp p g (imV.compLpL p volume F) := by
  apply Lp.ext
  have h1 := imV.coeFn_compLpL (μ := volume) (p := p) (rotLpC p g F)
  have h2 := coeFn_rotLpC g F
  have h3 := coeFn_rotLp g (imV.compLpL p volume F)
  have h4 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (imV.coeFn_compLpL (μ := volume) (p := p) F)
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  simp only [Function.comp_apply] at e4
  rw [e1, e2, e3, e4, imV_complexifyIso]

/-- Recombination: `ι_Re(g·U) + ι_Im(g·W) = g·(ι_Re U + ι_Im W)`. -/
theorem ofReV_ofImV_rotLp (g : Space ≃ₗᵢ[ℝ] Space) (U W : Lp Space p (volume : Measure Space)) :
    ofReV.compLpL p volume (rotLp p g U) + ofImV.compLpL p volume (rotLp p g W) =
      rotLpC p g (ofReV.compLpL p volume U + ofImV.compLpL p volume W) := by
  apply Lp.ext
  have h0 := Lp.coeFn_add (ofReV.compLpL p volume (rotLp p g U))
    (ofImV.compLpL p volume (rotLp p g W))
  have h1 := ofReV.coeFn_compLpL (μ := volume) (p := p) (rotLp p g U)
  have h2 := ofImV.coeFn_compLpL (μ := volume) (p := p) (rotLp p g W)
  have h3 := coeFn_rotLp g U
  have h4 := coeFn_rotLp g W
  have h5 := coeFn_rotLpC g (ofReV.compLpL p volume U + ofImV.compLpL p volume W)
  have h6 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_add (ofReV.compLpL p volume U) (ofImV.compLpL p volume W))
  have h7 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (ofReV.coeFn_compLpL (μ := volume) (p := p) U)
  have h8 := g.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (ofImV.coeFn_compLpL (μ := volume) (p := p) W)
  filter_upwards [h0, h1, h2, h3, h4, h5, h6, h7, h8] with x e0 e1 e2 e3 e4 e5 e6 e7 e8
  simp only [Function.comp_apply, Pi.add_apply] at e6 e7 e8
  rw [e0, Pi.add_apply, e1, e2, e3, e4, e5, e6, e7, e8, complexifyIso_apply]
  simp only [map_add, reV_ofReV, reV_ofImV, imV_ofReV, imV_ofImV, map_zero, add_zero, zero_add]

/-- **INF01 T16 for `ℂ³` (`𝒪`-equivariance).** For `1 < p < ∞` and every linear isometry `g`
of `R³`, `𝔓(g·F) = g·(𝔓F)` on `L^p(R³;ℂ³)` (B0440, `paper/main.tex` lines 3247–3255). -/
theorem lerayC_isometry (hp1 : 1 < p) (hp : p ≠ ⊤) (g : Space ≃ₗᵢ[ℝ] Space)
    (F : Lp CVec3 p (volume : Measure Space)) :
    lerayC p hp1 hp (rotLpC p g F) = rotLpC p g (lerayC p hp1 hp F) := by
  rw [lerayC_apply, lerayC_apply, reV_compLpL_rotLpC, imV_compLpL_rotLpC, lerayLp_rotLp,
    lerayLp_rotLp, ofReV_ofImV_rotLp]

/-- **`𝒪`-equivariance on `Y_p`.** The phase Leray projection commutes with every linear
isometry `g` acting slice by slice (B0440, `paper/main.tex` lines 3247–3255). -/
theorem lerayY_isometry {P : ℝ} [Fact (0 < P)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (g : Space ≃ₗᵢ[ℝ] Space) :
    ((lerayY P p hp1 hp).restrictScalars ℝ).comp
        ((rotLpC p g).compLpL p AddCircle.haarAddCircle) =
      ((rotLpC p g).compLpL p AddCircle.haarAddCircle).comp
        ((lerayY P p hp1 hp).restrictScalars ℝ) := by
  refine lerayY_comm_slicewise hp1 hp _ ?_
  ext1 F
  exact lerayC_isometry hp1 hp g F

end UnforcedLeray.RieszLp
