import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5

/-!
# `XSolDil` (task `PartIII-b:C/near/pins/3/5/5`)

Source `the November 2 reference manuscript` lines 2666-2668 and 1675-1677:
the dilation `x = εy` relates the outer variable of `X` to the similarity variable `y` of the
weak formulation.  Writing `D x = (x.1, ε • x.2)`, phase tests correspond by `φ = ψ ∘ D`,
`∇(ψ ∘ D) = ε (∇ψ) ∘ D`, and the period integral picks up `|ε³|⁻¹` from the spatial change of
variables.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0223 (MeridC SpaceC X PSpace)

/-- The dilation `(τ, y) ↦ (τ, ε y)` as a continuous linear map of `ℝ × ℝ³`. -/
def xsdL (ε : ℝ) : ℝ × Space →L[ℝ] ℝ × Space :=
  (ContinuousLinearMap.fst ℝ ℝ Space).prod (ε • ContinuousLinearMap.snd ℝ ℝ Space)

theorem xsdL_apply (ε : ℝ) (x : ℝ × Space) : xsdL ε x = (x.1, ε • x.2) := rfl

theorem xsdL_zero (ε : ℝ) (v : Space) : xsdL ε (0, v) = ε • ((0 : ℝ), v) := by
  rw [xsdL_apply]
  ext <;> simp

/-- Lemma A: dilation preserves phase tests (for `ε ≠ 0`). -/
theorem xsd_isPhaseTest {P ε : ℝ} (hε : ε ≠ 0) {ψ : ℝ × Space → ℂ} (hψ : IsPhaseTest P ψ) :
    IsPhaseTest P (fun x => ψ (x.1, ε • x.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : ContDiff ℝ ∞ (fun x : ℝ × Space => (x.1, ε • x.2)) :=
      contDiff_fst.prodMk (contDiff_snd.const_smul ε)
    exact hψ.smooth.comp hL
  · intro τ y
    exact hψ.periodic τ (ε • y)
  · obtain ⟨R, hR⟩ := hψ.bounded_support
    refine ⟨R / |ε|, fun τ y hy => hR τ (ε • y) ?_⟩
    have habs : 0 < |ε| := abs_pos.mpr hε
    have h1 : R < ‖y‖ * |ε| := (div_lt_iff₀ habs).mp hy
    rw [norm_smul, Real.norm_eq_abs]
    linarith [mul_comm ‖y‖ |ε|]

/-- Lemma B: the gradient of a dilated function. -/
theorem xsd_gradT {ε : ℝ} {ψ : ℝ × Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (x : ℝ × Space) :
    gradT (fun x => ψ (x.1, ε • x.2)) x = ε • gradT ψ (x.1, ε • x.2) := by
  have hDL : HasFDerivAt (fun x : ℝ × Space => (x.1, ε • x.2)) (xsdL ε) x :=
    (xsdL ε).hasFDerivAt
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (x.1, ε • x.2)) (x.1, ε • x.2) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have h1 : fderiv ℝ (fun x : ℝ × Space => ψ (x.1, ε • x.2)) x
      = (fderiv ℝ ψ (x.1, ε • x.2)).comp (xsdL ε) :=
    (hψd.comp x hDL).fderiv
  unfold gradT
  simp only [PhaseSpace.dy]
  simp only [h1]
  simp only [ContinuousLinearMap.comp_apply, xsdL_zero, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_assoc]

/-- Lemma C: the pairing of a dilated gradient test with a dilated field. -/
theorem xsd_pairF {P ε : ℝ} {ψ : ℝ × Space → ℂ} (hψ : IsPhaseTest P ψ)
    (u : ℝ × Space → CVec3) :
    pairF P (gradT (fun x => ψ (x.1, ε • x.2))) (fun x => u (x.1, ε • x.2))
      = ((ε * |ε ^ 3|⁻¹ : ℝ) : ℂ) * pairF P (gradT ψ) u := by
  unfold pairF phaseInt
  have key : ∀ t : ℝ, ∫ y : Space,
      dotL (gradT (fun x => ψ (x.1, ε • x.2)) (t, y)) (u (t, ε • y))
        = (ε * |ε ^ 3|⁻¹ : ℝ) • ∫ y : Space, dotL (gradT ψ (t, y)) (u (t, y)) := by
    intro t
    have h1 : ∀ y : Space,
        dotL (gradT (fun x => ψ (x.1, ε • x.2)) (t, y)) (u (t, ε • y))
          = ε • (fun z : ℝ × Space => dotL (gradT ψ z) (u z)) (t, ε • y) := by
      intro y
      rw [xsd_gradT hψ.smooth (t, y), ContinuousLinearMap.map_smul_of_tower]
      rfl
    simp_rw [h1]
    rw [integral_smul]
    have h2 := MeasureTheory.Measure.integral_comp_smul
      (μ := (volume : Measure Space)) (fun y : Space => dotL (gradT ψ (t, y)) (u (t, y))) ε
    rw [finrank_euclideanSpace_fin] at h2
    have h3 : (∫ y : Space, (fun z : ℝ × Space => dotL (gradT ψ z) (u z)) (t, ε • y))
        = |ε ^ 3|⁻¹ • ∫ y : Space, dotL (gradT ψ (t, y)) (u (t, y)) := by
      simpa using h2
    rw [h3, smul_smul]
  simp_rw [key]
  rw [integral_smul]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem xSolDil : XSolDil := by
  intro P _ ε hε F
  have hε0 : ε ≠ 0 := hε.ne'
  have hk : ((ε * |ε ^ 3|⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (ε * |ε ^ 3|⁻¹ : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  constructor
  · intro hF φ hφ
    have hψ : IsPhaseTest P (fun x : ℝ × Space => φ (x.1, ε⁻¹ • x.2)) :=
      xsd_isPhaseTest (ε := ε⁻¹) (inv_ne_zero hε0) hφ
    have key : pairF P (gradT (fun x : ℝ × Space => (fun x : ℝ × Space => φ (x.1, ε⁻¹ • x.2))
        (x.1, ε • x.2))) (fun x => repX P F (x.1, ε • x.2))
        = ((ε * |ε ^ 3|⁻¹ : ℝ) : ℂ) *
          pairF P (gradT (fun x : ℝ × Space => φ (x.1, ε⁻¹ • x.2))) (repX P F) :=
      xsd_pairF hψ (repX P F)
    have he : (fun x : ℝ × Space => (fun x : ℝ × Space => φ (x.1, ε⁻¹ • x.2))
        (x.1, ε • x.2)) = φ := by
      funext x
      simp [smul_smul, inv_mul_cancel₀ hε0]
    rw [he] at key
    have h0 : pairF P (gradT (fun x : ℝ × Space => φ (x.1, ε⁻¹ • x.2))) (repX P F) = 0 :=
      hF _ hψ
    rw [key, h0, mul_zero]
  · intro hW ψ hψ
    have hχ : IsPhaseTest P (fun x : ℝ × Space => ψ (x.1, ε • x.2)) :=
      xsd_isPhaseTest hε0 hψ
    have h : pairF P (gradT (fun x : ℝ × Space => ψ (x.1, ε • x.2)))
        (fun x => repX P F (x.1, ε • x.2)) = 0 := hW _ hχ
    rw [xsd_pairF hψ (repX P F)] at h
    exact (mul_eq_zero.1 h).resolve_left hk

end UnforcedLeray.Short.PartIIIb.NearInst
