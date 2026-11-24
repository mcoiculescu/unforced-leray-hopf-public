import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_2

/-!
# `PartII-b:T10/7/1/1/2/2`: `gl_testTransport` (phase tests are transported by `𝒪`)

Source of record: `the November 2 reference manuscript` lines 1912-1921, chart 1639-1668.
Mathematics: `trF T Φ = cApp T.symm ∘ Φ ∘ (id × T)`. The complexified map `cApp T.symm` is a continuous
`ℝ`-linear map of `ℂ³`, and `id × T` is continuous linear, so `trF T Φ` is smooth. Periodicity is inherited
from `Φ`, and the support bound transfers because `T` is an isometry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

namespace TT

theorem reS_add' (u v : CVec3) : reS (u + v) = reS u + reS v := by
  ext i
  simp [reS]

theorem imS_add' (u v : CVec3) : imS (u + v) = imS u + imS v := by
  ext i
  simp [imS]

theorem reS_smul' (r : ℝ) (v : CVec3) : reS (r • v) = r • reS v := by
  ext i
  simp [reS]

theorem imS_smul' (r : ℝ) (v : CVec3) : imS (r • v) = r • imS v := by
  ext i
  simp [imS]

theorem realC_add' (x y : Space) :
    B0412.realC (x + y) = B0412.realC x + B0412.realC y := by
  ext i
  simp [B0412.realC_apply]

theorem realC_smul' (r : ℝ) (x : Space) :
    B0412.realC (r • x) = (r : ℂ) • B0412.realC x := by
  ext i
  simp [B0412.realC_apply]

theorem cApp_add' (S : Space ≃ₗᵢ[ℝ] Space) (u v : CVec3) :
    cApp S (u + v) = cApp S u + cApp S v := by
  unfold cApp
  simp only [reS_add', imS_add', map_add, realC_add', smul_add]
  abel

theorem cApp_smul' (S : Space ≃ₗᵢ[ℝ] Space) (r : ℝ) (v : CVec3) :
    cApp S (r • v) = r • cApp S v := by
  unfold cApp
  rw [reS_smul', imS_smul']
  simp only [map_smul, realC_smul', RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_add, smul_comm Complex.I]
  rfl

/-- `cApp S` as an `ℝ`-linear map on `ℂ³`. -/
def cAppL (S : Space ≃ₗᵢ[ℝ] Space) : CVec3 →ₗ[ℝ] CVec3 where
  toFun := cApp S
  map_add' := cApp_add' S
  map_smul' := fun r v => cApp_smul' S r v

/-- `cApp S` as a continuous `ℝ`-linear map on `ℂ³`. -/
def cAppCLM (S : Space ≃ₗᵢ[ℝ] Space) : CVec3 →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap (cAppL S)

theorem cAppCLM_apply (S : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : cAppCLM S v = cApp S v := rfl

end TT

theorem gl_testTransport : UnforcedLeray.Short.IIb.GLTestTransport := by
  intro P T Φ hΦ
  let G : ℝ × Space →L[ℝ] ℝ × Space :=
    (ContinuousLinearMap.id ℝ ℝ).prodMap T.toContinuousLinearEquiv.toContinuousLinearMap
  have hΨ : trF T Φ = (TT.cAppCLM T.symm) ∘ (Φ ∘ G) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hΨ]
    exact (TT.cAppCLM T.symm).contDiff.comp (hΦ.smooth.comp G.contDiff)
  · intro τ y
    show cApp T.symm (Φ (τ + P, T y)) = cApp T.symm (Φ (τ, T y))
    rw [hΦ.periodic]
  · obtain ⟨R, hR⟩ := hΦ.bounded_support
    refine ⟨R, fun τ y hy => ?_⟩
    have hTy : R < ‖T y‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact hy
    show cApp T.symm (Φ (τ, T y)) = 0
    rw [hR τ (T y) hTy]
    exact (TT.cAppCLM_apply T.symm 0).symm.trans (map_zero (TT.cAppCLM T.symm))

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_testTransport
