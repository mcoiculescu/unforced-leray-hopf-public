import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayGradPerp.Cutoff
import UnforcedLeray.Short.PartIIa.StatementsNear
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDefs

/-!
# Derivatives of the cut-off potential (helper for `LerayGradPerp`)

For `N > 0` and a differentiable chart function `u`, the cut-off `Φ = chi(N⁻¹ η) u` has
`∂_q Φ = chi · ∂_q u` and `∂_η Φ = chi · ∂_η u + u · chi'(N⁻¹ η) N⁻¹`, so its flat gradient is
`cgrad 0 Φ = cvec ![chi · ∂_q u, chi · ∂_η u + u · chi'(N⁻¹η) N⁻¹]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut

/-- The cut-off potential `p ↦ chi(N⁻¹ η) u(p)`. -/
def cutFn (N : ℝ) (u : Chart → ℝ) : Chart → ℝ := fun p => chi (N⁻¹ * p.2.2) * u p

theorem hasFDerivAt_chiEta (N : ℝ) (p : Chart) :
    HasFDerivAt (fun q : Chart => chi (N⁻¹ * q.2.2))
      (deriv chi (N⁻¹ * p.2.2) •
        (N⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) p := by
  have hL : HasFDerivAt (fun q : Chart => N⁻¹ * q.2.2)
      (N⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.const_mul N⁻¹
  have hd : Differentiable ℝ chi := contDiff_chi.differentiable (by simp)
  have key := (hd (N⁻¹ * p.2.2)).hasDerivAt.comp_hasFDerivAt p hL
  exact key

theorem fderiv_cutFn {N : ℝ} {u : Chart → ℝ} (hu : Differentiable ℝ u) (p v : Chart) :
    fderiv ℝ (cutFn N u) p v =
      chi (N⁻¹ * p.2.2) * fderiv ℝ u p v + u p * (deriv chi (N⁻¹ * p.2.2) * (N⁻¹ * v.2.2)) := by
  have h1 : DifferentiableAt ℝ (fun q : Chart => chi (N⁻¹ * q.2.2)) p :=
    (hasFDerivAt_chiEta N p).differentiableAt
  have hfun : cutFn N u = (fun q : Chart => chi (N⁻¹ * q.2.2)) * u := rfl
  rw [hfun, fderiv_mul h1 (hu p), add_apply, smul_apply,
    smul_apply, (hasFDerivAt_chiEta N p).fderiv]
  simp [smul_eq_mul, ContinuousLinearMap.comp_apply]

theorem dQ_cutFn {N : ℝ} {u : Chart → ℝ} (hu : Differentiable ℝ u) (p : Chart) :
    UnforcedLeray.Axi.dQ (cutFn N u) p = chi (N⁻¹ * p.2.2) * UnforcedLeray.Axi.dQ u p := by
  unfold UnforcedLeray.Axi.dQ
  rw [fderiv_cutFn hu]
  simp

theorem dEta_cutFn {N : ℝ} {u : Chart → ℝ} (hu : Differentiable ℝ u) (p : Chart) :
    UnforcedLeray.Axi.dEta (cutFn N u) p =
      chi (N⁻¹ * p.2.2) * UnforcedLeray.Axi.dEta u p +
        u p * (deriv chi (N⁻¹ * p.2.2) * N⁻¹) := by
  unfold UnforcedLeray.Axi.dEta
  rw [fderiv_cutFn hu]
  simp

theorem cgrad_cutFn {N : ℝ} {u : Chart → ℝ} (hu : Differentiable ℝ u) (p : Chart) :
    UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn N u) p =
      cvec ![chi (N⁻¹ * p.2.2) * UnforcedLeray.Axi.dQ u p,
        chi (N⁻¹ * p.2.2) * UnforcedLeray.Axi.dEta u p + u p * (deriv chi (N⁻¹ * p.2.2) * N⁻¹)] := by
  ext i
  fin_cases i
  · simp only [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.Deps_zero]
    simp [cvec, dQ_cutFn hu]
  · simp only [UnforcedLeray.Short.PartIIa.cgrad]
    simp [cvec, dEta_cutFn hu]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut
