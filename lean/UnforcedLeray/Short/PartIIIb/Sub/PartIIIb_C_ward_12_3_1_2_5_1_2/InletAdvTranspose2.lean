import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.SmoothResidualWeakForm

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/5`: `inletAdvTranspose2_of`

Source `the November 2 reference manuscript`
lines 2385-2387.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt advT)
open UnforcedLeray.Short.IIb

private theorem div_identity_pair {Φ U E : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : ContDiff ℝ ∞ Φ) (hU : ContDiff ℝ ∞ U) (hE : ContDiff ℝ ∞ E)
    (hdiv : ∀ x : ℝ × UnforcedLeray.Space, ∑ j : Fin 3, dy j U x j = 0)
    (z : ℝ × UnforcedLeray.Space) :
    ∑ k : Fin 3, dy k (fun w => U w k * dotFn Φ E w) z =
      dotL (advT U Φ z) (E z) + dotL (Φ z) (advT U E z) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hEd : Differentiable ℝ E := hE.differentiable (by simp)
  have hk : ∀ k : Fin 3, dy k (fun w => U w k * dotFn Φ E w) z =
      dy k U z k * dotFn Φ E z + U z k * (dotL (dy k Φ z) (E z) + dotL (Φ z) (dy k E z)) := by
    intro k
    rw [srwf_dy_mul ((srwf_coord_contDiff hU k).differentiable (by simp))
      (differentiable_dotFn hΦd hEd) k z, srwf_dy_coord hUd k k z, dy_dotFn hΦd hEd k z]
  simp only [hk]
  have hd := hdiv z
  simp only [Fin.sum_univ_three] at hd
  simp only [Fin.sum_univ_three, advT, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, dotL_apply]
  linear_combination (dotFn Φ E z) * hd

private theorem pairF_advT_transpose {P : ℝ}
    {Φ U E : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (hU : ContDiff ℝ ∞ U) (hE : ContDiff ℝ ∞ E)
    (hdiv : ∀ x : ℝ × UnforcedLeray.Space, ∑ j : Fin 3, dy j U x j = 0) :
    pairF P (advT U Φ) E = -pairF P Φ (advT U E) := by
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hΦc : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hD : ContDiff ℝ ∞ (dotFn Φ E) := srwf_dotFn_contDiff hΦc hE
  have hAdvc : Continuous (advT U Φ) := by
    unfold advT
    exact continuous_finsetSum _ fun k _ =>
      (srwf_coord_contDiff hU k).continuous.smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hΦc k).continuous
  have hB_int : Integrable (fun z => dotL (advT U Φ z) (E z)) (srwfSlab P) :=
    UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hAdvc).clm_apply hE.continuous) (R := R)
      (fun t y hy => by
        have h0 : advT U Φ (t, y) = 0 := by
          unfold advT
          exact Finset.sum_eq_zero fun k _ => by rw [srwf_dy_bdd hR k t y hy, smul_zero]
        simp [h0])
  have hK'p : ∀ k : Fin 3,
      Integrable (fun z => dy k (fun w => U w k * dotFn Φ E w) z) (srwfSlab P) ∧
        ∫ z, dy k (fun w => U w k * dotFn Φ E w) z ∂(srwfSlab P) = 0 := by
    intro k
    exact srwf_slab_dy (R := R) ((srwf_coord_contDiff hU k).mul hD)
      (fun τ y hy => by simp [dotFn, hR τ y hy]) k
  have hDd_int : Integrable (fun z => dotL (Φ z) (advT U E z)) (srwfSlab P) := by
    have e : (fun z => dotL (Φ z) (advT U E z)) =
        fun z => (∑ k : Fin 3, dy k (fun w => U w k * dotFn Φ E w) z) -
          dotL (advT U Φ z) (E z) := by
      funext z
      rw [div_identity_pair hΦc hU hE hdiv z]
      ring
    rw [e]
    exact (integrable_finsetSum _ fun k _ => (hK'p k).1).sub hB_int
  have hBD : ∫ z, dotL (advT U Φ z) (E z) ∂(srwfSlab P) +
      ∫ z, dotL (Φ z) (advT U E z) ∂(srwfSlab P) = 0 := by
    rw [← integral_add hB_int hDd_int]
    have e : (fun z => dotL (advT U Φ z) (E z) + dotL (Φ z) (advT U E z)) =
        fun z => ∑ k : Fin 3, dy k (fun w => U w k * dotFn Φ E w) z :=
      funext fun z => (div_identity_pair hΦc hU hE hdiv z).symm
    rw [e, integral_finsetSum _ fun k _ => (hK'p k).1,
      Finset.sum_eq_zero fun k _ => (hK'p k).2]
  unfold pairF
  rw [srwf_phaseInt_eq hB_int, srwf_phaseInt_eq hDd_int]
  have hneg : ∫ z, dotL (advT U Φ z) (E z) ∂(srwfSlab P) =
      -∫ z, dotL (Φ z) (advT U E z) ∂(srwfSlab P) := eq_neg_of_add_eq_zero_left hBD
  rw [hneg, smul_neg]

theorem inletAdvTranspose2_of (hReg : InletFieldRegular) : InletAdvTranspose2 := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := hReg lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i ψ hψ => ?_⟩
  obtain ⟨hraw_s, hraw_div, hE⟩ := H0 p d hreg hν hm z g hg
  exact pairF_advT_transpose hψ hraw_s (hE i).1 hraw_div

end UnforcedLeray.Short.PartIIIb.Concrete
