import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1
import UnforcedLeray.Units.B0224.PlaneHeat

/-!
# Smoothness of `Ψ` on `{s > 0}` (`T0gHeatPos`) from its three parts

Source `the November 2 reference manuscript`
lines 1640-1656. On `{0 < s}` with `ν (e^t - 1) > 0`, `Ψ(s,q,η) = e^{-t/2} G(√θ, s, (q,η))`
with `θ = ν s (e^t - 1) > 0`, where `G` is the Gaussian average of `F(s,z) = Φ(e^t s, z)`
(`T0gGaussParam` gives its joint smoothness, `T0gHeatSub` the scaling form of the heat, and
`T0gBdd` the bounded derivatives of `F`, since `F` is `Φ` composed with a linear map).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

theorem t0gHeatPos_of_parts (h1 : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gBdd) (h2 : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gGaussParam) (h3 : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gHeatSub) : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0gHeatPos := by
  intro c ν t hc Φ hΦ hpos
  obtain ⟨L, hL⟩ : ∃ L : Profile →L[ℝ] Profile, ∀ q : Profile, L q = (Real.exp t * q.1, q.2) :=
    ⟨(Real.exp t • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
      fun q => rfl⟩
  let F : Profile → ℝ := fun q => Φ (Real.exp t * q.1, q.2)
  have hF : F = Φ ∘ L := by
    funext q
    show Φ (Real.exp t * q.1, q.2) = Φ (L q)
    rw [hL]
  have hFsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    rw [hF]
    exact hΦ.smooth.comp L.contDiff
  have hFb : ∀ k : ℕ, ∃ C : ℝ, ∀ q : Profile, ‖iteratedFDeriv ℝ k F q‖ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := h1 c hc Φ hΦ k
    refine ⟨C * ‖L‖ ^ k, fun q => ?_⟩
    rw [hF, L.iteratedFDeriv_comp_right hΦ.smooth q (i := k) (by simp)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hC _) (pow_nonneg (norm_nonneg _) k)
  have hG := h2 F hFsm hFb
  have hr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Profile => Real.sqrt (ν * p.1 * (Real.exp t - 1))) {p : Profile | 0 < p.1} := by
    intro p hp
    have hp' : 0 < p.1 := hp
    have hθ : 0 < ν * p.1 * (Real.exp t - 1) := by
      rw [show ν * p.1 * (Real.exp t - 1) = p.1 * (ν * (Real.exp t - 1)) by ring]
      exact mul_pos hp' hpos
    refine ContDiffAt.contDiffWithinAt ?_
    refine ContDiffAt.sqrt ?_ hθ.ne'
    fun_prop
  have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : Profile => (Real.sqrt (ν * p.1 * (Real.exp t - 1)), p.1, p.2))
      {p : Profile | 0 < p.1} :=
    ContDiffOn.prodMk hr (ContDiffOn.prodMk contDiff_fst.contDiffOn contDiff_snd.contDiffOn)
  have hmain := (contDiffOn_const (c := Real.exp (-t / 2))).mul (hG.comp_contDiffOn hcomp)
  refine hmain.congr ?_
  intro p hp
  have hp' : 0 < p.1 := hp
  have hθ : 0 < ν * p.1 * (Real.exp t - 1) := by
    rw [show ν * p.1 * (Real.exp t - 1) = p.1 * (ν * (Real.exp t - 1)) by ring]
    exact mul_pos hp' hpos
  have key := h3 _ hθ (fun z => Φ (Real.exp t * p.1, z)) p.2
  simp only [Function.comp, t0gPsi]
  rw [key]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
