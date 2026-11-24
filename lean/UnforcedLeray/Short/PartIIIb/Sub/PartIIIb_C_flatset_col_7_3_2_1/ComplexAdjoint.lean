import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1

/-!
# `T₀(t)^*` is the complex `H`-adjoint of `T₀(t)` (source `shorter-proof-2026-11-02.tex` 1650-1656)

`B0224.adjoint_T0_eq` gives the real adjoint. Since `T₀(t)^*` commutes with multiplication
by `i`, the imaginary parts agree, which yields the complex identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem t0c_planeHeat_smul_C (θ : ℝ) (a : ℂ) (u : ℝ × ℝ → MeridC) :
    UnforcedLeray.B0224.planeHeat θ (fun x => a • u x) =
      fun x => a • UnforcedLeray.B0224.planeHeat θ u x := by
  funext x
  by_cases hθ : 0 < θ
  · simp only [UnforcedLeray.B0224.planeHeat_of_pos hθ, smul_comm _ a, integral_smul]
  · simp only [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

theorem t0c_fiberHeat_smul_C (c : ℝ) (θ : ℝ → ℝ) (a : ℂ) (F : Profile → MeridC) :
    UnforcedLeray.B0224.fiberHeat c θ (a • F) = a • UnforcedLeray.B0224.fiberHeat c θ F := by
  funext p
  exact congrFun (t0c_planeHeat_smul_C (θ p.1) a (fun z => UnforcedLeray.B0220.periodize c F (p.1, z))) p.2

theorem t0c_heatH_smul_C {c : ℝ} (hc : 0 < c) {θ : ℝ → ℝ} (hθ : Measurable θ) (a : ℂ)
    (f : HSpace c MeridC) :
    UnforcedLeray.B0224.heatH hc hθ (a • f) = a • UnforcedLeray.B0224.heatH hc hθ f := by
  refine Lp.ext ?_
  have h1 := UnforcedLeray.B0224.coeFn_heatH hc hθ (a • f)
  have h2 := Lp.coeFn_smul a (UnforcedLeray.B0224.heatH hc hθ f)
  have h3 := UnforcedLeray.B0224.coeFn_heatH hc hθ f
  have h4 := Lp.coeFn_smul a f
  have h5 := UnforcedLeray.B0224.fiberHeat_congr_ae hc hθ (Lp.stronglyMeasurable (a • f))
    ((Lp.stronglyMeasurable f).const_smul a) h4
  filter_upwards [h1, h2, h3, h5] with p hp1 hp2 hp3 hp5
  rw [hp1, hp5, t0c_fiberHeat_smul_C c θ a (f : Profile → MeridC), Pi.smul_apply, hp2,
    Pi.smul_apply, hp3]

theorem t0c_dilH_smul_C {c a : ℝ} (ha : 0 < a) (s : ℂ) (f : HSpace c MeridC) :
    UnforcedLeray.B0224.dilH ha (s • f) = s • UnforcedLeray.B0224.dilH ha f := by
  refine Lp.ext ?_
  have h1 := UnforcedLeray.B0224.coeFn_dilH ha (s • f)
  have h2 := Lp.coeFn_smul s (UnforcedLeray.B0224.dilH ha f)
  have h3 := UnforcedLeray.B0224.coeFn_dilH ha f
  have h4 := Lp.coeFn_smul s f
  have h5 := UnforcedLeray.B0224.dil_congr_ae ha (Lp.stronglyMeasurable (s • f))
    ((Lp.stronglyMeasurable f).const_smul s) h4
  filter_upwards [h1, h2, h3, h5] with p hp1 hp2 hp3 hp5
  rw [hp1, hp5, hp2, Pi.smul_apply, hp3]
  rfl

theorem t0c_T0adj_smul_C {c : ℝ} (hc : 0 < c) (ν t : ℝ) (s : ℂ) (z : HSpace c MeridC) :
    UnforcedLeray.B0224.T0adj hc ν t (s • z) = s • UnforcedLeray.B0224.T0adj hc ν t z := by
  unfold UnforcedLeray.B0224.T0adj
  rw [smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    t0c_dilH_smul_C, t0c_heatH_smul_C, smul_comm]

theorem t0c_meridC_real_inner (x y : MeridC) :
    inner ℝ x y = (inner ℂ x y : ℂ).re := by
  simp [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, mul_comm]

theorem t0c_HS_real_inner {c : ℝ} (f g : HSpace c MeridC) :
    inner ℝ f g = (inner ℂ f g : ℂ).re := by
  rw [L2.inner_def, L2.inner_def]
  have hint := L2.integrable_inner (𝕜 := ℂ) f g
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  exact integral_congr_ae (Eventually.of_forall fun x => t0c_meridC_real_inner _ _)

theorem t0_complex_adjoint : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0ComplexAdjoint := by
  unfold T0ComplexAdjoint
  intro c ν hc t z g
  have hadj : ContinuousLinearMap.adjoint
      (UnforcedLeray.B0224.T0 hc ν t : HSpace c MeridC →L[ℝ] HSpace c MeridC) =
        UnforcedLeray.B0224.T0adj hc ν t := UnforcedLeray.B0224.adjoint_T0_eq hc ν t
  have hre : ∀ x y : HSpace c MeridC,
      (inner ℂ x (UnforcedLeray.B0224.T0 hc ν t y) : ℂ).re =
        (inner ℂ (UnforcedLeray.B0224.T0adj hc ν t x) y : ℂ).re := by
    intro x y
    have h := ContinuousLinearMap.adjoint_inner_left
      (UnforcedLeray.B0224.T0 hc ν t : HSpace c MeridC →L[ℝ] HSpace c MeridC) y x
    rw [hadj] at h
    rw [t0c_HS_real_inner, t0c_HS_real_inner] at h
    exact h.symm
  apply Complex.ext
  · exact hre z g
  · have h1 := hre ((Complex.I : ℂ) • z) g
    rw [t0c_T0adj_smul_C] at h1
    simp only [inner_smul_left] at h1
    simpa using h1
end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
