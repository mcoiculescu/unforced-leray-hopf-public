import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.HeatR3.GroupDeriv

/-!
# `SFCGaussShiftDeriv` (source 3426-3430): directional derivative of the plane heat
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

theorem planeι_sfcE_smul (j : Fin 2) (r : ℝ) :
    UnforcedLeray.B0224.planeι (r • sfcE j) = r • UnforcedLeray.B0579.dir j := by
  fin_cases j <;> ext <;> simp [sfcE, UnforcedLeray.B0579.dir, UnforcedLeray.B0224.planeι_apply]

theorem fderiv_gaussKernel_sfcE (θ : ℝ) (hθ : 0 < θ) (j : Fin 2) (y : Euc 2) :
    fderiv ℝ (gaussKernel 2 θ) y (sfcE j) = UnforcedLeray.Heat.gaussD1 2 θ j y := by
  have hdiff : DifferentiableAt ℝ (gaussKernel 2 θ) y :=
    ((UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable
      (by norm_num)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => y + t • sfcE j) (sfcE j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (sfcE j)).const_add y
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := UnforcedLeray.Heat.hasDerivAt_gaussKernel_shift (d := 2) hθ j y 0
  have h3 := h1.unique h2
  simpa using h3

/-- **Lemma 3 (derivative moved onto the Gaussian, source 3426-3430).** -/
theorem sfcGaussShiftDeriv : SFCGaussShiftDeriv := by
  unfold SFCGaussShiftDeriv
  intro θ hθ f hf hbd z j
  obtain ⟨C, hC⟩ := hbd
  have hH := UnforcedLeray.Heat.hasDerivAt_heatConv_dir (d := 2) (G := ℝ × ℝ)
    UnforcedLeray.B0224.planeι UnforcedLeray.B0224.measurable_planeι hθ
    (u := f) hf.stronglyMeasurable (M := C) hC j z
  have hK : UnforcedLeray.Heat.heatConvK UnforcedLeray.B0224.planeι
      (UnforcedLeray.Heat.gaussD1 2 θ j) f z =
      ∫ y : Euc 2, fderiv ℝ (gaussKernel 2 θ) y (sfcE j) •
        f (z - UnforcedLeray.B0224.planeι y) := by
    unfold UnforcedLeray.Heat.heatConvK
    congr 1
    funext y
    rw [fderiv_gaussKernel_sfcE θ hθ j y]
  have hfun : (fun t : ℝ => UnforcedLeray.B0224.planeHeat θ f (z + t • UnforcedLeray.B0579.dir j))
      = (fun r : ℝ => UnforcedLeray.Heat.heatConv UnforcedLeray.B0224.planeι θ f
          (z + UnforcedLeray.B0224.planeι (r • sfcE j))) := by
    funext r
    rw [planeι_sfcE_smul j r, UnforcedLeray.B0224.planeHeat_of_pos hθ]
    rfl
  rw [hfun, ← hK]
  exact hH

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
