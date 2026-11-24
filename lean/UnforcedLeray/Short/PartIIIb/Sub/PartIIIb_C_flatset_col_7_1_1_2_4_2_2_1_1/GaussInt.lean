import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1.GaussPeriodic
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Group.Basic

/-!
# `SFCGaussWeightedInt` (source 3426-3430)

Integrability of `y ↦ G_θ(y) • ∂_j f(z - y)` for a `c`-periodic bounded smooth `f` with finite
strip integral of `|∇f|²`. Pointwise `‖v‖ ≤ 1 + ‖v‖²` reduces the `L¹(G_θ)` norm to `∫ G_θ` plus
the Gaussian-weighted periodic integral of `‖∂_j f‖²`, which is finite by `sfcGaussPeriodicBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

theorem sfcGaussWeightedInt : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.SFCGaussWeightedInt := by
  intro c θ hc hθ f hyp z j
  obtain ⟨hf, hper, hbd, hfin⟩ := hyp
  -- continuity of the directional derivative
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hcont : Continuous (fun x : ℝ × ℝ => fderiv ℝ f x (B0579.dir j)) :=
    hfd.clm_apply continuous_const
  -- periodicity of the derivative
  have hper' : ∀ x : ℝ × ℝ, fderiv ℝ f (x.1 + c, x.2) = fderiv ℝ f x := by
    intro x
    have hfun : (fun x : ℝ × ℝ => f (x + ((c : ℝ), (0 : ℝ)))) = f := by
      funext x
      have hx : x + ((c : ℝ), (0 : ℝ)) = (x.1 + c, x.2) := by ext <;> simp
      rw [hx]
      exact hper x.1 x.2
    calc fderiv ℝ f (x.1 + c, x.2) = fderiv ℝ f (x + ((c : ℝ), (0 : ℝ))) := by
          congr 1
          ext <;> simp
      _ = fderiv ℝ (fun x : ℝ × ℝ => f (x + ((c : ℝ), (0 : ℝ)))) x :=
          (fderiv_comp_add_right _).symm
      _ = fderiv ℝ f x := by rw [hfun]
  -- the weight `φ = ‖∂_j f‖²`
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ × ℝ → ℝ≥0∞,
      φ = fun x => ENNReal.ofReal (‖fderiv ℝ f x (B0579.dir j)‖ ^ 2) := ⟨_, rfl⟩
  have hφp : UnforcedLeray.Cyl.IsPeriodic c φ := by
    intro x
    rw [hφdef]
    dsimp only
    rw [hper' x]
  have hφm : Measurable φ := by
    rw [hφdef]
    exact ((hcont.norm.pow 2).measurable).ennreal_ofReal
  -- comparison with the strip integral from the hypothesis
  have hsum : ∀ x : ℝ × ℝ, φ x ≤
      ENNReal.ofReal (‖fderiv ℝ f x (B0579.dir 0)‖ ^ 2 + ‖fderiv ℝ f x (B0579.dir 1)‖ ^ 2) := by
    intro x
    rw [hφdef]
    apply ENNReal.ofReal_le_ofReal
    fin_cases j
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact le_add_of_nonneg_left (sq_nonneg _)
  have hcell : UnforcedLeray.Cyl.cell c =
      Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
    unfold UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hstrip : ∫⁻ x in UnforcedLeray.B0224.strip c, φ x < ⊤ := by
    rw [UnforcedLeray.B0224.lintegral_strip_eq_cell hc hφp]
    calc ∫⁻ x in UnforcedLeray.Cyl.cell c, φ x
        ≤ ∫⁻ x in UnforcedLeray.Cyl.cell c,
            ENNReal.ofReal (‖fderiv ℝ f x (B0579.dir 0)‖ ^ 2 + ‖fderiv ℝ f x (B0579.dir 1)‖ ^ 2) :=
          lintegral_mono (fun x => hsum x)
      _ = ∫⁻ x in Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ),
            ENNReal.ofReal (‖fderiv ℝ f x (B0579.dir 0)‖ ^ 2 + ‖fderiv ℝ f x (B0579.dir 1)‖ ^ 2) := by
          rw [hcell]
      _ < ⊤ := hfin
  -- the periodic Gaussian bound
  obtain ⟨K, hK, hKb⟩ := sfcGaussPeriodicBound c θ hc hθ
  have hpb := hKb φ hφm hφp z
  -- the Gaussian is integrable
  have hG0 : ∀ y : Euc 2, 0 ≤ gaussKernel 2 θ y := fun y => UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y
  have hmeasG : Measurable (fun y : Euc 2 => ENNReal.ofReal (gaussKernel 2 θ y)) :=
    ENNReal.measurable_ofReal.comp (UnforcedLeray.Gaussian.continuous_gaussKernel θ).measurable
  have hGfin : ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) < ⊤ :=
    (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).lintegral_lt_top
  -- continuity of the integrand
  have hF : Continuous (fun y : Euc 2 =>
      gaussKernel 2 θ y • fderiv ℝ f (z - UnforcedLeray.B0224.planeι y) (B0579.dir j)) :=
    (UnforcedLeray.Gaussian.continuous_gaussKernel θ).smul
      (hcont.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  -- finiteness of the norm integral
  have hbound : ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) +
      ENNReal.ofReal (gaussKernel 2 θ y) * φ (z - UnforcedLeray.B0224.planeι y) < ⊤ := by
    rw [lintegral_add_left hmeasG]
    refine ENNReal.add_lt_top.2 ⟨hGfin, ?_⟩
    exact lt_of_le_of_lt hpb (ENNReal.mul_lt_top hK hstrip)
  refine lt_of_le_of_lt (lintegral_mono (fun y => ?_)) hbound
  show ‖gaussKernel 2 θ y • fderiv ℝ f (z - UnforcedLeray.B0224.planeι y) (B0579.dir j)‖ₑ ≤
    ENNReal.ofReal (gaussKernel 2 θ y) +
      ENNReal.ofReal (gaussKernel 2 θ y) * φ (z - UnforcedLeray.B0224.planeι y)
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (hG0 y), hφdef]
  dsimp only
  set G := gaussKernel 2 θ y with hGdef
  set x := ‖fderiv ℝ f (z - UnforcedLeray.B0224.planeι y) (B0579.dir j)‖ with hx
  have hG : 0 ≤ G := hG0 y
  have hx0 : 0 ≤ x := norm_nonneg _
  calc ENNReal.ofReal (G * x)
      ≤ ENNReal.ofReal (G + G * x ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hG (sq_nonneg (x - 1)), mul_nonneg hG hx0])
    _ = ENNReal.ofReal G + ENNReal.ofReal G * ENNReal.ofReal (x ^ 2) := by
        rw [ENNReal.ofReal_add hG (by positivity), ENNReal.ofReal_mul hG]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
