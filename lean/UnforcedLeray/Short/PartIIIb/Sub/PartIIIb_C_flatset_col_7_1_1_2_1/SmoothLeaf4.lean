import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel

/-!
# Leaf 4: uniform bounds on the `y`-derivatives of each slice `heatH ν G i τ` (task
`PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/4`, target `heatBound : HeatBound`).

For `τ = 0` the slice is the chart field itself. For `τ > 0` it is the Gaussian average
`∫ G_{ντ}(w) g(y - (τ, planeι w)) dw`, whose `n`-th derivative is the Gaussian average of the
`n`-th derivative of `g` at the translated points (differentiation under the integral sign,
`UnforcedLeray.L09.iteratedFDeriv_integral_eq`).  The Gaussian has unit mass, so the bound is the
uniform bound `C` on the derivatives of `g = G(·) i`, independent of `τ`.
Source `the November 2 reference manuscript` 1684-1689.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The complex-valued chart field `p ↦ G p i`, smooth. -/
theorem hbd_g_contDiff {c : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : Chart => ((G p i : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hG.1 i)

/-- Uniform bounds on all derivatives of the complex-valued chart field. -/
theorem hbd_g_bound {c : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (i : Fin 2)
    (n : ℕ) : ∃ C : ℝ, ∀ p : Chart, ‖iteratedFDeriv ℝ n (fun p : Chart => ((G p i : ℝ) : ℂ)) p‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.2.2.2 i n
  refine ⟨C, fun p => ?_⟩
  have hgn : ContDiff ℝ (n : WithTop ℕ∞) (fun p : Chart => G p i) :=
    (hG.1 i).of_le (by exact_mod_cast le_top)
  have hiso := LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (n := n) (x := p)
    Complex.ofRealLI hgn.contDiffAt (i := n) le_rfl
  have hfun : (fun p : Chart => ((G p i : ℝ) : ℂ)) = Complex.ofRealLI ∘ (fun p : Chart => G p i) := rfl
  rw [hfun, hiso]
  exact hC p

/-- Derivatives of `y ↦ k • g (y - v)`. -/
theorem hbd_iter_smul_comp_sub {g : Chart → ℂ} (hg : ContDiff ℝ ∞ g)
    (k : ℝ) (v : Chart) (n : ℕ) (y : Chart) :
    iteratedFDeriv ℝ n (fun y : Chart => k • g (y - v)) y =
      k • iteratedFDeriv ℝ n g (y - v) := by
  have hgn : ContDiff ℝ (n : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast le_top)
  have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Chart => g (y - v)) y :=
    (hgn.comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hf, iteratedFDeriv_comp_sub']

/-- The slice `heatH` as a Gaussian average, for `ν τ > 0`. -/
theorem hbd_heatH_eq {ν τ : ℝ} (hθ : 0 < ν * τ) (G : Chart → Fin 2 → ℝ) (i : Fin 2)
    (y : Chart) :
    heatH ν G i τ y = ∫ w : Euc 2, gaussKernel 2 (ν * τ) w •
      (fun p : Chart => ((G p i : ℝ) : ℂ)) (y - (τ, UnforcedLeray.B0224.planeι w)) := by
  unfold heatH
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rfl

/-- Differentiation under the Gaussian integral: the `n`-th derivative of
`y ↦ ∫ G_θ(w) g(y - (τ, planeι w)) dw` is the Gaussian average of the `n`-th derivative of `g`. -/
theorem hbd_iter_integral {g : Chart → ℂ} (hg : ContDiff ℝ ∞ g)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ p : Chart, ‖iteratedFDeriv ℝ n g p‖ ≤ C)
    {θ τ : ℝ} (hθ : 0 < θ) (n : ℕ) (y : Chart) :
    iteratedFDeriv ℝ n
        (fun y : Chart => ∫ w : Euc 2, gaussKernel 2 θ w • g (y - (τ, UnforcedLeray.B0224.planeι w))) y =
      ∫ w : Euc 2, gaussKernel 2 θ w • iteratedFDeriv ℝ n g (y - (τ, UnforcedLeray.B0224.planeι w)) := by
  have hgn : ∀ m : ℕ, Continuous (iteratedFDeriv ℝ m g) := fun m =>
    (hg.of_le (by exact_mod_cast le_top) :
      ContDiff ℝ (m : WithTop ℕ∞) g).continuous_iteratedFDeriv'
  have hF : ∀ w : Euc 2, ContDiff ℝ ∞
      (fun y : Chart => gaussKernel 2 θ w • g (y - (τ, UnforcedLeray.B0224.planeι w))) := by
    intro w
    exact ContDiff.smul (contDiff_const (c := gaussKernel 2 θ w))
      (hg.comp (contDiff_id.sub contDiff_const))
  have hint := UnforcedLeray.L09.iteratedFDeriv_integral_eq (μ := (volume : Measure (Euc 2)))
    (F := fun (w : Euc 2) (y : Chart) =>
      gaussKernel 2 θ w • g (y - (τ, UnforcedLeray.B0224.planeι w)))
    (U := (univ : Set Chart)) isOpen_univ
    (Filter.Eventually.of_forall fun w => (hF w).contDiffOn)
    (by
      intro m x _
      have hk : Continuous fun w : Euc 2 => gaussKernel 2 θ w :=
        UnforcedLeray.Gaussian.continuous_gaussKernel θ
      have hm : Continuous fun w : Euc 2 =>
          iteratedFDeriv ℝ m g (x - (τ, UnforcedLeray.B0224.planeι w)) :=
        (hgn m).comp (continuous_const.sub
          (continuous_const.prodMk UnforcedLeray.B0224.continuous_planeι))
      have hcont : Continuous fun w : Euc 2 =>
          gaussKernel 2 θ w • iteratedFDeriv ℝ m g (x - (τ, UnforcedLeray.B0224.planeι w)) :=
        hk.smul hm
      have heq : (fun w : Euc 2 => iteratedFDeriv ℝ m
          (fun y : Chart => gaussKernel 2 θ w • g (y - (τ, UnforcedLeray.B0224.planeι w))) x) =
          fun w : Euc 2 => gaussKernel 2 θ w •
            iteratedFDeriv ℝ m g (x - (τ, UnforcedLeray.B0224.planeι w)) := by
        funext w
        exact hbd_iter_smul_comp_sub hg _ _ m x
      rw [heq]
      exact hcont.aestronglyMeasurable)
    (by
      intro m x _
      obtain ⟨C, hC⟩ := hb m
      refine ⟨univ, univ_mem, fun w => C * gaussKernel 2 θ w,
        (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).const_mul C, ?_⟩
      refine Filter.Eventually.of_forall fun w y _ => ?_
      rw [hbd_iter_smul_comp_sub hg _ _ m y, norm_smul,
        Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w)]
      dsimp only
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w))
    n (mem_univ y)
  refine hint.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact hbd_iter_smul_comp_sub hg _ _ n y

/-- **Leaf 4.** Uniform bound on every `y`-derivative of `heatH ν G i τ`, `τ ≥ 0`. -/
theorem heatBound : HeatBound := by
  intro c ν G hG hν i n
  obtain ⟨C, hC⟩ := hbd_g_bound hG i n
  refine ⟨C, fun τ hτ y => ?_⟩
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0
    have hfun : heatH ν G i 0 = fun p : Chart => ((G p i : ℝ) : ℂ) := by
      funext p
      unfold heatH
      rw [UnforcedLeray.B0224.planeHeat_of_nonpos (by simp : ν * 0 ≤ 0)]
      simp
    rw [hfun]
    exact hC y
  · have hθ : 0 < ν * τ := mul_pos hν hpos
    have hfun : heatH ν G i τ = fun y : Chart => ∫ w : Euc 2, gaussKernel 2 (ν * τ) w •
        (fun p : Chart => ((G p i : ℝ) : ℂ)) (y - (τ, UnforcedLeray.B0224.planeι w)) :=
      funext fun y => hbd_heatH_eq hθ G i y
    rw [hfun, hbd_iter_integral (hbd_g_contDiff hG i) (fun m => hbd_g_bound hG i m) hθ n y]
    refine (norm_integral_le_of_norm_le (g := fun w : Euc 2 => C * gaussKernel 2 (ν * τ) w)
      ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).const_mul C)
      (Filter.Eventually.of_forall fun w => ?_)).trans_eq ?_
    · rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w)
    · rw [integral_const_mul, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ, mul_one]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
