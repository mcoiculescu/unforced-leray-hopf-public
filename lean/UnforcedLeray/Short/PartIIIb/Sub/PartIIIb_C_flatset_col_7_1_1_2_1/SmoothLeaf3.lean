import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral
import UnforcedLeray.Units.B0224.PlaneHeat

/-!
# Leaf 3: smoothness of each slice `heatH ν G i τ` (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/3`)

`heatH ν G i τ (s,x) = planeHeat (ν τ) (G(s-τ,·) i) x`.  For `τ = 0` this is the identity, so it is
`G(·) i` itself.  For `τ > 0` it is the Gaussian average
`∫ G_θ(w) G(s-τ, x - planeι w) i dw` with `θ = ν τ`, and smoothness follows from the parametric
integral theorem `UnforcedLeray.L09.contDiffOn_integral` (differentiation under the integral sign),
since the integrand is `G_θ(w) • g(y - (τ, planeι w))` with `g = ofReal ∘ G(·) i` smooth.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The complex-valued chart field `p ↦ G p i`. -/
theorem heatSmooth_g_contDiff {c : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : Chart => ((G p i : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hG.1 i)

/-- Uniform bounds on all derivatives of the complex-valued chart field. -/
theorem heatSmooth_g_bound {c : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (i : Fin 2)
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
theorem heatSmooth_iteratedFDeriv_smul_comp_sub {g : Chart → ℂ} (hg : ContDiff ℝ ∞ g)
    (k : ℝ) (v : Chart) (n : ℕ) (y : Chart) :
    iteratedFDeriv ℝ n (fun y : Chart => k • g (y - v)) y =
      k • iteratedFDeriv ℝ n g (y - v) := by
  have hgn : ContDiff ℝ (n : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast le_top)
  have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Chart => g (y - v)) y :=
    (hgn.comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hf, iteratedFDeriv_comp_sub']

/-- The slice `heatH` as a Gaussian average, for `ν τ > 0`. -/
theorem heatSmooth_heatH_eq {ν τ : ℝ} (hθ : 0 < ν * τ) (G : Chart → Fin 2 → ℝ) (i : Fin 2)
    (y : Chart) :
    heatH ν G i τ y = ∫ w : Euc 2, gaussKernel 2 (ν * τ) w •
      (fun p : Chart => ((G p i : ℝ) : ℂ)) (y - (τ, UnforcedLeray.B0224.planeι w)) := by
  unfold heatH
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rfl

/-- Smoothness of the slice for `τ > 0`, by differentiation under the Gaussian integral. -/
theorem heatSmooth_pos {c ν τ : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G)
    (hθ : 0 < ν * τ) (i : Fin 2) : ContDiff ℝ ∞ (heatH ν G i τ) := by
  set g : Chart → ℂ := fun p : Chart => ((G p i : ℝ) : ℂ) with hgdef
  have hg : ContDiff ℝ ∞ g := heatSmooth_g_contDiff hG i
  have hgn : ∀ n : ℕ, Continuous (iteratedFDeriv ℝ n g) := fun n =>
    (hg.of_le (by exact_mod_cast le_top) :
      ContDiff ℝ (n : WithTop ℕ∞) g).continuous_iteratedFDeriv'
  have hF : ∀ w : Euc 2, ContDiff ℝ ∞
      (fun y : Chart => gaussKernel 2 (ν * τ) w • g (y - (τ, UnforcedLeray.B0224.planeι w))) := by
    intro w
    exact ContDiff.smul (contDiff_const (c := gaussKernel 2 (ν * τ) w))
      (hg.comp (contDiff_id.sub contDiff_const))
  have hint := UnforcedLeray.L09.contDiffOn_integral (μ := (volume : Measure (Euc 2)))
    (F := fun (w : Euc 2) (y : Chart) =>
      gaussKernel 2 (ν * τ) w • g (y - (τ, UnforcedLeray.B0224.planeι w)))
    (U := (univ : Set Chart)) isOpen_univ
    (Filter.Eventually.of_forall fun w => (hF w).contDiffOn)
    (by
      intro n x _
      have hk : Continuous fun w : Euc 2 => gaussKernel 2 (ν * τ) w :=
        UnforcedLeray.Gaussian.continuous_gaussKernel (ν * τ)
      have hm : Continuous fun w : Euc 2 =>
          iteratedFDeriv ℝ n g (x - (τ, UnforcedLeray.B0224.planeι w)) :=
        (hgn n).comp (continuous_const.sub
          (continuous_const.prodMk UnforcedLeray.B0224.continuous_planeι))
      have hcont : Continuous fun w : Euc 2 =>
          gaussKernel 2 (ν * τ) w • iteratedFDeriv ℝ n g (x - (τ, UnforcedLeray.B0224.planeι w)) :=
        hk.smul hm
      have heq : (fun w : Euc 2 => iteratedFDeriv ℝ n
          (fun y : Chart => gaussKernel 2 (ν * τ) w • g (y - (τ, UnforcedLeray.B0224.planeι w))) x) =
          fun w : Euc 2 => gaussKernel 2 (ν * τ) w •
            iteratedFDeriv ℝ n g (x - (τ, UnforcedLeray.B0224.planeι w)) := by
        funext w
        exact heatSmooth_iteratedFDeriv_smul_comp_sub hg _ _ n x
      rw [heq]
      exact hcont.aestronglyMeasurable)
    (by
      intro n x _
      obtain ⟨C, hC⟩ := heatSmooth_g_bound hG i n
      refine ⟨univ, univ_mem, fun w => C * gaussKernel 2 (ν * τ) w,
        (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).const_mul C, ?_⟩
      refine Filter.Eventually.of_forall fun w y _ => ?_
      rw [heatSmooth_iteratedFDeriv_smul_comp_sub hg _ _ n y, norm_smul,
        Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w)]
      dsimp only
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w))
  have hfun : heatH ν G i τ = fun y => ∫ w : Euc 2, gaussKernel 2 (ν * τ) w •
      g (y - (τ, UnforcedLeray.B0224.planeι w)) :=
    funext fun y => heatSmooth_heatH_eq hθ G i y
  rw [hfun]
  exact contDiffOn_univ.1 hint

/-- **Leaf 3.** Each slice `heatH ν G i τ`, `τ ≥ 0`, is smooth in `(s,x)`. -/
theorem heatSmooth : HeatSmooth := by
  intro c ν G hG hν i τ hτ
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0
    have hfun : heatH ν G i 0 = fun y : Chart => ((G y i : ℝ) : ℂ) := by
      funext y
      unfold heatH
      rw [UnforcedLeray.B0224.planeHeat_of_nonpos (by simp : ν * 0 ≤ 0)]
      simp
    rw [hfun]
    exact heatSmooth_g_contDiff hG i
  · exact heatSmooth_pos hG (mul_pos hν hpos) i

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
