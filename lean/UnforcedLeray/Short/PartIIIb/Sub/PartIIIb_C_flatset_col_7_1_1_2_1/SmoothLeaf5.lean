import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel

/-!
# Leaf 5: joint continuity of the `y`-derivatives of `heatH ν G i τ` in `(τ, y)` (task
`PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/5`, target `heatCont : HeatCont`).

The Gaussian average is rescaled, `w = √(ν τ) • u`, so that the kernel `G_{ντ}` becomes the fixed
kernel `G_1` and all the `τ`-dependence sits in the translation `planeι (√(ν τ) • u)`:
`∂ⁿ_y heatH ν G i τ y = ∫ G_1(u) • (∂ⁿg)(y - (τ, planeι (√(ντ) • u))) du`, valid for all `τ ≥ 0`
(at `τ = 0` both sides are `∂ⁿg y`, since `G_1` has unit mass).  The integrand is jointly continuous
in `(τ, y)` and dominated by `C_n G_1(u)`, so dominated convergence gives joint continuity.
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
theorem hct_g_contDiff {c : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : Chart => ((G p i : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hG.1 i)

/-- Uniform bounds on all derivatives of the complex-valued chart field. -/
theorem hct_g_bound {c : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (i : Fin 2)
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
theorem hct_iter_smul_comp_sub {g : Chart → ℂ} (hg : ContDiff ℝ ∞ g)
    (k : ℝ) (v : Chart) (n : ℕ) (y : Chart) :
    iteratedFDeriv ℝ n (fun y : Chart => k • g (y - v)) y =
      k • iteratedFDeriv ℝ n g (y - v) := by
  have hgn : ContDiff ℝ (n : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast le_top)
  have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Chart => g (y - v)) y :=
    (hgn.comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hf, iteratedFDeriv_comp_sub']

/-- The slice `heatH` as a Gaussian average, for `ν τ > 0`. -/
theorem hct_heatH_eq {ν τ : ℝ} (hθ : 0 < ν * τ) (G : Chart → Fin 2 → ℝ) (i : Fin 2)
    (y : Chart) :
    heatH ν G i τ y = ∫ w : Euc 2, gaussKernel 2 (ν * τ) w •
      (fun p : Chart => ((G p i : ℝ) : ℂ)) (y - (τ, UnforcedLeray.B0224.planeι w)) := by
  unfold heatH
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rfl

/-- Differentiation under the Gaussian integral: the `n`-th derivative of
`y ↦ ∫ G_θ(w) g(y - (τ, planeι w)) dw` is the Gaussian average of the `n`-th derivative of `g`. -/
theorem hct_iter_integral {g : Chart → ℂ} (hg : ContDiff ℝ ∞ g)
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
        exact hct_iter_smul_comp_sub hg _ _ m x
      rw [heq]
      exact hcont.aestronglyMeasurable)
    (by
      intro m x _
      obtain ⟨C, hC⟩ := hb m
      refine ⟨univ, univ_mem, fun w => C * gaussKernel 2 θ w,
        (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).const_mul C, ?_⟩
      refine Filter.Eventually.of_forall fun w y _ => ?_
      rw [hct_iter_smul_comp_sub hg _ _ m y, norm_smul,
        Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w)]
      dsimp only
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ w))
    n (mem_univ y)
  refine hint.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  exact hct_iter_smul_comp_sub hg _ _ n y

/-- Rescaling of the planar Gaussian: `∫ G_θ(w) H(w) dw = ∫ G_1(u) H(√θ • u) du` for `θ > 0`. -/
theorem hct_gauss_scale {θ : ℝ} (hθ : 0 < θ) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (H : Euc 2 → V) :
    ∫ w : Euc 2, gaussKernel 2 θ w • H w = ∫ u : Euc 2, gaussKernel 2 1 u • H (Real.sqrt θ • u) := by
  set R : ℝ := Real.sqrt θ with hRdef
  have hR : 0 < R := Real.sqrt_pos.2 hθ
  have hR2 : R ^ 2 = θ := Real.sq_sqrt hθ.le
  have hsc : ∫ u : Euc 2, gaussKernel 2 θ (R • u) • H (R • u) =
      |(R ^ Module.finrank ℝ (Euc 2))⁻¹| • ∫ w : Euc 2, gaussKernel 2 θ w • H w :=
    MeasureTheory.Measure.integral_comp_smul (volume : Measure (Euc 2))
      (fun w : Euc 2 => gaussKernel 2 θ w • H w) R
  rw [UnforcedLeray.Gaussian.finrank_euc, hR2, abs_of_pos (inv_pos.2 hθ)] at hsc
  have hsc2 : ∀ u : Euc 2, gaussKernel 2 θ (R • u) = θ⁻¹ * gaussKernel 2 1 u := by
    intro u
    have h := UnforcedLeray.Gaussian.gaussKernel_scale (d := 2) hR one_pos u
    rw [mul_one, hR2] at h
    rw [h]
    congr 1
    rw [show (-((2:ℕ):ℝ)) = -(2:ℝ) by norm_num, Real.rpow_neg hR.le, Real.rpow_two, hR2]
  have hpt : ∀ u : Euc 2, gaussKernel 2 θ (R • u) • H (R • u) =
      θ⁻¹ • (gaussKernel 2 1 u • H (R • u)) := by
    intro u
    rw [hsc2 u, smul_smul]
  have hint : ∫ u : Euc 2, gaussKernel 2 θ (R • u) • H (R • u) =
      θ⁻¹ • ∫ u : Euc 2, gaussKernel 2 1 u • H (R • u) := by
    simp_rw [hpt]
    rw [integral_smul]
  have key : ∫ w : Euc 2, gaussKernel 2 θ w • H w = ∫ u : Euc 2, gaussKernel 2 1 u • H (R • u) := by
    have h1 : θ⁻¹ • ∫ w : Euc 2, gaussKernel 2 θ w • H w =
        θ⁻¹ • ∫ u : Euc 2, gaussKernel 2 1 u • H (R • u) := hsc.symm.trans hint
    calc ∫ w : Euc 2, gaussKernel 2 θ w • H w
        = θ • (θ⁻¹ • ∫ w : Euc 2, gaussKernel 2 θ w • H w) := by
          rw [smul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
      _ = θ • (θ⁻¹ • ∫ u : Euc 2, gaussKernel 2 1 u • H (R • u)) := by rw [h1]
      _ = ∫ u : Euc 2, gaussKernel 2 1 u • H (R • u) := by
          rw [smul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
  exact key

/-- The `n`-th `y`-derivative of the slice `heatH ν G i τ`, rescaled Gaussian form, for `τ ≥ 0`. -/
theorem hct_iter_eq {c ν : ℝ} {G : Chart → Fin 2 → ℝ} (hG : IsDriving c G) (hν : 0 < ν)
    (i : Fin 2) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (y : Chart) :
    iteratedFDeriv ℝ n (heatH ν G i τ) y =
      ∫ u : Euc 2, gaussKernel 2 1 u •
        iteratedFDeriv ℝ n (fun p : Chart => ((G p i : ℝ) : ℂ))
          (y - (τ, UnforcedLeray.B0224.planeι (Real.sqrt (ν * τ) • u))) := by
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0
    have hfun : heatH ν G i 0 = fun p : Chart => ((G p i : ℝ) : ℂ) := by
      funext p
      unfold heatH
      rw [UnforcedLeray.B0224.planeHeat_of_nonpos (by simp : ν * 0 ≤ 0)]
      simp
    rw [hfun]
    simp only [mul_zero, Real.sqrt_zero, zero_smul, map_zero, Prod.mk_zero_zero, sub_zero]
    rw [integral_smul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) one_pos, one_smul]
  · have hθ : 0 < ν * τ := mul_pos hν hpos
    have hfun : heatH ν G i τ = fun y : Chart => ∫ w : Euc 2, gaussKernel 2 (ν * τ) w •
        (fun p : Chart => ((G p i : ℝ) : ℂ)) (y - (τ, UnforcedLeray.B0224.planeι w)) :=
      funext fun y => hct_heatH_eq hθ G i y
    rw [hfun, hct_iter_integral (hct_g_contDiff hG i) (fun m => hct_g_bound hG i m) hθ n y]
    exact hct_gauss_scale hθ (fun w : Euc 2 =>
      iteratedFDeriv ℝ n (fun p : Chart => ((G p i : ℝ) : ℂ)) (y - (τ, UnforcedLeray.B0224.planeι w)))

/-- **Leaf 5.** Joint continuity in `(τ, y)`, `τ ≥ 0`, of every `y`-derivative of `heatH`. -/
theorem heatCont : HeatCont := by
  intro c ν G hG hν i n
  have hgn : Continuous (iteratedFDeriv ℝ n (fun p : Chart => ((G p i : ℝ) : ℂ))) :=
    ((hct_g_contDiff hG i).of_le (by exact_mod_cast le_top) :
      ContDiff ℝ (n : WithTop ℕ∞) (fun p : Chart => ((G p i : ℝ) : ℂ))).continuous_iteratedFDeriv'
  obtain ⟨C, hC⟩ := hct_g_bound hG i n
  have hcont : ContinuousOn (fun q : ℝ × Chart => ∫ u : Euc 2, gaussKernel 2 1 u •
      iteratedFDeriv ℝ n (fun p : Chart => ((G p i : ℝ) : ℂ))
        (q.2 - (q.1, UnforcedLeray.B0224.planeι (Real.sqrt (ν * q.1) • u))))
      (Ici (0 : ℝ) ×ˢ univ) := by
    apply continuousOn_of_dominated (bound := fun u : Euc 2 => gaussKernel 2 1 u * C)
    · intro q _
      have hu : Continuous fun u : Euc 2 =>
          q.2 - (q.1, UnforcedLeray.B0224.planeι (Real.sqrt (ν * q.1) • u)) := by
        apply Continuous.sub continuous_const
        apply Continuous.prodMk continuous_const
        exact UnforcedLeray.B0224.continuous_planeι.comp (continuous_const_smul (Real.sqrt (ν * q.1)))
      exact ((UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) 1).smul
        (hgn.comp hu)).aestronglyMeasurable
    · intro q _
      refine Filter.Eventually.of_forall fun u => ?_
      rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) one_pos u)]
      exact mul_le_mul_of_nonneg_left (hC _)
        (UnforcedLeray.Gaussian.gaussKernel_nonneg (d := 2) one_pos u)
    · exact (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) one_pos).mul_const C
    · refine Filter.Eventually.of_forall fun u => ?_
      have hq : Continuous fun q : ℝ × Chart =>
          q.2 - (q.1, UnforcedLeray.B0224.planeι (Real.sqrt (ν * q.1) • u)) := by
        apply Continuous.sub continuous_snd
        apply Continuous.prodMk continuous_fst
        exact UnforcedLeray.B0224.continuous_planeι.comp
          ((Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)).smul continuous_const)
      have hc : Continuous fun q : ℝ × Chart => gaussKernel 2 1 u •
          iteratedFDeriv ℝ n (fun p : Chart => ((G p i : ℝ) : ℂ))
            (q.2 - (q.1, UnforcedLeray.B0224.planeι (Real.sqrt (ν * q.1) • u))) :=
        (hgn.comp hq).const_smul (gaussKernel 2 1 u)
      exact hc.continuousOn
  refine hcont.congr ?_
  intro q hq
  exact hct_iter_eq hG hν i n (Set.mem_Ici.1 hq.1) q.2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
