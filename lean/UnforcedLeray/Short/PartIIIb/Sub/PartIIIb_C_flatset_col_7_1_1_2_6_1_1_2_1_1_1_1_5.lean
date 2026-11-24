import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2_1_1_1_1_1
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Decomposition of `T0gGrad` (N1/5)

The gradient `(∂_q, ∂_η)` of `Ψ = e^{-t/2} e^{θ(s) Δ_{q,η}} Φ(e^t s, ·)` (source
`the November 2 reference manuscript` 1650-1654)
is the heat flow of the gradient of `Φ(e^t s, ·)`: differentiation under the Gaussian integral.
Inputs: joint smoothness of `Ψ` (`T0gSmooth`) and bounded derivatives of a profile test
(`T0gBdd`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)
open UnforcedLeray.B0224 (planeHeat planeι)
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- Differentiation of the planar heat flow along a direction (scalar `C¹` data with bounded
value and derivative). -/
theorem t0g_planeHeat_hasDerivAt {θ : ℝ} {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) {M : ℝ}
    (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (hb : ∀ z, ‖u z‖ ≤ M) (v x : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ => planeHeat θ u (x + r • v))
      (planeHeat θ (fun z => fderiv ℝ u z v) x) 0 := by
  by_cases hθ : 0 < θ
  · simp only [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    have hG : Integrable (gaussKernel 2 θ) := UnforcedLeray.Gaussian.integrable_gaussKernel hθ
    have hGc : Continuous (gaussKernel 2 θ) := UnforcedLeray.Gaussian.continuous_gaussKernel θ
    have hGn : ∀ y : Euc 2, 0 ≤ gaussKernel 2 θ y := UnforcedLeray.Gaussian.gaussKernel_nonneg hθ
    have hu0 : Continuous u := hu.continuous
    have hu1 : Continuous (fun z => fderiv ℝ u z) := hu.continuous_fderiv one_ne_zero
    have hdiff : ∀ (r : ℝ) (y : Euc 2), HasDerivAt (fun r : ℝ => u (x + r • v - planeι y))
        (fderiv ℝ u (x + r • v - planeι y) v) r := by
      intro r y
      have h1 : HasDerivAt (fun r : ℝ => x + r • v - planeι y) v r := by
        have := (((hasDerivAt_id r).smul_const v).const_add x).sub_const (planeι y)
        simpa using this
      exact ((hu.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt r h1
    have hcpl : ∀ r : ℝ, Continuous (fun y : Euc 2 => x + r • v - planeι y) := fun r =>
      continuous_const.sub UnforcedLeray.B0224.continuous_planeι
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := (0 : ℝ))
      (s := Set.univ) (μ := volume)
      (F := fun (r : ℝ) (y : Euc 2) => gaussKernel 2 θ y • u (x + r • v - planeι y))
      (F' := fun (r : ℝ) (y : Euc 2) =>
        gaussKernel 2 θ y • fderiv ℝ u (x + r • v - planeι y) v)
      (bound := fun y => gaussKernel 2 θ y * (M * ‖v‖)) Filter.univ_mem
      (Filter.Eventually.of_forall fun r =>
        (hGc.smul (hu0.comp (hcpl r))).aestronglyMeasurable)
      (by
        refine Integrable.mono' (hG.mul_const M) (hGc.smul (hu0.comp (hcpl 0))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => ?_)
        rw [norm_smul, Real.norm_of_nonneg (hGn y)]
        exact mul_le_mul_of_nonneg_left (hb _) (hGn y))
      (hGc.smul ((hu1.clm_apply continuous_const).comp (hcpl 0))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y r _ => by
        rw [norm_smul, Real.norm_of_nonneg (hGn y)]
        refine mul_le_mul_of_nonneg_left ?_ (hGn y)
        exact ((fderiv ℝ u _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))
      (hG.mul_const _)
      (Filter.Eventually.of_forall fun y r _ => (hdiff r y).const_smul (gaussKernel 2 θ y))
    simpa using key.2
  · simp only [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    have h1 : HasDerivAt (fun r : ℝ => x + r • v) v 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      simpa using this
    have := ((hu.differentiable (by norm_num)) (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have e : x + (0 : ℝ) • v = x := by simp
    rw [e] at this
    exact this

/-- Planar heat commutes with continuous linear maps (bounded continuous data). -/
theorem t0g_planeHeat_clm {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℝ] G) (θ : ℝ) {u : ℝ × ℝ → F} (hu : Continuous u) {M : ℝ}
    (hb : ∀ z, ‖u z‖ ≤ M) (x : ℝ × ℝ) :
    planeHeat θ (fun z => L (u z)) x = L (planeHeat θ u x) := by
  by_cases hθ : 0 < θ
  · simp only [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    have hG : Integrable (gaussKernel 2 θ) := UnforcedLeray.Gaussian.integrable_gaussKernel hθ
    have hGc : Continuous (gaussKernel 2 θ) := UnforcedLeray.Gaussian.continuous_gaussKernel θ
    have hGn : ∀ y : Euc 2, 0 ≤ gaussKernel 2 θ y := UnforcedLeray.Gaussian.gaussKernel_nonneg hθ
    have hint : Integrable (fun y : Euc 2 => gaussKernel 2 θ y • u (x - planeι y)) := by
      refine Integrable.mono' (hG.mul_const M)
        (hGc.smul (hu.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [norm_smul, Real.norm_of_nonneg (hGn y)]
      exact mul_le_mul_of_nonneg_left (hb _) (hGn y)
    rw [← ContinuousLinearMap.integral_comp_comm L hint]
    simp [map_smul]
  · simp [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

/-- The embedding `ℝ² → ℂ²`, `(x, y) ↦ (x, y)`. -/
def t0gL : ℝ × ℝ →L[ℝ] MeridC :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => !₂[(w.1 : ℂ), (w.2 : ℂ)]
      map_add' := by
        intro a b
        ext i
        fin_cases i <;> simp
      map_smul' := by
        intro r a
        ext i
        fin_cases i <;> simp }

theorem t0gL_apply (w : ℝ × ℝ) : t0gL w = !₂[(w.1 : ℂ), (w.2 : ℂ)] := rfl

/-- Partial derivative of `Ψ` in a `(q, η)` direction. -/
theorem t0g_fderiv_dir (hS : T0gSmooth) (hB : T0gBdd) (c ν t : ℝ) (hc : 0 < c) (Φ : Profile → ℝ)
    (hΦ : IsProfileTest c Φ) (p : Profile) (w : ℝ × ℝ) :
    fderiv ℝ (t0gPsi ν t Φ) p (0, w) =
      Real.exp (-t / 2) * planeHeat (ν * p.1 * (Real.exp t - 1))
        (fun z => fderiv ℝ Φ (Real.exp t * p.1, z) (0, w)) p.2 := by
  obtain ⟨C0, hC0⟩ := hB c hc Φ hΦ 0
  obtain ⟨C1, hC1⟩ := hB c hc Φ hΦ 1
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by norm_num)
  set a := Real.exp t * p.1 with ha
  set θ := ν * p.1 * (Real.exp t - 1) with hθ
  set u : ℝ × ℝ → ℝ := fun z => Φ (a, z) with hu
  have hpair : ∀ z : ℝ × ℝ, HasFDerivAt (fun z : ℝ × ℝ => (a, z))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) z := fun z => hasFDerivAt_prodMk_right a z
  have hfd : ∀ z : ℝ × ℝ, HasFDerivAt u ((fderiv ℝ Φ (a, z)).comp
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) z := fun z =>
    (hΦd (a, z)).hasFDerivAt.comp z (hpair z)
  have hfu : ∀ z (w : ℝ × ℝ), fderiv ℝ u z w = fderiv ℝ Φ (a, z) (0, w) := by
    intro z w
    rw [(hfd z).fderiv]
    simp
  have hu1 : ContDiff ℝ 1 u := by
    have : ContDiff ℝ 1 Φ := hΦ.smooth.of_le (by exact_mod_cast le_top)
    exact this.comp (contDiff_const.prodMk contDiff_id)
  have hM0 : 0 ≤ max C0 C1 := by
    refine le_trans ?_ (le_max_left _ _)
    exact (norm_nonneg _).trans (hC0 0)
  have hb : ∀ z, ‖u z‖ ≤ max C0 C1 := by
    intro z
    have := hC0 (a, z)
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_max_left _ _)
  have hM : ∀ z, ‖fderiv ℝ u z‖ ≤ max C0 C1 := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun w => ?_
    rw [hfu]
    have h1 := hC1 (a, z)
    rw [norm_iteratedFDeriv_one] at h1
    calc ‖fderiv ℝ Φ (a, z) (0, w)‖ ≤ ‖fderiv ℝ Φ (a, z)‖ * ‖((0 : ℝ), w)‖ :=
          (fderiv ℝ Φ (a, z)).le_opNorm _
      _ ≤ max C0 C1 * ‖w‖ := by
          have : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
          rw [this]
          exact mul_le_mul_of_nonneg_right (h1.trans (le_max_right _ _)) (norm_nonneg _)
  have hcore := (t0g_planeHeat_hasDerivAt (θ := θ) hu1 hM hb w p.2).const_mul (Real.exp (-t / 2))
  have hΨd : DifferentiableAt ℝ (t0gPsi ν t Φ) p :=
    ((hS c ν t hc Φ hΦ).differentiable (by simp)) p
  have h1 : HasDerivAt (fun r : ℝ => p + r • ((0 : ℝ), w)) ((0 : ℝ), w) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ), w)).const_add p
    simpa using this
  have h2 := hΨd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  have h3 : (fun r : ℝ => t0gPsi ν t Φ (p + r • ((0 : ℝ), w))) =
      fun r : ℝ => Real.exp (-t / 2) * planeHeat θ u (p.2 + r • w) := by
    funext r
    simp [t0gPsi, hθ, hu, ha, Prod.smul_def, Prod.ext_iff]
  have h2' : HasDerivAt (fun r : ℝ => t0gPsi ν t Φ (p + r • ((0 : ℝ), w)))
      (fderiv ℝ (t0gPsi ν t Φ) p (0, w)) 0 := by
    exact h2
  rw [h3] at h2'
  have := h2'.unique hcore
  rw [this]
  congr 2
  funext z
  exact hfu z w

theorem t0gGrad_of (hS : T0gSmooth) (hB : T0gBdd) : T0gGrad := by
  intro c ν t hc Φ hΦ p
  obtain ⟨C0, hC0⟩ := hB c hc Φ hΦ 0
  obtain ⟨C1, hC1⟩ := hB c hc Φ hΦ 1
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by norm_num)
  set a := Real.exp t * p.1 with ha
  set θ := ν * p.1 * (Real.exp t - 1) with hθ
  have hQ := t0g_fderiv_dir hS hB c ν t hc Φ hΦ p (1, 0)
  have hE := t0g_fderiv_dir hS hB c ν t hc Φ hΦ p (0, 1)
  -- the pair of partial derivatives of `Φ(a, ·)`
  set u2 : ℝ × ℝ → ℝ × ℝ := fun z => (dQ Φ (a, z), dEta Φ (a, z)) with hu2
  have hcont : Continuous u2 := by
    have hc : Continuous (fun p : Profile => fderiv ℝ Φ p) := hΦ.smooth.continuous_fderiv (by simp)
    have hz : Continuous (fun z : ℝ × ℝ => (a, z)) := continuous_const.prodMk continuous_id
    refine Continuous.prodMk ?_ ?_
    · exact (hc.comp hz).clm_apply continuous_const
    · exact (hc.comp hz).clm_apply continuous_const
  have hbd : ∀ z, ‖u2 z‖ ≤ C1 := by
    intro z
    have h1 := hC1 (a, z)
    rw [norm_iteratedFDeriv_one] at h1
    have key : ∀ w : ℝ × ℝ, ‖w‖ ≤ 1 → ‖fderiv ℝ Φ (a, z) ((0 : ℝ), w)‖ ≤ C1 := by
      intro w hw
      calc ‖fderiv ℝ Φ (a, z) ((0 : ℝ), w)‖ ≤ ‖fderiv ℝ Φ (a, z)‖ * ‖((0 : ℝ), w)‖ :=
            (fderiv ℝ Φ (a, z)).le_opNorm _
        _ ≤ C1 * 1 := by
            have : ‖((0 : ℝ), w)‖ = ‖w‖ := by simp [Prod.norm_def]
            rw [this]
            exact mul_le_mul h1 hw (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = C1 := mul_one _
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · exact key (1, 0) (by simp [Prod.norm_def])
    · exact key (0, 1) (by simp [Prod.norm_def])
  have hcg : (fun z : ℝ × ℝ => UnforcedLeray.Short.PartIIa.cgrad 0 Φ (a, z)) =
      fun z => t0gL (u2 z) := by
    funext z
    simp [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.Deps, t0gL_apply, hu2]
  have hfst := t0g_planeHeat_clm (ContinuousLinearMap.fst ℝ ℝ ℝ) θ hcont hbd p.2
  have hsnd := t0g_planeHeat_clm (ContinuousLinearMap.snd ℝ ℝ ℝ) θ hcont hbd p.2
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at hfst hsnd
  rw [hcg, t0g_planeHeat_clm t0gL θ hcont hbd p.2, t0gL_apply]
  have hdQ : dQ (t0gPsi ν t Φ) p =
      Real.exp (-t / 2) * (planeHeat θ u2 p.2).1 := by
    rw [← hfst]
    exact hQ
  have hdE : dEta (t0gPsi ν t Φ) p =
      Real.exp (-t / 2) * (planeHeat θ u2 p.2).2 := by
    rw [← hsnd]
    exact hE
  ext i
  fin_cases i
  · simp [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.Deps, hdQ]
  · simp [UnforcedLeray.Short.PartIIa.cgrad, hdE]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
