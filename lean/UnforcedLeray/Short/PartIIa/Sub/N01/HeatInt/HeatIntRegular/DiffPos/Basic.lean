import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceBounds
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntRegular.PlaneHeatFderiv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# `PartII-a:N01/9/1/2/4/3/5` (helper): differentiability of the causal heat integral

Helpers for `heatIntDiffPos`. For `s > 0` the heat integral `smoothHeatInt (s, ·)` is differentiated
under the `σ`-integral over `(0, s)`; the slices `heatSlice c F σ = σ⁻¹ • F (σ, ·)` are uniformly
`C¹`-bounded and vanish for `σ < s₁`, and the Gaussian average of the slice derivative is
differentiated through `planeHeat_fderiv_apply`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- Bounded fields have bounded heat averages (any age). -/
theorem dp_planeHeat_norm_le (θ : ℝ) (u : ℝ × ℝ → MeridC) (B : ℝ)
    (hB : ∀ x, ‖u x‖ ≤ B) (x : ℝ × ℝ) : ‖UnforcedLeray.B0224.planeHeat θ u x‖ ≤ B := by
  by_cases hθ : 0 < θ
  · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    calc ‖∫ y : UnforcedLeray.Gaussian.Euc 2,
          UnforcedLeray.Gaussian.gaussKernel 2 θ y • u (x - UnforcedLeray.B0224.planeι y)‖
        ≤ ∫ y : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ y * B :=
          norm_integral_le_of_norm_le
            ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const B)
            (ae_of_all _ fun y => by
              rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)]
              exact mul_le_mul_of_nonneg_left (hB _)
                (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y))
      _ = B := by
          rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ, one_mul]
  · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    exact hB x

theorem dp_planeHeat_zero (θ : ℝ) :
    UnforcedLeray.B0224.planeHeat θ (fun _ : ℝ × ℝ => (0 : MeridC)) = fun _ => 0 := by
  by_cases hθ : 0 < θ
  · funext x
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    simp
  · exact UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ) _

/-- Uniform bounds for a `C¹`, `c`-periodic-in-`q` function vanishing on the band complement. -/
theorem dp_comp_bounds {c s₁ s₂ R : ℝ} (hc : 0 < c) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ψ : Profile → E}
    (hC : ContDiff ℝ 1 Ψ) (hper : UnforcedLeray.B0220.QPeriodic c Ψ)
    (hz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → Ψ p = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ p, ‖Ψ p‖ ≤ M) ∧ (∀ p, ‖fderiv ℝ Ψ p‖ ≤ M) := by
  have hΨc : Continuous Ψ := hC.continuous
  have hD : Continuous (fderiv ℝ Ψ) := hC.continuous_fderiv (by norm_num)
  have hxa' : ∀ x : Profile, x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) :=
    fun x => by ext <;> simp
  have hpa : ∀ x : Profile, Ψ (x + ((0 : ℝ), c, (0 : ℝ))) = Ψ x := fun x => by
    rw [hxa' x]
    exact hper x
  have hDper : UnforcedLeray.B0220.QPeriodic c (fderiv ℝ Ψ) := by
    intro p
    have hxa : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := hxa' p
    have h1 : fderiv ℝ (fun x : Profile => Ψ (x + ((0 : ℝ), c, (0 : ℝ)))) p =
        fderiv ℝ Ψ (p + ((0 : ℝ), c, (0 : ℝ))) := fderiv_comp_add_right _
    have h2 : (fun x : Profile => Ψ (x + ((0 : ℝ), c, (0 : ℝ)))) = Ψ := funext hpa
    rw [h2] at h1
    rw [← hxa]
    exact h1.symm
  have hU : IsOpen {p : Profile | p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|} :=
    (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hDz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → fderiv ℝ Ψ p = 0 := by
    intro p hp
    have hev : Ψ =ᶠ[𝓝 p] fun _ => (0 : E) :=
      Filter.eventually_of_mem (hU.mem_nhds hp) (fun y hy => hz y hy)
    rw [hev.fderiv_eq]
    simp
  obtain ⟨M1, hM1, hb1⟩ := hsb_bounded_of_periodic_band hc hΨc hper hz
  obtain ⟨M2, hM2, hb2⟩ := hsb_bounded_of_periodic_band hc hD hDper hDz
  exact ⟨max M1 M2, le_max_of_le_left hM1, fun p => (hb1 p).trans (le_max_left _ _),
    fun p => (hb2 p).trans (le_max_right _ _)⟩

/-- The `w`-derivative of a slice of `Ψ` is bounded by the full derivative. -/
theorem dp_norm_fderiv_slice_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : Profile → E} (hΨ : Differentiable ℝ Ψ) (σ : ℝ) (w : ℝ × ℝ) :
    ‖fderiv ℝ (fun w' : ℝ × ℝ => Ψ (σ, w')) w‖ ≤ ‖fderiv ℝ Ψ (σ, w)‖ := by
  have h1 : HasFDerivAt (fun w' : ℝ × ℝ => (σ, w')) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) w :=
    hasFDerivAt_prodMk_right σ w
  have h2 : HasFDerivAt (fun w' : ℝ × ℝ => Ψ (σ, w'))
      ((fderiv ℝ Ψ (σ, w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) w :=
    (hΨ (σ, w)).hasFDerivAt.comp w h1
  rw [h2.fderiv]
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp [Prod.norm_def])
  calc ‖(fderiv ℝ Ψ (σ, w)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))‖
      ≤ ‖fderiv ℝ Ψ (σ, w)‖ * ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        (fderiv ℝ Ψ (σ, w)).opNorm_comp_le _
    _ ≤ ‖fderiv ℝ Ψ (σ, w)‖ * 1 := mul_le_mul_of_nonneg_left hinr (norm_nonneg _)
    _ = ‖fderiv ℝ Ψ (σ, w)‖ := mul_one _

theorem dp_unpack {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) :
    ContDiff ℝ ∞ F ∧ (∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) := by
  obtain ⟨h1, h2, -⟩ := hF
  exact ⟨h1, h2⟩

theorem dp_heatSlice_eq {c : ℝ} {F : Profile → MeridC}
    (hFper : ∀ p : Profile, F (p.1, p.2.1 + c, p.2.2) = F p) (σ : ℝ) (w : ℝ × ℝ) :
    heatSlice c F σ w = σ⁻¹ • F (σ, w) := by
  unfold heatSlice UnforcedLeray.B0220.periodize
  have hq : UnforcedLeray.B0220.QPeriodic c (fun q : Profile => q.1⁻¹ • F q) := by
    intro p
    show p.1⁻¹ • F (p.1, p.2.1 + c, p.2.2) = p.1⁻¹ • F p
    rw [hFper p]
  exact UnforcedLeray.B0220.periodic_reduceIoc_eq _ hq σ w.1 w.2

theorem dp_support {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) :
    ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ σ : ℝ, σ < s₁ → ∀ w : ℝ × ℝ, heatSlice c F σ w = 0 := by
  obtain ⟨-, hFper⟩ := dp_unpack hF
  obtain ⟨_, _, s₁, s₂, R, hs₁, hz⟩ := hF
  exact ⟨s₁, hs₁, fun σ hσ w => by
    rw [dp_heatSlice_eq hFper σ w, hz (σ, w) (Or.inl hσ), smul_zero]⟩

theorem dp_slice_bounds {c : ℝ} {F : Profile → MeridC} (hc : 0 < c) (hF : IsSmoothForceFn c F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, ∀ w : ℝ × ℝ,
      ‖heatSlice c F σ w‖ ≤ M ∧ ‖fderiv ℝ (heatSlice c F σ) w‖ ≤ M := by
  obtain ⟨hFc, hFper⟩ := dp_unpack hF
  obtain ⟨_, _, s₁, s₂, R, hs₁, hz⟩ := hF
  have hF1 : ContDiff ℝ 1 F := hFc.of_le (by simp)
  obtain ⟨M, hM0, hv, hd⟩ := dp_comp_bounds hc hF1 hFper hz
  have hdF : Differentiable ℝ F := hFc.differentiable (by norm_num)
  have hK : 0 ≤ M * s₁⁻¹ := mul_nonneg hM0 (inv_nonneg.2 hs₁.le)
  refine ⟨M * s₁⁻¹, hK, fun σ w => ?_⟩
  by_cases hσ : σ < s₁
  · have h0 : heatSlice c F σ = fun _ => 0 := by
      funext w'
      rw [dp_heatSlice_eq hFper σ w', hz (σ, w') (Or.inl hσ), smul_zero]
    rw [h0]
    simp [hK]
  · push_neg at hσ
    have hσ0 : 0 < σ := lt_of_lt_of_le hs₁ hσ
    have hnorm : ‖σ⁻¹‖ ≤ s₁⁻¹ := by
      rw [Real.norm_of_nonneg (inv_nonneg.2 hσ0.le)]
      exact inv_anti₀ hs₁ hσ
    have hfun : heatSlice c F σ = fun w' => σ⁻¹ • F (σ, w') :=
      funext fun w' => dp_heatSlice_eq hFper σ w'
    have hdw : Differentiable ℝ (fun w' : ℝ × ℝ => F (σ, w')) := fun w' =>
      DifferentiableAt.comp w' (hdF (σ, w')) (hasFDerivAt_prodMk_right σ w').differentiableAt
    constructor
    · rw [dp_heatSlice_eq hFper σ w, norm_smul]
      calc ‖σ⁻¹‖ * ‖F (σ, w)‖ ≤ s₁⁻¹ * M :=
            mul_le_mul hnorm (hv _) (norm_nonneg _) (inv_nonneg.2 hs₁.le)
        _ = M * s₁⁻¹ := mul_comm _ _
    · have hsm : HasFDerivAt (fun w' : ℝ × ℝ => σ⁻¹ • F (σ, w'))
          (σ⁻¹ • fderiv ℝ (fun w' : ℝ × ℝ => F (σ, w')) w) w :=
        (hdw w).hasFDerivAt.const_smul σ⁻¹
      rw [hfun, hsm.fderiv, norm_smul]
      calc ‖σ⁻¹‖ * ‖fderiv ℝ (fun w' : ℝ × ℝ => F (σ, w')) w‖
          ≤ s₁⁻¹ * M :=
            mul_le_mul hnorm ((dp_norm_fderiv_slice_le hdF σ w).trans (hd _))
              (norm_nonneg _) (inv_nonneg.2 hs₁.le)
        _ = M * s₁⁻¹ := mul_comm _ _

theorem dp_slice_contDiff {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (σ : ℝ) :
    ContDiff ℝ 1 (heatSlice c F σ) := by
  obtain ⟨hFc, hFper⟩ := dp_unpack hF
  have hfun : heatSlice c F σ = fun w : ℝ × ℝ => σ⁻¹ • F (σ, w) :=
    funext fun w => dp_heatSlice_eq hFper σ w
  rw [hfun]
  have hF1 : ContDiff ℝ 1 F := hFc.of_le (by simp)
  exact ContDiff.const_smul σ⁻¹ (hF1.comp ((contDiff_const (c := σ)).prodMk contDiff_id))

theorem dp_fderiv_slice {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (σ : ℝ)
    (z : ℝ × ℝ) :
    fderiv ℝ (heatSlice c F σ) z =
      σ⁻¹ • (fderiv ℝ F (σ, z)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
  obtain ⟨hFc, hFper⟩ := dp_unpack hF
  have hdF : Differentiable ℝ F := hFc.differentiable (by norm_num)
  have hfun : heatSlice c F σ = fun w : ℝ × ℝ => σ⁻¹ • F (σ, w) :=
    funext fun w => dp_heatSlice_eq hFper σ w
  have hdw : HasFDerivAt (fun w : ℝ × ℝ => F (σ, w))
      ((fderiv ℝ F (σ, z)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) z :=
    (hdF (σ, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right σ z)
  have hsm : HasFDerivAt (fun w : ℝ × ℝ => σ⁻¹ • F (σ, w))
      (σ⁻¹ • ((fderiv ℝ F (σ, z)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)))) z :=
    hdw.const_smul σ⁻¹
  rw [hfun, hsm.fderiv]

theorem dp_meas_gauss {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 (f p.1) p.2) := by
  unfold UnforcedLeray.Gaussian.gaussKernel
  fun_prop

theorem dp_meas_slice {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (y : ℝ × ℝ) :
    Measurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      heatSlice c F p.1 (y - UnforcedLeray.B0224.planeι p.2)) := by
  obtain ⟨hFc, hFper⟩ := dp_unpack hF
  have hfun : (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      heatSlice c F p.1 (y - UnforcedLeray.B0224.planeι p.2)) =
      fun p => p.1⁻¹ • F (p.1, y - UnforcedLeray.B0224.planeι p.2) :=
    funext fun p => dp_heatSlice_eq hFper _ _
  rw [hfun]
  exact (measurable_fst.inv).smul (hFc.continuous.measurable.comp
    (measurable_fst.prodMk (measurable_const.sub
      (UnforcedLeray.B0224.measurable_planeι.comp measurable_snd))))

theorem dp_meas_fderiv {c : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (y : ℝ × ℝ) :
    Measurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      fderiv ℝ (heatSlice c F p.1) (y - UnforcedLeray.B0224.planeι p.2)) := by
  obtain ⟨hFc, hFper⟩ := dp_unpack hF
  have hFd : Continuous (fderiv ℝ F) := hFc.continuous_fderiv (by norm_num)
  have hc1 : Continuous (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      fderiv ℝ F (p.1, y - UnforcedLeray.B0224.planeι p.2)) :=
    hFd.comp (continuous_fst.prodMk
      (continuous_const.sub (UnforcedLeray.B0224.continuous_planeι.comp continuous_snd)))
  have hfun : (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      fderiv ℝ (heatSlice c F p.1) (y - UnforcedLeray.B0224.planeι p.2)) =
      fun p => p.1⁻¹ • (fderiv ℝ F (p.1, y - UnforcedLeray.B0224.planeι p.2)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) :=
    funext fun p => dp_fderiv_slice hF p.1 (y - UnforcedLeray.B0224.planeι p.2)
  rw [hfun]
  exact (measurable_fst.inv).smul (hc1.clm_comp continuous_const).measurable

/-- The Gaussian average of the slice derivative: the derivative of `planeHeat` at age `ν (s-σ)`. -/
def dpD (c ν s : ℝ) (F : Profile → MeridC) (σ : ℝ) (y : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] MeridC :=
  ∫ e : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - σ)) e •
    fderiv ℝ (heatSlice c F σ) (y - UnforcedLeray.B0224.planeι e)

/-- The Gaussian average of the slice: `planeHeat (ν (s-σ)) (heatSlice c F σ) y`. -/
def dpP (c ν s : ℝ) (F : Profile → MeridC) (σ : ℝ) (y : ℝ × ℝ) : MeridC :=
  ∫ e : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - σ)) e •
    heatSlice c F σ (y - UnforcedLeray.B0224.planeι e)

/-- The weight `(σ/s)^μ` of the causal heat integral. -/
def dpW (s : ℝ) (μ : ℂ) (σ : ℝ) : ℂ := ((σ / s : ℝ) : ℂ) ^ μ

/-- The `σ`-integrand of the heat integral at age `s`. -/
def dpF (c ν s : ℝ) (μ : ℂ) (F : Profile → MeridC) (σ : ℝ) (y : ℝ × ℝ) : MeridC :=
  dpW s μ σ • UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (heatSlice c F σ) y

/-- The `y`-derivative of the `σ`-integrand. -/
def dpF' (c ν s : ℝ) (μ : ℂ) (F : Profile → MeridC) (σ : ℝ) (y : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] MeridC :=
  dpW s μ σ • dpD c ν s F σ y

/-- Dominating function for the `σ`-integral. -/
def dpBound (s₁ s B M : ℝ) : ℝ → ℝ := Set.indicator (Icc s₁ s) (fun _ => B * M)

theorem dp_sm_D {c ν s : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (y : ℝ × ℝ) :
    StronglyMeasurable (fun σ : ℝ => dpD c ν s F σ y) := by
  have hm : Measurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - p.1)) p.2 •
        fderiv ℝ (heatSlice c F p.1) (y - UnforcedLeray.B0224.planeι p.2)) :=
    (dp_meas_gauss (f := fun σ => ν * (s - σ)) (by fun_prop)).smul (dp_meas_fderiv hF y)
  unfold dpD
  exact StronglyMeasurable.integral_prod_right' (ν := volume) hm.stronglyMeasurable

theorem dp_sm_P {c ν s : ℝ} {F : Profile → MeridC} (hF : IsSmoothForceFn c F) (y : ℝ × ℝ) :
    StronglyMeasurable (fun σ : ℝ => dpP c ν s F σ y) := by
  have hm : Measurable (fun p : ℝ × UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 (ν * (s - p.1)) p.2 •
        heatSlice c F p.1 (y - UnforcedLeray.B0224.planeι p.2)) :=
    (dp_meas_gauss (f := fun σ => ν * (s - σ)) (by fun_prop)).smul (dp_meas_slice hF y)
  unfold dpP
  exact StronglyMeasurable.integral_prod_right' (ν := volume) hm.stronglyMeasurable

theorem dp_integrable_D {θ : ℝ} (hθ : 0 < θ) {S : ℝ × ℝ → MeridC} (hS : ContDiff ℝ 1 S) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ S x‖ ≤ M) (y : ℝ × ℝ) :
    Integrable (fun e : UnforcedLeray.Gaussian.Euc 2 =>
      UnforcedLeray.Gaussian.gaussKernel 2 θ e • fderiv ℝ S (y - UnforcedLeray.B0224.planeι e)) := by
  refine Integrable.mono' ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const M)
    ?_ (ae_of_all _ fun e => ?_)
  · exact (Continuous.smul (UnforcedLeray.Gaussian.continuous_gaussKernel (d := 2) θ)
      ((hS.continuous_fderiv (by norm_num)).comp
        (continuous_const.sub UnforcedLeray.B0224.continuous_planeι))).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ e)]
    exact mul_le_mul_of_nonneg_left (hM _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ e)

theorem dp_hasFDerivAt_planeHeat {θ : ℝ} (hθ : 0 < θ) {S : ℝ × ℝ → MeridC} (hS : ContDiff ℝ 1 S)
    {M : ℝ} (hM : ∀ x, ‖S x‖ ≤ M ∧ ‖fderiv ℝ S x‖ ≤ M) (y : ℝ × ℝ) :
    HasFDerivAt (UnforcedLeray.B0224.planeHeat θ S)
      (∫ e : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ e •
        fderiv ℝ S (y - UnforcedLeray.B0224.planeι e)) y := by
  obtain ⟨hdiff, hfd⟩ := planeHeat_fderiv_apply θ hθ S hS ⟨M, fun x => hM x⟩
  have hint := dp_integrable_D hθ hS (fun x => (hM x).2) y
  have heq : fderiv ℝ (UnforcedLeray.B0224.planeHeat θ S) y =
      ∫ e : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ e •
        fderiv ℝ S (y - UnforcedLeray.B0224.planeι e) := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hfd y v, ContinuousLinearMap.integral_apply hint v,
      UnforcedLeray.B0224.planeHeat_of_pos hθ]
    simp only [ContinuousLinearMap.smul_apply]
  rw [← heq]
  exact (hdiff y).hasFDerivAt

theorem dp_norm_dpD_le {θ : ℝ} (hθ : 0 < θ) {S : ℝ × ℝ → MeridC} (hS : ContDiff ℝ 1 S) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ S x‖ ≤ M) (y : ℝ × ℝ) :
    ‖∫ e : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ e •
        fderiv ℝ S (y - UnforcedLeray.B0224.planeι e)‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y)
  have hint := dp_integrable_D hθ hS hM y
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun v => ?_)
  rw [ContinuousLinearMap.integral_apply hint v]
  have hpt : ∀ e : UnforcedLeray.Gaussian.Euc 2,
      ‖(UnforcedLeray.Gaussian.gaussKernel 2 θ e •
        fderiv ℝ S (y - UnforcedLeray.B0224.planeι e)) v‖ ≤
        UnforcedLeray.Gaussian.gaussKernel 2 θ e * (M * ‖v‖) := by
    intro e
    rw [ContinuousLinearMap.smul_apply, norm_smul,
      Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ e)]
    refine mul_le_mul_of_nonneg_left ?_ (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ e)
    exact ((fderiv ℝ S (y - UnforcedLeray.B0224.planeι e)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg v))
  calc ‖∫ e : UnforcedLeray.Gaussian.Euc 2, (UnforcedLeray.Gaussian.gaussKernel 2 θ e •
        fderiv ℝ S (y - UnforcedLeray.B0224.planeι e)) v‖
      ≤ ∫ e : UnforcedLeray.Gaussian.Euc 2, UnforcedLeray.Gaussian.gaussKernel 2 θ e * (M * ‖v‖) :=
        norm_integral_le_of_norm_le
          ((UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).mul_const _)
          (ae_of_all _ hpt)
    _ = M * ‖v‖ := by
        rw [integral_mul_const, UnforcedLeray.Gaussian.integral_gaussKernel (d := 2) hθ, one_mul]

theorem dp_W_bound {s : ℝ} (hs : 0 < s) (μ : ℂ) {s₁ : ℝ} (hs₁ : 0 < s₁) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ Icc s₁ s, ‖dpW s μ σ‖ ≤ B := by
  have hcont : ContinuousOn (fun σ : ℝ => (σ / s) ^ μ.re) (Icc s₁ s) := by
    refine ContinuousOn.rpow_const ((continuous_id.div_const s).continuousOn) ?_
    intro x hx
    exact Or.inl (ne_of_gt (div_pos (lt_of_lt_of_le hs₁ hx.1) hs))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun σ hσ => ?_⟩
  have hpos : 0 < σ / s := div_pos (lt_of_lt_of_le hs₁ hσ.1) hs
  have h1 := hB σ hσ
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)] at h1
  unfold dpW
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  exact h1.trans (le_max_left _ _)

end UnforcedLeray.Short.PartIIa.N01
