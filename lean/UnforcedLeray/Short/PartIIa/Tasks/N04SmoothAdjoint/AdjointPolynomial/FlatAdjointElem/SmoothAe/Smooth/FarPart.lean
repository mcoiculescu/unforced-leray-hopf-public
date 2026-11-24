import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.SmoothAe.Smooth.GlueKernel
import UnforcedLeray.Lib.Kernels.ParamIntegral
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Integral

/-!
# Smoothness of `flatAdjointRep` for Spatially Far-Field Profiles (`FarPart`)

Proves `ContDiffOn ℝ ∞ (flatAdjointRep ν μ w) (farNhd p₀)` around any `p₀` with `0 < p₀.1` for a
continuous bounded band-supported profile `w` that vanishes on the disk
`(q.2.1 - p₀.2.1) ^ 2 + (q.2.2 - p₀.2.2) ^ 2 ≤ 1`. On `farNhd p₀`, substituting `τ = e^t * p.1`
and `z = p.2 - planeι y` expresses `flatAdjointRep ν μ w p` as a smooth prefactor in `p.1` times a
fixed-domain integral against `safeHeatProfile ν τ z p` over `Icc σ H1 × ℝ²`, where all
derivatives fall on `safeHeatProfile` and `UnforcedLeray.Kernels.contDiffOn_integral` applies.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0224 (planeHeat planeHeat_of_pos planeι planeι_apply)
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-! ### 1. Open neighborhood `farNhd` and planar majorant inequalities -/

/-- Open neighborhood of `p₀ = (s₀, x₀)` (`0 < s₀`) on which `p.1 ∈ (s₀ / 2, s₀ + 1)` and
`(p.2.1 - x₀.1) ^ 2 + (p.2.2 - x₀.2) ^ 2 < 1 / 8`. -/
def farNhd (p₀ : Profile) : Set Profile :=
  {p : Profile | p₀.1 / 2 < p.1 ∧ p.1 < p₀.1 + 1 ∧
    (p.2.1 - p₀.2.1) ^ 2 + (p.2.2 - p₀.2.2) ^ 2 < 1 / 8}

theorem isOpen_farNhd (p₀ : Profile) : IsOpen (farNhd p₀) := by
  unfold farNhd
  have hc1 : Continuous (fun p : Profile => p.2.1 - p₀.2.1) :=
    (continuous_fst.comp continuous_snd).sub continuous_const
  have hc2 : Continuous (fun p : Profile => p.2.2 - p₀.2.2) :=
    (continuous_snd.comp continuous_snd).sub continuous_const
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt ((hc1.pow 2).add (hc2.pow 2)) continuous_const))

theorem mem_farNhd {p₀ : Profile} (hp₀ : 0 < p₀.1) : p₀ ∈ farNhd p₀ := by
  refine ⟨by linarith, by linarith, ?_⟩
  norm_num

private theorem inv_one_add_sub_sq_le {R u z : ℝ} (hR : 1 ≤ R) (hu : u ^ 2 ≤ R ^ 2) :
    (1 + (u - z) ^ 2)⁻¹ ≤ (8 * R ^ 2) * (1 + z ^ 2)⁻¹ := by
  have hle : 1 + z ^ 2 ≤ (8 * R ^ 2) * (1 + (u - z) ^ 2) := by
    by_cases hz : z ^ 2 ≤ 4 * R ^ 2
    · have hR2 : 1 ≤ R ^ 2 := by nlinarith
      nlinarith [sq_nonneg (u - z)]
    · have hhalf : (1 / 2 : ℝ) * z ^ 2 - u ^ 2 ≤ (u - z) ^ 2 := by
        nlinarith [sq_nonneg (z - 2 * u)]
      have hquarter : (1 / 4 : ℝ) * z ^ 2 ≤ (u - z) ^ 2 := by linarith
      have hR2 : 4 ≤ 8 * R ^ 2 := by nlinarith
      have h4 : 1 + z ^ 2 ≤ 4 * (1 + (u - z) ^ 2) := by linarith
      nlinarith [sq_nonneg (u - z)]
  have hpos1 : 0 < 1 + z ^ 2 := by positivity
  have hposR : 0 < 8 * R ^ 2 := by positivity
  rw [show (8 * R ^ 2) * (1 + z ^ 2)⁻¹ = ((1 + z ^ 2) / (8 * R ^ 2))⁻¹ by field_simp]
  exact inv_anti₀ (div_pos hpos1 hposR) ((div_le_iff₀' hposR).2 hle)

private theorem planar_decay_majorant {p₀ p : Profile} (hp : p ∈ farNhd p₀) (z : ℝ × ℝ) :
    ((1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2)⁻¹) ^ 2 ≤
      (64 * (1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2) ^ 4) *
        ((1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹) := by
  set R : ℝ := 1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2
  have hR1 : 1 ≤ R := by unfold R; nlinarith [sq_nonneg p₀.2.1, sq_nonneg p₀.2.2]
  have hp_ball : (p.2.1 - p₀.2.1) ^ 2 + (p.2.2 - p₀.2.2) ^ 2 < 1 / 8 := hp.2.2
  have hu1 : p.2.1 ^ 2 ≤ R ^ 2 := by
    have h1 : p.2.1 ^ 2 ≤ 2 * (p.2.1 - p₀.2.1) ^ 2 + 2 * p₀.2.1 ^ 2 := by
      nlinarith [sq_nonneg (p.2.1 - 2 * p₀.2.1)]
    have h2 : 2 * (p.2.1 - p₀.2.1) ^ 2 + 2 * p₀.2.1 ^ 2 ≤ R ^ 2 := by
      unfold R
      nlinarith [sq_nonneg (p.2.2 - p₀.2.2), sq_nonneg p₀.2.1, sq_nonneg p₀.2.2]
    exact h1.trans h2
  have hu2 : p.2.2 ^ 2 ≤ R ^ 2 := by
    have h1 : p.2.2 ^ 2 ≤ 2 * (p.2.2 - p₀.2.2) ^ 2 + 2 * p₀.2.2 ^ 2 := by
      nlinarith [sq_nonneg (p.2.2 - 2 * p₀.2.2)]
    have h2 : 2 * (p.2.2 - p₀.2.2) ^ 2 + 2 * p₀.2.2 ^ 2 ≤ R ^ 2 := by
      unfold R
      nlinarith [sq_nonneg (p.2.1 - p₀.2.1), sq_nonneg p₀.2.1, sq_nonneg p₀.2.2]
    exact h1.trans h2
  have hb1 := inv_one_add_sub_sq_le hR1 hu1 (z := z.1)
  have hb2 := inv_one_add_sub_sq_le hR1 hu2 (z := z.2)
  have hprod_den :
      (1 + (p.2.1 - z.1) ^ 2) * (1 + (p.2.2 - z.2) ^ 2) ≤
        (1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (p.2.1 - z.1), sq_nonneg (p.2.2 - z.2)]
  have hinv_le :
      ((1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2)⁻¹) ^ 2 ≤
        (1 + (p.2.1 - z.1) ^ 2)⁻¹ * (1 + (p.2.2 - z.2) ^ 2)⁻¹ := by
    rw [inv_pow, ← mul_inv]
    exact inv_anti₀ (by positivity) hprod_den
  calc ((1 + (p.2.1 - z.1) ^ 2 + (p.2.2 - z.2) ^ 2)⁻¹) ^ 2
      ≤ (1 + (p.2.1 - z.1) ^ 2)⁻¹ * (1 + (p.2.2 - z.2) ^ 2)⁻¹ := hinv_le
    _ ≤ ((8 * R ^ 2) * (1 + z.1 ^ 2)⁻¹) * ((8 * R ^ 2) * (1 + z.2 ^ 2)⁻¹) :=
        mul_le_mul hb1 hb2 (by positivity) (by positivity)
    _ = (64 * R ^ 4) * ((1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹) := by ring

private theorem integrable_prodWeight (σ H1 C : ℝ) :
    Integrable (fun a : ℝ × (ℝ × ℝ) => C * ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹))
      ((volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))) := by
  have h1 : Integrable (fun _ : ℝ => C) (volume.restrict (Icc σ H1)) :=
    integrableOn_const (hs := measure_Icc_lt_top.ne)
  have h2 : Integrable (fun z : ℝ × ℝ => (1 + z.1 ^ 2)⁻¹ * (1 + z.2 ^ 2)⁻¹)
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq
  exact h1.mul_prod h2

private theorem prod_restrict_band (σ H1 : ℝ) :
    (volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ)) =
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Icc σ H1 ×ˢ univ) := by
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ), ← Measure.prod_restrict,
    Measure.restrict_univ]

private theorem continuous_safeHeatProfile_param (ν : ℝ) (p : Profile) :
    Continuous (fun a : ℝ × (ℝ × ℝ) => safeHeatProfile ν a.1 a.2 p) := by
  show Continuous (fun a : ℝ × (ℝ × ℝ) => safeHeatPair (ν * (a.1 - p.1), p.2 - a.2))
  exact contDiff_safeHeatPair.continuous.comp
    ((continuous_const.mul (continuous_fst.sub continuous_const)).prodMk
      (continuous_const.sub continuous_snd))

/-! ### 2. Parametric smoothness of scalar and `MeridC` integrals on `farNhd p₀` -/

private theorem contDiffOn_scalarFarIntegral {σ H1 : ℝ} (hσ : 0 < σ) (ν : ℝ)
    {p₀ : Profile} (hp₀ : 0 < p₀.1) {g : ℝ × (ℝ × ℝ) → ℝ}
    (hg_cont : ContinuousOn g (Icc σ H1 ×ˢ univ))
    {M : ℝ} (hM0 : 0 ≤ M) (hg_bdd : ∀ a : ℝ × (ℝ × ℝ), a.1 ∈ Icc σ H1 → |g a| ≤ M) :
    ContDiffOn ℝ ∞
      (fun p : Profile => ∫ a, g a • safeHeatProfile ν a.1 a.2 p
        ∂((volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))))
      (farNhd p₀) := by
  set μ_prod : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))
  set F : (ℝ × (ℝ × ℝ)) → Profile → ℝ := fun a p => g a • safeHeatProfile ν a.1 a.2 p
  have hsmooth : ∀ᵐ a ∂μ_prod, ContDiff ℝ ∞ (F a) :=
    Eventually.of_forall fun a =>
      (contDiff_const (c := g a)).smul (contDiff_safeHeatProfile ν a.1 a.2)
  have hmeas : ∀ (n : ℕ) (p : Profile),
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) p) μ_prod := by
    intro n p
    have hrew : (fun a => iteratedFDeriv ℝ n (F a) p) =
        fun a => g a • iteratedFDeriv ℝ n (safeHeatProfile ν a.1 a.2) p :=
      funext fun a =>
        UnforcedLeray.Kernels.iteratedFDeriv_const_smul_left n _ (g a) p
    rw [hrew]
    change AEStronglyMeasurable _ ((volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ)))
    rw [prod_restrict_band]
    exact (hg_cont.smul (continuous_iteratedFDeriv_safeHeatProfile ν n p).continuousOn)
      |>.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  have hdom : UnforcedLeray.Kernels.LocDominated μ_prod F (farNhd p₀) := by
    intro n x hx
    set T : ℝ := |ν| * (|H1| + p₀.1 + 1)
    obtain ⟨K, hK0, hK⟩ := norm_iteratedFDeriv_safeHeatProfile_le ν n T
    set C_maj : ℝ := M * K * (64 * (1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2) ^ 4)
    refine ⟨farNhd p₀, (isOpen_farNhd p₀).mem_nhds hx,
      fun a => C_maj * ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹),
      integrable_prodWeight σ H1 C_maj, ?_⟩
    have hae : ∀ᵐ a ∂μ_prod, a ∈ Icc σ H1 ×ˢ (univ : Set (ℝ × ℝ)) := by
      change ∀ᵐ a ∂((volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))), _
      rw [prod_restrict_band]
      exact ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)
    filter_upwards [hae] with a ha p hp
    have ha1 : a.1 ∈ Icc σ H1 := ha.1
    have hp_pos : 0 < p.1 := lt_trans (half_pos hp₀) hp.1
    have hp_ub : p.1 < p₀.1 + 1 := hp.2.1
    have ha_pos : 0 < a.1 := lt_of_lt_of_le hσ ha1.1
    have ha_ub : a.1 ≤ |H1| := ha1.2.trans (le_abs_self H1)
    have hdiff_abs : |a.1 - p.1| ≤ |H1| + p₀.1 + 1 :=
      abs_le.2 ⟨by linarith [abs_nonneg H1], by linarith⟩
    have hT_le : |ν * (a.1 - p.1)| ≤ T := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hdiff_abs (abs_nonneg ν)
    have h1 := hg_bdd a ha1
    have h2 := (hK a.1 a.2 p hT_le).trans
      (mul_le_mul_of_nonneg_left (planar_decay_majorant hp a.2) hK0)
    show ‖iteratedFDeriv ℝ n (fun q => g a • safeHeatProfile ν a.1 a.2 q) p‖ ≤ _
    rw [UnforcedLeray.Kernels.iteratedFDeriv_const_smul_left, norm_smul, Real.norm_eq_abs]
    calc |g a| * ‖iteratedFDeriv ℝ n (safeHeatProfile ν a.1 a.2) p‖
        ≤ M * (K * ((64 * (1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2) ^ 4) *
            ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹))) :=
          mul_le_mul h1 h2 (norm_nonneg _) hM0
      _ = C_maj * ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹) := by unfold C_maj; ring
  exact UnforcedLeray.Kernels.contDiffOn_integral (isOpen_farNhd p₀) hsmooth hmeas hdom

private theorem integrable_meridFarIntegrand {σ H1 : ℝ} (hσ : 0 < σ) (ν : ℝ)
    {p₀ : Profile} (hp₀ : 0 < p₀.1) {W : ℝ × (ℝ × ℝ) → MeridC}
    (hW_cont : ContinuousOn W (Icc σ H1 ×ˢ univ))
    {M : ℝ} (hW_bdd : ∀ a : ℝ × (ℝ × ℝ), a.1 ∈ Icc σ H1 → ‖W a‖ ≤ M)
    {p : Profile} (hp : p ∈ farNhd p₀) :
    Integrable (fun a : ℝ × (ℝ × ℝ) => safeHeatProfile ν a.1 a.2 p • W a)
      ((volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))) := by
  set T : ℝ := |ν| * (|H1| + p₀.1 + 1)
  obtain ⟨K, hK0, hK⟩ := norm_iteratedFDeriv_safeHeatProfile_le ν 0 T
  set C_maj : ℝ := M * K * (64 * (1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2) ^ 4)
  refine (integrable_prodWeight σ H1 C_maj).mono' ?_ ?_
  · rw [prod_restrict_band]
    exact ((continuous_safeHeatProfile_param ν p).continuousOn.smul hW_cont).aestronglyMeasurable
      (measurableSet_Icc.prod MeasurableSet.univ)
  · have hae : ∀ᵐ a ∂((volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))),
        a ∈ Icc σ H1 ×ˢ (univ : Set (ℝ × ℝ)) := by
      rw [prod_restrict_band]
      exact ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)
    filter_upwards [hae] with a ha
    have ha1 : a.1 ∈ Icc σ H1 := ha.1
    have hp_pos : 0 < p.1 := lt_trans (half_pos hp₀) hp.1
    have hp_ub : p.1 < p₀.1 + 1 := hp.2.1
    have ha_pos : 0 < a.1 := lt_of_lt_of_le hσ ha1.1
    have ha_ub : a.1 ≤ |H1| := ha1.2.trans (le_abs_self H1)
    have hdiff_abs : |a.1 - p.1| ≤ |H1| + p₀.1 + 1 :=
      abs_le.2 ⟨by linarith [abs_nonneg H1], by linarith⟩
    have hT_le : |ν * (a.1 - p.1)| ≤ T := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hdiff_abs (abs_nonneg ν)
    have hK_pt : ‖safeHeatProfile ν a.1 a.2 p‖ ≤
        K * ((64 * (1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2) ^ 4) *
          ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹)) := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
      exact (hK a.1 a.2 p hT_le).trans
        (mul_le_mul_of_nonneg_left (planar_decay_majorant hp a.2) hK0)
    rw [norm_smul]
    calc ‖safeHeatProfile ν a.1 a.2 p‖ * ‖W a‖
        ≤ (K * ((64 * (1 + p₀.2.1 ^ 2 + p₀.2.2 ^ 2) ^ 4) *
            ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹))) * M :=
          mul_le_mul hK_pt (hW_bdd a ha1) (norm_nonneg _)
            (mul_nonneg hK0 (by positivity))
      _ = C_maj * ((1 + a.2.1 ^ 2)⁻¹ * (1 + a.2.2 ^ 2)⁻¹) := by unfold C_maj; ring

private theorem contDiffOn_meridFarIntegral {σ H1 : ℝ} (hσ : 0 < σ) (ν : ℝ)
    {p₀ : Profile} (hp₀ : 0 < p₀.1) {W : ℝ × (ℝ × ℝ) → MeridC}
    (hW_cont : ContinuousOn W (Icc σ H1 ×ˢ univ))
    {M : ℝ} (hM0 : 0 ≤ M) (hW_bdd : ∀ a : ℝ × (ℝ × ℝ), a.1 ∈ Icc σ H1 → ‖W a‖ ≤ M) :
    ContDiffOn ℝ ∞
      (fun p : Profile => ∫ τ in Icc σ H1, ∫ z : ℝ × ℝ, safeHeatProfile ν τ z p • W (τ, z))
      (farNhd p₀) := by
  set μ_prod : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict (Icc σ H1)).prod (volume : Measure (ℝ × ℝ))
  set I_prod : Profile → MeridC := fun p => ∫ a, safeHeatProfile ν a.1 a.2 p • W a ∂μ_prod
  have hI_smooth : ContDiffOn ℝ ∞ I_prod (farNhd p₀) := by
    refine contDiffOn_piLp' 2 fun j => ?_
    let projCLM : MeridC →L[ℝ] ℂ :=
      (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : Fin 2 => ℂ) j).restrictScalars ℝ
    let reL : MeridC →L[ℝ] ℝ := Complex.reCLM.comp projCLM
    let imL : MeridC →L[ℝ] ℝ := Complex.imCLM.comp projCLM
    have hre_cont : ContinuousOn (fun a => reL (W a)) (Icc σ H1 ×ˢ univ) :=
      reL.continuous.comp_continuousOn hW_cont
    have him_cont : ContinuousOn (fun a => imL (W a)) (Icc σ H1 ×ˢ univ) :=
      imL.continuous.comp_continuousOn hW_cont
    have hre_bdd : ∀ a : ℝ × (ℝ × ℝ), a.1 ∈ Icc σ H1 → |reL (W a)| ≤ M := fun a ha =>
      (Complex.abs_re_le_norm (W a j)).trans ((PiLp.norm_apply_le (W a) j).trans (hW_bdd a ha))
    have him_bdd : ∀ a : ℝ × (ℝ × ℝ), a.1 ∈ Icc σ H1 → |imL (W a)| ≤ M := fun a ha =>
      (Complex.abs_im_le_norm (W a j)).trans ((PiLp.norm_apply_le (W a) j).trans (hW_bdd a ha))
    have hre_sm := contDiffOn_scalarFarIntegral hσ ν hp₀ hre_cont hM0 hre_bdd
    have him_sm := contDiffOn_scalarFarIntegral hσ ν hp₀ him_cont hM0 him_bdd
    have hcomp_sm : ContDiffOn ℝ ∞
        (fun p : Profile =>
          Complex.ofRealCLM (∫ a, reL (W a) • safeHeatProfile ν a.1 a.2 p ∂μ_prod) +
          (Complex.I : ℂ) •
            Complex.ofRealCLM (∫ a, imL (W a) • safeHeatProfile ν a.1 a.2 p ∂μ_prod))
        (farNhd p₀) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hre_sm).add
        ((contDiffOn_const (c := Complex.I)).smul
          (Complex.ofRealCLM.contDiff.comp_contDiffOn him_sm))
    refine hcomp_sm.congr fun p hp => ?_
    have hint := integrable_meridFarIntegrand hσ ν hp₀ hW_cont hW_bdd hp
    have hre_eq : (I_prod p j).re = ∫ a, reL (W a) • safeHeatProfile ν a.1 a.2 p ∂μ_prod := by
      have hcomm := (reL.integral_comp_comm hint).symm
      change reL (I_prod p) = _
      rw [hcomm]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      simp [reL, projCLM, smul_eq_mul, mul_comm]
    have him_eq : (I_prod p j).im = ∫ a, imL (W a) • safeHeatProfile ν a.1 a.2 p ∂μ_prod := by
      have hcomm := (imL.integral_comp_comm hint).symm
      change imL (I_prod p) = _
      rw [hcomm]
      refine integral_congr_ae (Eventually.of_forall fun a => ?_)
      simp [imL, projCLM, smul_eq_mul, mul_comm]
    rw [Complex.ofRealCLM_apply, Complex.ofRealCLM_apply, ← hre_eq, ← him_eq, smul_eq_mul,
      mul_comm Complex.I _]
    exact (Complex.re_add_im _).symm
  refine hI_smooth.congr fun p hp => ?_
  have hint := integrable_meridFarIntegrand hσ ν hp₀ hW_cont hW_bdd hp
  exact (MeasureTheory.integral_prod _ hint).symm

/-! ### 3. Change of variables identifying `flatAdjointRep` on `farNhd p₀` -/

private theorem integral_planeι_sub_eq (x : ℝ × ℝ) (F : ℝ × ℝ → MeridC) :
    (∫ y : Euc 2, F (x - planeι y)) = ∫ z : ℝ × ℝ, F z := by
  let e : Euc 2 ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : (e : Euc 2 → ℝ × ℝ) = planeι := rfl
  have hmp : MeasurePreserving e volume volume :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have h1 := hmp.integral_comp' (fun z : ℝ × ℝ => F (x - z))
  rw [he] at h1
  rw [h1, MeasureTheory.integral_sub_left_eq_self F volume x]

private theorem planar_far_eq {ν : ℝ} (hν : 0 < ν) {p₀ p : Profile} (hp : p ∈ farNhd p₀)
    {w : Profile → MeridC}
    (hw_supp_y : ∀ q : Profile, (q.2.1 - p₀.2.1) ^ 2 + (q.2.2 - p₀.2.2) ^ 2 ≤ 1 → w q = 0)
    (τ : ℝ) :
    (∫ z : ℝ × ℝ, safeHeatProfile ν τ z p • w (τ, z)) =
      if p.1 < τ then planeHeat (ν * (τ - p.1)) (fun z => w (τ, z)) p.2 else 0 := by
  split_ifs with hτ
  · have hθ : 0 < ν * (τ - p.1) := mul_pos hν (sub_pos.2 hτ)
    rw [planeHeat_of_pos hθ,
      ← integral_planeι_sub_eq p.2 (fun z => safeHeatProfile ν τ z p • w (τ, z))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    by_cases hy_near :
        ((p.2 - planeι y).1 - p₀.2.1) ^ 2 + ((p.2 - planeι y).2 - p₀.2.2) ^ 2 ≤ 1
    · rw [hw_supp_y (τ, p.2 - planeι y) hy_near, smul_zero, smul_zero]
    · have hp_ball : (p.2.1 - p₀.2.1) ^ 2 + (p.2.2 - p₀.2.2) ^ 2 < 1 / 8 := hp.2.2
      have hq_ge : 1 / 4 ≤ (planeι y).1 ^ 2 + (planeι y).2 ^ 2 := by
        set u1 : ℝ := p.2.1 - p₀.2.1
        set u2 : ℝ := p.2.2 - p₀.2.2
        set q1 : ℝ := (planeι y).1
        set q2 : ℝ := (planeι y).2
        have hd1 : (p.2 - planeι y).1 - p₀.2.1 = u1 - q1 := by unfold u1 q1; simp; ring
        have hd2 : (p.2 - planeι y).2 - p₀.2.2 = u2 - q2 := by unfold u2 q2; simp; ring
        rw [hd1, hd2] at hy_near
        nlinarith [sq_nonneg (u1 + q1), sq_nonneg (u2 + q2)]
      have hker : safeHeatProfile ν τ (p.2 - planeι y) p = gaussKernel 2 (ν * (τ - p.1)) y := by
        unfold safeHeatProfile
        rw [sub_sub_cancel, safeHeat2D_eq_gaussKernel hθ hq_ge]
      rw [hker]
  · have hθ : ν * (τ - p.1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hν.le (by linarith)
    have hzero : (fun z : ℝ × ℝ => safeHeatProfile ν τ z p • w (τ, z)) = fun _ => 0 := by
      funext z
      simp [safeHeatProfile, safeHeat2D_of_nonpos hθ]
    simp [hzero]

private theorem band_to_Ioi_eq {σ H1 s : ℝ} {G : ℝ → MeridC}
    (hG_supp : ∀ τ : ℝ, τ < σ ∨ H1 < τ → G τ = 0) :
    (∫ τ in Icc σ H1, (if s < τ then G τ else 0)) = ∫ τ in Ioi s, G τ := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioi]
  congr 1
  funext τ
  by_cases hIcc : τ ∈ Icc σ H1
  · by_cases hs : s < τ
    · simp [Set.indicator, hIcc, Set.mem_Ioi, hs]
    · simp [Set.indicator, hIcc, Set.mem_Ioi, hs]
  · by_cases hs : s < τ
    · have hout : τ < σ ∨ H1 < τ := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hIcc
        exact hIcc
      simp [Set.indicator, hIcc, Set.mem_Ioi, hs, hG_supp τ hout]
    · simp [Set.indicator, hIcc, Set.mem_Ioi, hs]

private theorem exp_mul_image_Ioi {s : ℝ} (hs : 0 < s) :
    (fun t : ℝ => Real.exp t * s) '' Ioi (0 : ℝ) = Ioi s := by
  ext τ
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    calc s = 1 * s := (one_mul s).symm
      _ < Real.exp t * s := mul_lt_mul_of_pos_right (Real.one_lt_exp_iff.2 ht) hs
  · intro hτ
    refine ⟨Real.log (τ / s), Real.log_pos ((one_lt_div hs).2 hτ), ?_⟩
    rw [Real.exp_log (div_pos (hs.trans hτ) hs), div_mul_cancel₀ τ hs.ne']

private theorem flatAdjointRep_eq_farIntegral {σ H1 ν : ℝ} (hν : 0 < ν) (μ : ℂ)
    {p₀ p : Profile} (hp₀ : 0 < p₀.1) (hp : p ∈ farNhd p₀)
    {w : Profile → MeridC}
    (hw_supp_s : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0)
    (hw_supp_y : ∀ q : Profile, (q.2.1 - p₀.2.1) ^ 2 + (q.2.2 - p₀.2.2) ^ 2 ≤ 1 → w q = 0) :
    flatAdjointRep ν μ w p =
      Complex.exp ((starRingEnd ℂ μ + (1 / 2 : ℂ)) * (Real.log p.1 : ℂ)) •
        ∫ τ in Icc σ H1, ∫ z : ℝ × ℝ, safeHeatProfile ν τ z p •
          ((τ⁻¹ : ℝ) •
            Complex.exp (-((starRingEnd ℂ μ + (1 / 2 : ℂ)) * (Real.log τ : ℂ))) •
            w (τ, z)) := by
  have hp_pos : 0 < p.1 := lt_trans (half_pos hp₀) hp.1
  set cμ : ℂ := starRingEnd ℂ μ + (1 / 2 : ℂ)
  set G : ℝ → MeridC := fun τ =>
    (τ⁻¹ : ℝ) • Complex.exp (-(cμ * (Real.log τ : ℂ))) •
      planeHeat (ν * (τ - p.1)) (fun z => w (τ, z)) p.2
  have hinner : ∀ τ : ℝ,
      (∫ z : ℝ × ℝ, safeHeatProfile ν τ z p •
        ((τ⁻¹ : ℝ) • Complex.exp (-(cμ * (Real.log τ : ℂ))) • w (τ, z))) =
        if p.1 < τ then G τ else 0 := by
    intro τ
    have hpull : (fun z : ℝ × ℝ => safeHeatProfile ν τ z p •
        ((τ⁻¹ : ℝ) • Complex.exp (-(cμ * (Real.log τ : ℂ))) • w (τ, z))) =
        fun z => (τ⁻¹ : ℝ) • Complex.exp (-(cμ * (Real.log τ : ℂ))) •
          (safeHeatProfile ν τ z p • w (τ, z)) := by
      funext z
      rw [smul_comm (safeHeatProfile ν τ z p) (τ⁻¹ : ℝ),
        smul_comm (safeHeatProfile ν τ z p) (Complex.exp _)]
    rw [hpull, integral_smul, integral_smul, planar_far_eq hν hp hw_supp_y τ]
    split_ifs <;> simp [G]
  have hG_supp : ∀ τ : ℝ, τ < σ ∨ H1 < τ → G τ = 0 := by
    intro τ hτ
    have hzero : (fun z : ℝ × ℝ => w (τ, z)) = fun _ => 0 :=
      funext fun z => hw_supp_s (τ, z) hτ
    simp only [G, hzero, planeHeat_zero, smul_zero]
  simp_rw [hinner]
  rw [band_to_Ioi_eq hG_supp]
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (f := fun t : ℝ => Real.exp t * p.1)
    (f' := fun t : ℝ => Real.exp t * p.1)
    (fun t _ => ((Real.hasDerivAt_exp t).mul_const p.1).hasDerivWithinAt)
    (Real.exp_strictMono.mul_const hp_pos).injective.injOn G
  rw [exp_mul_image_Ioi hp_pos] at hcov
  rw [hcov, ← integral_smul]
  simp only [flatAdjointRep, hp_pos, ↓reduceIte]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht_pos : 0 < t := ht
  have hexp_pos : 0 < Real.exp t * p.1 := mul_pos (Real.exp_pos t) hp_pos
  have hlog : Real.log (Real.exp t * p.1) = t + Real.log p.1 := by
    rw [Real.log_mul (Real.exp_pos t).ne' hp_pos.ne', Real.log_exp]
  have hθ_eq : ν * (Real.exp t * p.1 - p.1) = ν * p.1 * (Real.exp t - 1) := by ring
  dsimp only [G]
  rw [abs_of_pos hexp_pos, smul_smul (Real.exp t * p.1) (Real.exp t * p.1)⁻¹,
    mul_inv_cancel₀ hexp_pos.ne', one_smul, hlog, hθ_eq, smul_smul, ← Complex.exp_add]
  have hexp_arg : cμ * (Real.log p.1 : ℂ) + -(cμ * ((t + Real.log p.1 : ℝ) : ℂ)) =
      -(cμ * (t : ℂ)) := by
    push_cast
    ring
  rw [hexp_arg]
  rfl

/-! ### 4. Main far-field smoothness theorem -/

/-- For a continuous bounded profile `w` supported in `s ∈ [σ, H1]` and vanishing on the disk
`(q.2.1 - p₀.2.1) ^ 2 + (q.2.2 - p₀.2.2) ^ 2 ≤ 1`, `flatAdjointRep ν μ w` is smooth on
`farNhd p₀`. -/
theorem contDiffOn_flatAdjointRep_of_far {σ H1 ν : ℝ}
    (hν : 0 < ν) (hσ : 0 < σ) (μ : ℂ) {p₀ : Profile} (hp₀ : 0 < p₀.1)
    {w : Profile → MeridC} (hw_cont : Continuous w)
    (hw_supp_s : ∀ q : Profile, q.1 < σ ∨ H1 < q.1 → w q = 0)
    (hw_supp_y : ∀ q : Profile, (q.2.1 - p₀.2.1) ^ 2 + (q.2.2 - p₀.2.2) ^ 2 ≤ 1 → w q = 0)
    (hw_bdd : ∃ B : ℝ, ∀ q : Profile, ‖w q‖ ≤ B) :
    ContDiffOn ℝ ∞ (flatAdjointRep ν μ w) (farNhd p₀) := by
  obtain ⟨B, hB⟩ := hw_bdd
  set cμ : ℂ := starRingEnd ℂ μ + (1 / 2 : ℂ)
  set W : ℝ × (ℝ × ℝ) → MeridC := fun a =>
    (a.1⁻¹ : ℝ) • Complex.exp (-(cμ * (Real.log a.1 : ℂ))) • w (a.1, a.2)
  have hexp_cont : ContinuousOn
      (fun τ : ℝ => Complex.exp (-(cμ * (Real.log τ : ℂ)))) (Icc σ H1) := by
    refine (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal).neg).comp_continuousOn ?_
    exact continuousOn_id.log fun τ hτ => (lt_of_lt_of_le hσ hτ.1).ne'
  have hW_cont : ContinuousOn W (Icc σ H1 ×ˢ univ) := by
    refine (continuousOn_fst.inv₀ fun a ha => (lt_of_lt_of_le hσ ha.1.1).ne').smul ?_
    exact (hexp_cont.comp continuousOn_fst fun a ha => ha.1).smul hw_cont.continuousOn
  obtain ⟨C_exp, hC_exp⟩ := isCompact_Icc.exists_bound_of_continuousOn hexp_cont
  set M : ℝ := σ⁻¹ * max C_exp 0 * max B 0
  have hM0 : 0 ≤ M := by positivity
  have hW_bdd : ∀ a : ℝ × (ℝ × ℝ), a.1 ∈ Icc σ H1 → ‖W a‖ ≤ M := by
    intro a ha
    have ha_pos : 0 < a.1 := lt_of_lt_of_le hσ ha.1
    have hinv : a.1⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ ha.1
    have he_le : ‖Complex.exp (-(cμ * (Real.log a.1 : ℂ)))‖ ≤ max C_exp 0 :=
      (hC_exp a.1 ha).trans (le_max_left C_exp 0)
    have hw_le : ‖w (a.1, a.2)‖ ≤ max B 0 := (hB (a.1, a.2)).trans (le_max_left B 0)
    simp only [W, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha_pos.le)]
    calc a.1⁻¹ * (‖Complex.exp (-(cμ * (Real.log a.1 : ℂ)))‖ * ‖w (a.1, a.2)‖)
        ≤ σ⁻¹ * (max C_exp 0 * max B 0) :=
          mul_le_mul hinv (mul_le_mul he_le hw_le (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = M := by unfold M; ring
  have hInt_smooth := contDiffOn_meridFarIntegral hσ ν hp₀ hW_cont hM0 hW_bdd
  have hpre_smooth : ContDiffOn ℝ ∞
      (fun p : Profile => Complex.exp (cμ * (Real.log p.1 : ℂ))) (farNhd p₀) := by
    have hlog : ContDiffOn ℝ ∞ (fun p : Profile => Real.log p.1) (farNhd p₀) :=
      contDiff_fst.contDiffOn.log fun p hp => (lt_trans (half_pos hp₀) hp.1).ne'
    have hlin : ContDiff ℝ ∞ (fun r : ℝ => cμ * (r : ℂ)) :=
      (contDiff_const (c := cμ)).mul Complex.ofRealCLM.contDiff
    exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp hlin).comp_contDiffOn hlog
  refine (hpre_smooth.smul hInt_smooth).congr fun p hp => ?_
  exact flatAdjointRep_eq_farIntegral hν μ hp₀ hp hw_supp_s hw_supp_y

end UnforcedLeray.Short.PartIIa.FlatAdjointSmoothAux
