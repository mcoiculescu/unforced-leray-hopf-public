import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2

/-!
# Shared Gaussian integration-by-parts helpers for `PlaneGaussIbpQ` / `PlaneGaussIbpEta`
(task `PartIII-b:C/flatset/col/7/3/2/1/2/5`, source 1650-1656).

For a smooth meridional test `ζ` and a unit direction `v` of `Euc 2`, with
`w = (0, planeι v)` the Gaussian `G_θ` satisfies `∂_v²G_θ = ((⟪y,v⟫²/(4θ²)) - 1/(2θ)) G_θ`,
and two integrations by parts along `v` move the second derivative onto the test.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdQ pdEta)
open UnforcedLeray.B0220 (Profile QPeriodic)
open UnforcedLeray.B0224 (planeι)
open UnforcedLeray.Gaussian (Euc gaussKernel gaussKernel_eq_exp)

/-- Directional derivative field `q ↦ ∂_w f(q)`. -/
def ibpPdW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Profile → E) (w : Profile) : Profile → E :=
  fun q => fderiv ℝ f q w

/-- `D_v G_θ(y) = ∂_v G_θ(y) = -(⟪y,v⟫/(2θ)) G_θ(y)`. -/
def ibpDfun (θ : ℝ) (v y : Euc 2) : ℝ :=
  -(inner ℝ y v / (2 * θ)) * gaussKernel 2 θ y

/-- `∂_v² G_θ(y) = (⟪y,v⟫²/(4θ²) - 1/(2θ)) G_θ(y)`. -/
def ibpA0 (θ : ℝ) (v y : Euc 2) : ℝ :=
  ((inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * gaussKernel 2 θ y

theorem ibp_inner_single (y : Euc 2) (i : Fin 2) :
    inner ℝ y (EuclideanSpace.single i (1 : ℝ)) = y i := by
  simp [EuclideanSpace.inner_single_right]

theorem ibp_norm_single (i : Fin 2) : ‖(EuclideanSpace.single i (1 : ℝ) : Euc 2)‖ = 1 := by
  simp

theorem ibp_pd_periodic {c : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : QPeriodic c f) (w : Profile) :
    QPeriodic c (ibpPdW f w) :=
  pd_periodic_aux hf w

/-- A derivative of a function vanishing outside a band is zero outside the band. -/
theorem ibp_band_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} {s0 s1 L : ℝ}
    (hf : ∀ p : Profile, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (w : Profile) (p : Profile) (hp : fderiv ℝ f p w ≠ 0) :
    p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  by_contra hB
  have hclosed : IsClosed {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_snd.snd.abs) continuous_const)
  have hpU : p ∈ {q : Profile | q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L}ᶜ := hB
  have hev : f =ᶠ[𝓝 p] (fun _ : Profile => (0 : E)) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hpU] with q hq
    by_contra hne
    exact hq (hf q hne)
  have hfd : fderiv ℝ f p = 0 := by
    rw [hev.fderiv_eq]
    simp
  rw [hfd] at hp
  simp at hp

/-- A continuous `c`-periodic-in-`q` profile supported in a band is bounded. -/
theorem ibp_bdd_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {f : Profile → E} (hcont : Continuous f) (hper : QPeriodic c f)
    {s0 s1 L : ℝ} (hf : ∀ p : Profile, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∃ M : ℝ, ∀ p : Profile, ‖f p‖ ≤ M := by
  have hK : IsCompact (Icc s0 s1 ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun p => ?_⟩
  by_cases hp : f p = 0
  · rw [hp, norm_zero]
    exact le_max_right _ _
  · obtain ⟨hs, hL⟩ := hf p hp
    have hper1 : Function.Periodic (fun t : ℝ => f (p.1, t, p.2.2)) c :=
      fun t => hper (p.1, t, p.2.2)
    obtain ⟨y, hy, hfy⟩ := hper1.exists_mem_Ico₀ hc p.2.1
    have hmem : (p.1, y, p.2.2) ∈ Icc s0 s1 ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-L) L) :=
      ⟨hs, ⟨hy.1, hy.2.le⟩, abs_le.mp hL⟩
    have hfp : f p = f (p.1, y, p.2.2) := hfy
    rw [hfp]
    exact (hC _ hmem).trans (le_max_left _ _)

/-- The coordinate map `y ↦ (y 0, y 1)` as a continuous linear map. -/
def ibpPlaneCLM : Euc 2 →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))

theorem ibp_planeCLM_apply (y : Euc 2) : ibpPlaneCLM y = planeι y := rfl

theorem ibp_hasFDerivAt_planeι (y : Euc 2) :
    HasFDerivAt (fun z : Euc 2 => planeι z) ibpPlaneCLM y :=
  ibpPlaneCLM.hasFDerivAt

theorem ibp_differentiable_planeι : Differentiable ℝ (fun z : Euc 2 => planeι z) :=
  fun y => (ibp_hasFDerivAt_planeι y).differentiableAt

theorem ibp_differentiable_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Profile → E} (hF : Differentiable ℝ F) (σ : ℝ) (x : ℝ × ℝ) :
    Differentiable ℝ (fun z : Euc 2 => F (σ, x - planeι z)) :=
  hF.comp ((differentiable_const σ).prodMk ((differentiable_const x).sub ibp_differentiable_planeι))

/-- Chain rule for the shifted profile `y ↦ F(σ, x - ι y)`. -/
theorem ibp_shift_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Profile → E} (hF : Differentiable ℝ F) (σ : ℝ) (x : ℝ × ℝ) (y v : Euc 2) :
    fderiv ℝ (fun z : Euc 2 => F (σ, x - planeι z)) y v =
      -(fderiv ℝ F (σ, x - planeι y) (0, planeι v)) := by
  have hpl : HasFDerivAt (fun z : Euc 2 => planeι z) ibpPlaneCLM y :=
    ibp_hasFDerivAt_planeι y
  have hq : HasFDerivAt (fun z : Euc 2 => ((σ, x - planeι z) : Profile))
      (ContinuousLinearMap.prod (0 : Euc 2 →L[ℝ] ℝ) (0 - ibpPlaneCLM)) y :=
    (hasFDerivAt_const σ y).prodMk ((hasFDerivAt_const x y).sub hpl)
  have hFd : HasFDerivAt F (fderiv ℝ F (σ, x - planeι y)) (σ, x - planeι y) :=
    (hF (σ, x - planeι y)).hasFDerivAt
  have hcomp := hFd.comp y hq
  have hfun : (fun z : Euc 2 => F (σ, x - planeι z)) =
      F ∘ (fun z : Euc 2 => ((σ, x - planeι z) : Profile)) := rfl
  rw [hfun, hcomp.fderiv]
  have hneg : ((0 : ℝ), -(ibpPlaneCLM v)) = -((0 : ℝ), planeι v) := by
    rw [← ibp_planeCLM_apply]
    simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, zero_sub, ContinuousLinearMap.neg_apply]
  rw [hneg, map_neg]

/-- `∂_v G_θ(y) = -(⟪y,v⟫/(2θ)) G_θ(y)` on `Euc 2`. -/
theorem ibp_gauss_fderiv {θ : ℝ} (y v : Euc 2) :
    fderiv ℝ (gaussKernel 2 θ) y v = -(inner ℝ y v / (2 * θ)) * gaussKernel 2 θ y := by
  have hn : HasFDerivAt (fun z : Euc 2 => ‖z‖ ^ 2)
      (2 • (innerSL ℝ y).comp (ContinuousLinearMap.id ℝ (Euc 2))) y :=
    (hasFDerivAt_id y).norm_sq
  have h := ((hn.const_mul (-(4 * θ)⁻¹)).exp).const_mul
    ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2))
  have hfun : gaussKernel 2 θ = fun z : Euc 2 =>
      (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-(4 * θ)⁻¹ * ‖z‖ ^ 2) :=
    funext fun z => gaussKernel_eq_exp z
  have hd : fderiv ℝ (fun z : Euc 2 => (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
      Real.exp (-(4 * θ)⁻¹ * ‖z‖ ^ 2)) y = _ := h.fderiv
  rw [hfun, hd]
  simp [innerSL_apply_apply]
  ring


theorem ibp_inner_hasFDerivAt (v : Euc 2) (y : Euc 2) :
    HasFDerivAt (fun z : Euc 2 => inner ℝ z v) (innerSL ℝ v) y := by
  have h : (fun z : Euc 2 => inner ℝ z v) = fun z => innerSL ℝ v z := by
    funext z
    rw [innerSL_apply_apply]
    exact real_inner_comm v z
  rw [h]
  exact (innerSL ℝ v).hasFDerivAt

theorem ibp_hasFDerivAt_coef (θ : ℝ) (v y : Euc 2) :
    HasFDerivAt (fun z : Euc 2 => -(inner ℝ z v / (2 * θ))) ((-(2 * θ)⁻¹) • innerSL ℝ v) y := by
  have h : (fun z : Euc 2 => -(inner ℝ z v / (2 * θ))) =
      fun z => (-(2 * θ)⁻¹) * inner ℝ z v := by
    funext z
    ring
  rw [h]
  exact (ibp_inner_hasFDerivAt v y).const_mul (-(2 * θ)⁻¹)

theorem ibp_differentiableAt_Dfun (θ : ℝ) (v y : Euc 2) :
    DifferentiableAt ℝ (ibpDfun θ v) y := by
  have hA := ibp_hasFDerivAt_coef θ v y
  have hG : DifferentiableAt ℝ (gaussKernel 2 θ) y :=
    (UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable
      (by norm_num) y
  exact hA.differentiableAt.mul hG

/-- `∂_v D_v G_θ(y) = ((⟪y,v⟫²/(4θ²)) - 1/(2θ)) G_θ(y)` for a unit `v`. -/
theorem ibp_fderiv_Dfun {θ : ℝ} (hθ : 0 < θ) (y v : Euc 2) (hv : ‖v‖ = 1) :
    fderiv ℝ (ibpDfun θ v) y v = ibpA0 θ v y := by
  have hA := ibp_hasFDerivAt_coef θ v y
  have hG : HasFDerivAt (gaussKernel 2 θ) (fderiv ℝ (gaussKernel 2 θ) y) y :=
    ((UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable
      (by norm_num) y).hasFDerivAt
  have hprod : HasFDerivAt (fun z : Euc 2 => -(inner ℝ z v / (2 * θ)) * gaussKernel 2 θ z)
      _ y := hA.mul hG
  have hfun : ibpDfun θ v = fun z => (-(inner ℝ z v / (2 * θ))) * gaussKernel 2 θ z := rfl
  rw [hfun, hprod.fderiv]
  have hθ' : θ ≠ 0 := hθ.ne'
  have hvv : inner ℝ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    innerSL_apply_apply, ibp_gauss_fderiv, hvv]
  unfold ibpA0
  field_simp
  ring

theorem ibp_integrable_sq_gauss_key (a : ℝ) (ha : 0 < a) (t : ℝ) :
    t ^ 2 * Real.exp (-(a / 2) * t ^ 2) ≤ 2 / a := by
  have h1 : 1 + (a / 2) * t ^ 2 ≤ Real.exp ((a / 2) * t ^ 2) := by
    linarith [Real.add_one_le_exp ((a / 2) * t ^ 2)]
  have hE : 0 < Real.exp ((a / 2) * t ^ 2) := Real.exp_pos _
  have e1 : Real.exp (-(a / 2) * t ^ 2) = (Real.exp ((a / 2) * t ^ 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have h2 : t ^ 2 = (2 / a) * ((a / 2) * t ^ 2) := by field_simp
  have hpos : 0 ≤ 2 / a := div_nonneg (by norm_num) ha.le
  rw [e1, mul_inv_le_iff₀ hE]
  calc t ^ 2 = (2 / a) * ((a / 2) * t ^ 2) := h2
    _ ≤ (2 / a) * (1 + (a / 2) * t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        linarith
    _ ≤ (2 / a) * Real.exp ((a / 2) * t ^ 2) := mul_le_mul_of_nonneg_left h1 hpos

theorem ibp_integrable_sq_gauss {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun y : Euc 2 => ‖y‖ ^ 2 * gaussKernel 2 θ y) := by
  have ha : 0 < (4 * θ)⁻¹ := by positivity
  have hb : 0 < (4 * θ)⁻¹ / 2 := by positivity
  have hK : 0 ≤ (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) := by positivity
  have hbound : ∀ y : Euc 2, ‖‖y‖ ^ 2 * gaussKernel 2 θ y‖ ≤
      ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * (2 / (4 * θ)⁻¹)) *
        Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2) := by
    intro y
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)),
      gaussKernel_eq_exp y]
    have e2 : Real.exp (-(4 * θ)⁻¹ * ‖y‖ ^ 2) =
        Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2) * Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    have hk := ibp_integrable_sq_gauss_key ((4 * θ)⁻¹) ha ‖y‖
    have hE := Real.exp_pos (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2)
    calc ‖y‖ ^ 2 * ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) *
          (Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2) * Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2)))
        = ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2)) *
          (‖y‖ ^ 2 * Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2)) := by ring
      _ ≤ ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-((4 * θ)⁻¹ / 2) * ‖y‖ ^ 2)) *
          (2 / (4 * θ)⁻¹) := mul_le_mul_of_nonneg_left hk (mul_nonneg hK hE.le)
      _ = _ := by ring
  exact Integrable.mono'
    ((UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) hb).const_mul
      ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * (2 / (4 * θ)⁻¹)))
    ((continuous_norm.pow 2).mul (UnforcedLeray.Gaussian.continuous_gaussKernel θ)).aestronglyMeasurable
    (Eventually.of_forall hbound)

theorem ibp_integrable_weight {θ : ℝ} (hθ : 0 < θ) {w : Euc 2 → ℝ} (hw : Continuous w) {C : ℝ}
    (hC : ∀ y : Euc 2, |w y| ≤ C * (1 + ‖y‖ ^ 2)) :
    Integrable (fun y : Euc 2 => w y * gaussKernel 2 θ y) := by
  have hG : Integrable (fun y : Euc 2 => gaussKernel 2 θ y + ‖y‖ ^ 2 * gaussKernel 2 θ y) :=
    (UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ).add (ibp_integrable_sq_gauss hθ)
  refine Integrable.mono' (hG.const_mul C)
    (hw.mul (UnforcedLeray.Gaussian.continuous_gaussKernel θ)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hGy : 0 ≤ gaussKernel 2 θ y := UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hGy]
  calc |w y| * gaussKernel 2 θ y ≤ C * (1 + ‖y‖ ^ 2) * gaussKernel 2 θ y :=
        mul_le_mul_of_nonneg_right (hC y) hGy
    _ = C * (gaussKernel 2 θ y + ‖y‖ ^ 2 * gaussKernel 2 θ y) := by ring

theorem ibp_integrable_smul_bdd {F : Euc 2 → ℝ} (hF : Integrable F) {g : Euc 2 → MeridC}
    (hg : Continuous g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun y => F y • g y) := by
  refine Integrable.mono' (hF.norm.const_mul M)
    (hF.aestronglyMeasurable.smul hg.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)

/-- Core: two integrations by parts along `v` for `∂_v²G_θ = a₀G_θ`. -/
theorem ibp_core {c θ σ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {ζ : Profile → MeridC}
    (hζ : IsMeridTest c ζ) (x : ℝ × ℝ) (v : Euc 2) (hv : ‖v‖ = 1) (w : Profile)
    (hw : w = (0, planeι v)) :
    Integrable (fun y : Euc 2 => ibpA0 θ v y • ζ (σ, x - planeι y)) ∧
    Integrable (fun y : Euc 2 => gaussKernel 2 θ y • ibpPdW (ibpPdW ζ w) w (σ, x - planeι y)) ∧
    ∫ y : Euc 2, ibpA0 θ v y • ζ (σ, x - planeι y) =
      ∫ y : Euc 2, gaussKernel 2 θ y • ibpPdW (ibpPdW ζ w) w (σ, x - planeι y) := by
  have hζs : ContDiff ℝ ∞ ζ := hζ.smooth
  have hζd : Differentiable ℝ ζ := hζs.differentiable (by simp)
  have hζc : Continuous ζ := hζs.continuous
  obtain ⟨s0, s1, L, _, hb⟩ := hζ.band
  have hW1s : ContDiff ℝ ∞ (ibpPdW ζ w) :=
    (hζs.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hW1d : Differentiable ℝ (ibpPdW ζ w) := hW1s.differentiable (by simp)
  have hW1c : Continuous (ibpPdW ζ w) := hW1s.continuous
  have hW1p : QPeriodic c (ibpPdW ζ w) := ibp_pd_periodic hζ.periodic w
  have hW1b : ∀ p : Profile, ibpPdW ζ w p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
    fun p hp => ibp_band_fderiv hb w p hp
  have hW2s : ContDiff ℝ ∞ (ibpPdW (ibpPdW ζ w) w) :=
    (hW1s.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hW2c : Continuous (ibpPdW (ibpPdW ζ w) w) := hW2s.continuous
  have hW2p : QPeriodic c (ibpPdW (ibpPdW ζ w) w) := ibp_pd_periodic hW1p w
  have hW2b : ∀ p : Profile, ibpPdW (ibpPdW ζ w) w p ≠ 0 →
      p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L :=
    fun p hp => ibp_band_fderiv hW1b w p hp
  obtain ⟨M0, hM0⟩ := ibp_bdd_band hc hζc hζ.periodic hb
  obtain ⟨M1, hM1⟩ := ibp_bdd_band hc hW1c hW1p hW1b
  obtain ⟨M2, hM2⟩ := ibp_bdd_band hc hW2c hW2p hW2b
  have hpc : Continuous (fun y : Euc 2 => ((σ, x - planeι y) : Profile)) :=
    continuous_const.prodMk (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)
  have hgc : Continuous (fun y : Euc 2 => ζ (σ, x - planeι y)) := hζc.comp hpc
  have hW1gc : Continuous (fun y : Euc 2 => ibpPdW ζ w (σ, x - planeι y)) := hW1c.comp hpc
  have hW2gc : Continuous (fun y : Euc 2 => ibpPdW (ibpPdW ζ w) w (σ, x - planeι y)) :=
    hW2c.comp hpc
  have hW1gd : Differentiable ℝ (fun y : Euc 2 => ibpPdW ζ w (σ, x - planeι y)) :=
    ibp_differentiable_shift hW1d σ x
  have hgd : Differentiable ℝ (fun y : Euc 2 => ζ (σ, x - planeι y)) :=
    ibp_differentiable_shift hζd σ x
  have hGint : Integrable (gaussKernel 2 θ) :=
    UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  have hGd : Differentiable ℝ (gaussKernel 2 θ) :=
    (UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable (by norm_num)
  -- weights
  have hcontD : Continuous (fun y : Euc 2 => -(inner ℝ y v / (2 * θ))) := by
    fun_prop
  have hDint : Integrable (ibpDfun θ v) := by
    refine ibp_integrable_weight hθ (w := fun y : Euc 2 => -(inner ℝ y v / (2 * θ)))
      (C := 1 / (2 * θ)) hcontD ?_
    intro y
    show |-(inner ℝ y v / (2 * θ))| ≤ 1 / (2 * θ) * (1 + ‖y‖ ^ 2)
    have hi : |inner ℝ y v| ≤ 1 + ‖y‖ ^ 2 := by
      have h1 := abs_real_inner_le_norm y v
      rw [hv, mul_one] at h1
      nlinarith [sq_nonneg (‖y‖ - 1), norm_nonneg y]
    have h2θ : 0 < 2 * θ := by linarith
    rw [abs_neg, abs_div, abs_of_pos h2θ]
    calc |inner ℝ y v| / (2 * θ) ≤ (1 + ‖y‖ ^ 2) / (2 * θ) := by gcongr
      _ = 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by ring
  have hcontA : Continuous (fun y : Euc 2 => (inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) := by
    fun_prop
  have hA0int : Integrable (ibpA0 θ v) := by
    refine ibp_integrable_weight hθ
      (w := fun y : Euc 2 => (inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ))
      (C := 1 / (4 * θ ^ 2) + 1 / (2 * θ)) hcontA ?_
    intro y
    show |(inner ℝ y v) ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)| ≤
      (1 / (4 * θ ^ 2) + 1 / (2 * θ)) * (1 + ‖y‖ ^ 2)
    have h1 := abs_real_inner_le_norm y v
    rw [hv, mul_one] at h1
    have hi2 : (inner ℝ y v) ^ 2 ≤ 1 + ‖y‖ ^ 2 := by
      nlinarith [abs_nonneg (inner ℝ y v), sq_abs (inner ℝ y v), norm_nonneg y,
        mul_nonneg (sub_nonneg.2 h1) (add_nonneg (norm_nonneg y) (abs_nonneg (inner ℝ y v)))]
    have hq0 : 0 ≤ (inner ℝ y v) ^ 2 / (4 * θ ^ 2) := by positivity
    have hq1 : (inner ℝ y v) ^ 2 / (4 * θ ^ 2) ≤ (1 + ‖y‖ ^ 2) / (4 * θ ^ 2) := by
      gcongr
    have hq2 : (1 + ‖y‖ ^ 2) / (4 * θ ^ 2) = 1 / (4 * θ ^ 2) * (1 + ‖y‖ ^ 2) := by ring
    have hb1 : 1 / (2 * θ) ≤ 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * θ)) (sq_nonneg ‖y‖)
      nlinarith
    have hp1 : 0 ≤ 1 / (4 * θ ^ 2) * (1 + ‖y‖ ^ 2) := by positivity
    have hp2 : 0 ≤ 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by positivity
    have hpos2 : 0 < 1 / (2 * θ) := by positivity
    have hexp : (1 / (4 * θ ^ 2) + 1 / (2 * θ)) * (1 + ‖y‖ ^ 2) =
        1 / (4 * θ ^ 2) * (1 + ‖y‖ ^ 2) + 1 / (2 * θ) * (1 + ‖y‖ ^ 2) := by ring
    rw [abs_le, hexp]
    constructor <;> linarith
  -- Gaussian-weighted bounds
  have hMb0 : ∀ y : Euc 2, ‖ζ (σ, x - planeι y)‖ ≤ M0 := fun y => hM0 _
  have hMb1 : ∀ y : Euc 2, ‖ibpPdW ζ w (σ, x - planeι y)‖ ≤ M1 := fun y => hM1 _
  have hMb2 : ∀ y : Euc 2, ‖ibpPdW (ibpPdW ζ w) w (σ, x - planeι y)‖ ≤ M2 := fun y => hM2 _
  have I1 : Integrable (fun y : Euc 2 => ibpA0 θ v y • ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hA0int hgc hMb0
  have I2 : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • ibpPdW (ibpPdW ζ w) w (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hGint hW2gc hMb2
  -- first integration by parts, along `v`, for `ζ(σ, x - ι ·)`
  have E1 : ∫ y : Euc 2, ibpDfun θ v y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v
      = -∫ y : Euc 2, ibpDfun θ v y • ibpPdW ζ w (σ, x - planeι y) := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [ibp_shift_fderiv hζd σ x y v, ← hw, smul_neg]
    try rfl
  have E2 : ∫ y : Euc 2, fderiv ℝ (ibpDfun θ v) y v • ζ (σ, x - planeι y)
      = ∫ y : Euc 2, ibpA0 θ v y • ζ (σ, x - planeι y) := by
    congr 1
    funext y
    rw [ibp_fderiv_Dfun hθ y v hv]
  have J1 : Integrable (fun y : Euc 2 => fderiv ℝ (ibpDfun θ v) y v • ζ (σ, x - planeι y)) := by
    have e : (fun y : Euc 2 => fderiv ℝ (ibpDfun θ v) y v • ζ (σ, x - planeι y))
        = fun y => ibpA0 θ v y • ζ (σ, x - planeι y) := by
      funext y
      rw [ibp_fderiv_Dfun hθ y v hv]
    rw [e]
    exact I1
  have J2 : Integrable (fun y : Euc 2 =>
      ibpDfun θ v y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v) := by
    have e : (fun y : Euc 2 =>
        ibpDfun θ v y • fderiv ℝ (fun z : Euc 2 => ζ (σ, x - planeι z)) y v)
        = fun y => ibpDfun θ v y • -(ibpPdW ζ w (σ, x - planeι y)) := by
      funext y
      rw [ibp_shift_fderiv hζd σ x y v, ← hw]
      try rfl
    rw [e]
    exact ibp_integrable_smul_bdd hDint hW1gc.neg (M := M1) (fun y => by
      show ‖-(ibpPdW ζ w (σ, x - planeι y))‖ ≤ M1
      rw [norm_neg]
      exact hMb1 y)
  have J3 : Integrable (fun y : Euc 2 => ibpDfun θ v y • ζ (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hDint hgc hMb0
  have S1 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := ibpDfun θ v) (g := fun y : Euc 2 => ζ (σ, x - planeι y)) (v := v) J1 J2 J3
    (fun z _ => ibp_differentiableAt_Dfun θ v z) (fun z _ => hgd z)
  rw [E1, E2] at S1
  -- second integration by parts, along `v`, for `G_θ`
  have K1 : Integrable (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y v • ibpPdW ζ w (σ, x - planeι y)) := by
    have e : (fun y : Euc 2 => fderiv ℝ (gaussKernel 2 θ) y v • ibpPdW ζ w (σ, x - planeι y))
        = fun y => ibpDfun θ v y • ibpPdW ζ w (σ, x - planeι y) := by
      funext y
      rw [ibp_gauss_fderiv]
      try rfl
    rw [e]
    exact ibp_integrable_smul_bdd hDint hW1gc hMb1
  have K2 : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • fderiv ℝ (fun z : Euc 2 => ibpPdW ζ w (σ, x - planeι z)) y v) := by
    have e : (fun y : Euc 2 =>
        gaussKernel 2 θ y • fderiv ℝ (fun z : Euc 2 => ibpPdW ζ w (σ, x - planeι z)) y v)
        = fun y => gaussKernel 2 θ y • -(ibpPdW (ibpPdW ζ w) w (σ, x - planeι y)) := by
      funext y
      rw [ibp_shift_fderiv hW1d σ x y v, ← hw]
      try rfl
    rw [e]
    exact ibp_integrable_smul_bdd hGint hW2gc.neg (M := M2) (fun y => by
      show ‖-(ibpPdW (ibpPdW ζ w) w (σ, x - planeι y))‖ ≤ M2
      rw [norm_neg]
      exact hMb2 y)
  have K3 : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • ibpPdW ζ w (σ, x - planeι y)) :=
    ibp_integrable_smul_bdd hGint hW1gc hMb1
  have S2 := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := gaussKernel 2 θ) (g := fun y : Euc 2 => ibpPdW ζ w (σ, x - planeι y)) (v := v)
    K1 K2 K3 (fun z _ => hGd.differentiableAt) (fun z _ => hW1gd z)
  have E3 : ∫ y : Euc 2, gaussKernel 2 θ y •
      fderiv ℝ (fun z : Euc 2 => ibpPdW ζ w (σ, x - planeι z)) y v
      = -∫ y : Euc 2, gaussKernel 2 θ y • ibpPdW (ibpPdW ζ w) w (σ, x - planeι y) := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [ibp_shift_fderiv hW1d σ x y v, ← hw, smul_neg]
    try rfl
  have E4 : ∫ y : Euc 2, fderiv ℝ (gaussKernel 2 θ) y v • ibpPdW ζ w (σ, x - planeι y)
      = ∫ y : Euc 2, ibpDfun θ v y • ibpPdW ζ w (σ, x - planeι y) := by
    congr 1
    funext y
    rw [ibp_gauss_fderiv]
    try rfl
  rw [E3, E4] at S2
  refine ⟨I1, I2, ?_⟩
  exact (neg_inj.mp S1).symm.trans (neg_inj.mp S2).symm


end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
