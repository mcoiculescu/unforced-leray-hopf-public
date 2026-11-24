import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.FiberBound

/-!
# `HeatFiberContReduce` (source `the November 2 reference manuscript` lines 1650-1656)

The `MeridC = ℂ²`-valued fibre statement `HeatFiberCont` follows from the `Vec = ℝ²`-valued one
`HeatFiberContVec`. Split `v ∈ MeridC` into its real part vector `(Re v₀, Re v₁)` and imaginary part
vector `(Im v₀, Im v₁)`, both in `Vec`. Then `‖v‖² = ‖Re v‖² + ‖Im v‖²` exactly. The real-linear
coordinate maps commute with `planeHeat θ` (θ > 0) for almost every point of the strip, because the
Gaussian-weighted integrand is integrable there (`integrable_gauss_smul`). The strip integral of
the fibre error therefore splits as the sum of the two `Vec`-valued fibre errors.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0224 (planeHeat strip planeι planeHeat_of_pos planeHeat_of_nonpos
  lintegral_strip_gauss measurable_planeι measurable_ofReal_gauss integrable_gauss_smul)
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The real parts of the two complex coordinates, as a real vector (real-linear, continuous). -/
def meridRe : MeridC →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i : Fin 2 => (v i).re)
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro r v; ext i; simp }

/-- The imaginary parts of the two complex coordinates, as a real vector. -/
def meridIm : MeridC →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i : Fin 2 => (v i).im)
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro r v; ext i; simp }

theorem meridRe_apply (v : MeridC) (i : Fin 2) : meridRe v i = (v i).re := rfl

theorem meridIm_apply (v : MeridC) (i : Fin 2) : meridIm v i = (v i).im := rfl

/-- `‖v‖ₑ² = ‖Re v‖ₑ² + ‖Im v‖ₑ²` for `v ∈ MeridC`. -/
theorem meridC_sq_enorm (v : MeridC) :
    ‖v‖ₑ ^ 2 = ‖meridRe v‖ₑ ^ 2 + ‖meridIm v‖ₑ ^ 2 := by
  have hreal : ‖v‖ ^ 2 = ‖meridRe v‖ ^ 2 + ‖meridIm v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, meridRe_apply, meridIm_apply, Real.norm_eq_abs, sq_abs,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  calc ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (‖meridRe v‖ ^ 2 + ‖meridIm v‖ ^ 2) := by rw [hreal]
    _ = ENNReal.ofReal (‖meridRe v‖ ^ 2) + ENNReal.ofReal (‖meridIm v‖ ^ 2) :=
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
    _ = ‖meridRe v‖ₑ ^ 2 + ‖meridIm v‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
          ofReal_norm, ofReal_norm]

/-- A real-linear continuous map commutes with the planar heat for `θ > 0` at points where the
Gaussian-weighted integrand is integrable. -/
theorem planeHeat_comp_clm {θ : ℝ} (hθ : 0 < θ) (L : MeridC →L[ℝ] Vec) (u : ℝ × ℝ → MeridC)
    (z : ℝ × ℝ)
    (hint : Integrable (fun y : Euc 2 => gaussKernel 2 θ y • u (z - planeι y))) :
    L (planeHeat θ u z) = planeHeat θ (fun w => L (u w)) z := by
  rw [planeHeat_of_pos hθ, planeHeat_of_pos hθ, ← ContinuousLinearMap.integral_comp_comm L hint]
  congr 1
  funext y
  exact map_smul L _ _

/-- Strip integrals with `c ≤ 0` vanish: the strip is empty. -/
theorem ae_strip_of_not_pos {c : ℝ} (hc : ¬ 0 < c) (P : ℝ × ℝ → Prop) :
    ∀ᵐ z ∂(volume.restrict (strip c)), P z := by
  rw [strip, Set.Ioc_eq_empty hc, Set.empty_prod, Measure.restrict_empty]
  rw [ae_zero]
  exact Filter.eventually_bot

theorem heatFiberContReduce_holds (c : ℝ) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberContReduce c := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberContReduce
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberCont
  intro hVec u hm hp hfin
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberContVec at hVec
  have hu1m : StronglyMeasurable (fun w => meridRe (u w)) :=
    meridRe.continuous.comp_stronglyMeasurable hm
  have hu2m : StronglyMeasurable (fun w => meridIm (u w)) :=
    meridIm.continuous.comp_stronglyMeasurable hm
  have hu1p : UnforcedLeray.Cyl.IsPeriodic c (fun w => meridRe (u w)) :=
    fun z => by
      show meridRe (u (z.1 + c, z.2)) = meridRe (u z)
      rw [hp z]
  have hu2p : UnforcedLeray.Cyl.IsPeriodic c (fun w => meridIm (u w)) :=
    fun z => by
      show meridIm (u (z.1 + c, z.2)) = meridIm (u z)
      rw [hp z]
  have hfin1 : ∫⁻ z in strip c, ‖(fun w => meridRe (u w)) z‖ₑ ^ 2 < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hfin
    rw [meridC_sq_enorm (u z)]
    exact le_self_add
  have hfin2 : ∫⁻ z in strip c, ‖(fun w => meridIm (u w)) z‖ₑ ^ 2 < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hfin
    rw [meridC_sq_enorm (u z)]
    exact le_add_self
  have hV1 := hVec (fun w => meridRe (u w)) hu1m hu1p hfin1
  have hV2 := hVec (fun w => meridIm (u w)) hu2m hu2p hfin2
  have hdecomp : ∀ θ : ℝ,
      (∫⁻ z in strip c, ‖planeHeat θ u z - u z‖ₑ ^ 2) =
        (∫⁻ z in strip c, ‖planeHeat θ (fun w => meridRe (u w)) z - meridRe (u z)‖ₑ ^ 2) +
        (∫⁻ z in strip c, ‖planeHeat θ (fun w => meridIm (u w)) z - meridIm (u z)‖ₑ ^ 2) := by
    intro θ
    by_cases hθ : 0 < θ
    · have hm2 : Measurable (fun w : ℝ × ℝ => ‖u w‖ₑ ^ 2) :=
        (hm.measurable.enorm).pow_const 2
      have hae : ∀ᵐ z ∂(volume.restrict (strip c)),
          (∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (z - planeι y)‖ₑ ^ 2) < ∞ := by
        by_cases hc : 0 < c
        · have hF : Measurable (fun z : ℝ × ℝ =>
              ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (z - planeι y)‖ₑ ^ 2) := by
            refine Measurable.lintegral_prod_right'
              (f := fun q : (ℝ × ℝ) × Euc 2 =>
                ENNReal.ofReal (gaussKernel 2 θ q.2) * ‖u (q.1 - planeι q.2)‖ₑ ^ 2) ?_
            exact ((measurable_ofReal_gauss θ).comp measurable_snd).mul
              (hm2.comp (measurable_fst.sub (measurable_planeι.comp measurable_snd)))
          have hφ : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ‖u z‖ₑ ^ 2) :=
            fun z => by
              show ‖u (z.1 + c, z.2)‖ₑ ^ 2 = ‖u z‖ₑ ^ 2
              rw [hp z]
          have hlin : (∫⁻ z in strip c,
              (∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ‖u (z - planeι y)‖ₑ ^ 2))
              = ∫⁻ z in strip c, ‖u z‖ₑ ^ 2 :=
            lintegral_strip_gauss hc hθ hm2 hφ
          exact ae_lt_top hF (by rw [hlin]; exact hfin.ne)
        · exact ae_strip_of_not_pos hc _
      have hint : ∀ᵐ z ∂(volume.restrict (strip c)),
          Integrable (fun y : Euc 2 => gaussKernel 2 θ y • u (z - planeι y)) := by
        filter_upwards [hae] with z hz
        exact integrable_gauss_smul hθ
          (hm.comp_measurable (measurable_const.sub measurable_planeι)).aestronglyMeasurable hz
      have hcommR : ∀ᵐ z ∂(volume.restrict (strip c)),
          meridRe (planeHeat θ u z) = planeHeat θ (fun w => meridRe (u w)) z := by
        filter_upwards [hint] with z hz
        exact planeHeat_comp_clm hθ meridRe u z hz
      have hcommI : ∀ᵐ z ∂(volume.restrict (strip c)),
          meridIm (planeHeat θ u z) = planeHeat θ (fun w => meridIm (u w)) z := by
        filter_upwards [hint] with z hz
        exact planeHeat_comp_clm hθ meridIm u z hz
      have hNorm : ∀ᵐ z ∂(volume.restrict (strip c)),
          ‖planeHeat θ u z - u z‖ₑ ^ 2 =
            ‖planeHeat θ (fun w => meridRe (u w)) z - meridRe (u z)‖ₑ ^ 2 +
            ‖planeHeat θ (fun w => meridIm (u w)) z - meridIm (u z)‖ₑ ^ 2 := by
        filter_upwards [hcommR, hcommI] with z h1 h2
        rw [meridC_sq_enorm (planeHeat θ u z - u z), map_sub, map_sub, h1, h2]
      have hA : Measurable (fun z : ℝ × ℝ =>
          ‖planeHeat θ (fun w => meridRe (u w)) z - meridRe (u z)‖ₑ ^ 2) :=
        (((FiberBoundAux.stronglyMeasurable_planeHeat_pos' hθ hu1m).measurable).sub
          (meridRe.continuous.measurable.comp hm.measurable)).enorm.pow_const 2
      rw [lintegral_congr_ae hNorm, lintegral_add_left' hA.aemeasurable]
    · have h1 : planeHeat θ u = u := planeHeat_of_nonpos (not_lt.1 hθ) u
      have h2 : planeHeat θ (fun w => meridRe (u w)) = fun w => meridRe (u w) :=
        planeHeat_of_nonpos (not_lt.1 hθ) _
      have h3 : planeHeat θ (fun w => meridIm (u w)) = fun w => meridIm (u w) :=
        planeHeat_of_nonpos (not_lt.1 hθ) _
      simp only [h1, h2, h3, sub_self, enorm_zero, zero_pow two_ne_zero, lintegral_zero, add_zero]
  have hfun : (fun θ : ℝ => ∫⁻ z in strip c, ‖planeHeat θ u z - u z‖ₑ ^ 2) =
      fun θ : ℝ => (∫⁻ z in strip c, ‖planeHeat θ (fun w => meridRe (u w)) z - meridRe (u z)‖ₑ ^ 2) +
        (∫⁻ z in strip c, ‖planeHeat θ (fun w => meridIm (u w)) z - meridIm (u z)‖ₑ ^ 2) :=
    funext hdecomp
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.stripN
  rw [hfun]
  simpa using hV1.add hV2

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
