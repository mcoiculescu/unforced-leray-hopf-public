import UnforcedLeray.Short.PartIIa.Tasks.R05ResidualFromTable.EnvelopeBounds
import UnforcedLeray.Lib.Axisymmetric.RingMeasure
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Helper module `EnvelopeLp` for `PartII-a:R05`

Proves that `spatialEnvelope R y := resEnvelope (Axi.age R y) (Axi.trans R y)` belongs to
`L^p(ℝ³)` for `2 ≤ p` and `2 ≤ R` with norm bounded by `C_env * R ^ (2 / p)` (via
`Axi.lintegral_ringChart`), and derives `MemLp`, `eLpNorm` bounds, and `L^p` time continuity
(by dominated convergence) for any family of fields dominated off the axis by
`K * spatialEnvelope R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.R05

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0188 UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa

/-! ### 1. The 1D integral `I₁ = ∫ (1 + x²)^{-1} dx < ∞` -/

/-- The 1D integral `∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-1 : ℝ))`. -/
def envI1 : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-1 : ℝ))

theorem envI1_lt_top : envI1 < ⊤ := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * (1 : ℝ) := by
    simp only [Module.finrank_self, Nat.cast_one]
    norm_num
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) hr
  have hexp : -(2 * (1 : ℝ)) / 2 = (-1 : ℝ) := by ring
  have heq : envI1 = ∫⁻ x : ℝ, ‖((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * (1 : ℝ)) / 2)‖ₑ := by
    unfold envI1
    refine lintegral_congr fun x => ?_
    have hx : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
    rw [hexp, Real.norm_eq_abs, sq_abs, Real.enorm_eq_ofReal (Real.rpow_nonneg hx _)]
  rw [heq]
  exact hint.2

/-- Real value of `envI1`. -/
def envM1 : ℝ := envI1.toReal

theorem envM1_nonneg : 0 ≤ envM1 := ENNReal.toReal_nonneg

theorem ofReal_envM1 : ENNReal.ofReal envM1 = envI1 :=
  ENNReal.ofReal_toReal envI1_lt_top.ne

/-! ### 2. Pointwise inequalities for the ring-chart integrand -/

theorem inv_one_add_sq_le_one (x : ℝ) : (1 + x ^ 2) ^ (-1 : ℝ) ≤ 1 := by
  rw [Real.rpow_neg_one]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])

theorem early_integrand_bound {s η p : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hp : 2 ≤ p) :
    s ^ (-(5 / 2 : ℝ)) * (resEnvelope s η) ^ p ≤ (1 + η ^ 2) ^ (-1 : ℝ) := by
  have henv : resEnvelope s η = s ^ (3 / 2 : ℝ) * (1 + η ^ 2) ^ (-1 : ℝ) := by
    unfold resEnvelope
    rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hs0)),
      ite_eq_left_iff.mpr (fun h => absurd hs1 h)]
  rw [henv]
  have hs32_0 : 0 ≤ s ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hs32_1 : s ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hs0.le hs1 (by norm_num)
  have hη_0 : 0 ≤ (1 + η ^ 2) ^ (-1 : ℝ) := by positivity
  have hη_1 : (1 + η ^ 2) ^ (-1 : ℝ) ≤ 1 := inv_one_add_sq_le_one η
  rw [Real.mul_rpow hs32_0 hη_0]
  have hp_s : (s ^ (3 / 2 : ℝ)) ^ p ≤ s ^ (3 : ℝ) := by
    calc (s ^ (3 / 2 : ℝ)) ^ p ≤ (s ^ (3 / 2 : ℝ)) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos hs0 _) hs32_1 hp
      _ = s ^ ((3 / 2 : ℝ) * 2) := (Real.rpow_mul hs0.le _ _).symm
      _ = s ^ (3 : ℝ) := by norm_num
  have hp_η : ((1 + η ^ 2) ^ (-1 : ℝ)) ^ p ≤ (1 + η ^ 2) ^ (-1 : ℝ) := by
    calc ((1 + η ^ 2) ^ (-1 : ℝ)) ^ p ≤ ((1 + η ^ 2) ^ (-1 : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity) hη_1 (by linarith)
      _ = (1 + η ^ 2) ^ (-1 : ℝ) := Real.rpow_one _
  have hs_prod : s ^ (-(5 / 2 : ℝ)) * s ^ (3 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hs0, show -(5 / 2 : ℝ) + 3 = 1 / 2 by ring]
    exact Real.rpow_le_one hs0.le hs1 (by norm_num)
  calc s ^ (-(5 / 2 : ℝ)) * ((s ^ (3 / 2 : ℝ)) ^ p * ((1 + η ^ 2) ^ (-1 : ℝ)) ^ p)
      ≤ s ^ (-(5 / 2 : ℝ)) * (s ^ (3 : ℝ) * (1 + η ^ 2) ^ (-1 : ℝ)) := by gcongr
    _ = (s ^ (-(5 / 2 : ℝ)) * s ^ (3 : ℝ)) * (1 + η ^ 2) ^ (-1 : ℝ) := by ring
    _ ≤ 1 * (1 + η ^ 2) ^ (-1 : ℝ) := by gcongr
    _ = (1 + η ^ 2) ^ (-1 : ℝ) := one_mul _

theorem late_integrand_bound {s η p : ℝ} (hs1 : 1 < s) (hp : 2 ≤ p) :
    s ^ (-(5 / 2 : ℝ)) * (resEnvelope s η) ^ p ≤
      s ^ (-(5 / 2 : ℝ)) * (1 + (η / √s) ^ 2) ^ (-1 : ℝ) := by
  have hs0 : 0 < s := by linarith
  have henv : resEnvelope s η = (1 + (η / √s) ^ 2) ^ (-1 : ℝ) := by
    unfold resEnvelope
    rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hs0)),
      ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hs1)),
      div_pow, Real.sq_sqrt hs0.le]
  rw [henv]
  have hη_1 : (1 + (η / √s) ^ 2) ^ (-1 : ℝ) ≤ 1 := inv_one_add_sq_le_one (η / √s)
  have hp_η : ((1 + (η / √s) ^ 2) ^ (-1 : ℝ)) ^ p ≤ (1 + (η / √s) ^ 2) ^ (-1 : ℝ) := by
    calc ((1 + (η / √s) ^ 2) ^ (-1 : ℝ)) ^ p ≤ ((1 + (η / √s) ^ 2) ^ (-1 : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity) hη_1 (by linarith)
      _ = (1 + (η / √s) ^ 2) ^ (-1 : ℝ) := Real.rpow_one _
  gcongr

theorem one_le_two_inv_one_add_sq {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    1 ≤ 2 * (1 + s ^ 2) ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, one_le_div (by positivity)]
  nlinarith [sq_nonneg s]

theorem rpow_neg_two_le_two_inv_one_add_sq {s : ℝ} (hs1 : 1 < s) :
    s ^ (-2 : ℝ) ≤ 2 * (1 + s ^ 2) ^ (-1 : ℝ) := by
  have hs0 : 0 < s := by linarith
  rw [Real.rpow_neg hs0.le, Real.rpow_two, Real.rpow_neg_one, inv_eq_one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (pow_pos hs0 2) (by positivity)]
  nlinarith [sq_nonneg s]

theorem rpow_neg_five_halves_mul_sqrt {s : ℝ} (hs0 : 0 < s) :
    s ^ (-(5 / 2 : ℝ)) * √s = s ^ (-2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
  norm_num

/-! ### 3. The 2D majorant on `Ioi 0 ×ˢ univ` and `MemLp` of `spatialEnvelope R` -/

/-- The 2D majorant on `(s, η)` independent of `p ≥ 2`. -/
def envMaj2D (q : ℝ × ℝ) : ℝ≥0∞ :=
  if q.1 ≤ 1 then ENNReal.ofReal ((1 + q.2 ^ 2) ^ (-1 : ℝ))
  else ENNReal.ofReal (q.1 ^ (-(5 / 2 : ℝ))) *
    ENNReal.ofReal ((1 + (q.2 / √q.1) ^ 2) ^ (-1 : ℝ))

theorem measurable_envMaj2D : Measurable envMaj2D := by
  unfold envMaj2D
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ ?_
  · fun_prop
  · fun_prop

theorem lintegral_envMaj2D_eta {s : ℝ} (hs : 0 < s) :
    ∫⁻ η : ℝ, envMaj2D (s, η) ≤
      ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1 := by
  unfold envMaj2D
  dsimp only
  split_ifs with hs1
  · change envI1 ≤ ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) :=
      ENNReal.ofReal_le_ofReal (one_le_two_inv_one_add_sq hs hs1)
    calc envI1 = ENNReal.ofReal 1 * envI1 := by rw [ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1 := by gcongr
  · have hs1' : 1 < s := not_le.mp hs1
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      Axi.lintegral_comp_div_pos (Real.sqrt_pos.mpr hs)
        (fun z => ENNReal.ofReal ((1 + z ^ 2) ^ (-1 : ℝ))),
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      rpow_neg_five_halves_mul_sqrt hs]
    change ENNReal.ofReal (s ^ (-2 : ℝ)) * envI1 ≤ _
    gcongr
    exact rpow_neg_two_le_two_inv_one_add_sq hs1'

theorem lintegral_envMaj2D_le :
    ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), envMaj2D q ≤
      ENNReal.ofReal (2 * envM1 ^ 2) := by
  rw [Measure.volume_eq_prod ℝ ℝ, Axi.setLIntegral_prod_univ _ measurable_envMaj2D]
  have h1 : ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, envMaj2D (s, η) ≤
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1 :=
    setLIntegral_mono' measurableSet_Ioi (fun s hs => lintegral_envMaj2D_eta hs)
  have h2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1 ≤
      ∫⁻ s : ℝ, ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1 :=
    setLIntegral_le_lintegral _ _
  have h3 : ∫⁻ s : ℝ, ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1 =
      ENNReal.ofReal (2 * envM1 ^ 2) := by
    have hsplit : (fun s : ℝ => ENNReal.ofReal (2 * (1 + s ^ 2) ^ (-1 : ℝ)) * envI1) =
        fun s : ℝ => (ENNReal.ofReal 2 * envI1) * ENNReal.ofReal ((1 + s ^ 2) ^ (-1 : ℝ)) := by
      funext s
      rw [ENNReal.ofReal_mul zero_le_two]
      ring
    rw [hsplit, lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top envI1_lt_top.ne)]
    change (ENNReal.ofReal 2 * envI1) * envI1 = ENNReal.ofReal (2 * envM1 ^ 2)
    rw [← ofReal_envM1, ← ENNReal.ofReal_mul zero_le_two,
      ← ENNReal.ofReal_mul (mul_nonneg zero_le_two envM1_nonneg)]
    congr 1
    ring
  exact (h1.trans h2).trans_eq h3

/-- Spatial envelope `y ↦ resEnvelope (Axi.age R y) (Axi.trans R y)`. -/
def spatialEnvelope (R : ℝ) (y : Space) : ℝ :=
  resEnvelope (Axi.age R y) (Axi.trans R y)

theorem spatialEnvelope_nonneg (R : ℝ) (y : Space) : 0 ≤ spatialEnvelope R y :=
  resEnvelope_nonneg _ _

theorem measurable_spatialEnvelope (R : ℝ) : Measurable (spatialEnvelope R) :=
  measurable_resEnvelope.comp ((Axi.measurable_age R).prodMk (Axi.measurable_trans R))

theorem lintegral_spatialEnvelope_rpow_le {R p : ℝ} (hR : 0 < R) (hp : 2 ≤ p) :
    ∫⁻ y : Space, ‖spatialEnvelope R y‖ₑ ^ p ≤
      ENNReal.ofReal (2 * π * envM1 ^ 2 * R ^ 2) := by
  have hp0 : 0 ≤ p := by linarith
  have heq : (fun y : Space => ‖spatialEnvelope R y‖ₑ ^ p) =
      fun y : Space => ENNReal.ofReal (resEnvelope (Axi.age R y) (Axi.trans R y) ^ p) := by
    funext y
    rw [Real.enorm_eq_ofReal (spatialEnvelope_nonneg R y),
      ENNReal.ofReal_rpow_of_nonneg (spatialEnvelope_nonneg R y) hp0]
    rfl
  rw [heq]
  have hg : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (resEnvelope q.1 q.2 ^ p)) :=
    ENNReal.measurable_ofReal.comp (measurable_resEnvelope.pow_const p)
  rw [Axi.lintegral_ringChart hR (fun q => ENNReal.ofReal (resEnvelope q.1 q.2 ^ p)) hg]
  have hmono : ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (q.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (resEnvelope q.1 q.2 ^ p) ≤
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), envMaj2D q := by
    refine setLIntegral_mono' (measurableSet_Ioi.prod MeasurableSet.univ) (fun q hq => ?_)
    have hs : 0 < q.1 := hq.1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    unfold envMaj2D
    split_ifs with hs1
    · exact ENNReal.ofReal_le_ofReal (early_integrand_bound hs hs1 hp)
    · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
      exact ENNReal.ofReal_le_ofReal (late_integrand_bound (not_le.mp hs1) hp)
  have hstep : ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (q.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (resEnvelope q.1 q.2 ^ p) ≤
      ENNReal.ofReal (2 * envM1 ^ 2) :=
    hmono.trans lintegral_envMaj2D_le
  calc ENNReal.ofReal (π * R ^ 2) *
        ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (q.1 ^ (-(5 / 2 : ℝ))) * ENNReal.ofReal (resEnvelope q.1 q.2 ^ p)
      ≤ ENNReal.ofReal (π * R ^ 2) * ENNReal.ofReal (2 * envM1 ^ 2) := by gcongr
    _ = ENNReal.ofReal (2 * π * envM1 ^ 2 * R ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Universal constant `C_env := 1 + 2 * π * envM1 ^ 2`. -/
def envConst : ℝ := 1 + 2 * π * envM1 ^ 2

theorem envConst_pos : 0 < envConst := by
  unfold envConst
  have : 0 ≤ 2 * π * envM1 ^ 2 := by positivity
  linarith

theorem memLp_spatialEnvelope {R p : ℝ} (hR : 0 < R) (hp : 2 ≤ p) :
    MemLp (spatialEnvelope R) (ENNReal.ofReal p) volume := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨(measurable_spatialEnvelope R).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal (by linarith)]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
    ((lintegral_spatialEnvelope_rpow_le hR hp).trans_lt ENNReal.ofReal_lt_top).ne

theorem eLpNorm_spatialEnvelope_le {R p : ℝ} (hR : 2 ≤ R) (hp : 2 ≤ p) :
    (eLpNorm (spatialEnvelope R) (ENNReal.ofReal p) volume).toReal ≤
      envConst * R ^ (2 / p) := by
  have hR0 : 0 < R := by linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have h1p0 : 0 ≤ 1 / p := by positivity
  have h1p1 : 1 / p ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr, ← ENNReal.toReal_rpow]
  have hle : (∫⁻ y : Space, ‖spatialEnvelope R y‖ₑ ^ p).toReal ≤
      envConst * R ^ 2 := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_spatialEnvelope_rpow_le hR0 hp)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    have h2 : 2 * π * envM1 ^ 2 ≤ envConst := by
      unfold envConst
      linarith
    calc (∫⁻ y : Space, ‖spatialEnvelope R y‖ₑ ^ p).toReal
        ≤ 2 * π * envM1 ^ 2 * R ^ 2 := h1
      _ ≤ envConst * R ^ 2 := by gcongr
  have hpow : (envConst * R ^ 2) ^ (1 / p) ≤ envConst * R ^ (2 / p) := by
    rw [Real.mul_rpow envConst_pos.le (by positivity)]
    have hc1 : 1 ≤ envConst := by
      unfold envConst
      have : 0 ≤ 2 * π * envM1 ^ 2 := by positivity
      linarith
    have hc_pow : envConst ^ (1 / p) ≤ envConst := by
      calc envConst ^ (1 / p) ≤ envConst ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hc1 h1p1
        _ = envConst := Real.rpow_one _
    have hR_pow : (R ^ 2) ^ (1 / p) = R ^ (2 / p) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hR0.le, mul_one_div]
    rw [hR_pow]
    gcongr
  exact (Real.rpow_le_rpow ENNReal.toReal_nonneg hle h1p0).trans hpow

/-! ### 4. Generic `MemLp`, `eLpNorm` bound, and `L^p` continuity for dominated off-axis fields -/

theorem aestronglyMeasurable_of_continuousOn_offAxis {f : SpatialField}
    (hf : ContinuousOn f Axi.axisᶜ) : AEStronglyMeasurable f volume := by
  have h1 : AEStronglyMeasurable f (volume.restrict Axi.axisᶜ) :=
    hf.aestronglyMeasurable Axi.isOpen_compl_axis.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := Axi.axisᶜ) Axi.ae_not_mem_axis] at h1

theorem memLp_and_norm_le_of_envelope {R p K : ℝ} (hR : 2 ≤ R) (hp : 2 ≤ p) (hK : 0 ≤ K)
    {f : SpatialField} (hmeas : AEStronglyMeasurable f volume)
    (hbdd : ∀ y ∉ Axi.axis, ‖f y‖ ≤ K * spatialEnvelope R y) :
    MemLp f (ENNReal.ofReal p) volume ∧
      (eLpNorm f (ENNReal.ofReal p) volume).toReal ≤
        K * envConst * R ^ (2 / p) := by
  have hR0 : 0 < R := by linarith
  have hEnvLp : MemLp (fun y => K * spatialEnvelope R y) (ENNReal.ofReal p) volume :=
    (memLp_spatialEnvelope hR0 hp).const_mul K
  have hae : ∀ᵐ y : Space ∂volume, ‖f y‖ ≤ K * spatialEnvelope R y :=
    Axi.ae_not_mem_axis.mono hbdd
  have hae_norm : ∀ᵐ y : Space ∂volume, ‖f y‖ ≤ K * ‖spatialEnvelope R y‖ := by
    filter_upwards [hae] with y hy
    rwa [Real.norm_of_nonneg (spatialEnvelope_nonneg R y)]
  have hfLp : MemLp f (ENNReal.ofReal p) volume :=
    MemLp.of_le_mul (memLp_spatialEnvelope hR0 hp) hmeas hae_norm
  refine ⟨hfLp, ?_⟩
  have hae_enorm : ∀ᵐ y : Space ∂volume, ‖f y‖ ≤ ‖(fun y => K * spatialEnvelope R y) y‖ := by
    filter_upwards [hae] with y hy
    rwa [Real.norm_of_nonneg (mul_nonneg hK (spatialEnvelope_nonneg R y))]
  have hmono := eLpNorm_mono_ae (p := ENNReal.ofReal p) hae_enorm
  have hreal := ENNReal.toReal_mono hEnvLp.2.ne hmono
  have hsmul : eLpNorm (fun y => K * spatialEnvelope R y) (ENNReal.ofReal p) volume =
      ENNReal.ofReal K * eLpNorm (spatialEnvelope R) (ENNReal.ofReal p) volume := by
    have := eLpNorm_const_smul K (spatialEnvelope R) (ENNReal.ofReal p) volume
    rwa [Real.enorm_eq_ofReal hK] at this
  rw [hsmul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at hreal
  calc (eLpNorm f (ENNReal.ofReal p) volume).toReal
      ≤ K * (eLpNorm (spatialEnvelope R) (ENNReal.ofReal p) volume).toReal := hreal
    _ ≤ K * (envConst * R ^ (2 / p)) :=
        mul_le_mul_of_nonneg_left (eLpNorm_spatialEnvelope_le hR hp) hK
    _ = K * envConst * R ^ (2 / p) := by ring

theorem tendsto_eLpNorm_sub_of_envelope {R p K : ℝ} (hR : 2 ≤ R) (hp : 2 ≤ p) (hK : 0 ≤ K)
    {H : ℝ → SpatialField} (hmeas : ∀ τ, AEStronglyMeasurable (H τ) volume)
    (hbdd : ∀ τ, ∀ y ∉ Axi.axis, ‖H τ y‖ ≤ K * spatialEnvelope R y)
    (htime : ∀ y ∉ Axi.axis, Continuous (fun τ => H τ y)) (τ₀ : ℝ) :
    Tendsto (fun τ => (eLpNorm (H τ - H τ₀) (ENNReal.ofReal p) volume).toReal)
      (𝓝 τ₀) (𝓝 0) := by
  have hR0 : 0 < R := by linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hMajLp : MemLp (fun y => (2 * K) * spatialEnvelope R y) (ENNReal.ofReal p) volume :=
    (memLp_spatialEnvelope hR0 hp).const_mul (2 * K)
  have hMajInt : Integrable (fun y => ‖(2 * K) * spatialEnvelope R y‖ ^ p) volume := by
    have h := hMajLp.integrable_norm_rpow hp0 hpt
    rwa [hpr] at h
  have hIntTendsto : Tendsto (fun τ => ∫ y, ‖H τ y - H τ₀ y‖ ^ p) (𝓝 τ₀) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : Space, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖(2 * K) * spatialEnvelope R y‖ ^ p) ?_ ?_ hMajInt ?_
    · exact Eventually.of_forall fun τ =>
        ((hmeas τ).sub (hmeas τ₀)).norm.aemeasurable.pow_const p |>.aestronglyMeasurable
    · refine Eventually.of_forall fun τ => ?_
      filter_upwards [Axi.ae_not_mem_axis] with y hy
      have hpos : 0 ≤ ‖H τ y - H τ₀ y‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
      rw [Real.norm_of_nonneg hpos]
      have hdiff : ‖H τ y - H τ₀ y‖ ≤ ‖(2 * K) * spatialEnvelope R y‖ := by
        have h1 := hbdd τ y hy
        have h2 := hbdd τ₀ y hy
        have h3 : 0 ≤ (2 * K) * spatialEnvelope R y :=
          mul_nonneg (by positivity) (spatialEnvelope_nonneg R y)
        rw [Real.norm_of_nonneg h3]
        calc ‖H τ y - H τ₀ y‖ ≤ ‖H τ y‖ + ‖H τ₀ y‖ := norm_sub_le _ _
          _ ≤ (2 * K) * spatialEnvelope R y := by linarith
      exact Real.rpow_le_rpow (norm_nonneg _) hdiff (by linarith)
    · filter_upwards [Axi.ae_not_mem_axis] with y hy
      have hc : Continuous (fun τ => ‖H τ y - H τ₀ y‖ ^ p) :=
        (((htime y hy).sub continuous_const).norm).rpow_const (fun _ => Or.inr (by linarith))
      have hval := hc.tendsto τ₀
      simp only [sub_self, norm_zero, Real.zero_rpow (by linarith : p ≠ 0)] at hval
      exact hval
  have heq : (fun τ => (eLpNorm (H τ - H τ₀) (ENNReal.ofReal p) volume).toReal) =
      fun τ => (∫ y, ‖H τ y - H τ₀ y‖ ^ p) ^ (1 / p) := by
    funext τ
    have hτ := (memLp_and_norm_le_of_envelope hR hp hK (hmeas τ) (hbdd τ)).1
    have hτ0 := (memLp_and_norm_le_of_envelope hR hp hK (hmeas τ₀) (hbdd τ₀)).1
    have hsub : MemLp (H τ - H τ₀) (ENNReal.ofReal p) volume := hτ.sub hτ0
    rw [hsub.eLpNorm_eq_integral_rpow_norm hp0 hpt, hpr, ENNReal.toReal_ofReal]
    · simp only [Pi.sub_apply, one_div]
    · exact Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  rw [heq]
  have hrpow : Continuous (fun x : ℝ => x ^ (1 / p)) :=
    continuous_id.rpow_const (fun _ => Or.inr (by positivity))
  have hlim := (hrpow.tendsto 0).comp hIntTendsto
  rwa [Real.zero_rpow (by positivity : (1 / p : ℝ) ≠ 0)] at hlim

end UnforcedLeray.Short.PartIIa.R05
