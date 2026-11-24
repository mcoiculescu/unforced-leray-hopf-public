import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# B0582 (`prepared:p1.3`): one-dimensional Hardy inequality for the zero mode

Blueprint unit B0582, label `prepared:p1.3`, `paper/main.tex` lines 9412--9425 (Section P1,
reconstruction from weighted vorticity to velocity, the `k = 0` horizontal mode).

Statement in words. Let `ω̄ : ℝ → ℝ` be the zero (horizontal-mean) mode of the vorticity,
with `⟨η⟩ ω̄ ∈ L²(ℝ)`, where `⟨η⟩ = (1 + η²)^{1/2}`, and with zero total circulation
`∫_ℝ ω̄ = 0`. Then `ω̄ ∈ L¹(ℝ)` (so the circulation is a genuine integral), the primitive
`F(η) = ∫_{-∞}^η ω̄(y) dy` tends to `0` as `η → ±∞` (tex lines 9413--9414), `F ∈ L²(ℝ)`, and
`‖F‖_{L²(ℝ)} ≤ C ‖⟨η⟩ ω̄‖_{L²(ℝ)}` (display at tex lines 9416--9421) with `C = 2`.
In fact the sharper bound `‖F‖_{L²} ≤ 2 ‖η ω̄‖_{L²}` holds as soon as `ω̄ ∈ L¹` and
`∫ ω̄ = 0` (`lintegral_sq_zeroModePrimitive_le`, stated in `[0, ∞]`).

Hypotheses made explicit. The manuscript's hypotheses are `⟨η⟩ ω̄ ∈ L²` and `∫ ω̄ = 0`;
they are taken verbatim (`MemLp (fun η => jb η * ω η) 2` and `∫ η, ω η = 0`). Integrability
of `ω̄` is not assumed: it is proved (`integrable_of_weighted`), so the Bochner integral in
the zero-circulation hypothesis is never a junk value. The norm inequality is stated for
`eLpNorm` in `ℝ≥0∞` together with `MemLp F 2`, so neither side is a truncated `∞`; the
real-norm version is `hardy_zero_mode_toReal`.

Proof route. The manuscript integrates `F²` by parts on each half-line and applies
Cauchy--Schwarz. Here, to avoid the boundary terms and the absolute continuity of `F`, each
half-line is treated by the weighted Cauchy--Schwarz bound
`(∫_x^∞ |ω̄|)² ≤ (∫_x^∞ t^{-3/2}) (∫_x^∞ t^{3/2} |ω̄|²) = 2 x^{-1/2} ∫_x^∞ t^{3/2} |ω̄|²`
followed by Tonelli, `∫_0^t 2 x^{-1/2} dx = 4 t^{1/2}`, which gives
`∫_0^∞ F² ≤ 4 ∫_0^∞ t² |ω̄|²` (`hardy_Ioi`); the negative half-line follows by reflection
(`hardy_Iio`). On `η > 0` the primitive is `-∫_η^∞ ω̄` by zero circulation, as in the
manuscript. All the half-line work is done with lower Lebesgue integrals in `[0, ∞]`, so no
integrability side conditions arise there. No code was copied from the reference
formalization.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.B0582

/-- `(a^{1/2} b^{1/2})² = a b` in `[0, ∞]`. -/
lemma sq_rpow_half_mul (a b : ℝ≥0∞) : (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ 2 = a * b := by
  have h : ∀ c : ℝ≥0∞, (c ^ (1 / 2 : ℝ)) ^ 2 = c := by
    intro c
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [mul_pow, h, h]

/-- Weighted Cauchy--Schwarz on `(x, ∞)`, `x > 0`, with the weights `t^{∓3/2}`. -/
lemma cs_Ioi (ν : ℝ → ℝ≥0∞) (hν : AEMeasurable ν) {x : ℝ} (hx : 0 < x) :
    (∫⁻ t in Ioi x, ν t) ^ 2 ≤
      (∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ)))) *
        ∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (3 / 2 : ℝ)) * ν t ^ 2 := by
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (-(3 / 4 : ℝ))) with hf
  set h : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (3 / 4 : ℝ)) * ν t with hh
  have hfm : AEMeasurable f (volume.restrict (Ioi x)) :=
    (measurable_id.pow_const _).ennreal_ofReal.aemeasurable
  have hhm : AEMeasurable h (volume.restrict (Ioi x)) :=
    (measurable_id.pow_const _).ennreal_ofReal.aemeasurable.mul hν.restrict
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi x))
    Real.HolderConjugate.two_two hfm hhm
  have e1 : ∫⁻ t in Ioi x, (f * h) t = ∫⁻ t in Ioi x, ν t := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hx ht
    simp only [Pi.mul_apply, hf, hh]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ← Real.rpow_add ht0]
    norm_num
  have e2 : ∫⁻ t in Ioi x, f t ^ (2 : ℝ) = ∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hx ht
    simp only [hf]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht0.le _) (by norm_num),
      ← Real.rpow_mul ht0.le]
    norm_num
  have e3 : ∫⁻ t in Ioi x, h t ^ (2 : ℝ) =
      ∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (3 / 2 : ℝ)) * ν t ^ 2 := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hx ht
    simp only [hh]
    rw [ENNReal.rpow_two, mul_pow, ← ENNReal.rpow_two,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht0.le _) (by norm_num),
      ← Real.rpow_mul ht0.le]
    norm_num
  rw [e1, e2, e3] at hH
  calc (∫⁻ t in Ioi x, ν t) ^ 2
      ≤ ((∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ)))) ^ (1 / 2 : ℝ) *
          (∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (3 / 2 : ℝ)) * ν t ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' hH 2
    _ = _ := sq_rpow_half_mul _ _

/-- `∫_x^∞ t^{-3/2} dt = 2 x^{-1/2}` for `x > 0`. -/
lemma lintegral_Ioi_rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    ∫⁻ t in Ioi x, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) =
      ENNReal.ofReal (2 * x ^ (-(1 / 2 : ℝ))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hx)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num) hx]
    congr 1
    norm_num
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hx ht)) _

/-- `∫_0^t 2 x^{-1/2} dx = 4 t^{1/2}` for `t > 0`. -/
lemma lintegral_Ioo_rpow_neg_half {t : ℝ} (ht : 0 < t) :
    ∫⁻ x in Ioo 0 t, ENNReal.ofReal (2 * x ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal (4 * t ^ (1 / 2 : ℝ)) := by
  have hint : IntegrableOn (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) (Ioc 0 t) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) (r := -(1 / 2 : ℝ))
      (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le] at this
    exact this.const_mul 2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [← intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num))]
    congr 1
    rw [Real.zero_rpow (by norm_num)]
    norm_num
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have := Real.rpow_nonneg hx.1.le (-(1 / 2 : ℝ))
    positivity

/-- Dual Hardy inequality on the positive half-line (tex lines 9422--9423, "on `η > 0`"),
for an arbitrary a.e.-measurable `ν : ℝ → [0, ∞]`:
`∫_0^∞ (∫_x^∞ ν)² dx ≤ 4 ∫_0^∞ t² ν(t)² dt`. -/
theorem hardy_Ioi (ν : ℝ → ℝ≥0∞) (hν : AEMeasurable ν) :
    ∫⁻ x in Ioi 0, (∫⁻ t in Ioi x, ν t) ^ 2 ≤
      4 * ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ 2) * ν t ^ 2 := by
  set Φ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (2 * x ^ (-(1 / 2 : ℝ))) with hΦ
  set Ψ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (3 / 2 : ℝ)) * ν t ^ 2 with hΨ
  have hΦm : Measurable Φ := ((measurable_id.pow_const _).const_mul 2).ennreal_ofReal
  have hΨm : AEMeasurable Ψ :=
    (measurable_id.pow_const _).ennreal_ofReal.aemeasurable.mul (hν.pow_const 2)
  have step1 : ∫⁻ x in Ioi 0, (∫⁻ t in Ioi x, ν t) ^ 2 ≤
      ∫⁻ x in Ioi 0, Φ x * ∫⁻ t in Ioi x, Ψ t := by
    refine setLIntegral_mono' measurableSet_Ioi (fun x hx => ?_)
    have := cs_Ioi ν hν hx
    rwa [lintegral_Ioi_rpow_neg_three_halves hx] at this
  set S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  set K : ℝ → ℝ → ℝ≥0∞ := fun x t => S.indicator (fun p => Φ p.1 * Ψ p.2) (x, t) with hK
  have hKm : AEMeasurable (Function.uncurry K) (volume.prod volume) := by
    have : Function.uncurry K = S.indicator (fun p : ℝ × ℝ => Φ p.1 * Ψ p.2) := by
      funext p; rfl
    rw [this]
    exact ((hΦm.comp measurable_fst).aemeasurable.mul hΨm.comp_snd).indicator hSm
  have e1 : ∫⁻ x in Ioi 0, Φ x * ∫⁻ t in Ioi x, Ψ t = ∫⁻ x, ∫⁻ t, K x t := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr (fun x => ?_)
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi 0 from hx),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr (fun t => ?_)
      show _ = S.indicator (fun p => Φ p.1 * Ψ p.2) (x, t)
      by_cases hxt : x < t
      · rw [indicator_of_mem (show (x, t) ∈ S from ⟨hx, hxt⟩),
          indicator_of_mem (show t ∈ Ioi x from hxt)]
      · rw [indicator_of_notMem (show (x, t) ∉ S from fun h => hxt h.2),
          indicator_of_notMem (show t ∉ Ioi x from hxt)]
    · rw [indicator_of_notMem (show x ∉ Ioi 0 from hx)]
      symm
      have : (fun t => K x t) = fun _ => 0 := by
        funext t
        exact indicator_of_notMem (show (x, t) ∉ S from fun h => hx h.1) _
      rw [this, lintegral_zero]
  have e2 : ∫⁻ t, ∫⁻ x, K x t = ∫⁻ t in Ioi 0, Ψ t * ∫⁻ x in Ioo 0 t, Φ x := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr (fun t => ?_)
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi 0 from ht), mul_comm, ← lintegral_mul_const _ hΦm,
        ← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr (fun x => ?_)
      show S.indicator (fun p => Φ p.1 * Ψ p.2) (x, t) = _
      by_cases hxt : 0 < x ∧ x < t
      · rw [indicator_of_mem (show (x, t) ∈ S from hxt),
          indicator_of_mem (show x ∈ Ioo 0 t from hxt)]
      · rw [indicator_of_notMem (show (x, t) ∉ S from hxt),
          indicator_of_notMem (show x ∉ Ioo 0 t from hxt)]
    · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht)]
      have : (fun x => K x t) = fun _ => 0 := by
        funext x
        exact indicator_of_notMem (show (x, t) ∉ S from fun h => ht (h.1.trans h.2)) _
      rw [this, lintegral_zero]
  have e3 : ∫⁻ t in Ioi 0, Ψ t * ∫⁻ x in Ioo 0 t, Φ x =
      4 * ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ 2) * ν t ^ 2 := by
    rw [← lintegral_const_mul' 4 _ (by norm_num)]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    simp only [hΦ]
    rw [lintegral_Ioo_rpow_neg_half ht0]
    have key : ENNReal.ofReal (t ^ (3 / 2 : ℝ)) * ENNReal.ofReal (4 * t ^ (1 / 2 : ℝ)) =
        4 * ENNReal.ofReal (t ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
      have : t ^ (3 / 2 : ℝ) * (4 * t ^ (1 / 2 : ℝ)) = 4 * t ^ 2 := by
        rw [mul_left_comm, ← Real.rpow_add ht0]
        norm_num
      rw [this, ENNReal.ofReal_mul (by norm_num)]
      simp
    calc Ψ t * ENNReal.ofReal (4 * t ^ (1 / 2 : ℝ))
        = (ENNReal.ofReal (t ^ (3 / 2 : ℝ)) * ENNReal.ofReal (4 * t ^ (1 / 2 : ℝ))) * ν t ^ 2 := by
          simp only [hΨ]; ring
      _ = 4 * (ENNReal.ofReal (t ^ 2) * ν t ^ 2) := by rw [key]; ring
  calc ∫⁻ x in Ioi 0, (∫⁻ t in Ioi x, ν t) ^ 2
      ≤ ∫⁻ x in Ioi 0, Φ x * ∫⁻ t in Ioi x, Ψ t := step1
    _ = ∫⁻ x, ∫⁻ t, K x t := e1
    _ = ∫⁻ t, ∫⁻ x, K x t := lintegral_lintegral_swap hKm
    _ = ∫⁻ t in Ioi 0, Ψ t * ∫⁻ x in Ioo 0 t, Φ x := e2
    _ = 4 * ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ 2) * ν t ^ 2 := e3

/-- Hardy inequality on the negative half-line (tex lines 9424--9425, "the negative half-line
is identical"): `∫_{-∞}^0 (∫_{-∞}^x ν)² dx ≤ 4 ∫_{-∞}^0 t² ν(t)² dt`, by reflection. -/
theorem hardy_Iio (ν : ℝ → ℝ≥0∞) (hν : AEMeasurable ν) :
    ∫⁻ x in Iio 0, (∫⁻ t in Iio x, ν t) ^ 2 ≤
      4 * ∫⁻ t in Iio 0, ENNReal.ofReal (t ^ 2) * ν t ^ 2 := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hme : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hν' : AEMeasurable (fun t => ν (-t)) :=
    hν.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have pre : ∀ a : ℝ, (fun x : ℝ => -x) ⁻¹' Iio a = Ioi (-a) := by
    intro a; ext y
    simp only [mem_preimage, mem_Iio, mem_Ioi]
    constructor <;> intro h <;> linarith
  have inner : ∀ x : ℝ, ∫⁻ t in Iio x, ν t = ∫⁻ t in Ioi (-x), ν (-t) := by
    intro x
    rw [← hmp.setLIntegral_comp_preimage_emb hme ν (Iio x), pre]
  have h1 : ∫⁻ x in Iio 0, (∫⁻ t in Iio x, ν t) ^ 2 =
      ∫⁻ x in Ioi 0, (∫⁻ t in Ioi x, ν (-t)) ^ 2 := by
    rw [← hmp.setLIntegral_comp_preimage_emb hme (fun x => (∫⁻ t in Iio x, ν t) ^ 2) (Iio 0),
      pre, neg_zero]
    refine lintegral_congr (fun x => ?_)
    simp only [inner, neg_neg]
  have h2 : ∫⁻ t in Iio 0, ENNReal.ofReal (t ^ 2) * ν t ^ 2 =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ 2) * ν (-t) ^ 2 := by
    rw [← hmp.setLIntegral_comp_preimage_emb hme
      (fun t => ENNReal.ofReal (t ^ 2) * ν t ^ 2) (Iio 0), pre, neg_zero]
    refine lintegral_congr (fun x => ?_)
    simp only [neg_sq]
  rw [h1, h2]
  exact hardy_Ioi _ hν'

/-- The Japanese bracket `⟨η⟩ = (1 + η²)^{1/2}` of tex line 9418 (the one-dimensional case of
`⟨(q, η)⟩` in the weight of `X_m`, tex line 9373). -/
noncomputable def jb (η : ℝ) : ℝ := Real.sqrt (1 + η ^ 2)

/-- `⟨η⟩ > 0`. -/
lemma jb_pos (η : ℝ) : 0 < jb η := Real.sqrt_pos.mpr (by positivity)

/-- `⟨η⟩² = 1 + η²`. -/
lemma jb_sq (η : ℝ) : jb η ^ 2 = 1 + η ^ 2 := Real.sq_sqrt (by positivity)

/-- `⟨·⟩` is continuous. -/
lemma continuous_jb : Continuous jb := by
  unfold jb; fun_prop

/-- The primitive `∫_{-∞}^η ω̄(y) dy` of the zero mode (tex lines 9412--9413 and 9417): the
`k = 0` velocity. -/
noncomputable def zeroModePrimitive (ω : ℝ → ℝ) (η : ℝ) : ℝ := ∫ y in Iic η, ω y

/-- Measurability of `ω̄` from that of `⟨η⟩ ω̄`. -/
lemma aestronglyMeasurable_of_weighted {ω : ℝ → ℝ}
    (hω : AEStronglyMeasurable (fun η => jb η * ω η) volume) :
    AEStronglyMeasurable ω volume := by
  have e : ω = fun η => (jb η)⁻¹ * (jb η * ω η) := by
    funext η; rw [← mul_assoc, inv_mul_cancel₀ (jb_pos η).ne', one_mul]
  rw [e]
  exact (continuous_jb.inv₀ (fun η => (jb_pos η).ne')).aestronglyMeasurable.mul hω

/-- `⟨η⟩ ω̄ ∈ L²` forces `ω̄ ∈ L¹`, so the total circulation `∫ ω̄` (tex lines 9408 and
9414) is a genuine integral: `|ω̄| ≤ ((1 + η²)⁻¹ + (⟨η⟩ ω̄)²) / 2`. -/
theorem integrable_of_weighted {ω : ℝ → ℝ} (hω : MemLp (fun η => jb η * ω η) 2 volume) :
    Integrable ω := by
  have hm := aestronglyMeasurable_of_weighted hω.1
  refine Integrable.mono' ((integrable_inv_one_add_sq.add hω.integrable_sq).div_const 2) hm
    (Eventually.of_forall (fun η => ?_))
  have hs := jb_pos η
  set a : ℝ := (jb η)⁻¹ with ha
  set b : ℝ := jb η * |ω η| with hb
  have hab : |ω η| = a * b := by
    rw [ha, hb, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have ha2 : (1 + η ^ 2)⁻¹ = a ^ 2 := by rw [ha, inv_pow, jb_sq]
  have hb2 : (jb η * ω η) ^ 2 = b ^ 2 := by rw [hb, mul_pow, mul_pow, sq_abs]
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [ha2, hb2, hab]
  nlinarith [sq_nonneg (a - b)]

/-- The primitive as the integral of an indicator. -/
lemma integral_indicator_Iic (ω : ℝ → ℝ) (η : ℝ) :
    ∫ y, (Iic η).indicator ω y = zeroModePrimitive ω η :=
  integral_indicator measurableSet_Iic

/-- The primitive vanishes at `-∞` (tex lines 9413--9414). -/
theorem tendsto_zeroModePrimitive_atBot {ω : ℝ → ℝ} (hint : Integrable ω) :
    Tendsto (zeroModePrimitive ω) atBot (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atBot)
    (F := fun η => (Iic η).indicator ω) (f := fun _ => (0 : ℝ)) (fun y => ‖ω y‖)
    (Eventually.of_forall (fun η => hint.aestronglyMeasurable.indicator measurableSet_Iic))
    (Eventually.of_forall (fun η => Eventually.of_forall
      (fun y => norm_indicator_le_norm_self _ _)))
    hint.norm
    (Eventually.of_forall (fun y => tendsto_const_nhds.congr'
      ((eventually_lt_atBot y).mono (fun η hη =>
        (indicator_of_notMem (show y ∉ Iic η from not_le.mpr hη) _).symm))))
  simpa only [integral_zero, integral_indicator_Iic] using h

/-- With zero total circulation, the primitive vanishes at `+∞` (tex lines 9413--9414). -/
theorem tendsto_zeroModePrimitive_atTop {ω : ℝ → ℝ} (hint : Integrable ω)
    (hmean : ∫ η, ω η = 0) :
    Tendsto (zeroModePrimitive ω) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun η => (Iic η).indicator ω) (f := ω) (fun y => ‖ω y‖)
    (Eventually.of_forall (fun η => hint.aestronglyMeasurable.indicator measurableSet_Iic))
    (Eventually.of_forall (fun η => Eventually.of_forall
      (fun y => norm_indicator_le_norm_self _ _)))
    hint.norm
    (Eventually.of_forall (fun y => tendsto_const_nhds.congr'
      ((eventually_ge_atTop y).mono (fun η hη =>
        (indicator_of_mem (show y ∈ Iic η from hη) _).symm))))
  simpa only [hmean, integral_indicator_Iic] using h

/-- The primitive of an integrable function is continuous. -/
theorem continuous_zeroModePrimitive {ω : ℝ → ℝ} (hint : Integrable ω) :
    Continuous (zeroModePrimitive ω) := by
  have e : zeroModePrimitive ω = fun η => zeroModePrimitive ω 0 + ∫ y in (0 : ℝ)..η, ω y := by
    funext η
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
    simp only [zeroModePrimitive]
    ring
  rw [e]
  exact continuous_const.add
    (intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0)

/-- `|F(x)| ≤ ∫_{-∞}^x |ω̄|`. -/
lemma enorm_zeroModePrimitive_le_Iio {ω : ℝ → ℝ} (x : ℝ) :
    ‖zeroModePrimitive ω x‖ₑ ≤ ∫⁻ t in Iio x, ‖ω t‖ₑ := by
  rw [setLIntegral_congr Iio_ae_eq_Iic]
  exact enorm_integral_le_lintegral_enorm _

/-- With zero circulation `F(x) = -∫_x^∞ ω̄` (tex lines 9422--9423), so
`|F(x)| ≤ ∫_x^∞ |ω̄|`. -/
lemma enorm_zeroModePrimitive_le_Ioi {ω : ℝ → ℝ} (hint : Integrable ω)
    (hmean : ∫ η, ω η = 0) (x : ℝ) :
    ‖zeroModePrimitive ω x‖ₑ ≤ ∫⁻ t in Ioi x, ‖ω t‖ₑ := by
  have h := integral_add_compl (measurableSet_Iic (a := x)) hint
  rw [compl_Iic, hmean] at h
  have e : zeroModePrimitive ω x = -∫ t in Ioi x, ω t := by
    simp only [zeroModePrimitive]; linarith
  rw [e, enorm_neg]
  exact enorm_integral_le_lintegral_enorm _

/-- Splitting a lower integral over `ℝ` at `0`. -/
lemma lintegral_split (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x = (∫⁻ x in Iio 0, f x) + ∫⁻ x in Ioi 0, f x := by
  rw [← lintegral_add_compl f (measurableSet_Iio (a := (0 : ℝ))), compl_Iio,
    setLIntegral_congr (Ioi_ae_eq_Ici (a := (0 : ℝ))).symm]

/-- Sharp form of the Hardy inequality (tex lines 9416--9425): if `ω̄ ∈ L¹(ℝ)` and
`∫ ω̄ = 0`, then `∫ |∫_{-∞}^η ω̄|² dη ≤ 4 ∫ η² |ω̄(η)|² dη` (in `[0, ∞]`). -/
theorem lintegral_sq_zeroModePrimitive_le {ω : ℝ → ℝ} (hint : Integrable ω)
    (hmean : ∫ η, ω η = 0) :
    ∫⁻ η, ‖zeroModePrimitive ω η‖ₑ ^ 2 ≤ 4 * ∫⁻ η, ‖η * ω η‖ₑ ^ 2 := by
  have hν : AEMeasurable (fun t => ‖ω t‖ₑ) := hint.aestronglyMeasurable.enorm
  have w : ∀ η : ℝ, ‖η * ω η‖ₑ ^ 2 = ENNReal.ofReal (η ^ 2) * ‖ω η‖ₑ ^ 2 := by
    intro η
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [w]
  rw [lintegral_split, lintegral_split (fun η => ENNReal.ofReal (η ^ 2) * ‖ω η‖ₑ ^ 2), mul_add]
  gcongr ?_ + ?_
  · calc ∫⁻ x in Iio 0, ‖zeroModePrimitive ω x‖ₑ ^ 2
        ≤ ∫⁻ x in Iio 0, (∫⁻ t in Iio x, ‖ω t‖ₑ) ^ 2 :=
          lintegral_mono (fun x => pow_le_pow_left' (enorm_zeroModePrimitive_le_Iio x) 2)
      _ ≤ _ := hardy_Iio _ hν
  · calc ∫⁻ x in Ioi 0, ‖zeroModePrimitive ω x‖ₑ ^ 2
        ≤ ∫⁻ x in Ioi 0, (∫⁻ t in Ioi x, ‖ω t‖ₑ) ^ 2 :=
          lintegral_mono (fun x => pow_le_pow_left'
            (enorm_zeroModePrimitive_le_Ioi hint hmean x) 2)
      _ ≤ _ := hardy_Ioi _ hν

/-- `‖f‖_{L²} = (∫ |f|²)^{1/2}` in `[0, ∞]`. -/
lemma eLpNorm_two_eq (f : ℝ → ℝ) :
    eLpNorm f 2 volume = (∫⁻ η, ‖f η‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  simp_rw [ENNReal.rpow_two]

/-- **B0582, `prepared:p1.3` (tex lines 9412--9425).** If `⟨η⟩ ω̄ ∈ L²(ℝ)` and the total
circulation vanishes, `∫ ω̄ = 0`, then `ω̄ ∈ L¹(ℝ)` (so `∫ ω̄` is a genuine integral), the
primitive `∫_{-∞}^η ω̄` tends to `0` at both ends (tex lines 9413--9414), it lies in `L²(ℝ)`,
and `‖∫_{-∞}^η ω̄‖_{L²} ≤ C ‖⟨η⟩ ω̄‖_{L²}` with `C = 2` (the display at tex lines 9416--9421). -/
theorem hardy_zero_mode (ω : ℝ → ℝ)
    (hω : MemLp (fun η => jb η * ω η) 2 volume) (hmean : ∫ η, ω η = 0) :
    Integrable ω ∧
    Tendsto (zeroModePrimitive ω) atBot (𝓝 0) ∧
    Tendsto (zeroModePrimitive ω) atTop (𝓝 0) ∧
    MemLp (zeroModePrimitive ω) 2 volume ∧
    eLpNorm (zeroModePrimitive ω) 2 volume ≤ 2 * eLpNorm (fun η => jb η * ω η) 2 volume := by
  have hint := integrable_of_weighted hω
  have hle : eLpNorm (zeroModePrimitive ω) 2 volume ≤
      2 * eLpNorm (fun η => jb η * ω η) 2 volume := by
    have h1 : ∫⁻ η, ‖zeroModePrimitive ω η‖ₑ ^ 2 ≤ 4 * ∫⁻ η, ‖jb η * ω η‖ₑ ^ 2 := by
      refine (lintegral_sq_zeroModePrimitive_le hint hmean).trans ?_
      gcongr with η
      rw [enorm_mul, enorm_mul]
      gcongr
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal (jb_pos η).le]
      exact ENNReal.ofReal_le_ofReal (Real.abs_le_sqrt (by linarith))
    rw [eLpNorm_two_eq, eLpNorm_two_eq]
    calc (∫⁻ η, ‖zeroModePrimitive ω η‖ₑ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (4 * ∫⁻ η, ‖jb η * ω η‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = 2 * (∫⁻ η, ‖jb η * ω η‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) by rw [ENNReal.rpow_two]; norm_num,
            ← ENNReal.rpow_mul]
          norm_num
  refine ⟨hint, tendsto_zeroModePrimitive_atBot hint, tendsto_zeroModePrimitive_atTop hint hmean,
    ⟨(continuous_zeroModePrimitive hint).aestronglyMeasurable, ?_⟩, hle⟩
  exact hle.trans_lt (ENNReal.mul_lt_top (by norm_num) hω.2)

/-- The inequality of tex lines 9416--9421 for the real `L²` norms (both finite). -/
theorem hardy_zero_mode_toReal (ω : ℝ → ℝ)
    (hω : MemLp (fun η => jb η * ω η) 2 volume) (hmean : ∫ η, ω η = 0) :
    (eLpNorm (zeroModePrimitive ω) 2 volume).toReal ≤
      2 * (eLpNorm (fun η => jb η * ω η) 2 volume).toReal := by
  have h := (hardy_zero_mode ω hω hmean).2.2.2.2
  have hfin : 2 * eLpNorm (fun η => jb η * ω η) 2 volume ≠ ∞ :=
    (ENNReal.mul_lt_top (by norm_num) hω.2).ne
  have := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

/-- The display at tex lines 9416--9421 in the manuscript's form: there is one constant `C`
such that for every `ω̄` with `⟨η⟩ ω̄ ∈ L²(ℝ)` and `∫ ω̄ = 0` the primitive is in `L²(ℝ)`
and `‖∫_{-∞}^η ω̄‖_{L²} ≤ C ‖⟨η⟩ ω̄‖_{L²}`. -/
theorem hardy_zero_mode_exists_const :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω : ℝ → ℝ, MemLp (fun η => jb η * ω η) 2 volume →
      ∫ η, ω η = 0 →
      MemLp (zeroModePrimitive ω) 2 volume ∧
      eLpNorm (zeroModePrimitive ω) 2 volume ≤
        ENNReal.ofReal C * eLpNorm (fun η => jb η * ω η) 2 volume := by
  refine ⟨2, by norm_num, fun ω hω hmean => ?_⟩
  obtain ⟨-, -, -, hL2, hle⟩ := hardy_zero_mode ω hω hmean
  refine ⟨hL2, ?_⟩
  simpa using hle

end UnforcedLeray.B0582
