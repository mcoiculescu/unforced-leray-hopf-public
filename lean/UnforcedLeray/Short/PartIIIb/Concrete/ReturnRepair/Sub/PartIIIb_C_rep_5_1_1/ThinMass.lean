import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.Real.ConjExponents

/-!
# `PartIII-b:C/rep/5/1/1/2`: the thin mass bound `ThinMassBoundSlice`

Source `the November 2 reference manuscript` 5569-5584.

For `m_Z > 3/2`, `N_0(a) = ∫_a^∞ t^{-3/2} ∫ ‖T(t,·,η)‖_{L²_q} dη dt ≤ C(a^{-3/4}+a^{-1/2})‖T‖_{Z_1}`:

1. transverse Cauchy-Schwarz in `η` with weight `W^{-2}`, `∫ W^{-2} dη = (1+t)^{1/2} I(m_Z)`;
2. Cauchy-Schwarz in `t` with measure `dt`, splitting `t^{-3/2} = t^{-5/4} · t^{-1/4}`;
3. the `t`-integral `∫_a^∞ t^{-5/2}(1+t)^{1/2} dt ≤ a^{-1} + (2/3) a^{-3/2}`;
4. the identity `∫ t^{-1/2} G(t) dt = ‖T‖²_{Z_1}` (Fubini on the `ageμ` cell).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Elementary identities -/

lemma transWeight_sq_eq (mZ t q η : ℝ) :
    UnforcedLeray.Short.IIIa.transWeight mZ (t, (q, η)) ^ 2
      = (1 + (η / Real.sqrt (1 + t)) ^ 2) ^ mZ := by
  have hx0 : (0 : ℝ) ≤ 1 + (η / Real.sqrt (1 + t)) ^ 2 := by positivity
  show ((1 + (η / Real.sqrt (1 + t)) ^ 2) ^ (mZ / 2)) ^ 2 = (1 + (η / Real.sqrt (1 + t)) ^ 2) ^ mZ
  rw [← Real.rpow_natCast ((1 + (η / Real.sqrt (1 + t)) ^ 2) ^ (mZ / 2)) 2,
    ← Real.rpow_mul hx0]
  congr 1
  push_cast
  ring

lemma ofReal_rpow_two_eq {x e f : ℝ} (hx : 0 ≤ x) (hef : 2 * e = f) :
    (ENNReal.ofReal (x ^ e)) ^ (2 : ℝ) = ENNReal.ofReal (x ^ f) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx _) (by norm_num), ← Real.rpow_mul hx,
    mul_comm e 2, hef]

lemma sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-! ## 2. The transverse integral -/

lemma lintegral_I_lt_top {m : ℝ} (hm : 1 / 2 < m) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-m)) < ⊤ := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * m := by
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) hr
  have hexp : -(2 * m) / 2 = -m := by ring
  have heq : ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-m))
      = ∫⁻ x : ℝ, ‖((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * m) / 2)‖ₑ := by
    refine lintegral_congr fun x => ?_
    have hx : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
    rw [hexp, Real.norm_eq_abs, sq_abs, Real.enorm_eq_ofReal (Real.rpow_nonneg hx _)]
  rw [heq]
  exact hint.2

lemma lintegral_scale_rpow {m k : ℝ} (hk : 0 < k) :
    ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (-m))
      = ENNReal.ofReal k * ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-m)) :=
  lintegral_comp_div_pos hk (fun z => ENNReal.ofReal ((1 + z ^ 2) ^ (-m)))

/-- Transverse Cauchy-Schwarz: `∫ u dη ≤ (∫ W^{-2})^{1/2} (∫ W² u²)^{1/2}` with
`W = (1+(η/k)²)^{m/2}`, `∫ W^{-2} = k · I(m)`. -/
lemma lintegral_eta_cs {m k : ℝ} (hk : 0 < k) (hm : 1 / 2 < m) (u : ℝ → ℝ≥0∞)
    (hu : Measurable u) :
    ∫⁻ η, u η ≤ (ENNReal.ofReal k * ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-m))) ^ (1 / 2 : ℝ)
      * (∫⁻ η, ENNReal.ofReal ((1 + (η / k) ^ 2) ^ m) * u η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hpos : ∀ η : ℝ, 0 < 1 + (η / k) ^ 2 := fun η => by positivity
  have hf : Measurable fun η : ℝ => ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (-(m / 2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hh : Measurable fun η : ℝ => ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (m / 2)) * u η :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hu
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
    Real.HolderConjugate.two_two hf.aemeasurable hh.aemeasurable
  have hpt : ∀ η : ℝ, u η = ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (-(m / 2))) *
      (ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (m / 2)) * u η) := by
    intro η
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpos η).le (-(m / 2))),
      ← Real.rpow_add (hpos η)]
    norm_num
  have h1 : ∫⁻ η, ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (-(m / 2))) ^ (2 : ℝ)
      = ENNReal.ofReal k * ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-m)) := by
    rw [← lintegral_scale_rpow hk]
    exact lintegral_congr fun η => ofReal_rpow_two_eq (hpos η).le (by ring)
  have h2 : ∫⁻ η, (ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (m / 2)) * u η) ^ (2 : ℝ)
      = ∫⁻ η, ENNReal.ofReal ((1 + (η / k) ^ 2) ^ m) * u η ^ (2 : ℝ) := by
    refine lintegral_congr fun η => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ofReal_rpow_two_eq (hpos η).le (by ring)]
  calc ∫⁻ η, u η = ∫⁻ η, ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (-(m / 2))) *
        (ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (m / 2)) * u η) := lintegral_congr hpt
    _ ≤ (∫⁻ η, ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (-(m / 2))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ η, (ENNReal.ofReal ((1 + (η / k) ^ 2) ^ (m / 2)) * u η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          hCS
    _ = _ := by rw [h1, h2]

/-! ## 3. Measurability of the slice quantities -/

lemma measurable_sliceSq (c : ℝ) {F : Chart → Ten3} (hF : Measurable F) :
    Measurable fun p : ℝ × ℝ => ∫⁻ q in Ico (-c / 2) (c / 2),
      ENNReal.ofReal c⁻¹ * ‖F (p.1, (q, p.2))‖ₑ ^ (2 : ℝ) := by
  have hg : Measurable fun z : (ℝ × ℝ) × ℝ => ((z.1.1, (z.2, z.1.2)) : Chart) := by
    fun_prop
  have hf : Measurable fun z : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal c⁻¹ * ‖F (z.1.1, (z.2, z.1.2))‖ₑ ^ (2 : ℝ) :=
    measurable_const.mul ((hF.comp hg).enorm.pow_const (2 : ℝ))
  exact hf.lintegral_prod_right'

lemma measurable_sliceL2q (c : ℝ) {F : Chart → Ten3} (hF : Measurable F) :
    Measurable fun p : ℝ × ℝ => sliceL2q c F p.1 p.2 :=
  (measurable_sliceSq c hF).pow_const (1 / 2 : ℝ)

lemma measurable_sliceL2q_eta (c : ℝ) {F : Chart → Ten3} (hF : Measurable F) (t : ℝ) :
    Measurable fun η : ℝ => sliceL2q c F t η := by
  have hf : Measurable fun z : ℝ × ℝ => ENNReal.ofReal c⁻¹ * ‖F (t, (z.2, z.1))‖ₑ ^ (2 : ℝ) := by
    apply Measurable.const_mul
    apply Measurable.pow_const
    apply Measurable.enorm
    exact hF.comp (by fun_prop)
  have h := hf.lintegral_prod_right' (ν := volume.restrict (Ico (-c / 2) (c / 2)))
  exact h.pow_const (1 / 2 : ℝ)

lemma sliceL2q_rpow_two (c : ℝ) (F : Chart → Ten3) (t η : ℝ) :
    sliceL2q c F t η ^ (2 : ℝ)
      = ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * ‖F (t, (q, η))‖ₑ ^ (2 : ℝ) := by
  unfold sliceL2q
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The transverse-weighted slice integral `G(t) = ∫_η W² · (sliceL2q)²` at age `t`. -/
def gSq (c mZ : ℝ) (F : Chart → Ten3) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ η, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + t)) ^ 2) ^ mZ) * sliceL2q c F t η ^ (2 : ℝ)

lemma measurable_gSq (c mZ : ℝ) {F : Chart → Ten3} (hF : Measurable F) :
    Measurable (gSq c mZ F) := by
  have hW : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((1 + (p.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  have hf : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((1 + (p.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ)
        * sliceL2q c F p.1 p.2 ^ (2 : ℝ) :=
    hW.mul ((measurable_sliceL2q c hF).pow_const (2 : ℝ))
  unfold gSq
  exact hf.lintegral_prod_right'

/-! ## 4. Fubini identity linking `G` to the `Z_1` norm -/

lemma gSq_identity {c : ℝ} (hc : 0 < c) (mZ t : ℝ) (F : Chart → Ten3) :
    ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * gSq c mZ F t
      = ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal (c⁻¹ * t ^ (-1 / 2 : ℝ)) *
          (ENNReal.ofReal ((1 + (η / Real.sqrt (1 + t)) ^ 2) ^ mZ)
            * ‖F (t, (q, η))‖ₑ ^ (2 : ℝ)) := by
  unfold gSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun η => ?_
  rw [sliceL2q_rpow_two, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  ring

lemma lintegral_ioi_qCell {c : ℝ} (H : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, H p
      = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2), H (t, (q, η)) := by
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hH.aemeasurable]
  refine lintegral_congr fun t => ?_
  exact lintegral_qCell c (hH.comp (measurable_const.prodMk measurable_id))

lemma lintegral_z1_eq_gSq {c : ℝ} (hc : 0 < c) (mZ : ℝ) {F : Chart → Ten3}
    (hF : Measurable F) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * gSq c mZ F t
      = ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
  have hW : Measurable fun p : Chart =>
      ENNReal.ofReal ((1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  have hFm : Measurable fun p : Chart => ‖F p‖ₑ ^ (2 : ℝ) := hF.enorm.pow_const (2 : ℝ)
  have hHf : Measurable fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ))
      * (ENNReal.ofReal ((1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ) * ‖F p‖ₑ ^ (2 : ℝ)) := by
    apply Measurable.mul
    · apply ENNReal.measurable_ofReal.comp
      fun_prop
    · exact hW.mul hFm
  have hdens : Measurable fun p : Chart => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) :=
    ENNReal.measurable_ofReal.comp (by unfold UnforcedLeray.Short.IIIa.transWeight; fun_prop)
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * gSq c mZ F t
      = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ η, ∫⁻ q in Ico (-c / 2) (c / 2),
          (fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ))
            * (ENNReal.ofReal ((1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ)
              * ‖F p‖ₑ ^ (2 : ℝ))) (t, (q, η)) :=
        lintegral_congr fun t => gSq_identity hc mZ t F
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ))
            * (ENNReal.ofReal ((1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ)
              * ‖F p‖ₑ ^ (2 : ℝ)) :=
        (lintegral_ioi_qCell _ hHf).symm
    _ = ∫⁻ p, (ENNReal.ofReal ((1 + (p.2.2 / Real.sqrt (1 + p.1)) ^ 2) ^ mZ)
            * ‖F p‖ₑ ^ (2 : ℝ)) ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)) :=
        (lintegral_ageμ hc (-1 / 2) (hW.mul hFm)).symm
    _ = ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
        unfold z1Measure
        rw [lintegral_withDensity_eq_lintegral_mul _ hdens hFm]
        refine lintegral_congr fun p => ?_
        simp only [Pi.mul_apply]
        rw [← transWeight_sq_eq mZ p.1 p.2.1 p.2.2]

/-! ## 5. The `t`-integral of the tail -/

lemma lintegral_tail_bound {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-5 / 2 : ℝ) * Real.sqrt (1 + t))
      ≤ ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2)) := by
  have hpt : ∀ t ∈ Ioi a, ENNReal.ofReal (t ^ (-5 / 2 : ℝ) * Real.sqrt (1 + t))
      ≤ ENNReal.ofReal (t ^ (-2 : ℝ)) + ENNReal.ofReal (t ^ (-5 / 2 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht
    have hsq : Real.sqrt (1 + t) ≤ t ^ (1 / 2 : ℝ) + 1 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]
    have hmul : t ^ (-5 / 2 : ℝ) * Real.sqrt (1 + t) ≤ t ^ (-2 : ℝ) + t ^ (-5 / 2 : ℝ) := by
      calc t ^ (-5 / 2 : ℝ) * Real.sqrt (1 + t) ≤ t ^ (-5 / 2 : ℝ) * (t ^ (1 / 2 : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg ht0.le _)
        _ = t ^ (-2 : ℝ) + t ^ (-5 / 2 : ℝ) := by
            rw [mul_add, mul_one, ← Real.rpow_add ht0]
            norm_num
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _)]
    exact ENNReal.ofReal_le_ofReal hmul
  have hint1 : ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-2 : ℝ)) = ENNReal.ofReal (a⁻¹) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        Real.rpow_nonneg (lt_trans ha ht).le _)]
    congr 1
    rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
    norm_num [Real.rpow_neg_one]
  have hint2 : ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-5 / 2 : ℝ))
      = ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        Real.rpow_nonneg (lt_trans ha ht).le _)]
    congr 1
    rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
    norm_num
  have hm2 : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hsplit : ∫⁻ t in Ioi a, (ENNReal.ofReal (t ^ (-2 : ℝ)) + ENNReal.ofReal (t ^ (-5 / 2 : ℝ)))
      = (∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-2 : ℝ)))
          + ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-5 / 2 : ℝ)) :=
    lintegral_add_left hm2 (fun t => ENNReal.ofReal (t ^ (-5 / 2 : ℝ)))
  calc ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-5 / 2 : ℝ) * Real.sqrt (1 + t))
      ≤ ∫⁻ t in Ioi a, (ENNReal.ofReal (t ^ (-2 : ℝ)) + ENNReal.ofReal (t ^ (-5 / 2 : ℝ))) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => hpt t ht
    _ = (∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-2 : ℝ)))
          + ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-5 / 2 : ℝ)) := hsplit
    _ = ENNReal.ofReal a⁻¹ + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2)) := by
        rw [hint1, hint2]

lemma sqrt_tail_le {a : ℝ} (ha : 0 < a) :
    (ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)) := by
  have hp0 : 0 < a ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos ha _
  have hq0 : 0 < a ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have hp2 : (a ^ (-3 / 4 : ℝ)) ^ 2 = a ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num
  have hq2 : (a ^ (-1 / 2 : ℝ)) ^ 2 = a⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num [Real.rpow_neg_one]
  have hB : -a ^ (-3 / 2 : ℝ) / (-3 / 2) = 2 / 3 * (a ^ (-3 / 4 : ℝ)) ^ 2 := by
    rw [hp2]
    ring
  have hBnn : 0 ≤ -a ^ (-3 / 2 : ℝ) / (-3 / 2) := by
    rw [hB]
    positivity
  rw [← hq2, ← ENNReal.ofReal_add (by positivity) hBnn, hB]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_pos hp0 hq0, sq_nonneg (a ^ (-3 / 4 : ℝ)), sq_nonneg (a ^ (-1 / 2 : ℝ))]

lemma r_sq_identity {t : ℝ} (ht : 0 < t) :
    (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t))) ^ (2 : ℝ)
      = t ^ (-5 / 2 : ℝ) * Real.sqrt (1 + t) := by
  have h1 : (t ^ (-5 / 4 : ℝ)) ^ (2 : ℝ) = t ^ (-5 / 2 : ℝ) := by
    rw [← Real.rpow_mul ht.le]
    norm_num
  have h2 : (Real.sqrt (Real.sqrt (1 + t))) ^ (2 : ℝ) = Real.sqrt (1 + t) := by
    rw [Real.rpow_two, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) (Real.sqrt_nonneg _), h1, h2]

lemma rpow_half_eq_ofReal {I : ℝ≥0∞} (hI : I ≠ ⊤) :
    I ^ (1 / 2 : ℝ) = ENNReal.ofReal (I.toReal ^ (1 / 2 : ℝ)) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hI]
  rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]

/-! ## 6. The pointwise and `t`-Cauchy-Schwarz bounds -/

/-- Pointwise bound at output age `t > 0`: transverse Cauchy-Schwarz with the exponents
`t^{-3/2} = t^{-5/4} · t^{-1/4}`. -/
lemma thin_pointwise {c mZ : ℝ} (hm : 1 / 2 < mZ) {F : Chart → Ten3} (hF : Measurable F)
    {t : ℝ} (ht0 : 0 < t) :
    ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c F t η
      ≤ (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t)))
          * (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ))) := by
  have hk : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.2 (by linarith)
  have hu : Measurable fun η : ℝ => sliceL2q c F t η := measurable_sliceL2q_eta c hF t
  have hη : ∫⁻ η, sliceL2q c F t η ≤
      (ENNReal.ofReal (Real.sqrt (1 + t)) * ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ)))
          ^ (1 / 2 : ℝ) * gSq c mZ F t ^ (1 / 2 : ℝ) :=
    lintegral_eta_cs hk hm (fun η => sliceL2q c F t η) hu
  have hid : ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
      ((ENNReal.ofReal (Real.sqrt (1 + t)) * ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ)))
          ^ (1 / 2 : ℝ) * gSq c mZ F t ^ (1 / 2 : ℝ))
      = (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t)))
          * (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ))) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow]
    have e1 : t ^ (-3 / 2 : ℝ) = t ^ (-5 / 4 : ℝ) * t ^ (-1 / 4 : ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    rw [e1, ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le (-5 / 4)),
      ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le (-5 / 4))]
    ring
  calc ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * ∫⁻ η, sliceL2q c F t η
      ≤ ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
          ((ENNReal.ofReal (Real.sqrt (1 + t)) * ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ)))
            ^ (1 / 2 : ℝ) * gSq c mZ F t ^ (1 / 2 : ℝ)) :=
        mul_le_mul_right hη _
    _ = _ := hid

/-- The `t`-Cauchy-Schwarz bound on the tail `t > a`, by `(Q)^{1/2} ‖F‖_{Z_1}`. -/
lemma thin_tail {c mZ : ℝ} {F : Chart → Ten3} (hc : 0 < c) (hF : Measurable F) {a : ℝ}
    (ha : 0 < a) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t)))
        * (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ))
      ≤ (ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ)
        * UnforcedLeray.Short.PartIIIb.Concrete.z1Norm c mZ F := by
  have hr_meas : Measurable fun t : ℝ =>
      ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hg_meas : Measurable fun t : ℝ =>
      ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul ((measurable_gSq c mZ hF).pow_const _)
  have step3 : ∫⁻ t in Ioi a,
      ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t)))
        * (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ))
      ≤ (∫⁻ t in Ioi a,
            ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t))) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ)
        * (∫⁻ t in Ioi a,
            (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ)) ^ (2 : ℝ))
          ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two
      hr_meas.aemeasurable hg_meas.aemeasurable
  have hf2 : ∫⁻ t in Ioi a,
      ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t))) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2)) := by
    refine le_trans (le_of_eq ?_) (lintegral_tail_bound ha)
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans ha ht
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.sqrt_nonneg _)) (by norm_num),
      r_sq_identity ht0]
  have hg2 : ∫⁻ t in Ioi a,
      (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
        ≤ ∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) := by
    rw [← lintegral_z1_eq_gSq hc mZ hF]
    refine le_trans (le_of_eq ?_) (lintegral_mono_set (Ioi_subset_Ioi ha.le))
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans ha ht
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ofReal_rpow_two_eq ht0.le (by ring : 2 * (-1 / 4 : ℝ) = -1 / 2), sq_rpow_half]
  calc _ ≤ _ := step3
    _ ≤ (ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ)
          * (∫⁻ p, ‖F p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hf2 (by norm_num))
          (ENNReal.rpow_le_rpow hg2 (by norm_num))
    _ = _ := rfl

/-! ## 7. The `ThinMassBoundSlice` -/

set_option maxHeartbeats 1000000 in
/-- **Thin mass bound** (5569-5584). -/
theorem thinMassBoundSlice (mZ : ℝ) : ThinMassBoundSlice mZ := by
  unfold ThinMassBoundSlice
  intro hm
  have hm' : 1 / 2 < mZ := by linarith
  have hI0 : (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ≠ ⊤ :=
    (lintegral_I_lt_top hm').ne
  refine ⟨(∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))).toReal ^ (1 / 2 : ℝ),
    fun c hc a ha F hF => ?_⟩
  have hJne : (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hI0
  have step2 : thinMass c F a ≤
      (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ) * ∫⁻ t in Ioi a,
        ENNReal.ofReal (t ^ (-5 / 4 : ℝ) * Real.sqrt (Real.sqrt (1 + t)))
          * (ENNReal.ofReal (t ^ (-1 / 4 : ℝ)) * gSq c mZ F t ^ (1 / 2 : ℝ)) := by
    unfold thinMass
    rw [← lintegral_const_mul' _ _ hJne]
    exact setLIntegral_mono' measurableSet_Ioi fun t ht =>
      thin_pointwise hm' hF (lt_trans ha ht)
  have hJQ : (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ)
      * (ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))).toReal ^ (1 / 2 : ℝ)
          * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) := by
    rw [rpow_half_eq_ofReal hI0]
    calc ENNReal.ofReal ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))).toReal ^ (1 / 2 : ℝ))
          * (ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))).toReal ^ (1 / 2 : ℝ))
          * ENNReal.ofReal (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)) :=
          mul_le_mul_right (sqrt_tail_le ha) _
      _ = ENNReal.ofReal ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))).toReal ^ (1 / 2 : ℝ)
          * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _)).symm
  calc thinMass c F a
      ≤ (∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ) *
          ((ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ)
            * UnforcedLeray.Short.PartIIIb.Concrete.z1Norm c mZ F) :=
        le_trans step2 (mul_le_mul_right (thin_tail hc hF ha) _)
    _ = ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))) ^ (1 / 2 : ℝ)
          * (ENNReal.ofReal (a⁻¹) + ENNReal.ofReal (-a ^ (-3 / 2 : ℝ) / (-3 / 2))) ^ (1 / 2 : ℝ))
            * UnforcedLeray.Short.PartIIIb.Concrete.z1Norm c mZ F := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal ((∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ (-mZ))).toReal ^ (1 / 2 : ℝ)
          * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)))
          * UnforcedLeray.Short.PartIIIb.Concrete.z1Norm c mZ F :=
        mul_le_mul_left hJQ _

end UnforcedLeray.Short.PartIIIb.Concrete
