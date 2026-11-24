import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Tasks.MinkowskiLintegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Part II-b, task `PartII-b:T04`: the singular Hardy estimate

Source of record: `the November 2 reference manuscript`, lines 2240-2257 (the
`align` labelled `short-bg:hardy`, third line: the factor `(1-u)^{-1/2} u^{-21/22}`).

Target: `hardySingular_proof : HardySingular` (statement in `StatementsMixed.lean`, not changed here).

Proof: on `(0, T]`, `∫₀^s (s-t)^{-1/2} g(t) dt = s^{1/2} ∫₀¹ (1-u)^{-1/2} g(su) du`. Minkowski's
integral inequality (`minkowski_lintegral_rpow`, T02) in the variables `(s, u)` bounds the
`L^p(s^{13/8} ds)` norm by `∫₀¹ (1-u)^{-1/2} ‖s^{1/2} g(su)‖ du`. The scaling
`∫_{(0,T)} g(su)^p s^{13/8} ds ≤ u^{-21/8} ∫_{(0,T)} g^p s^{13/8} ds` gives the factor `u^{-21/22}`
after the `1/p = 4/11` power. The constant is `C = ∫₀¹ (1-u)^{-1/2} u^{-21/22} du + 1`, which is
finite by a pointwise majorant split at `u = 1/2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Integrals over `(0, T]` against the weight `s ^ b` (the measure `sMeas b`). -/
lemma hardySing_sMeas_Ioc (b T : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s in Ioc 0 T, F s ∂sMeas b = ∫⁻ s in Ioc 0 T, F s * ENNReal.ofReal (s ^ b) := by
  have hφ : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ b)) := by fun_prop
  have hset : Ioc (0 : ℝ) T ∩ Ioi 0 = Ioc 0 T := Set.inter_eq_left.mpr (fun x hx => hx.1)
  unfold sMeas
  rw [restrict_withDensity measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hset,
    lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

lemma hardySing_sMeas_sFinite (b : ℝ) : SFinite (sMeas b) := by
  unfold sMeas
  infer_instance

/-- The integrand `(s, u) ↦ (1-u)^{-1/2} s^{1/2} g(su)` of the Minkowski step. -/
def hsF (g : ℝ → ℝ≥0∞) (s u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * g (s * u))

/-- The fibre constant `A_u = (1-u)^{-1/2} · √T · u^{-21/22}`. -/
def hsA (T u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) *
    (ENNReal.ofReal (Real.sqrt T) * ENNReal.ofReal (u ^ (-21 / 22 : ℝ)))

/-- The constant `∫₀¹ (1-u)^{-1/2} u^{-21/22} du`. -/
def hsC0 : ℝ≥0∞ :=
  ∫⁻ u in Ioc 0 1, ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (u ^ (-21 / 22 : ℝ))

/-- Inner scaling: `∫₀^s (s-t)^{-1/2} g(t) dt = ∫₀¹ (1-u)^{-1/2} s^{1/2} g(su) du` for `s > 0`. -/
lemma hardySing_inner (s : ℝ) (hs : 0 < s) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * g t =
      ∫⁻ u in Ioc 0 1, hsF g s u := by
  have himg : (fun u : ℝ => s * u) '' Ioc 0 1 = Ioc 0 s := by
    rw [image_mul_left_Ioc hs, mul_zero, mul_one]
  have hderiv : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => s * u) s (Ioc 0 1) x := by
    intro x _
    have h : HasDerivAt (fun u : ℝ => s * u) s x := by
      simpa using (hasDerivAt_id x).const_mul s
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => s * u) (Ioc 0 1) :=
    (mul_right_injective₀ hs.ne').injOn
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  have h1u : (0 : ℝ) ≤ 1 - u := by linarith [hu.2]
  have hsplit : s - s * u = s * (1 - u) := by ring
  have hpow : s ^ (1 / 2 : ℝ) = s * s ^ (-1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hs, Real.rpow_one]
  have hmul : (s - s * u) ^ (-1 / 2 : ℝ) = s ^ (-1 / 2 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ) := by
    rw [hsplit, Real.mul_rpow hs.le h1u]
  have hkey : ENNReal.ofReal s * ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ))
      = ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul hs.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    congr 1
    rw [hpow]
    ring
  show ENNReal.ofReal |s| * (ENNReal.ofReal ((s - s * u) ^ (-1 / 2 : ℝ)) * g (s * u))
      = ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * g (s * u))
  rw [abs_of_pos hs, hmul]
  calc ENNReal.ofReal s * (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ)) * g (s * u))
      = (ENNReal.ofReal s * ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ))) *
          g (s * u) := by ring
    _ = (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ))) *
          g (s * u) := by rw [hkey]
    _ = ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) * g (s * u)) := by
          ring

/-- Scaling of the weighted `L^p` norm: `∫_{(0,T)} g(su)^p s^{13/8} ds ≤ u^{-21/8} ∫_{(0,T)} g^p s^{13/8}`. -/
lemma hardySing_scale (T u : ℝ) (hT : 0 < T) (hu0 : 0 < u) (hu1 : u ≤ 1) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ s in Ioc 0 T, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) ≤
      ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) *
        ∫⁻ v in Ioc 0 T, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) := by
  have himg : (fun s : ℝ => s * u) '' Ioc 0 T = Ioc 0 (T * u) := by
    rw [image_mul_right_Ioc _ _ hu0, zero_mul]
  have hderiv : ∀ x ∈ Ioc (0 : ℝ) T, HasDerivWithinAt (fun s : ℝ => s * u) u (Ioc 0 T) x := by
    intro x _
    have h : HasDerivAt (fun s : ℝ => s * u) u x := by
      simpa using (hasDerivAt_id x).mul_const u
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => s * u) (Ioc 0 T) :=
    (mul_left_injective₀ hu0.ne').injOn
  have hpt : ∀ s ∈ Ioc (0 : ℝ) T,
      ENNReal.ofReal u * (g (s * u) ^ bgp * ENNReal.ofReal ((s * u) ^ (13 / 8 : ℝ))) =
        ENNReal.ofReal (u ^ (21 / 8 : ℝ)) *
          (g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by
    intro s hs
    have e1 : u ^ (21 / 8 : ℝ) = u * u ^ (13 / 8 : ℝ) := by
      rw [show (21 / 8 : ℝ) = 1 + 13 / 8 by norm_num, Real.rpow_add hu0, Real.rpow_one]
    rw [Real.mul_rpow hs.1.le hu0.le, ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _), e1,
      ENNReal.ofReal_mul hu0.le]
    ring
  have hgu : Measurable (fun s : ℝ => g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by
    fun_prop
  have hCOV : ∫⁻ v in Ioc 0 (T * u), g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) =
      ENNReal.ofReal (u ^ (21 / 8 : ℝ)) *
        ∫⁻ s in Ioc 0 T, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) := by
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj,
      ← lintegral_const_mul _ hgu]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    show ENNReal.ofReal |u| * (g (s * u) ^ bgp * ENNReal.ofReal ((s * u) ^ (13 / 8 : ℝ))) =
      ENNReal.ofReal (u ^ (21 / 8 : ℝ)) * (g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)))
    rw [abs_of_pos hu0]
    exact hpt s hs
  have hmono : ∫⁻ v in Ioc 0 (T * u), g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) ≤
      ∫⁻ v in Ioc 0 T, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) :=
    lintegral_mono_set (Set.Ioc_subset_Ioc_right (mul_le_of_le_one_right hT.le hu1))
  have hcancel : ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) * ENNReal.ofReal (u ^ (21 / 8 : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _), ← Real.rpow_add hu0]
    norm_num
  calc ∫⁻ s in Ioc 0 T, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))
      = (ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) * ENNReal.ofReal (u ^ (21 / 8 : ℝ))) *
          ∫⁻ s in Ioc 0 T, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) := by
        rw [hcancel, one_mul]
    _ = ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) *
          (ENNReal.ofReal (u ^ (21 / 8 : ℝ)) *
            ∫⁻ s in Ioc 0 T, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by ring
    _ ≤ ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) *
          ∫⁻ v in Ioc 0 T, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        rw [← hCOV]
        exact hmono

/-- Pointwise real inequality: `(1-u)^{-1/2} u^{-21/22} ≤ K₁ u^{-21/22} + K₂ (1-u)^{-1/2}` on
`(0, 1]`, with `K₁ = (1/2)^{-1/2}` and `K₂ = (1/2)^{-21/22}`. -/
lemma hardySing_pt (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (1 - u) ^ (-1 / 2 : ℝ) * u ^ (-21 / 22 : ℝ) ≤
      (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * u ^ (-21 / 22 : ℝ) +
        (1 / 2 : ℝ) ^ (-21 / 22 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ) := by
  have ha0 : 0 ≤ u ^ (-21 / 22 : ℝ) := Real.rpow_nonneg hu0.le _
  have hb0 : 0 ≤ (1 - u) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hK1 : 0 ≤ (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hK2 : 0 ≤ (1 / 2 : ℝ) ^ (-21 / 22 : ℝ) := Real.rpow_nonneg (by norm_num) _
  rcases le_total u (1 / 2) with h | h
  · have hb : (1 - u) ^ (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hb ha0, mul_nonneg hK2 hb0]
  · have ha : u ^ (-21 / 22 : ℝ) ≤ (1 / 2 : ℝ) ^ (-21 / 22 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) h (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left ha hb0, mul_nonneg hK1 ha0]

/-- The constant `∫₀¹ (1-u)^{-1/2} u^{-21/22} du` is finite. -/
lemma hsC0_lt_top : hsC0 < ⊤ := by
  have ha : IntegrableOn (fun x : ℝ => x ^ (-21 / 22 : ℝ)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (r := -21 / 22) (by norm_num) :
      IntervalIntegrable (fun x : ℝ => x ^ (-21 / 22 : ℝ)) volume 0 1).1
  have hb : IntegrableOn (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) (Ioc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (r := -1 / 2) (by norm_num) :
      IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 1).comp_sub_left 1
    simpa using h.2
  have hint : Integrable (fun x : ℝ => (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) * x ^ (-21 / 22 : ℝ) +
      (1 / 2 : ℝ) ^ (-21 / 22 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ)) (volume.restrict (Ioc 0 1)) :=
    (Integrable.const_mul ha _).add (Integrable.const_mul hb _)
  refine lt_of_le_of_lt ?_ hint.lintegral_lt_top
  unfold hsC0
  apply setLIntegral_mono' measurableSet_Ioc
  intro u hu
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (show (0 : ℝ) ≤ 1 - u by linarith [hu.2]) _)]
  exact ENNReal.ofReal_le_ofReal (hardySing_pt u hu.1 hu.2)

lemma hardySing_rpow_inv (A : ℝ≥0∞) : (A ^ bgp) ^ (1 / bgp) = A := by
  have hb : bgp ≠ 0 := by norm_num [bgp]
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hb, ENNReal.rpow_one]

lemma hardySing_hsA_pow (T u : ℝ) (hu0 : 0 < u) :
    hsA T u ^ bgp = (ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
        ENNReal.ofReal (Real.sqrt T) ^ bgp) * ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) := by
  have hp0 : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  unfold hsA
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hu0.le _) hp0, ← Real.rpow_mul hu0.le,
    show (-21 / 22 : ℝ) * bgp = -21 / 8 by norm_num [bgp]]
  ring

lemma hardySing_hsA_integral (T : ℝ) :
    ∫⁻ b in Ioc 0 1, hsA T b = ENNReal.ofReal (Real.sqrt T) * hsC0 := by
  have h : ∀ b : ℝ, hsA T b = ENNReal.ofReal (Real.sqrt T) *
      (ENNReal.ofReal ((1 - b) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (b ^ (-21 / 22 : ℝ))) := by
    intro b
    unfold hsA
    ring
  simp only [h]
  rw [lintegral_const_mul _ (by fun_prop : Measurable fun b : ℝ =>
    ENNReal.ofReal ((1 - b) ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (b ^ (-21 / 22 : ℝ))), hsC0]

/-- The fibre bound: `∫_{(0,T)} (hsF g s u)^p ds^{13/8} ≤ A_u^p ∫_{(0,T)} g^p ds^{13/8}`. -/
lemma hardySing_fiber (T : ℝ) (hT : 0 < T) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (u : ℝ)
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∫⁻ s in Ioc 0 T, hsF g s u ^ bgp ∂sMeas (13 / 8) ≤
      hsA T u ^ bgp * ∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8) := by
  have hp0 : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hFm : Measurable (fun s : ℝ => hsF g s u ^ bgp) := by
    unfold hsF
    fun_prop
  have hgm : Measurable (fun s : ℝ => g s ^ bgp) := by fun_prop
  rw [hardySing_sMeas_Ioc (13 / 8) T _ hFm, hardySing_sMeas_Ioc (13 / 8) T _ hgm]
  have hgu : Measurable (fun s : ℝ => g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by
    fun_prop
  have hpt : ∀ s ∈ Ioc (0 : ℝ) T,
      hsF g s u ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) ≤
        (ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp * ENNReal.ofReal (Real.sqrt T) ^ bgp) *
          (g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by
    intro s hs
    have hsq : s ^ (1 / 2 : ℝ) ≤ Real.sqrt T := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow hs.1.le hs.2 (by norm_num)
    have h2 : ENNReal.ofReal (s ^ (1 / 2 : ℝ)) ^ bgp ≤ ENNReal.ofReal (Real.sqrt T) ^ bgp :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsq) hp0
    have h1 : hsF g s u ^ bgp = ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
        (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) ^ bgp * g (s * u) ^ bgp) := by
      unfold hsF
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0]
    rw [h1]
    have hA1 : ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
        (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) ^ bgp * g (s * u) ^ bgp) ≤
        ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
          (ENNReal.ofReal (Real.sqrt T) ^ bgp * g (s * u) ^ bgp) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 zero_le) zero_le
    have hA2 : ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
        (ENNReal.ofReal (s ^ (1 / 2 : ℝ)) ^ bgp * g (s * u) ^ bgp) *
          ENNReal.ofReal (s ^ (13 / 8 : ℝ)) ≤
        ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
          (ENNReal.ofReal (Real.sqrt T) ^ bgp * g (s * u) ^ bgp) *
          ENNReal.ofReal (s ^ (13 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_right hA1 zero_le
    exact hA2.trans_eq (by ring)
  have hmain : ∫⁻ s in Ioc 0 T, hsF g s u ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) ≤
      ∫⁻ s in Ioc 0 T, (ENNReal.ofReal ((1 - u) ^ (-1 / 2 : ℝ)) ^ bgp *
          ENNReal.ofReal (Real.sqrt T) ^ bgp) * (g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) :=
    setLIntegral_mono' measurableSet_Ioc hpt
  rw [lintegral_const_mul _ hgu] at hmain
  have hsc := hardySing_scale T u hT hu0 hu1 g hg
  refine le_trans hmain ?_
  rw [hardySing_hsA_pow T u hu0]
  exact le_trans (mul_le_mul_of_nonneg_left hsc zero_le) (le_of_eq (by ring))

theorem hardySingular_proof : UnforcedLeray.Short.IIb.HardySingular := by
  have hfin : hsC0 < ⊤ := hsC0_lt_top
  unfold HardySingular
  refine ⟨hsC0.toReal + 1, by linarith [ENNReal.toReal_nonneg (a := hsC0)], ?_⟩
  intro T hT g hg
  have hp1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have hp0 : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hinv : (4 / 11 : ℝ) = 1 / bgp := by norm_num [bgp]
  have := hardySing_sMeas_sFinite (13 / 8)
  have hsFm : Measurable (Function.uncurry (hsF g)) := by
    have h : Measurable (fun q : ℝ × ℝ => hsF g q.1 q.2) := by
      unfold hsF
      fun_prop
    exact h
  have hmink := minkowski_lintegral_rpow (μ := (sMeas (13 / 8)).restrict (Ioc 0 T))
    (ν := volume.restrict (Ioc 0 1)) (p := bgp) hp1 (f := hsF g) hsFm
  have hL : ∫⁻ s in Ioc 0 T,
        (∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * g t) ^ bgp ∂sMeas (13 / 8)
      = ∫⁻ a, (∫⁻ b, hsF g a b ∂(volume.restrict (Ioc 0 1))) ^ bgp
          ∂((sMeas (13 / 8)).restrict (Ioc 0 T)) := by
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    exact congrArg (fun x => x ^ bgp) (hardySing_inner s hs.1 g)
  have hfib : ∀ u ∈ Ioc (0 : ℝ) 1,
      (∫⁻ a, hsF g a u ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T))) ^ (1 / bgp) ≤
        hsA T u * (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
    intro u hu
    have h1 := hardySing_fiber T hT g hg u hu.1 hu.2
    calc (∫⁻ a, hsF g a u ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T))) ^ (1 / bgp)
        ≤ (hsA T u ^ bgp * ∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
          ENNReal.rpow_le_rpow h1 (one_div_nonneg.mpr hp0)
      _ = hsA T u * (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0), hardySing_rpow_inv]
  have hR : ∫⁻ b, (∫⁻ a, hsF g a b ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T)))
        ^ (1 / bgp) ∂(volume.restrict (Ioc 0 1))
      ≤ (ENNReal.ofReal (Real.sqrt T) * hsC0) *
          (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
    have hsAm : Measurable fun b : ℝ => hsA T b := by
      unfold hsA
      fun_prop
    calc ∫⁻ b, (∫⁻ a, hsF g a b ^ bgp ∂((sMeas (13 / 8)).restrict (Ioc 0 T)))
            ^ (1 / bgp) ∂(volume.restrict (Ioc 0 1))
        ≤ ∫⁻ b in Ioc 0 1, hsA T b * (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
          setLIntegral_mono' measurableSet_Ioc (fun u hu => hfib u hu)
      _ = (∫⁻ b in Ioc 0 1, hsA T b) * (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
          lintegral_mul_const _ hsAm
      _ = (ENNReal.ofReal (Real.sqrt T) * hsC0) *
          (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
          rw [hardySing_hsA_integral]
  have hC : ENNReal.ofReal (Real.sqrt T) * hsC0 ≤
      ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt T) := by
    have hnn : (0 : ℝ) ≤ hsC0.toReal + 1 := by linarith [ENNReal.toReal_nonneg (a := hsC0)]
    have hle : hsC0 ≤ ENNReal.ofReal (hsC0.toReal + 1) := by
      calc hsC0 = ENNReal.ofReal hsC0.toReal := (ENNReal.ofReal_toReal hfin.ne).symm
        _ ≤ ENNReal.ofReal (hsC0.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
    calc ENNReal.ofReal (Real.sqrt T) * hsC0
        ≤ ENNReal.ofReal (Real.sqrt T) * ENNReal.ofReal (hsC0.toReal + 1) :=
          mul_le_mul_of_nonneg_left hle zero_le
      _ = ENNReal.ofReal ((hsC0.toReal + 1) * Real.sqrt T) := by
          rw [ENNReal.ofReal_mul hnn]
          ring
  rw [hinv, hL]
  exact le_trans hmink (le_trans hR (mul_le_mul_of_nonneg_right hC zero_le))

end UnforcedLeray.Short.IIb
