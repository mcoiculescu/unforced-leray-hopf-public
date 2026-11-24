import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Tasks.MinkowskiLintegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Part II-b, task `PartII-b:T03`: the mean Hardy estimate

Source of record: `the November 2 reference manuscript`, lines 2245-2246 and
2254-2257 (the `align` labelled `short-bg:hardy`, second line; constant `22 = ∫₀¹ u^{-21/22} du`).

Target: `hardyMean_proof : HardyMean` (statement in `StatementsMixed.lean`, not changed here).

Proof: for every real `s`, `∫₀^s g = ∫₀¹ s g(su) du` (change of variables on `(0, s]`, and both
sides vanish for `s ≤ 0`). Minkowski's integral inequality (`minkowski_lintegral_rpow`, T02) in the
variables `(s, u)` with integrand `s g(su)` bounds the `L^p(s^{-9/8} ds)` norm by
`∫₀¹ ‖s g(su)‖_{L^p(s^{-9/8} ds)} du`. The scaling identity
`∫ g(su)^p s^{13/8} ds = u^{-21/8} ∫ g^p s^{13/8} ds` on `(0, ∞)` gives the factor `u^{-21/22}`
after the `1/p = 4/11` power, and `∫₀¹ u^{-21/22} du = 22`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

lemma hardyMean_sFinite (b : ℝ) : SFinite (sMeas b) := by
  unfold sMeas
  infer_instance

/-- Integrals against `sMeas b` over the whole line are integrals over `(0, ∞)`. -/
lemma hardyMean_sMeas_full (b : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s, F s ∂sMeas b = ∫⁻ s in Ioi 0, F s * ENNReal.ofReal (s ^ b) := by
  have hφ : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ b)) := by fun_prop
  unfold sMeas
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

/-- Change of variables on `(0, s]`: `∫₀^s g = ∫₀¹ s g(su) du` for every real `s`. -/
lemma hardyMean_inner (s : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioc 0 s, g t = ∫⁻ u in Ioc 0 1, ENNReal.ofReal s * g (s * u) := by
  rcases le_or_gt s 0 with hs | hs
  · have hI : Ioc (0 : ℝ) s = ∅ := Set.Ioc_eq_empty (not_lt.mpr hs)
    simp [hI, ENNReal.ofReal_eq_zero.mpr hs]
  · have himg : (fun u : ℝ => s * u) '' Ioc 0 1 = Ioc 0 s := by
      rw [image_mul_left_Ioc hs, mul_zero, mul_one]
    have hderiv : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt (fun u : ℝ => s * u) s (Ioc 0 1) x := by
      intro x _
      have h : HasDerivAt (fun u : ℝ => s * u) s x := by
        simpa using (hasDerivAt_id x).const_mul s
      exact h.hasDerivWithinAt
    have hinj : InjOn (fun u : ℝ => s * u) (Ioc 0 1) :=
      (mul_right_injective₀ hs.ne').injOn
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    show ENNReal.ofReal |s| * g (s * u) = ENNReal.ofReal s * g (s * u)
    rw [abs_of_pos hs]

/-- Scaling identity on `(0, ∞)`: `∫ g(v)^p v^{13/8} dv = u^{21/8} ∫ g(su)^p s^{13/8} ds`. -/
lemma hardyMean_cov (u : ℝ) (hu0 : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v in Ioi 0, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) =
      ENNReal.ofReal (u ^ (21 / 8 : ℝ)) *
        ∫⁻ s in Ioi 0, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) := by
  have himg : (fun s : ℝ => s * u) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mul_pos (Set.mem_Ioi.mp hs) hu0
    · intro hx
      refine ⟨x / u, div_pos (Set.mem_Ioi.mp hx) hu0, ?_⟩
      show x / u * u = x
      field_simp [hu0.ne']
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ => s * u) u (Ioi 0) x := by
    intro x _
    have h : HasDerivAt (fun s : ℝ => s * u) u x := by
      simpa using (hasDerivAt_id x).mul_const u
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => s * u) (Ioi 0) :=
    (mul_left_injective₀ hu0.ne').injOn
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal u * (g (s * u) ^ bgp * ENNReal.ofReal ((s * u) ^ (13 / 8 : ℝ))) =
        ENNReal.ofReal (u ^ (21 / 8 : ℝ)) *
          (g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e1 : u ^ (21 / 8 : ℝ) = u * u ^ (13 / 8 : ℝ) := by
      rw [show (21 / 8 : ℝ) = 1 + 13 / 8 by norm_num, Real.rpow_add hu0, Real.rpow_one]
    rw [Real.mul_rpow hs0.le hu0.le, ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), e1,
      ENNReal.ofReal_mul hu0.le]
    ring
  have hgu : Measurable (fun s : ℝ => g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))) := by
    fun_prop
  have hCOV : ∫⁻ v in Ioi 0, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) =
      ∫⁻ v in (fun s : ℝ => s * u) '' Ioi 0, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) := by
    rw [himg]
  rw [hCOV, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj,
    ← lintegral_const_mul _ hgu]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  show ENNReal.ofReal |u| * (g (s * u) ^ bgp * ENNReal.ofReal ((s * u) ^ (13 / 8 : ℝ))) =
    ENNReal.ofReal (u ^ (21 / 8 : ℝ)) * (g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)))
  rw [abs_of_pos hu0]
  exact hpt s hs

/-- Scaled weighted norm: `∫_{(0,∞)} g(su)^p s^{13/8} ds = u^{-21/8} ∫_{(0,∞)} g^p s^{13/8}`. -/
lemma hardyMean_scale (u : ℝ) (hu0 : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ s in Ioi 0, g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ)) =
      ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) *
        ∫⁻ v in Ioi 0, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) := by
  have hc : ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) * ENNReal.ofReal (u ^ (21 / 8 : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _), ← Real.rpow_add hu0]
    norm_num
  rw [hardyMean_cov u hu0 g hg, ← mul_assoc, hc, one_mul]

/-- The moment identity: `∫ (s g(su))^p s^{-9/8} ds = u^{-21/8} ∫_{(0,∞)} g^p s^{13/8}`. -/
lemma hardyMean_moment (u : ℝ) (hu0 : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ s, (ENNReal.ofReal s * g (s * u)) ^ bgp ∂sMeas (-9 / 8) =
      ENNReal.ofReal (u ^ (-21 / 8 : ℝ)) *
        ∫⁻ v in Ioi 0, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) := by
  have hp0 : (0 : ℝ) ≤ bgp := by norm_num [bgp]
  have hFm : Measurable (fun s : ℝ => (ENNReal.ofReal s * g (s * u)) ^ bgp) := by
    fun_prop
  have hm1 : ∫⁻ s, (ENNReal.ofReal s * g (s * u)) ^ bgp ∂sMeas (-9 / 8) =
      ∫⁻ s in Ioi 0, (ENNReal.ofReal s * g (s * u)) ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) :=
    hardyMean_sMeas_full (-9 / 8) (fun s : ℝ => (ENNReal.ofReal s * g (s * u)) ^ bgp) hFm
  rw [hm1, ← hardyMean_scale u hu0 g hg]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hs0 : (0 : ℝ) < s := hs
  have hexp : s ^ bgp * s ^ (-9 / 8 : ℝ) = s ^ (13 / 8 : ℝ) := by
    rw [← Real.rpow_add hs0, show bgp + (-9 / 8 : ℝ) = 13 / 8 by norm_num [bgp]]
  show (ENNReal.ofReal s * g (s * u)) ^ bgp * ENNReal.ofReal (s ^ (-9 / 8 : ℝ)) =
    g (s * u) ^ bgp * ENNReal.ofReal (s ^ (13 / 8 : ℝ))
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.ofReal_rpow_of_nonneg hs0.le hp0,
    mul_right_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _), hexp]
  ring

/-- Fibre bound: the `(1/p)`-th root of the `u`-slice of the Minkowski integrand. -/
lemma hardyMean_fibre (u : ℝ) (hu0 : 0 < u) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ s, (ENNReal.ofReal s * g (s * u)) ^ bgp ∂sMeas (-9 / 8)) ^ (1 / bgp) =
      ENNReal.ofReal (u ^ (-21 / 22 : ℝ)) * (∫⁻ s, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
  have hp0 : (0 : ℝ) ≤ 1 / bgp := by norm_num [bgp]
  have hgm : Measurable (fun s : ℝ => g s ^ bgp) := by fun_prop
  have hI : ∫⁻ s, g s ^ bgp ∂sMeas (13 / 8) =
      ∫⁻ v in Ioi 0, g v ^ bgp * ENNReal.ofReal (v ^ (13 / 8 : ℝ)) :=
    hardyMean_sMeas_full (13 / 8) (fun s : ℝ => g s ^ bgp) hgm
  rw [hardyMean_moment u hu0 g hg, hI, ENNReal.mul_rpow_of_nonneg _ _ hp0,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hu0.le _) hp0, ← Real.rpow_mul hu0.le,
    show (-21 / 8 : ℝ) * (1 / bgp) = -21 / 22 by norm_num [bgp]]

/-- The constant: `∫₀¹ u^{-21/22} du = 22`, as a lower integral. -/
lemma hardyMean_integral_pow :
    ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (-21 / 22 : ℝ)) = 22 := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-21 / 22 : ℝ)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (r := -21 / 22) (by norm_num) :
      IntervalIntegrable (fun x : ℝ => x ^ (-21 / 22 : ℝ)) volume 0 1).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun x : ℝ => x ^ (-21 / 22 : ℝ) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx => Real.rpow_nonneg hx.1.le _
  have key := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [← key, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_rpow (r := -21 / 22) (Or.inl (by norm_num))]
  have h0 : (0 : ℝ) ^ ((-21 / 22 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
  rw [h0, Real.one_rpow]
  norm_num

theorem hardyMean_proof : UnforcedLeray.Short.IIb.HardyMean := by
  unfold HardyMean
  intro g hg
  have hp1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have hinv : (4 / 11 : ℝ) = 1 / bgp := by norm_num [bgp]
  haveI := hardyMean_sFinite (-9 / 8)
  have hsFm : Measurable (Function.uncurry (fun s u : ℝ => ENNReal.ofReal s * g (s * u))) := by
    have h : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * g (q.1 * q.2)) := by
      fun_prop
    exact h
  have hmink := minkowski_lintegral_rpow (μ := sMeas (-9 / 8))
    (ν := volume.restrict (Ioc (0 : ℝ) 1)) (p := bgp) hp1
    (f := fun s u : ℝ => ENNReal.ofReal s * g (s * u)) hsFm
  have hL : ∫⁻ s, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8) =
      ∫⁻ s, (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal s * g (s * u)) ^ bgp ∂sMeas (-9 / 8) :=
    lintegral_congr fun s => congrArg (fun x => x ^ bgp) (hardyMean_inner s g)
  have hmeas : Measurable (fun u : ℝ => ENNReal.ofReal (u ^ (-21 / 22 : ℝ))) := by
    fun_prop
  rw [hinv, hL]
  calc (∫⁻ s, (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal s * g (s * u)) ^ bgp ∂sMeas (-9 / 8)) ^ (1 / bgp)
      ≤ ∫⁻ u in Ioc (0 : ℝ) 1,
          (∫⁻ s, (ENNReal.ofReal s * g (s * u)) ^ bgp ∂sMeas (-9 / 8)) ^ (1 / bgp) := hmink
    _ = ∫⁻ u in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (u ^ (-21 / 22 : ℝ)) * (∫⁻ s, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
        setLIntegral_congr_fun measurableSet_Ioc (fun u hu => hardyMean_fibre u hu.1 g hg)
    _ = (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (-21 / 22 : ℝ))) *
          (∫⁻ s, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) :=
        lintegral_mul_const _ hmeas
    _ = 22 * (∫⁻ s, g s ^ bgp ∂sMeas (13 / 8)) ^ (1 / bgp) := by
        rw [hardyMean_integral_pow]

end UnforcedLeray.Short.IIb
