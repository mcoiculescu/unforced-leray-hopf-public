import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.T20_CTEmbeddings
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.TestedImpulse
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.CompactComparison
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Part III-a, task `PartIII-a:T22/5` — Mellin output (`eq:ct-mellin`, SP 3300-3343)

Proves `CTMellin` (`UnforcedLeray.Short.IIIa.ctMellin`):
1. Exact clock substitution `s = clockAge ν θ = (1 - ν θ)/(ν² θ)` mapping `(0, θ_o(ν))` onto
   `(onsetAge ν, ∞)` (`θ_o(ν) = (ν + √ν)⁻¹`), factoring out the prefactor
   `-(π N_ν / (4 c)) ν^{3 + 2μ}` via `quadQ c (w s) = N_ν quadQ (d(θ)) (Z θ)`.
2. Continuity of `θ ↦ quadQ (d(θ)) (Z θ)` from `IsLinearisedFlow.strongCont` and `CTE.quadQ_bound`,
   together with symmetrized homogeneous flow restart at `s_r = clockAge ν r` for `ctTestedImpulse`
   at exponent `p₀ = 3/2`.
3. Three-regime split `(0, r) ∪ (r, b) ∪ (b, θ_o(ν))` against `mellinJc P μ`:
   - `(0, r)`: `ctTestedImpulse` + `ctCompactComparison` at `θ = r` + uniform canonical branch bound;
   - `(r, b)`: `ctCompactComparison` on `[r, b]`;
   - `(b, θ_o(ν))`: `ctLongComparison` + exponential decay `e^{-Re λ θ}`;
   - weight `(1 - ν θ)^{-μ - 5/2} - 1 = O_K(√ν)` uniformly on `(0, θ_o(ν)) × K` and integrable
     canonical tails on `(0, r)` and `(θ_o(ν), ∞)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace MellinAux

/-! ## Section 1: Onset clock, Jacobian substitution, and complex power estimates -/

private def thetaOnset (ν : ℝ) : ℝ := clockTheta ν (onsetAge ν)

private def mellinPref (P : PlanarData) (ν : ℝ) (μ : ℂ) : ℂ :=
  -((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν / (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
    (ν : ℂ) ^ (3 + 2 * μ)

private def fZ (P : PlanarData) (ν : ℝ) (μ : ℂ) (w : ℝ → ℝ × ℝ → ℂ) (θ : ℝ) : ℂ :=
  (θ : ℂ) ^ (μ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) *
    quadQ (dOfTheta ν θ) (heatColumn P ν w θ)

private def fCanWt (P : PlanarData) (ν : ℝ) (μ : ℂ) (θ : ℝ) : ℂ :=
  (θ : ℂ) ^ (μ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) *
    quadrupole (P.canonical θ)

private def fCan (P : PlanarData) (μ : ℂ) (θ : ℝ) : ℂ :=
  (θ : ℂ) ^ (μ + 1 / 2) * quadrupole (P.canonical θ)

private lemma onsetAge_pos {ν : ℝ} (hν : 0 < ν) : 0 < onsetAge ν :=
  Real.rpow_pos_of_pos hν _

private lemma clockA_onsetAge_pos {ν : ℝ} (hν : 0 < ν) : 0 < clockA ν (onsetAge ν) := by
  unfold clockA
  have := onsetAge_pos hν
  positivity

private lemma thetaOnset_pos {ν : ℝ} (hν : 0 < ν) : 0 < thetaOnset ν := by
  unfold thetaOnset clockTheta
  have := clockA_onsetAge_pos hν
  positivity

private lemma clockAge_thetaOnset {ν : ℝ} (hν : 0 < ν) :
    clockAge ν (thetaOnset ν) = onsetAge ν :=
  T22Sub.clockAge_clockTheta hν (clockA_onsetAge_pos hν)

private lemma thetaOnset_eq {ν : ℝ} (hν : 0 < ν) :
    thetaOnset ν = (ν + Real.sqrt ν)⁻¹ := by
  unfold thetaOnset clockTheta clockA onsetAge
  congr 1
  have h1 : ν * (1 + ν * ν ^ (-3 / 2 : ℝ)) = ν + ν ^ (1 : ℝ) * ν ^ (-1 / 2 : ℝ) := by
    have hpow : ν ^ (1 : ℝ) * ν ^ (-3 / 2 : ℝ) = ν ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hν]
      norm_num
    rw [Real.rpow_one] at hpow
    rw [mul_add, mul_one, hpow, Real.rpow_one]
  have h2 : ν ^ (1 : ℝ) * ν ^ (-1 / 2 : ℝ) = Real.sqrt ν := by
    rw [← Real.rpow_add hν, Real.sqrt_eq_rpow]
    norm_num
  rw [h1, h2]

private lemma nu_mul_thetaOnset_lt_sqrt {ν : ℝ} (hν : 0 < ν) :
    ν * thetaOnset ν < Real.sqrt ν := by
  rw [thetaOnset_eq hν]
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hden : 0 < ν + Real.sqrt ν := by positivity
  rw [← div_eq_mul_inv, div_lt_iff₀ hden]
  have hsq2 : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt hν.le
  nlinarith

private lemma thetaOnset_lt_inv {ν : ℝ} (hν : 0 < ν) :
    thetaOnset ν < ν⁻¹ := by
  rw [thetaOnset_eq hν]
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  exact inv_strictAnti₀ hν (by linarith)

private lemma lt_thetaOnset_of_sum_lt_inv {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (hsum : ν + Real.sqrt ν < B⁻¹) :
    B < thetaOnset ν := by
  rw [thetaOnset_eq hν]
  have hpos : 0 < ν + Real.sqrt ν := by
    have := Real.sqrt_pos.2 hν
    positivity
  exact (lt_inv_comm₀ hB hpos).2 hsum

private lemma clockAge_eq_sub_inv {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    clockAge ν θ = (ν ^ 2 * θ)⁻¹ - ν⁻¹ := by
  unfold clockAge
  have hν_ne : ν ≠ 0 := hν.ne'
  have hθ_ne : θ ≠ 0 := hθ.ne'
  field_simp

private lemma clockAge_strictAnti {ν θ₁ θ₂ : ℝ} (hν : 0 < ν) (hθ₁ : 0 < θ₁) (h12 : θ₁ < θ₂) :
    clockAge ν θ₂ < clockAge ν θ₁ := by
  have hθ₂ : 0 < θ₂ := hθ₁.trans h12
  rw [clockAge_eq_sub_inv hν hθ₂, clockAge_eq_sub_inv hν hθ₁]
  have hlt : ν ^ 2 * θ₁ < ν ^ 2 * θ₂ := mul_lt_mul_of_pos_left h12 (pow_pos hν 2)
  have hinv : (ν ^ 2 * θ₂)⁻¹ < (ν ^ 2 * θ₁)⁻¹ := inv_strictAnti₀ (by positivity) hlt
  linarith

private lemma clockAge_anti {ν θ₁ θ₂ : ℝ} (hν : 0 < ν) (hθ₁ : 0 < θ₁) (h12 : θ₁ ≤ θ₂) :
    clockAge ν θ₂ ≤ clockAge ν θ₁ := by
  rcases h12.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (clockAge_strictAnti hν hθ₁ hlt).le

private lemma hasDerivAt_clockAge {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    HasDerivAt (clockAge ν) (-(ν ^ 2 * θ ^ 2)⁻¹) θ := by
  have hcongr : clockAge ν =ᶠ[𝓝 θ] fun u => (ν ^ 2)⁻¹ * u⁻¹ - ν⁻¹ := by
    filter_upwards [Ioi_mem_nhds hθ] with u hu
    rw [clockAge_eq_sub_inv hν hu, mul_inv]
  have hd : HasDerivAt (fun u => (ν ^ 2)⁻¹ * u⁻¹ - ν⁻¹)
      ((ν ^ 2)⁻¹ * (-(θ ^ 2)⁻¹)) θ :=
    ((hasDerivAt_inv hθ.ne').const_mul (ν ^ 2)⁻¹).sub_const ν⁻¹
  refine (hd.congr_of_eventuallyEq hcongr).congr_deriv ?_
  have hν_ne : ν ≠ 0 := hν.ne'
  have hθ_ne : θ ≠ 0 := hθ.ne'
  field_simp

private lemma injOn_clockAge_Ioi {ν : ℝ} (hν : 0 < ν) :
    InjOn (clockAge ν) (Ioi 0) := by
  intro θ₁ hθ₁ θ₂ hθ₂ heq
  have h1 := T22Sub.clockTheta_clockAge hν hθ₁
  have h2 := T22Sub.clockTheta_clockAge hν hθ₂
  rw [heq] at h1
  exact h1.symm.trans h2

private lemma image_clockAge_Ioo_thetaOnset {ν : ℝ} (hν : 0 < ν) :
    clockAge ν '' Ioo 0 (thetaOnset ν) = Ioi (onsetAge ν) := by
  ext s
  constructor
  · rintro ⟨θ, ⟨hθ0, hθT⟩, rfl⟩
    rw [mem_Ioi, ← clockAge_thetaOnset hν]
    exact clockAge_strictAnti hν hθ0 hθT
  · intro hs
    rw [mem_Ioi] at hs
    have hs0 : 0 < s := (onsetAge_pos hν).trans hs
    have ha : 0 < clockA ν s := by unfold clockA; positivity
    let θ := clockTheta ν s
    have hθ0 : 0 < θ := by unfold θ clockTheta; positivity
    have hage : clockAge ν θ = s := T22Sub.clockAge_clockTheta hν ha
    refine ⟨θ, ⟨hθ0, ?_⟩, hage⟩
    by_contra hge
    have hle : thetaOnset ν ≤ θ := le_of_not_gt hge
    have hanti := clockAge_anti hν (thetaOnset_pos hν) hle
    rw [hage, clockAge_thetaOnset hν] at hanti
    linarith

private lemma mellinPref_ne_zero (P : PlanarData) {ν : ℝ} (hν : 0 < ν) (μ : ℂ) :
    mellinPref P ν μ ≠ 0 := by
  unfold mellinPref
  have hpi : -((Real.pi : ℝ) : ℂ) ≠ 0 := neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hgf : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν
  have hc : 4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hν _).ne')
  have hpow : (ν : ℂ) ^ (3 + 2 * μ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (Complex.ofReal_ne_zero.2 hν.ne') h.1
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hpi hgf) hc) hpow

private lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le]

private lemma ofReal_rpow_eq_exp {x : ℝ} (hx : 0 < x) (r : ℝ) :
    ((x ^ r : ℝ) : ℂ) = Complex.exp ((Real.log x : ℂ) * (r : ℂ)) := by
  rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp, Complex.ofReal_mul]

private lemma cpow_jacobian_identity {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) (h1 : ν * θ < 1)
    (μ : ℂ) :
    (clockAge ν θ : ℂ) ^ (-μ) * ((clockAge ν θ ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
        (((ν ^ 2 * θ ^ 2)⁻¹ : ℝ) : ℂ) =
      (ν : ℂ) ^ (3 + 2 * μ) *
        ((θ : ℂ) ^ (μ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)) := by
  set u : ℝ := 1 - ν * θ
  have hu : 0 < u := by dsimp [u]; linarith
  set s : ℝ := clockAge ν θ
  have hs_eq : s = u / (ν ^ 2 * θ) := rfl
  have hs : 0 < s := by rw [hs_eq]; positivity
  have hjac_pos : 0 < (ν ^ 2 * θ ^ 2)⁻¹ := by positivity
  have hjac_exp : (((ν ^ 2 * θ ^ 2)⁻¹ : ℝ) : ℂ) =
      Complex.exp ((Real.log ((ν ^ 2 * θ ^ 2)⁻¹) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log hjac_pos]
  have hlog_s : Real.log s = Real.log u - 2 * Real.log ν - Real.log θ := by
    rw [hs_eq, Real.log_div hu.ne' (by positivity), Real.log_mul (pow_ne_zero 2 hν.ne') hθ.ne',
      Real.log_pow, Nat.cast_ofNat]
    ring
  have hlog_jac : Real.log ((ν ^ 2 * θ ^ 2)⁻¹) = -(2 * Real.log ν + 2 * Real.log θ) := by
    rw [Real.log_inv, Real.log_mul (pow_ne_zero 2 hν.ne') (pow_ne_zero 2 hθ.ne'),
      Real.log_pow, Real.log_pow, Nat.cast_ofNat]
  rw [ofReal_cpow_eq_exp hs, ofReal_rpow_eq_exp hs, hjac_exp,
    ofReal_cpow_eq_exp hν, ofReal_cpow_eq_exp hθ, ofReal_cpow_eq_exp hu]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hlog_s, hlog_jac]
  push_cast
  ring

private lemma norm_one_sub_cpow_le_eight {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    {μ : ℂ} (hμ0 : 0 < μ.re) (hμ1 : μ.re < 1 / 4) :
    ‖((1 - x : ℝ) : ℂ) ^ (-μ - 5 / 2)‖ ≤ 8 := by
  have hpos : 0 < 1 - x := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-μ - 5 / 2).re = -μ.re - 5 / 2 := by
    have : (5 / 2 : ℂ).re = 5 / 2 := by norm_num
    simp [this]
  rw [hre]
  have hexp_ge : (-3 : ℝ) ≤ -μ.re - 5 / 2 := by linarith
  have hle1 : 1 - x ≤ 1 := by linarith
  have hge_half : (1 / 2 : ℝ) ≤ 1 - x := by linarith
  calc (1 - x) ^ (-μ.re - 5 / 2)
      ≤ (1 - x) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hpos hle1 hexp_ge
    _ = ((1 - x) ^ (3 : ℝ))⁻¹ := Real.rpow_neg hpos.le 3
    _ ≤ ((1 / 2 : ℝ) ^ (3 : ℝ))⁻¹ := by
        refine inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) 3) ?_
        exact Real.rpow_le_rpow (by norm_num) hge_half (by norm_num)
    _ = 8 := by norm_num

private lemma abs_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hle1 : 1 - x ≤ 1 := by linarith
  have hlog_nonpos : Real.log (1 - x) ≤ 0 := Real.log_nonpos hpos.le hle1
  rw [abs_of_nonpos hlog_nonpos, ← Real.log_inv]
  have hinv_le : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [← one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)]
  have h1 : Real.log ((1 - x)⁻¹) ≤ Real.log (1 + 2 * x) :=
    Real.log_le_log (inv_pos.2 hpos) hinv_le
  have h2 : Real.log (1 + 2 * x) ≤ 2 * x := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    linarith [Real.add_one_le_exp (2 * x)]
  exact h1.trans h2

private lemma norm_one_sub_cpow_sub_one_le {x M_K : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hMK : 0 ≤ M_K) {μ : ℂ} (hμ : ‖μ‖ ≤ M_K) (hsmall : (M_K + 3) * (2 * x) ≤ 1) :
    ‖((1 - x : ℝ) : ℂ) ^ (-μ - 5 / 2) - 1‖ ≤ 4 * (M_K + 3) * x := by
  have hpos : 0 < 1 - x := by linarith
  rw [ofReal_cpow_eq_exp hpos]
  set z : ℂ := (Real.log (1 - x) : ℂ) * (-μ - 5 / 2)
  have hmu_bd : ‖-μ - 5 / 2‖ ≤ M_K + 3 := by
    have h52 : ‖(5 / 2 : ℂ)‖ = 5 / 2 := by norm_num
    calc ‖-μ - 5 / 2‖ ≤ ‖-μ‖ + ‖(5 / 2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖μ‖ + 5 / 2 := by rw [norm_neg, h52]
      _ ≤ M_K + 3 := by linarith
  have hz_bd : ‖z‖ ≤ (M_K + 3) * (2 * x) := by
    dsimp [z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul hmu_bd (abs_log_one_sub_le hx0 hx1) (abs_nonneg _) (by positivity)
  have hz1 : ‖z‖ ≤ 1 := hz_bd.trans hsmall
  calc ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hz1
    _ ≤ 2 * ((M_K + 3) * (2 * x)) := mul_le_mul_of_nonneg_left hz_bd (by norm_num)
    _ = 4 * (M_K + 3) * x := by ring

/-! ## Section 2: Rescaling, `quadQ` continuity, Jacobian CoV, and symmetrized flow restart -/

private lemma map_sqrt_smul_volume {a : ℝ} (ha : 0 < a) :
    Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume =
      ENNReal.ofReal a⁻¹ • (volume : Measure (ℝ × ℝ)) := by
  have hR : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hR
  simpa only [hfin, Real.sq_sqrt ha.le, abs_inv, abs_of_pos ha] using hmap

private lemma qmp_sqrt_smul {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ => Real.sqrt a • y) volume volume :=
  ⟨measurable_const_smul (Real.sqrt a), by
    rw [map_sqrt_smul_volume ha]
    exact Measure.smul_absolutelyContinuous⟩

private lemma lintegral_aemeasurable_comp_sqrt_smul {a : ℝ} (ha : 0 < a)
    {H : ℝ × ℝ → ℝ≥0∞} (hH : AEMeasurable H volume) :
    ∫⁻ y, H (Real.sqrt a • y) = ENNReal.ofReal a⁻¹ * ∫⁻ x, H x := by
  have hmap := map_sqrt_smul_volume ha
  have hH_map : AEMeasurable H (Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume) := by
    rw [hmap]
    exact hH.mono_ac Measure.smul_absolutelyContinuous
  rw [← lintegral_map' hH_map (measurable_const_smul (Real.sqrt a)).aemeasurable,
    hmap, lintegral_smul_measure, smul_eq_mul]

private lemma integrableOn_and_integral_comp_sqrt_smul {a d : ℝ} (ha : 0 < a)
    {g : ℝ × ℝ → ℂ} (hg : IntegrableOn g (B0579.cell (d * Real.sqrt a))) :
    IntegrableOn (fun y => g (Real.sqrt a • y)) (B0579.cell d) ∧
      (∫ y in B0579.cell d, g (Real.sqrt a • y)) =
        ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), g x := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set G : ℝ × ℝ → ℂ := (B0579.cell (d * Real.sqrt a)).indicator g
  have hG_int : Integrable G volume :=
    (integrable_indicator_iff (B0579.measurableSet_cell _)).2 hg
  have hmap := map_sqrt_smul_volume ha
  have hG_map : Integrable G (Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume) := by
    rw [hmap]
    exact hG_int.smul_measure ENNReal.ofReal_ne_top
  have hcomp_int : Integrable (fun y => G (Real.sqrt a • y)) volume :=
    (integrable_map_measure hG_map.1 (measurable_const_smul (Real.sqrt a)).aemeasurable).1 hG_map
  have hind_eq : (fun y : ℝ × ℝ => G (Real.sqrt a • y)) =
      (B0579.cell d).indicator (fun y => g (Real.sqrt a • y)) := by
    funext y
    by_cases hy : y ∈ B0579.cell d
    · have hy' : Real.sqrt a • y ∈ B0579.cell (d * Real.sqrt a) :=
        (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp [G, hy, hy']
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [G, hy, hy']
  have hint_d : IntegrableOn (fun y => g (Real.sqrt a • y)) (B0579.cell d) := by
    rw [← integrable_indicator_iff (B0579.measurableSet_cell d), ← hind_eq]
    exact hcomp_int
  refine ⟨hint_d, ?_⟩
  rw [← integral_indicator (B0579.measurableSet_cell d), ← hind_eq,
    ← integral_map (measurable_const_smul (Real.sqrt a)).aemeasurable hG_map.1,
    hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 ha.le),
    Complex.real_smul, integral_indicator (B0579.measurableSet_cell _)]

private lemma dOfTheta_mul_sqrt_inv {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    dOfTheta ν x * Real.sqrt ((ν * x)⁻¹) = ν ^ (-2 : ℝ) := by
  unfold dOfTheta
  have hc_pos : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
    ring
  rw [← Real.sqrt_mul (by positivity : 0 ≤ x / ν ^ 3)]
  have hprod : x / ν ^ 3 * (ν * x)⁻¹ = (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hc_sq]
    have hν_ne := hν.ne'
    have hx_ne := hx.ne'
    field_simp
  rw [hprod, Real.sqrt_sq hc_pos.le]

private lemma integrableOn_etaSq_mul {d m : ℝ} (hm : 3 < m) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure d m)) :
    IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * g x) (B0579.cell d) := by
  have hg_aesm : AEStronglyMeasurable g (volume.restrict (B0579.cell d)) :=
    hg.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure d m)
  have hmeas_eta : Continuous (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_snd.pow 2)
  refine ⟨hmeas_eta.aestronglyMeasurable.mul hg_aesm, ?_⟩
  show ∫⁻ x in B0579.cell d, ‖((x.2 ^ 2 : ℝ) : ℂ) * g x‖ₑ < ⊤
  simp_rw [enorm_mul]
  rw [CTE.QuadQBoundProof.lintegral_cell_eq d m]
  have hF : AEMeasurable (fun x : ℝ × ℝ => (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ *
      ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) (B0579.cellMeasure d m) := by
    apply Measurable.aemeasurable
    exact ((B0579.continuous_jb_rpow m).measurable.ennreal_ofReal.inv).mul
      hmeas_eta.measurable.enorm
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure d m)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hF hg.aestronglyMeasurable.enorm
  simp only [ENNReal.rpow_two] at hCS
  have hstep : ∫⁻ x, (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * (‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖g x‖ₑ)
      ∂(B0579.cellMeasure d m) ≤
      (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) *
        xNorm d m g := by
    refine (le_of_eq (lintegral_congr fun x => by simp only [Pi.mul_apply, mul_assoc])).trans
      (hCS.trans ?_)
    rw [← CTE.QuadQBoundProof.eLpNorm_two_eq]
    refine mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow ?_ (by norm_num)) zero_le
    rw [CTE.QuadQBoundProof.lintegral_cellMeasure_eq]
    exact (lintegral_mono fun x => CTE.QuadQBoundProof.density_mul_sq_le m hm x).trans
      (setLIntegral_le_lintegral _ _)
  refine hstep.trans_lt (ENNReal.mul_lt_top ?_ hg.2)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (CTE.QuadQBoundProof.integrable_moment m hm).lintegral_lt_top.ne

private lemma quadQ_smul (d : ℝ) (α : ℂ) (g : ℝ × ℝ → ℂ) :
    quadQ d (fun x => α * g x) = α * quadQ d g := by
  unfold quadQ
  have hpt : (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * (α * g x)) =
      fun x => α * (((x.2 ^ 2 : ℝ) : ℂ) * g x) := by
    funext x; ring
  rw [hpt, integral_const_mul]
  ring

private lemma quadQ_sub {d m : ℝ} (hm : 3 < m) {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure d m)) (hg : MemLp g 2 (B0579.cellMeasure d m)) :
    quadQ d (f - g) = quadQ d f - quadQ d g := by
  have hif := integrableOn_etaSq_mul hm hf
  have hig := integrableOn_etaSq_mul hm hg
  unfold quadQ
  have hpt : (fun x : B0579.Plane => ((x.2 ^ 2 : ℝ) : ℂ) * (f - g) x) =
      fun x => ((x.2 ^ 2 : ℝ) : ℂ) * f x - ((x.2 ^ 2 : ℝ) : ℂ) * g x := by
    funext x; simp [Pi.sub_apply, mul_sub]
  rw [hpt, integral_sub hif hig, mul_sub]

private lemma integrableOn_and_quadQ_jscaleInv {a d : ℝ} (ha : 0 < a) {g : ℝ × ℝ → ℂ}
    (hg : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * g x) (B0579.cell (d * Real.sqrt a))) :
    IntegrableOn (fun y => ((y.2 ^ 2 : ℝ) : ℂ) * JscaleInv a g y) (B0579.cell d) ∧
      quadQ d (JscaleInv a g) = quadQ (d * Real.sqrt a) g := by
  obtain ⟨hint_comp, hval_comp⟩ := integrableOn_and_integral_comp_sqrt_smul ha hg
  have hpt : (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * JscaleInv a g y) =
      fun y => ((a : ℝ) : ℂ) * ((((Real.sqrt a • y).2 ^ 2 : ℝ) : ℂ) * g (Real.sqrt a • y)) := by
    funext y
    unfold JscaleInv
    have hsmul : (Real.sqrt a • y).2 ^ 2 = a * y.2 ^ 2 := by
      simp only [Prod.smul_snd, smul_eq_mul, mul_pow, Real.sq_sqrt ha.le]
    rw [← T07.sqrt_smul_eq, hsmul]
    push_cast
    ring
  refine ⟨by rw [hpt]; exact hint_comp.const_mul _, ?_⟩
  unfold quadQ
  have hainv : ((a : ℝ) : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one]
  rw [hpt, integral_const_mul, hval_comp, ← mul_assoc ((a : ℝ) : ℂ) ((a⁻¹ : ℝ) : ℂ),
    hainv, one_mul]

private lemma quadQ_heatColumn_eq (P : PlanarData) {ν m θ : ℝ} (hm : 3 < m)
    (hν : 0 < ν) (hθ : 0 < θ) (hθν : θ ≤ ν⁻¹)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w u) :
    quadQ (dOfTheta ν θ) (heatColumn P ν w θ) =
      (P.gaugeFactor ν)⁻¹ * quadQ (ν ^ (-2 : ℝ)) (w (clockAge ν θ)) := by
  have hs0 : 0 ≤ clockAge ν θ := T22Sub.clockAge_nonneg hν hθ hθν
  have ha : 0 < (ν * θ)⁻¹ := inv_pos.2 (mul_pos hν hθ)
  have hdc : dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹) = ν ^ (-2 : ℝ) := dOfTheta_mul_sqrt_inv hν hθ
  have hmem : MemLp (w (clockAge ν θ)) 2
      (B0579.cellMeasure (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹)) m) :=
    hdc.symm ▸ hw.memX (clockAge ν θ) hs0
  have hint := integrableOn_etaSq_mul hm hmem
  unfold heatColumn
  rw [quadQ_smul, (integrableOn_and_quadQ_jscaleInv ha hint).2, hdc]

private lemma continuousOn_quadQ_flow {ν c m : ℝ} (hm : 3 < m)
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr 0 f₀ w u) :
    ContinuousOn (fun s => quadQ c (w s)) (Ici 0) := by
  obtain ⟨C_q, hCq⟩ := CTE.quadQ_bound m hm
  let C' : ℝ := max C_q 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  intro s hs
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro δ hδ
  have hlim := hw.strongCont s hs
  have hmul : Tendsto (fun s' => ENNReal.ofReal C' * xNorm c m (w s' - w s))
      (𝓝[Ici 0] s) (𝓝 0) := by
    simpa [mul_zero] using
      (ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.ofReal_ne_top (r := C'))))
  have hev : ∀ᶠ s' in 𝓝[Ici 0] s,
      ENNReal.ofReal C' * xNorm c m (w s' - w s) < ENNReal.ofReal δ :=
    hmul.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hδ))
  filter_upwards [hev, self_mem_nhdsWithin] with s' hs'_lt hs'0
  rw [dist_eq_norm, ← quadQ_sub hm (hw.memX s' hs'0) (hw.memX s hs)]
  have hbd : ENNReal.ofReal ‖quadQ c (w s' - w s)‖ ≤
      ENNReal.ofReal C' * xNorm c m (w s' - w s) :=
    (hCq c (w s' - w s) ((hw.memX s' hs'0).sub (hw.memX s hs))).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).1 (lt_of_le_of_lt hbd hs'_lt)

private lemma continuousOn_fZ (P : PlanarData) {ν m : ℝ} (hm : 3 < m) (hν : 0 < ν)
    (μ : ℂ) {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w u) :
    ContinuousOn (fZ P ν μ w) (Ioc 0 (thetaOnset ν)) := by
  have hT_lt : thetaOnset ν < ν⁻¹ := thetaOnset_lt_inv hν
  have hage_cont : ContinuousOn (clockAge ν) (Ioc 0 (thetaOnset ν)) := by
    intro θ hθ
    exact ((hasDerivAt_clockAge hν hθ.1).continuousAt).continuousWithinAt
  have hmaps : MapsTo (clockAge ν) (Ioc 0 (thetaOnset ν)) (Ici 0) :=
    fun θ hθ => T22Sub.clockAge_nonneg hν hθ.1 (hθ.2.trans hT_lt.le)
  have hq_cont : ContinuousOn (fun θ => quadQ (dOfTheta ν θ) (heatColumn P ν w θ))
      (Ioc 0 (thetaOnset ν)) := by
    refine ContinuousOn.congr
      (((continuousOn_quadQ_flow hm hw).comp hage_cont hmaps).const_mul (P.gaugeFactor ν)⁻¹) ?_
    intro θ hθ
    exact quadQ_heatColumn_eq P hm hν hθ.1 (hθ.2.trans hT_lt.le) hw
  have hc1 : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2)) (Ioc 0 (thetaOnset ν)) := by
    intro θ hθ
    have harg : (θ : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hθ.1))
    exact ((continuousAt_cpow_const harg).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hc2 : ContinuousOn (fun θ : ℝ => ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2))
      (Ioc 0 (thetaOnset ν)) := by
    intro θ hθ
    have hmul_lt : ν * θ < 1 := by
      have := (mul_lt_mul_of_pos_left (hθ.2.trans_lt hT_lt) hν)
      simpa [mul_inv_cancel₀ hν.ne'] using this
    have hpos : 0 < 1 - ν * θ := by linarith
    have harg : ((1 - ν * θ : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hpos))
    have hinner : ContinuousAt (fun t : ℝ => ((1 - ν * t : ℝ) : ℂ)) θ :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    exact (ContinuousAt.comp (f := fun t : ℝ => ((1 - ν * t : ℝ) : ℂ))
      (continuousAt_cpow_const harg) hinner).continuousWithinAt
  exact (hc1.mul hc2).mul hq_cont

private lemma cov_integrand_pointwise (P : PlanarData) {ν m θ : ℝ} (hm : 3 < m)
    (hν : 0 < ν) (hθ : θ ∈ Ioo 0 (thetaOnset ν)) (μ : ℂ)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w u) :
    |-(ν ^ 2 * θ ^ 2)⁻¹| •
        (aPlus ν μ w (clockAge ν θ) * ((clockAge ν θ ^ (-5 / 2 : ℝ) : ℝ) : ℂ)) =
      mellinPref P ν μ * fZ P ν μ w θ := by
  have hT_lt : thetaOnset ν < ν⁻¹ := thetaOnset_lt_inv hν
  have hθ0 : 0 < θ := hθ.1
  have hθν : θ < ν⁻¹ := hθ.2.trans hT_lt
  have h1 : ν * θ < 1 := by
    have := mul_lt_mul_of_pos_left hθν hν
    simpa [mul_inv_cancel₀ hν.ne'] using this
  have hjac_pos : 0 < (ν ^ 2 * θ ^ 2)⁻¹ := by positivity
  rw [abs_neg, abs_of_pos hjac_pos, Complex.real_smul]
  have hq := quadQ_heatColumn_eq P hm hν hθ0 hθν.le hw
  have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν
  have hq_inv : quadQ (ν ^ (-2 : ℝ)) (w (clockAge ν θ)) =
      P.gaugeFactor ν * quadQ (dOfTheta ν θ) (heatColumn P ν w θ) := by
    rw [hq, mul_inv_cancel_left₀ hgf_ne]
  have hcpow := cpow_jacobian_identity hν hθ0 h1 μ
  unfold aPlus mellinPref fZ
  rw [hq_inv]
  calc (((ν ^ 2 * θ ^ 2)⁻¹ : ℝ) : ℂ) *
        (-((Real.pi : ℝ) : ℂ) * (clockAge ν θ : ℂ) ^ (-μ) *
          (P.gaugeFactor ν * quadQ (dOfTheta ν θ) (heatColumn P ν w θ)) /
          (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
          ((clockAge ν θ ^ (-5 / 2 : ℝ) : ℝ) : ℂ))
      = (-((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν / (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ))) *
          ((clockAge ν θ : ℂ) ^ (-μ) * ((clockAge ν θ ^ (-5 / 2 : ℝ) : ℝ) : ℂ) *
            (((ν ^ 2 * θ ^ 2)⁻¹ : ℝ) : ℂ)) *
          quadQ (dOfTheta ν θ) (heatColumn P ν w θ) := by ring
    _ = -((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν / (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) *
          (ν : ℂ) ^ (3 + 2 * μ) *
          ((θ : ℂ) ^ (μ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) *
            quadQ (dOfTheta ν θ) (heatColumn P ν w θ)) := by
        rw [hcpow]; ring

private lemma iA_cov (P : PlanarData) {ν m : ℝ} (hm : 3 < m) (hν : 0 < ν) (μ : ℂ)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w u)
    (hint : IntegrableOn (fZ P ν μ w) (Ioo 0 (thetaOnset ν))) :
    IntegrableOn (fun s => aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ))
        (Ioi (onsetAge ν)) ∧
      iA ν μ w / mellinPref P ν μ =
        ∫ θ in Ioo 0 (thetaOnset ν), fZ P ν μ w θ := by
  let S : Set ℝ := Ioo 0 (thetaOnset ν)
  let g : ℝ → ℂ := fun s => aPlus ν μ w s * ((s ^ (-5 / 2 : ℝ) : ℝ) : ℂ)
  have hS : MeasurableSet S := measurableSet_Ioo
  have hderiv : ∀ θ ∈ S, HasDerivWithinAt (clockAge ν) (-(ν ^ 2 * θ ^ 2)⁻¹) S θ :=
    fun θ hθ => (hasDerivAt_clockAge hν hθ.1).hasDerivWithinAt
  have hinj : InjOn (clockAge ν) S := (injOn_clockAge_Ioi hν).mono (fun _ h => h.1)
  have himg : clockAge ν '' S = Ioi (onsetAge ν) := image_clockAge_Ioo_thetaOnset hν
  have hcongr : EqOn (fun θ => |-(ν ^ 2 * θ ^ 2)⁻¹| • g (clockAge ν θ))
      (fun θ => mellinPref P ν μ * fZ P ν μ w θ) S :=
    fun θ hθ => cov_integrand_pointwise P hm hν hθ μ hw
  have hint_rhs : IntegrableOn (fun θ => mellinPref P ν μ * fZ P ν μ w θ) S :=
    hint.const_mul (mellinPref P ν μ)
  have hint_pulled : IntegrableOn (fun θ => |-(ν ^ 2 * θ ^ 2)⁻¹| • g (clockAge ν θ)) S :=
    hint_rhs.congr_fun hcongr.symm hS
  have hint_g : IntegrableOn g (Ioi (onsetAge ν)) := by
    rw [← himg]
    exact (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hderiv hinj g).2 hint_pulled
  refine ⟨hint_g, ?_⟩
  have hval : iA ν μ w = mellinPref P ν μ * ∫ θ in S, fZ P ν μ w θ := by
    unfold iA
    change ∫ s in Ioi (onsetAge ν), g s = _
    rw [← himg, integral_image_eq_integral_abs_deriv_smul hS hderiv hinj g,
      setIntegral_congr_fun hS hcongr, integral_const_mul]
  rw [hval, mul_div_cancel_left₀ _ (mellinPref_ne_zero P hν μ)]

/-! ### Symmetrization and homogeneous `IsLinearisedFlow` restart -/

private def symEven (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  (2 : ℂ)⁻¹ * (f x + f (-x))

private def symOddVel (u : ℝ × ℝ → Fin 2 → ℂ) (x : ℝ × ℝ) (j : Fin 2) : ℂ :=
  (2 : ℂ)⁻¹ * (u x j - u (-x) j)

private def rescaleVel (a : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (y : ℝ × ℝ) (j : Fin 2) : ℂ :=
  ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u (Real.sqrt a • y) j

private lemma isCentrallyEven_symEven (f : ℝ × ℝ → ℂ) : IsCentrallyEven (symEven f) := by
  intro x
  unfold symEven
  rw [neg_neg, add_comm]

private lemma cell_neg_ae_eq (c : ℝ) :
    (Neg.neg ⁻¹' B0579.cell c : Set (ℝ × ℝ)) =ᵐ[volume] B0579.cell c := by
  rw [MeasureTheory.ae_eq_set]
  by_cases hc : 0 < c
  · refine ⟨?_, ?_⟩
    · have hsub : (Neg.neg ⁻¹' B0579.cell c) \ B0579.cell c ⊆ {c / 2} ×ˢ (univ : Set ℝ) := by
        rintro x ⟨h1, h2⟩
        simp only [mem_preimage, B0579.cell, mem_prod, mem_Ico, mem_univ, and_true,
          Prod.fst_neg] at h1 h2
        have hx' : x.1 = c / 2 := by
          by_contra hne
          exact h2 ⟨by linarith, lt_of_le_of_ne (by linarith) hne⟩
        exact ⟨hx', trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
    · have hsub : B0579.cell c \ (Neg.neg ⁻¹' B0579.cell c) ⊆ {-(c / 2)} ×ˢ (univ : Set ℝ) := by
        rintro x ⟨h1, h2⟩
        simp only [mem_preimage, B0579.cell, mem_prod, mem_Ico, mem_univ, and_true,
          Prod.fst_neg] at h1 h2
        have hx' : x.1 = -(c / 2) := by
          by_contra hne
          exact h2 ⟨by linarith, by have := lt_of_le_of_ne h1.1 (Ne.symm hne); linarith⟩
        exact ⟨hx', trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  · have h1 : B0579.cell c = ∅ := by
      ext x
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, mem_empty_iff_false, iff_false]
      rintro ⟨a, b⟩; linarith
    simp [h1]

private lemma measurePreserving_neg_cell (c : ℝ) :
    MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ)
      (volume.restrict (B0579.cell c)) (volume.restrict (B0579.cell c)) := by
  refine ⟨measurable_neg, ?_⟩
  have hmp : MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_neg volume
  have heq : volume.restrict (Neg.neg ⁻¹' B0579.cell c) = volume.restrict (B0579.cell c) :=
    Measure.restrict_congr_set (cell_neg_ae_eq c)
  calc Measure.map Neg.neg (volume.restrict (B0579.cell c))
      = Measure.map Neg.neg (volume.restrict (Neg.neg ⁻¹' B0579.cell c)) := by rw [heq]
    _ = (Measure.map Neg.neg volume).restrict (B0579.cell c) :=
        ((MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding.restrict_map volume (B0579.cell c)).symm
    _ = volume.restrict (B0579.cell c) := by rw [hmp.map_eq]

private lemma integral_cell_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : ℝ × ℝ → E) :
    ∫ x in B0579.cell c, f (-x) = ∫ x in B0579.cell c, f x :=
  (measurePreserving_neg_cell c).integral_comp (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding f

private lemma ae_neg_of_ae_cell {c : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => g (-x)) :=
  (measurePreserving_neg_cell c).quasiMeasurePreserving.ae_eq_comp h

private lemma xNorm_comp_neg_cellMeasure (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    xNorm c m (fun x => F (-x)) = xNorm c m F := by
  unfold xNorm
  rw [PairContAux.eLpNorm_cellMeasure_cx, PairContAux.eLpNorm_cellMeasure_cx,
    T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral]
  congr 1
  have hjb : ∀ x : ℝ × ℝ, B0579.jb (-x) = B0579.jb x := fun x => by simp [B0579.jb]
  have hfn : (fun x : ℝ × ℝ => ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F (-x)‖ₑ ^ 2) =
      (fun y : ℝ × ℝ => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2) ∘ Neg.neg := by
    funext x; simp [Function.comp, hjb x]
  rw [hfn]
  exact (measurePreserving_neg_cell c).lintegral_comp_emb
    (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding
    (fun y => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2)

private lemma memLp_comp_neg_cellMeasure {c m : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => F (-x)) 2 (B0579.cellMeasure c m) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_vol : F =ᵐ[volume.restrict (B0579.cell c)] F₀ :=
    (B0579.ac_cellMeasure c m).ae_le hF.1.ae_eq_mk
  have hae_neg : (fun x => F (-x)) =ᵐ[B0579.cellMeasure c m] (fun x => F₀ (-x)) :=
    (B0579.cellMeasure_ac c m).ae_le (ae_neg_of_ae_cell hae_vol)
  have hm : AEStronglyMeasurable (fun x => F (-x)) (B0579.cellMeasure c m) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  change xNorm c m (fun x => F (-x)) < ⊤
  rw [xNorm_comp_neg_cellMeasure]
  exact hF.2

private lemma memLp_and_eLpNorm_comp_neg_vol {c : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun x => F (-x)) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => F (-x)) 2 (volume.restrict (B0579.cell c)) =
        eLpNorm F 2 (volume.restrict (B0579.cell c)) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_neg : (fun x => F (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => F₀ (-x)) :=
    ae_neg_of_ae_cell hF.1.ae_eq_mk
  have hm : AEStronglyMeasurable (fun x => F (-x)) (volume.restrict (B0579.cell c)) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  have heq : eLpNorm (fun x => F (-x)) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm F 2 (volume.restrict (B0579.cell c)) := by
    rw [T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral]
    congr 1
    exact (measurePreserving_neg_cell c).lintegral_comp_emb
      (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding (fun y => ‖F y‖ₑ ^ 2)
  exact ⟨⟨hm, heq.trans_lt hF.2⟩, heq⟩

private lemma quadQ_symEven_eq {d m : ℝ} (hm : 3 < m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure d m)) :
    quadQ d (symEven f) = quadQ d f := by
  have hint : Integrable (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * f x) (volume.restrict (B0579.cell d)) :=
    integrableOn_etaSq_mul hm hf
  have hint_neg : IntegrableOn (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * f (-x)) (B0579.cell d) := by
    have hcomp := (measurePreserving_neg_cell d).integrable_comp_of_integrable hint
    refine hcomp.congr (Eventually.of_forall fun x => ?_)
    simp [Function.comp]
  have hval_neg : ∫ x in B0579.cell d, ((x.2 ^ 2 : ℝ) : ℂ) * f (-x) =
      ∫ x in B0579.cell d, ((x.2 ^ 2 : ℝ) : ℂ) * f x := by
    have hpt : (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * f (-x)) =
        fun x => (((-x).2 ^ 2 : ℝ) : ℂ) * f (-x) := by
      funext x; simp
    rw [hpt, integral_cell_neg d (fun y => ((y.2 ^ 2 : ℝ) : ℂ) * f y)]
  unfold quadQ symEven
  have hpt : (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * ((2 : ℂ)⁻¹ * (f x + f (-x)))) =
      fun x => (2 : ℂ)⁻¹ * (((x.2 ^ 2 : ℝ) : ℂ) * f x + ((x.2 ^ 2 : ℝ) : ℂ) * f (-x)) := by
    funext x; ring
  rw [hpt, integral_const_mul, integral_add hint hint_neg, hval_neg]
  ring

private lemma pd_comp_neg_any (F : ℝ × ℝ → ℝ) (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => F (-y)) x = -B0579.pd k F (-x) := by
  let e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.neg ℝ
  have hfun : (fun y => F (-y)) = F ∘ e := rfl
  unfold B0579.pd
  rw [hfun, e.comp_right_fderiv, ContinuousLinearMap.comp_apply]
  simp [e]

private lemma pd_neg_any (G : ℝ × ℝ → ℝ) (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => -G y) x = -B0579.pd k G x := by
  unfold B0579.pd
  change (fderiv ℝ (-G) x) (B0579.dir k) = -(fderiv ℝ G x) (B0579.dir k)
  rw [fderiv_neg]
  rfl

private lemma isCylTest_neg {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun x => ψ (-x)) := by
  refine ⟨hψ.smooth.comp contDiff_neg, fun x => ?_, ?_⟩
  · have hp := hψ.periodic (-x.1 - c, -x.2)
    dsimp only at hp
    have h1 : -((x.1 + c, x.2) : ℝ × ℝ) = (-x.1 - c, -x.2) := by
      ext
      · simp; ring
      · simp
    have h2 : (-x.1 - c + c, -x.2) = -x := by ext <;> simp
    rw [h1, ← hp, h2]
  · obtain ⟨B, hB⟩ := hψ.band
    refine ⟨B, fun x hx => hB (-x) ?_⟩
    simpa using hx

private lemma isBiotSavart_smul {d : ℝ} (z : ℂ) {f : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : IsBiotSavart d f u) :
    IsBiotSavart d (fun x => z * f x) (fun x j => z * u x j) := by
  refine ⟨fun j => (hu.1 j).const_mul z, ?_, ?_⟩
  · intro ψ hψ
    have hp : (fun x => z * u x 0 * (B0579.pd 0 ψ x : ℂ) + z * u x 1 * (B0579.pd 1 ψ x : ℂ)) =
        fun x => z * (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x; ring
    rw [hp, integral_const_mul, hu.2.1 ψ hψ, mul_zero]
  · intro ψ hψ
    have hp1 : (fun x => z * f x * (ψ x : ℂ)) = fun x => z * (f x * (ψ x : ℂ)) := by
      funext x; ring
    have hp2 : (fun x => z * u x 0 * (B0579.pd 1 ψ x : ℂ) - z * u x 1 * (B0579.pd 0 ψ x : ℂ)) =
        fun x => z * (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      funext x; ring
    rw [hp1, hp2, integral_const_mul, integral_const_mul, hu.2.2 ψ hψ]

private lemma isBiotSavart_refl_neg {d : ℝ} {f : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : IsBiotSavart d f u) :
    IsBiotSavart d (fun x => f (-x)) (fun x j => -u (-x) j) := by
  refine ⟨fun j => (memLp_and_eLpNorm_comp_neg_vol (hu.1 j)).1.neg, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hψn := isCylTest_neg hψ
    have hpt : (fun x => -u (-x) 0 * (B0579.pd 0 ψ x : ℂ) + -u (-x) 1 * (B0579.pd 1 ψ x : ℂ)) =
        fun x => u (-x) 0 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) +
          u (-x) 1 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) := by
      funext x
      have p0 := pd_comp_neg_any ψ 0 (-x)
      have p1 := pd_comp_neg_any ψ 1 (-x)
      rw [neg_neg] at p0 p1
      rw [p0, p1]
      push_cast; ring
    rw [hpt, integral_cell_neg d (fun y => u y 0 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ) +
      u y 1 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ))]
    exact hu.2.1 _ hψn
  · have hψn := isCylTest_neg hψ
    have hl : ∫ x in B0579.cell d, f (-x) * (ψ x : ℂ) =
        ∫ y in B0579.cell d, f y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun x : ℝ × ℝ => f (-x) * (ψ x : ℂ)) =
          fun x => f (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp
      rw [hp]
      exact integral_cell_neg d (fun y => f y * ((fun z => ψ (-z)) y : ℂ))
    have hr : (fun x => -u (-x) 0 * (B0579.pd 1 ψ x : ℂ) - -u (-x) 1 * (B0579.pd 0 ψ x : ℂ)) =
        fun x => u (-x) 0 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) -
          u (-x) 1 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) := by
      funext x
      have p0 := pd_comp_neg_any ψ 0 (-x)
      have p1 := pd_comp_neg_any ψ 1 (-x)
      rw [neg_neg] at p0 p1
      rw [p0, p1]
      push_cast; ring
    rw [hl, hr, integral_cell_neg d (fun y => u y 0 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ) -
      u y 1 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ))]
    exact hu.2.2 _ hψn

private lemma isBiotSavart_congr_ae {d : ℝ} {f₁ f₂ : ℝ × ℝ → ℂ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (h : IsBiotSavart d f₁ u₁)
    (hf : f₁ =ᵐ[volume.restrict (B0579.cell d)] f₂)
    (hu : u₁ =ᵐ[volume.restrict (B0579.cell d)] u₂) :
    IsBiotSavart d f₂ u₂ := by
  refine ⟨fun j => ⟨(h.1 j).1.congr (hu.mono fun x hx => congrArg (fun v => v j) hx),
      (eLpNorm_congr_ae (hu.symm.mono fun x hx => congrArg (fun v => v j) hx)).trans_lt (h.1 j).2⟩,
    ?_, ?_⟩
  · intro ψ hψ
    rw [← h.2.1 ψ hψ]
    exact integral_congr_ae (hu.symm.mono fun x hx => by simp [hx])
  · intro ψ hψ
    have hl : ∫ x in B0579.cell d, f₂ x * (ψ x : ℂ) = ∫ x in B0579.cell d, f₁ x * (ψ x : ℂ) :=
      integral_congr_ae (hf.symm.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
    have hr : ∫ x in B0579.cell d, (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) =
        ∫ x in B0579.cell d, (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) :=
      integral_congr_ae (hu.symm.mono fun x hx => by simp [hx])
    rw [hl, hr, h.2.2 ψ hψ]

private lemma isBiotSavart_add {d m : ℝ} (hm : 1 < m) {f₁ f₂ : ℝ × ℝ → ℂ}
    {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure d m)) (hf₂ : MemLp f₂ 2 (B0579.cellMeasure d m))
    (h₁ : IsBiotSavart d f₁ u₁) (h₂ : IsBiotSavart d f₂ u₂) :
    IsBiotSavart d (f₁ + f₂) (u₁ + u₂) := by
  have hneg := isBiotSavart_smul (-1 : ℂ) h₂
  have hsub := ladBSSub m d f₁ (fun x => (-1 : ℂ) * f₂ x) u₁ (fun x j => (-1 : ℂ) * u₂ x j)
    hm hf₁ (hf₂.const_mul (-1 : ℂ)) h₁ hneg
  refine isBiotSavart_congr_ae hsub (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · simp [Pi.sub_apply, Pi.add_apply]
  · funext j; simp [Pi.sub_apply, Pi.add_apply]

private lemma velNorm_smul {d : ℝ} (z : ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) :
    velNorm d (fun x j => z * u x j) = ENNReal.ofReal ‖z‖ * velNorm d u := by
  unfold velNorm
  have he : ∀ j : Fin 2, eLpNorm (fun x => z * u x j) 2 (volume.restrict (B0579.cell d)) =
      ENNReal.ofReal ‖z‖ * eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) := by
    intro j
    change eLpNorm (z • fun x => u x j) 2 (volume.restrict (B0579.cell d)) = _
    rw [eLpNorm_const_smul, ofReal_norm]
  have hsum : (∑ j : Fin 2, eLpNorm (fun x => z * u x j) 2 (volume.restrict (B0579.cell d)) ^ 2) =
      ENNReal.ofReal ‖z‖ ^ 2 *
        ∑ j : Fin 2, eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he j, mul_pow]
  rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private lemma velNorm_add_le {d : ℝ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (h₁ : ∀ j, MemLp (fun x => u₁ x j) 2 (volume.restrict (B0579.cell d)))
    (h₂ : ∀ j, MemLp (fun x => u₂ x j) 2 (volume.restrict (B0579.cell d))) :
    velNorm d (u₁ + u₂) ≤ velNorm d u₁ + velNorm d u₂ := by
  have hm1 : MemLp (fun x => (WithLp.equiv 2 (Fin 2 → ℂ)).symm (u₁ x)) 2 (B0581.cellVol d) :=
    memLp_piLp_iff.2 h₁
  have hm2 : MemLp (fun x => (WithLp.equiv 2 (Fin 2 → ℂ)).symm (u₂ x)) 2 (B0581.cellVol d) :=
    memLp_piLp_iff.2 h₂
  by_cases hd : 0 < d
  · have : Fact (0 < d) := ⟨hd⟩
    let F₁ : Lp B0581.Vel 2 (B0581.cellVol d) := hm1.toLp _
    let F₂ : Lp B0581.Vel 2 (B0581.cellVol d) := hm2.toLp _
    have e1 : velNorm d u₁ = ENNReal.ofReal ‖F₁‖ := by
      rw [← CTE.velNorm_eq_lp d F₁]
      unfold velNorm; congr 1; refine Finset.sum_congr rfl fun j _ => ?_; congr 1
      exact eLpNorm_congr_ae (hm1.coeFn_toLp.symm.mono fun x hx =>
        congrArg (fun v : B0581.Vel => v j) hx)
    have e2 : velNorm d u₂ = ENNReal.ofReal ‖F₂‖ := by
      rw [← CTE.velNorm_eq_lp d F₂]
      unfold velNorm; congr 1; refine Finset.sum_congr rfl fun j _ => ?_; congr 1
      exact eLpNorm_congr_ae (hm2.coeFn_toLp.symm.mono fun x hx =>
        congrArg (fun v : B0581.Vel => v j) hx)
    have e12 : velNorm d (u₁ + u₂) = ENNReal.ofReal ‖F₁ + F₂‖ := by
      rw [← CTE.velNorm_eq_lp d (F₁ + F₂)]
      unfold velNorm; congr 1; refine Finset.sum_congr rfl fun j _ => ?_; congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_add F₁ F₂, hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx h1x h2x
      have hj : ((F₁ + F₂ : Lp B0581.Vel 2 (B0581.cellVol d)) x).ofLp j =
          (F₁ x).ofLp j + (F₂ x).ofLp j :=
        congrArg (fun v : B0581.Vel => v.ofLp j) hx
      have hj1 : (F₁ x).ofLp j = u₁ x j := congrArg (fun v : B0581.Vel => v.ofLp j) h1x
      have hj2 : (F₂ x).ofLp j = u₂ x j := congrArg (fun v : B0581.Vel => v.ofLp j) h2x
      show u₁ x j + u₂ x j = ((F₁ + F₂ : Lp B0581.Vel 2 (B0581.cellVol d)) x).ofLp j
      rw [hj, hj1, hj2]
    rw [e1, e2, e12, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  · have hcell : B0579.cell d = ∅ := by
      ext x
      simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩; linarith
    simp [velNorm, hcell]

private lemma velNorm_symOddVel_le {d : ℝ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell d))) :
    velNorm d (symOddVel u) ≤ velNorm d u := by
  let u_neg : ℝ × ℝ → Fin 2 → ℂ := fun x j => -u (-x) j
  have hu_neg_mem : ∀ j, MemLp (fun x => u_neg x j) 2 (volume.restrict (B0579.cell d)) :=
    fun j => (memLp_and_eLpNorm_comp_neg_vol (hu j)).1.neg
  have hu_neg_nrm : velNorm d u_neg = velNorm d u := by
    unfold velNorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    dsimp [u_neg]
    rw [show (fun x => -u (-x) j) = -(fun x => u (-x) j) from rfl, eLpNorm_neg,
      (memLp_and_eLpNorm_comp_neg_vol (hu j)).2]
  have heq : symOddVel u = fun x j => (2 : ℂ)⁻¹ * (u + u_neg) x j := by
    funext x j
    unfold symOddVel
    simp [u_neg, Pi.add_apply, sub_eq_add_neg]
  rw [heq, velNorm_smul]
  have hnorm_half : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hnorm_half]
  calc ENNReal.ofReal (1 / 2) * velNorm d (u + u_neg)
      ≤ ENNReal.ofReal (1 / 2) * (velNorm d u + velNorm d u_neg) :=
        mul_le_mul_of_nonneg_left (velNorm_add_le hu hu_neg_mem) zero_le
    _ = ENNReal.ofReal (1 / 2) * (velNorm d u + velNorm d u) := by rw [hu_neg_nrm]
    _ = (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2)) * velNorm d u := by ring
    _ = velNorm d u := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

private lemma kinNorm_eq_velNorm {d : ℝ} (hd : 0 < d) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hu : IsBiotSavart d f u) :
    kinNorm d f = velNorm d u := by
  apply le_antisymm (iInf₂_le u hu)
  refine le_iInf₂ fun v hv => le_of_eq ?_
  unfold velNorm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [CTE.isBiotSavart_unique d hd f u v hu hv] with x hx
  rw [hx]

private lemma memLp_and_eLpNorm_rescaleVel {a d : ℝ} (ha : 0 < a)
    {u : ℝ × ℝ → Fin 2 → ℂ} (j : Fin 2)
    (hu : MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a)))) :
    MemLp (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) =
        ENNReal.ofReal a *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have ha32_nn : 0 ≤ a ^ (3 / 2 : ℝ) := Real.rpow_nonneg ha.le _
  have hind_aesm : AEStronglyMeasurable
      ((B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j)) volume :=
    (aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell _)).2 hu.1
  have hcomp_aesm : AEStronglyMeasurable
      (fun y : ℝ × ℝ =>
        (B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j) (Real.sqrt a • y)) volume :=
    hind_aesm.comp_quasiMeasurePreserving (qmp_sqrt_smul ha)
  have hind_eq : (fun y : ℝ × ℝ =>
        (B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j) (Real.sqrt a • y)) =
      (B0579.cell d).indicator (fun y => u (Real.sqrt a • y) j) := by
    funext y
    by_cases hy : y ∈ B0579.cell d
    · have hy' := (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp [hy, hy']
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [hy, hy']
  rw [hind_eq] at hcomp_aesm
  have hu_comp_aesm : AEStronglyMeasurable (fun y => u (Real.sqrt a • y) j)
      (volume.restrict (B0579.cell d)) :=
    (aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell d)).1 hcomp_aesm
  have hsc_aesm : AEStronglyMeasurable (fun y => rescaleVel a u y j)
      (volume.restrict (B0579.cell d)) :=
    hu_comp_aesm.const_mul _
  set H : ℝ × ℝ → ℝ≥0∞ :=
    (B0579.cell (d * Real.sqrt a)).indicator (fun x => ‖u x j‖ₑ ^ 2)
  have hH_aem : AEMeasurable H volume :=
    (aemeasurable_indicator_iff (B0579.measurableSet_cell _)).2 (hu.1.enorm.pow_const 2)
  have hpt : ∀ y : ℝ × ℝ,
      (B0579.cell d).indicator (fun y => ‖rescaleVel a u y j‖ₑ ^ 2) y =
        ENNReal.ofReal (a ^ 3) * H (Real.sqrt a • y) := by
    intro y
    have hpow_a : (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
      rw [← Real.rpow_natCast (a ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul ha.le]
      norm_num
    by_cases hy : y ∈ B0579.cell d
    · have hy' := (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp only [H, hy, hy', indicator_of_mem, rescaleVel, enorm_mul,
        T07.enorm_ofReal_cast ha32_nn, mul_pow, ← ENNReal.ofReal_pow ha32_nn 2, hpow_a]
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [H, hy, hy']
  have hlint : ∫⁻ y in B0579.cell d, ‖rescaleVel a u y j‖ₑ ^ 2 =
      ENNReal.ofReal (a ^ 2) * ∫⁻ x in B0579.cell (d * Real.sqrt a), ‖u x j‖ₑ ^ 2 := by
    rw [← lintegral_indicator (B0579.measurableSet_cell d), lintegral_congr hpt,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_aemeasurable_comp_sqrt_smul ha hH_aem, ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg ha.le 3),
      show a ^ 3 * a⁻¹ = a ^ 2 by field_simp,
      lintegral_indicator (B0579.measurableSet_cell _)]
  have hnorm_eq : eLpNorm (fun y => rescaleVel a u y j) 2 (volume.restrict (B0579.cell d)) =
      ENNReal.ofReal a *
        eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
    rw [T07.eLpNorm_two_eq_lintegral, T07.eLpNorm_two_eq_lintegral, hlint,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg a) (by norm_num),
      ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    norm_num
  exact ⟨⟨hsc_aesm, hnorm_eq ▸ ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2⟩, hnorm_eq⟩

private lemma isCylTest_inv_sqrt_smul {a d : ℝ} (ha : 0 < a) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) :
    B0579.IsCylTest (d * Real.sqrt a) (fun x => ψ ((Real.sqrt a)⁻¹ • x)) ∧
      ∀ (j : Fin 2) (y : ℝ × ℝ),
        B0579.pd j (fun x => ψ ((Real.sqrt a)⁻¹ • x)) (Real.sqrt a • y) =
          (Real.sqrt a)⁻¹ * B0579.pd j ψ y := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hR_ne : Real.sqrt a ≠ 0 := hR.ne'
  obtain ⟨R, hR_band⟩ := hψ.band
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := (Real.sqrt a)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have htest : B0579.IsCylTest (d * Real.sqrt a) (fun x => ψ ((Real.sqrt a)⁻¹ • x)) := by
    refine ⟨hψ.smooth.comp L.contDiff, ?_, ⟨|R| * Real.sqrt a, ?_⟩⟩
    · intro x
      have heq : (Real.sqrt a)⁻¹ • (x.1 + d * Real.sqrt a, x.2) =
          (((Real.sqrt a)⁻¹ • x).1 + d, ((Real.sqrt a)⁻¹ • x).2) := by
        ext
        · dsimp; field_simp [hR_ne]
        · rfl
      rw [heq]
      exact hψ.periodic _
    · intro x hx
      apply hR_band
      have h1 : |R| < |(Real.sqrt a)⁻¹ * x.2| := by
        rw [abs_mul, abs_inv, abs_of_pos hR]
        calc |R| = |R| * Real.sqrt a * (Real.sqrt a)⁻¹ := by field_simp [hR_ne]
          _ < |x.2| * (Real.sqrt a)⁻¹ := mul_lt_mul_of_pos_right hx (inv_pos.2 hR)
          _ = (Real.sqrt a)⁻¹ * |x.2| := mul_comm _ _
      exact (le_abs_self R).trans_lt h1
  refine ⟨htest, fun j y => ?_⟩
  have hLy : L (Real.sqrt a • y) = y := inv_smul_smul₀ hR_ne y
  have hfderiv : HasFDerivAt (fun x => ψ ((Real.sqrt a)⁻¹ • x))
      ((fderiv ℝ ψ y).comp L) (Real.sqrt a • y) := by
    have hψ_fderiv : HasFDerivAt ψ (fderiv ℝ ψ y) (L (Real.sqrt a • y)) := by
      rw [hLy]
      exact (hψ.smooth.differentiable (by simp) y).hasFDerivAt
    exact HasFDerivAt.comp (Real.sqrt a • y) hψ_fderiv L.hasFDerivAt
  unfold B0579.pd
  rw [hfderiv.fderiv]
  simp [L, smul_eq_mul]

private lemma isBiotSavart_jscaleInv {a d : ℝ} (ha : 0 < a) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ}
    (hf : MemLp f 2 (volume.restrict (B0579.cell (d * Real.sqrt a))))
    (hu : IsBiotSavart (d * Real.sqrt a) f u) :
    IsBiotSavart d (JscaleInv a f) (rescaleVel a u) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hR_ne : Real.sqrt a ≠ 0 := hR.ne'
  have ha_pow : a ^ (3 / 2 : ℝ) * Real.sqrt a = a ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]
    norm_num
  refine ⟨fun j => (memLp_and_eLpNorm_rescaleVel ha j (hu.1 j)).1, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨hψ_sc, hpd_sc⟩ := isCylTest_inv_sqrt_smul ha hψ
    set g_div : ℝ × ℝ → ℂ := fun x =>
      u x 0 * (B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ) +
        u x 1 * (B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ)
    have hg_int : IntegrableOn g_div (B0579.cell (d * Real.sqrt a)) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 0) (hu.1 0)).add
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 1) (hu.1 1))
    obtain ⟨_, hcov⟩ := integrableOn_and_integral_comp_sqrt_smul ha hg_int
    have hpt : (fun y : ℝ × ℝ =>
          rescaleVel a u y 0 * (B0579.pd 0 ψ y : ℂ) +
            rescaleVel a u y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_div (Real.sqrt a • y) := by
      funext y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 0 y]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 1 y]; field_simp [hR_ne]
      dsimp only [rescaleVel, g_div]
      rw [hp0', hp1', ← ha_pow]
      push_cast; ring
    rw [hpt, integral_const_mul, hcov, hu.2.1 _ hψ_sc, mul_zero, mul_zero]
  · intro ψ hψ
    obtain ⟨hψ_sc, hpd_sc⟩ := isCylTest_inv_sqrt_smul ha hψ
    set g_lhs : ℝ × ℝ → ℂ := fun x => f x * (ψ ((Real.sqrt a)⁻¹ • x) : ℂ)
    set g_rhs : ℝ × ℝ → ℂ := fun x =>
      u x 0 * (B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ) -
        u x 1 * (B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ)
    have hgl_int : IntegrableOn g_lhs (B0579.cell (d * Real.sqrt a)) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hψ_sc hf
    have hgr_int : IntegrableOn g_rhs (B0579.cell (d * Real.sqrt a)) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 1) (hu.1 0)).sub
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 0) (hu.1 1))
    obtain ⟨_, hcov_l⟩ := integrableOn_and_integral_comp_sqrt_smul ha hgl_int
    obtain ⟨_, hcov_r⟩ := integrableOn_and_integral_comp_sqrt_smul ha hgr_int
    have hpt_l : (fun y : ℝ × ℝ => JscaleInv a f y * (ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_lhs (Real.sqrt a • y) := by
      funext y
      dsimp only [JscaleInv, g_lhs]
      rw [← T07.sqrt_smul_eq, inv_smul_smul₀ hR_ne]
      ring
    have hpt_r : (fun y : ℝ × ℝ =>
          rescaleVel a u y 0 * (B0579.pd 1 ψ y : ℂ) -
            rescaleVel a u y 1 * (B0579.pd 0 ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_rhs (Real.sqrt a • y) := by
      funext y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 0 y]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 1 y]; field_simp [hR_ne]
      dsimp only [rescaleVel, g_rhs]
      rw [hp0', hp1', ← ha_pow]
      push_cast; ring
    rw [hpt_l, hpt_r, integral_const_mul, integral_const_mul, hcov_l, hcov_r, hu.2.2 _ hψ_sc]

private lemma ae_smul_sqrt_of_ae {a d : ℝ} (ha : 0 < a) {f g : ℝ × ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] g) :
    (fun y => f (Real.sqrt a * y.1, Real.sqrt a * y.2)) =ᵐ[volume.restrict (B0579.cell d)]
      (fun y => g (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  rw [EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell _)] at hfg ⊢
  filter_upwards [(qmp_sqrt_smul ha).ae hfg] with y hy hyd
  simpa [T07.sqrt_smul_eq] using hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hyd)

private lemma jscaleInv_memLp {m a d : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure (d * Real.sqrt a) m)) :
    MemLp (JscaleInv a f) 2 (B0579.cellMeasure d m) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  set f₀ : ℝ × ℝ → ℂ := hf.1.mk f
  have hfm : Measurable f₀ := hf.1.stronglyMeasurable_mk.measurable
  have hae_cm : f =ᵐ[B0579.cellMeasure (d * Real.sqrt a) m] f₀ := hf.1.ae_eq_mk
  have hae_vol : f =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] f₀ :=
    (B0579.ac_cellMeasure (d * Real.sqrt a) m).ae_le hae_cm
  have hJae_vol : JscaleInv a f =ᵐ[volume.restrict (B0579.cell d)] JscaleInv a f₀ := by
    filter_upwards [ae_smul_sqrt_of_ae ha0 hae_vol] with y hy
    simp [JscaleInv, hy]
  have hJae_cm : JscaleInv a f =ᵐ[B0579.cellMeasure d m] JscaleInv a f₀ :=
    (B0579.cellMeasure_ac d m).ae_le hJae_vol
  have hsc := scalingJaInv m hm a d ha hd f₀ hfm
  have hxf : xNorm (d * Real.sqrt a) m f₀ = xNorm (d * Real.sqrt a) m f :=
    eLpNorm_congr_ae hae_cm.symm
  have hxJ : xNorm d m (JscaleInv a f) = xNorm d m (JscaleInv a f₀) :=
    eLpNorm_congr_ae hJae_cm
  have hbd : xNorm d m (JscaleInv a f) ≤
      ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm (d * Real.sqrt a) m f := by
    rw [hxJ, ← hxf]; exact hsc
  have hJ₀m : Measurable (JscaleInv a f₀) := by
    unfold JscaleInv
    exact (hfm.comp ((measurable_fst.const_mul _).prodMk (measurable_snd.const_mul _))).const_mul _
  exact ⟨hJ₀m.aestronglyMeasurable.congr hJae_cm.symm,
    lt_of_le_of_lt hbd (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)⟩

private lemma hasZeroCirculation_jscaleInv {a d : ℝ} (ha : 0 < a) {f : ℝ × ℝ → ℂ}
    (hf : HasZeroCirculation (d * Real.sqrt a) f) :
    HasZeroCirculation d (JscaleInv a f) := by
  obtain ⟨hint_comp, hval_comp⟩ := integrableOn_and_integral_comp_sqrt_smul ha hf.1
  have heq : JscaleInv a f = fun y => ((a ^ 2 : ℝ) : ℂ) * f (Real.sqrt a • y) := by
    funext y; unfold JscaleInv; rw [T07.sqrt_smul_eq]
  rw [heq]
  refine ⟨hint_comp.const_mul _, ?_⟩
  rw [integral_const_mul, hval_comp, hf.2, mul_zero, mul_zero]

private lemma hasZeroCirculation_smul {d : ℝ} (α : ℂ) {f : ℝ × ℝ → ℂ}
    (hf : HasZeroCirculation d f) :
    HasZeroCirculation d (fun x => α * f x) :=
  ⟨hf.1.const_mul α, by rw [integral_const_mul, hf.2, mul_zero]⟩

private lemma hasZeroCirculation_symEven {d : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : HasZeroCirculation d f) :
    HasZeroCirculation d (symEven f) := by
  have hint_neg : IntegrableOn (fun x => f (-x)) (B0579.cell d) :=
    (measurePreserving_neg_cell d).integrable_comp_of_integrable hf.1
  refine ⟨(hf.1.add hint_neg).const_mul (2 : ℂ)⁻¹, ?_⟩
  unfold symEven
  rw [integral_const_mul, integral_add hf.1 hint_neg, integral_cell_neg d f, hf.2]
  ring

private lemma isLinearisedFlow_restart {ν c m t₀ t₁ : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f₀ : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t₀ f₀ w u) (ht : t₀ ≤ t₁) :
    IsLinearisedFlow ν c m tr t₁ (w t₁) w u where
  initial := EventuallyEq.refl _ _
  memX s hs := hw.memX s (ht.trans hs)
  strongCont s hs :=
    (hw.strongCont s (ht.trans hs)).mono_left (nhdsWithin_mono s (Ici_subset_Ici.2 ht))
  biotSavart s hs := hw.biotSavart s (ht.trans hs)
  integrable φ hφ τ hτ := hw.integrable φ hφ τ (ht.trans hτ)
  timeIntegrable φ hφ s hs := by
    refine (hw.timeIntegrable φ hφ s (ht.trans hs)).mono_set ?_
    rw [uIcc_of_le hs, uIcc_of_le (ht.trans hs)]
    exact Icc_subset_Icc_left ht
  weak φ hφ s hs := by
    have hti₁ : IntervalIntegrable
        (fun τ => ∫ x in B0579.cell c, flowIntegrand tr (w τ) (u τ) τ φ x) volume t₀ t₁ :=
      hw.timeIntegrable φ hφ t₁ ht
    have hti₂ : IntervalIntegrable
        (fun τ => ∫ x in B0579.cell c, flowIntegrand tr (w τ) (u τ) τ φ x) volume t₁ s := by
      refine (hw.timeIntegrable φ hφ s (ht.trans hs)).mono_set ?_
      rw [uIcc_of_le hs, uIcc_of_le (ht.trans hs)]
      exact Icc_subset_Icc_left ht
    have hadj := intervalIntegral.integral_add_adjacent_intervals hti₁ hti₂
    have hw_s := hw.weak φ hφ s (ht.trans hs)
    have hw_t₁ := hw.weak φ hφ t₁ ht
    rw [hw_s, hw_t₁, ← hadj, add_assoc]

private lemma isLinearisedFlow_smul {ν c m t₀ : ℝ} (α : ℂ)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t₀ f w u) :
    IsLinearisedFlow ν c m tr t₀ (fun x => α * f x) (fun s x => α * w s x)
      (fun s x j => α * u s x j) where
  initial := hw.initial.mono fun x hx => by dsimp only; rw [hx]
  memX s hs := (hw.memX s hs).const_mul α
  strongCont s hs := by
    have hlim := ENNReal.Tendsto.const_mul (a := ‖α‖ₑ) (hw.strongCont s hs)
      (Or.inr ENNReal.coe_ne_top)
    rw [mul_zero] at hlim
    refine hlim.congr' (Eventually.of_forall fun s' => ?_)
    have heq : ((fun x => α * w s' x) - fun x => α * w s x) = α • (w s' - w s) := by
      ext x; simp [mul_sub]
    dsimp only
    unfold xNorm
    rw [heq, eLpNorm_const_smul]
  biotSavart s hs := isBiotSavart_smul α (hw.biotSavart s hs)
  integrable φ hφ r hr := by
    have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
        fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq]
    exact (hw.integrable φ hφ r hr).const_mul α
  timeIntegrable φ hφ s hs := by
    refine ((hw.timeIntegrable φ hφ s hs).const_mul α).congr fun r _ => ?_
    have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
        fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq, integral_const_mul]
  weak φ hφ s hs := by
    have hl : (fun x => α * w s x * (φ x : ℂ)) = fun x => α * (w s x * (φ x : ℂ)) := by
      funext x; ring
    have hf_eq : (fun x => α * f x * (φ x : ℂ)) = fun x => α * (f x * (φ x : ℂ)) := by
      funext x; ring
    have hr_eq : (∫ r in t₀..s, ∫ x in B0579.cell c,
        flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ x) =
        α * ∫ r in t₀..s, ∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r φ x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
          fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
        funext x; unfold flowIntegrand; ring
      rw [heq, integral_const_mul]
    rw [hl, integral_const_mul, hf_eq, integral_const_mul, hr_eq, ← mul_add, hw.weak φ hφ s hs]

private lemma isLinearisedFlow_refl_neg {ν c m t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t₀ f w u) :
    IsLinearisedFlow ν c m tr t₀ (fun x => f (-x)) (fun s x => w s (-x))
      (fun s x j => -u s (-x) j) := by
  let w' : ℝ → ℝ × ℝ → ℂ := fun τ x => w τ (-x)
  let u' : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun τ x j => -u τ (-x) j
  have hlap_neg : ∀ (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ), lapP (fun y => ψ (-y)) x = lapP ψ (-x) := by
    intro ψ x
    unfold lapP
    have e0 : B0579.pd 0 (fun y => ψ (-y)) = fun y => -B0579.pd 0 ψ (-y) :=
      funext (pd_comp_neg_any ψ 0)
    have e1 : B0579.pd 1 (fun y => ψ (-y)) = fun y => -B0579.pd 1 ψ (-y) :=
      funext (pd_comp_neg_any ψ 1)
    rw [e0, e1, pd_neg_any, pd_neg_any, pd_comp_neg_any (B0579.pd 0 ψ) 0 x,
      pd_comp_neg_any (B0579.pd 1 ψ) 1 x, neg_neg, neg_neg]
  have hpdE_odd : ∀ r : ℝ, 0 ≤ r → ∀ (j : Fin 2) (x : ℝ × ℝ),
      B0579.pd j (UnforcedLeray.B0238.Ec tr r) (-x) =
        -B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by
    intro r hr j x
    have heven : (fun y => UnforcedLeray.B0238.Ec tr r (-y)) = UnforcedLeray.B0238.Ec tr r :=
      funext (UnforcedLeray.B0238.Ec_even tr hr)
    have h1 := pd_comp_neg_any (UnforcedLeray.B0238.Ec tr r) j x
    rw [heven] at h1
    linarith
  have hfl_eq : ∀ (ψ : ℝ × ℝ → ℝ) (r : ℝ), t₀ ≤ r → ∀ x : ℝ × ℝ,
      flowIntegrand tr (w' r) (u' r) r ψ x =
        flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) := by
    intro ψ r hr x
    have hr0 : 0 ≤ r := ht₀.trans hr
    have p0 := pd_comp_neg_any ψ 0 (-x)
    have p1 := pd_comp_neg_any ψ 1 (-x)
    have pl := hlap_neg ψ (-x)
    rw [neg_neg] at p0 p1 pl
    have hv_odd : ∀ j : Fin 2, tr.v r (-x) j = -tr.v r x j := fun j => by
      have h := congrArg (fun v : UnforcedLeray.Train.Vec => v j) (tr.isTrain.odd r hr0 x)
      simpa using h
    have eE0 := hpdE_odd r hr0 0 x
    have eE1 := hpdE_odd r hr0 1 x
    unfold flowIntegrand
    dsimp only [w', u']
    rw [p0, p1, pl, hv_odd 0, hv_odd 1, eE0, eE1, neg_neg]
    push_cast
    ring
  refine ⟨ae_neg_of_ae_cell hw.initial, fun s hs => memLp_comp_neg_cellMeasure (hw.memX s hs),
    ?_, fun s hs => isBiotSavart_refl_neg (hw.biotSavart s hs), ?_, ?_, ?_⟩
  · intro s hs
    refine (hw.strongCont s hs).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' _
    have heq : w' s' - w' s = fun x => (w s' - w s) (-x) := rfl
    rw [heq, xNorm_comp_neg_cellMeasure]
  · intro ψ hψ r hr
    have hψn := isCylTest_neg hψ
    have hInt : Integrable (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))
        (volume.restrict (B0579.cell c)) := hw.integrable _ hψn r hr
    exact ((measurePreserving_neg_cell c).integrable_comp_of_integrable hInt).congr
      (Eventually.of_forall fun x => (hfl_eq ψ r hr x).symm)
  · intro ψ hψ s hs
    have hψn := isCylTest_neg hψ
    refine (hw.timeIntegrable _ hψn s hs).congr fun r hr => ?_
    rw [uIoc_of_le hs] at hr
    have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
        fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
      funext (hfl_eq ψ r hr.1.le)
    rw [heq_r, integral_cell_neg c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
  · intro ψ hψ s hs
    have hψn := isCylTest_neg hψ
    have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
        ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
          fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp [w']
      rw [hp]
      exact integral_cell_neg c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
    have hf_int : ∫ x in B0579.cell c, f (-x) * (ψ x : ℂ) =
        ∫ y in B0579.cell c, f y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun x : ℝ × ℝ => f (-x) * (ψ x : ℂ)) =
          fun x => f (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp
      rw [hp]
      exact integral_cell_neg c (fun y => f y * ((fun z => ψ (-z)) y : ℂ))
    have hr_int : ∫ r in t₀..s, (∫ x in B0579.cell c, flowIntegrand tr (w' r) (u' r) r ψ x) =
        ∫ r in t₀..s, (∫ y in B0579.cell c,
          flowIntegrand tr (w r) (u r) r (fun z => ψ (-z)) y) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs] at hr
        have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
            fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
          funext (hfl_eq ψ r hr.1)
        rw [heq_r, integral_cell_neg c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
    rw [hl, hf_int, hr_int, hw.weak _ hψn s hs]

private lemma memLp_vol_of_cellMeasure {c m : ℝ} (hm : 0 ≤ m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    MemLp f 2 (volume.restrict (B0579.cell c)) := by
  have haesm : AEStronglyMeasurable f (volume.restrict (B0579.cell c)) :=
    hf.1.mono_ac (B0579.ac_cellMeasure c m)
  refine ⟨haesm, ?_⟩
  rw [T07.eLpNorm_two_eq_lintegral]
  have hle : ∫⁻ x in B0579.cell c, ‖f x‖ₑ ^ 2 ≤
      ∫⁻ x in B0579.cell c, ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x‖ₑ ^ 2 := by
    refine lintegral_mono fun x => ?_
    have hjb1 : 1 ≤ B0579.jb x := by
      unfold B0579.jb
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hrpow1 : (1 : ℝ) ≤ B0579.jb x ^ (m / 2) :=
      Real.one_le_rpow hjb1 (by positivity)
    have henorm1 : (1 : ℝ≥0∞) ≤ ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ)‖ₑ := by
      rw [T07.enorm_ofReal_cast (by linarith)]
      exact ENNReal.one_le_ofReal.2 hrpow1
    rw [enorm_mul, mul_pow]
    calc ‖f x‖ₑ ^ 2 = 1 * ‖f x‖ₑ ^ 2 := (one_mul _).symm
      _ ≤ ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ)‖ₑ ^ 2 * ‖f x‖ₑ ^ 2 :=
          mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_left' henorm1 2) zero_le
  have hfin : (∫⁻ x in B0579.cell c,
      ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) < ⊤ := by
    rw [← T07.eLpNorm_two_eq_lintegral, ← eLpNorm_cellMeasure_cx]
    exact hf.2
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  intro htop
  rw [htop] at hle
  have htop2 : ∫⁻ x in B0579.cell c,
      ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x‖ₑ ^ 2 = ⊤ := top_unique hle
  rw [htop2, ENNReal.top_rpow_of_pos (by norm_num)] at hfin
  exact lt_irrefl ⊤ hfin

private lemma isLinearisedFlow_add {ν c m t₀ : ℝ} (hm : 1 < m)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f₁ f₂ : ℝ × ℝ → ℂ}
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure c m)) (hf₂ : MemLp f₂ 2 (B0579.cellMeasure c m))
    {w₁ w₂ : ℝ → ℝ × ℝ → ℂ} {u₁ u₂ : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw₁ : IsLinearisedFlow ν c m tr t₀ f₁ w₁ u₁)
    (hw₂ : IsLinearisedFlow ν c m tr t₀ f₂ w₂ u₂) :
    IsLinearisedFlow ν c m tr t₀ (f₁ + f₂) (fun s => w₁ s + w₂ s)
      (fun s => u₁ s + u₂ s) where
  initial := hw₁.initial.add hw₂.initial
  memX s hs := (hw₁.memX s hs).add (hw₂.memX s hs)
  strongCont s hs := by
    have hsum : Tendsto (fun s' => xNorm c m (w₁ s' - w₁ s) + xNorm c m (w₂ s' - w₂ s))
        (𝓝[Ici t₀] s) (𝓝 0) := by
      simpa using (hw₁.strongCont s hs).add (hw₂.strongCont s hs)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    have heq : (w₁ s' + w₂ s') - (w₁ s + w₂ s) = (w₁ s' - w₁ s) + (w₂ s' - w₂ s) := by
      ext x; simp [Pi.add_apply, Pi.sub_apply]; ring
    unfold xNorm
    rw [heq]
    exact eLpNorm_add_le
      ((hw₁.memX s' hs').sub (hw₁.memX s hs)).1
      ((hw₂.memX s' hs').sub (hw₂.memX s hs)).1 (by norm_num)
  biotSavart s hs := isBiotSavart_add hm (hw₁.memX s hs) (hw₂.memX s hs)
    (hw₁.biotSavart s hs) (hw₂.biotSavart s hs)
  integrable φ hφ r hr := by
    have heq : flowIntegrand tr (w₁ r + w₂ r) (u₁ r + u₂ r) r φ =
        flowIntegrand tr (w₁ r) (u₁ r) r φ + flowIntegrand tr (w₂ r) (u₂ r) r φ := by
      funext x; unfold flowIntegrand; simp [Pi.add_apply]; ring
    rw [heq]
    exact (hw₁.integrable φ hφ r hr).add (hw₂.integrable φ hφ r hr)
  timeIntegrable φ hφ s hs := by
    refine ((hw₁.timeIntegrable φ hφ s hs).add (hw₂.timeIntegrable φ hφ s hs)).congr fun r hr => ?_
    rw [uIoc_of_le hs] at hr
    have heq : (fun x => flowIntegrand tr (w₁ r + w₂ r) (u₁ r + u₂ r) r φ x) =
        fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x + flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
      funext x; unfold flowIntegrand; simp [Pi.add_apply]; ring
    rw [heq, integral_add (hw₁.integrable φ hφ r hr.1.le) (hw₂.integrable φ hφ r hr.1.le)]
  weak φ hφ s hs := by
    have hm0 : 0 ≤ m := by linarith
    have hl₁ : IntegrableOn (fun x => w₁ s x * (φ x : ℂ)) (B0579.cell c) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hφ (memLp_vol_of_cellMeasure hm0 (hw₁.memX s hs))
    have hl₂ : IntegrableOn (fun x => w₂ s x * (φ x : ℂ)) (B0579.cell c) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hφ (memLp_vol_of_cellMeasure hm0 (hw₂.memX s hs))
    have hf₁_int : IntegrableOn (fun x => f₁ x * (φ x : ℂ)) (B0579.cell c) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hφ (memLp_vol_of_cellMeasure hm0 hf₁)
    have hf₂_int : IntegrableOn (fun x => f₂ x * (φ x : ℂ)) (B0579.cell c) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hφ (memLp_vol_of_cellMeasure hm0 hf₂)
    have hpt_w : (fun x : B0579.Plane => (w₁ s + w₂ s) x * (φ x : ℂ)) =
        fun x => w₁ s x * (φ x : ℂ) + w₂ s x * (φ x : ℂ) := by
      funext x; simp [Pi.add_apply, add_mul]
    have hpt_f : (fun x : B0579.Plane => (f₁ + f₂) x * (φ x : ℂ)) =
        fun x => f₁ x * (φ x : ℂ) + f₂ x * (φ x : ℂ) := by
      funext x; simp [Pi.add_apply, add_mul]
    have htime_eq : (∫ r in t₀..s, ∫ x in B0579.cell c,
          flowIntegrand tr (w₁ r + w₂ r) (u₁ r + u₂ r) r φ x) =
        (∫ r in t₀..s, ∫ x in B0579.cell c, flowIntegrand tr (w₁ r) (u₁ r) r φ x) +
          (∫ r in t₀..s, ∫ x in B0579.cell c, flowIntegrand tr (w₂ r) (u₂ r) r φ x) := by
      rw [← intervalIntegral.integral_add (hw₁.timeIntegrable φ hφ s hs)
        (hw₂.timeIntegrable φ hφ s hs)]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs] at hr
      have heq : (fun x => flowIntegrand tr (w₁ r + w₂ r) (u₁ r + u₂ r) r φ x) =
          fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x + flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
        funext x; unfold flowIntegrand; simp [Pi.add_apply]; ring
      rw [heq, integral_add (hw₁.integrable φ hφ r hr.1) (hw₂.integrable φ hφ r hr.1)]
    rw [hpt_w, integral_add hl₁ hl₂, hpt_f, integral_add hf₁_int hf₂_int, htime_eq,
      hw₁.weak φ hφ s hs, hw₂.weak φ hφ s hs]
    ring

private lemma isLinearisedFlow_symm {ν c m t₀ : ℝ} (hm : 1 < m) (ht₀ : 0 ≤ t₀)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c m))
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t₀ f w u) :
    IsLinearisedFlow ν c m tr t₀ (symEven f) (fun s => symEven (w s))
      (fun s => symOddVel (u s)) := by
  have hw_neg := isLinearisedFlow_refl_neg ht₀ hw
  have hf_neg := memLp_comp_neg_cellMeasure hf
  have hw_sum := isLinearisedFlow_add hm hf hf_neg hw hw_neg
  have hw_half := isLinearisedFlow_smul (2 : ℂ)⁻¹ hw_sum
  have heq_f : (fun x => (2 : ℂ)⁻¹ * (f + fun y => f (-y)) x) = symEven f := rfl
  have heq_w : (fun s x => (2 : ℂ)⁻¹ * (w s + fun y => w s (-y)) x) =
      fun s => symEven (w s) := rfl
  have heq_u : (fun s x j => (2 : ℂ)⁻¹ * (u s + fun y k => -u s (-y) k) x j) =
      fun s => symOddVel (u s) := by
    funext s x j
    simp [symOddVel, Pi.add_apply, sub_eq_add_neg]
  rwa [heq_f, heq_w, heq_u] at hw_half

private lemma jscale_jscaleInv {a : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) :
    Jscale a (JscaleInv a f) = f := by
  funext x
  unfold Jscale JscaleInv
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hcoord : (Real.sqrt a * (x.1 / Real.sqrt a), Real.sqrt a * (x.2 / Real.sqrt a)) = x := by
    ext <;> simp [mul_div_cancel₀ _ hsq]
  have hpow : (a ^ (-2 : ℝ) : ℝ) * a ^ 2 = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')]
  dsimp only
  rw [hcoord]
  calc ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (((a ^ 2 : ℝ) : ℂ) * f x)
      = (((a ^ (-2 : ℝ) * a ^ 2 : ℝ)) : ℂ) * f x := by push_cast; ring
    _ = f x := by rw [hpow, Complex.ofReal_one, one_mul]

private lemma heatColumn_memLp (P : PlanarData) {ν m θ : ℝ} (hm : 0 ≤ m)
    (hν : 0 < ν) (hθ : 0 < θ) (hθν : θ ≤ ν⁻¹)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w u) :
    MemLp (heatColumn P ν w θ) 2 (B0579.cellMeasure (dOfTheta ν θ) m) := by
  have hs0 : 0 ≤ clockAge ν θ := T22Sub.clockAge_nonneg hν hθ hθν
  have ha1 : 1 ≤ (ν * θ)⁻¹ := by
    rw [one_le_inv₀ (mul_pos hν hθ)]
    calc ν * θ ≤ ν * ν⁻¹ := mul_le_mul_of_nonneg_left hθν hν.le
      _ = 1 := mul_inv_cancel₀ hν.ne'
  have hd0 : 0 < dOfTheta ν θ := by unfold dOfTheta; positivity
  have hdc : dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹) = ν ^ (-2 : ℝ) := dOfTheta_mul_sqrt_inv hν hθ
  have hmem : MemLp (w (clockAge ν θ)) 2
      (B0579.cellMeasure (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹)) m) :=
    hdc.symm ▸ hw.memX (clockAge ν θ) hs0
  unfold heatColumn
  exact (jscaleInv_memLp hm ha1 hd0 hmem).const_mul (P.gaugeFactor ν)⁻¹

private lemma heatColumn_isBiotSavart (P : PlanarData) {ν m θ : ℝ} (hm : 0 ≤ m)
    (hν : 0 < ν) (hθ : 0 < θ) (hθν : θ ≤ ν⁻¹)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w u) :
    IsBiotSavart (dOfTheta ν θ) (heatColumn P ν w θ)
      (fun y j => (P.gaugeFactor ν)⁻¹ * rescaleVel (ν * θ)⁻¹ (u (clockAge ν θ)) y j) := by
  have hs0 : 0 ≤ clockAge ν θ := T22Sub.clockAge_nonneg hν hθ hθν
  have ha : 0 < (ν * θ)⁻¹ := inv_pos.2 (mul_pos hν hθ)
  have hdc : dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹) = ν ^ (-2 : ℝ) := dOfTheta_mul_sqrt_inv hν hθ
  have hvol : MemLp (w (clockAge ν θ)) 2
      (volume.restrict (B0579.cell (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹)))) :=
    hdc.symm ▸ memLp_vol_of_cellMeasure hm (hw.memX (clockAge ν θ) hs0)
  have hbs : IsBiotSavart (dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹))
      (w (clockAge ν θ)) (u (clockAge ν θ)) :=
    hdc.symm ▸ hw.biotSavart (clockAge ν θ) hs0
  unfold heatColumn
  exact isBiotSavart_smul (P.gaugeFactor ν)⁻¹ (isBiotSavart_jscaleInv ha hvol hbs)

private lemma heatColumn_symEven_package {P : PlanarData} (hP : IsPlanarReference P)
    {ν m r : ℝ} (hm : 8 < m) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hr0 : 0 < r) (hrν : r ≤ ν⁻¹)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u) :
    let h := symEven (heatColumn P ν w r)
    let Zh := fun θ => symEven (heatColumn P ν w θ)
    MemLp h 2 (B0579.cellMeasure (dOfTheta ν r) m) ∧
      HasZeroCirculation (dOfTheta ν r) h ∧
      IsCentrallyEven h ∧
      quadQ (dOfTheta ν r) h = quadQ (dOfTheta ν r) (heatColumn P ν w r) ∧
      kinNorm (dOfTheta ν r) h ≤ kinNorm (dOfTheta ν r) (heatColumn P ν w r) ∧
      (∀ θ ∈ Ioc 0 r, quadQ (dOfTheta ν θ) (Zh θ) =
        quadQ (dOfTheta ν θ) (heatColumn P ν w θ)) ∧
      (∀ θ ∈ Ioc 0 r, HeatEvolvesTo ν m tr r θ h (Zh θ)) := by
  have hm0 : 0 ≤ m := by linarith
  have hm1 : 1 < m := by linarith
  have hm3 : 3 < m := by linarith
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    rw [Real.rpow_neg hν0.le, one_le_inv₀ (Real.rpow_pos_of_pos hν0 2), Real.rpow_two]
    exact pow_le_one₀ hν0.le hν1
  have hs_r0 : 0 ≤ clockAge ν r := T22Sub.clockAge_nonneg hν0 hr0 hrν
  have ha_r : 0 < (ν * r)⁻¹ := inv_pos.2 (mul_pos hν0 hr0)
  have hd_r0 : 0 < dOfTheta ν r := by unfold dOfTheta; positivity
  have hdc_r : dOfTheta ν r * Real.sqrt ((ν * r)⁻¹) = c := dOfTheta_mul_sqrt_inv hν0 hr0
  have hZr_mem : MemLp (heatColumn P ν w r) 2 (B0579.cellMeasure (dOfTheta ν r) m) :=
    heatColumn_memLp P hm0 hν0 hr0 hrν hw
  have hh_mem : MemLp (symEven (heatColumn P ν w r)) 2 (B0579.cellMeasure (dOfTheta ν r) m) :=
    ((hZr_mem.add (memLp_comp_neg_cellMeasure hZr_mem)).const_mul (2 : ℂ)⁻¹)
  obtain ⟨_, hprep_zc, _⟩ := (T22Sub.ctCanonicalBranchProps P hP m hm).1 ν ⟨hν0, hν1⟩
  have hws_zc : HasZeroCirculation c (w (clockAge ν r)) :=
    ladFlowZeroCirc m hm1 ν c tr 0 (preparedDatum P ν) w u hc1 hprep_zc hw (clockAge ν r) hs_r0
  have hZr_zc : HasZeroCirculation (dOfTheta ν r) (heatColumn P ν w r) :=
    hasZeroCirculation_smul (P.gaugeFactor ν)⁻¹
      (hasZeroCirculation_jscaleInv ha_r (hdc_r.symm ▸ hws_zc))
  have hh_zc : HasZeroCirculation (dOfTheta ν r) (symEven (heatColumn P ν w r)) :=
    hasZeroCirculation_symEven hZr_zc
  have hh_ev : IsCentrallyEven (symEven (heatColumn P ν w r)) :=
    isCentrallyEven_symEven _
  have hh_quad : quadQ (dOfTheta ν r) (symEven (heatColumn P ν w r)) =
      quadQ (dOfTheta ν r) (heatColumn P ν w r) :=
    quadQ_symEven_eq hm3 hZr_mem
  have hZr_bs := heatColumn_isBiotSavart P hm0 hν0 hr0 hrν hw
  have hh_bs : IsBiotSavart (dOfTheta ν r) (symEven (heatColumn P ν w r))
      (symOddVel (fun y j => (P.gaugeFactor ν)⁻¹ * rescaleVel (ν * r)⁻¹ (u (clockAge ν r)) y j)) := by
    have hbs_neg := isBiotSavart_refl_neg hZr_bs
    have hbs_sum := isBiotSavart_add hm1 hZr_mem (memLp_comp_neg_cellMeasure hZr_mem)
      hZr_bs hbs_neg
    have hbs_half := isBiotSavart_smul (2 : ℂ)⁻¹ hbs_sum
    refine isBiotSavart_congr_ae hbs_half (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun x => ?_)
    funext j
    simp [symOddVel, Pi.add_apply, sub_eq_add_neg]
  have hh_kin : kinNorm (dOfTheta ν r) (symEven (heatColumn P ν w r)) ≤
      kinNorm (dOfTheta ν r) (heatColumn P ν w r) := by
    rw [kinNorm_eq_velNorm hd_r0 hh_bs, kinNorm_eq_velNorm hd_r0 hZr_bs]
    exact velNorm_symOddVel_le hZr_bs.1
  have hZθ_quad : ∀ θ ∈ Ioc 0 r,
      quadQ (dOfTheta ν θ) (symEven (heatColumn P ν w θ)) =
        quadQ (dOfTheta ν θ) (heatColumn P ν w θ) := by
    intro θ hθ
    exact quadQ_symEven_eq hm3 (heatColumn_memLp P hm0 hν0 hθ.1 (hθ.2.trans hrν) hw)
  have hEvol : ∀ θ ∈ Ioc 0 r,
      HeatEvolvesTo ν m tr r θ (symEven (heatColumn P ν w r))
        (symEven (heatColumn P ν w θ)) := by
    intro θ _
    have hw_rest := isLinearisedFlow_restart hw hs_r0
    have hw_sc := isLinearisedFlow_smul (P.gaugeFactor ν)⁻¹ hw_rest
    have hf_sc_mem : MemLp (fun x => (P.gaugeFactor ν)⁻¹ * w (clockAge ν r) x) 2
        (B0579.cellMeasure c m) :=
      (hw.memX (clockAge ν r) hs_r0).const_mul (P.gaugeFactor ν)⁻¹
    have hw_sym := isLinearisedFlow_symm hm1 hs_r0 hf_sc_mem hw_sc
    have hinit_eq : Jscale (ν * r)⁻¹ (symEven (heatColumn P ν w r)) =
        symEven (fun x => (P.gaugeFactor ν)⁻¹ * w (clockAge ν r) x) := by
      have hcomm : symEven (heatColumn P ν w r) =
          JscaleInv (ν * r)⁻¹ (symEven (fun x => (P.gaugeFactor ν)⁻¹ * w (clockAge ν r) x)) := by
        funext y
        unfold symEven heatColumn JscaleInv
        have hneg : (Real.sqrt (ν * r)⁻¹ * (-y).1, Real.sqrt (ν * r)⁻¹ * (-y).2) =
            -(Real.sqrt (ν * r)⁻¹ * y.1, Real.sqrt (ν * r)⁻¹ * y.2) := by
          ext <;> simp
        rw [hneg]
        ring
      rw [hcomm, jscale_jscaleInv ha_r]
    refine ⟨fun s => symEven (fun x => (P.gaugeFactor ν)⁻¹ * w s x),
      fun s => symOddVel (fun x j => (P.gaugeFactor ν)⁻¹ * u s x j), ?_, ?_⟩
    · rw [hinit_eq]
      exact hw_sym
    · funext y
      unfold symEven heatColumn JscaleInv
      have hneg : (Real.sqrt (ν * θ)⁻¹ * (-y).1, Real.sqrt (ν * θ)⁻¹ * (-y).2) =
          -(Real.sqrt (ν * θ)⁻¹ * y.1, Real.sqrt (ν * θ)⁻¹ * y.2) := by
        ext <;> simp
      rw [hneg]
      ring
  exact ⟨hh_mem, hh_zc, hh_ev, hh_quad, hh_kin, hZθ_quad, hEvol⟩

/-! ## Section 3: Canonical branch majorant `gCan` and exponential tail integrability -/

private def gCan (P : PlanarData) (θ : ℝ) : ℝ :=
  (θ ^ (1 / 2 : ℝ) + θ ^ (3 / 4 : ℝ)) * ‖quadrupole (P.canonical θ)‖

private lemma gCan_nonneg (P : PlanarData) {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ gCan P θ := by
  unfold gCan
  positivity

private lemma aesm_quadrupole_canonical {P : PlanarData} (hP : IsPlanarReference P) :
    AEStronglyMeasurable (fun θ => quadrupole (P.canonical θ)) (volume.restrict (Ioi 0)) := by
  have hint := hP.mellin_integrable (1 / 2) (by norm_num)
  have hc_inv : ContinuousOn (fun θ : ℝ => (((θ ^ (1 : ℝ))⁻¹ : ℝ) : ℂ)) (Ioi 0) := by
    intro θ hθ
    rw [mem_Ioi] at hθ
    have hpow : ContinuousAt (fun t : ℝ => t ^ (1 : ℝ)) θ :=
      ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inl hθ.ne')
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hpow.inv₀ (Real.rpow_pos_of_pos hθ 1).ne')).continuousWithinAt
  have haesm_inv : AEStronglyMeasurable (fun θ : ℝ => (((θ ^ (1 : ℝ))⁻¹ : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) :=
    hc_inv.aestronglyMeasurable measurableSet_Ioi
  have hprod := haesm_inv.mul hint.1
  refine hprod.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
  rw [mem_Ioi] at hθ
  have h12 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  dsimp only [Pi.mul_apply]
  rw [h12, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hθ 1).ne', Complex.ofReal_one, one_mul]

private lemma integrableOn_gCan {P : PlanarData} (hP : IsPlanarReference P) :
    IntegrableOn (gCan P) (Ioi 0) := by
  have h0 := (hP.mellin_integrable 0 (by norm_num)).norm
  have h14 := (hP.mellin_integrable (1 / 4) (by norm_num)).norm
  refine IntegrableOn.congr_fun (h0.add h14) (fun θ hθ => ?_) measurableSet_Ioi
  rw [mem_Ioi] at hθ
  have e0 : (0 : ℝ) + 1 / 2 = 1 / 2 := by norm_num
  have e14 : (1 / 4 : ℝ) + 1 / 2 = 3 / 4 := by norm_num
  simp only [Pi.add_apply, e0, e14, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hθ _)]
  unfold gCan
  ring

private lemma norm_fCan_le_gCan (P : PlanarData) {θ : ℝ} (hθ : 0 < θ) {μ : ℂ}
    (hμ0 : 0 < μ.re) (hμ1 : μ.re < 1 / 4) :
    ‖fCan P μ θ‖ ≤ gCan P θ := by
  unfold fCan gCan
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ]
  have hre : (μ + 1 / 2).re = μ.re + 1 / 2 := by simp
  rw [hre]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  by_cases h1 : θ ≤ 1
  · have hle : θ ^ (μ.re + 1 / 2) ≤ θ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hθ h1 (by linarith)
    have hpos : 0 ≤ θ ^ (3 / 4 : ℝ) := Real.rpow_nonneg hθ.le _
    linarith
  · have h1' : 1 < θ := lt_of_not_ge h1
    have hle : θ ^ (μ.re + 1 / 2) ≤ θ ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1'.le (by linarith)
    have hpos : 0 ≤ θ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hθ.le _
    linarith

private lemma integrableOn_fCan {P : PlanarData} (hP : IsPlanarReference P) {μ : ℂ}
    (hμ0 : 0 < μ.re) (hμ1 : μ.re < 1 / 4) :
    IntegrableOn (fCan P μ) (Ioi 0) := by
  have hc_pow : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2)) (Ioi 0) := by
    intro θ hθ
    rw [mem_Ioi] at hθ
    have harg : (θ : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hθ))
    exact ((continuousAt_cpow_const harg).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have haesm : AEStronglyMeasurable (fCan P μ) (volume.restrict (Ioi 0)) :=
    (hc_pow.aestronglyMeasurable measurableSet_Ioi).mul (aesm_quadrupole_canonical hP)
  refine Integrable.mono' (integrableOn_gCan hP) haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
  exact norm_fCan_le_gCan P hθ hμ0 hμ1

private lemma tendsto_setIntegral_Ioo_zero {G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ θ > 0, 0 ≤ G θ) :
    Tendsto (fun r : ℝ => ∫ θ in Ioo 0 r, G θ) (𝓝[>] 0) (𝓝 0) := by
  let μ₀ : Measure ℝ := volume.restrict (Ioi 0)
  have heq : ∀ r > (0 : ℝ), ∫ θ in Ioo 0 r, G θ = ∫ θ, (Ioo 0 r).indicator G θ ∂μ₀ := by
    intro r _
    rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Ioo_inter_Ioi, max_self]
  have hlim : Tendsto (fun r : ℝ => ∫ θ, (Ioo 0 r).indicator G θ ∂μ₀) (𝓝[>] 0)
      (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ₀)) := by
    refine tendsto_integral_filter_of_dominated_convergence G ?_ ?_ hG ?_
    · exact Eventually.of_forall fun r => hG.1.indicator measurableSet_Ioo
    · refine Eventually.of_forall fun r => ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      by_cases hmem : θ ∈ Ioo 0 r
      · simp [hmem, abs_of_nonneg (hG0 θ hθ)]
      · simp [hmem, hG0 θ hθ]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      rw [mem_Ioi] at hθ
      refine tendsto_const_nhds.congr' ?_
      have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < θ :=
        nhdsWithin_le_nhds (Iio_mem_nhds hθ)
      filter_upwards [hlt] with r hr
      have hnmem : θ ∉ Ioo 0 r := fun h => not_lt_of_ge h.2.le hr
      simp [hnmem]
  rw [integral_zero] at hlim
  exact hlim.congr' (by filter_upwards [self_mem_nhdsWithin] with r hr; exact (heq r hr).symm)

private lemma tendsto_setIntegral_Ioi_zero {G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ θ > 0, 0 ≤ G θ) :
    Tendsto (fun T : ℝ => ∫ θ in Ioi T, G θ) atTop (𝓝 0) := by
  let μ₀ : Measure ℝ := volume.restrict (Ioi 0)
  have heq : ∀ T : ℝ, 0 ≤ T → ∫ θ in Ioi T, G θ = ∫ θ, (Ioi T).indicator G θ ∂μ₀ := by
    intro T hT
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left hT]
  have hlim : Tendsto (fun T : ℝ => ∫ θ, (Ioi T).indicator G θ ∂μ₀) atTop
      (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ₀)) := by
    refine tendsto_integral_filter_of_dominated_convergence G ?_ ?_ hG ?_
    · exact Eventually.of_forall fun T => hG.1.indicator measurableSet_Ioi
    · refine Eventually.of_forall fun T => ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      by_cases hmem : θ ∈ Ioi T
      · simp [hmem, abs_of_nonneg (hG0 θ hθ)]
      · simp [hmem, hG0 θ hθ]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ _
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.mem_atTop θ] with T hT
      have hnmem : θ ∉ Ioi T := not_lt.2 hT
      simp [hnmem]
  rw [integral_zero] at hlim
  exact hlim.congr' (by filter_upwards [Filter.mem_atTop (0 : ℝ)] with T hT; exact (heq T hT).symm)

private lemma long_exp_rpow_integrable {γ : ℝ} (hγ : 0 < γ) (A : ℝ) {b : ℝ} (hb1 : 1 ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧
      IntegrableOn (fun θ : ℝ => Real.exp (-γ * θ) * θ ^ A) (Ioi b) ∧
      ∫ θ in Ioi b, Real.exp (-γ * θ) * θ ^ A ≤ M := by
  let N : ℕ := ⌈max A 0⌉₊
  let η : ℝ := γ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let C_fac : ℝ := (N.factorial : ℝ) / η ^ N
  have hC_fac : 0 ≤ C_fac := by dsimp [C_fac]; positivity
  have hint_dom : IntegrableOn (fun θ : ℝ => C_fac * Real.exp ((-η) * θ)) (Ioi b) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hη) b).const_mul C_fac
  have hc_f : ContinuousOn (fun θ : ℝ => Real.exp (-γ * θ) * θ ^ A) (Ioi b) := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le one_pos (hb1.trans hθ.le)
    exact ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).mul
      (ContinuousAt.rpow continuousAt_id continuousAt_const (Or.inl hθ0.ne'))).continuousWithinAt
  have hpt : ∀ θ ∈ Ioi b, 0 ≤ Real.exp (-γ * θ) * θ ^ A ∧
      Real.exp (-γ * θ) * θ ^ A ≤ C_fac * Real.exp ((-η) * θ) := by
    intro θ hθ
    have hθ1 : 1 ≤ θ := hb1.trans hθ.le
    have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
    refine ⟨by positivity, ?_⟩
    have hAN : A ≤ (N : ℝ) := (le_max_left A 0).trans (Nat.le_ceil _)
    have hrpow_le : θ ^ A ≤ θ ^ N := by
      calc θ ^ A ≤ θ ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hθ1 hAN
        _ = θ ^ N := Real.rpow_natCast θ N
    have hfac := Real.pow_div_factorial_le_exp (η * θ) (by positivity) N
    have hpow_le : θ ^ N ≤ C_fac * Real.exp (η * θ) := by
      have hηN : 0 < η ^ N := pow_pos hη N
      have hfac_pos : 0 < (N.factorial : ℝ) := Nat.cast_pos.2 N.factorial_pos
      rw [mul_pow, div_le_iff₀ hfac_pos] at hfac
      dsimp [C_fac]
      rw [div_mul_eq_mul_div, le_div_iff₀ hηN]
      linarith
    calc Real.exp (-γ * θ) * θ ^ A
        ≤ Real.exp (-γ * θ) * (C_fac * Real.exp (η * θ)) :=
          mul_le_mul_of_nonneg_left (hrpow_le.trans hpow_le) (Real.exp_pos _).le
      _ = C_fac * (Real.exp (-γ * θ) * Real.exp (η * θ)) := by ring
      _ = C_fac * Real.exp ((-η) * θ) := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          dsimp [η]
          ring
  have hint_f : IntegrableOn (fun θ : ℝ => Real.exp (-γ * θ) * θ ^ A) (Ioi b) := by
    refine Integrable.mono' hint_dom (hc_f.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
    rw [Real.norm_of_nonneg (hpt θ hθ).1]
    exact (hpt θ hθ).2
  let M : ℝ := ∫ θ in Ioi b, C_fac * Real.exp ((-η) * θ)
  have hM0 : 0 ≤ M :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => by positivity
  refine ⟨M, hM0, hint_f, ?_⟩
  exact setIntegral_mono_on hint_f hint_dom measurableSet_Ioi fun θ hθ => (hpt θ hθ).2

/-! ## Section 4: Interval splitting and assembly of `ctMellin` -/

private lemma integral_Ioo_split_three {r b T : ℝ} (hr0 : 0 < r) (hrb : r < b) (hbT : b < T)
    {f : ℝ → ℂ} (hf : IntegrableOn f (Ioo 0 T)) :
    ∫ θ in Ioo 0 T, f θ =
      (∫ θ in Ioo 0 r, f θ) + (∫ θ in Ioo r b, f θ) + (∫ θ in Ioo b T, f θ) := by
  have hf_oc : IntegrableOn f (Ioc 0 T) := (integrableOn_Ioc_iff_integrableOn_Ioo).2 hf
  have h_0b : Ioc 0 b ⊆ Ioc 0 T := Ioc_subset_Ioc_right hbT.le
  have h_bT : Ioc b T ⊆ Ioc 0 T := Ioc_subset_Ioc_left (hr0.trans hrb).le
  have h_0r : Ioc 0 r ⊆ Ioc 0 b := Ioc_subset_Ioc_right hrb.le
  have h_rb : Ioc r b ⊆ Ioc 0 b := Ioc_subset_Ioc_left hr0.le
  have hd1 : Disjoint (Ioc 0 b) (Ioc b T) := Ioc_disjoint_Ioc_of_le le_rfl
  have hd2 : Disjoint (Ioc 0 r) (Ioc r b) := Ioc_disjoint_Ioc_of_le le_rfl
  rw [← integral_Ioc_eq_integral_Ioo,
    ← Ioc_union_Ioc_eq_Ioc (hr0.trans hrb).le hbT.le,
    setIntegral_union hd1 measurableSet_Ioc (hf_oc.mono_set h_0b) (hf_oc.mono_set h_bT),
    ← Ioc_union_Ioc_eq_Ioc hr0.le hrb.le,
    setIntegral_union hd2 measurableSet_Ioc ((hf_oc.mono_set h_0b).mono_set h_0r)
      ((hf_oc.mono_set h_0b).mono_set h_rb),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

private lemma integral_Ioi_split_four {r b T : ℝ} (hr0 : 0 < r) (hrb : r < b) (hbT : b < T)
    {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    ∫ θ in Ioi 0, g θ =
      (∫ θ in Ioo 0 r, g θ) + (∫ θ in Ioo r b, g θ) + (∫ θ in Ioo b T, g θ) +
        (∫ θ in Ioi T, g θ) := by
  have hT0 : 0 < T := (hr0.trans hrb).trans hbT
  have hd : Disjoint (Ioc 0 T) (Ioi T) :=
    Set.disjoint_left.2 fun _ hx hy => not_lt_of_ge hx.2 hy
  have hg_oc : IntegrableOn g (Ioc 0 T) := hg.mono_set Ioc_subset_Ioi_self
  have hg_oo : IntegrableOn g (Ioo 0 T) := (integrableOn_Ioc_iff_integrableOn_Ioo).1 hg_oc
  have hg_oi : IntegrableOn g (Ioi T) := hg.mono_set (Ioi_subset_Ioi hT0.le)
  rw [← Ioc_union_Ioi_eq_Ioi hT0.le,
    setIntegral_union hd measurableSet_Ioi hg_oc hg_oi,
    integral_Ioc_eq_integral_Ioo, integral_Ioo_split_three hr0 hrb hbT hg_oo]

end MellinAux

/-- **`eq:ct-mellin`** (`PartIII-a:T22/5`, SP 3300-3343). -/
theorem ctMellin : CTMellin := by
  intro P hP m hm K hK ε hε
  rcases K.eq_empty_or_nonempty with rfl | hK_ne
  · exact Filter.eventually_of_mem self_mem_nhdsWithin fun _ _ _ _ _ _ _ _ hμ => False.elim hμ
  open MellinAux in
  obtain ⟨M_K', hMK'_bd⟩ := hK.1.isBounded.exists_norm_le
  let M_K : ℝ := max M_K' 0
  have hMK0 : 0 ≤ M_K := le_max_right _ _
  have hMK : ∀ μ ∈ K, ‖μ‖ ≤ M_K := fun μ hμ => (hMK'_bd μ hμ).trans (le_max_left _ _)
  have hm0 : 0 ≤ m := by linarith
  have hm1 : 1 < m := by linarith
  have hm3 : 3 < m := by linarith
  obtain ⟨C_q, hCq⟩ := CTE.quadQ_bound m hm3
  let C_q' : ℝ := max C_q 0
  have hCq'0 : 0 ≤ C_q' := le_max_right _ _
  obtain ⟨C_bu, hCbu⟩ := CTE.biotSavart_exists_uniform m hm
  let C_bu' : ℝ := max C_bu 0
  have hCbu'0 : 0 ≤ C_bu' := le_max_right _ _
  obtain ⟨b₀_long, hLong_b⟩ := ctLongComparison P hP m hm
  obtain ⟨b₀_imp, hImp_b⟩ := ctTestedImpulse P hP m hm
  obtain ⟨b₀_comp, hComp_b⟩ := ctCompactComparison P hP m hm
  let b : ℝ := max 1 (max b₀_long (max b₀_imp b₀_comp))
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hb_r1 := le_max_right 1 (max b₀_long (max b₀_imp b₀_comp))
  have hb_long : b₀_long ≤ b := (le_max_left _ _).trans hb_r1
  have hb_r2 := (le_max_right _ _).trans hb_r1
  have hb_imp : b₀_imp ≤ b := (le_max_left _ _).trans hb_r2
  have hb_comp : b₀_comp ≤ b := (le_max_right _ _).trans hb_r2
  obtain ⟨C_long, a₁, ν_long, ha₁, hν_long, hLong⟩ := hLong_b b hb_long
  let C_long' : ℝ := max C_long 0
  have hClong'0 : 0 ≤ C_long' := le_max_right _ _
  obtain ⟨C_imp, ν_imp, hν_imp, hImp⟩ := hImp_b b hb_imp (3 / 2) (by norm_num)
  let C_imp' : ℝ := max C_imp 0
  have hCimp'0 : 0 ≤ C_imp' := le_max_right _ _
  obtain ⟨C_br, hCbr_pos, hBr_small⟩ := (T22Sub.ctCanonicalBranchProps P hP m hm).2.2.2 b hb0
  let M_data : ℝ := (1 + C_q' * C_br) + (1 + C_bu' * C_br)
  have hM_data_pos : 0 < M_data := by dsimp [M_data]; positivity
  have hint_gCan : IntegrableOn (gCan P) (Ioi 0) := integrableOn_gCan hP
  let I_G : ℝ := ∫ θ in Ioi 0, gCan P θ
  have hIG0 : 0 ≤ I_G := setIntegral_nonneg measurableSet_Ioi fun _ hθ => gCan_nonneg P hθ.le
  obtain ⟨M_exp, hM_exp0, hint_exp, hbd_exp⟩ :=
    long_exp_rpow_integrable hP.eigenpair.re_pos (3 / 4 - P.kappa.re) hb1
  -- Step 1: Choose r ∈ (0, min 1 (b / 2)) small enough for both small-θ tails
  have : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  have hr_ev1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 (min 1 (b / 2)) := by
    have hpos : 0 < min 1 (b / 2) := lt_min one_pos (by positivity)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hpos)] with r hr0 hr1
    exact ⟨hr0, hr1⟩
  have hr_ev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      8 * C_imp' * M_data * r ^ (3 / 2 : ℝ) < ε / 6 := by
    have hcont : ContinuousAt (fun r : ℝ => 8 * C_imp' * M_data * r ^ (3 / 2 : ℝ)) 0 :=
      continuousAt_const.mul (ContinuousAt.rpow continuousAt_id continuousAt_const
        (Or.inr (by norm_num)))
    have h0 : 8 * C_imp' * M_data * (0 : ℝ) ^ (3 / 2 : ℝ) = 0 := by
      rw [Real.zero_rpow (by norm_num), mul_zero]
    have htend : Tendsto (fun r : ℝ => 8 * C_imp' * M_data * r ^ (3 / 2 : ℝ))
        (𝓝[>] 0) (𝓝 0) := by
      have ht := hcont.continuousWithinAt (s := Ioi 0)
      rwa [ContinuousWithinAt, h0] at ht
    exact htend.eventually (Iio_mem_nhds (by positivity))
  have hr_ev3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ θ in Ioo 0 r, gCan P θ < ε / 6 :=
    (tendsto_setIntegral_Ioo_zero hint_gCan (fun _ hθ => gCan_nonneg P hθ.le)).eventually
      (Iio_mem_nhds (by positivity))
  obtain ⟨r, ⟨⟨hr0, hr_lt⟩, hr_p1, hr_p2⟩⟩ := (hr_ev1.and (hr_ev2.and hr_ev3)).exists
  have hr1 : r ≤ 1 := hr_lt.le.trans (min_le_left _ _)
  have hrb_lt : r < b := lt_of_lt_of_le (hr_lt.trans_le (min_le_right _ _)) (by linarith)
  have hrb : r ≤ b := hrb_lt.le
  -- Step 2: Choose T₀ > 2 * b large enough for the upper canonical tail
  have hT_ev : ∀ᶠ T in atTop, 2 * b < T ∧ ∫ θ in Ioi T, gCan P θ < ε / 6 :=
    (Filter.eventually_gt_atTop (2 * b)).and
      ((tendsto_setIntegral_Ioi_zero hint_gCan (fun _ hθ => gCan_nonneg P hθ.le)).eventually
        (Iio_mem_nhds (by positivity)))
  obtain ⟨T₀, hT₀_2b, hT₀_p6⟩ := hT_ev.exists
  have hT₀_pos : 0 < T₀ := by linarith
  -- Step 3: Compact comparison tolerance on [r, b]
  let δ_comp : ℝ := (ε / 6) / (8 * b ^ (3 / 4 : ℝ) * b + 1)
  have hδ_comp : 0 < δ_comp := by dsimp [δ_comp]; positivity
  -- Step 4: Long comparison constant on [b, θ_o(ν)]
  let K_long : ℝ := 8 * C_q' * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * M_exp
  have hK_long0 : 0 ≤ K_long := by dsimp [K_long]; positivity
  -- Step 5: Assemble 𝓝[>] 0 filter for ν
  have hν_comp1 := hComp_b b hb_comp r hr0 hrb 1 one_pos
  have hν_comp2 := hComp_b b hb_comp r hr0 hrb δ_comp hδ_comp
  have hν_bound : ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      ν < min 1 (min r (min ν_imp ν_long)) := by
    have hpos : 0 < min 1 (min r (min ν_imp ν_long)) :=
      lt_min one_pos (lt_min hr0 (lt_min hν_imp hν_long))
    exact nhdsWithin_le_nhds (Iio_mem_nhds hpos)
  have hcont_sqrt0 : ContinuousAt (fun ν : ℝ => Real.sqrt ν) 0 :=
    Real.continuous_sqrt.continuousAt
  have hν_T₀ : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν + Real.sqrt ν < T₀⁻¹ := by
    have hc : ContinuousAt (fun ν : ℝ => ν + Real.sqrt ν) 0 :=
      continuousAt_id.add hcont_sqrt0
    have h0 : (0 : ℝ) + Real.sqrt 0 = 0 := by simp
    have ht : Tendsto (fun ν : ℝ => ν + Real.sqrt ν) (𝓝[>] 0) (𝓝 0) := by
      have ht' := hc.continuousWithinAt (s := Ioi 0)
      rwa [ContinuousWithinAt, h0] at ht'
    exact ht.eventually (Iio_mem_nhds (inv_pos.2 hT₀_pos))
  have hν_wt_small : ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      Real.sqrt ν < 1 / 2 ∧ (M_K + 3) * (2 * Real.sqrt ν) < 1 := by
    have ht1 : Tendsto Real.sqrt (𝓝[>] 0) (𝓝 0) := by
      simpa using hcont_sqrt0.tendsto.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun ν : ℝ => (M_K + 3) * (2 * Real.sqrt ν)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ht1.const_mul 2).const_mul (M_K + 3)
    exact (ht1.eventually (Iio_mem_nhds (by norm_num))).and
      (ht2.eventually (Iio_mem_nhds one_pos))
  have hν_p4 : ∀ᶠ ν in 𝓝[>] (0 : ℝ), K_long * ν < ε / 6 := by
    have hc : ContinuousAt (fun ν : ℝ => K_long * ν) 0 :=
      continuousAt_const.mul continuousAt_id
    have ht : Tendsto (fun ν : ℝ => K_long * ν) (𝓝[>] 0) (𝓝 0) := by
      have ht' := hc.continuousWithinAt (s := Ioi 0)
      rwa [ContinuousWithinAt, mul_zero] at ht'
    exact ht.eventually (Iio_mem_nhds (by positivity))
  have hν_p5 : ∀ᶠ ν in 𝓝[>] (0 : ℝ), 4 * (M_K + 3) * Real.sqrt ν * I_G < ε / 6 := by
    have ht1 : Tendsto Real.sqrt (𝓝[>] 0) (𝓝 0) := by
      simpa using hcont_sqrt0.tendsto.mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun ν : ℝ => 4 * (M_K + 3) * Real.sqrt ν * I_G) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((ht1.const_mul (4 * (M_K + 3))).mul_const I_G)
    exact ht.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [self_mem_nhdsWithin, hν_bound, hν_T₀, hν_wt_small, hν_p4, hν_p5,
    hν_comp1, hν_comp2] with ν hν0 hν_bd hν_sum hν_wt hν_long_sm hν_wt_p5 hcomp1 hcomp2
    tr hbuc w u hw μ hμ
  rw [mem_Ioi] at hν0
  have hν1 : ν ≤ 1 := hν_bd.le.trans (min_le_left _ _)
  have hν_r1 := hν_bd.le.trans (min_le_right _ _)
  have hν_le_r : ν ≤ r := hν_r1.trans (min_le_left _ _)
  have hν_r2 := hν_r1.trans (min_le_right _ _)
  have hν_le_imp : ν ≤ ν_imp := hν_r2.trans (min_le_left _ _)
  have hν_le_long : ν ≤ ν_long := hν_r2.trans (min_le_right _ _)
  have hμ0 : 0 < μ.re := (hK.2 μ hμ).1
  have hμ14 : μ.re < 1 / 4 := (hK.2 μ hμ).2
  have hμ_norm : ‖μ‖ ≤ M_K := hMK μ hμ
  let T : ℝ := thetaOnset ν
  have hT₀_lt_T : T₀ < T := lt_thetaOnset_of_sum_lt_inv hν0 hT₀_pos hν_sum
  have hbT : b < T := (by linarith : b < T₀).trans hT₀_lt_T
  have hT_lt_inv : T < ν⁻¹ := thetaOnset_lt_inv hν0
  have hr_inv : r ≤ ν⁻¹ := (hrb.trans hbT.le).trans hT_lt_inv.le
  have hb_inv : b ≤ ν⁻¹ := hbT.le.trans hT_lt_inv.le
  have hν3_le_ν : ν ^ 3 ≤ ν := by
    have h2 : ν ^ 2 ≤ 1 := pow_le_one₀ hν0.le hν1
    nlinarith
  have hν6_le_ν : ν ^ 6 ≤ ν := by
    have h5 : ν ^ 5 ≤ 1 := pow_le_one₀ hν0.le hν1
    nlinarith
  have hν3_le_r : ν ^ 3 ≤ r := hν3_le_ν.trans hν_le_r
  have hd_r1 : 1 ≤ dOfTheta ν r := T22Sub.one_le_dOfTheta hν0 hν3_le_r
  have hd_r0 : 0 < dOfTheta ν r := lt_of_lt_of_le one_pos hd_r1
  -- Weight bounds on (0, T]
  have hwt_eight : ∀ θ ∈ Ioc 0 T,
      ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖ ≤ 8 := by
    intro θ hθ
    have hx0 : 0 ≤ ν * θ := mul_nonneg hν0.le hθ.1.le
    have hx1 : ν * θ ≤ 1 / 2 := by
      have hlt : ν * θ ≤ ν * T := mul_le_mul_of_nonneg_left hθ.2 hν0.le
      exact hlt.trans ((nu_mul_thetaOnset_lt_sqrt hν0).le.trans hν_wt.1.le)
    exact norm_one_sub_cpow_le_eight hx0 hx1 hμ0 hμ14
  have hwt_diff : ∀ θ ∈ Ioc 0 T,
      ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) - 1‖ ≤ 4 * (M_K + 3) * Real.sqrt ν := by
    intro θ hθ
    have hx0 : 0 ≤ ν * θ := mul_nonneg hν0.le hθ.1.le
    have hx_sqrt : ν * θ ≤ Real.sqrt ν :=
      (mul_le_mul_of_nonneg_left hθ.2 hν0.le).trans (nu_mul_thetaOnset_lt_sqrt hν0).le
    have hx1 : ν * θ ≤ 1 / 2 := hx_sqrt.trans hν_wt.1.le
    have hsm : (M_K + 3) * (2 * (ν * θ)) ≤ 1 := by
      calc (M_K + 3) * (2 * (ν * θ)) ≤ (M_K + 3) * (2 * Real.sqrt ν) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ 1 := hν_wt.2.le
    exact (norm_one_sub_cpow_sub_one_le hx0 hx1 hMK0 hμ_norm hsm).trans
      (mul_le_mul_of_nonneg_left hx_sqrt (by positivity))
  -- Step 6: Bound |Q_d(Z r)| + r * kinNorm d(r) (Z r) ≤ M_data and apply ctTestedImpulse
  have hVr_props := (T22Sub.ctCanonicalBranchProps P hP m hm).2.1 ν r hν0 hr0 hd_r1
  have hVr_xnorm := hBr_small ν ⟨hν0, hν1⟩ r ⟨hr0, hrb⟩ hd_r1
  have hVr_quad : ENNReal.ofReal ‖quadQ (dOfTheta ν r) (canonicalPeriodized P ν r)‖ ≤
      ENNReal.ofReal (C_q' * C_br) := by
    calc ENNReal.ofReal ‖quadQ (dOfTheta ν r) (canonicalPeriodized P ν r)‖
        ≤ ENNReal.ofReal C_q * xNorm (dOfTheta ν r) m (canonicalPeriodized P ν r) :=
          hCq (dOfTheta ν r) _ hVr_props.1
      _ ≤ ENNReal.ofReal C_q' * ENNReal.ofReal C_br :=
          mul_le_mul (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hVr_xnorm zero_le zero_le
      _ = ENNReal.ofReal (C_q' * C_br) := (ENNReal.ofReal_mul hCq'0).symm
  obtain ⟨u_Vr, hu_Vr_bs, hu_Vr_vel⟩ :=
    hCbu (dOfTheta ν r) hd_r1 (canonicalPeriodized P ν r) hVr_props.1 hVr_props.2.1 hVr_props.2.2.1
  have hVr_vel_bd : velNorm (dOfTheta ν r) u_Vr ≤ ENNReal.ofReal (C_bu' * C_br) := by
    calc velNorm (dOfTheta ν r) u_Vr
        ≤ ENNReal.ofReal C_bu * xNorm (dOfTheta ν r) m (canonicalPeriodized P ν r) := hu_Vr_vel
      _ ≤ ENNReal.ofReal C_bu' * ENNReal.ofReal C_br :=
          mul_le_mul (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hVr_xnorm zero_le zero_le
      _ = ENNReal.ofReal (C_bu' * C_br) := (ENNReal.ofReal_mul hCbu'0).symm
  have hcomp1_r := hcomp1 tr hbuc w u hw r ⟨le_rfl, hrb⟩
  have hZr_mem := heatColumn_memLp P hm0 hν0 hr0 hr_inv hw
  have hZr_bs := heatColumn_isBiotSavart P hm0 hν0 hr0 hr_inv hw
  have hZr_quad_le : ‖quadQ (dOfTheta ν r) (heatColumn P ν w r)‖ ≤ 1 + C_q' * C_br := by
    have hdiff_q : ‖quadQ (dOfTheta ν r) (heatColumn P ν w r - canonicalPeriodized P ν r)‖ ≤ 1 :=
      (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 hcomp1_r.2
    have hvq : ‖quadQ (dOfTheta ν r) (canonicalPeriodized P ν r)‖ ≤ C_q' * C_br :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hVr_quad
    have hsplit : quadQ (dOfTheta ν r) (heatColumn P ν w r) =
        quadQ (dOfTheta ν r) (heatColumn P ν w r - canonicalPeriodized P ν r) +
          quadQ (dOfTheta ν r) (canonicalPeriodized P ν r) := by
      rw [quadQ_sub hm3 hZr_mem hVr_props.1, sub_add_cancel]
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hdiff_q hvq)
  have hZr_kin_le : kinNorm (dOfTheta ν r) (heatColumn P ν w r) ≤
      ENNReal.ofReal (1 + C_bu' * C_br) := by
    let u_Zr := fun y j => (P.gaugeFactor ν)⁻¹ * rescaleVel (ν * r)⁻¹ (u (clockAge ν r)) y j
    let u_diff := fun y j => u_Zr y j - u_Vr y j
    have hdiff_bs : IsBiotSavart (dOfTheta ν r)
        (heatColumn P ν w r - canonicalPeriodized P ν r) u_diff :=
      ladBSSub m (dOfTheta ν r) (heatColumn P ν w r) (canonicalPeriodized P ν r)
        u_Zr u_Vr hm1 hZr_mem hVr_props.1 hZr_bs hu_Vr_bs
    have hdiff_vel : velNorm (dOfTheta ν r) u_diff ≤ ENNReal.ofReal 1 := by
      rw [← kinNorm_eq_velNorm hd_r0 hdiff_bs]
      exact hcomp1_r.1
    have hu_sum : u_Zr = u_diff + u_Vr := by
      funext y j; simp [u_diff, Pi.add_apply]
    rw [kinNorm_eq_velNorm hd_r0 hZr_bs]
    change velNorm (dOfTheta ν r) u_Zr ≤ _
    rw [hu_sum]
    calc velNorm (dOfTheta ν r) (u_diff + u_Vr)
        ≤ velNorm (dOfTheta ν r) u_diff + velNorm (dOfTheta ν r) u_Vr :=
          velNorm_add_le hdiff_bs.1 hu_Vr_bs.1
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (C_bu' * C_br) :=
          add_le_add hdiff_vel hVr_vel_bd
      _ = ENNReal.ofReal (1 + C_bu' * C_br) :=
          (ENNReal.ofReal_add zero_le_one (by positivity)).symm
  obtain ⟨hh_mem, hh_zc, hh_ev, hh_quad, hh_kin, hZθ_quad, hEvol⟩ :=
    heatColumn_symEven_package hP hm hν0 hν1 hr0 hr_inv hw
  have himp_raw := hImp ν ⟨hν0, hν_le_imp⟩ tr hbuc r hr0 hrb
    (symEven (heatColumn P ν w r)) hh_mem hh_zc hh_ev
    (fun θ => symEven (heatColumn P ν w θ)) hEvol
  have himp_Z : ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ ((3 / 2 : ℝ) - 1)) *
        ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ)‖ ≤
      ENNReal.ofReal (C_imp' * M_data * r ^ (3 / 2 : ℝ)) := by
    have hlhs : ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ ((3 / 2 : ℝ) - 1)) *
          ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ)‖ =
        ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ ((3 / 2 : ℝ) - 1)) *
          ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (symEven (heatColumn P ν w θ))‖ := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
      rw [hZθ_quad θ ⟨hθ.1, hθ.2.le⟩]
    rw [hlhs]
    refine himp_raw.trans ?_
    rw [hh_quad]
    have hdata_bd : ENNReal.ofReal ‖quadQ (dOfTheta ν r) (heatColumn P ν w r)‖ +
        ENNReal.ofReal r * kinNorm (dOfTheta ν r) (symEven (heatColumn P ν w r)) ≤
        ENNReal.ofReal M_data := by
      calc ENNReal.ofReal ‖quadQ (dOfTheta ν r) (heatColumn P ν w r)‖ +
            ENNReal.ofReal r * kinNorm (dOfTheta ν r) (symEven (heatColumn P ν w r))
          ≤ ENNReal.ofReal (1 + C_q' * C_br) +
              ENNReal.ofReal 1 * ENNReal.ofReal (1 + C_bu' * C_br) :=
            add_le_add (ENNReal.ofReal_le_ofReal hZr_quad_le)
              (mul_le_mul (ENNReal.ofReal_le_ofReal hr1)
                (hh_kin.trans hZr_kin_le) zero_le zero_le)
        _ = ENNReal.ofReal M_data := by
            rw [ENNReal.ofReal_one, one_mul,
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
    calc ENNReal.ofReal (C_imp * r ^ (3 / 2 : ℝ)) *
          (ENNReal.ofReal ‖quadQ (dOfTheta ν r) (heatColumn P ν w r)‖ +
            ENNReal.ofReal r * kinNorm (dOfTheta ν r) (symEven (heatColumn P ν w r)))
        ≤ ENNReal.ofReal (C_imp' * r ^ (3 / 2 : ℝ)) * ENNReal.ofReal M_data := by
          refine mul_le_mul (ENNReal.ofReal_le_ofReal ?_) hdata_bd zero_le zero_le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = ENNReal.ofReal (C_imp' * M_data * r ^ (3 / 2 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- Step 7: IntegrableOn of fZ on (0, T) and Piece 1 bound
  have hc_fZ : ContinuousOn (fZ P ν μ w) (Ioc 0 T) := continuousOn_fZ P hm3 hν0 μ hw
  have hlint_fZ_0r : ∫⁻ θ in Ioo 0 r, ‖fZ P ν μ w θ‖ₑ ≤
      ENNReal.ofReal (8 * C_imp' * M_data * r ^ (3 / 2 : ℝ)) := by
    have hpt : ∀ θ ∈ Ioo 0 r, ‖fZ P ν μ w θ‖ₑ ≤
        ENNReal.ofReal 8 * (ENNReal.ofReal (θ ^ ((3 / 2 : ℝ) - 1)) *
          ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ)‖) := by
      intro θ hθ
      rw [← ofReal_norm]
      have hθT : θ ∈ Ioc 0 T := ⟨hθ.1, (hθ.2.trans hrb_lt).le.trans hbT.le⟩
      have hθ1 : θ ≤ 1 := hθ.2.le.trans hr1
      have hpow_le : ‖(θ : ℂ) ^ (μ + 1 / 2)‖ ≤ θ ^ ((3 / 2 : ℝ) - 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hθ.1]
        have hre : (μ + 1 / 2).re = μ.re + 1 / 2 := by simp
        rw [hre]
        exact Real.rpow_le_rpow_of_exponent_ge hθ.1 hθ1 (by linarith)
      have hwt8 := hwt_eight θ hθT
      have hnrm : ‖fZ P ν μ w θ‖ ≤
          8 * (θ ^ ((3 / 2 : ℝ) - 1) * ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ)‖) := by
        unfold fZ
        rw [norm_mul, norm_mul]
        have h12 : ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖ ≤
            8 * θ ^ ((3 / 2 : ℝ) - 1) := by
          calc ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖
              ≤ θ ^ ((3 / 2 : ℝ) - 1) * 8 :=
                mul_le_mul hpow_le hwt8 (norm_nonneg _) (Real.rpow_nonneg hθ.1.le _)
            _ = 8 * θ ^ ((3 / 2 : ℝ) - 1) := mul_comm _ _
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h12 (norm_nonneg _)
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hθ.1.le _), ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hnrm
    calc ∫⁻ θ in Ioo 0 r, ‖fZ P ν μ w θ‖ₑ
        ≤ ∫⁻ θ in Ioo 0 r, ENNReal.ofReal 8 * (ENNReal.ofReal (θ ^ ((3 / 2 : ℝ) - 1)) *
            ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ)‖) :=
          lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioo hpt)
      _ = ENNReal.ofReal 8 * ∫⁻ θ in Ioo 0 r, ENNReal.ofReal (θ ^ ((3 / 2 : ℝ) - 1)) *
            ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ)‖ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (C_imp' * M_data * r ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left himp_Z zero_le
      _ = ENNReal.ofReal (8 * C_imp' * M_data * r ^ (3 / 2 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
  have hrT_lt : r < T := hrb_lt.trans hbT
  have hint_fZ_0r : IntegrableOn (fZ P ν μ w) (Ioo 0 r) :=
    ⟨(hc_fZ.mono (fun _ h => ⟨h.1, (h.2.trans hrT_lt).le⟩)).aestronglyMeasurable measurableSet_Ioo,
      hasFiniteIntegral_iff_enorm.2 (lt_of_le_of_lt hlint_fZ_0r ENNReal.ofReal_lt_top)⟩
  have hint_fZ_rT : IntegrableOn (fZ P ν μ w) (Ioc r T) :=
    ((hc_fZ.mono (fun _ h => ⟨hr0.trans_le h.1, h.2⟩)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hint_fZ_oc : IntegrableOn (fZ P ν μ w) (Ioc 0 T) := by
    rw [← Ioc_union_Ioc_eq_Ioc hr0.le hrT_lt.le]
    exact ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hint_fZ_0r).union hint_fZ_rT
  have hint_fZ : IntegrableOn (fZ P ν μ w) (Ioo 0 T) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).1 hint_fZ_oc
  obtain ⟨hint_iA, hiA_eq⟩ := iA_cov P hm3 hν0 μ hw hint_fZ
  refine ⟨hint_iA, ?_⟩
  change ‖iA ν μ w / mellinPref P ν μ - mellinJc P μ‖ ≤ ε
  -- Step 8: Integrability of fCan and fCanWt on (0, T]
  have hint_fCan : IntegrableOn (fCan P μ) (Ioi 0) := integrableOn_fCan hP hμ0 hμ14
  have hint_fCanWt_0T : IntegrableOn (fCanWt P ν μ) (Ioc 0 T) := by
    have hc_wt : ContinuousOn (fun θ : ℝ => ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)) (Ioc 0 T) := by
      intro θ hθ
      have hmul_lt : ν * θ < 1 := by
        have := mul_lt_mul_of_pos_left (hθ.2.trans_lt hT_lt_inv) hν0
        simpa [mul_inv_cancel₀ hν0.ne'] using this
      have hpos : 0 < 1 - ν * θ := by linarith
      have harg : ((1 - ν * θ : ℝ) : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hpos))
      have hinner : ContinuousAt (fun t : ℝ => ((1 - ν * t : ℝ) : ℂ)) θ :=
        Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
      exact (ContinuousAt.comp (f := fun t : ℝ => ((1 - ν * t : ℝ) : ℂ))
        (continuousAt_cpow_const harg) hinner).continuousWithinAt
    have haesm_wt : AEStronglyMeasurable (fCanWt P ν μ) (volume.restrict (Ioc 0 T)) := by
      have heq : fCanWt P ν μ =
          fun θ => ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) * fCan P μ θ := by
        funext θ; unfold fCanWt fCan; ring
      rw [heq]
      exact (hc_wt.aestronglyMeasurable measurableSet_Ioc).mul
        (hint_fCan.mono_set Ioc_subset_Ioi_self).1
    refine Integrable.mono' ((hint_gCan.mono_set Ioc_subset_Ioi_self).const_mul 8) haesm_wt ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have heq : fCanWt P ν μ θ = ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) * fCan P μ θ := by
      unfold fCanWt fCan; ring
    rw [heq, norm_mul]
    exact mul_le_mul (hwt_eight θ hθ) (norm_fCan_le_gCan P hθ.1 hμ0 hμ14)
      (norm_nonneg _) (by norm_num)
  have hint_fCanWt_rb : IntegrableOn (fCanWt P ν μ) (Ioo r b) :=
    hint_fCanWt_0T.mono_set (fun _ h => ⟨hr0.trans h.1, h.2.le.trans hbT.le⟩)
  have hint_fCanWt_bT : IntegrableOn (fCanWt P ν μ) (Ioo b T) :=
    hint_fCanWt_0T.mono_set (fun _ h => ⟨hb0.trans h.1, h.2.le⟩)
  have hint_fCan_rb : IntegrableOn (fCan P μ) (Ioo r b) :=
    hint_fCan.mono_set (fun _ h => hr0.trans h.1)
  have hint_fCan_bT : IntegrableOn (fCan P μ) (Ioo b T) :=
    hint_fCan.mono_set (fun _ h => hb0.trans h.1)
  have hint_fZ_rb : IntegrableOn (fZ P ν μ w) (Ioo r b) :=
    hint_fZ.mono_set (fun _ h => ⟨hr0.trans h.1, h.2.trans hbT⟩)
  have hint_fZ_bT : IntegrableOn (fZ P ν μ w) (Ioo b T) :=
    hint_fZ.mono_set (fun _ h => ⟨hb0.trans h.1, h.2⟩)
  -- Step 9: Bound each of the 6 decomposed integral pieces by ≤ ε / 6
  let I₁ : ℂ := ∫ θ in Ioo 0 r, fZ P ν μ w θ
  let I₂ : ℂ := ∫ θ in Ioo 0 r, fCan P μ θ
  let I₃ : ℂ := (∫ θ in Ioo r b, fZ P ν μ w θ) - (∫ θ in Ioo r b, fCanWt P ν μ θ)
  let I₄ : ℂ := (∫ θ in Ioo b T, fZ P ν μ w θ) - (∫ θ in Ioo b T, fCanWt P ν μ θ)
  let I₅ : ℂ := ((∫ θ in Ioo r b, fCanWt P ν μ θ) - (∫ θ in Ioo r b, fCan P μ θ)) +
    ((∫ θ in Ioo b T, fCanWt P ν μ θ) - (∫ θ in Ioo b T, fCan P μ θ))
  let I₆ : ℂ := ∫ θ in Ioi T, fCan P μ θ
  have hdecomp : iA ν μ w / mellinPref P ν μ - mellinJc P μ =
      I₁ - I₂ + I₃ + I₄ + I₅ - I₆ := by
    rw [hiA_eq, integral_Ioo_split_three hr0 hrb_lt hbT hint_fZ]
    change _ - ∫ θ in Ioi 0, fCan P μ θ = _
    rw [integral_Ioi_split_four hr0 hrb_lt hbT hint_fCan]
    dsimp [I₁, I₂, I₃, I₄, I₅, I₆]
    ring
  -- Piece 1: ‖I₁‖ ≤ ε / 6
  have hb₁ : ‖I₁‖ ≤ ε / 6 := by
    have h1 : ‖I₁‖ ≤ ∫ θ in Ioo 0 r, ‖fZ P ν μ w θ‖ := norm_integral_le_integral_norm _
    have h2 : ENNReal.ofReal (∫ θ in Ioo 0 r, ‖fZ P ν μ w θ‖) ≤
        ENNReal.ofReal (8 * C_imp' * M_data * r ^ (3 / 2 : ℝ)) := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hint_fZ_0r]
      exact hlint_fZ_0r
    have h3 : ∫ θ in Ioo 0 r, ‖fZ P ν μ w θ‖ ≤ 8 * C_imp' * M_data * r ^ (3 / 2 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    exact (h1.trans h3).trans hr_p1.le
  -- Piece 2: ‖I₂‖ ≤ ε / 6
  have hb₂ : ‖I₂‖ ≤ ε / 6 := by
    have h1 : ‖I₂‖ ≤ ∫ θ in Ioo 0 r, ‖fCan P μ θ‖ := norm_integral_le_integral_norm _
    have h2 : ∫ θ in Ioo 0 r, ‖fCan P μ θ‖ ≤ ∫ θ in Ioo 0 r, gCan P θ :=
      setIntegral_mono_on (hint_fCan.mono_set Ioo_subset_Ioi_self).norm
        (hint_gCan.mono_set Ioo_subset_Ioi_self) measurableSet_Ioo
        fun θ hθ => norm_fCan_le_gCan P hθ.1 hμ0 hμ14
    exact (h1.trans h2).trans hr_p2.le
  -- Piece 3: ‖I₃‖ ≤ ε / 6 (compact comparison on (r, b))
  have hb₃ : ‖I₃‖ ≤ ε / 6 := by
    have hsub : I₃ = ∫ θ in Ioo r b, (fZ P ν μ w θ - fCanWt P ν μ θ) :=
      (integral_sub hint_fZ_rb hint_fCanWt_rb).symm
    rw [hsub]
    have hpt : ∀ θ ∈ Ioo r b,
        ‖fZ P ν μ w θ - fCanWt P ν μ θ‖ ≤ 8 * b ^ (3 / 4 : ℝ) * δ_comp := by
      intro θ hθ
      have hθ0 : 0 < θ := hr0.trans hθ.1
      have hθT : θ ∈ Ioc 0 T := ⟨hθ0, hθ.2.le.trans hbT.le⟩
      have hd_θ1 : 1 ≤ dOfTheta ν θ :=
        T22Sub.one_le_dOfTheta hν0 (hν3_le_r.trans hθ.1.le)
      have hVθ := (T22Sub.ctCanonicalBranchProps P hP m hm).2.1 ν θ hν0 hθ0 hd_θ1
      have hZθ_mem := heatColumn_memLp P hm0 hν0 hθ0 (hθ.2.le.trans hb_inv) hw
      have hdiff_eq : fZ P ν μ w θ - fCanWt P ν μ θ =
          (θ : ℂ) ^ (μ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) *
            quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ) := by
        rw [quadQ_sub hm3 hZθ_mem hVθ.1, hVθ.2.2.2]
        unfold fZ fCanWt
        ring
      have hpow_le : ‖(θ : ℂ) ^ (μ + 1 / 2)‖ ≤ b ^ (3 / 4 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hθ0]
        have hre : (μ + 1 / 2).re = μ.re + 1 / 2 := by simp
        rw [hre]
        exact (Real.rpow_le_rpow hθ0.le hθ.2.le (by linarith)).trans
          (Real.rpow_le_rpow_of_exponent_le hb1 (by linarith))
      have hq_le : ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖ ≤
          δ_comp :=
        (ENNReal.ofReal_le_ofReal_iff hδ_comp.le).1
          (hcomp2 tr hbuc w u hw θ ⟨hθ.1.le, hθ.2.le⟩).2
      rw [hdiff_eq, norm_mul, norm_mul]
      have h12 : ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖ ≤
          8 * b ^ (3 / 4 : ℝ) := by
        calc ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖
            ≤ b ^ (3 / 4 : ℝ) * 8 :=
              mul_le_mul hpow_le (hwt_eight θ hθT) (norm_nonneg _) (by positivity)
          _ = 8 * b ^ (3 / 4 : ℝ) := mul_comm _ _
      exact mul_le_mul h12 hq_le (norm_nonneg _) (by positivity)
    have hmeas_lt : volume (Ioo r b) < ⊤ := by simp [Real.volume_Ioo]
    have hint_le := norm_setIntegral_le_of_norm_le_const hmeas_lt hpt
    rw [Real.volume_real_Ioo_of_le hrb] at hint_le
    have hbr_le : b - r ≤ b := by linarith
    have hden_pos : 0 < 8 * b ^ (3 / 4 : ℝ) * b + 1 := by positivity
    calc ‖∫ θ in Ioo r b, (fZ P ν μ w θ - fCanWt P ν μ θ)‖
        ≤ (8 * b ^ (3 / 4 : ℝ) * δ_comp) * (b - r) := hint_le
      _ ≤ (8 * b ^ (3 / 4 : ℝ) * δ_comp) * b :=
          mul_le_mul_of_nonneg_left hbr_le (by positivity)
      _ = (8 * b ^ (3 / 4 : ℝ) * b) * ((ε / 6) / (8 * b ^ (3 / 4 : ℝ) * b + 1)) := by
          dsimp [δ_comp]; ring
      _ ≤ (8 * b ^ (3 / 4 : ℝ) * b + 1) * ((ε / 6) / (8 * b ^ (3 / 4 : ℝ) * b + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 6 := mul_div_cancel₀ _ hden_pos.ne'
  -- Piece 4: ‖I₄‖ ≤ ε / 6 (long comparison + exponential decay on (b, T))
  have hb₄ : ‖I₄‖ ≤ ε / 6 := by
    have hsub : I₄ = ∫ θ in Ioo b T, (fZ P ν μ w θ - fCanWt P ν μ θ) :=
      (integral_sub hint_fZ_bT hint_fCanWt_bT).symm
    rw [hsub]
    let K_fac : ℝ := 8 * C_q' * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν
    have hK_fac0 : 0 ≤ K_fac := by dsimp [K_fac]; positivity
    have hpt : ∀ θ ∈ Ioo b T, ‖fZ P ν μ w θ - fCanWt P ν μ θ‖ ≤
        K_fac * (Real.exp (-P.eigenvalue.re * θ) * θ ^ (3 / 4 - P.kappa.re)) := by
      intro θ hθ
      have hb_θ : b ≤ θ := hθ.1.le
      have hθ1 : 1 ≤ θ := hb1.trans hb_θ
      have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
      have hθν : θ ≤ ν⁻¹ := hθ.2.le.trans hT_lt_inv.le
      have hθT : θ ∈ Ioc 0 T := ⟨hθ0, hθ.2.le⟩
      have hd_θ1 : 1 ≤ dOfTheta ν θ :=
        T22Sub.one_le_dOfTheta hν0 ((hν3_le_r.trans hrb).trans hb_θ)
      have hVθ := (T22Sub.ctCanonicalBranchProps P hP m hm).2.1 ν θ hν0 hθ0 hd_θ1
      have hZθ_mem := heatColumn_memLp P hm0 hν0 hθ0 hθν hw
      have hdiff_eq : fZ P ν μ w θ - fCanWt P ν μ θ =
          (θ : ℂ) ^ (μ + 1 / 2) * ((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) *
            quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ) := by
        rw [quadQ_sub hm3 hZθ_mem hVθ.1, hVθ.2.2.2]
        unfold fZ fCanWt
        ring
      have hL := (hLong ν ⟨hν0, hν_le_long⟩ tr hbuc).2 w u hw θ hb_θ hθν
      let W : ℝ := Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re
      have hW0 : 0 < W := by dsimp [W]; positivity
      let R_θ : ℝ := ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3)
      have hR_θ0 : 0 ≤ R_θ := by dsimp [R_θ]; positivity
      have hWq_enn : ENNReal.ofReal
            (W * ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖) ≤
          ENNReal.ofReal (C_q' * C_long' * R_θ) := by
        rw [ENNReal.ofReal_mul hW0.le]
        calc ENNReal.ofReal W *
              ENNReal.ofReal ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖
            ≤ ENNReal.ofReal W * (ENNReal.ofReal C_q' *
                xNorm (dOfTheta ν θ) m (heatColumn P ν w θ - canonicalPeriodized P ν θ)) := by
              refine mul_le_mul_of_nonneg_left ?_ zero_le
              exact (hCq (dOfTheta ν θ) _ (hZθ_mem.sub hVθ.1)).trans
                (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
          _ = ENNReal.ofReal C_q' *
              (ENNReal.ofReal W *
                xNorm (dOfTheta ν θ) m (heatColumn P ν w θ - canonicalPeriodized P ν θ)) := by
              ring
          _ ≤ ENNReal.ofReal C_q' * ENNReal.ofReal (C_long' * R_θ) := by
              refine mul_le_mul_of_nonneg_left (hL.trans ?_) zero_le
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_max_left _ _) hR_θ0)
          _ = ENNReal.ofReal (C_q' * C_long' * R_θ) := by
              rw [← ENNReal.ofReal_mul hCq'0, mul_assoc]
      have hWq_real : W *
            ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖ ≤
          C_q' * C_long' * R_θ :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hWq_enn
      have hR_bd : R_θ ≤ (1 + b⁻¹ + (a₁ * b)⁻¹) * ν := by
        have ht2 : (ν ^ 3) ^ 2 / θ ≤ b⁻¹ * ν := by
          have hpow6 : (ν ^ 3) ^ 2 = ν ^ 6 := by ring
          rw [hpow6]
          calc ν ^ 6 / θ ≤ ν ^ 6 / b :=
                div_le_div_of_nonneg_left (pow_nonneg hν0.le 6) hb0 hb_θ
            _ ≤ ν / b := div_le_div_of_nonneg_right hν6_le_ν hb0.le
            _ = b⁻¹ * ν := by ring
        have ht3 : Real.exp (-a₁ * θ / ν ^ 3) ≤ (a₁ * b)⁻¹ * ν := by
          let X : ℝ := a₁ * θ / ν ^ 3
          have hX0 : 0 < X := by dsimp [X]; positivity
          have hexp_ge : X ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
          have hexp_le : Real.exp (-a₁ * θ / ν ^ 3) ≤ X⁻¹ := by
            have heq : -a₁ * θ / ν ^ 3 = -X := by dsimp [X]; ring
            rw [heq, Real.exp_neg]
            exact inv_anti₀ hX0 hexp_ge
          have hXinv : X⁻¹ = ν ^ 3 / (a₁ * θ) := by dsimp [X]; rw [inv_div]
          calc Real.exp (-a₁ * θ / ν ^ 3) ≤ ν ^ 3 / (a₁ * θ) := hXinv ▸ hexp_le
            _ ≤ ν ^ 3 / (a₁ * b) :=
                div_le_div_of_nonneg_left (pow_nonneg hν0.le 3) (mul_pos ha₁ hb0)
                  (mul_le_mul_of_nonneg_left hb_θ ha₁.le)
            _ ≤ ν / (a₁ * b) := div_le_div_of_nonneg_right hν3_le_ν (mul_pos ha₁ hb0).le
            _ = (a₁ * b)⁻¹ * ν := by ring
        dsimp [R_θ]
        linarith
      have hWinv : W⁻¹ = Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re) := by
        dsimp [W]
        rw [mul_inv, ← Real.exp_neg, ← Real.rpow_neg hθ0.le]
        congr 2; ring
      have hq_bd : ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖ ≤
          C_q' * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν *
            (Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) := by
        calc ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖
            = (W * ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖) *
                W⁻¹ := by field_simp [hW0.ne']
          _ ≤ (C_q' * C_long' * ((1 + b⁻¹ + (a₁ * b)⁻¹) * ν)) * W⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hW0.le)
              exact hWq_real.trans (mul_le_mul_of_nonneg_left hR_bd (by positivity))
          _ = C_q' * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν *
                (Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) := by
              rw [hWinv]; ring
      have hpow_le : ‖(θ : ℂ) ^ (μ + 1 / 2)‖ ≤ θ ^ (3 / 4 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hθ0]
        have hre : (μ + 1 / 2).re = μ.re + 1 / 2 := by simp
        rw [hre]
        exact Real.rpow_le_rpow_of_exponent_le hθ1 (by linarith)
      have h12 : ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖ ≤
          8 * θ ^ (3 / 4 : ℝ) := by
        calc ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖
            ≤ θ ^ (3 / 4 : ℝ) * 8 :=
              mul_le_mul hpow_le (hwt_eight θ hθT) (norm_nonneg _) (by positivity)
          _ = 8 * θ ^ (3 / 4 : ℝ) := mul_comm _ _
      have hrpow_comb : θ ^ (3 / 4 : ℝ) *
            (Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) =
          Real.exp (-P.eigenvalue.re * θ) * θ ^ (3 / 4 - P.kappa.re) := by
        rw [mul_left_comm, ← Real.rpow_add hθ0, sub_eq_add_neg]
      rw [hdiff_eq, norm_mul, norm_mul]
      calc ‖(θ : ℂ) ^ (μ + 1 / 2)‖ * ‖((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2)‖ *
            ‖quadQ (dOfTheta ν θ) (heatColumn P ν w θ - canonicalPeriodized P ν θ)‖
          ≤ (8 * θ ^ (3 / 4 : ℝ)) *
              (C_q' * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν *
                (Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re))) :=
            mul_le_mul h12 hq_bd (norm_nonneg _) (by positivity)
        _ = (8 * C_q' * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν) *
              (θ ^ (3 / 4 : ℝ) *
                (Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re))) := by ring
        _ = K_fac * (Real.exp (-P.eigenvalue.re * θ) * θ ^ (3 / 4 - P.kappa.re)) := by
            rw [hrpow_comb]
    have h1 : ‖∫ θ in Ioo b T, (fZ P ν μ w θ - fCanWt P ν μ θ)‖ ≤
        ∫ θ in Ioo b T, ‖fZ P ν μ w θ - fCanWt P ν μ θ‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ θ in Ioo b T, ‖fZ P ν μ w θ - fCanWt P ν μ θ‖ ≤
        K_fac * ∫ θ in Ioo b T, Real.exp (-P.eigenvalue.re * θ) * θ ^ (3 / 4 - P.kappa.re) := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hint_fZ_bT.sub hint_fCanWt_bT).norm
        ((hint_exp.mono_set Ioo_subset_Ioi_self).const_mul K_fac) measurableSet_Ioo hpt
    have h3 : ∫ θ in Ioo b T, Real.exp (-P.eigenvalue.re * θ) * θ ^ (3 / 4 - P.kappa.re) ≤
        M_exp := by
      refine (setIntegral_mono_set hint_exp ?_ ?_).trans hbd_exp
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
        have hθ0 : 0 < θ := hb0.trans hθ
        positivity
      · exact Eventually.of_forall fun _ h => h.1
    have h4 : K_fac * M_exp = K_long * ν := by dsimp [K_fac, K_long]; ring
    exact (h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hK_fac0))).trans
      (h4.le.trans hν_long_sm.le)
  -- Piece 5: ‖I₅‖ ≤ ε / 6 (combined weight error on (r, b) ∪ (b, T))
  have hb₅ : ‖I₅‖ ≤ ε / 6 := by
    have hint_wt_diff_rT : IntegrableOn (fun θ => fCanWt P ν μ θ - fCan P μ θ) (Ioc r T) :=
      (hint_fCanWt_0T.mono_set (Ioc_subset_Ioc_left hr0.le)).sub
        (hint_fCan.mono_set (fun _ h => hr0.trans h.1))
    have hI₅_eq : I₅ = ∫ θ in Ioc r T, (fCanWt P ν μ θ - fCan P μ θ) := by
      dsimp [I₅]
      rw [← integral_sub hint_fCanWt_rb hint_fCan_rb,
        ← integral_sub hint_fCanWt_bT hint_fCan_bT,
        ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
        ← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          (hint_wt_diff_rT.mono_set (Ioc_subset_Ioc_right hbT.le))
          (hint_wt_diff_rT.mono_set (Ioc_subset_Ioc_left hrb)),
        Ioc_union_Ioc_eq_Ioc hrb hbT.le]
    rw [hI₅_eq]
    have hpt : ∀ θ ∈ Ioc r T, ‖fCanWt P ν μ θ - fCan P μ θ‖ ≤
        (4 * (M_K + 3) * Real.sqrt ν) * gCan P θ := by
      intro θ hθ
      have hθ0 : 0 < θ := hr0.trans hθ.1
      have hθT : θ ∈ Ioc 0 T := ⟨hθ0, hθ.2⟩
      have hfac : fCanWt P ν μ θ - fCan P μ θ =
          (((1 - ν * θ : ℝ) : ℂ) ^ (-μ - 5 / 2) - 1) * fCan P μ θ := by
        unfold fCanWt fCan; ring
      rw [hfac, norm_mul]
      exact mul_le_mul (hwt_diff θ hθT) (norm_fCan_le_gCan P hθ0 hμ0 hμ14)
        (norm_nonneg _) (by positivity)
    have h1 : ‖∫ θ in Ioc r T, (fCanWt P ν μ θ - fCan P μ θ)‖ ≤
        ∫ θ in Ioc r T, ‖fCanWt P ν μ θ - fCan P μ θ‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ θ in Ioc r T, ‖fCanWt P ν μ θ - fCan P μ θ‖ ≤
        (4 * (M_K + 3) * Real.sqrt ν) * ∫ θ in Ioc r T, gCan P θ := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on hint_wt_diff_rT.norm
        ((hint_gCan.mono_set (fun _ h => hr0.trans h.1)).const_mul _) measurableSet_Ioc hpt
    have h3 : ∫ θ in Ioc r T, gCan P θ ≤ I_G := by
      refine setIntegral_mono_set hint_gCan ?_ (Eventually.of_forall fun _ h => hr0.trans h.1)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      exact gCan_nonneg P hθ.le
    exact (h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))).trans hν_wt_p5.le
  -- Piece 6: ‖I₆‖ ≤ ε / 6 (canonical upper tail on (T, ∞))
  have hb₆ : ‖I₆‖ ≤ ε / 6 := by
    have h1 : ‖I₆‖ ≤ ∫ θ in Ioi T, ‖fCan P μ θ‖ := norm_integral_le_integral_norm _
    have h2 : ∫ θ in Ioi T, ‖fCan P μ θ‖ ≤ ∫ θ in Ioi T, gCan P θ :=
      setIntegral_mono_on (hint_fCan.mono_set (Ioi_subset_Ioi (hT₀_pos.trans hT₀_lt_T).le)).norm
        (hint_gCan.mono_set (Ioi_subset_Ioi (hT₀_pos.trans hT₀_lt_T).le)) measurableSet_Ioi
        fun θ hθ => norm_fCan_le_gCan P ((hT₀_pos.trans hT₀_lt_T).trans hθ) hμ0 hμ14
    have h3 : ∫ θ in Ioi T, gCan P θ ≤ ∫ θ in Ioi T₀, gCan P θ := by
      refine setIntegral_mono_set (hint_gCan.mono_set (Ioi_subset_Ioi hT₀_pos.le)) ?_
        (Eventually.of_forall fun _ h => hT₀_lt_T.trans h)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      exact gCan_nonneg P (hT₀_pos.trans hθ).le
    exact (h1.trans (h2.trans h3)).trans hT₀_p6.le
  -- Combine all 6 bounds
  rw [hdecomp]
  calc ‖I₁ - I₂ + I₃ + I₄ + I₅ - I₆‖
      ≤ ‖I₁ - I₂ + I₃ + I₄ + I₅‖ + ‖I₆‖ := norm_sub_le _ _
    _ ≤ ‖I₁ - I₂ + I₃ + I₄‖ + ‖I₅‖ + ‖I₆‖ := by linarith [norm_add_le (I₁ - I₂ + I₃ + I₄) I₅]
    _ ≤ ‖I₁ - I₂ + I₃‖ + ‖I₄‖ + ‖I₅‖ + ‖I₆‖ := by linarith [norm_add_le (I₁ - I₂ + I₃) I₄]
    _ ≤ ‖I₁ - I₂‖ + ‖I₃‖ + ‖I₄‖ + ‖I₅‖ + ‖I₆‖ := by linarith [norm_add_le (I₁ - I₂) I₃]
    _ ≤ ‖I₁‖ + ‖I₂‖ + ‖I₃‖ + ‖I₄‖ + ‖I₅‖ + ‖I₆‖ := by linarith [norm_sub_le I₁ I₂]
    _ ≤ ε := by linarith

end UnforcedLeray.Short.IIIa
end

