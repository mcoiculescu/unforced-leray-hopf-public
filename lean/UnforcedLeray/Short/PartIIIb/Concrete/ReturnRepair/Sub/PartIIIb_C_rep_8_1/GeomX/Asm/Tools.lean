import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Defs
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `PartIII-b:C/rep/8/1/1/1/asm`: tools of the stream-cut assembly

Source `the November 2 reference manuscript`
lines 5415-5427 (normalized phase `L²` estimates), 2666-2668 (the chart), 4178-4186.

* `cellN`: the normalized phase `L²` norm of an extended-real function of the cell variable `q`;
  `cellL2 = cellN ∘ ofReal`, monotone, subadditive (Minkowski), homogeneous, constants;
* `cellN_lintegral_le`: Minkowski's integral inequality for `∫_r^∞ w(ρ) F(q, ρ) dρ` (Cauchy–Schwarz
  against the density `w b` and Tonelli);
* `cellN_shift`: `c`-periodic functions have shift-invariant cell norms;
* `rayPow_le`: `r^{-(j+1)} ∫_r^∞ ρ^j (R/ρ)^5 dρ ≤ (R/r)^5` for `j ≤ 2`;
* `wardX0_periodic`, `dPhase_periodic`: the old-source responses have the phase period `2c/R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomXAsm

/-! ## 1. The cell norm -/

/-- The normalized cell measure `c⁻¹ dq` on `[-c/2, c/2)`. -/
def cellμ (c : ℝ) : Measure ℝ := ENNReal.ofReal c⁻¹ • volume.restrict (Ico (-c / 2) (c / 2))

instance cellμ_sFinite (c : ℝ) : SFinite (cellμ c) := by
  unfold cellμ
  infer_instance

/-- The normalized phase `L²` norm `(c⁻¹∫_cell Φ²)^{1/2}` of an extended-real function. -/
def cellN (c : ℝ) (Φ : ℝ → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ q, Φ q ^ 2 ∂cellμ c) ^ (1 / 2 : ℝ)

theorem lintegral_cellμ (c : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ q, f q ∂cellμ c = ∫⁻ q in Ico (-c / 2) (c / 2), ENNReal.ofReal c⁻¹ * f q := by
  unfold cellμ
  rw [lintegral_smul_measure, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

theorem cellL2_eq_cellN (R c : ℝ) (F : ℝ → Space → ℝ) (s η : ℝ) :
    cellL2 R c F s η = cellN c (fun q => ENNReal.ofReal
      (F (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))))) := by
  unfold cellL2 cellN
  rw [lintegral_cellμ]

theorem cellN_mono {c : ℝ} {Φ Ψ : ℝ → ℝ≥0∞} (h : ∀ q, Φ q ≤ Ψ q) : cellN c Φ ≤ cellN c Ψ := by
  unfold cellN
  gcongr with q
  exact h q

theorem cellN_add_le {c : ℝ} {Φ Ψ : ℝ → ℝ≥0∞} (hΦ : AEMeasurable Φ (cellμ c))
    (hΨ : AEMeasurable Ψ (cellμ c)) :
    cellN c (fun q => Φ q + Ψ q) ≤ cellN c Φ + cellN c Ψ := by
  have h := ENNReal.lintegral_Lp_add_le hΦ hΨ (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two, Pi.add_apply] at h
  exact h

theorem cellN_const_mul (c : ℝ) {a : ℝ≥0∞} (ha : a ≠ ∞) (Φ : ℝ → ℝ≥0∞) :
    cellN c (fun q => a * Φ q) = a * cellN c Φ := by
  unfold cellN
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ha),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem rpow_half_sq (X : ℝ≥0∞) : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sq_rpow_half (X : ℝ≥0∞) : (X ^ 2) ^ (1 / 2 : ℝ) = X := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem le_sq_of_rpow_half_le {X Y : ℝ≥0∞} (h : X ^ (1 / 2 : ℝ) ≤ Y) : X ≤ Y ^ 2 := by
  have h2 : (X ^ (1 / 2 : ℝ)) ^ 2 ≤ Y ^ 2 := by gcongr
  rwa [rpow_half_sq] at h2

theorem rpow_half_le_of_le_sq {X Y : ℝ≥0∞} (h : X ≤ Y ^ 2) : X ^ (1 / 2 : ℝ) ≤ Y := by
  calc X ^ (1 / 2 : ℝ) ≤ (Y ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = Y := sq_rpow_half Y

theorem cellN_const {c : ℝ} (hc : 0 < c) (a : ℝ≥0∞) : cellN c (fun _ => a) = a := by
  unfold cellN
  rw [lintegral_const]
  have : cellμ c univ = 1 := by
    unfold cellμ
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
    rw [show c / 2 - -c / 2 = c by ring, inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  rw [this, mul_one, sq_rpow_half]

/-- Cauchy–Schwarz against the density `w b`: `(∫ w F)² ≤ (∫ w b)(∫ w F² / b)`. -/
theorem lintegral_sq_le_weighted {r : ℝ} {f w b : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hw : Measurable w) (hb : Measurable b) (hb0 : ∀ ρ ∈ Ioi r, b ρ ≠ 0)
    (hbt : ∀ ρ, b ρ ≠ ∞) :
    (∫⁻ ρ in Ioi r, w ρ * f ρ) ^ 2 ≤
      (∫⁻ ρ in Ioi r, w ρ * b ρ) * ∫⁻ ρ in Ioi r, w ρ * f ρ ^ 2 * (b ρ)⁻¹ := by
  set ν' : Measure ℝ := volume.restrict (Ioi r)
  have hwb : Measurable fun ρ => w ρ * b ρ := hw.mul hb
  have hh : Measurable fun ρ => f ρ * (b ρ)⁻¹ := hf.mul hb.inv
  have e1 : ∫⁻ ρ, w ρ * f ρ ∂ν' =
      ∫⁻ ρ, f ρ * (b ρ)⁻¹ ∂(ν'.withDensity fun ρ => w ρ * b ρ) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hwb hh]
    refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    simp only [Pi.mul_apply]
    rw [show w ρ * b ρ * (f ρ * (b ρ)⁻¹) = w ρ * f ρ * (b ρ * (b ρ)⁻¹) by ring,
      ENNReal.mul_inv_cancel (hb0 ρ hρ) (hbt ρ), mul_one]
  have e2 : ∫⁻ ρ, (fun _ => (1 : ℝ≥0∞)) ρ ^ (2 : ℝ) ∂(ν'.withDensity fun ρ => w ρ * b ρ) =
      ∫⁻ ρ, w ρ * b ρ ∂ν' := by
    simp only [ENNReal.one_rpow, lintegral_one]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have e3 : ∫⁻ ρ, (f ρ * (b ρ)⁻¹) ^ (2 : ℝ) ∂(ν'.withDensity fun ρ => w ρ * b ρ) =
      ∫⁻ ρ, w ρ * f ρ ^ 2 * (b ρ)⁻¹ ∂ν' := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hwb (hh.pow_const _)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
    simp only [Pi.mul_apply, ENNReal.rpow_two]
    have hb1 : b ρ * (b ρ)⁻¹ = 1 := ENNReal.mul_inv_cancel (hb0 ρ hρ) (hbt ρ)
    calc w ρ * b ρ * (f ρ * (b ρ)⁻¹) ^ 2
        = w ρ * f ρ ^ 2 * (b ρ)⁻¹ * (b ρ * (b ρ)⁻¹) := by ring
      _ = w ρ * f ρ ^ 2 * (b ρ)⁻¹ := by rw [hb1, mul_one]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν'.withDensity fun ρ => w ρ * b ρ)
    Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞)) (g := fun ρ => f ρ * (b ρ)⁻¹)
    aemeasurable_const hh.aemeasurable
  simp only [Pi.mul_apply, one_mul] at hH
  rw [e2, e3] at hH
  rw [e1]
  calc (∫⁻ ρ, f ρ * (b ρ)⁻¹ ∂(ν'.withDensity fun ρ => w ρ * b ρ)) ^ 2
      ≤ ((∫⁻ ρ, w ρ * b ρ ∂ν') ^ (1 / 2 : ℝ) *
          (∫⁻ ρ, w ρ * f ρ ^ 2 * (b ρ)⁻¹ ∂ν') ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- **Minkowski's integral inequality** for the cell norm of a ray integral, with a per-ray-point
bound `cellN (F · ρ) ≤ K b(ρ)`. -/
theorem cellN_lintegral_le {c r : ℝ} {F : ℝ → ℝ → ℝ≥0∞} {w b : ℝ → ℝ≥0∞} {K : ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (hw : Measurable w) (hb : Measurable b)
    (hwt : ∀ ρ, w ρ ≠ ∞) (hb0 : ∀ ρ ∈ Ioi r, b ρ ≠ 0) (hbt : ∀ ρ, b ρ ≠ ∞)
    (hB : ∀ ρ ∈ Ioi r, cellN c (fun q => F q ρ) ≤ K * b ρ) :
    cellN c (fun q => ∫⁻ ρ in Ioi r, w ρ * F q ρ) ≤ K * ∫⁻ ρ in Ioi r, w ρ * b ρ := by
  set S := ∫⁻ ρ in Ioi r, w ρ * b ρ
  have hFq : ∀ q, Measurable fun ρ => F q ρ := fun q => hF.comp measurable_prodMk_left
  have hG : Measurable (Function.uncurry fun q ρ => w ρ * F q ρ ^ 2 * (b ρ)⁻¹) := by
    have h1 : Measurable fun p : ℝ × ℝ => w p.2 := hw.comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ => (b p.2)⁻¹ := (hb.comp measurable_snd).inv
    exact (h1.mul (hF.pow_const 2)).mul h2
  apply rpow_half_le_of_le_sq
  have hS : K ^ 2 * S = ∫⁻ ρ in Ioi r, K ^ 2 * (w ρ * b ρ) :=
    (lintegral_const_mul _ (hw.mul hb)).symm
  calc ∫⁻ q, (∫⁻ ρ in Ioi r, w ρ * F q ρ) ^ 2 ∂cellμ c
      ≤ ∫⁻ q, S * (∫⁻ ρ in Ioi r, w ρ * F q ρ ^ 2 * (b ρ)⁻¹) ∂cellμ c :=
        lintegral_mono fun q => lintegral_sq_le_weighted (hFq q) hw hb hb0 hbt
    _ = S * ∫⁻ q, (∫⁻ ρ in Ioi r, w ρ * F q ρ ^ 2 * (b ρ)⁻¹) ∂cellμ c := by
        rw [lintegral_const_mul]
        exact hG.lintegral_prod_right'
    _ = S * ∫⁻ ρ in Ioi r, (∫⁻ q, w ρ * F q ρ ^ 2 * (b ρ)⁻¹ ∂cellμ c) := by
        rw [lintegral_lintegral_swap hG.aemeasurable]
    _ = S * ∫⁻ ρ in Ioi r, w ρ * (b ρ)⁻¹ * (∫⁻ q, F q ρ ^ 2 ∂cellμ c) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top (hwt ρ) (ENNReal.inv_ne_top.2 (hb0 ρ hρ)))]
        congr 1
        ext q
        ring
    _ ≤ S * ∫⁻ ρ in Ioi r, w ρ * (b ρ)⁻¹ * (K * b ρ) ^ 2 := by
        gcongr S * ?_
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        gcongr
        exact le_sq_of_rpow_half_le (hB ρ hρ)
    _ = S * (K ^ 2 * S) := by
        rw [hS]
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
        have hb1 : b ρ * (b ρ)⁻¹ = 1 := ENNReal.mul_inv_cancel (hb0 ρ hρ) (hbt ρ)
        calc w ρ * (b ρ)⁻¹ * (K * b ρ) ^ 2 = K ^ 2 * (w ρ * b ρ) * (b ρ * (b ρ)⁻¹) := by ring
          _ = K ^ 2 * (w ρ * b ρ) := by rw [hb1, mul_one]
    _ = (K * S) ^ 2 := by ring

/-! ## 2. Shift invariance of the cell integral for `c`-periodic integrands -/

theorem lintegral_cell_shift {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞} (hf : ∀ q, f (q + c) = f q)
    (a : ℝ) :
    ∫⁻ q in Ico (-c / 2) (c / 2), f (q + a) = ∫⁻ q in Ico (-c / 2) (c / 2), f q := by
  have hI : Ico (-c / 2) (c / 2) =ᵐ[volume] Ioc (-c / 2) (-c / 2 + c) := by
    rw [show -c / 2 + c = c / 2 by ring]
    exact Ico_ae_eq_Ioc
  rw [setLIntegral_congr hI, setLIntegral_congr hI]
  have hpre : (fun q : ℝ => q + a) ⁻¹' Ioc (-c / 2 + a) (-c / 2 + a + c) =
      Ioc (-c / 2) (-c / 2 + c) := by
    ext q
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have e := (measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding f (Ioc (-c / 2 + a) (-c / 2 + a + c))
  rw [hpre] at e
  rw [e]
  have hper : ∀ (g : AddSubgroup.zmultiples c) (x : ℝ), f (g +ᵥ x) = f x := by
    intro g x
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
    have hP : Function.Periodic f c := hf
    rw [AddSubgroup.vadd_def, vadd_eq_add, ← hk, add_comm]
    exact hP.zsmul k x
  exact (isAddFundamentalDomain_Ioc hc (-c / 2 + a)).setLIntegral_eq
    (isAddFundamentalDomain_Ioc hc (-c / 2)) f hper

theorem cellN_shift {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞} (hf : ∀ q, f (q + c) = f q) (a : ℝ) :
    cellN c (fun q => f (q + a)) = cellN c f := by
  unfold cellN
  rw [lintegral_cellμ, lintegral_cellμ]
  congr 1
  exact lintegral_cell_shift hc (f := fun q => ENNReal.ofReal c⁻¹ * f q ^ 2)
    (fun q => by simp only [hf q]) a

/-! ## 3. The ray power integral -/

theorem rayPow_le {j : ℕ} (hj : j ≤ 2) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ENNReal.ofReal (r⁻¹ ^ (j + 1)) * ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) ≤
      ENNReal.ofReal ((R / r) ^ 5) := by
  have hjr : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have ha : (j : ℝ) - 5 < -1 := by linarith
  have hkey : ∀ ρ ∈ Ioi r, ρ ^ j * (R / ρ) ^ 5 = R ^ 5 * ρ ^ ((j : ℝ) - 5) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hr.trans hρ
    rw [Real.rpow_sub hρ0, Real.rpow_natCast, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp
  have hint : IntegrableOn (fun ρ : ℝ => R ^ 5 * ρ ^ ((j : ℝ) - 5)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt ha hr).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)] fun ρ : ℝ => R ^ 5 * ρ ^ ((j : ℝ) - 5) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact mul_nonneg (pow_nonneg hR 5) (Real.rpow_nonneg (hr.trans hρ).le _)
  have e1 : ∫⁻ ρ in Ioi r, ENNReal.ofReal (ρ ^ j * (R / ρ) ^ 5) =
      ENNReal.ofReal (R ^ 5 * (-r ^ ((j : ℝ) - 5 + 1) / ((j : ℝ) - 5 + 1))) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => by rw [hkey ρ hρ]),
      ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      integral_Ioi_rpow_of_lt ha hr]
  have e2 : r ^ ((j : ℝ) - 5 + 1) = r ^ j / r ^ 4 := by
    rw [show (j : ℝ) - 5 + 1 = (j : ℝ) - 4 by ring, Real.rpow_sub hr, Real.rpow_natCast,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e1, e2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h4 : (0 : ℝ) < 4 - j := by linarith
  have e3 : r⁻¹ ^ (j + 1) * (R ^ 5 * (-(r ^ j / r ^ 4) / ((j : ℝ) - 5 + 1))) =
      (R / r) ^ 5 * (4 - (j : ℝ))⁻¹ := by
    have h5 : (j : ℝ) - 5 + 1 = -(4 - j) := by ring
    have hrj : r ^ j ≠ 0 := pow_ne_zero j hr.ne'
    rw [h5, inv_pow, pow_succ, div_pow]
    field_simp
  rw [e3]
  apply mul_le_of_le_one_right (by positivity)
  rw [inv_le_one₀ h4]
  linarith

/-! ## 4. The phase period of the old-source responses -/

theorem chartOf_add_period {R c : ℝ} (hR : R ≠ 0) (hc : c ≠ 0) (z : Space) (τ : ℝ) :
    NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
  unfold NearInst.chartOf
  have h1 : R * (τ + 2 * c / R) / 2 = R * τ / 2 + c := by field_simp
  have key : ∀ x : ℝ, x + c - c * (⌊(x + c) / c + 1 / 2⌋ : ℝ) = x - c * (⌊x / c + 1 / 2⌋ : ℝ) := by
    intro x
    have : (x + c) / c + 1 / 2 = (x / c + 1 / 2) + 1 := by field_simp; ring
    rw [this, Int.floor_add_one]
    push_cast
    ring
  rw [h1, ← add_assoc, key]

theorem cartLift_add_period {R c : ℝ} (hR : R ≠ 0) (hc : c ≠ 0) (T : Chart → Ten3) (τ : ℝ)
    (z : Space) : NearInst.cartLift R c T (τ + 2 * c / R) z = NearInst.cartLift R c T τ z := by
  unfold NearInst.cartLift
  rw [chartOf_add_period hR hc]

theorem sepW_add_period (ν : ℝ) (μ : ℂ) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} {P : ℝ}
    (hT : ∀ t, T (t + P) = T t) (y : Space) (τ : ℝ) :
    IIIa.sepW ν μ T y (τ + P) = IIIa.sepW ν μ T y τ := by
  unfold IIIa.sepW
  simp only [add_right_comm τ P, hT]

theorem wardX0_add_period (ν μ : ℝ) {R c : ℝ} (hR : R ≠ 0) (hc : c ≠ 0) (g : Chart → Ten3)
    (τ : ℝ) : wardX0 ν μ R c g (τ + 2 * c / R) = wardX0 ν μ R c g τ := by
  funext y
  have hT : ∀ t, oldPhys R c g (t + 2 * c / R) = oldPhys R c g t :=
    fun t => funext fun z => cartLift_add_period hR hc g t z
  unfold wardX0
  rw [sepW_add_period _ _ hT, sepW_add_period _ _ hT]

theorem dPhase_add_period (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L) (τ : ℝ) (y : Space) :
    dPhase Pl K L μ T (τ + 2 * cOf L.ν / L.ε⁻¹) y = dPhase Pl K L μ T τ y := by
  have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero L.ε_pos.ne'
  have hc : cOf L.ν ≠ 0 := by unfold cOf; exact inv_ne_zero (pow_ne_zero 2 L.ν_pos.ne')
  unfold dPhase zAct zMid
  rw [wardX0_add_period _ _ hR hc, wardX0_add_period _ _ hR hc]

end GeomXAsm

end UnforcedLeray.Short.PartIIIb.Concrete
