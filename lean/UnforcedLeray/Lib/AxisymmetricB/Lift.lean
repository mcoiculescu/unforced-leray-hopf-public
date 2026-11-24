import UnforcedLeray.Lib.Axisymmetric
import UnforcedLeray.Lib.Cylinder

/-!
# AX04 (measure part): the age-weighted cylinder measures and the ring lift `N_v`


§5 Layer 3, target AX04 (`Axi/Lift.lean`); Wave 2 block 2J AXI1 of `scoping/README.md`;
bypass BP8 (age-weighted spaces are flat `L^p` spaces on `(0,∞) × ℝ × ℝ` with a density).
Blueprint units served: B0219 (`eq:m3-cylinder-measure`, tex 3256–3268), B0228 (tex 3684–3718),
B0283 (`background:eq:2.22`, tex 5229–5235), B0417 (`eq:m4-free-spaces`, tex 7272–7297),
B0482 (`eq:free-stress-B1`, tex 7920–7949), B0550 (`eq:stress-setup:3.1`, tex 8724–8732),
B0783 (`eq:st18-t00640`, tex 11116–11127).

* `ageμ c a = s^a ds|_{s>0} ⊗ dξ/c dη|_{cell}` (`Cyl.avgμ c`, decision D1). With `a = q/2 − 5/2`
  this is the measure of `H_q` (tex 3258); `a = −3/2` gives `H`, `a = −1/2` gives `H_T`,
  `a = 1/2` gives `H_g` (tex 7272–7276).
* `Nv R b τ y = √s (b_r e_r + b_z e_z)` at the chart point `(s, ξ, η)` of `y` (tex 2077,
  3260: `N_v b = √s b`), `NT R T τ y = s · (frame lift of T)` (tex 7276: `N_T T = s T`).
* `lintegral_Nv_rpow` (tex 3260, 3700–3704, 5233): the phase average over one period
  `P = 2c/R` of `∫ |N_v b|^q dy` is `πR² ∫ |b|^q dageμ c (q/2 − 5/2)`;
  `eLpNorm_Nv`: `‖N_v b‖_{Y_q} = (πR²)^{1/q} ‖b‖_{H_q}` on the normalized phase measure.
* `lintegral_NT_sq` (tex 7276, 8730): `‖N_T T‖²_{Y₂} = πR² ‖T‖²_{H_T}` (Frobenius).
* `lintegral_Ms`, `eLpNorm_Ms` (tex 3262–3264, 5235, 11116–11120): `g ↦ s g` is an isometry
  from `L^q(s^{3q/2−5/2})` into `H_q`: `‖s g‖_{ageμ (q/2−5/2)} = ‖g‖_{ageμ (3q/2−5/2)}`.

Junk values. On the axis `ϱ = 0`, Lean gives `age = 0`, `e_r = 0`; the axis is Lebesgue-null
(`ae_not_mem_axis`), so the integral identities are unaffected. The profile `b` is a function on
all of `ℝ × ℝ × ℝ`; only its values on `s > 0` enter, and the identities assume `b` is
`c`-periodic in `ξ` (as in tex 3256: profiles live on `(0,∞) × T_c × ℝ`). The exponent `q` is
real with `0 < q`; `‖·‖ₑ ^ q` is the extended-real power.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Axi

/-! ### The age-weighted cylinder measure -/

/-- The age-weighted cylinder measure `s^a ds × dξ/c dη` on `(0,∞) × cell` (BP8; tex 3258,
7272–7276). The cell measure is the normalized `Cyl.avgμ c = c⁻¹ dξ dη|_{cell}` (D1). -/
def ageμ (c a : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)).prod
    (Cyl.avgμ c)

theorem measurable_ofReal_rpow (a : ℝ) : Measurable fun s : ℝ => ENNReal.ofReal (s ^ a) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const a)

theorem qCell_eq_cell (c : ℝ) : qCell c = Cyl.cell c := rfl

/-- `∫ f dageμ c a = ∫_{(0,∞) × cell} c⁻¹ s^a f(s, ξ, η)`. -/
instance sFinite_cellμ (c : ℝ) : SFinite (Cyl.cellμ c) := by
  unfold Cyl.cellμ
  infer_instance

/-- `∫ f dageμ c a = ∫_{(0,∞) × cell} c⁻¹ s^a f(s, ξ, η)`. -/
theorem lintegral_ageμ {c : ℝ} (hc : 0 < c) (a : ℝ) {f : ℝ × (ℝ × ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ p, f p ∂ageμ c a =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ qCell c, ENNReal.ofReal (c⁻¹ * p.1 ^ a) * f p := by
  have hw : Measurable fun z : ℝ × (ℝ × ℝ) => ENNReal.ofReal (z.1 ^ a) :=
    (measurable_ofReal_rpow a).comp measurable_fst
  rw [ageμ, Cyl.avgμ, Cyl.cellμ, Measure.prod_smul_right,
    prod_withDensity_left (measurable_ofReal_rpow a), Measure.prod_restrict,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hw hf, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, qCell_eq_cell, Measure.volume_eq_prod]
  refine lintegral_congr fun p => ?_
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]

/-! ### The frame vector and the lift `N_v` -/

/-- The frame map `v ↦ v_r e_r + v_z e_z` at `y`. -/
def frameL (y : Space) : Merid →L[ℝ] Space :=
  (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).smulRight (eR y) +
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).smulRight e3

theorem frameL_apply (y : Space) (v : Merid) : frameL y v = v 0 • eR y + v 1 • e3 := by
  simp [frameL]

theorem liftMer_eq_frameL (b : ℝ × ℝ → Merid) (y : Space) :
    liftMer b y = frameL y (b (mer y)) := by
  rw [frameL_apply]
  rfl

/-- Off the axis the frame map is an isometry. -/
theorem norm_frameL {y : Space} (hy : y ∉ axis) (v : Merid) : ‖frameL y v‖ = ‖v‖ := by
  have h := norm_liftMer (fun _ => v) hy
  rwa [liftMer_eq_frameL] at h

/-- **AX04 `Nv`.** The ring lift `N_v b(τ, y) = √s (b_r e_r + b_z e_z)` at the chart point
`(s, ξ, η) = (R²/ϱ², Rτ/2 − (R/2) log s, R y₃/ϱ)` (tex 2077, 3260, 7276). -/
def Nv (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) (y : Space) : Space :=
  √(age R y) • frameL y (b (chart R τ y))

theorem Nv_add (R : ℝ) (b b' : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) (y : Space) :
    Nv R (b + b') τ y = Nv R b τ y + Nv R b' τ y := by
  simp only [Nv, Pi.add_apply, map_add, smul_add]

theorem Nv_sub (R : ℝ) (b b' : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) (y : Space) :
    Nv R (b - b') τ y = Nv R b τ y - Nv R b' τ y := by
  simp only [Nv, Pi.sub_apply, map_sub, smul_sub]

theorem Nv_smul (R k : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) (y : Space) :
    Nv R (k • b) τ y = k • Nv R b τ y := by
  simp only [Nv, Pi.smul_apply, map_smul, smul_comm (√(age R y)) k]

theorem age_nonneg (R : ℝ) (y : Space) : 0 ≤ age R y :=
  div_nonneg (sq_nonneg R) (sq_nonneg _)

theorem norm_Nv (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    ‖Nv R b τ y‖ = √(age R y) * ‖b (chart R τ y)‖ := by
  rw [Nv, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_frameL hy]

theorem sqrt_rpow {s : ℝ} (hs : 0 ≤ s) (q : ℝ) : √s ^ q = s ^ (q / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
  ring_nf

theorem enorm_Nv_rpow (R : ℝ) (b : ℝ × (ℝ × ℝ) → Merid) (τ : ℝ) {y : Space} (hy : y ∉ axis)
    {q : ℝ} (hq : 0 ≤ q) :
    ‖Nv R b τ y‖ₑ ^ q = ENNReal.ofReal (age R y ^ (q / 2)) * ‖b (chart R τ y)‖ₑ ^ q := by
  rw [← ofReal_norm, norm_Nv R b τ hy, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hq,
    sqrt_rpow (age_nonneg R y), ofReal_norm]

/-- `s^{-5/2} s^{a} = s^{a − 5/2}` for `s > 0`, with the cell normalization `c⁻¹`. -/
theorem ofReal_density_mul {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (a : ℝ) (B : ℝ≥0∞) :
    ENNReal.ofReal (c⁻¹ * s ^ (-(5 / 2 : ℝ))) * (ENNReal.ofReal (s ^ a) * B) =
      ENNReal.ofReal (c⁻¹ * s ^ (a - 5 / 2)) * B := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [show a - 5 / 2 = a + (-(5 / 2 : ℝ)) by ring, Real.rpow_add hs]
  ring

/-- **AX04 `lintegral_Nv_rpow`** (B0219, tex 3260; B0228, tex 3700–3704; B0283, tex 5233;
B0550, tex 8730). For a measurable profile `b`, `c`-periodic in `ξ`, `P = 2c/R` and `q > 0`,
`P⁻¹ ∫_{(0,P]} ∫_{ℝ³} |N_v b|^q dy dτ = πR² ∫ |b|^q dageμ c (q/2 − 5/2)`. -/
theorem lintegral_Nv_rpow {R c P q : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (hq : 0 < q) {b : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b)
    (hper : ∀ s ξ η, b (s, (ξ + c, η)) = b (s, (ξ, η))) :
    (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Nv R b τ y‖ₑ ^ q =
      ENNReal.ofReal (π * R ^ 2) * ∫⁻ p, ‖b p‖ₑ ^ q ∂ageμ c (q / 2 - 5 / 2) := by
  set G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (q / 2)) * ‖b p‖ₑ ^ q with hG
  have hGm : Measurable G :=
    ((measurable_ofReal_rpow _).comp measurable_fst).mul (hb.enorm.pow_const q)
  have hGper : ∀ s ξ η, G (s, (ξ + c, η)) = G (s, (ξ, η)) := fun s ξ η => by
    simp only [hG, hper]
  have hin : ∀ τ : ℝ, ∫⁻ y, ‖Nv R b τ y‖ₑ ^ q = ∫⁻ y, G (age R y, (phase R τ y, trans R y)) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_not_mem_axis] with y hy
    rw [enorm_Nv_rpow R b τ hy hq.le]
    rfl
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun τ _ => hin τ),
    phaseAvg_ringChart hR hc hP G hGm hGper,
    lintegral_ageμ hc _ (hb.enorm.pow_const q)]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ))
    fun p hp => ?_
  exact ofReal_density_mul hc hp.1 _ _

/-! ### `M_s : g ↦ s g` -/

/-- **AX04 `Ms_isometry`, lintegral form** (B0219, tex 3262–3264; B0283, tex 5235; B0783,
tex 11116–11120). `∫ |s g|^q dageμ c (q/2 − 5/2) = ∫ |g|^q dageμ c (3q/2 − 5/2)`. -/
theorem lintegral_Ms {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {g : ℝ × (ℝ × ℝ) → E} (hg : Measurable g) :
    ∫⁻ p, ‖p.1 • g p‖ₑ ^ q ∂ageμ c (q / 2 - 5 / 2) =
      ∫⁻ p, ‖g p‖ₑ ^ q ∂ageμ c (3 * q / 2 - 5 / 2) := by
  have hsm : Measurable fun p : ℝ × (ℝ × ℝ) => p.1 • g p := measurable_fst.smul hg
  rw [lintegral_ageμ hc _ (hsm.enorm.pow_const q), lintegral_ageμ hc _ (hg.enorm.pow_const q)]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ))
    fun p hp => ?_
  have hs : 0 < p.1 := hp.1
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg hs.le, ENNReal.ofReal_mul hs.le,
    ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.ofReal_rpow_of_nonneg hs.le hq, ofReal_norm,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [mul_assoc, ← Real.rpow_add hs]
  congr 2
  ring

/-- **AX04 `Ms_isometry`** (B0219, tex 3262–3264). For `1 ≤ q < ∞` real,
`‖s g‖_{L^q(ageμ c (q/2 − 5/2))} = ‖g‖_{L^q(ageμ c (3q/2 − 5/2))}`. -/
theorem eLpNorm_Ms {c q : ℝ} (hc : 0 < c) (hq : 0 < q) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {g : ℝ × (ℝ × ℝ) → E} (hg : Measurable g) :
    eLpNorm (fun p => p.1 • g p) (ENNReal.ofReal q) (ageμ c (q / 2 - 5 / 2)) =
      eLpNorm g (ENNReal.ofReal q) (ageμ c (3 * q / 2 - 5 / 2)) := by
  have h0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, lintegral_Ms hc hq.le hg]

/-! ### The tensor lift `N_T` -/

/-- The frame lift of a frame-component tensor `M` (order `(r, φ, z)`) at `y`:
`(∑_{ab} M_{ab} e_a e_bᵀ)_{ij}` (`liftTensor` of `Axisymmetric/Tensor.lean` at a constant). -/
def frameTensor (M : Matrix (Fin 3) (Fin 3) ℝ) (y : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ a : Fin 3, ∑ b : Fin 3, M a b * frame y a i * frame y b j

/-- **AX04 `NT`.** The tensor lift `N_T T(τ, y) = s T` in the frame, at the chart point
(tex 7276, 7944). -/
def NT (R : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => age R y * frameTensor (T (chart R τ y)) y i j

theorem frobenius_frameTensor {M : Matrix (Fin 3) (Fin 3) ℝ} {y : Space} (hy : y ∉ axis)
    (hM : IsMeridTensor M) :
    ∑ i : Fin 3, ∑ j : Fin 3, frameTensor M y i j ^ 2 = ∑ a : Fin 3, ∑ b : Fin 3, M a b ^ 2 :=
  frobenius_liftTensor (fun _ => M) hy hM

theorem frobenius_NT (R : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) {y : Space}
    (hy : y ∉ axis) (hT : IsMeridTensor (T (chart R τ y))) :
    ∑ i : Fin 3, ∑ j : Fin 3, NT R T τ y i j ^ 2 =
      age R y ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, T (chart R τ y) a b ^ 2 := by
  rw [← frobenius_frameTensor hy hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [NT]
  ring

theorem measurable_frame_apply (a i : Fin 3) : Measurable fun y : Space => frame y a i := by
  have hρ : Measurable fun y : Space => (ϱ y)⁻¹ := measurable_ϱ.inv
  fin_cases a <;> fin_cases i <;>
    simp [frame, eR_apply_zero, eR_apply_one, eΦ_apply_zero, eΦ_apply_one, div_eq_mul_inv] <;>
    exact (measurable_coord _).mul hρ

/-- **AX04 `lintegral_NT_sq`** (B0417, tex 7272–7297; B0482, tex 7920–7949; B0550, tex 8730).
For a tensor profile with no entry with exactly one azimuthal index, `c`-periodic in `ξ`,
`P⁻¹ ∫_{(0,P]} ∫_{ℝ³} |N_T T|²_F dy dτ = πR² ∫ |T|²_F dageμ c (−1/2)` (Frobenius norms). -/
theorem lintegral_NT_sq {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (hT : ∀ a b, Measurable fun p => T p a b)
    (hTm : ∀ p, IsMeridTensor (T p))
    (hper : ∀ s ξ η, T (s, (ξ + c, η)) = T (s, (ξ, η))) :
    (ENNReal.ofReal P)⁻¹ *
        ∫⁻ τ in Ioc 0 P, ∫⁻ y, ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, NT R T τ y i j ^ 2) =
      ENNReal.ofReal (π * R ^ 2) *
        ∫⁻ p, ENNReal.ofReal (∑ a : Fin 3, ∑ b : Fin 3, T p a b ^ 2) ∂ageμ c (-1 / 2) := by
  have hFm : Measurable fun p => ∑ a : Fin 3, ∑ b : Fin 3, T p a b ^ 2 := by
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    exact (hT a b).pow_const 2
  have hFm' : Measurable fun p => ENNReal.ofReal (∑ a : Fin 3, ∑ b : Fin 3, T p a b ^ 2) :=
    ENNReal.measurable_ofReal.comp hFm
  set G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (2 : ℝ)) *
    ENNReal.ofReal (∑ a : Fin 3, ∑ b : Fin 3, T p a b ^ 2) with hG
  have hGm : Measurable G := ((measurable_ofReal_rpow _).comp measurable_fst).mul hFm'
  have hGper : ∀ s ξ η, G (s, (ξ + c, η)) = G (s, (ξ, η)) := fun s ξ η => by
    simp only [hG, hper]
  have hin : ∀ τ : ℝ, ∫⁻ y, ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, NT R T τ y i j ^ 2) =
      ∫⁻ y, G (age R y, (phase R τ y, trans R y)) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_not_mem_axis] with y hy
    rw [frobenius_NT R T τ hy (hTm _), ENNReal.ofReal_mul (by positivity), hG]
    simp only [Real.rpow_two]
    rfl
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun τ _ => hin τ),
    phaseAvg_ringChart hR hc hP G hGm hGper, lintegral_ageμ hc _ hFm']
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ))
    fun p hp => ?_
  rw [hG, ofReal_density_mul hc hp.1]
  norm_num

end UnforcedLeray.Axi
