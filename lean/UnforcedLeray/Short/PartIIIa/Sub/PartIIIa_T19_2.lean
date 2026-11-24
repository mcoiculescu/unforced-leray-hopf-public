import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19
import UnforcedLeray.Short.PartIIIa.Clock.Existence
import UnforcedLeray.Short.PartIIIa.T20_7_BiotSavartExistsUniform
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.AgeSlice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.NormSq

/-!
# Part III-a, task `PartIII-a:T19/2`: core Duhamel propagation and Biot-Savart velocity

Source of record: `the November 2 reference manuscript` (SP), lines 3456-3515
(Steps P2-duality, P3-Duhamel, P4: core Duhamel vorticity propagation and Biot-Savart velocity
reconstruction on `(0, H)` with `H = coreEnd ν b`).

## What is proved unconditionally in this file

* `lintegral_Iio_ageμ_eq`: exact Tonelli slice representation of `∫⁻` on `Iio H ×ˢ univ` with
  respect to `ageμ c a` as an integral over `s ∈ Ioo 0 H` of the `c⁻¹ s^a`-weighted cell `∫⁻`.
* `s_rpow_neg_half_le`: on `s ∈ Ioo (0 : ℝ) H`, `s ^ (-1 / 2 : ℝ) ≤ H * s ^ (-3 / 2 : ℝ)`.
* `vnorm2_eq`, `vnorm2_add_le`, `vnorm2_nonneg`: Euclidean model and triangle inequality for
  `vnorm2`.
* `hCalNormOn_add_le`, `tCalNormOn_add_le`: triangle inequalities for `hCalNormOn` and `tCalNormOn`
  on `(0, H)`.
* `hCalNormOn_le_of_slice_bound`, `sqrt_nu_tCalNormOn_le_of_slice_bound`: slice-to-space-time
  `L²` bounds converting a `c⁻¹`-normalized cell `H¹` bound `≤ K * W s` into bounds on
  `hCalNormOn c H u₁` and `√ν * tCalNormOn c H G₁` in terms of `(∫_0^H s^{-3/2} W(s)² ds)^{1/2}`.
* `core_perturbation_energy_bound`: assembles the full core energy bound (clause 3 of
  `CoreDuhamelBiotSavart`, SP 3497-3509) for `b_core = b₀ + g u₁`, `G_core = G₀ + g G₁`.
* `unnormSliceVel`, `unnormSliceGrad`, `coreSourceProfile`, `coreVortProfile`: normalized source
  and vorticity norm profiles `N` and `W` on `(0, H)`, with unconditional proofs of `Measurable N`
  (`measurable_coreSourceProfile`), the `L²(t^{-1/2} dt)` source bound (`coreSourceProfile_l2_bound`,
  clause 1 of `CoreDuhamelBiotSavart`), the Duhamel clock rescaling (`coreVortProfile_le_of_unnorm`,
  clause 2 of `CoreDuhamelBiotSavart`), and the Biot-Savart slice rescaling
  (`slice_bound_of_unnorm_BS`).
* `coreDuhamelBiotSavart_of`: assembles `CoreDuhamelBiotSavart` from the three leaves
  `CoreCurlDuality` (`PartIII-a:T19/2/1`), `CoreBiotSavartH1Uniform` (`PartIII-a:T19/2/2`), and
  `CoreDuhamelPropagation` (`PartIII-a:T19/2/3`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## 1. Slice representation of `ageμ` on `(0, H)` and age-weight comparison -/

/-- Exact Tonelli slice representation of `∫⁻` on `Iio H ×ˢ univ` with respect to `ageμ c a`. -/
theorem lintegral_Iio_ageμ_eq {c a H : ℝ} (hc : 0 < c) (g : ℝ × (ℝ × ℝ) → ℝ)
    (hg : Measurable g) :
    ∫⁻ p in Iio H ×ˢ (univ : Set (ℝ × ℝ)), ENNReal.ofReal (g p) ∂(ageμ c a) =
      ∫⁻ s in Ioo (0 : ℝ) H,
        ENNReal.ofReal (s ^ a) *
          (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (g (s, x))) := by
  have hF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p) := hg.ennreal_ofReal
  have hS : MeasurableSet (Iio H ×ˢ (univ : Set (ℝ × ℝ))) := measurableSet_Iio.prod MeasurableSet.univ
  rw [← lintegral_indicator hS (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p))]
  have hW : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ a) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const a).const_mul c⁻¹)
  rw [lintegral_ageμ hc a (hF.indicator hS)]
  rw [lintegral_restrict_prod_eq (Ioi 0) (qCell c)
    (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (c⁻¹ * p.1 ^ a) *
      (Iio H ×ˢ (univ : Set (ℝ × ℝ))).indicator (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) p)
    (hW.mul (hF.indicator hS))]
  have hstep : ∀ s : ℝ, ∫⁻ x in qCell c,
      ENNReal.ofReal (c⁻¹ * s ^ a) *
        (Iio H ×ˢ (univ : Set (ℝ × ℝ))).indicator (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) (s, x) =
      (Iio H).indicator (fun s : ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) *
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (g (s, x))) s := by
    intro s
    by_cases hs : s ∈ Iio H
    · have hpt : ∀ x : ℝ × ℝ, (Iio H ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) (s, x) = ENNReal.ofReal (g (s, x)) := by
        intro x
        rw [indicator_of_mem (mk_mem_prod hs (mem_univ x))]
      simp only [hpt]
      rw [Set.indicator_of_mem hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        qCell_eq_B0579_cell]
    · have hpt : ∀ x : ℝ × ℝ, (Iio H ×ˢ (univ : Set (ℝ × ℝ))).indicator
          (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (g p)) (s, x) = 0 := by
        intro x
        rw [indicator_of_notMem (fun h => hs h.1)]
      simp only [hpt, mul_zero, lintegral_zero, Set.indicator_of_notMem hs]
  refine (lintegral_congr fun s => hstep s).trans ?_
  have hIoo : Iio H ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) H := inter_comm (Iio H) (Ioi 0)
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hIoo]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), mul_comm (ENNReal.ofReal c⁻¹), mul_assoc]

/-- On `s ∈ Ioo (0 : ℝ) H`, `s ^ (-1 / 2 : ℝ) ≤ H * s ^ (-3 / 2 : ℝ)` (SP 3506-3509). -/
theorem s_rpow_neg_half_le {s H : ℝ} (hs : s ∈ Ioo (0 : ℝ) H) :
    s ^ (-1 / 2 : ℝ) ≤ H * s ^ (-3 / 2 : ℝ) := by
  have hs0 : 0 < s := hs.1
  have hsH : s ≤ H := hs.2.le
  have hpos : 0 < s ^ (-3 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
  calc s ^ (-1 / 2 : ℝ)
      = s ^ (1 : ℝ) * s ^ (-3 / 2 : ℝ) := by
        rw [← Real.rpow_add hs0]
        norm_num
    _ = s * s ^ (-3 / 2 : ℝ) := by rw [Real.rpow_one]
    _ ≤ H * s ^ (-3 / 2 : ℝ) := mul_le_mul_of_nonneg_right hsH hpos.le

/-! ## 2. Triangle inequalities for `hCalNormOn` and `tCalNormOn` -/

/-- A `2`-vector of complex numbers as a vector in `EuclideanSpace ℂ (Fin 2)`. -/
def toV (a : Fin 2 → ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 a

theorem vnorm2_eq (a : Fin 2 → ℂ) : vnorm2 a = ‖toV a‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [vnorm2, toV]

theorem vnorm2_add_le (a b : Fin 2 → ℂ) :
    vnorm2 (fun i => a i + b i) ≤ vnorm2 a + vnorm2 b := by
  rw [vnorm2_eq, vnorm2_eq, vnorm2_eq]
  have : toV (fun i => a i + b i) = toV a + toV b := by ext i; simp [toV]
  rw [this]
  exact norm_add_le _ _

theorem vnorm2_nonneg (a : Fin 2 → ℂ) : 0 ≤ vnorm2 a := Real.sqrt_nonneg _

/-- Triangle inequality for `hCalNormOn`. -/
theorem hCalNormOn_add_le (c H : ℝ) {u₀ u₁ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hu₀ : ∀ i, Measurable fun p => u₀ p i) (hu₁ : ∀ i, Measurable fun p => u₁ p i) :
    hCalNormOn c H (fun p i => u₀ p i + u₁ p i) ≤ hCalNormOn c H u₀ + hCalNormOn c H u₁ := by
  unfold hCalNormOn
  refine eLpNorm_two_le_add
    (causalLin_measurable_vnorm2 hu₀).aestronglyMeasurable
    (causalLin_measurable_vnorm2 hu₁).aestronglyMeasurable
    (fun p => vnorm2_nonneg _) (fun p => vnorm2_nonneg _) fun p => ?_
  rw [Real.norm_of_nonneg (vnorm2_nonneg _)]
  exact vnorm2_add_le (u₀ p) (u₁ p)

/-- Triangle inequality for `tCalNormOn`. -/
theorem tCalNormOn_add_le (c H : ℝ) {G₀ G₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG₀ : ∀ i j, Measurable fun p => G₀ p i j) (hG₁ : ∀ i j, Measurable fun p => G₁ p i j) :
    tCalNormOn c H (fun p i j => G₀ p i j + G₁ p i j) ≤ tCalNormOn c H G₀ + tCalNormOn c H G₁ := by
  unfold tCalNormOn
  refine eLpNorm_two_le_add
    (causalLin_measurable_tnorm2 hG₀).aestronglyMeasurable
    (causalLin_measurable_tnorm2 hG₁).aestronglyMeasurable
    (fun p => tnorm2_nonneg _) (fun p => tnorm2_nonneg _) fun p => ?_
  rw [Real.norm_of_nonneg (tnorm2_nonneg _)]
  exact tnorm2_add_le (G₀ p) (G₁ p)

/-! ## 3. Slice-to-space-time `L²` bounds on `(0, H)` (SP 3497-3509) -/

/-- Bound on `hCalNormOn c H u₁` from a slice `L²(cell c)` bound `≤ K * W s` on `s ∈ Ioo 0 H`. -/
theorem hCalNormOn_le_of_slice_bound {c H K : ℝ} (hc : 0 < c) (_hK : 0 ≤ K)
    {u₁ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu₁ : ∀ i, Measurable fun p => u₁ p i)
    {W : ℝ → ℝ≥0∞}
    (hslice : ∀ s ∈ Ioo (0 : ℝ) H,
      ENNReal.ofReal c⁻¹ * (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₁ (s, x)) ^ 2)) ≤
        (ENNReal.ofReal K * W s) ^ (2 : ℝ)) :
    hCalNormOn c H u₁ ≤
      ENNReal.ofReal K *
        (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
  apply le_of_sq_le_sq
  unfold hCalNormOn
  rw [eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => vnorm2 (u₁ p)) (fun _ => vnorm2_nonneg _)]
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (u₁ p) ^ 2 :=
    (causalLin_measurable_vnorm2 hu₁).pow_const 2
  rw [lintegral_Iio_ageμ_eq hc _ hm]
  have hRHS_sq :
      (ENNReal.ofReal K *
          (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) ^ 2 =
        ENNReal.ofReal K ^ (2 : ℝ) *
          ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ) := by
    rw [mul_pow, ← ENNReal.rpow_natCast (ENNReal.ofReal K),
      ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    norm_num
  rw [hRHS_sq, ← lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hs_bd := hslice s hs
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hs_bd
  calc ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₁ (s, x)) ^ 2))
      ≤ ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * (ENNReal.ofReal K ^ (2 : ℝ) * W s ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hs_bd bot_le
    _ = ENNReal.ofReal K ^ (2 : ℝ) * (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) := by
        ring

/-- Bound on `√ν * tCalNormOn c H G₁` from a slice `L²(cell c)` bound `≤ K * W s` on `s ∈ Ioo 0 H`,
using `s ^ (-1 / 2 : ℝ) ≤ H * s ^ (-3 / 2 : ℝ)`. -/
theorem sqrt_nu_tCalNormOn_le_of_slice_bound {c ν H K : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hH : 0 < H) (hK : 0 ≤ K)
    {G₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hG₁ : ∀ i j, Measurable fun p => G₁ p i j)
    {W : ℝ → ℝ≥0∞}
    (hslice : ∀ s ∈ Ioo (0 : ℝ) H,
      ENNReal.ofReal c⁻¹ * (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₁ (s, x)) ^ 2)) ≤
        (ENNReal.ofReal K * W s) ^ (2 : ℝ)) :
    ENNReal.ofReal (Real.sqrt ν) * tCalNormOn c H G₁ ≤
      ENNReal.ofReal (K * Real.sqrt (ν * H)) *
        (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
  apply le_of_sq_le_sq
  unfold tCalNormOn
  rw [mul_pow, eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => tnorm2 (G₁ p))
    (fun _ => tnorm2_nonneg _)]
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G₁ p) ^ 2 :=
    (causalLin_measurable_tnorm2 hG₁).pow_const 2
  rw [lintegral_Iio_ageμ_eq hc _ hm,
    ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hRHS_sq :
      (ENNReal.ofReal (K * Real.sqrt (ν * H)) *
          (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) ^ 2 =
        ENNReal.ofReal (K * Real.sqrt (ν * H)) ^ 2 *
          ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ) := by
    rw [mul_pow, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  rw [hRHS_sq, ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hs_bd := hslice s hs
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two] at hs_bd
  have hν_sq : ENNReal.ofReal (Real.sqrt ν) ^ 2 = ENNReal.ofReal ν := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hν.le]
  have hKνH_sq : ENNReal.ofReal (K * Real.sqrt (ν * H)) ^ 2 =
      ENNReal.ofReal ν * ENNReal.ofReal H * ENNReal.ofReal K ^ 2 := by
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt (by positivity),
      ENNReal.ofReal_mul (sq_nonneg K), ENNReal.ofReal_pow hK, ENNReal.ofReal_mul hν.le]
    ring
  have hs_wt : ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ≤
      ENNReal.ofReal H * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul hH.le]
    exact ENNReal.ofReal_le_ofReal (s_rpow_neg_half_le hs)
  calc ENNReal.ofReal (Real.sqrt ν) ^ 2 *
          (ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₁ (s, x)) ^ 2)))
      ≤ ENNReal.ofReal ν *
          ((ENNReal.ofReal H * ENNReal.ofReal (s ^ (-3 / 2 : ℝ))) *
            (ENNReal.ofReal K ^ 2 * W s ^ (2 : ℝ))) := by
        rw [hν_sq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hs_wt hs_bd bot_le bot_le) bot_le
    _ = ENNReal.ofReal (K * Real.sqrt (ν * H)) ^ 2 *
          (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) := by
        rw [hKνH_sq]
        ring

/-- Full core perturbation energy bound (clause 3 of `CoreDuhamelBiotSavart`, SP 3497-3509):
for `b_core = b₀ + g u₁` and `G_core = G₀ + g G₁` with slice `L²(cell c)` norms bounded by
`C_BS * (1 + c) * W s` on `s ∈ Ioo (0 : ℝ) H`. -/
theorem core_perturbation_energy_bound {c γ ν H C_BS : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hH : 0 < H) (hC_BS : 0 ≤ C_BS)
    {b₀ u₁ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ G₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hb₀ : ∀ i, Measurable fun p => b₀ p i) (hu₁ : ∀ i, Measurable fun p => u₁ p i)
    (hG₀ : ∀ i j, Measurable fun p => G₀ p i j) (hG₁ : ∀ i j, Measurable fun p => G₁ p i j)
    {W : ℝ → ℝ≥0∞}
    (hu₁_slice : ∀ s ∈ Ioo (0 : ℝ) H,
      ENNReal.ofReal c⁻¹ * (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₁ (s, x)) ^ 2)) ≤
        (ENNReal.ofReal (C_BS * (1 + c)) * W s) ^ (2 : ℝ))
    (hG₁_slice : ∀ s ∈ Ioo (0 : ℝ) H,
      ENNReal.ofReal c⁻¹ * (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₁ (s, x)) ^ 2)) ≤
        (ENNReal.ofReal (C_BS * (1 + c)) * W s) ^ (2 : ℝ)) :
    hCalNormOn c H (gainConj γ ν (fun p i => b₀ p i + gainG γ ν p.1 • u₁ p i)) +
        ENNReal.ofReal (Real.sqrt ν) *
          tCalNormOn c H (gainConj γ ν (fun p i j => G₀ p i j + gainG γ ν p.1 • G₁ p i j)) ≤
      (hCalNorm c (gainConj γ ν b₀) +
          ENNReal.ofReal (Real.sqrt ν) * tCalNorm c (gainConj γ ν G₀)) +
        ENNReal.ofReal (C_BS * (1 + c) * (1 + Real.sqrt (ν * H))) *
          (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
  have hK : 0 ≤ C_BS * (1 + c) := mul_nonneg hC_BS (by linarith)
  have hconj_b : gainConj γ ν (fun p i => b₀ p i + gainG γ ν p.1 • u₁ p i) =
      fun p i => gainConj γ ν b₀ p i + u₁ p i := by
    funext p i
    unfold gainConj
    simp only [Pi.smul_apply, smul_add]
    have hg_ne : gainG γ ν p.1 ≠ 0 := by
      unfold gainG
      exact (Real.exp_pos _).ne'
    rw [inv_smul_smul₀ hg_ne]
  have hconj_G : gainConj γ ν (fun p i j => G₀ p i j + gainG γ ν p.1 • G₁ p i j) =
      fun p i j => gainConj γ ν G₀ p i j + G₁ p i j := by
    funext p i j
    unfold gainConj
    simp only [Pi.smul_apply, smul_add]
    have hg_ne : gainG γ ν p.1 ≠ 0 := by
      unfold gainG
      exact (Real.exp_pos _).ne'
    rw [inv_smul_smul₀ hg_ne]
  have hmb₀ : ∀ i, Measurable fun p => gainConj γ ν b₀ p i :=
    fun i => measurable_gainConj_vec hb₀ i
  have hmG₀ : ∀ i j, Measurable fun p => gainConj γ ν G₀ p i j :=
    fun i j => measurable_gainConj hG₀ i j
  rw [hconj_b, hconj_G]
  set IW := (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^
    (1 / 2 : ℝ)
  have h1 : hCalNormOn c H (fun p i => gainConj γ ν b₀ p i + u₁ p i) ≤
      hCalNorm c (gainConj γ ν b₀) + ENNReal.ofReal (C_BS * (1 + c)) * IW :=
    (hCalNormOn_add_le c H hmb₀ hu₁).trans
      (add_le_add (hCalNormOn_le_hCalNorm c H _)
        (hCalNormOn_le_of_slice_bound hc hK hu₁ hu₁_slice))
  have h2 : ENNReal.ofReal (Real.sqrt ν) *
      tCalNormOn c H (fun p i j => gainConj γ ν G₀ p i j + G₁ p i j) ≤
      ENNReal.ofReal (Real.sqrt ν) * tCalNorm c (gainConj γ ν G₀) +
        ENNReal.ofReal (C_BS * (1 + c) * Real.sqrt (ν * H)) * IW := by
    calc ENNReal.ofReal (Real.sqrt ν) *
            tCalNormOn c H (fun p i j => gainConj γ ν G₀ p i j + G₁ p i j)
        ≤ ENNReal.ofReal (Real.sqrt ν) *
            (tCalNormOn c H (gainConj γ ν G₀) + tCalNormOn c H G₁) :=
          mul_le_mul_of_nonneg_left (tCalNormOn_add_le c H hmG₀ hG₁) bot_le
      _ = ENNReal.ofReal (Real.sqrt ν) * tCalNormOn c H (gainConj γ ν G₀) +
            ENNReal.ofReal (Real.sqrt ν) * tCalNormOn c H G₁ := mul_add _ _ _
      _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (tCalNormOn_le_tCalNorm c H _) bot_le)
          (sqrt_nu_tCalNormOn_le_of_slice_bound hc hν hH hK hG₁ hG₁_slice)
  calc hCalNormOn c H (fun p i => gainConj γ ν b₀ p i + u₁ p i) +
          ENNReal.ofReal (Real.sqrt ν) *
            tCalNormOn c H (fun p i j => gainConj γ ν G₀ p i j + G₁ p i j)
      ≤ (hCalNorm c (gainConj γ ν b₀) + ENNReal.ofReal (C_BS * (1 + c)) * IW) +
          (ENNReal.ofReal (Real.sqrt ν) * tCalNorm c (gainConj γ ν G₀) +
            ENNReal.ofReal (C_BS * (1 + c) * Real.sqrt (ν * H)) * IW) := add_le_add h1 h2
    _ = (hCalNorm c (gainConj γ ν b₀) +
            ENNReal.ofReal (Real.sqrt ν) * tCalNorm c (gainConj γ ν G₀)) +
          (ENNReal.ofReal (C_BS * (1 + c)) +
            ENNReal.ofReal (C_BS * (1 + c) * Real.sqrt (ν * H))) * IW := by ring
    _ = (hCalNorm c (gainConj γ ν b₀) +
            ENNReal.ofReal (Real.sqrt ν) * tCalNorm c (gainConj γ ν G₀)) +
          ENNReal.ofReal (C_BS * (1 + c) * (1 + Real.sqrt (ν * H))) * IW := by
        rw [← ENNReal.ofReal_add hK (by positivity)]
        congr 3
        ring

/-! ## 4. Normalized source and vorticity profiles (`N` and `W`, SP 3456-3496) -/

/-- Unnormalized `L²(cell c)` velocity slice norm `(∫_{cell c} ‖u(t, x)‖² dx)^{1/2}`. -/
def unnormSliceVel (c : ℝ) (u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (t : ℝ) : ℝ≥0∞ :=
  (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u (t, x)) ^ 2)) ^ (1 / 2 : ℝ)

/-- Unnormalized `L²(cell c)` gradient slice norm `(∫_{cell c} ‖G(t, x)‖² dx)^{1/2}`. -/
def unnormSliceGrad (c : ℝ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (t : ℝ) : ℝ≥0∞ :=
  (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G (t, x)) ^ 2)) ^ (1 / 2 : ℝ)

/-- Normalized source profile `N(t)` on `(0, H)` (SP 3456-3480):
`c^{-1/2} * C_dual * A_m * (t^{-1/2} ‖u₀(t)‖_{L²(cell c)} + ‖G̃₀(t)‖_{L²(cell c)})`. -/
def coreSourceProfile (c C_dual A_m : ℝ) (u₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt c⁻¹ * C_dual * A_m) *
    (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t + unnormSliceGrad c G₀ t)

/-- Normalized vorticity profile `W(s) = (1 + c)⁻¹ c^{-1/2} W_raw(s)` on `(0, H)`. -/
def coreVortProfile (c : ℝ) (W_raw : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + c)⁻¹ * Real.sqrt c⁻¹) * W_raw s

theorem measurable_unnormSliceVel (c : ℝ) {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hu : ∀ i, Measurable fun p => u p i) :
    Measurable (unnormSliceVel c u) := by
  unfold unnormSliceVel
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (u p) ^ 2) :=
    ((causalLin_measurable_vnorm2 hu).pow_const 2).ennreal_ofReal
  exact hm.lintegral_prod_right'.pow_const (1 / 2 : ℝ)

theorem measurable_unnormSliceGrad (c : ℝ) {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hG : ∀ i j, Measurable fun p => G p i j) :
    Measurable (unnormSliceGrad c G) := by
  unfold unnormSliceGrad
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (tnorm2 (G p) ^ 2) :=
    ((causalLin_measurable_tnorm2 hG).pow_const 2).ennreal_ofReal
  exact hm.lintegral_prod_right'.pow_const (1 / 2 : ℝ)

theorem measurable_coreSourceProfile (c C_dual A_m : ℝ)
    {u₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hu₀ : ∀ i, Measurable fun p => u₀ p i) (hG₀ : ∀ i j, Measurable fun p => G₀ p i j) :
    Measurable (coreSourceProfile c C_dual A_m u₀ G₀) := by
  unfold coreSourceProfile
  have h1 : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) :=
    (measurable_id.pow_const (-1 / 2 : ℝ)).ennreal_ofReal
  exact ((h1.mul (measurable_unnormSliceVel c hu₀)).add
    (measurable_unnormSliceGrad c hG₀)).const_mul _

private theorem add_sq_le_four_mul_add_sq (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2) := by
  rw [ENNReal.rpow_two]
  rcases le_total a b with hab | hba
  · calc (a + b) ^ 2 ≤ (b + b) ^ 2 := pow_le_pow_left₀ bot_le (add_le_add hab le_rfl) 2
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left le_add_self bot_le
  · calc (a + b) ^ 2 ≤ (a + a) ^ 2 := pow_le_pow_left₀ bot_le (add_le_add le_rfl hba) 2
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left le_self_add bot_le

private theorem add_sq_le_sq_add (X Y : ℝ≥0∞) :
    X ^ 2 + Y ^ 2 ≤ (X + Y) ^ 2 := by
  calc X ^ 2 + Y ^ 2 ≤ (X ^ 2 + Y ^ 2) + 2 * X * Y := le_self_add
    _ = (X + Y) ^ 2 := by ring

/-- Space-time `L²(t^{-1/2} dt)` bound for `coreSourceProfile` on `(0, H)` (clause 1 of
`CoreDuhamelBiotSavart`, SP 3456-3480). -/
theorem coreSourceProfile_l2_bound {c H C_dual A_m : ℝ} (hc : 0 < c)
    (hC_dual : 0 ≤ C_dual) (hAm : 0 ≤ A_m)
    {u₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hu₀ : ∀ i, Measurable fun p => u₀ p i) (hG₀ : ∀ i j, Measurable fun p => G₀ p i j) :
    (∫⁻ t in Ioo (0 : ℝ) H,
        ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
          coreSourceProfile c C_dual A_m u₀ G₀ t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * C_dual * A_m) *
        (hCalNorm c u₀ + tCalNorm c G₀) := by
  apply le_of_sq_le_sq
  rw [← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  have hmu : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (u₀ p) ^ 2 :=
    (causalLin_measurable_vnorm2 hu₀).pow_const 2
  have hmG : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G₀ p) ^ 2 :=
    (causalLin_measurable_tnorm2 hG₀).pow_const 2
  have hu_eq : ∫⁻ t in Ioo (0 : ℝ) H,
      ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2)) =
      hCalNormOn c H u₀ ^ 2 := by
    rw [← lintegral_Iio_ageμ_eq hc _ hmu]
    unfold hCalNormOn
    exact (eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => vnorm2 (u₀ p))
      (fun _ => vnorm2_nonneg _)).symm
  have hG_eq : ∫⁻ t in Ioo (0 : ℝ) H,
      ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2)) =
      tCalNormOn c H G₀ ^ 2 := by
    rw [← lintegral_Iio_ageμ_eq hc _ hmG]
    unfold tCalNormOn
    exact (eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => tnorm2 (G₀ p))
      (fun _ => tnorm2_nonneg _)).symm
  have hpt : ∀ t ∈ Ioo (0 : ℝ) H,
      ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * coreSourceProfile c C_dual A_m u₀ G₀ t ^ (2 : ℝ) ≤
        ENNReal.ofReal ((2 * C_dual * A_m) ^ 2) *
          (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
              (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2)) +
            ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2))) := by
    intro t ht
    unfold coreSourceProfile
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have h4 := add_sq_le_four_mul_add_sq
      (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t) (unnormSliceGrad c G₀ t)
    have hK_sq : ENNReal.ofReal (Real.sqrt c⁻¹ * C_dual * A_m) ^ (2 : ℝ) * 4 =
        ENNReal.ofReal ((2 * C_dual * A_m) ^ 2) * ENNReal.ofReal c⁻¹ := by
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity),
        show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : Real.sqrt c⁻¹ ^ 2 = c⁻¹ := Real.sq_sqrt (inv_nonneg.2 hc.le)
      calc (Real.sqrt c⁻¹ * C_dual * A_m) ^ 2 * 4
          = Real.sqrt c⁻¹ ^ 2 * (2 * C_dual * A_m) ^ 2 := by ring
        _ = (2 * C_dual * A_m) ^ 2 * c⁻¹ := by rw [this]; ring
    have hA_sq : (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t) ^ 2 =
        ENNReal.ofReal (t ^ (-1 : ℝ)) *
          ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2) := by
      unfold unnormSliceVel
      rw [mul_pow, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one,
        ← ENNReal.ofReal_pow (Real.rpow_nonneg ht.1.le _), ← Real.rpow_natCast,
        ← Real.rpow_mul ht.1.le]
      norm_num
    have hB_sq : unnormSliceGrad c G₀ t ^ 2 =
        ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2) := by
      unfold unnormSliceGrad
      rw [← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    have ht_mul : ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (t ^ (-1 : ℝ)) =
        ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _), ← Real.rpow_add ht.1]
      norm_num
    calc ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal (Real.sqrt c⁻¹ * C_dual * A_m) ^ (2 : ℝ) *
              (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t +
                unnormSliceGrad c G₀ t) ^ (2 : ℝ))
        ≤ ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal (Real.sqrt c⁻¹ * C_dual * A_m) ^ (2 : ℝ) *
              (4 * ((ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t) ^ 2 +
                unnormSliceGrad c G₀ t ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 bot_le) bot_le
      _ = ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
            ((ENNReal.ofReal (Real.sqrt c⁻¹ * C_dual * A_m) ^ (2 : ℝ) * 4) *
              (ENNReal.ofReal (t ^ (-1 : ℝ)) *
                  (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2)) +
                ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2))) := by
          rw [hA_sq, hB_sq, mul_assoc (ENNReal.ofReal _ ^ (2 : ℝ)) 4]
      _ = ENNReal.ofReal ((2 * C_dual * A_m) ^ 2) *
            ((ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (t ^ (-1 : ℝ))) *
                (ENNReal.ofReal c⁻¹ *
                  ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2)) +
              ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal c⁻¹ *
                  ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2))) := by
          rw [hK_sq]
          ring
      _ = _ := by rw [ht_mul]
  have hm1 : Measurable fun t : ℝ =>
      ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2)) :=
    (measurable_id.pow_const (-3 / 2 : ℝ)).ennreal_ofReal.mul
      ((hmu.ennreal_ofReal.lintegral_prod_right').const_mul _)
  have hm2 : Measurable fun t : ℝ =>
      ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2)) :=
    (measurable_id.pow_const (-1 / 2 : ℝ)).ennreal_ofReal.mul
      ((hmG.ennreal_ofReal.lintegral_prod_right').const_mul _)
  calc ∫⁻ t in Ioo (0 : ℝ) H,
          ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
            coreSourceProfile c C_dual A_m u₀ G₀ t ^ (2 : ℝ)
      ≤ ∫⁻ t in Ioo (0 : ℝ) H,
          ENNReal.ofReal ((2 * C_dual * A_m) ^ 2) *
            (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) *
                (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u₀ (t, x)) ^ 2)) +
              ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G₀ (t, x)) ^ 2))) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal ((2 * C_dual * A_m) ^ 2) *
          (hCalNormOn c H u₀ ^ 2 + tCalNormOn c H G₀ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1, hu_eq, hG_eq]
    _ ≤ ENNReal.ofReal (2 * C_dual * A_m) ^ 2 *
          (hCalNorm c u₀ ^ 2 + tCalNorm c G₀ ^ 2) := by
        rw [ENNReal.ofReal_pow (by positivity)]
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) bot_le
        · exact pow_le_pow_left₀ bot_le (hCalNormOn_le_hCalNorm c H u₀) 2
        · exact pow_le_pow_left₀ bot_le (tCalNormOn_le_tCalNorm c H G₀) 2
    _ ≤ (ENNReal.ofReal (2 * C_dual * A_m) * (hCalNorm c u₀ + tCalNorm c G₀)) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (add_sq_le_sq_add _ _) bot_le

/-- Pointwise absorption of `1 ≤ (1 + c) * t ^ (-1 / 2 : ℝ)` on `t ∈ Ioo (0 : ℝ) H` when `H ≤ c`
and `0 < c`, converting an unnormalized Duhamel bound on `W_raw` into clause 2 of
`CoreDuhamelBiotSavart` for `coreVortProfile c W_raw`. -/
theorem coreVortProfile_le_of_unnorm {c H D C_dual A_m σ : ℝ} (hc : 0 < c) (hHc : H ≤ c)
    (hC_dual : 0 ≤ C_dual) (hAm : 0 ≤ A_m)
    {u₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {W_raw : ℝ → ℝ≥0∞} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) H)
    (hW : W_raw s ≤ ∫⁻ t in Ioo (0 : ℝ) s,
      ENNReal.ofReal (D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
        (ENNReal.ofReal (C_dual * A_m) * (unnormSliceVel c u₀ t + unnormSliceGrad c G₀ t))) :
    coreVortProfile c W_raw s ≤ ∫⁻ t in Ioo (0 : ℝ) s,
      ENNReal.ofReal (D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
        coreSourceProfile c C_dual A_m u₀ G₀ t := by
  unfold coreVortProfile
  refine (mul_le_mul_of_nonneg_left hW bot_le).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have htc : t ≤ c := (ht.2.trans hs.2).le.trans hHc
  have h1c_pos : 0 < 1 + c := by linarith
  have ht_le_sq : t ≤ (1 + c) ^ 2 := by
    nlinarith [sq_nonneg c]
  have hsqrt_t : Real.sqrt t ≤ 1 + c := by
    calc Real.sqrt t ≤ Real.sqrt ((1 + c) ^ 2) := Real.sqrt_le_sqrt ht_le_sq
      _ = 1 + c := Real.sqrt_sq h1c_pos.le
  have hpos_rpow : 0 < t ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have h1_le : 1 ≤ (1 + c) * t ^ (-1 / 2 : ℝ) := by
    calc (1 : ℝ) = t ^ (1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) := by
          rw [← Real.rpow_add ht0]; norm_num
      _ = Real.sqrt t * t ^ (-1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ (1 + c) * t ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hsqrt_t hpos_rpow.le
  have h1_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + c) * ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul h1c_pos.le, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1_le
  have hvel_le : unnormSliceVel c u₀ t ≤
      ENNReal.ofReal (1 + c) * (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t) := by
    calc unnormSliceVel c u₀ t = 1 * unnormSliceVel c u₀ t := (one_mul _).symm
      _ ≤ (ENNReal.ofReal (1 + c) * ENNReal.ofReal (t ^ (-1 / 2 : ℝ))) * unnormSliceVel c u₀ t :=
          mul_le_mul_of_nonneg_right h1_enn bot_le
      _ = _ := mul_assoc _ _ _
  have hgrad_le : unnormSliceGrad c G₀ t ≤
      ENNReal.ofReal (1 + c) * unnormSliceGrad c G₀ t := by
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + c) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc unnormSliceGrad c G₀ t = 1 * unnormSliceGrad c G₀ t := (one_mul _).symm
      _ ≤ ENNReal.ofReal (1 + c) * unnormSliceGrad c G₀ t :=
          mul_le_mul_of_nonneg_right this bot_le
  have hsum_le : unnormSliceVel c u₀ t + unnormSliceGrad c G₀ t ≤
      ENNReal.ofReal (1 + c) *
        (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t + unnormSliceGrad c G₀ t) := by
    rw [mul_add]
    exact add_le_add hvel_le hgrad_le
  have hconst_eq :
      ENNReal.ofReal ((1 + c)⁻¹ * Real.sqrt c⁻¹) * ENNReal.ofReal (C_dual * A_m) *
        ENNReal.ofReal (1 + c) =
      ENNReal.ofReal (Real.sqrt c⁻¹ * C_dual * A_m) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hne : 1 + c ≠ 0 := h1c_pos.ne'
    field_simp
  unfold coreSourceProfile
  calc ENNReal.ofReal ((1 + c)⁻¹ * Real.sqrt c⁻¹) *
          (ENNReal.ofReal (D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
            (ENNReal.ofReal (C_dual * A_m) * (unnormSliceVel c u₀ t + unnormSliceGrad c G₀ t)))
      ≤ ENNReal.ofReal ((1 + c)⁻¹ * Real.sqrt c⁻¹) *
          (ENNReal.ofReal (D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
            (ENNReal.ofReal (C_dual * A_m) *
              (ENNReal.ofReal (1 + c) *
                (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t +
                  unnormSliceGrad c G₀ t)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ bot_le) bot_le
        exact mul_le_mul_of_nonneg_left hsum_le bot_le
    _ = ENNReal.ofReal (D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
          ((ENNReal.ofReal ((1 + c)⁻¹ * Real.sqrt c⁻¹) * ENNReal.ofReal (C_dual * A_m) *
              ENNReal.ofReal (1 + c)) *
            (ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * unnormSliceVel c u₀ t +
              unnormSliceGrad c G₀ t)) := by ring
    _ = _ := by rw [hconst_eq]

/-- Rescaling of an unnormalized `L²(cell c)` Biot-Savart bound `≤ (C_BS * W_raw s)²` to the
`c⁻¹`-normalized bound `≤ (C_BS * (1 + c) * coreVortProfile c W_raw s)²`. -/
theorem slice_bound_of_unnorm_BS {c C_BS : ℝ} (hc : 0 < c) (hC_BS : 0 ≤ C_BS)
    {I_slice : ℝ≥0∞} {W_raw : ℝ → ℝ≥0∞} {s : ℝ}
    (hunnorm : I_slice ≤ (ENNReal.ofReal C_BS * W_raw s) ^ (2 : ℝ)) :
    ENNReal.ofReal c⁻¹ * I_slice ≤
      (ENNReal.ofReal (C_BS * (1 + c)) * coreVortProfile c W_raw s) ^ (2 : ℝ) := by
  have h1c_pos : 0 < 1 + c := by linarith
  have hprod : ENNReal.ofReal (C_BS * (1 + c)) * coreVortProfile c W_raw s =
      ENNReal.ofReal (Real.sqrt c⁻¹) * (ENNReal.ofReal C_BS * W_raw s) := by
    unfold coreVortProfile
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← mul_assoc (ENNReal.ofReal (Real.sqrt c⁻¹)), ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 2
    have hne : 1 + c ≠ 0 := h1c_pos.ne'
    field_simp
  have hsq_c : ENNReal.ofReal (Real.sqrt c⁻¹) ^ (2 : ℝ) = ENNReal.ofReal c⁻¹ := by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (inv_nonneg.2 hc.le)]
  rw [hprod, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq_c]
  exact mul_le_mul_of_nonneg_left hunnorm bot_le

/-! ## 5. The three leaf statements for `PartIII-a:T19/2` (`PartIII-a:T19/2/1..3`) -/

/-- The spatial advection-stretching vector field `(v·∇)u + (u·∇)v` at a fixed age, where `G` is
the spatial gradient of `u`: `(advStretch v u G x)_i = ∑_j (v_j(x) G_{ij}(x) + u_j(x) ∂_j v_i(x))`
(SP 3463). -/
def advStretch (v : ℝ × ℝ → Fin 2 → ℝ) (u : ℝ × ℝ → Fin 2 → ℂ)
    (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) (x : ℝ × ℝ) (i : Fin 2) : ℂ :=
  ∑ j : Fin 2, ((v x j : ℂ) * G x i j + u x j * (B0579.pd j (fun y => v y i) x : ℂ))

/-- **Leaf `PartIII-a:T19/2/1` (`CoreCurlDuality`, SP lines 3456-3480)**:
Weighted `X_{9,c}` and `Z^{-1}_{9,c}` curl duality bound for the advection-stretching source
`f = -curl((v·∇)u + (u·∇)v)` on `B0579.cell c`:
for any smooth vector field `v` satisfying `⟨x⟩^9 (‖v(x)‖ + ‖Dv(x)‖) ≤ A_m` on `B0579.cell c` and
measurable `(u, G)`, `advStretch v u G` satisfies the pointwise bound
`⟨x⟩^9 ‖advStretch v u G x‖ ≤ C_dual A_m (‖u(x)‖ + ‖G(x)‖)`, the weighted `L²(cell c)` bound, and the
`Z^{-1}_{9,c}` negative-norm bound `negNorm c 9 f ≤ C_dual A_m (‖u‖_{L²(cell c)} + ‖G‖_{L²(cell c)})`
for any `f` whose pairing with `(φ, g) ∈ H^1_{-9,c}` is bounded by
`∫_{cell c} ‖advStretch v u G x‖ ‖g(x)‖ dx`. -/
def CoreCurlDuality : Prop :=
  ∃ C_dual : ℝ, 0 ≤ C_dual ∧
    ∀ (c A_m : ℝ), 0 < c → 0 ≤ A_m →
      ∀ (v : ℝ × ℝ → Fin 2 → ℝ), ContDiff ℝ 1 v →
        (∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m) →
        ∀ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
          (∀ i, Measurable fun x => u x i) → (∀ i j, Measurable fun x => G x i j) →
          (∀ x ∈ B0579.cell c,
            B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) ≤
              C_dual * A_m * (vnorm2 (u x) + tnorm2 (G x))) ∧
          (∫⁻ x in B0579.cell c,
              ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) ≤
            ENNReal.ofReal (C_dual * A_m) *
              ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) ∧
          ∀ (f : ℝ × ℝ → ℂ),
            (∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
              (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
              ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖ ≤
                ∫⁻ x in B0579.cell c,
                  ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x))) →
            negNorm c 9 f ≤
              ENNReal.ofReal (C_dual * A_m) *
                ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                  (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ))

/-- **Leaf `PartIII-a:T19/2/2` (`CoreBiotSavartH1Uniform`, SP lines 3497-3505)**:
Complex `H¹(cell c)` Biot-Savart velocity and weak gradient reconstruction on `X_{9,c}` with
zero circulation for `c ≥ 1`, with constant `C_BS` independent of `c`.
Follows from `CTE.realBiotSavartUniform` (`T20_6_RealBiotSavartUniform.lean`),
`CTE.velocityIsBiotSavart` (`T20_4_VelocityIsBiotSavart.lean`), `CTE.velNorm_eq_lp`
(`T20_5_VelNormEqLp.lean`), `B0583.hasWeakVelDeriv_velocity_q`,
`B0583.hasWeakVelDeriv_velocity_eta`, `B0583.norm_velGradQ_le`, `B0583.norm_velGradEta_le`
(`Units/B0583.lean`), and splitting `f = Re f + i Im f` as in `T20_7_BiotSavartExistsUniform.lean`. -/
def CoreBiotSavartH1Uniform : Prop :=
  ∃ C_BS : ℝ, 0 ≤ C_BS ∧
    ∀ (c : ℝ), 1 ≤ c → ∀ (f : ℝ × ℝ → ℂ),
      MemLp f 2 (B0579.cellMeasure c 9) → HasZeroCirculation c f →
      ∃ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
        (∀ i, Measurable fun x => u x i) ∧
        (∀ i j, Measurable fun x => G x i j) ∧
        IsBiotSavart c f u ∧
        (∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j)) ∧
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ≤
          (ENNReal.ofReal C_BS * xNorm c 9 f) ^ (2 : ℝ) ∧
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ≤
          (ENNReal.ofReal C_BS * xNorm c 9 f) ^ (2 : ℝ)

/-- **Leaf `PartIII-a:T19/2/3` (`CoreDuhamelPropagation`, SP lines 3489-3515)**:
Given `CoreCurlDuality` and `CoreBiotSavartH1Uniform`, forward Duhamel vorticity propagation
`ω(s) = ∫_0^s (t/s)^μ (g(t)/g(s)) U(s, t) f(t) dt` (`Exist.fullFlowExistsSmall` and
`ClockBoundAt P 9 b C_clock ν tr`) and Biot-Savart velocity reconstruction `u₁(s) = K_c(ω(s))`,
`G₁(s) = ∇ K_c(ω(s))` on `(0, coreEnd ν b)` produce an unnormalized vorticity norm profile
`W_raw : ℝ → ℝ≥0∞` (`W_raw s = xNorm c 9 (ω s)`) and measurable perturbation `(u₁, G₁)` such that
`b_core = b₀ + g u₁`, `G_core = G₀ + g G₁` solves `IsCoreCausalSolution` on `(0, coreEnd ν b)` and
`(W_raw, u₁, G₁)` satisfy the unnormalized Duhamel and Biot-Savart slice bounds. -/
def CoreDuhamelPropagation : Prop :=
  ∀ (C_dual C_BS : ℝ), 0 ≤ C_dual → 0 ≤ C_BS →
    (∀ (c A_m : ℝ), 0 < c → 0 ≤ A_m →
      ∀ (v : ℝ × ℝ → Fin 2 → ℝ), ContDiff ℝ 1 v →
        (∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m) →
        ∀ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
          (∀ i, Measurable fun x => u x i) → (∀ i j, Measurable fun x => G x i j) →
          (∀ x ∈ B0579.cell c,
            B0579.bracket x ^ (9 : ℝ) * vnorm2 (advStretch v u G x) ≤
              C_dual * A_m * (vnorm2 (u x) + tnorm2 (G x))) ∧
          (∫⁻ x in B0579.cell c,
              ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
            (1 / 2 : ℝ) ≤
            ENNReal.ofReal (C_dual * A_m) *
              ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) ∧
          ∀ (f : ℝ × ℝ → ℂ),
            (∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
              (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
              ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖ ≤
                ∫⁻ x in B0579.cell c,
                  ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x))) →
            negNorm c 9 f ≤
              ENNReal.ofReal (C_dual * A_m) *
                ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
                  (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ))) →
    (∀ (c : ℝ), 1 ≤ c → ∀ (f : ℝ × ℝ → ℂ),
      MemLp f 2 (B0579.cellMeasure c 9) → HasZeroCirculation c f →
      ∃ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
        (∀ i, Measurable fun x => u x i) ∧
        (∀ i j, Measurable fun x => G x i j) ∧
        IsBiotSavart c f u ∧
        (∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => u x i) (fun x => G x i j)) ∧
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ≤
          (ENNReal.ofReal C_BS * xNorm c 9 f) ^ (2 : ℝ) ∧
        (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ≤
          (ENNReal.ofReal C_BS * xNorm c 9 f) ^ (2 : ℝ)) →
    ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
      ∀ b : ℝ, 1 ≤ b → ∃ ν_core : ℝ, 0 < ν_core ∧
        ∀ ν ∈ Ioc 0 ν_core, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
          ∀ A_m C_clock : ℝ, 0 ≤ A_m →
            (∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
              B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m) →
            ClockBoundAt P 9 b C_clock ν tr →
            ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
              (∀ i j, Measurable fun p => F p i j) →
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
              ∀ b₀ G₀, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b₀ G₀ →
                ∃ (W_raw : ℝ → ℝ≥0∞)
                  (u₁ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
                  (G₁ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
                  (∀ i, Measurable fun p => u₁ p i) ∧
                  (∀ i j, Measurable fun p => G₁ p i j) ∧
                  IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν (coreEnd ν b) μ (trainVel tr) F
                    (fun p i => b₀ p i + gainG P.eigenvalue.re ν p.1 • u₁ p i)
                    (fun p i j => G₀ p i j + gainG P.eigenvalue.re ν p.1 • G₁ p i j) ∧
                  (∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
                    W_raw s ≤ ∫⁻ t in Ioo (0 : ℝ) s,
                      ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
                        (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
                        (ENNReal.ofReal (C_dual * A_m) *
                          (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
                            unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t))) ∧
                  (∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
                    (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
                        ENNReal.ofReal (vnorm2 (u₁ (s, x)) ^ 2)) ≤
                      (ENNReal.ofReal C_BS * W_raw s) ^ (2 : ℝ) ∧
                    (∫⁻ x in B0579.cell (ν ^ (-2 : ℝ)),
                        ENNReal.ofReal (tnorm2 (G₁ (s, x)) ^ 2)) ≤
                      (ENNReal.ofReal C_BS * W_raw s) ^ (2 : ℝ))

/-! ## 6. Conditional assembly of `CoreDuhamelBiotSavart` from the three leaves -/

/-- **Conditional assembly of `CoreDuhamelBiotSavart`** (`PartIII-a:T19/2`, SP 3456-3515) from
`CoreCurlDuality`, `CoreBiotSavartH1Uniform`, and `CoreDuhamelPropagation`. -/
theorem coreDuhamelBiotSavart_of (hDual : CoreCurlDuality) (hBS : CoreBiotSavartH1Uniform)
    (hProp : CoreDuhamelPropagation) :
    UnforcedLeray.Short.IIIa.CoreDuhamelBiotSavart := by
  obtain ⟨C_dual, hC_dual, hDual_bd⟩ := hDual
  obtain ⟨C_BS, hC_BS, hBS_bd⟩ := hBS
  intro P hP K hK b hb1
  obtain ⟨ν_core, hν_core, hP_core⟩ :=
    hProp C_dual C_BS hC_dual hC_BS hDual_bd hBS_bd P hP K hK b hb1
  set ν_core' : ℝ := min ν_core (min (1 / 2) ((2 * b)⁻¹))
  have hν_core' : 0 < ν_core' :=
    lt_min hν_core (lt_min (by norm_num) (inv_pos.2 (by linarith)))
  refine ⟨2 * C_dual, C_BS, ν_core', by positivity, hC_BS, hν_core',
    fun ν hν tr htr μ hμ A_m C_clock hAm0 hAm hClk F hsym hmeas hfin b₀ G₀ hsol₀ => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_c : ν ≤ ν_core := hν.2.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_2b : ν ≤ (2 * b)⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hH1, hHc, -, -⟩ := coreEnd_bounds hb1 hν0 hν_half hν_2b
  have hH0 : 0 < coreEnd ν b := by linarith
  have hc0 : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  obtain ⟨W_raw, u₁, G₁, hu₁, hG₁, hCoreSol, hW_raw, hBS_raw⟩ :=
    hP_core ν ⟨hν0, hν_c⟩ tr htr μ hμ A_m C_clock hAm0 hAm hClk F hsym hmeas hfin b₀ G₀ hsol₀
  set u₀ := gainConj P.eigenvalue.re ν b₀
  set G₀_conj := gainConj P.eigenvalue.re ν G₀
  have hmu₀ : ∀ i, Measurable fun p => u₀ p i :=
    fun i => measurable_gainConj_vec hsol₀.measurable i
  have hmG₀ : ∀ i j, Measurable fun p => G₀_conj p i j :=
    fun i j => measurable_gainConj hsol₀.gradMeasurable i j
  refine ⟨coreSourceProfile (ν ^ (-2 : ℝ)) C_dual A_m u₀ G₀_conj,
    coreVortProfile (ν ^ (-2 : ℝ)) W_raw,
    fun p i => b₀ p i + gainG P.eigenvalue.re ν p.1 • u₁ p i,
    fun p i j => G₀ p i j + gainG P.eigenvalue.re ν p.1 • G₁ p i j,
    measurable_coreSourceProfile _ _ _ hmu₀ hmG₀,
    hCoreSol,
    coreSourceProfile_l2_bound hc0 hC_dual hAm0 hmu₀ hmG₀,
    fun s hs => coreVortProfile_le_of_unnorm hc0 hHc hC_dual hAm0 hs (hW_raw s hs),
    ?_⟩
  exact core_perturbation_energy_bound hc0 hν0 hH0 hC_BS hsol₀.measurable hu₁
    hsol₀.gradMeasurable hG₁
    (fun s hs => slice_bound_of_unnorm_BS hc0 hC_BS (hBS_raw s hs).1)
    (fun s hs => slice_bound_of_unnorm_BS hc0 hC_BS (hBS_raw s hs).2)

end UnforcedLeray.Short.IIIa
