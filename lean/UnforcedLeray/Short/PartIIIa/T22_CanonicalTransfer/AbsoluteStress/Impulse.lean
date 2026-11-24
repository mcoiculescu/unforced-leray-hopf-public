import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Part III-a, `PartIII-a:T22/6/1`: Absolute stress impulse bound (`eq:ct-absolute-impulse`)

Source of record: `the November 2 reference manuscript` (SP), lines 3275-3289.

Establishes `UnforcedLeray.Short.IIIa.T22Sub.CTAbsoluteImpulse` via `ctAbsoluteImpulse` for
`k ≤ 1`:
1. Pointwise Frobenius bound `|v ⊗ u_μ + u_μ ⊗ v| ≤ 2 s^{-Re μ} |v| |u|` and spatial Cauchy-Schwarz
   on `B0579.cell (ν⁻²)` yield `sAbs tr μ (u s) s ≤ 2 ν² s^{-Re μ} ‖v(s)‖₂ ‖u(s)‖₂`.
2. Biot-Savart rescaling between `dOfTheta ν θ` (`θ = clockTheta ν s`) and `c = ν⁻²`, combined with
   `CTE.isBiotSavart_unique` and `ctKineticImpulse`, yields
   `velNorm c (u s) ≤ C_kin ν r * kinNorm (dOfTheta ν r) h` for all `s ≥ clockAge ν r`.
3. `T22Sub.trainL2Decay_unconditional` at `ρ = 2` (`c = trainPeriod 2 ν = ν⁻²`) bounds `‖v(s)‖₂`
   before and after `s_c = B0146.overlapAge ν c`, and integrating over `s > clockAge ν r` yields
   the stated bound in both regimes `r ≤ ν³` and `ν³ < r`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa

/-! ## 1. Spatial Frobenius and Cauchy-Schwarz bound on `sAbs` -/

private lemma frobenius_sym_le (v : UnforcedLeray.Train.Vec) (z : ℂ) (u : Fin 2 → ℂ) :
    Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
      ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2) ≤
      2 * ‖z‖ * ‖v‖ * Real.sqrt (∑ j : Fin 2, ‖u j‖ ^ 2) := by
  have hterm : ∀ i j : Fin 2,
      ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2 ≤
        2 * (‖z‖ ^ 2 * ((v i) ^ 2 * ‖u j‖ ^ 2 + ‖u i‖ ^ 2 * (v j) ^ 2)) := by
    intro i j
    set X : ℝ := |v i| * (‖z‖ * ‖u j‖)
    set Y : ℝ := (‖z‖ * ‖u i‖) * |v j|
    have hX : 0 ≤ X := by positivity
    have hY : 0 ≤ Y := by positivity
    have htri : ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ≤ X + Y := by
      calc ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖
          ≤ ‖((v i : ℝ) : ℂ) * (z * u j)‖ + ‖(z * u i) * ((v j : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = X + Y := by
            simp only [X, Y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsq1 : ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2 ≤ (X + Y) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hsq2 : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by nlinarith [sq_nonneg (X - Y)]
    have hXY : X ^ 2 + Y ^ 2 = ‖z‖ ^ 2 * ((v i) ^ 2 * ‖u j‖ ^ 2 + ‖u i‖ ^ 2 * (v j) ^ 2) := by
      dsimp only [X, Y]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    linarith
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2,
      ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2 ≤
      4 * ‖z‖ ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2) := by
    simp only [Fin.sum_univ_two]
    have h00 := hterm 0 0
    have h01 := hterm 0 1
    have h10 := hterm 1 0
    have h11 := hterm 1 1
    linarith
  have hv_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hnn : 0 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by positivity
    rw [Real.sq_sqrt hnn, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  set R : ℝ := 2 * ‖z‖ * ‖v‖ * Real.sqrt (∑ j : Fin 2, ‖u j‖ ^ 2)
  have hR_nn : 0 ≤ R := by dsimp [R]; positivity
  have hR_sq : R ^ 2 = 4 * ‖z‖ ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2) := by
    dsimp only [R]
    have hu_nn : 0 ≤ ∑ j : Fin 2, ‖u j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hu_nn, hv_sq, Fin.sum_univ_two]
    ring
  calc Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
        ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2)
      ≤ Real.sqrt (R ^ 2) := by
        rw [hR_sq]
        exact Real.sqrt_le_sqrt hsum
    _ = R := Real.sqrt_sq hR_nn

private lemma cyl_cellμ_eq_restrict_cell (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell B0579.cell
  rw [neg_div]

private lemma continuous_train_vel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {s : ℝ} (hs : 0 ≤ s) :
    Continuous (tr.v s) :=
  tr.isTrain.smooth_v.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨hs, trivial⟩)

private lemma sAbs_le_cellL2_mul_velNorm {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) {s : ℝ} (hs : 0 < s)
    (hu : ∀ j : Fin 2, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) :
    sAbs tr μ u s ≤
      ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) *
        UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) *
        velNorm (ν ^ (-2 : ℝ)) u := by
  let c : ℝ := ν ^ (-2 : ℝ)
  let μ_c : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  have hc_inv : c⁻¹ = ν ^ 2 := by
    dsimp [c]
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_inv]
  have hcpow : ‖(s : ℂ) ^ (-μ)‖ = s ^ (-μ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs, Complex.neg_re]
  set F : ℝ × ℝ → ℝ≥0∞ := fun x => ‖tr.v s x‖ₑ
  set G : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2))
  have hF_aem : AEMeasurable F μ_c :=
    ((continuous_train_vel tr hs.le).measurable.enorm).aemeasurable
  have hG_aem : AEMeasurable G μ_c := by
    have hsum_aem : AEMeasurable (fun x => ∑ j : Fin 2, ‖u x j‖ ^ 2) μ_c :=
      Finset.aemeasurable_sum Finset.univ fun j _ => ((hu j).1.norm.aemeasurable.pow_const 2)
    exact (Real.continuous_sqrt.measurable.comp_aemeasurable hsum_aem).ennreal_ofReal
  have hpt : ∀ x : ℝ × ℝ,
      ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
          ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
              ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2)) ≤
        ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * (F x * G x) := by
    intro x
    have hfrob := frobenius_sym_le (tr.v s x) ((s : ℂ) ^ (-μ)) (u x)
    rw [hcpow] at hfrob
    rw [hc_inv]
    have h1 : ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
          ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
              ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2)) ≤
        ENNReal.ofReal (2 * s ^ (-μ.re) * ‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) :=
      ENNReal.ofReal_le_ofReal hfrob
    calc ENNReal.ofReal (ν ^ 2) *
          ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
            ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
                ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2))
        ≤ ENNReal.ofReal (ν ^ 2) *
            ENNReal.ofReal (2 * s ^ (-μ.re) * ‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 bot_le
      _ = ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * (F x * G x) := by
          have hv_nn : 0 ≤ ‖tr.v s x‖ := norm_nonneg _
          dsimp only [F, G]
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ν ^ 2),
            show ν ^ 2 * (2 * s ^ (-μ.re) * ‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) =
              (2 * ν ^ 2 * s ^ (-μ.re)) * (‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) by ring,
            ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ν ^ 2 * s ^ (-μ.re)),
            ENNReal.ofReal_mul hv_nn, ofReal_norm]
  have hFG_le : ∫⁻ x, F x * G x ∂μ_c ≤
      UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c u := by
    have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ_c Real.HolderConjugate.two_two hF_aem hG_aem
    have hF_lp : (∫⁻ x, F x ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) =
        UnforcedLeray.Train.cellL2 c (tr.v s) := by
      unfold UnforcedLeray.Train.cellL2
      rw [cyl_cellμ_eq_restrict_cell,
        eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      simp [F, μ_c]
    have hG_lp : (∫⁻ x, G x ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) = velNorm c u := by
      have hG_sq : ∀ x : ℝ × ℝ, G x ^ (2 : ℝ) = ∑ j : Fin 2, ‖u x j‖ₑ ^ 2 := by
        intro x
        set S : ℝ := ∑ j : Fin 2, ‖u x j‖ ^ 2
        have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
        dsimp only [G]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg S) 2, Real.sq_sqrt hS_nn]
        dsimp only [S]
        rw [Fin.sum_univ_two, Fin.sum_univ_two,
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _) 2, ENNReal.ofReal_pow (norm_nonneg _) 2,
          ofReal_norm, ofReal_norm]
      rw [lintegral_congr hG_sq,
        lintegral_finsetSum' Finset.univ (fun j _ => ((hu j).1.enorm.pow_const 2))]
      unfold velNorm
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [T07.eLpNorm_two_eq_lintegral, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    simpa only [Pi.mul_apply, hF_lp, hG_lp] using hhold
  unfold sAbs
  calc ∫⁻ x, ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
          ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
              ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2)) ∂μ_c
      ≤ ∫⁻ x, ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * (F x * G x) ∂μ_c := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * ∫⁻ x, F x * G x ∂μ_c :=
        lintegral_const_mul'' _ (hF_aem.mul hG_aem)
    _ ≤ ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) *
          (UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c u) :=
        mul_le_mul_of_nonneg_left hFG_le bot_le
    _ = ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) *
          UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c u := (mul_assoc _ _ _).symm

/-! ## 2. Biot-Savart rescaling and physical velocity bound from `ctKineticImpulse` -/

private def rescaleVelImp (a : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (y : ℝ × ℝ) (j : Fin 2) : ℂ :=
  ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u (Real.sqrt a • y) j

private lemma map_sqrt_smul_vol {a : ℝ} (ha : 0 < a) :
    Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume =
      ENNReal.ofReal a⁻¹ • (volume : Measure (ℝ × ℝ)) := by
  have hR : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ℝ × ℝ)) hR
  simpa only [hfin, Real.sq_sqrt ha.le, abs_inv, abs_of_pos ha] using hmap

private lemma qmp_sqrt_smul_vol {a : ℝ} (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ => Real.sqrt a • y) volume volume :=
  ⟨measurable_const_smul (Real.sqrt a), by
    rw [map_sqrt_smul_vol ha]
    exact Measure.smul_absolutelyContinuous⟩

private lemma lintegral_aem_comp_sqrt_smul {a : ℝ} (ha : 0 < a)
    {H : ℝ × ℝ → ℝ≥0∞} (hH : AEMeasurable H volume) :
    ∫⁻ y, H (Real.sqrt a • y) = ENNReal.ofReal a⁻¹ * ∫⁻ x, H x := by
  have hmap := map_sqrt_smul_vol ha
  have hH_map : AEMeasurable H (Measure.map (fun y : ℝ × ℝ => Real.sqrt a • y) volume) := by
    rw [hmap]
    exact hH.mono_ac Measure.smul_absolutelyContinuous
  rw [← lintegral_map' hH_map (measurable_const_smul (Real.sqrt a)).aemeasurable,
    hmap, lintegral_smul_measure, smul_eq_mul]

private lemma integrableOn_and_integral_comp_sqrt_smul_imp {a d : ℝ} (ha : 0 < a)
    {g : ℝ × ℝ → ℂ} (hg : IntegrableOn g (B0579.cell (d * Real.sqrt a))) :
    IntegrableOn (fun y => g (Real.sqrt a • y)) (B0579.cell d) ∧
      (∫ y in B0579.cell d, g (Real.sqrt a • y)) =
        ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), g x := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set G : ℝ × ℝ → ℂ := (B0579.cell (d * Real.sqrt a)).indicator g
  have hG_int : Integrable G volume :=
    (integrable_indicator_iff (B0579.measurableSet_cell _)).2 hg
  have hmap := map_sqrt_smul_vol ha
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

private lemma memLp_and_eLpNorm_rescaleVelImp {a d : ℝ} (ha : 0 < a)
    {u : ℝ × ℝ → Fin 2 → ℂ} (j : Fin 2)
    (hu : MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a)))) :
    MemLp (fun y => rescaleVelImp a u y j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun y => rescaleVelImp a u y j) 2 (volume.restrict (B0579.cell d)) =
        ENNReal.ofReal a *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have ha32_nn : 0 ≤ a ^ (3 / 2 : ℝ) := Real.rpow_nonneg ha.le _
  have hind_aesm : AEStronglyMeasurable
      ((B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j)) volume :=
    (aestronglyMeasurable_indicator_iff (B0579.measurableSet_cell _)).2 hu.1
  have hcomp_aesm : AEStronglyMeasurable
      (fun y : ℝ × ℝ => (B0579.cell (d * Real.sqrt a)).indicator (fun x => u x j) (Real.sqrt a • y))
      volume :=
    hind_aesm.comp_quasiMeasurePreserving (qmp_sqrt_smul_vol ha)
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
  have hsc_aesm : AEStronglyMeasurable (fun y => rescaleVelImp a u y j)
      (volume.restrict (B0579.cell d)) :=
    hu_comp_aesm.const_mul _
  set H : ℝ × ℝ → ℝ≥0∞ :=
    (B0579.cell (d * Real.sqrt a)).indicator (fun x => ‖u x j‖ₑ ^ 2)
  have hH_aem : AEMeasurable H volume :=
    (aemeasurable_indicator_iff (B0579.measurableSet_cell _)).2 (hu.1.enorm.pow_const 2)
  have hpt : ∀ y : ℝ × ℝ,
      (B0579.cell d).indicator (fun y => ‖rescaleVelImp a u y j‖ₑ ^ 2) y =
        ENNReal.ofReal (a ^ 3) * H (Real.sqrt a • y) := by
    intro y
    have hpow_a : (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
      rw [← Real.rpow_natCast (a ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul ha.le]
      norm_num
    by_cases hy : y ∈ B0579.cell d
    · have hy' := (T07.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      simp only [H, hy, hy', indicator_of_mem, rescaleVelImp, enorm_mul,
        T07.enorm_ofReal_cast ha32_nn, mul_pow, ← ENNReal.ofReal_pow ha32_nn 2, hpow_a]
    · have hy' : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T07.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [H, hy, hy']
  have hlint : ∫⁻ y in B0579.cell d, ‖rescaleVelImp a u y j‖ₑ ^ 2 =
      ENNReal.ofReal (a ^ 2) * ∫⁻ x in B0579.cell (d * Real.sqrt a), ‖u x j‖ₑ ^ 2 := by
    rw [← lintegral_indicator (B0579.measurableSet_cell d), lintegral_congr hpt,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_aem_comp_sqrt_smul ha hH_aem, ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg ha.le 3),
      show a ^ 3 * a⁻¹ = a ^ 2 by field_simp,
      lintegral_indicator (B0579.measurableSet_cell _)]
  have hnorm_eq : eLpNorm (fun y => rescaleVelImp a u y j) 2 (volume.restrict (B0579.cell d)) =
      ENNReal.ofReal a *
        eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
    rw [T07.eLpNorm_two_eq_lintegral, T07.eLpNorm_two_eq_lintegral, hlint,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg a) (by norm_num),
      ← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    norm_num
  refine ⟨⟨hsc_aesm, ?_⟩, hnorm_eq⟩
  rw [hnorm_eq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2

private lemma velNorm_rescaleVelImp {a d : ℝ} (ha : 0 < a)
    {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a)))) :
    velNorm d (rescaleVelImp a u) = ENNReal.ofReal a * velNorm (d * Real.sqrt a) u := by
  unfold velNorm
  have hj : ∀ j : Fin 2,
      eLpNorm (fun y => rescaleVelImp a u y j) 2 (volume.restrict (B0579.cell d)) ^ 2 =
        ENNReal.ofReal a ^ 2 *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) ^ 2 := by
    intro j
    rw [(memLp_and_eLpNorm_rescaleVelImp ha j (hu j)).2, mul_pow]
  simp_rw [hj, ← Finset.mul_sum]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]

private lemma isCylTest_inv_sqrt_smul_imp {a d : ℝ} (ha : 0 < a) {ψ : ℝ × ℝ → ℝ}
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
        have : |R| * Real.sqrt a < |x.2| := hx
        calc |R| = |R| * Real.sqrt a * (Real.sqrt a)⁻¹ := by field_simp [hR_ne]
          _ < |x.2| * (Real.sqrt a)⁻¹ := mul_lt_mul_of_pos_right this (inv_pos.2 hR)
          _ = (Real.sqrt a)⁻¹ * |x.2| := mul_comm _ _
      exact (le_abs_self R).trans_lt h1
  refine ⟨htest, fun j y => ?_⟩
  have hLy : L (Real.sqrt a • y) = y := by
    dsimp [L]
    exact inv_smul_smul₀ hR_ne y
  have hfderiv : HasFDerivAt (fun x => ψ ((Real.sqrt a)⁻¹ • x))
      ((fderiv ℝ ψ y).comp L) (Real.sqrt a • y) := by
    have hψ_fderiv : HasFDerivAt ψ (fderiv ℝ ψ y) (L (Real.sqrt a • y)) := by
      rw [hLy]
      exact (hψ.smooth.differentiable (by simp) y).hasFDerivAt
    exact HasFDerivAt.comp (Real.sqrt a • y) hψ_fderiv L.hasFDerivAt
  unfold B0579.pd
  rw [hfderiv.fderiv]
  simp [L, smul_eq_mul]

private lemma isBiotSavart_jscaleInv_imp {a d : ℝ} (ha : 0 < a) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ}
    (hf : MemLp f 2 (volume.restrict (B0579.cell (d * Real.sqrt a))))
    (hu : IsBiotSavart (d * Real.sqrt a) f u) :
    IsBiotSavart d (JscaleInv a f) (rescaleVelImp a u) := by
  have hR_ne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have ha_pow : a ^ (3 / 2 : ℝ) * Real.sqrt a = a ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]
    norm_num
  refine ⟨fun j => (memLp_and_eLpNorm_rescaleVelImp ha j (hu.1 j)).1, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨hψ_sc, hpd_sc⟩ := isCylTest_inv_sqrt_smul_imp ha hψ
    set g_div : ℝ × ℝ → ℂ := fun x =>
      u x 0 * (B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ) +
        u x 1 * (B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ)
    have hg_int : IntegrableOn g_div (B0579.cell (d * Real.sqrt a)) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 0) (hu.1 0)).add
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 1) (hu.1 1))
    obtain ⟨_, hcov⟩ := integrableOn_and_integral_comp_sqrt_smul_imp ha hg_int
    have hpt : (fun y : ℝ × ℝ =>
          rescaleVelImp a u y 0 * (B0579.pd 0 ψ y : ℂ) +
            rescaleVelImp a u y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_div (Real.sqrt a • y) := by
      funext y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 0 y]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 1 y]; field_simp [hR_ne]
      dsimp only [rescaleVelImp, g_div]
      rw [hp0', hp1', ← ha_pow]
      push_cast
      ring
    rw [hpt, integral_const_mul, hcov, hu.2.1 _ hψ_sc, mul_zero, mul_zero]
  · intro ψ hψ
    obtain ⟨hψ_sc, hpd_sc⟩ := isCylTest_inv_sqrt_smul_imp ha hψ
    set g_lhs : ℝ × ℝ → ℂ := fun x => f x * (ψ ((Real.sqrt a)⁻¹ • x) : ℂ)
    set g_rhs : ℝ × ℝ → ℂ := fun x =>
      u x 0 * (B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ) -
        u x 1 * (B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) x : ℂ)
    have hgl_int : IntegrableOn g_lhs (B0579.cell (d * Real.sqrt a)) :=
      CoreDuhamelRepSub.integrableOn_cylTest_mul hψ_sc hf
    have hgr_int : IntegrableOn g_rhs (B0579.cell (d * Real.sqrt a)) :=
      (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 1) (hu.1 0)).sub
        (CoreDuhamelRepSub.integrableOn_cylTest_mul (hψ_sc.pd 0) (hu.1 1))
    obtain ⟨_, hcov_l⟩ := integrableOn_and_integral_comp_sqrt_smul_imp ha hgl_int
    obtain ⟨_, hcov_r⟩ := integrableOn_and_integral_comp_sqrt_smul_imp ha hgr_int
    have hpt_l : (fun y : ℝ × ℝ => JscaleInv a f y * (ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_lhs (Real.sqrt a • y) := by
      funext y
      dsimp only [JscaleInv, g_lhs]
      rw [← T07.sqrt_smul_eq, inv_smul_smul₀ hR_ne]
      ring
    have hpt_r : (fun y : ℝ × ℝ =>
          rescaleVelImp a u y 0 * (B0579.pd 1 ψ y : ℂ) -
            rescaleVelImp a u y 1 * (B0579.pd 0 ψ y : ℂ)) =
        fun y => ((a ^ 2 : ℝ) : ℂ) * g_rhs (Real.sqrt a • y) := by
      funext y
      have hp0' : B0579.pd 0 ψ y = Real.sqrt a *
          B0579.pd 0 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 0 y]; field_simp [hR_ne]
      have hp1' : B0579.pd 1 ψ y = Real.sqrt a *
          B0579.pd 1 (fun z => ψ ((Real.sqrt a)⁻¹ • z)) (Real.sqrt a • y) := by
        rw [hpd_sc 1 y]; field_simp [hR_ne]
      dsimp only [rescaleVelImp, g_rhs]
      rw [hp0', hp1', ← ha_pow]
      push_cast
      ring
    rw [hpt_l, hpt_r, integral_const_mul, integral_const_mul, hcov_l, hcov_r, hu.2.2 _ hψ_sc]

private lemma dOfTheta_mul_sqrt_inv_imp {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    dOfTheta ν x * Real.sqrt ((ν * x)⁻¹) = ν ^ (-2 : ℝ) := by
  unfold dOfTheta
  have hc_pos : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
    ring
  rw [← Real.sqrt_mul (by positivity : 0 ≤ x / ν ^ 3)]
  have hprod : x / ν ^ 3 * (ν * x)⁻¹ = (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hc_sq]
    have := hν.ne'
    have := hx.ne'
    field_simp
  rw [hprod, Real.sqrt_sq hc_pos.le]

private lemma velNorm_congr_ae_imp {d : ℝ} {u v : ℝ × ℝ → Fin 2 → ℂ}
    (h : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), u x = v x) :
    velNorm d u = velNorm d v := by
  unfold velNorm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

private lemma velNorm_le_of_kineticImpulse {m b C_kin ν r s : ℝ}
    (hm : 0 ≤ m) (_hC_kin : 0 < C_kin) (hν : 0 < ν) (hr : 0 < r) (_hrb : r ≤ b)
    (hs_pos : 0 < s) (hs : clockAge ν r ≤ s)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {h : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (_hh_mem : MemLp h 2 (B0579.cellMeasure (dOfTheta ν r) m))
    (_hh_zc : HasZeroCirculation (dOfTheta ν r) h)
    (_hh_even : IsCentrallyEven h)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (clockAge ν r) (Jscale (ν * r)⁻¹ h) w u)
    (hkin : ∀ θ : ℝ, 0 < θ → θ ≤ r → ∀ Zh : ℝ × ℝ → ℂ,
      HeatEvolvesTo ν m tr r θ h Zh →
        kinNorm (dOfTheta ν θ) Zh ≤ ENNReal.ofReal (C_kin * (r / θ)) * kinNorm (dOfTheta ν r) h) :
    velNorm (ν ^ (-2 : ℝ)) (u s) ≤ ENNReal.ofReal (C_kin * ν * r) * kinNorm (dOfTheta ν r) h := by
  have ha_s : 0 < clockA ν s := by unfold clockA; positivity
  set θ : ℝ := clockTheta ν s
  have hθ_pos : 0 < θ := by unfold θ clockTheta; positivity
  have hs_eq : clockAge ν θ = s := clockAge_clockTheta hν ha_s
  have hθ_le_r : θ ≤ r := by
    have hs' : (1 - ν * r) / (ν ^ 2 * r) ≤ s := hs
    have hmul : 1 - ν * r ≤ s * (ν ^ 2 * r) := (div_le_iff₀ (by positivity)).1 hs'
    have h1 : 1 ≤ (ν * clockA ν s) * r := by unfold clockA; nlinarith
    unfold θ clockTheta
    exact (inv_le_iff_one_le_mul₀' (by positivity)).2 h1
  set Zh : ℝ × ℝ → ℂ := JscaleInv (ν * θ)⁻¹ (w (clockAge ν θ))
  have hEvol : HeatEvolvesTo ν m tr r θ h Zh := ⟨w, u, hw, rfl⟩
  have hkin_bd := hkin θ hθ_pos hθ_le_r Zh hEvol
  let c : ℝ := ν ^ (-2 : ℝ)
  set d_θ : ℝ := dOfTheta ν θ
  have hd_θ_pos : 0 < d_θ := by unfold d_θ dOfTheta; exact Real.sqrt_pos.2 (by positivity)
  have ha_θ_pos : 0 < (ν * θ)⁻¹ := inv_pos.2 (mul_pos hν hθ_pos)
  have hd_eq : d_θ * Real.sqrt ((ν * θ)⁻¹) = c := dOfTheta_mul_sqrt_inv_imp hν hθ_pos
  have hw_s_l2 : MemLp (w s) 2 (volume.restrict (B0579.cell (d_θ * Real.sqrt ((ν * θ)⁻¹)))) := by
    rw [hd_eq]
    exact (hw.memX s hs).mono_measure (B0581.cellVol_le_cellMeasure c hm)
  have hbs_c : IsBiotSavart (d_θ * Real.sqrt ((ν * θ)⁻¹)) (w s) (u s) := by
    rw [hd_eq]
    exact hw.biotSavart s hs
  have hu_sc_bs : IsBiotSavart d_θ Zh (rescaleVelImp (ν * θ)⁻¹ (u s)) := by
    dsimp only [Zh]
    rw [hs_eq]
    exact isBiotSavart_jscaleInv_imp ha_θ_pos hw_s_l2 hbs_c
  have hkin_lower : ENNReal.ofReal ((ν * θ)⁻¹) * velNorm c (u s) ≤ kinNorm d_θ Zh := by
    have hv_eq : velNorm d_θ (rescaleVelImp (ν * θ)⁻¹ (u s)) =
        ENNReal.ofReal ((ν * θ)⁻¹) * velNorm c (u s) := by
      rw [velNorm_rescaleVelImp ha_θ_pos hbs_c.1, hd_eq]
    rw [← hv_eq]
    unfold kinNorm
    refine le_iInf₂ fun v hv => ?_
    have hae := CTE.isBiotSavart_unique d_θ hd_θ_pos Zh (rescaleVelImp (ν * θ)⁻¹ (u s)) v
      hu_sc_bs hv
    rw [velNorm_congr_ae_imp hae]
  have hscaled := mul_le_mul_of_nonneg_left (hkin_lower.trans hkin_bd)
    (bot_le : 0 ≤ ENNReal.ofReal (ν * θ))
  have hlhs : ENNReal.ofReal (ν * θ) * (ENNReal.ofReal ((ν * θ)⁻¹) * velNorm c (u s)) =
      velNorm c (u s) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_pos hν hθ_pos).le,
      mul_inv_cancel₀ (mul_pos hν hθ_pos).ne', ENNReal.ofReal_one, one_mul]
  have hrhs : ENNReal.ofReal (ν * θ) *
      (ENNReal.ofReal (C_kin * (r / θ)) * kinNorm (dOfTheta ν r) h) =
      ENNReal.ofReal (C_kin * ν * r) * kinNorm (dOfTheta ν r) h := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_pos hν hθ_pos).le]
    congr 1
    have := hθ_pos.ne'
    field_simp
  rwa [hlhs, hrhs] at hscaled

/-! ## 3. Clock/overlap arithmetic, train `L²` bounds, and `Ioi` power integrals -/

private lemma clock_and_overlap_bounds {b ν r : ℝ} (hb : 1 ≤ b) (hν : 0 < ν)
    (hν_half : ν ≤ 1 / 2) (hν_3b : ν ≤ (3 * b)⁻¹) (hr : 0 < r) (hrb : r ≤ b) :
    let c := ν ^ (-2 : ℝ)
    let s_r := clockAge ν r
    let s_c := UnforcedLeray.B0146.overlapAge ν c
    0 < s_r ∧ s_r⁻¹ ≤ 2 * ν ^ 2 * r ∧
      0 < s_c ∧ s_c ≤ (ν ^ 5)⁻¹ ∧ s_c⁻¹ ≤ 2 * ν ^ 5 ∧
      (r ≤ ν ^ 3 → s_c ≤ s_r) ∧ (ν ^ 3 < r → s_r < s_c) := by
  dsimp only
  have hb_pos : 0 < b := by linarith
  have hνr_le : ν * r ≤ 1 / 3 := by
    calc ν * r ≤ ν * b := mul_le_mul_of_nonneg_left hrb hν.le
      _ ≤ (3 * b)⁻¹ * b := mul_le_mul_of_nonneg_right hν_3b hb_pos.le
      _ = 1 / 3 := by field_simp
  have hsr_ge : (2 * ν ^ 2 * r)⁻¹ ≤ clockAge ν r := by
    unfold clockAge
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * (ν ^ 2 * r)
        ≤ ((1 - ν * r) * 2) * (ν ^ 2 * r) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1 - ν * r) * (2 * ν ^ 2 * r) := by ring
  have hsr_pos : 0 < clockAge ν r := lt_of_lt_of_le (by positivity) hsr_ge
  have hsr_inv : (clockAge ν r)⁻¹ ≤ 2 * ν ^ 2 * r := by
    have h := inv_anti₀ (by positivity : 0 < (2 * ν ^ 2 * r)⁻¹) hsr_ge
    rwa [inv_inv] at h
  have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
    ring
  have hsc_eq : UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) = (1 - ν ^ 4) / ν ^ 5 := by
    unfold UnforcedLeray.B0146.overlapAge
    rw [hc_sq]
    have := hν.ne'
    field_simp
  have hν4_le : ν ^ 4 ≤ 1 / 16 := by
    calc ν ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hν.le hν_half 4
      _ = 1 / 16 := by norm_num
  have hsc_ge : (2 * ν ^ 5)⁻¹ ≤ UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) := by
    rw [hsc_eq, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hν 5]
  have hsc_pos : 0 < UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) :=
    lt_of_lt_of_le (by positivity) hsc_ge
  have hsc_le : UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) ≤ (ν ^ 5)⁻¹ := by
    rw [hsc_eq, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hν.le 4]) (by positivity)
  have hsc_inv : (UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)))⁻¹ ≤ 2 * ν ^ 5 := by
    have h := inv_anti₀ (by positivity : 0 < (2 * ν ^ 5)⁻¹) hsc_ge
    rwa [inv_inv] at h
  refine ⟨hsr_pos, hsr_inv, hsc_pos, hsc_le, hsc_inv, fun hrc => ?_, fun hr_gt => ?_⟩
  · rw [hsc_eq]
    unfold clockAge
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 - ν ^ 4) * (ν ^ 2 * r) = ν ^ 2 * r - ν ^ 6 * r := by ring
    have h2 : (1 - ν * r) * ν ^ 5 = ν ^ 5 - ν ^ 6 * r := by ring
    rw [h1, h2]
    nlinarith [sq_nonneg ν]
  · rw [hsc_eq]
    unfold clockAge
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hlt : ν ^ 5 < ν ^ 2 * r := by
      calc ν ^ 5 = ν ^ 2 * ν ^ 3 := by ring
        _ < ν ^ 2 * r := mul_lt_mul_of_pos_left hr_gt (pow_pos hν 2)
    have h1 : (1 - ν * r) * ν ^ 5 = ν ^ 5 - ν ^ 6 * r := by ring
    have h2 : (1 - ν ^ 4) * (ν ^ 2 * r) = ν ^ 2 * r - ν ^ 6 * r := by ring
    rw [h1, h2]
    exact sub_lt_sub_right hlt (ν ^ 6 * r)

private lemma train_cellL2_pre_le {C_tr ν s : ℝ} (_hC_tr : 0 < C_tr) (hν : 0 < ν) (hs : 0 < s)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤
      ENNReal.ofReal (C_tr * (UnforcedLeray.Train.width ν s)⁻¹)) :
    UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤
      ENNReal.ofReal (C_tr * ν⁻¹ * s ^ (-1 : ℝ)) := by
  refine hbd.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw_ge : ν * s ≤ UnforcedLeray.Train.width ν s := by
    unfold UnforcedLeray.Train.width
    linarith
  have hinv : (UnforcedLeray.Train.width ν s)⁻¹ ≤ (ν * s)⁻¹ :=
    inv_anti₀ (mul_pos hν hs) hw_ge
  calc C_tr * (UnforcedLeray.Train.width ν s)⁻¹
      ≤ C_tr * (ν * s)⁻¹ := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = C_tr * ν⁻¹ * s ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, mul_inv]
        ring

private lemma train_cellL2_post_le {C_tr ν s : ℝ} (_hC_tr : 0 < C_tr) (hν : 0 < ν) (hs : 0 < s)
    (hsc_pos : 0 < UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)))
    (hsc_le : UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) ≤ (ν ^ 5)⁻¹)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤
      ENNReal.ofReal (C_tr * (ν ^ (-2 : ℝ)) ^ (-2 : ℝ) *
        (s / UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ))) ^ (-(3 / 4 : ℝ)))) :
    UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) ≤
      ENNReal.ofReal (C_tr * ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ))) := by
  refine hbd.trans (ENNReal.ofReal_le_ofReal ?_)
  set s_c := UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ))
  have hc_pow : (ν ^ (-2 : ℝ)) ^ (-2 : ℝ) = ν ^ (4 : ℝ) := by
    rw [← Real.rpow_mul hν.le]
    norm_num
  have hdiv_pow : (s / s_c) ^ (-(3 / 4 : ℝ)) = s_c ^ (3 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) := by
    rw [div_eq_mul_inv, Real.mul_rpow hs.le (inv_nonneg.2 hsc_pos.le),
      Real.inv_rpow hsc_pos.le, ← Real.rpow_neg hsc_pos.le, neg_neg, mul_comm]
  have hsc_rpow : s_c ^ (3 / 4 : ℝ) ≤ ν ^ (-15 / 4 : ℝ) := by
    have hinv5 : (ν ^ 5)⁻¹ = ν ^ (-5 : ℝ) := by
      rw [show (-5 : ℝ) = -((5 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast]
    calc s_c ^ (3 / 4 : ℝ)
        ≤ ((ν ^ 5)⁻¹) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hsc_pos.le hsc_le (by norm_num)
      _ = (ν ^ (-5 : ℝ)) ^ (3 / 4 : ℝ) := by rw [hinv5]
      _ = ν ^ (-15 / 4 : ℝ) := by
          rw [← Real.rpow_mul hν.le]
          norm_num
  have hν_comb : ν ^ (4 : ℝ) * ν ^ (-15 / 4 : ℝ) = ν ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hν]
    norm_num
  rw [hc_pow, hdiv_pow]
  calc C_tr * ν ^ (4 : ℝ) * (s_c ^ (3 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))
      = C_tr * s ^ (-(3 / 4 : ℝ)) * (ν ^ (4 : ℝ) * s_c ^ (3 / 4 : ℝ)) := by ring
    _ ≤ C_tr * s ^ (-(3 / 4 : ℝ)) * (ν ^ (4 : ℝ) * ν ^ (-15 / 4 : ℝ)) := by
        gcongr
    _ = C_tr * ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)) := by
        rw [hν_comb]
        ring

private lemma lintegral_Ioi_ofReal_rpow {a q : ℝ} (ha : 0 < a) (hq : 1 < q) :
    ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ (-q)) =
      ENNReal.ofReal ((a⁻¹) ^ (q - 1) / (q - 1)) := by
  have hlt : -q < -1 := by linarith
  have hint := integrableOn_Ioi_rpow_of_lt hlt ha
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun s : ℝ => s ^ (-q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Real.rpow_nonneg (ha.trans hs).le _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_Ioi_rpow_of_lt hlt ha]
  congr 1
  have hpow : a ^ (-q + 1) = (a⁻¹) ^ (q - 1) := by
    rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [hpow]
  have hq_ne : q - 1 ≠ 0 := by linarith
  have h1q_ne : -q + 1 ≠ 0 := by linarith
  field_simp
  ring

private lemma scale_base_eq {ν r σ : ℝ} (hν : 0 < ν) (_hr : 0 < r) (k : ℕ) :
    let p_k := σ + 3 / 2 + (k : ℝ) / 2
    (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * r ^ (σ + 5 / 2 + (k : ℝ) / 2) =
      ν ^ (2 + 2 * p_k) * r ^ (p_k + 1) := by
  intro p_k
  have hdiv : ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ) = ν ^ (5 + 2 * σ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hν.le, neg_neg, ← Real.rpow_add hν]
    congr 1
    ring
  rw [hdiv, ← Real.rpow_natCast ν k, ← Real.rpow_add hν]
  congr 1
  · congr 1; dsimp [p_k]; ring
  · congr 1; dsimp [p_k]; ring

/-! ## 4. Main proof of `ctAbsoluteImpulse` -/

/-- **`eq:ct-absolute-impulse`** (SP 3275-3289): absolute stress impulse bound for `k ≤ 1`. -/
theorem ctAbsoluteImpulse : UnforcedLeray.Short.IIIa.T22Sub.CTAbsoluteImpulse := by
  intro P hP m hm K hK k hk
  obtain ⟨b₀_kin, hkin_all⟩ := ctKineticImpulse P hP m hm
  obtain ⟨C_tr, ν_tr, hC_tr, hν_tr, htr_l2⟩ :=
    trainL2Decay_unconditional 2 (by norm_num : (1 / 2 : ℝ) < 2)
  refine ⟨max b₀_kin 1, fun b hb => ?_⟩
  have hb_kin : b₀_kin ≤ b := (le_max_left _ _).trans hb
  have hb_one : 1 ≤ b := (le_max_right _ _).trans hb
  have hb_pos : 0 < b := by linarith
  obtain ⟨C_kin0, ν_kin, hν_kin, hkin_ν⟩ := hkin_all b hb_kin
  set C_kin : ℝ := max C_kin0 1
  have hC_kin : 0 < C_kin := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set C : ℝ := 24 * C_kin * C_tr
  have hC_pos : 0 < C := by positivity
  set ν₀ : ℝ := min ν_kin (min ν_tr (min (1 / 2) ((3 * b)⁻¹)))
  have hν₀_pos : 0 < ν₀ :=
    lt_min hν_kin (lt_min hν_tr (lt_min (by norm_num) (inv_pos.2 (by positivity))))
  refine ⟨C, ν₀, hν₀_pos,
    fun ν hν tr htr r hr hrb h hh_mem hh_zc hh_even w u hw μ hμ => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_le_kin : ν ≤ ν_kin := hν.2.trans (min_le_left _ _)
  have hν_le_tr : ν ≤ ν_tr := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_half : ν ≤ 1 / 2 :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_3b : ν ≤ (3 * b)⁻¹ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hσ_pos, hσ_lt⟩ := hK.2 μ hμ
  set σ : ℝ := μ.re
  set p_k : ℝ := σ + 3 / 2 + (k : ℝ) / 2
  have hk_nn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk_le1 : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  have hp_gt : 3 / 2 < p_k := by dsimp [p_k]; linarith
  have hp_lt : p_k < 9 / 4 := by dsimp [p_k]; linarith
  let c : ℝ := ν ^ (-2 : ℝ)
  set s_r : ℝ := clockAge ν r
  set s_c : ℝ := UnforcedLeray.B0146.overlapAge ν c
  obtain ⟨hsr_pos, hsr_inv, hsc_pos, hsc_le, hsc_inv, hrc_imp, hr_gt_imp⟩ :=
    clock_and_overlap_bounds hb_one hν_pos hν_half hν_3b hr hrb
  set K_norm : ℝ≥0∞ := kinNorm (dOfTheta ν r) h
  -- Uniform physical velocity bound `velNorm c (u s) ≤ ofReal (C_kin * ν * r) * K_norm` on `s ≥ s_r`
  have hvel_bd : ∀ s : ℝ, s_r ≤ s →
      velNorm c (u s) ≤ ENNReal.ofReal (C_kin * ν * r) * K_norm := by
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hsr_pos hs
    refine velNorm_le_of_kineticImpulse (by linarith : 0 ≤ m) hC_kin hν_pos hr hrb
      hs_pos hs hh_mem hh_zc hh_even hw (fun θ hθ hθr Zh hEvol => ?_)
    have hraw := hkin_ν ν ⟨hν_pos, hν_le_kin⟩ tr htr r θ hθ hθr hrb h Zh hh_mem hh_zc hh_even hEvol
    refine hraw.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (div_pos hr hθ).le
  -- Pointwise bound on the full integrand for `s ∈ Ioi s_r` in terms of `cellL2 c (tr.v s)`
  have hint_pt : ∀ s : ℝ, s_r < s →
      ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s ≤
        ENNReal.ofReal (2 * C_kin * ν ^ 3 * r * s ^ (-p_k)) *
          UnforcedLeray.Train.cellL2 c (tr.v s) * K_norm := by
    intro s hs
    have hs_pos : 0 < s := hsr_pos.trans hs
    have hs_abs := sAbs_le_cellL2_mul_velNorm hν_pos tr μ (u s) hs_pos (hw.biotSavart s hs.le).1
    have hv_s := hvel_bd s hs.le
    have hexp_s : s ^ (-3 / 2 - (k : ℝ) / 2) * (2 * ν ^ 2 * s ^ (-σ)) * (C_kin * ν * r) =
        2 * C_kin * ν ^ 3 * r * s ^ (-p_k) := by
      have hs_pow : s ^ (-3 / 2 - (k : ℝ) / 2) * s ^ (-σ) = s ^ (-p_k) := by
        rw [← Real.rpow_add hs_pos]
        congr 1
        dsimp [p_k]
        ring
      calc s ^ (-3 / 2 - (k : ℝ) / 2) * (2 * ν ^ 2 * s ^ (-σ)) * (C_kin * ν * r)
          = 2 * C_kin * (ν ^ 2 * ν) * r * (s ^ (-3 / 2 - (k : ℝ) / 2) * s ^ (-σ)) := by ring
        _ = 2 * C_kin * ν ^ 3 * r * s ^ (-p_k) := by rw [hs_pow]; ring
    calc ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s
        ≤ ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
            (ENNReal.ofReal (2 * ν ^ 2 * s ^ (-σ)) *
              UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c (u s)) :=
          mul_le_mul_of_nonneg_left hs_abs bot_le
      _ ≤ ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
            (ENNReal.ofReal (2 * ν ^ 2 * s ^ (-σ)) *
              UnforcedLeray.Train.cellL2 c (tr.v s) *
              (ENNReal.ofReal (C_kin * ν * r) * K_norm)) := by
          gcongr
      _ = (ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
            ENNReal.ofReal (2 * ν ^ 2 * s ^ (-σ)) *
            ENNReal.ofReal (C_kin * ν * r)) *
            UnforcedLeray.Train.cellL2 c (tr.v s) * K_norm := by
          simp only [mul_assoc, mul_left_comm (UnforcedLeray.Train.cellL2 c (tr.v s))]
      _ = ENNReal.ofReal (2 * C_kin * ν ^ 3 * r * s ^ (-p_k)) *
            UnforcedLeray.Train.cellL2 c (tr.v s) * K_norm := by
          congr 2
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hexp_s]
  -- Pointwise pre- and post-overlap specializations on `s > s_r`
  have hpt_pre : ∀ s : ℝ, s_r < s → s ≤ s_c →
      ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s ≤
        (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) *
          ENNReal.ofReal (s ^ (-(p_k + 1)))) * K_norm := by
    intro s hs hsc
    have hs_pos : 0 < s := hsr_pos.trans hs
    have hl2 := train_cellL2_pre_le hC_tr hν_pos hs_pos
      ((htr_l2 ν hν_pos hν_le_tr tr htr s hs_pos.le).1 hsc)
    refine (hint_pt s hs).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ bot_le
    refine (mul_le_mul_of_nonneg_left hl2 bot_le).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs_comb : s ^ (-p_k) * s ^ (-1 : ℝ) = s ^ (-(p_k + 1)) := by
      rw [← Real.rpow_add hs_pos]; congr 1; ring
    have hν_comb : ν ^ 3 * ν⁻¹ = ν ^ 2 := by
      have := hν_pos.ne'; field_simp
    exact (calc 2 * C_kin * ν ^ 3 * r * s ^ (-p_k) * (C_tr * ν⁻¹ * s ^ (-1 : ℝ))
        = 2 * C_kin * C_tr * (ν ^ 3 * ν⁻¹) * r * (s ^ (-p_k) * s ^ (-1 : ℝ)) := by ring
      _ = 2 * C_kin * C_tr * ν ^ 2 * r * s ^ (-(p_k + 1)) := by rw [hν_comb, hs_comb]).le
  have hpt_post : ∀ s : ℝ, s_r < s → s_c ≤ s →
      ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s ≤
        (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
          ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
    intro s hs hsc
    have hs_pos : 0 < s := hsr_pos.trans hs
    have hl2 := train_cellL2_post_le hC_tr hν_pos hs_pos hsc_pos hsc_le
      ((htr_l2 ν hν_pos hν_le_tr tr htr s hs_pos.le).2 hsc)
    refine (hint_pt s hs).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ bot_le
    refine (mul_le_mul_of_nonneg_left hl2 bot_le).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs_comb : s ^ (-p_k) * s ^ (-(3 / 4 : ℝ)) = s ^ (-(p_k + 3 / 4)) := by
      rw [← Real.rpow_add hs_pos]; congr 1; ring
    have hν_comb : ν ^ 3 * ν ^ (1 / 4 : ℝ) = ν ^ (13 / 4 : ℝ) := by
      rw [← Real.rpow_natCast ν 3, ← Real.rpow_add hν_pos]; norm_num
    exact (calc 2 * C_kin * ν ^ 3 * r * s ^ (-p_k) * (C_tr * ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))
        = 2 * C_kin * C_tr * (ν ^ 3 * ν ^ (1 / 4 : ℝ)) * r *
            (s ^ (-p_k) * s ^ (-(3 / 4 : ℝ))) := by ring
      _ = 2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r * s ^ (-(p_k + 3 / 4)) := by
          rw [hν_comb, hs_comb]).le
  -- Base target scale identity
  set S_base : ℝ := (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * r ^ (σ + 5 / 2 + (k : ℝ) / 2)
  have hS_base_eq : S_base = ν ^ (2 + 2 * p_k) * r ^ (p_k + 1) :=
    scale_base_eq hν_pos hr k
  have hS_base_nn : 0 ≤ S_base := by rw [hS_base_eq]; positivity
  -- Split into `r ≤ ν ^ 3` vs `ν ^ 3 < r`
  by_cases hrc : r ≤ ν ^ 3
  · -- Case 1: `r ≤ ν ^ 3`, so `s_c ≤ s_r` and only post-overlap enters
    have hsc_le_sr : s_c ≤ s_r := hrc_imp hrc
    have hmeas_post : Measurable (fun s : ℝ =>
        ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
          ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) :=
      measurable_const.mul ((measurable_id.pow_const _).ennreal_ofReal)
    have hI_le : ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s ≤
        (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
          ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
      calc ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s
          ≤ ∫⁻ s in Ioi s_r,
              (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
                ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
            refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
            exact hpt_post s hs (hsc_le_sr.trans hs.le)
        _ = (∫⁻ s in Ioi s_r,
              ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
                ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm :=
            lintegral_mul_const K_norm hmeas_post
        _ = (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
              ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_Ioi_ofReal_rpow hsr_pos (by linarith only [hp_gt] : 1 < p_k + 3 / 4)] at hI_le
    refine hI_le.trans (mul_le_mul_of_nonneg_right ?_ bot_le)
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hexp_eq : p_k + 3 / 4 - 1 = p_k - 1 / 4 := by ring
    rw [hexp_eq]
    have hq_gt1 : 1 ≤ p_k - 1 / 4 := by linarith only [hp_gt]
    have hq_pos : 0 < p_k - 1 / 4 := by linarith only [hp_gt]
    have hq_lt2 : p_k - 1 / 4 ≤ 2 := by linarith only [hp_lt]
    have hdiv_le : (s_r⁻¹) ^ (p_k - 1 / 4) / (p_k - 1 / 4) ≤ (s_r⁻¹) ^ (p_k - 1 / 4) :=
      div_le_self (Real.rpow_nonneg (inv_nonneg.2 hsr_pos.le) _) hq_gt1
    have hsr_pow : (s_r⁻¹) ^ (p_k - 1 / 4) ≤ 4 * ν ^ (2 * p_k - 1 / 2) * r ^ (p_k - 1 / 4) := by
      calc (s_r⁻¹) ^ (p_k - 1 / 4)
          ≤ (2 * ν ^ 2 * r) ^ (p_k - 1 / 4) :=
            Real.rpow_le_rpow (inv_nonneg.2 hsr_pos.le) hsr_inv hq_pos.le
        _ = 2 ^ (p_k - 1 / 4) * (ν ^ 2) ^ (p_k - 1 / 4) * r ^ (p_k - 1 / 4) := by
            rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by norm_num) (sq_nonneg ν)]
        _ ≤ 4 * (ν ^ 2) ^ (p_k - 1 / 4) * r ^ (p_k - 1 / 4) := by
            have h2_pow : (2 : ℝ) ^ (p_k - 1 / 4) ≤ 4 := by
              calc (2 : ℝ) ^ (p_k - 1 / 4) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq_lt2
                _ = 4 := by norm_num
            gcongr
        _ = 4 * ν ^ (2 * p_k - 1 / 2) * r ^ (p_k - 1 / 4) := by
            congr 2
            rw [← Real.rpow_natCast ν 2, ← Real.rpow_mul hν_pos.le]
            congr 1; push_cast; ring
    have hmax_ge : (ν ^ 3 / r) ^ (1 / 4 : ℝ) ≤ max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) := le_max_right _ _
    have hprod_eq : ν ^ (13 / 4 : ℝ) * r * (ν ^ (2 * p_k - 1 / 2) * r ^ (p_k - 1 / 4)) =
        S_base * ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) := by
      have h_rat : (ν ^ 3 / r) ^ (1 / 4 : ℝ) =
          ν ^ ((3 : ℕ) * (1 / 4 : ℝ)) * r ^ (-(1 / 4 : ℝ)) := by
        rw [div_eq_mul_inv, Real.mul_rpow (pow_nonneg hν_pos.le 3) (inv_nonneg.2 hr.le),
          ← Real.rpow_natCast ν 3, ← Real.rpow_mul hν_pos.le,
          Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
      rw [hS_base_eq, h_rat]
      have hν_lhs : ν ^ (13 / 4 : ℝ) * ν ^ (2 * p_k - 1 / 2) =
          ν ^ (2 + 2 * p_k) * ν ^ ((3 : ℕ) * (1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hν_pos, ← Real.rpow_add hν_pos]
        congr 1; push_cast; ring
      have hr_lhs : r * r ^ (p_k - 1 / 4) = r ^ (p_k + 1) * r ^ (-(1 / 4 : ℝ)) := by
        have hL : r ^ (1 + (p_k - 1 / 4)) = r * r ^ (p_k - 1 / 4) := by
          rw [Real.rpow_add hr 1 (p_k - 1 / 4), Real.rpow_one]
        rw [← hL, ← Real.rpow_add hr (p_k + 1) (-(1 / 4 : ℝ))]
        congr 1; ring
      calc ν ^ (13 / 4 : ℝ) * r * (ν ^ (2 * p_k - 1 / 2) * r ^ (p_k - 1 / 4))
          = (ν ^ (13 / 4 : ℝ) * ν ^ (2 * p_k - 1 / 2)) * (r * r ^ (p_k - 1 / 4)) := by ring
        _ = (ν ^ (2 + 2 * p_k) * ν ^ ((3 : ℕ) * (1 / 4 : ℝ))) *
              (r ^ (p_k + 1) * r ^ (-(1 / 4 : ℝ))) := by rw [hν_lhs, hr_lhs]
        _ = ν ^ (2 + 2 * p_k) * r ^ (p_k + 1) *
              (ν ^ ((3 : ℕ) * (1 / 4 : ℝ)) * r ^ (-(1 / 4 : ℝ))) := by ring
    calc 2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r * ((s_r⁻¹) ^ (p_k - 1 / 4) / (p_k - 1 / 4))
        ≤ 2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r * (4 * ν ^ (2 * p_k - 1 / 2) * r ^ (p_k - 1 / 4)) :=
          mul_le_mul_of_nonneg_left (hdiv_le.trans hsr_pow) (by positivity)
      _ = 8 * C_kin * C_tr * (ν ^ (13 / 4 : ℝ) * r *
            (ν ^ (2 * p_k - 1 / 2) * r ^ (p_k - 1 / 4))) := by ring
      _ = 8 * C_kin * C_tr * (S_base * ((ν ^ 3 / r) ^ (1 / 4 : ℝ))) := by rw [hprod_eq]
      _ ≤ 8 * C_kin * C_tr * (S_base * max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax_ge hS_base_nn) (by positivity)
      _ ≤ C * (S_base * max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ))) := by
          have hprod_pos : 0 < C_kin * C_tr := mul_pos hC_kin hC_tr
          have h2 : 8 * C_kin * C_tr ≤ C := by dsimp [C]; linarith only [hprod_pos]
          exact mul_le_mul_of_nonneg_right h2
            (mul_nonneg hS_base_nn (zero_le_one.trans (le_max_left _ _)))
      _ = C * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * r ^ (σ + 5 / 2 + (k : ℝ) / 2) *
            max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) := by
          dsimp [S_base]; ring
  · -- Case 2: `ν ^ 3 < r`, split `Ioi s_r ⊆ Ioc s_r s_c ∪ Ioi s_c`
    have hr_gt : ν ^ 3 < r := not_le.1 hrc
    set F_int : ℝ → ℝ≥0∞ := fun s =>
      ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s
    have hcov : Ioi s_r ⊆ Ioc s_r s_c ∪ Ioi s_c := by
      intro s hs
      by_cases hsc : s ≤ s_c
      · exact Or.inl ⟨hs, hsc⟩
      · exact Or.inr (not_le.1 hsc)
    have hsplit : ∫⁻ s in Ioi s_r, F_int s ≤
        (∫⁻ s in Ioc s_r s_c, F_int s) + (∫⁻ s in Ioi s_c, F_int s) :=
      (lintegral_mono_set hcov).trans (lintegral_union_le _ _ _)
    -- Sub-integral 2a: pre-overlap `Ioc s_r s_c`
    have hmeas_pre : Measurable (fun s : ℝ =>
        ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) * ENNReal.ofReal (s ^ (-(p_k + 1)))) :=
      measurable_const.mul ((measurable_id.pow_const _).ennreal_ofReal)
    have hI_pre : ∫⁻ s in Ioc s_r s_c, F_int s ≤
        (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) *
          ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-(p_k + 1)))) * K_norm := by
      calc ∫⁻ s in Ioc s_r s_c, F_int s
          ≤ ∫⁻ s in Ioc s_r s_c,
              (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) *
                ENNReal.ofReal (s ^ (-(p_k + 1)))) * K_norm := by
            refine setLIntegral_mono' measurableSet_Ioc fun s hs => hpt_pre s hs.1 hs.2
        _ ≤ ∫⁻ s in Ioi s_r,
              (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) *
                ENNReal.ofReal (s ^ (-(p_k + 1)))) * K_norm :=
            lintegral_mono_set Ioc_subset_Ioi_self
        _ = (∫⁻ s in Ioi s_r,
              ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) *
                ENNReal.ofReal (s ^ (-(p_k + 1)))) * K_norm :=
            lintegral_mul_const K_norm hmeas_pre
        _ = (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ 2 * r) *
              ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-(p_k + 1)))) * K_norm := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_Ioi_ofReal_rpow hsr_pos (by linarith only [hp_gt] : 1 < p_k + 1)] at hI_pre
    have hI_pre_bd : ∫⁻ s in Ioc s_r s_c, F_int s ≤
        ENNReal.ofReal (16 * C_kin * C_tr * S_base) * K_norm := by
      refine hI_pre.trans (mul_le_mul_of_nonneg_right ?_ bot_le)
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [show p_k + 1 - 1 = p_k by ring, hS_base_eq]
      have hp_pos : 0 < p_k := by linarith only [hp_gt]
      have hp_ge1 : 1 ≤ p_k := by linarith only [hp_gt]
      have hp_le3 : p_k ≤ 3 := by linarith only [hp_lt]
      have hdiv_le : (s_r⁻¹) ^ p_k / p_k ≤ (s_r⁻¹) ^ p_k :=
        div_le_self (Real.rpow_nonneg (inv_nonneg.2 hsr_pos.le) _) hp_ge1
      have hsr_pow : (s_r⁻¹) ^ p_k ≤ 8 * ν ^ (2 * p_k) * r ^ p_k := by
        calc (s_r⁻¹) ^ p_k
            ≤ (2 * ν ^ 2 * r) ^ p_k :=
              Real.rpow_le_rpow (inv_nonneg.2 hsr_pos.le) hsr_inv hp_pos.le
          _ = 2 ^ p_k * (ν ^ 2) ^ p_k * r ^ p_k := by
              rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by norm_num) (sq_nonneg ν)]
          _ ≤ 8 * (ν ^ 2) ^ p_k * r ^ p_k := by
              have h2_pow : (2 : ℝ) ^ p_k ≤ 8 := by
                calc (2 : ℝ) ^ p_k ≤ (2 : ℝ) ^ (3 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) hp_le3
                  _ = 8 := by norm_num
              gcongr
          _ = 8 * ν ^ (2 * p_k) * r ^ p_k := by
              congr 2
              rw [← Real.rpow_natCast ν 2, ← Real.rpow_mul hν_pos.le]
              congr 1
      have hcomb : ν ^ 2 * r * (ν ^ (2 * p_k) * r ^ p_k) = ν ^ (2 + 2 * p_k) * r ^ (p_k + 1) := by
        have h1 : ν ^ 2 * ν ^ (2 * p_k) = ν ^ (2 + 2 * p_k) := by
          rw [← Real.rpow_natCast ν 2, ← Real.rpow_add hν_pos]; push_cast; rfl
        have h2 : r * r ^ p_k = r ^ (p_k + 1) := by
          rw [Real.rpow_add hr p_k 1, Real.rpow_one, mul_comm]
        calc ν ^ 2 * r * (ν ^ (2 * p_k) * r ^ p_k)
            = (ν ^ 2 * ν ^ (2 * p_k)) * (r * r ^ p_k) := by ring
          _ = ν ^ (2 + 2 * p_k) * r ^ (p_k + 1) := by rw [h1, h2]
      calc 2 * C_kin * C_tr * ν ^ 2 * r * ((s_r⁻¹) ^ p_k / p_k)
          ≤ 2 * C_kin * C_tr * ν ^ 2 * r * (8 * ν ^ (2 * p_k) * r ^ p_k) :=
            mul_le_mul_of_nonneg_left (hdiv_le.trans hsr_pow) (by positivity)
        _ = 16 * C_kin * C_tr * (ν ^ 2 * r * (ν ^ (2 * p_k) * r ^ p_k)) := by ring
        _ = 16 * C_kin * C_tr * (ν ^ (2 + 2 * p_k) * r ^ (p_k + 1)) := by rw [hcomb]
    -- Sub-integral 2b: post-overlap `Ioi s_c`
    have hmeas_post : Measurable (fun s : ℝ =>
        ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
          ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) :=
      measurable_const.mul ((measurable_id.pow_const _).ennreal_ofReal)
    have hs_gt_sr_of_sc : ∀ s : ℝ, s_c < s → s_r < s :=
      fun _ hs => (hr_gt_imp hr_gt).trans hs
    have hI_post : ∫⁻ s in Ioi s_c, F_int s ≤
        (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
          ∫⁻ s in Ioi s_c, ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
      calc ∫⁻ s in Ioi s_c, F_int s
          ≤ ∫⁻ s in Ioi s_c,
              (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
                ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
            refine setLIntegral_mono' measurableSet_Ioi fun s hs =>
              hpt_post s (hs_gt_sr_of_sc s hs) hs.le
        _ = (∫⁻ s in Ioi s_c,
              ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
                ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm :=
            lintegral_mul_const K_norm hmeas_post
        _ = (ENNReal.ofReal (2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r) *
              ∫⁻ s in Ioi s_c, ENNReal.ofReal (s ^ (-(p_k + 3 / 4)))) * K_norm := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [lintegral_Ioi_ofReal_rpow hsc_pos (by linarith only [hp_gt] : 1 < p_k + 3 / 4)] at hI_post
    have hI_post_bd : ∫⁻ s in Ioi s_c, F_int s ≤
        ENNReal.ofReal (8 * C_kin * C_tr * S_base) * K_norm := by
      refine hI_post.trans (mul_le_mul_of_nonneg_right ?_ bot_le)
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [show p_k + 3 / 4 - 1 = p_k - 1 / 4 by ring, hS_base_eq]
      have hq_pos : 0 < p_k - 1 / 4 := by linarith only [hp_gt]
      have hq_ge1 : 1 ≤ p_k - 1 / 4 := by linarith only [hp_gt]
      have hq_le2 : p_k - 1 / 4 ≤ 2 := by linarith only [hp_lt]
      have hp_pos : 0 < p_k := by linarith only [hp_gt]
      have hdiv_le : (s_c⁻¹) ^ (p_k - 1 / 4) / (p_k - 1 / 4) ≤ (s_c⁻¹) ^ (p_k - 1 / 4) :=
        div_le_self (Real.rpow_nonneg (inv_nonneg.2 hsc_pos.le) _) hq_ge1
      have hsc_pow : (s_c⁻¹) ^ (p_k - 1 / 4) ≤ 4 * ν ^ (5 * p_k - 5 / 4) := by
        calc (s_c⁻¹) ^ (p_k - 1 / 4)
            ≤ (2 * ν ^ 5) ^ (p_k - 1 / 4) :=
              Real.rpow_le_rpow (inv_nonneg.2 hsc_pos.le) hsc_inv hq_pos.le
          _ = 2 ^ (p_k - 1 / 4) * (ν ^ 5) ^ (p_k - 1 / 4) :=
              Real.mul_rpow (by norm_num) (pow_nonneg hν_pos.le 5)
          _ ≤ 4 * (ν ^ 5) ^ (p_k - 1 / 4) := by
              have h2_pow : (2 : ℝ) ^ (p_k - 1 / 4) ≤ 4 := by
                calc (2 : ℝ) ^ (p_k - 1 / 4) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq_le2
                  _ = 4 := by norm_num
              gcongr
          _ = 4 * ν ^ (5 * p_k - 5 / 4) := by
              congr 1
              rw [← Real.rpow_natCast ν 5, ← Real.rpow_mul hν_pos.le]
              congr 1; push_cast; ring
      have hν_split : ν ^ (13 / 4 : ℝ) * ν ^ (5 * p_k - 5 / 4) =
          ν ^ (2 + 2 * p_k) * (ν ^ 3) ^ p_k := by
        rw [← Real.rpow_add hν_pos, ← Real.rpow_natCast ν 3, ← Real.rpow_mul hν_pos.le,
          ← Real.rpow_add hν_pos]
        congr 1; push_cast; ring
      have hr_pow : (ν ^ 3) ^ p_k * r ≤ r ^ (p_k + 1) := by
        have h1 : (ν ^ 3) ^ p_k ≤ r ^ p_k :=
          Real.rpow_le_rpow (pow_nonneg hν_pos.le 3) hr_gt.le hp_pos.le
        have h2 : r ^ p_k * r = r ^ (p_k + 1) := by
          rw [Real.rpow_add hr p_k 1, Real.rpow_one]
        calc (ν ^ 3) ^ p_k * r ≤ r ^ p_k * r := mul_le_mul_of_nonneg_right h1 hr.le
          _ = r ^ (p_k + 1) := h2
      calc 2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r * ((s_c⁻¹) ^ (p_k - 1 / 4) / (p_k - 1 / 4))
          ≤ 2 * C_kin * C_tr * ν ^ (13 / 4 : ℝ) * r * (4 * ν ^ (5 * p_k - 5 / 4)) :=
            mul_le_mul_of_nonneg_left (hdiv_le.trans hsc_pow) (by positivity)
        _ = 8 * C_kin * C_tr * ((ν ^ (13 / 4 : ℝ) * ν ^ (5 * p_k - 5 / 4)) * r) := by ring
        _ = 8 * C_kin * C_tr * (ν ^ (2 + 2 * p_k) * ((ν ^ 3) ^ p_k * r)) := by
            rw [hν_split]; ring
        _ ≤ 8 * C_kin * C_tr * (ν ^ (2 + 2 * p_k) * r ^ (p_k + 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hr_pow (by positivity)) (by positivity)
    -- Combine Sub-integrals 2a and 2b
    calc ∫⁻ s in Ioi s_r, F_int s
        ≤ (∫⁻ s in Ioc s_r s_c, F_int s) + (∫⁻ s in Ioi s_c, F_int s) := hsplit
      _ ≤ ENNReal.ofReal (16 * C_kin * C_tr * S_base) * K_norm +
            ENNReal.ofReal (8 * C_kin * C_tr * S_base) * K_norm :=
          add_le_add hI_pre_bd hI_post_bd
      _ = (ENNReal.ofReal (16 * C_kin * C_tr * S_base) +
            ENNReal.ofReal (8 * C_kin * C_tr * S_base)) * K_norm := (add_mul _ _ _).symm
      _ = ENNReal.ofReal (C * S_base) * K_norm := by
          rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) hS_base_nn)
            (mul_nonneg (by positivity) hS_base_nn)]
          congr 2; dsimp [C]; ring
      _ ≤ ENNReal.ofReal (C * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k *
            r ^ (σ + 5 / 2 + (k : ℝ) / 2) * max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ))) * K_norm := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
          have h1 : 1 ≤ max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) := le_max_left _ _
          have h2 : C * S_base ≤ C * S_base * max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) :=
            le_mul_of_one_le_right (mul_nonneg hC_pos.le hS_base_nn) h1
          calc C * S_base
              ≤ C * S_base * max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) := h2
            _ = C * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k *
                  r ^ (σ + 5 / 2 + (k : ℝ) / 2) * max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) := by
                dsimp [S_base]; ring

end UnforcedLeray.Short.IIIa.T22Sub
