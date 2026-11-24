import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetL2Bridge
import UnforcedLeray.Short.PartI.Sub.PartI_T09.TrainPeriodAsymptotics
import UnforcedLeray.Units.B0155
import UnforcedLeray.Lib.Gaussian.LpNorm

/-!
# `PartI:T11`: overlap rescaling of the train equation and initial `H^N` bound

Source of record: `the November 2 reference manuscript`, lines 379-382
("At overlap, `U = c³ v` solves `U_T + e_c U·∇U + ∇Π = ΔU` on the unit cylinder, and
`(sct:comparison)` gives `‖U(0)‖_{H^N} ≤ C_N`").

* **Part (i)** (`overlap_equation_of_trainSol`, and the first two conjuncts of
  `overlap_rescaled_equation_and_datum`): for `tr : B0140.TrainSol ν c` with `0 < ν` and `1 < c`,
  the overlap-rescaled field `U = overlapField ν c tr.v`, pressure `P = B0155.ovPi ν c tr.p`
  (`∇P = (c⁵/ν)∇p`) and stream `Ψ = B0155.ovPsi ν c tr.ψ` satisfy `B0155.IsOverlapSol (eC ν c) 0 U P Ψ`
  on the unit cylinder and the pointwise momentum equation
  `deriv (fun t => U t y) T + eC ν c • Train.advection (U T) y + Train.gradS (P T) y = Train.vecLaplacian (U T) y`
  for every `T ≥ 0` and `y : Plane`.
* **Part (ii)** (`overlap_datum_bound_j`, and the third conjunct of
  `overlap_rescaled_equation_and_datum`): under the dilation `(scaleField c f) y = c³ • f(c • y)`,
  `Train.jet j (scaleField c f) y = (c³ c^j) • Train.jet j f (c • y)` (`jet_scaleField`),
  `B0277.supNormD j (scaleField c f) ≤ ofReal (c³ c^j) * B0277.supNormD j f` (`supNormD_scaleField_le`),
  and `Train.cellL2 1 (Train.jet j (scaleField c f)) = ofReal (c² c^j) * Train.cellL2 c (Train.jet j f)`
  (`cellL2_jet_scaleField`). At `T = 0`, `s = s_c = B0146.overlapAge ν c` has `width ν s_c = c²`;
  decomposing `tr.v s_c = (tr.v s_c - Vc ν c s_c) + Vc ν c s_c` and combining
  `trainComparison_proof` (`PartI:T10`) with `Train.Vc_bounds j 1` yields uniform `cellL2 1` and
  `supNormD` bounds on `U 0` for all `j ≤ N`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 Vc width)

/-! ### 1. Identification of `overlapField` with `B0155.ovU` and the rescaled equation -/

/-- `eC ν c` is `B0155.coeff ν c`. -/
theorem eC_eq_coeff (ν c : ℝ) : eC ν c = B0155.coeff ν c := rfl

/-- `B0146.overlapAge ν c` is `B0155.age ν c`. -/
theorem overlapAge_eq_age (ν c : ℝ) : B0146.overlapAge ν c = B0155.age ν c := rfl

/-- `overlapField ν c v` is `B0155.ovU ν c v`. -/
theorem overlapField_eq_ovU (ν c : ℝ) (v : ℝ → Plane → Vec) :
    overlapField ν c v = B0155.ovU ν c v := by
  funext T y
  simp only [overlapField, B0155.ovU, B0155.ageOf, B0146.overlapAge, B0155.age, B0155.dil_eq_smul]
  congr 2
  ring

/-- At `T = 0`, the overlap field evaluates `c³ • v s_c (c • y)` at `s_c = B0146.overlapAge ν c`. -/
theorem overlapField_zero (ν c : ℝ) (v : ℝ → Plane → Vec) (y : Plane) :
    overlapField ν c v 0 y = c ^ 3 • v (B0146.overlapAge ν c) (c • y) := by
  simp [overlapField]

/-- **Part (i): the overlap-rescaled equation on the unit cylinder** (source lines 379-381).
For `0 < ν` and `1 < c`, `U = overlapField ν c tr.v` and `P = B0155.ovPi ν c tr.p` form an overlap
solution on `[0, ∞)` and satisfy `U_T + e_c (U·∇)U + ∇P = ΔU` for all `T ≥ 0`. -/
theorem overlap_equation_of_trainSol {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) :
    B0155.IsOverlapSol (eC ν c) 0 (overlapField ν c tr.v)
      (B0155.ovPi ν c tr.p) (B0155.ovPsi ν c tr.ψ) ∧
    ∀ T : ℝ, 0 ≤ T → ∀ y : Plane,
      deriv (fun t => overlapField ν c tr.v t y) T +
        eC ν c • Train.advection (overlapField ν c tr.v T) y +
        Train.gradS (B0155.ovPi ν c tr.p T) y =
        Train.vecLaplacian (overlapField ν c tr.v T) y := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hc1 : 1 ≤ c := hc.le
  rw [overlapField_eq_ovU, eC_eq_coeff]
  refine ⟨B0155.isOverlapSol_zero_of_isTrain hν hc1 tr.isTrain, fun T hT y => ?_⟩
  have hT0 : B0155.ovTime ν c 0 < T := (B0155.ovTime_zero_neg hν.ne' hc).trans_le hT
  have hres := (B0155.isOverlapSol_of_isTrain hν hc0 tr.isTrain).momentum T hT0 y
  exact (B0155.periodOneResidual_eq_zero_iff _ _ _ T y).1 hres

/-! ### 2. Scaling of `Train.jet`, `B0277.supNormD` and `Train.cellL2` under `y ↦ c • y` -/

/-- Spatial overlap scaling `(scaleField c f) y = c³ • f (c • y)`. -/
def scaleField (c : ℝ) (f : Plane → Vec) (y : Plane) : Vec :=
  c ^ 3 • f (c • y)

theorem overlapField_zero_eq_scaleField (ν c : ℝ) (v : ℝ → Plane → Vec) :
    overlapField ν c v 0 = scaleField c (v (B0146.overlapAge ν c)) := by
  funext y
  exact overlapField_zero ν c v y

/-- Scaling of `Train.jet`: `D^j (c³ f(c ·))(y) = (c³ c^j) (D^j f)(c • y)`. -/
theorem jet_scaleField (j : ℕ) (c : ℝ) (f : Plane → Vec) (y : Plane) :
    jet j (scaleField c f) y = (c ^ 3 * c ^ j) • jet j f (c • y) :=
  UnforcedLeray.Gaussian.iteratedFDeriv_comp_smul j f (c ^ 3) c y

/-- Scaling of `B0277.supNormD` under `scaleField c`. -/
theorem supNormD_scaleField_le {c : ℝ} (hc : 0 ≤ c) (j : ℕ) (f : Plane → Vec) :
    B0277.supNormD j (scaleField c f) ≤ ENNReal.ofReal (c ^ 3 * c ^ j) * B0277.supNormD j f := by
  unfold B0277.supNormD
  apply iSup_le
  intro y
  have hpt : iteratedFDeriv ℝ j (scaleField c f) y =
      (c ^ 3 * c ^ j) • iteratedFDeriv ℝ j f (c • y) :=
    jet_scaleField j c f y
  rw [hpt, enorm_smul, Real.enorm_eq_ofReal (by positivity)]
  have hle : ‖iteratedFDeriv ℝ j f (c • y)‖ₑ ≤ ⨆ z : Plane, ‖iteratedFDeriv ℝ j f z‖ₑ :=
    le_iSup (fun z : Plane => ‖iteratedFDeriv ℝ j f z‖ₑ) (c • y)
  gcongr

/-- Dilation of `cellL2` from the unit cell to the period-`c` cell:
`cellL2 1 (fun y => F (c • y)) = c⁻¹ * cellL2 c F` for `c > 0` and continuous `F`. -/
theorem cellL2_one_comp_smul {E : Type*} [NormedAddCommGroup E] {c : ℝ} (hc : 0 < c)
    {F : Plane → E} (hF : Continuous F) :
    cellL2 1 (fun y => F (c • y)) = ENNReal.ofReal c⁻¹ * cellL2 c F := by
  let G : Plane → E := (Cyl.cell c).indicator F
  have hind : (Cyl.cell 1).indicator (fun y => F (c • y)) = G ∘ (fun y : Plane => c • y) := by
    funext y
    by_cases hy : y ∈ Cyl.cell 1
    · have hyc : c • y ∈ Cyl.cell c := (B0155.dil_mem_cell_iff hc y).2 hy
      simp [G, hy, hyc]
    · have hyc : c • y ∉ Cyl.cell c := fun h => hy ((B0155.dil_mem_cell_iff hc y).1 h)
      simp [G, hy, hyc]
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure Plane)) hc.ne'
  have hm : AEMeasurable (fun y : Plane => c • y) volume :=
    (continuous_const_smul c).aemeasurable
  have hG : AEStronglyMeasurable G (Measure.map (fun y : Plane => c • y) volume) :=
    hF.aestronglyMeasurable.indicator (Cyl.measurableSet_cell c)
  have hrank : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have hne : ENNReal.ofReal |(c ^ Module.finrank ℝ Plane)⁻¹| ≠ 0 := by
    rw [hrank]; simp [hc.ne']
  unfold cellL2 Cyl.cellμ
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (Cyl.measurableSet_cell 1),
    ← eLpNorm_indicator_eq_eLpNorm_restrict (Cyl.measurableSet_cell c), hind,
    ← eLpNorm_map_measure hG hm, hmap,
    eLpNorm_smul_measure_of_ne_zero hne, smul_eq_mul, hrank]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by positivity),
    abs_of_pos (by positivity)]
  congr 1
  have hpow : ((c ^ 2)⁻¹ : ℝ) = (c⁻¹) ^ (2 : ℝ) := by
    rw [← inv_pow, Real.rpow_two]
  rw [hpow, ← Real.rpow_mul (inv_nonneg.2 hc.le)]
  norm_num

/-- Scaling of `cellL2 1 (jet j (scaleField c f))` for smooth `f`:
`cellL2 1 (jet j (scaleField c f)) = ofReal (c² c^j) * cellL2 c (jet j f)`. -/
theorem cellL2_jet_scaleField {c : ℝ} (hc : 0 < c) (j : ℕ) {f : Plane → Vec}
    (hf : ContDiff ℝ ∞ f) :
    cellL2 1 (jet j (scaleField c f)) = ENNReal.ofReal (c ^ 2 * c ^ j) * cellL2 c (jet j f) := by
  have hnorm : (fun y : Plane => ‖jet j (scaleField c f) y‖) =
      (c ^ 3 * c ^ j) • (fun y : Plane => ‖jet j f (c • y)‖) := by
    funext y
    rw [jet_scaleField, norm_smul, Real.norm_of_nonneg (by positivity), Pi.smul_apply, smul_eq_mul]
  have hcont : Continuous (fun z : Plane => ‖jet j f z‖) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  unfold cellL2
  rw [← eLpNorm_norm (jet j (scaleField c f)), ← eLpNorm_norm (jet j f), hnorm,
    eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
  change ENNReal.ofReal (c ^ 3 * c ^ j) * cellL2 1 (fun y => ‖jet j f (c • y)‖) = _
  rw [cellL2_one_comp_smul hc hcont]
  unfold cellL2
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hc0 : c ≠ 0 := hc.ne'
  field_simp

/-! ### 3. Bounds for the isolated vortex part and the comparison error at `s_c` -/

/-- At `s_c = B0146.overlapAge ν c`, `width ν s_c = c²` for `ν ≠ 0`. -/
theorem width_overlapAge {ν c : ℝ} (hν : ν ≠ 0) :
    width ν (B0146.overlapAge ν c) = c ^ 2 := by
  unfold width B0146.overlapAge
  field_simp
  ring

theorem overlapAge_nonneg {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) :
    0 ≤ B0146.overlapAge ν c := by
  unfold B0146.overlapAge
  exact div_nonneg (by nlinarith) hν.le

/-- The function `y ↦ (1 + y.2 ^ 2)⁻¹` belongs to `L²(Cyl.cellμ 1)`. -/
private theorem inv_one_add_sq_memLp_unit_cell :
    MemLp (fun y : Plane => (1 + y.2 ^ 2)⁻¹) 2 (Cyl.cellμ 1) := by
  have hφ : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · have hc : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
        Continuous.inv₀ (by fun_prop) (fun x => by positivity)
      exact (hc.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      have h1 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [show 0 ≤ (1 + x ^ 2)⁻¹ by positivity]
  have hcont : Continuous (fun y : Plane => (1 + y.2 ^ 2)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun y => by positivity)
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  rw [Cyl.cellμ_eq_prod]
  have : IsFiniteMeasure (volume.restrict (Set.Ico (-1 / 2 : ℝ) (1 / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  exact hφ.comp_snd _

/-- Uniform `cellL2 1` and `supNormD` bounds for the rescaled isolated vortex
`scaleField c (Vc ν c s_c)` at the overlap age `s_c = B0146.overlapAge ν c`. -/
theorem overlap_Vc_bound (j : ℕ) :
    ∃ CV : ℝ, 0 < CV ∧
      ∀ ν c : ℝ, 0 < ν → 1 ≤ c →
        let s_c := B0146.overlapAge ν c
        cellL2 1 (jet j (scaleField c (Vc ν c s_c))) ≤ ENNReal.ofReal CV ∧
        B0277.supNormD j (scaleField c (Vc ν c s_c)) ≤ ENNReal.ofReal CV := by
  obtain ⟨C, _, hC, _, hVc⟩ := Train.Vc_bounds j 1
  let W₀ : ℝ := (eLpNorm (fun y : Plane => (1 + y.2 ^ 2)⁻¹) 2 (Cyl.cellμ 1)).toReal
  have hW₀_nn : 0 ≤ W₀ := ENNReal.toReal_nonneg
  have hW₀_eq : eLpNorm (fun y : Plane => (1 + y.2 ^ 2)⁻¹) 2 (Cyl.cellμ 1) = ENNReal.ofReal W₀ :=
    (ENNReal.ofReal_toReal inv_one_add_sq_memLp_unit_cell.eLpNorm_lt_top.ne).symm
  let K : ℝ := 2 * 2 ^ j * C
  have hK_nn : 0 ≤ K := by positivity
  refine ⟨1 + K + K * W₀, by positivity, fun ν c hν hc => ?_⟩
  intro s_c
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hw_eq : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
  have ha1 : 1 ≤ width ν s_c := by rw [hw_eq]; nlinarith
  have hac : width ν s_c ≤ c ^ 2 := hw_eq.le
  have ha0 : 0 < width ν s_c := zero_lt_one.trans_le ha1
  have hV_sm : ContDiff ℝ ∞ (Vc ν c s_c) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 ha0
  -- Pointwise bound `‖jet j (scaleField c (Vc ν c s_c)) y‖ ≤ K * (1 + y.2 ^ 2)⁻¹`.
  have hpt : ∀ y : Plane,
      ‖jet j (scaleField c (Vc ν c s_c)) y‖ ≤ K * (1 + y.2 ^ 2)⁻¹ := by
    intro y
    rw [jet_scaleField, norm_smul, Real.norm_of_nonneg (by positivity)]
    have hpow : (width ν s_c) ^ (-(3 + (j : ℝ)) / 2) = (c ^ 3 * c ^ j)⁻¹ := by
      rw [hw_eq, ← Real.rpow_natCast c 2, ← Real.rpow_mul hc0.le]
      have he : ((2 : ℕ) : ℝ) * (-(3 + (j : ℝ)) / 2) = -((3 + j : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_neg hc0.le, Real.rpow_natCast, pow_add]
    have hword : ∀ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
        c ^ 3 * c ^ j * |wordComp i.1 (Vc ν c s_c) i.2 (c • y)| ≤ C * (1 + y.2 ^ 2)⁻¹ := by
      intro i hi
      rw [Finset.mem_product] at hi
      have hlen : i.1.length = j := by
        unfold wordsOfLength at hi
        rcases Finset.mem_image.1 hi.1 with ⟨u, _, hiu⟩
        rw [← hiu]
        simp
      have hz := (hVc ν c s_c hc0 ha1 hac).1 i.1 hlen i.2 (c • y)
      have hwt : (1 + (c • y).2 ^ 2 / width ν s_c) ^ 1 = 1 + y.2 ^ 2 := by
        rw [pow_one, hw_eq]
        change 1 + (c * y.2) ^ 2 / c ^ 2 = 1 + y.2 ^ 2
        have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0.ne'
        rw [mul_pow, mul_div_cancel_left₀ _ hc2]
      rw [hwt, hpow] at hz
      have hp1 : 0 < 1 + y.2 ^ 2 := by positivity
      have hc3j : 0 < c ^ 3 * c ^ j := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ hp1]
      calc c ^ 3 * c ^ j * |wordComp i.1 (Vc ν c s_c) i.2 (c • y)| * (1 + y.2 ^ 2)
          = (c ^ 3 * c ^ j) * ((1 + y.2 ^ 2) * |wordComp i.1 (Vc ν c s_c) i.2 (c • y)|) := by ring
        _ ≤ (c ^ 3 * c ^ j) * (C * (c ^ 3 * c ^ j)⁻¹) :=
            mul_le_mul_of_nonneg_left hz hc3j.le
        _ = C := by field_simp
    have hcard : ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) ≤ 2 * 2 ^ j := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have hW : (wordsOfLength j).card ≤ 2 ^ j := by
        unfold wordsOfLength
        calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
          _ = 2 ^ j := by simp
      have hW' : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by exact_mod_cast hW
      push_cast; linarith
    calc c ^ 3 * c ^ j * ‖jet j (Vc ν c s_c) (c • y)‖
        ≤ c ^ 3 * c ^ j *
            ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
              |wordComp i.1 (Vc ν c s_c) i.2 (c • y)| :=
          mul_le_mul_of_nonneg_left (jl2_pointwise j (Vc ν c s_c) hV_sm (c • y)) (by positivity)
      _ = ∑ i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)),
            c ^ 3 * c ^ j * |wordComp i.1 (Vc ν c s_c) i.2 (c • y)| := Finset.mul_sum _ _ _
      _ ≤ ∑ _i ∈ wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2)), C * (1 + y.2 ^ 2)⁻¹ :=
          Finset.sum_le_sum hword
      _ = ((wordsOfLength j ×ˢ (Finset.univ : Finset (Fin 2))).card : ℝ) *
            (C * (1 + y.2 ^ 2)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * 2 ^ j) * (C * (1 + y.2 ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K * (1 + y.2 ^ 2)⁻¹ := by ring
  refine ⟨?_, ?_⟩
  · -- `cellL2 1` bound
    have hmono : cellL2 1 (jet j (scaleField c (Vc ν c s_c))) ≤
        eLpNorm (K • fun y : Plane => (1 + y.2 ^ 2)⁻¹) 2 (Cyl.cellμ 1) := by
      apply eLpNorm_mono_enorm
      intro y
      have hy : 0 ≤ K * (1 + y.2 ^ 2)⁻¹ := by positivity
      rw [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal hy, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hpt y)
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hK_nn, hW₀_eq,
      ← ENNReal.ofReal_mul hK_nn] at hmono
    exact hmono.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · -- `supNormD` bound
    unfold B0277.supNormD
    apply iSup_le
    intro y
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 + y.2 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg y.2])
    have h2 : K * (1 + y.2 ^ 2)⁻¹ ≤ K * 1 := mul_le_mul_of_nonneg_left h1 hK_nn
    have h3 : ‖iteratedFDeriv ℝ j (scaleField c (Vc ν c s_c)) y‖ ≤ K * (1 + y.2 ^ 2)⁻¹ := hpt y
    linarith [mul_nonneg hK_nn hW₀_nn]

/-- Single-order `j` initial bound on `overlapField ν (trainPeriod ρ ν) tr.v 0` at `T = 0`,
combining `trainComparison_proof` (`PartI:T10`) and `overlap_Vc_bound`. -/
theorem overlap_datum_bound_j (ρ : ℝ) (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          let c := trainPeriod ρ ν
          cellL2 1 (jet j (overlapField ν c tr.v 0)) ≤ ENNReal.ofReal C ∧
          B0277.supNormD j (overlapField ν c tr.v 0) ≤ ENNReal.ofReal C := by
  obtain ⟨Ce, be, νe, hCe, hbe, hνe, hcomp⟩ := trainComparison_proof ρ hρ j
  obtain ⟨CV, hCV, hVc⟩ := overlap_Vc_bound j
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
  refine ⟨Ce + CV, min νe νp, add_pos hCe hCV, lt_min hνe hνp, fun ν hν hν₀ tr hBUC => ?_⟩
  intro c
  have hν_e : ν ≤ νe := hν₀.trans (min_le_left _ _)
  have hν_p : ν ≤ νp := hν₀.trans (min_le_right _ _)
  obtain ⟨hc1, hνc2⟩ := hp ν hν hν_p
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let s_c := B0146.overlapAge ν c
  have hs_c : 0 ≤ s_c := overlapAge_nonneg hν hc1
  have hw_eq : width ν s_c = c ^ 2 := width_overlapAge hν.ne'
  have ⟨hL2_e, hSup_e⟩ := hcomp ν hν hν_e tr hBUC s_c hs_c hw_eq.le
  have ⟨hL2_V, hSup_V⟩ := hVc ν c hν hc1
  -- Smoothness of `tr.v s_c`, `Vc ν c s_c`, and their difference.
  have hv_sm : ContDiff ℝ ∞ (tr.v s_c) := by
    have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
      (fun z _ => ⟨mem_Ici.2 hs_c, mem_univ z⟩)
    exact contDiffOn_univ.1 h
  have hV_sm : ContDiff ℝ ∞ (Vc ν c s_c) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 (by rw [hw_eq]; positivity)
  let err : Plane → Vec := fun z => tr.v s_c z - Vc ν c s_c z
  have herr_sm : ContDiff ℝ ∞ err := hv_sm.sub hV_sm
  have hU_eq : overlapField ν c tr.v 0 =
      fun y => scaleField c err y + scaleField c (Vc ν c s_c) y := by
    funext y
    rw [overlapField_zero_eq_scaleField]
    simp [scaleField, err, smul_sub, sub_add_cancel, s_c]
  have hs_err_sm : ContDiff ℝ ∞ (scaleField c err) :=
    (herr_sm.comp (contDiff_id.const_smul c)).const_smul (c ^ 3)
  have hs_V_sm : ContDiff ℝ ∞ (scaleField c (Vc ν c s_c)) :=
    (hV_sm.comp (contDiff_id.const_smul c)).const_smul (c ^ 3)
  have hj_top : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hjet_add : jet j (overlapField ν c tr.v 0) =
      fun y => jet j (scaleField c err) y + jet j (scaleField c (Vc ν c s_c)) y := by
    funext y
    rw [hU_eq]
    exact iteratedFDeriv_add_apply (hs_err_sm.contDiffAt.of_le hj_top)
      (hs_V_sm.contDiffAt.of_le hj_top)
  -- Rescaled error bounds: `c² c^j * (ν⁻¹ (c²)^{-(2+j/2)} e^{-b}) ≤ 1` and
  -- `c³ c^j * (ν⁻¹ (c²)^{-(5+j)/2} e^{-b}) ≤ 1`.
  have hexp_le : Real.exp (-(be * c ^ 2 / width ν s_c)) ≤ 1 := by
    rw [hw_eq, mul_div_cancel_right₀ _ (pow_ne_zero 2 hc0.ne')]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hec_le : (ν * c ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hrpow_L2 : c ^ 2 * c ^ j * (width ν s_c) ^ (-(2 + (j : ℝ) / 2)) = (c ^ 2)⁻¹ := by
    rw [hw_eq, ← Real.rpow_natCast c 2, ← Real.rpow_mul hc0.le]
    have he : ((2 : ℕ) : ℝ) * (-(2 + (j : ℝ) / 2)) = -((4 + j : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_neg hc0.le, Real.rpow_natCast, Real.rpow_natCast,
      show 4 + j = 2 + (2 + j) by omega, pow_add, pow_add]
    have hc_ne : c ≠ 0 := hc0.ne'
    field_simp
  have hrpow_Sup : c ^ 3 * c ^ j * (width ν s_c) ^ (-((5 + (j : ℝ)) / 2)) = (c ^ 2)⁻¹ := by
    rw [hw_eq, ← Real.rpow_natCast c 2, ← Real.rpow_mul hc0.le]
    have he : ((2 : ℕ) : ℝ) * (-((5 + (j : ℝ)) / 2)) = -((5 + j : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_neg hc0.le, Real.rpow_natCast, Real.rpow_natCast,
      show 5 + j = 2 + (3 + j) by omega, pow_add, pow_add]
    have hc_ne : c ≠ 0 := hc0.ne'
    field_simp
  have hL2_err_scaled : cellL2 1 (jet j (scaleField c err)) ≤ ENNReal.ofReal Ce := by
    rw [cellL2_jet_scaleField hc0 j herr_sm]
    calc ENNReal.ofReal (c ^ 2 * c ^ j) * cellL2 c (jet j err)
        ≤ ENNReal.ofReal (c ^ 2 * c ^ j) *
            ENNReal.ofReal (Ce * ν⁻¹ * width ν s_c ^ (-(2 + (j : ℝ) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s_c))) := by gcongr
      _ = ENNReal.ofReal (c ^ 2 * c ^ j *
            (Ce * ν⁻¹ * width ν s_c ^ (-(2 + (j : ℝ) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s_c)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal Ce := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : c ^ 2 * c ^ j *
              (Ce * ν⁻¹ * width ν s_c ^ (-(2 + (j : ℝ) / 2)) *
                Real.exp (-(be * c ^ 2 / width ν s_c))) =
              Ce * ((ν * c ^ 2)⁻¹ * Real.exp (-(be * c ^ 2 / width ν s_c))) := by
            calc _ = Ce * ν⁻¹ * (c ^ 2 * c ^ j * width ν s_c ^ (-(2 + (j : ℝ) / 2))) *
                  Real.exp (-(be * c ^ 2 / width ν s_c)) := by ring
              _ = Ce * ((ν * c ^ 2)⁻¹ * Real.exp (-(be * c ^ 2 / width ν s_c))) := by
                  rw [hrpow_L2, mul_inv]; ring
          rw [h1]
          have hprod : (ν * c ^ 2)⁻¹ * Real.exp (-(be * c ^ 2 / width ν s_c)) ≤ 1 * 1 :=
            mul_le_mul hec_le hexp_le (Real.exp_nonneg _) zero_le_one
          nlinarith
  have hSup_err_scaled : B0277.supNormD j (scaleField c err) ≤ ENNReal.ofReal Ce := by
    calc B0277.supNormD j (scaleField c err)
        ≤ ENNReal.ofReal (c ^ 3 * c ^ j) * B0277.supNormD j err :=
          supNormD_scaleField_le hc0.le j err
      _ ≤ ENNReal.ofReal (c ^ 3 * c ^ j) *
            ENNReal.ofReal (Ce * ν⁻¹ * width ν s_c ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s_c))) := by gcongr
      _ = ENNReal.ofReal (c ^ 3 * c ^ j *
            (Ce * ν⁻¹ * width ν s_c ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(be * c ^ 2 / width ν s_c)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal Ce := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : c ^ 3 * c ^ j *
              (Ce * ν⁻¹ * width ν s_c ^ (-((5 + (j : ℝ)) / 2)) *
                Real.exp (-(be * c ^ 2 / width ν s_c))) =
              Ce * ((ν * c ^ 2)⁻¹ * Real.exp (-(be * c ^ 2 / width ν s_c))) := by
            calc _ = Ce * ν⁻¹ * (c ^ 3 * c ^ j * width ν s_c ^ (-((5 + (j : ℝ)) / 2))) *
                  Real.exp (-(be * c ^ 2 / width ν s_c)) := by ring
              _ = Ce * ((ν * c ^ 2)⁻¹ * Real.exp (-(be * c ^ 2 / width ν s_c))) := by
                  rw [hrpow_Sup, mul_inv]; ring
          rw [h1]
          have hprod : (ν * c ^ 2)⁻¹ * Real.exp (-(be * c ^ 2 / width ν s_c)) ≤ 1 * 1 :=
            mul_le_mul hec_le hexp_le (Real.exp_nonneg _) zero_le_one
          nlinarith
  refine ⟨?_, ?_⟩
  · -- Triangle inequality in `cellL2 1`
    have hm1 : AEStronglyMeasurable (jet j (scaleField c err)) (Cyl.cellμ 1) :=
      (hs_err_sm.continuous_iteratedFDeriv hj_top).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (jet j (scaleField c (Vc ν c s_c))) (Cyl.cellμ 1) :=
      (hs_V_sm.continuous_iteratedFDeriv hj_top).aestronglyMeasurable
    unfold cellL2
    rw [hjet_add, ENNReal.ofReal_add hCe.le hCV.le]
    exact (eLpNorm_add_le hm1 hm2 one_le_two).trans (add_le_add hL2_err_scaled hL2_V)
  · -- Triangle inequality in `supNormD`
    unfold B0277.supNormD
    rw [ENNReal.ofReal_add hCe.le hCV.le]
    apply iSup_le
    intro y
    have hy : iteratedFDeriv ℝ j (overlapField ν c tr.v 0) y =
        iteratedFDeriv ℝ j (scaleField c err) y +
          iteratedFDeriv ℝ j (scaleField c (Vc ν c s_c)) y :=
      congrFun hjet_add y
    rw [hy]
    calc ‖iteratedFDeriv ℝ j (scaleField c err) y +
            iteratedFDeriv ℝ j (scaleField c (Vc ν c s_c)) y‖ₑ
        ≤ ‖iteratedFDeriv ℝ j (scaleField c err) y‖ₑ +
            ‖iteratedFDeriv ℝ j (scaleField c (Vc ν c s_c)) y‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ ≤ B0277.supNormD j (scaleField c err) +
            B0277.supNormD j (scaleField c (Vc ν c s_c)) :=
          add_le_add (le_iSup (fun z => ‖iteratedFDeriv ℝ j (scaleField c err) z‖ₑ) y)
            (le_iSup (fun z => ‖iteratedFDeriv ℝ j (scaleField c (Vc ν c s_c)) z‖ₑ) y)
      _ ≤ ENNReal.ofReal Ce + ENNReal.ofReal CV := add_le_add hSup_err_scaled hSup_V

/-! ### 4. Main theorem (`PartI:T11`) -/

/-- **`PartI:T11` (`overlap_rescaled_equation_and_datum`)** (source lines 379-382):
for `c = trainPeriod ρ ν` (`1 / 2 < ρ`), `tr : B0140.TrainSol ν c` in `IsBUCTrain`, and
`U = overlapField ν c tr.v`, `P = B0155.ovPi ν c tr.p`, `Ψ = B0155.ovPsi ν c tr.ψ`:
(i) `(U, P, Ψ)` is a smooth period-1 overlap solution on `[0, ∞)` satisfying
`U_T + e_c (U·∇)U + ∇P = ΔU` with `e_c = (ν c²)⁻¹`, and
(ii) `‖U(0)‖_{H^N} ≤ C_N` in both `cellL2 1 (jet j (U 0))` and `supNormD j (U 0)` for all `j ≤ N`. -/
theorem overlap_rescaled_equation_and_datum (ρ : ℝ) (hρ : 1 / 2 < ρ) (N : ℕ) :
    ∃ C ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
          let c := trainPeriod ρ ν
          let U := overlapField ν c tr.v
          let P := B0155.ovPi ν c tr.p
          let Ψ := B0155.ovPsi ν c tr.ψ
          B0155.IsOverlapSol (eC ν c) 0 U P Ψ ∧
          (∀ T : ℝ, 0 ≤ T → ∀ y : Plane,
            deriv (fun t => U t y) T + eC ν c • Train.advection (U T) y + Train.gradS (P T) y =
              Train.vecLaplacian (U T) y) ∧
          (∀ j : ℕ, j ≤ N →
            cellL2 1 (jet j (U 0)) ≤ ENNReal.ofReal C ∧
            B0277.supNormD j (U 0) ≤ ENNReal.ofReal C) := by
  induction N with
  | zero =>
    obtain ⟨C₀, ν₀, hC₀, hν₀, h0⟩ := overlap_datum_bound_j ρ hρ 0
    obtain ⟨νp, hνp, _, _⟩ := trainPeriodAsymptotics_proof ρ hρ 2 two_pos
    refine ⟨C₀, min ν₀ (min νp (1 / 2)), hC₀, lt_min hν₀ (lt_min hνp (by norm_num)),
      fun ν hν hν_le tr hBUC => ?_⟩
    have hν_0 : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
    have hν_half : ν ≤ 1 / 2 := hν_le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hc_gt1 : 1 < trainPeriod ρ ν := by
      unfold trainPeriod
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)
    obtain ⟨hSol, hEq⟩ := overlap_equation_of_trainSol hν hc_gt1 tr
    refine ⟨hSol, hEq, fun j hj => ?_⟩
    have hj0 : j = 0 := Nat.le_zero.1 hj
    subst hj0
    exact h0 ν hν hν_0 tr hBUC
  | succ N ih =>
    obtain ⟨CN, νN, hCN, hνN, hN⟩ := ih
    obtain ⟨C1, ν1, hC1, hν1, h1⟩ := overlap_datum_bound_j ρ hρ (N + 1)
    refine ⟨max CN C1, min νN ν1, lt_max_of_lt_left hCN, lt_min hνN hν1,
      fun ν hν hν_le tr hBUC => ?_⟩
    have hν_N : ν ≤ νN := hν_le.trans (min_le_left _ _)
    have hν_1 : ν ≤ ν1 := hν_le.trans (min_le_right _ _)
    obtain ⟨hSol, hEq, hBoundN⟩ := hN ν hν hν_N tr hBUC
    refine ⟨hSol, hEq, fun j hj => ?_⟩
    rcases Nat.of_le_succ hj with hjN | rfl
    · obtain ⟨hL, hS⟩ := hBoundN j hjN
      exact ⟨hL.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
        hS.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    · obtain ⟨hL, hS⟩ := h1 ν hν hν_1 tr hBUC
      exact ⟨hL.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)),
        hS.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩

end UnforcedLeray.Short.PartI
