import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.TrainGrowth
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Short.PartIIIa.FlatCausal

/-!
# Cauchy-Schwarz on one cell for the stress readout (source 3283-3287, 4610-4612)

`SymOuterSliceProp m`: for the BUC train velocity `v = tr.v u` read through `trainMer`, and
`y ∈ X_{m,c}` read through `kcMer`,
`c⁻¹ ∫_cell |v ⊗ K_c y + K_c y ⊗ v|  ≤ 2 c⁻¹ ‖v‖_{L²(cell)} ‖K_c y‖_{L²(cell)}`.

Proof: pointwise `|a ⊗ b + b ⊗ a|_F ≤ 2|a||b|` (`frobSq_symOuter_le`), the train mer equals
`tr.v u x` for `u ≥ 0` (and is `0` for `u < 0`), `kcMer = kcLp` a.e. on the cell, then Hölder with
exponents `2, 2` on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Pointwise Frobenius bound for symmetric outer products: `|a ⊗ b + b ⊗ a|_F ≤ 2|a||b|`. -/
theorem frob_symOuter_le_aux (a b : UnforcedLeray.Axi.Merid) :
    UnforcedLeray.Short.PartIIIb.Concrete.frob (UnforcedLeray.Short.IIIa.symOuter a b) ≤
      2 * ‖a‖ * ‖b‖ := by
  have h := UnforcedLeray.Short.IIIa.frobSq_symOuter_le a b
  unfold UnforcedLeray.Short.PartIIIb.Concrete.frob
  rw [Real.sqrt_le_left (by positivity)]
  have e : (2 * ‖a‖ * ‖b‖) ^ 2 = 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring
  rw [e]
  exact h

/-- The real-to-`ℝ≥0∞` form of `2|a||b|`. -/
theorem ofReal_two_mul_norm_mul_norm (a b : UnforcedLeray.Axi.Merid) :
    ENNReal.ofReal (2 * ‖a‖ * ‖b‖) = 2 * (‖a‖ₑ * ‖b‖ₑ) := by
  rw [ENNReal.ofReal_mul (p := 2 * ‖a‖) (by positivity), ENNReal.ofReal_mul (p := 2) (by norm_num),
    ENNReal.ofReal_ofNat, ofReal_norm a, ofReal_norm b]
  ring

/-- The general one-cell Cauchy-Schwarz bound, for any period `c > 0`. -/
theorem slice_gen (m : ℝ) [Fact (1 < m)] {ν c : ℝ} [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (u : ℝ) (y : Xmc c m) :
    ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.PartIIIb.Concrete.frob
        (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x)) (kcMer y x)))
      ∂(UnforcedLeray.Cyl.avgμ c) ≤
      2 * ENNReal.ofReal c⁻¹ * UnforcedLeray.Train.cellL2 c (tr.v u) *
        ENNReal.ofReal ‖kcLp y‖ := by
  have hset : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  have hμ : UnforcedLeray.Cyl.cellμ c = UnforcedLeray.B0581.cellVol c := by
    unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.B0581.cellVol
    rw [hset]
  have hav : UnforcedLeray.Cyl.avgμ c = ENNReal.ofReal c⁻¹ • UnforcedLeray.B0581.cellVol c := by
    unfold UnforcedLeray.Cyl.avgμ
    rw [hμ]
  have hA : UnforcedLeray.Train.cellL2 c (tr.v u) =
      (∫⁻ x, ‖tr.v u x‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.B0581.cellVol c)) ^ (1 / (2 : ℝ)) := by
    unfold UnforcedLeray.Train.cellL2
    rw [hμ, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have hB : ENNReal.ofReal ‖kcLp y‖ =
      (∫⁻ x, ‖kcLp y x‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.B0581.cellVol c)) ^ (1 / (2 : ℝ)) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (kcLp y)),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  rw [hav, lintegral_smul_measure, smul_eq_mul, hA, hB]
  by_cases hu : 0 ≤ u
  · -- the train velocity at age `u ≥ 0`
    have hmer : ∀ x : (ℝ × ℝ),
        UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x) = tr.v u x := by
      intro x
      ext i
      simp [UnforcedLeray.Short.PartIIIb.NearInst.trainMer,
        UnforcedLeray.Short.IIIa.trainVel, hu]
    have hcont : Continuous (fun x : (ℝ × ℝ) => tr.v u x) := by
      have hc := tr.isTrain.smooth_v.continuousOn
      have h2 : ContinuousOn (fun x : (ℝ × ℝ) => tr.v u x) univ := by
        have hm : ∀ x ∈ (univ : Set (ℝ × ℝ)),
            ((u, x) : ℝ × (ℝ × ℝ)) ∈ Ici 0 ×ˢ univ :=
          fun x _ => ⟨Set.mem_Ici.2 hu, Set.mem_univ _⟩
        exact hc.comp (continuousOn_const.prodMk continuousOn_id) hm
      exact continuousOn_univ.1 h2
    have hv : AEMeasurable (fun x : (ℝ × ℝ) => ‖tr.v u x‖ₑ)
        (UnforcedLeray.B0581.cellVol c) :=
      (hcont.measurable.enorm).aemeasurable
    have hk : AEMeasurable (fun x : (ℝ × ℝ) => ‖kcLp y x‖ₑ)
        (UnforcedLeray.B0581.cellVol c) :=
      (Lp.aestronglyMeasurable (kcLp y)).aemeasurable.enorm
    have hpt : ∀ x : (ℝ × ℝ),
        ENNReal.ofReal (UnforcedLeray.Short.PartIIIb.Concrete.frob
          (UnforcedLeray.Short.IIIa.symOuter
            (UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x)) (kcMer y x))) ≤
        ENNReal.ofReal (2 * ‖tr.v u x‖ * ‖kcMer y x‖) := by
      intro x
      apply ENNReal.ofReal_le_ofReal
      refine (frob_symOuter_le_aux _ _).trans (le_of_eq ?_)
      rw [hmer x]
    have hae : ∫⁻ x, ENNReal.ofReal (2 * ‖tr.v u x‖ * ‖kcMer y x‖)
        ∂(UnforcedLeray.B0581.cellVol c) =
        ∫⁻ x, ENNReal.ofReal (2 * ‖tr.v u x‖ * ‖kcLp y x‖)
        ∂(UnforcedLeray.B0581.cellVol c) :=
      lintegral_congr_ae (by
        filter_upwards [kcMer_ae y] with x hx
        rw [hx])
    have hmain : ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.PartIIIb.Concrete.frob
          (UnforcedLeray.Short.IIIa.symOuter
            (UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x)) (kcMer y x)))
        ∂(UnforcedLeray.B0581.cellVol c) ≤
        2 * ((∫⁻ x, ‖tr.v u x‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.B0581.cellVol c)) ^ (1 / (2 : ℝ)) *
          (∫⁻ x, ‖kcLp y x‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.B0581.cellVol c)) ^ (1 / (2 : ℝ))) := by
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (UnforcedLeray.B0581.cellVol c)
        Real.HolderConjugate.two_two hv hk
      calc ∫⁻ x, ENNReal.ofReal (UnforcedLeray.Short.PartIIIb.Concrete.frob
              (UnforcedLeray.Short.IIIa.symOuter
                (UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x)) (kcMer y x)))
            ∂(UnforcedLeray.B0581.cellVol c)
          ≤ ∫⁻ x, ENNReal.ofReal (2 * ‖tr.v u x‖ * ‖kcMer y x‖)
            ∂(UnforcedLeray.B0581.cellVol c) := lintegral_mono hpt
        _ = ∫⁻ x, ENNReal.ofReal (2 * ‖tr.v u x‖ * ‖kcLp y x‖)
            ∂(UnforcedLeray.B0581.cellVol c) := hae
        _ = ∫⁻ x, 2 * (‖tr.v u x‖ₑ * ‖kcLp y x‖ₑ) ∂(UnforcedLeray.B0581.cellVol c) :=
            lintegral_congr (fun x => ofReal_two_mul_norm_mul_norm _ _)
        _ = 2 * ∫⁻ x, ‖tr.v u x‖ₑ * ‖kcLp y x‖ₑ ∂(UnforcedLeray.B0581.cellVol c) :=
            lintegral_const_mul' (2 : ℝ≥0∞)
              (fun x => ‖tr.v u x‖ₑ * ‖kcLp y x‖ₑ) ENNReal.ofNat_ne_top
        _ ≤ 2 * ((∫⁻ x, ‖tr.v u x‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.B0581.cellVol c)) ^ (1 / (2 : ℝ)) *
            (∫⁻ x, ‖kcLp y x‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.B0581.cellVol c)) ^ (1 / (2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hH (by norm_num)
    rw [show ∀ a b d : ℝ≥0∞, 2 * a * b * d = a * (2 * (b * d)) from fun a b d => by ring]
    exact mul_le_mul_of_nonneg_left hmain (by positivity)
  · -- for `u < 0` the train mer vanishes, so the left side is zero
    have h0 : ∀ x : (ℝ × ℝ),
        ENNReal.ofReal (UnforcedLeray.Short.PartIIIb.Concrete.frob
          (UnforcedLeray.Short.IIIa.symOuter
            (UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x)) (kcMer y x))) = 0 := by
      intro x
      apply ENNReal.ofReal_eq_zero.2
      have hm : UnforcedLeray.Short.PartIIIb.NearInst.trainMer tr (u, x) = 0 := by
        ext i
        simp [UnforcedLeray.Short.PartIIIb.NearInst.trainMer,
          UnforcedLeray.Short.IIIa.trainVel, hu]
      refine (frob_symOuter_le_aux _ _).trans (le_of_eq ?_)
      rw [hm]
      simp
    refine (le_of_eq ?_).trans zero_le
    simp only [h0, lintegral_zero, mul_zero]

/-- **Cauchy-Schwarz on one cell for the stress readout** (source 3283-3287, 4610-4612), the
statement `SymOuterSliceProp m` of `TrainEnergyUnif` / `TrainOldStressBound`. -/
theorem symOuterSlice (m : ℝ) [Fact (1 < m)] : SymOuterSliceProp m := by
  unfold SymOuterSliceProp
  intro ν hν tr
  haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  intro u y
  exact slice_gen m tr u y

end UnforcedLeray.Short.PartIIIb.Concrete
