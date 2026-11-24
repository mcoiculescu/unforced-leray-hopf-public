import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Transfer
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

/-!
# `thinMultPin`: the thin multiplier on young output

Source `the November 2 reference manuscript` 2758-2772, 4147, 5779-5782
(`(M_Uu)₁ = v⊗u + u⊗v`), 4164 (`|χ_y| ≤ 1`), 3875, 5117 (`g⁻¹ ≤ 1`), 2697.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem thinMultPin : ThinMultPin := by
  intro Pl K L μ hχ hC0 hnear hs hγ v
  have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have h3 := youngMul_ae (c := cOf L.ν) (γ := gRate Pl) (ν := L.ν) hχ v
  have h3a : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)),
      (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p := by
    rw [← NearInst.ae_bodyMeasure (cOf L.ν) (gRate Pl) L.ν]; exact h3
  have h3b := (NearInst.CoeffMult.z1_ac hc K.mZ).ae_le h3a
  have h3z : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν),
      (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p := by
    rw [NearInst.ae_gainZ1Measure]; exact h3b
  have h1 : ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ
      (gRate Pl) L.ν] fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p) ((youngMul hχ v : Chart → Merid) p)) :=
    (hEx (youngMul hχ v)).1
  have hW : Measurable fun p : Chart => ENNReal.ofReal
      (UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2) :=
    ENNReal.measurable_ofReal.comp ((NearInst.transWeight_measurable K.mZ).pow_const 2)
  constructor
  · -- norm bound
    set y := multOp Pl K L (youngMul hχ v) with hy
    rw [lrt_norm_thinPart]
    have hb := lrt_gainZ1_le_glob (c := cOf L.ν) (mZ := K.mZ) (γ := gRate Pl) (ν := L.ν)
      (B := 1) zero_le_one (fun p => ginv_le_one hγ L.ν_pos.le p) y.fst
    rw [ENNReal.ofReal_one, one_mul] at hb
    unfold z1Ung at hb
    calc ENNReal.ofReal ‖y.fst‖ ^ (2 : ℝ)
        ≤ ((∫⁻ p, ‖(y.fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure (cOf L.ν) K.mZ)) ^
            (1 / 2 : ℝ)) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hb (by norm_num)
      _ = ∫⁻ p, ‖(y.fst : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure (cOf L.ν) K.mZ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ = _ := by
          unfold z1Measure
          rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hW
            (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
          rfl
  · have h1' : ∀ᵐ p ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν),
        ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) p = NearInst.ten3Of
          (UnforcedLeray.Short.IIIa.symOuter (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p)
            ((youngMul hχ v : Chart → Merid) p)) ∧
        (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p :=
      h1.and h3z
    have h1'' : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
        ((multOp Pl K L (youngMul hχ v)).fst : Chart → Ten3) p = NearInst.ten3Of
          (UnforcedLeray.Short.IIIa.symOuter (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p)
            ((youngMul hχ v : Chart → Merid) p)) ∧
        (youngMul hχ v : Chart → Merid) p = cutFun K.χy L.ν p • (v : Chart → Merid) p := by
      rw [← NearInst.ae_z1Measure, ← NearInst.ae_gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      exact h1'
    filter_upwards [h1''] with p ⟨e1, e3⟩
    rw [e1, e3]
    set a := UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.V p
    set t := cutFun K.χy L.ν p
    set u := (v : Chart → Merid) p
    set W2 := UnforcedLeray.Short.IIIa.transWeight K.mZ p ^ 2
    have hW0 : 0 ≤ W2 := sq_nonneg _
    have ht : t ^ 2 ≤ 1 := by
      have := cutFun_bound_y hχ L.ν p
      have h2 : |t| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) this
      rwa [sq_abs] at h2
    have hF : ‖NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter a (t • u))‖ ^ 2 ≤
        4 * ‖a‖ ^ 2 * ‖u‖ ^ 2 := by
      rw [NearInst.CoeffMult.norm_sq_ten3Of]
      refine (NearInst.CoeffMult.frobSq_symOuter_le' a (t • u)).trans ?_
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg ‖a‖))
        (sq_nonneg ‖u‖)]
    simp only [NearInst.CoeffMult.enorm_rpow_two']
    rw [← ENNReal.ofReal_mul hW0, ← ENNReal.ofReal_mul (by positivity),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_le_mul_of_nonneg_left hF hW0]

end UnforcedLeray.Short.PartIIIb.Concrete
