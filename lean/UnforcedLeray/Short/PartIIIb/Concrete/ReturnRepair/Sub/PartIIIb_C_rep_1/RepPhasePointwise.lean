import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.CartLift
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd

/-!
# Proof of the leaf `RepPhasePointwise` (`PartIII-b:C/rep/1/2`, source 4147, 5169-5171)

The physical repair stress is `cartLift` of `repSrcTen w = χ_o · (M_U w).snd`; by the exact
multiplier pin, `(M_U w).snd = r_b ⊗ w + w ⊗ r_b` a.e. for `gainHTMeasure`; the null sets transfer to
the chart points `chartOf z τ` by `chartOfNullPullback`; the lift is pointwise linear in the chart
tensor and `cartLiftSymOuter_proved` identifies it with `symProd`; `0 ≤ |χ_o| ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- The chart tensor `ten3Of (symOuter (chartCoeff R r_b p) (w p))` of the exact multiplier. -/
def repG (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (w : LVel Pl L) :
    Chart → Ten3 :=
  fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
    (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) (w p))

theorem tensorNorm_smul_le' (f : ℝ) (hf : |f| ≤ 1) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.IIIa.tensorNorm (f • M) ≤ UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  have h2 : f ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one f).mpr hf
  have hX : 0 ≤ ∑ i, ∑ j, M i j ^ 2 := by positivity
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, (f • M) i j ^ 2 = f ^ 2 * ∑ i, ∑ j, M i j ^ 2 := by
        simp [Matrix.smul_apply, mul_pow, Finset.mul_sum]
    _ ≤ 1 * ∑ i, ∑ j, M i j ^ 2 := mul_le_mul_of_nonneg_right h2 hX
    _ = ∑ i, ∑ j, M i j ^ 2 := one_mul _

theorem tensorNorm_symProd_le' (a b : Space) :
    UnforcedLeray.Short.IIIa.tensorNorm (symProd a b) ≤ 2 * ‖a‖ * ‖b‖ := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  have ha : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hb : ‖b‖ ^ 2 = ∑ i, b i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  have h : ∑ i, ∑ j, (symProd a b) i j ^ 2 ≤ (2 * ‖a‖ * ‖b‖) ^ 2 := by
    have key : (2 * ‖a‖ * ‖b‖) ^ 2 = 4 * (‖a‖ ^ 2) * (‖b‖ ^ 2) := by ring
    rw [key, ha, hb]
    simp only [symProd, Fin.sum_univ_three]
    nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
      sq_nonneg (a 1 * b 2 - a 2 * b 1)]
  calc Real.sqrt (∑ i, ∑ j, (symProd a b) i j ^ 2) ≤ Real.sqrt ((2 * ‖a‖ * ‖b‖) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = 2 * ‖a‖ * ‖b‖ := Real.sqrt_sq hab

theorem nsSym_smul_pt (f : ℝ) (T : Ten3) :
    NearInst.nsSym (f • T) = f • NearInst.nsSym T := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem cartLift_smul_pt (R c : ℝ) (f : Chart → ℝ) (G : Chart → Ten3) (τ : ℝ) (z : Space) :
    NearInst.cartLift R c (fun p => f p • G p) τ z =
      f (NearInst.chartOf R c z τ) • NearInst.cartLift R c G τ z := by
  unfold NearInst.cartLift
  simp only [nsSym_smul_pt]
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply]
  ring

theorem cartLift_congr_pt (R c : ℝ) (F F' : Chart → Ten3) (τ : ℝ) (z : Space)
    (h : F (NearInst.chartOf R c z τ) = F' (NearInst.chartOf R c z τ)) :
    NearInst.cartLift R c F τ z = NearInst.cartLift R c F' τ z := by
  unfold NearInst.cartLift
  rw [h]

theorem repPhasePointwise : RepPhasePointwise := by
  unfold RepPhasePointwise
  intro Pl K L μ hC0 hnear hs hax hper w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hrhoRep : 0 < rhoRep K L := by
    unfold rhoRep
    exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
  have hρpos : 0 < L.ρb Pl K := by
    rw [rhoB_eq]
    exact mul_pos (mul_pos hC0 (pow_pos (inv_pos.2 hν) _)) hrhoRep
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  -- the exact multiplier
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have hEx2 : ((multOp Pl K L w).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K)
      (gRate Pl) L.ν] repG Pl K L w := (hEx w).2
  -- the cut stress agrees with the exact stress on a gain-null complement
  have hC : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd :
      Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        fun p => cutFun K.χo L.ν p • ((multOp Pl K L w).snd : Chart → Ten3) p :=
    (chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo (multOp Pl K L w)).2
  have hgood : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd :
        Chart → Ten3) p = cutFun K.χo L.ν p • repG Pl K L w p := by
    filter_upwards [hC, hEx2] with p h1 h2
    rw [h1, h2]
  have hgood' := hgood
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρpos] at hgood'
  have hN0 := ae_iff.mp hgood'
  have hpt := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hN0
  have hcart := cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.rb hR hc hax hper w
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      UnforcedLeray.Short.IIIa.tensorNorm (repStressPhys Pl K L w x) ≤
        2 * ‖L.rb x.1 x.2‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) w x‖ := by
    filter_upwards [hpt] with x hx
    have hP : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd :
        Chart → Ten3) (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) =
          cutFun K.χo L.ν (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) •
            repG Pl K L w (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) :=
      not_not.mp hx
    have e1 : repStressPhys Pl K L w x =
        NearInst.cartLift L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w) x.1 x.2 := rfl
    have e2 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) (repSrcTen Pl K L w) x.1 x.2 =
        NearInst.cartLift L.ε⁻¹ (cOf L.ν) (fun p => cutFun K.χo L.ν p • repG Pl K L w p)
          x.1 x.2 :=
      cartLift_congr_pt _ _ _ _ _ _ hP
    have e3 := cartLift_smul_pt L.ε⁻¹ (cOf L.ν) (cutFun K.χo L.ν) (repG Pl K L w) x.1 x.2
    have e4 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) (repG Pl K L w) x.1 x.2 =
        symProd (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2) :=
      hcart x.1 x.2
    have hv : ‖velPhys L.ε⁻¹ (cOf L.ν) w x‖ = ‖Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2‖ :=
      wda_norm_realC _
    have hcut : |cutFun K.χo L.ν (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1)| ≤ 1 :=
      cutFun_bound K.hχo L.ν _
    rw [e1, e2, e3, e4, hv]
    calc UnforcedLeray.Short.IIIa.tensorNorm
          (cutFun K.χo L.ν (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) •
            symProd (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2))
        ≤ UnforcedLeray.Short.IIIa.tensorNorm
            (symProd (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2)) :=
          tensorNorm_smul_le' _ hcut _
      _ ≤ 2 * ‖L.rb x.1 x.2‖ * ‖Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2‖ :=
          tensorNorm_symProd_le' _ _
  rw [Measure.volume_eq_prod] at hae
  have h2 := Measure.ae_ae_of_ae_prod hae
  exact ae_restrict_of_ae h2

end UnforcedLeray.Short.PartIIIb.Concrete
