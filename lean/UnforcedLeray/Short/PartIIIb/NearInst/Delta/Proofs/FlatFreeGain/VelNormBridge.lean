import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.Props

/-!
# `VelNormBridge` (item `PartIII-b:C/near/delta/7/3`)

Source `the November 2 reference manuscript` 3412: `𝓗 = L²(s^{-3/2} ds; L²)`.
The velocity `g⁻¹ v` (multiplication by the bounded gain inverse) has the same `H`-norm as the
conjugated field `g⁻¹ b` when `b` represents `v`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

theorem vnorm2_smul_realVec (k : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    UnforcedLeray.Short.IIIa.vnorm2 (k • (fun i => (((x i : ℝ)) : ℂ))) = |k| * ‖x‖ := by
  unfold UnforcedLeray.Short.IIIa.vnorm2
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i : Fin 2, ‖(k • (fun i => (((x i : ℝ)) : ℂ))) i‖ ^ 2)
      = |k| ^ 2 * ∑ i : Fin 2, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Pi.smul_apply, Real.norm_eq_abs, mul_pow]
  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

theorem velNormBridge : VelNormBridge := by
  intro c γ ν hν v b hb
  set w := (gainH c γ hν).symm v with hwdef
  -- the age measure lives on `s > 0`
  have hs : ∀ᵐ p ∂ageμ c (-3 / 2), 0 < p.1 := by
    rw [ae_iff]
    have hset : {p : ℝ × (ℝ × ℝ) | ¬ 0 < p.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
      ext p; simp
    rw [hset]
    have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      infer_instance
    unfold UnforcedLeray.Axi.ageμ
    rw [Measure.prod_prod, withDensity_apply _ measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi, Set.Ioc_self,
      Measure.restrict_empty, lintegral_zero_measure, zero_mul]
  have hmul : mulBdd (μ := ageμ c (-3 / 2)) (gainFun γ ν) (gainFun_measurable γ ν)
      (Real.exp (|γ| / ν)) (gainFun_le hν) w = v :=
    (gainH c γ hν).apply_symm_apply v
  have h1 : (gainFun γ ν • (w : Chart → Merid)) =ᵐ[ageμ c (-3 / 2)] (v : Chart → Merid) := by
    have := mulBdd_apply_ae (μ := ageμ c (-3 / 2)) (gainFun γ ν) (gainFun_measurable γ ν)
      (Real.exp (|γ| / ν)) (gainFun_le hν) w
    rw [hmul] at this
    exact this.symm
  have hw : (w : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      fun p => gainInvFun γ ν p • (v : Chart → Merid) p := by
    filter_upwards [h1] with p hp
    have hp' : gainFun γ ν p • (w : Chart → Merid) p = (v : Chart → Merid) p := hp
    calc (w : Chart → Merid) p
        = (gainInvFun γ ν p * gainFun γ ν p) • (w : Chart → Merid) p := by
          rw [gainInvFun_mul, one_smul]
      _ = gainInvFun γ ν p • (gainFun γ ν p • (w : Chart → Merid) p) := mul_smul _ _ _
      _ = gainInvFun γ ν p • (v : Chart → Merid) p := by rw [hp']
  have hfin : eLpNorm (w : Chart → Merid) 2 (ageμ c (-3 / 2)) ≠ ⊤ := (Lp.memLp w).2.ne
  have hLHS : ENNReal.ofReal ‖w‖ = eLpNorm (w : Chart → Merid) 2 (ageμ c (-3 / 2)) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal hfin]
  unfold UnforcedLeray.Short.IIIa.hCalNorm
  rw [hLHS, ← eLpNorm_norm]
  apply le_of_eq
  apply eLpNorm_congr_ae
  filter_upwards [hw, hs, hb] with p hwp hsp hbp
  have hgg : gainInvFun γ ν p = (UnforcedLeray.Short.IIIa.gainG γ ν p.1)⁻¹ := by
    unfold gainInvFun gainFun
    rw [max_eq_left hsp.le]
  have hbp' : b p = fun i => (((v : Chart → Merid) p i : ℝ) : ℂ) := hbp
  show ‖(w : Chart → Merid) p‖ = UnforcedLeray.Short.IIIa.vnorm2
    ((UnforcedLeray.Short.IIIa.gainConj γ ν b) p)
  unfold UnforcedLeray.Short.IIIa.gainConj
  rw [hwp, norm_smul, Real.norm_eq_abs, ← hgg, hbp', vnorm2_smul_realVec]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
