import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.ChiOMultYoung

/-!
# `PartIII-b:C/rep/5/2/1/8`: the two source representatives agree a.e. for `ageμ c (-1/2)`

Source `the November 2 reference manuscript` 5153-5157, 5377-5379.
For `T₂ = (0, M_{r_b}w)` the old source `χ_oT₂` has thin part `0` and repair part `χ_o M_{r_b}w`
(`chiOStr`, pointwise multiplication by `χ̂_o(ν s)`); the early source `T₂ - χ_oT₂` has repair
part `(1-χ̂_o(νs)) M_{r_b}w`.  The gain measures `gainZ1Measure`, `gainHTMeasure` are `ageμ c (-1/2)`
times positive densities, so their a.e. statements transfer to `ageμ c (-1/2)`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rsa_F_ne (γ ν : ℝ) (p : ℝ × (ℝ × ℝ)) :
    ENNReal.ofReal (ginv γ ν p ^ 2) ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (pow_pos (cmo_ginv_pos γ ν p) 2)).ne'

theorem rsa_W_ne (mZ : ℝ) (p : ℝ × (ℝ × ℝ)) :
    ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) ≠ 0 := by
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  unfold UnforcedLeray.Short.IIIa.transWeight
  positivity

/-- `ρ_b > 0` from `C₀ > 0` (the formula `ρ_b = C₀ ν^{-k₀} e^{m₀/ν} ε^{3/11}`). -/
theorem rsa_rhoB_pos (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) :
    0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
  have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
  have h3 := Real.exp_pos (K.m0 / (L.params Pl).ν)
  positivity

/-- A.e. statements for `gainZ1Measure` transfer to `ageμ c (-1/2)` (positive densities). -/
theorem rsa_ae_gainZ1 {c mZ γ ν : ℝ} {P : ℝ × (ℝ × ℝ) → Prop}
    (h : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), P p) : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p := by
  have hF : Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((cmo_ginv_meas γ ν).pow_const 2)
  have hW : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((cmo_transWeight_meas mZ).pow_const 2)
  unfold gainZ1Measure z1Measure at h
  rw [ae_withDensity_iff hF] at h
  rw [ae_withDensity_iff hW] at h
  exact h.mono fun p hp => hp (rsa_W_ne mZ p) (rsa_F_ne γ ν p)

/-- A.e. statements for `gainHTMeasure` transfer to `ageμ c (-1/2)` (`ρ_b > 0`). -/
theorem rsa_ae_gainHT {c ρb γ ν : ℝ} (hρ : 0 < ρb) {P : ℝ × (ℝ × ℝ) → Prop}
    (h : ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), P p) : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p := by
  have hF : Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((cmo_ginv_meas γ ν).pow_const 2)
  unfold gainHTMeasure htRhoMeasure at h
  rw [ae_withDensity_iff hF] at h
  rw [Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr (inv_pos.mpr hρ)).ne'] at h
  exact h.mono fun p hp => hp (rsa_F_ne γ ν p)

theorem rsa_ae_gainZ1_eq {E : Type*} {c mZ γ ν : ℝ} {f g : ℝ × (ℝ × ℝ) → E}
    (h : f =ᵐ[gainZ1Measure c mZ γ ν] g) : f =ᵐ[ageμ c (-1 / 2)] g :=
  rsa_ae_gainZ1 (P := fun p => f p = g p) h

theorem rsa_ae_gainHT_eq {E : Type*} {c ρb γ ν : ℝ} (hρ : 0 < ρb) {f g : ℝ × (ℝ × ℝ) → E}
    (h : f =ᵐ[gainHTMeasure c ρb γ ν] g) : f =ᵐ[ageμ c (-1 / 2)] g :=
  rsa_ae_gainHT hρ (P := fun p => f p = g p) h

/-- The thin part of `χ_oT` is `χ̂_o(ν s)` times the thin part of `T` (gain measure `Z_1`). -/
theorem rsa_chiO_fst {c mZ ρb γ ν : ℝ} {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ)
    (T : StrG c mZ ρb γ ν) :
    ((chiOStr c mZ ρb γ ν hχ T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      cutFun χ ν • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) :=
  NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainZ1Measure c mZ γ ν) (cutFun χ ν)
    (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) T.fst

/-- The repair part of `χ_oT` is `χ̂_o(ν s)` times the repair part of `T` (gain measure `H_T`). -/
theorem rsa_chiO_snd {c mZ ρb γ ν : ℝ} {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ)
    (T : StrG c mZ ρb γ ν) :
    ((chiOStr c mZ ρb γ ν hχ T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      cutFun χ ν • ((T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) : Chart → Ten3) :=
  NearInst.mulBdd_apply_ae (E := Ten3) (μ := gainHTMeasure c ρb γ ν) (cutFun χ ν)
    (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν) T.snd

/-- The parts of the repair projection: `(0, T₂)` has thin part `0` and repair part `T₂`. -/
theorem rsa_repPart_parts {c mZ ρb γ ν : ℝ} (X : StrG c mZ ρb γ ν) :
    WithLp.fst (repPart X) = 0 ∧ WithLp.snd (repPart X) = WithLp.snd X := by
  have h : (WithLp.prodContinuousLinearEquiv 1 ℝ
      (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
      (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) (repPart X)) =
      (0, WithLp.snd X) := by
    simp only [repPart, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_snd']
    rfl
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact ⟨h1, h2⟩

/-- Additivity of the first projection on stresses. -/
theorem rsa_fst_sub {c mZ ρb γ ν : ℝ} (A B : StrG c mZ ρb γ ν) :
    WithLp.fst (A - B) = WithLp.fst A - WithLp.fst B := by
  rfl

/-- Additivity of the second projection on stresses. -/
theorem rsa_snd_sub {c mZ ρb γ ν : ℝ} (A B : StrG c mZ ρb γ ν) :
    WithLp.snd (A - B) = WithLp.snd A - WithLp.snd B := by
  rfl

theorem repSplitAE : RepSplitAE := by
  intro Pl K L hC0 w
  unfold repSrcTen earlyRepTen
  set X : LStr Pl K L := multOp Pl K L w with hXdef
  have hρ : 0 < L.ρb Pl K := rsa_rhoB_pos Pl K L hC0
  obtain ⟨hf0, hs0⟩ := rsa_repPart_parts X
  have hsnd_eq : ((WithLp.snd (repPart X) : Lp (α := Chart) Ten3 2
      (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)) : Chart → Ten3) =
      ((WithLp.snd X : Lp (α := Chart) Ten3 2
      (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)) : Chart → Ten3) := by
    rw [hs0]
  -- the thin part of the repair source vanishes
  have hz : ((WithLp.fst (repPart X) : Lp (α := Chart) Ten3 2
      (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) : Chart → Ten3) =ᵐ[
      gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] 0 := by
    rw [hf0]
    exact Lp.coeFn_zero _ _ _
  have hF1g : ((ftOld Pl K L (repPart X)).fst : Chart → Ten3) =ᵐ[
      gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] 0 := by
    filter_upwards [rsa_chiO_fst K.hχo (repPart X), hz] with p h1 h2
    rw [h1]
    simp [h2]
  have hF1 := rsa_ae_gainZ1_eq hF1g
  -- the repair part of the old source is the repair source
  have hS1g : ((ftOld Pl K L (repPart X)).snd : Chart → Ten3) =ᵐ[
      gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
      ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo X).snd : Chart → Ten3) := by
    filter_upwards [rsa_chiO_snd K.hχo (repPart X), rsa_chiO_snd K.hχo X] with p h1 h2
    rw [h1, h2, hsnd_eq]
  have hS1 := rsa_ae_gainHT_eq hρ hS1g
  constructor
  · filter_upwards [hF1, hS1] with p h1 h2
    simp only [strSum, h1, h2, Pi.zero_apply, zero_add]
  · -- the early source: fst part zero, snd part `(1-χ_o) X.snd`
    have hFst2g : ((WithLp.fst (repPart X - ftOld Pl K L (repPart X)) :
        Lp (α := Chart) Ten3 2 (gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν)) :
        Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] 0 := by
      rw [rsa_fst_sub]
      filter_upwards [Lp.coeFn_sub (WithLp.fst (repPart X))
        (WithLp.fst (ftOld Pl K L (repPart X))), hz, hF1g] with p h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      all_goals simp
    have hFst2 := rsa_ae_gainZ1_eq hFst2g
    have hSnd2g : ((WithLp.snd (repPart X - ftOld Pl K L (repPart X)) :
        Lp (α := Chart) Ten3 2 (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)) :
        Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        fun p => (1 - K.χo (L.ν * p.1)) • ((WithLp.snd X : Lp (α := Chart) Ten3 2
          (gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν)) : Chart → Ten3) p := by
      rw [rsa_snd_sub]
      filter_upwards [Lp.coeFn_sub (WithLp.snd (repPart X))
        (WithLp.snd (ftOld Pl K L (repPart X))),
        rsa_chiO_snd K.hχo (repPart X)] with p h1 h2
      rw [h1, Pi.sub_apply, h2, hsnd_eq]
      simp [cutFun, sub_smul]
    have hSnd2 := rsa_ae_gainHT_eq hρ hSnd2g
    filter_upwards [hFst2, hSnd2] with p h1 h2
    simp only [strSum, h1, h2, Pi.zero_apply, zero_add]

end UnforcedLeray.Short.PartIIIb.Concrete
