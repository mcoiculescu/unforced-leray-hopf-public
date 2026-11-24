import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply

/-!
# `chiOMultYoung_of`: `χ_o` annihilates the multiplier of a young velocity (source 4310-4311, 4163)

If `w` has young support (`w = 0` at ages `6/5 < ν s`, `bodyMeasure`-a.e.), then `M_U w` has
`χ_o`-cut stress zero: at ages `ν s ≤ 6/5` the cutoff `χ_o` vanishes, and at ages `6/5 < ν s` the
velocity `w` vanishes.  The a.e. transfer from `bodyMeasure` to the gain measures uses that the
gain densities are positive and the age measures `ageμ c a` are mutually absolutely continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem cmo_ginv_pos (γ ν : ℝ) (p : Chart) : 0 < ginv γ ν p := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  positivity

theorem cmo_ginv_meas (γ ν : ℝ) : Measurable (fun p : Chart => ginv γ ν p) := by
  unfold ginv UnforcedLeray.Short.IIIa.gainG
  fun_prop

theorem cmo_transWeight_meas (mZ : ℝ) :
    Measurable (fun p : Chart => UnforcedLeray.Short.IIIa.transWeight mZ p) := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  fun_prop

theorem cmo_avg_sfinite (c : ℝ) : SFinite (Cyl.avgμ c) := by
  unfold Cyl.avgμ
  infer_instance

theorem cmo_ac_ageμ (c a b : ℝ) : ageμ c a ≪ ageμ c b := by
  unfold ageμ
  have := cmo_avg_sfinite c
  refine Measure.AbsolutelyContinuous.prod ?_ (Measure.AbsolutelyContinuous.refl _)
  refine (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous' ?_ ?_)
  · exact (measurable_ofReal_rpow b).aemeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun s hs =>
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Set.mem_Ioi.mp hs) b)).ne'

theorem cmo_ae_half (c γ ν : ℝ) {P : Chart → Prop} (h : ∀ᵐ p ∂(bodyMeasure c γ ν), P p) :
    ∀ᵐ p ∂(ageμ c (-1 / 2)), P p := by
  have hmeas : Measurable (fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((cmo_ginv_meas γ ν).pow_const 2))
  have h1 : ∀ᵐ p ∂(ageμ c (-3 / 2)), P p := by
    unfold bodyMeasure at h
    rw [ae_withDensity_iff hmeas] at h
    exact h.mono fun p hp =>
      hp (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (pow_pos (cmo_ginv_pos γ ν p) 2))).ne'
  exact Filter.Eventually.filter_mono
    (Measure.ae_le_iff_absolutelyContinuous.mpr (cmo_ac_ageμ c (-1 / 2) (-3 / 2))) h1

theorem cmo_ae_gainZ1 (c mZ γ ν : ℝ) {P : Chart → Prop} (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p) :
    ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), P p := by
  have hF : Measurable (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((cmo_ginv_meas γ ν).pow_const 2)
  have hW : Measurable (fun p : Chart =>
      ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((cmo_transWeight_meas mZ).pow_const 2)
  unfold gainZ1Measure z1Measure
  refine (ae_withDensity_iff hF).mpr ?_
  refine (ae_withDensity_iff hW).mpr ?_
  exact h.mono fun p hp _ _ => hp

theorem cmo_ae_gainHT (c ρb γ ν : ℝ) {P : Chart → Prop} (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p) :
    ∀ᵐ p ∂(gainHTMeasure c ρb γ ν), P p := by
  have hF : Measurable (fun p : Chart => ENNReal.ofReal (ginv γ ν p ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((cmo_ginv_meas γ ν).pow_const 2)
  unfold gainHTMeasure htRhoMeasure
  refine (ae_withDensity_iff hF).mpr ?_
  refine Measure.ae_smul_measure ?_ (ENNReal.ofReal ρb⁻¹)
  exact h.mono fun p hp _ => hp

theorem cmo_pt {ν R : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (V : ℝ → SpatialField)
    (u : Chart → Merid) (p : Chart) (hu : 6 / 5 < ν * p.1 → u p = 0) :
    cutFun χo ν p • NearInst.ten3Of (IIIa.symOuter (IIIa.chartCoeff R V p) (u p)) = 0 := by
  by_cases hpν : ν * p.1 ≤ 6 / 5
  · have hc : cutFun χo ν p = 0 := hχo.zero _ hpν
    rw [hc, zero_smul]
  · have hso : IIIa.symOuter (IIIa.chartCoeff R V p) (0 : Merid) = 0 := by
      funext i j
      fin_cases i <;> fin_cases j <;> simp [IIIa.symOuter, IIIa.embedMerid]
    rw [hu (not_le.mp hpν), hso]
    have h0 : NearInst.ten3Of (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      ext ab
      simp [NearInst.ten3Of]
    rw [h0, smul_zero]

theorem chiOMultYoung_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {R : ℝ}
    {V rb : ℝ → SpatialField} (hM : IsExactMultiplier B R V rb) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) : ChiOMultYoung B hχo := by
  intro w hw
  have hwP : ∀ᵐ p ∂(bodyMeasure c γ ν), (6 / 5 < ν * p.1 → (w : Chart → Merid) p = 0) := hw
  have h1 := cmo_ae_half c γ ν hwP
  have hZ := cmo_ae_gainZ1 c mZ γ ν h1
  have hHT := cmo_ae_gainHT c ρb γ ν h1
  have hfst : (chiOStr c mZ ρb γ ν hχo (B.M w)).fst = 0 := by
    apply Lp.ext
    filter_upwards [(chiOStrApply c mZ ρb γ ν χo hχo (B.M w)).1, (hM w).1, hZ,
      Lp.coeFn_zero Ten3 2 (gainZ1Measure c mZ γ ν)] with p h1' h2' h3' h4'
    simp only [h1', h2', h4']
    exact cmo_pt hχo V w p h3'
  have hsnd : (chiOStr c mZ ρb γ ν hχo (B.M w)).snd = 0 := by
    apply Lp.ext
    filter_upwards [(chiOStrApply c mZ ρb γ ν χo hχo (B.M w)).2, (hM w).2, hHT,
      Lp.coeFn_zero Ten3 2 (gainHTMeasure c ρb γ ν)] with p h1' h2' h3' h4'
    simp only [h1', h2', h4']
    exact cmo_pt hχo rb w p h3'
  rw [WithLp.ext_iff]
  exact Prod.ext hfst hsnd

end UnforcedLeray.Short.PartIIIb.Concrete
