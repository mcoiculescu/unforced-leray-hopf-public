import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLiftDefs
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Bridge
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_4

/-!
# The Ward velocity identity for `Yf + hf` (source 4161-4174)

Under `IsWardPinned`, the physical velocity of `Yf T + hf T` is `realC (wardY + wardH)` almost
everywhere in `ℝ × ℝ³`.  The two body-measure a.e. identities of `IsWardPinned` are summed
(`Lp.coeFn_add`), the chart coefficient is additive (`vyh_coefOf_add`), and the body-a.e. equality
is transferred to `volume`-a.e. equality of the physical velocities (`vyh_ae_body`, the argument of
`fwuSubAE`: `liftFun_congr_ae`, periodic slicing `ae_slice`, `ae_zero_of_periodic`).
The pointwise identity is `SmoothWardInput.liftYH`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem vyh_realC_continuous : Continuous (B0412.realC : Space → CVec3) := by
  unfold B0412.realC
  exact continuous_finsetSum _ fun i _ =>
    (Complex.continuous_ofReal.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).smul
      continuous_const

theorem vyh_velPhys_eq (R c : ℝ) (hR : R ≠ 0) (b : Chart → Merid) (x : ℝ × Space) :
    velPhys R c b x = B0412.realC ((Real.sqrt Real.pi * R) • liftFun R c b x) := by
  have h : (Real.sqrt Real.pi * R) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.2 Real.pi_pos).ne' hR
  simp only [velPhys, liftFun, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem vyh_velPhys_periodic {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Chart → Merid) (τ : ℝ) (y : Space) :
    velPhys R c b (τ + P, y) = velPhys R c b (τ, y) := by
  have hk := liftFun_add_period hR hc hP b τ y
  rw [vyh_velPhys_eq R c hR.ne' b, vyh_velPhys_eq R c hR.ne' b, hk]

theorem vyh_velPhys_intper {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Chart → Merid) (k : ℤ) (τ : ℝ) (y : Space) :
    velPhys R c b (τ + (k : ℝ) * P, y) = velPhys R c b (τ, y) := by
  have hp : Function.Periodic (fun s : ℝ => velPhys R c b (s, y)) P :=
    fun s => vyh_velPhys_periodic hR hc hP b s y
  exact hp.int_mul k τ

theorem vyh_measurable_velPhys (R c : ℝ) {b : Chart → Merid} (hb : Measurable b) :
    Measurable (velPhys R c b) :=
  vyh_realC_continuous.measurable.comp (measurable_Nv R (measurable_perExt c hb))

theorem vyh_ageμ_absCont_body (c γ ν : ℝ) : ageμ c (-3 / 2) ≪ bodyMeasure c γ ν := by
  unfold bodyMeasure
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((NearInst.ginv_measurable' γ ν).pow_const 2))).aemeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    have hg := NearInst.ginv_pos' γ ν p
    positivity

/-- Body-a.e. equal chart fields have volume-a.e. equal physical velocities (periodic slicing). -/
theorem vyh_ae_body {c γ ν ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (G G' : Chart → Merid)
    (hG : Measurable G) (hG' : Measurable G') (h : G =ᵐ[bodyMeasure c γ ν] G') :
    velPhys ε⁻¹ c G =ᵐ[volume] velPhys ε⁻¹ c G' := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * ε * c := by positivity
  have : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hG3 : G =ᵐ[ageμ c (-3 / 2)] G' := (vyh_ageμ_absCont_body c γ ν).ae_le h
  have h2 := liftFun_congr_ae hR hc hP hG hG' hG3
  have key : ∀ᵐ x ∂(phaseμ (2 * ε * c)),
      velPhys ε⁻¹ c G x - velPhys ε⁻¹ c G' x = 0 := by
    filter_upwards [h2] with x hx
    rw [vyh_velPhys_eq ε⁻¹ c hR.ne' G x, vyh_velPhys_eq ε⁻¹ c hR.ne' G' x, hx, sub_self]
  have hs := ae_slice (p := fun x : ℝ × Space =>
      velPhys ε⁻¹ c G x - velPhys ε⁻¹ c G' x = 0) key
  have hDm : Measurable (fun x : ℝ × Space =>
      velPhys ε⁻¹ c G x - velPhys ε⁻¹ c G' x) :=
    (vyh_measurable_velPhys ε⁻¹ c hG).sub (vyh_measurable_velPhys ε⁻¹ c hG')
  have hper : ∀ (k : ℤ) (x : ℝ × Space),
      (fun x : ℝ × Space => velPhys ε⁻¹ c G x - velPhys ε⁻¹ c G' x) (x.1 + (k : ℝ) * (2 * ε * c), x.2) =
        (fun x : ℝ × Space => velPhys ε⁻¹ c G x - velPhys ε⁻¹ c G' x) x := by
    intro k x
    obtain ⟨τ, y⟩ := x
    simp only [vyh_velPhys_intper hR hc hP G k τ y, vyh_velPhys_intper hR hc hP G' k τ y]
  have hz := UnforcedLeray.Short.IIb.BLRepLinAux.ae_zero_of_periodic (P := 2 * ε * c) hP0 hDm
    hper hs
  filter_upwards [hz] with x hx
  exact sub_eq_zero.1 hx

theorem vyh_coefOf_add (R : ℝ) (F G : ℝ → Space → Space) :
    coefOf R (fun τ y => F τ y + G τ y) = coefOf R F + coefOf R G := by
  funext p
  ext i
  fin_cases i <;> simp [coefOf] <;> ring

theorem vyh_measurable_coefOf (R : ℝ) {F : ℝ → Space → Space}
    (hF : Measurable (fun x : ℝ × Space => F x.1 x.2)) : Measurable (coefOf R F) := by
  unfold coefOf
  have hc : Measurable (fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p)) :=
    (by unfold NearInst.chartTau; fun_prop : Measurable (NearInst.chartTau R)).prodMk
      (by unfold NearInst.chartY; fun_prop : Measurable (NearInst.chartY R))
  have h0 : Measurable (fun p : Chart => F (NearInst.chartTau R p) (NearInst.chartY R p)) :=
    hF.comp hc
  fun_prop

/-- **(a)** (source 4161-4174): under `IsWardPinned`, the physical velocity of `Yf T + hf T` is
`realC (wardY + wardH)` almost everywhere on `ℝ × ℝ³`. -/
theorem wardVelPhysYH_proved {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) (hν : 0 < ν) (μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    WardVelPhysYH B hc ε hε hν μ hχo χy U p := by
  intro hW T g₁ g₂ hg1 hg2 hin
  obtain ⟨hY, hH, -⟩ := wardPinned_reg B hε.ne' hW T g₁ g₂ hg1 hg2
  have hA : ((B.Yf T : Chart → Merid) + (B.hf T : Chart → Merid)) =ᵐ[bodyMeasure c γ ν]
      coefOf ε⁻¹ (fun τ y => wardYr ν μ ε⁻¹ c χy (g₁ + g₂) τ y +
        wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) τ y) := by
    rw [vyh_coefOf_add]
    filter_upwards [hY, hH] with q h1 h2
    simp only [Pi.add_apply]
    rw [h1, h2]
  have hS : Measurable ((B.Yf T : Chart → Merid) + (B.hf T : Chart → Merid)) :=
    (Lp.stronglyMeasurable (B.Yf T)).measurable.add (Lp.stronglyMeasurable (B.hf T)).measurable
  have hFH : Measurable (fun x : ℝ × Space =>
      wardYr ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) x.1 x.2) :=
    hin.smoothY.continuous.measurable.add hin.smoothH.continuous.measurable
  have hG' := vyh_measurable_coefOf (F := fun τ y => wardYr ν μ ε⁻¹ c χy (g₁ + g₂) τ y +
    wardHr ν μ ε⁻¹ c χy U (g₁ + g₂) τ y) ε⁻¹ hFH
  have hV := vyh_ae_body hc hε _ _ hS hG' hA
  filter_upwards [hV, realC_wardYHr_ae ν μ ε⁻¹ c χy U (g₁ + g₂)] with x hx hr
  exact hx.trans ((hin.liftYH x).trans hr)

end UnforcedLeray.Short.PartIIIb.Concrete
