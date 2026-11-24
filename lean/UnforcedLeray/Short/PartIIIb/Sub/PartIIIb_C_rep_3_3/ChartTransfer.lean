import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L2

/-!
# Leaf 1 (`PartIII-b:C/rep/3/3/1`): chart measurability and lift transfer for `meanJetDens`

Source of record: `the November 2 reference manuscript` (73 pages), lines
2681-2689 and 5259-5268.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)
open WardEMeasAux

private def rjOff (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space) : ℝ :=
  ‖jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y‖ +
    ∑ j : Fin 3, ‖wemOff (fun t z => physPd (X t) j z) τ y‖ +
    ∑ j : Fin 3, ∑ l : Fin 3, ‖wemOff (fun t z => physPd2 (X t) j l z) τ y‖

private lemma rjOff_eq_of_not_mem (X Y : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    rjOff X Y τ y = meanJetDens (X τ) (Y τ) y := by
  unfold rjOff meanJetDens
  have hY : (jet1 fun j => wemOff (fun t z => physPd (Y t) j z) τ y) = fderiv ℝ (Y τ) y := by
    conv_rhs => rw [eq_jet1 (fderiv ℝ (Y τ) y)]
    congr 1
    funext j
    exact wem_off_of_not_mem (F := fun t z => physPd (Y t) j z) hy
  have hX1 : ∀ j : Fin 3, wemOff (fun t z => physPd (X t) j z) τ y = physPd (X τ) j y :=
    fun j => wem_off_of_not_mem (F := fun t z => physPd (X t) j z) hy
  have hX2 : ∀ j l : Fin 3, wemOff (fun t z => physPd2 (X t) j l z) τ y = physPd2 (X τ) j l y :=
    fun j l => wem_off_of_not_mem (F := fun t z => physPd2 (X t) j l z) hy
  simp only [hY, hX1, hX2]

private lemma rjOff_measurable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}
    (hχy : IsStreamCutoff K.χy) (hμ : -(1 / 4 : ℝ) < μ) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (w : LVel Pl L) :
    Measurable fun x : ℝ × Space => rjOff (repX Pl K L μ w) (repY Pl K L μ w) x.1 x.2 := by
  have hO : IsOpen axisᶜ := isClosed_axis.isOpen_compl
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hχy' : IsYoungCutoff K.χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  have hg : IsOldL2 (cOf L.ν) L.ν (repSrcTen Pl K L w) :=
    vr_isOldL2_repSrcTen Pl K L hC0 hmZ w
  set X := repX Pl K L μ w with hXdef
  set Y := repY Pl K L μ w with hYdef
  have hD := fun τ =>
    wardXDiff_proved L.ν μ L.ε⁻¹ (cOf L.ν) K.χy hχy' hν hR hc hμ (repSrcTen Pl K L w) hg τ
  have hC3 : ∀ τ, ContDiffOn ℝ 3 (X τ) axisᶜ := fun τ => (hD τ).1
  have hXm : Measurable fun x : ℝ × Space => X x.1 x.2 :=
    T8_4.t84_ward_stream hχy' hg.measurable
  have dX : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (X τ) y := fun τ y hy =>
    WardCalc.diffAt_of_contDiffOn hO (hC3 τ) hy
  have dpX : ∀ l : Fin 3, ∀ τ y, y ∉ axis →
      DifferentiableAt ℝ ((fun τ y => physPd (X τ) l y) τ) y := fun l τ y hy =>
    WardCalc.differentiableAt_physPd hO (hC3 τ) hy l
  have dY : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (Y τ) y := by
    intro τ y hy
    have hcd : ContDiffAt ℝ 3 (X τ) y := (hC3 τ).contDiffAt (hO.mem_nhds hy)
    have d1 : DifferentiableAt ℝ (fun y' => deriv (fun t => X t y') τ) y :=
      ((hD τ).2.2).differentiableAt (hO.mem_nhds hy)
    have d2 : DifferentiableAt ℝ (fun y' => fderiv ℝ (X τ) y' y') y :=
      ((hcd.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).clm_apply
        differentiableAt_id
    have d3 : DifferentiableAt ℝ (fun y' => physLap (X τ) y') y := by
      unfold physLap
      exact DifferentiableAt.fun_sum fun j _ =>
        WardCalc.differentiableAt_physPd2 hO (hC3 τ) hy j j
    have d4 : DifferentiableAt ℝ (X τ) y := dX τ y hy
    have hfun : Y τ = fun y' => deriv (fun t => X t y') τ - (1 / 2 : ℝ) • fderiv ℝ (X τ) y' y' -
        L.ν • physLap (X τ) y' + (μ + 1 - 1 / 2) • X τ y' := by
      funext y'
      simp only [hYdef, hXdef, repY, repX, wardY, physDmu]
    rw [hfun]
    exact ((d1.sub (d2.const_smul (1 / 2 : ℝ))).sub (d3.const_smul L.ν)).add
      (d4.const_smul (μ + 1 - 1 / 2))
  have mX : Measurable fun x : ℝ × Space => wemOff X x.1 x.2 := wem_off_meas hXm
  have mpX : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (X τ) j y) x.1 x.2 := fun j => wem_meas_pd mX dX j
  have mp2X : ∀ j l : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd2 (X τ) j l y) x.1 x.2 := fun j l =>
    wem_meas_pd (F := fun τ y => physPd (X τ) l y) (mpX l) (dpX l) j
  have mdt : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 :=
    wem_meas_deriv_tau hXm fun τ y hy => (hD τ).2.1 y hy
  have mfy : Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 :=
    wem_meas_fderiv_apply (V := fun _ y => y) mX measurable_snd dX
  have mY : Measurable fun x : ℝ × Space => wemOff Y x.1 x.2 := by
    have heq : (fun x : ℝ × Space => wemOff Y x.1 x.2) = fun x =>
        wemOff (fun τ y => deriv (fun t => X t y) τ) x.1 x.2 -
          (1 / 2 : ℝ) • wemOff (fun τ y => fderiv ℝ (X τ) y y) x.1 x.2 -
          L.ν • ∑ j : Fin 3, wemOff (fun τ y => physPd2 (X τ) j j y) x.1 x.2 +
          (μ + 1 - 1 / 2) • wemOff X x.1 x.2 := by
      funext x
      by_cases hx : x.2 ∈ axis
      · simp [wemOff, hx]
      · simp only [wem_off_of_not_mem hx, hYdef, hXdef, repY, repX, wardY, physDmu, physLap]
    rw [heq]
    exact ((mdt.sub (mfy.const_smul (1 / 2 : ℝ))).sub
      ((Finset.measurable_sum _ fun j _ => mp2X j j).const_smul L.ν)).add
      (mX.const_smul (μ + 1 - 1 / 2))
  have mpY : ∀ j : Fin 3, Measurable fun x : ℝ × Space =>
      wemOff (fun τ y => physPd (Y τ) j y) x.1 x.2 := fun j => wem_meas_pd mY dY j
  unfold rjOff
  have m1 : Measurable fun x : ℝ × Space =>
      ‖jet1 fun j => wemOff (fun t z => physPd (Y t) j z) x.1 x.2‖ :=
    (continuous_jet1.measurable.comp (measurable_pi_iff.2 fun j => mpY j)).norm
  have m2 : Measurable fun x : ℝ × Space =>
      ∑ j : Fin 3, ‖wemOff (fun t z => physPd (X t) j z) x.1 x.2‖ :=
    Finset.measurable_sum _ fun j _ => (mpX j).norm
  have m3 : Measurable fun x : ℝ × Space =>
      ∑ j : Fin 3, ∑ l : Fin 3, ‖wemOff (fun t z => physPd2 (X t) j l z) x.1 x.2‖ :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ => (mp2X j l).norm
  exact (m1.add m2).add m3

private lemma rj_ringRead_measurable {R : ℝ} {F : ℝ → Space → ℝ}
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2) : Measurable (ringRead R F) := by
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hτ : Measurable fun p : Chart => NearInst.chartTau R p := by
    unfold NearInst.chartTau
    exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
      (Real.measurable_log.comp measurable_fst)
  have hY : Measurable fun p : Chart => NearInst.chartY R p := by
    unfold NearInst.chartY
    exact T8_4.t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
      (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
      (measurable_const.div hsq) measurable_const
      ((measurable_snd.comp measurable_snd).div hsq)
  exact hF.comp (hτ.prodMk hY)

private lemma rj_wardX_periodic (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (τ : ℝ) :
    wardX ν μ R c χy g (τ + 2 * c / R) = wardX ν μ R c χy g τ := by
  have hZ : wardX0 ν μ R c g (τ + 2 * c / R) = wardX0 ν μ R c g τ :=
    funext (wardX0_periodic oldPhysPeriodic ν μ R c g τ)
  funext y
  simp only [wardX, wardStreamCut, outPrim, hZ]

/-- **Leaf 1 (`PartIII-b:C/rep/3/3/1`): chart measurability and lift transfer for `meanJetDens`**
(source 2681-2689, 5259-5268). -/
theorem repJetChartTransfer : RepJetChartTransfer := by
  intro Pl K L μ hχy hμ hC0 hmZ w
  set R : ℝ := L.ε⁻¹ with hRdef
  set c : ℝ := cOf L.ν with hcdef
  set X := repX Pl K L μ w with hXdef
  set Y := repY Pl K L μ w with hYdef
  have hν : 0 < L.ν := L.ν_pos
  have hR : 0 < R := inv_pos.2 L.ε_pos
  have hc : 0 < c := cOf_pos hν
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set g : Chart → ℝ := ringRead R (rjOff X Y) with hgdef
  have hgm : Measurable g :=
    rj_ringRead_measurable (rjOff_measurable hχy hμ hC0 hmZ w)
  have hge_age : ringRead R (fun τ => meanJetDens (X τ) (Y τ)) =ᵐ[ageμ c (-5 / 2)] g := by
    filter_upwards [ae_ageμ_mem hc (-5 / 2)] with p hp
    have hs : 0 < p.1 := hp.1
    have hy : NearInst.chartY R p ∉ axis := by
      intro h
      have h' : NearInst.chartY R p 0 = 0 ∧ NearInst.chartY R p 1 = 0 := h
      have h1 : NearInst.chartY R p 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
      have hne : R / Real.sqrt p.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hs).ne'
      exact hne (h1 ▸ h'.1)
    unfold g ringRead
    exact (rjOff_eq_of_not_mem X Y (NearInst.chartTau R p) hy).symm
  have hge : ringRead R (fun τ => meanJetDens (X τ) (Y τ)) =ᵐ[ringPhysμ R c] g := by
    unfold ringPhysμ
    exact Measure.ae_smul_measure hge_age _
  refine ⟨hgm.aestronglyMeasurable.congr hge.symm, ?_⟩
  intro B hB
  set q : ℝ := 22 / 3 with hqdef
  have hq0 : 0 < q := by rw [hqdef]; norm_num
  have hp0 : (22 / 3 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt_top : (22 / 3 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hpR : (22 / 3 : ℝ≥0∞).toReal = q := by
    rw [ENNReal.toReal_div, hqdef]; norm_num
  set G : Chart → ℝ≥0∞ := fun p => ‖g p‖ₑ ^ q with hGdef
  have hGm : Measurable G := hgm.enorm.pow_const q
  have hL : eLpNorm (ringRead R fun τ => meanJetDens (X τ) (Y τ)) (22 / 3) (ringPhysμ R c) =
      (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) ^ (1 / q) := by
    rw [eLpNorm_congr_ae hge, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt_top, hpR,
      ringPhysμ, lintegral_smul_measure]
    rfl
  have hperX : Function.Periodic X (2 * c / R) :=
    fun τ => rj_wardX_periodic L.ν μ R c K.χy (repSrcTen Pl K L w) τ
  have hperY : Function.Periodic Y (2 * c / R) :=
    fun τ => vr_wardY_periodic L.ν μ R c K.χy (repSrcTen Pl K L w) τ
  have hpt : ∀ (τ : ℝ) (z : Space), z ∉ axis →
      G (NearInst.chartOf R c z τ) =
        ENNReal.ofReal (meanJetDens (X τ) (Y τ) !₂[ϱ z, 0, z 2]) ^ q := by
    intro τ z hz
    have hρ : 0 < NearInst.hRad z := by
      have h1 : ϱ z ≠ 0 := fun h => hz ((mem_axis_iff z).2 h)
      exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h1)
    have hmerid_not_axis : (!₂[ϱ z, 0, z 2] : Space) ∉ axis := by
      intro h
      have h' : (!₂[ϱ z, 0, z 2] : Space) 0 = 0 ∧ (!₂[ϱ z, 0, z 2] : Space) 1 = 0 := h
      exact hz ((mem_axis_iff z).2 h'.1)
    have hYo : NearInst.chartY R (NearInst.chartOf R c z τ) = !₂[ϱ z, 0, z 2] :=
      chartYOf_proved R c z τ hR hρ
    have hTo := chartTauOf_proved R c z τ hR.ne'
    have hg_eq : g (NearInst.chartOf R c z τ) = meanJetDens (X τ) (Y τ) !₂[ϱ z, 0, z 2] := by
      show rjOff X Y (NearInst.chartTau R (NearInst.chartOf R c z τ))
          (NearInst.chartY R (NearInst.chartOf R c z τ)) = _
      rw [hYo, rjOff_eq_of_not_mem X Y _ hmerid_not_axis, hTo, hperX.sub_int_mul_eq,
        hperY.sub_int_mul_eq]
    simp only [hGdef, hg_eq]
    congr 1
    rw [← ofReal_norm, Real.norm_of_nonneg (meanJetDens_nonneg (X τ) (Y τ) _)]
  have hslice : ∀ τ : ℝ, ∫⁻ z : Space, G (NearInst.chartOf R c z τ) ≤ B ^ q := by
    intro τ
    have heq : ∫⁻ z : Space, G (NearInst.chartOf R c z τ) =
        ∫⁻ z : Space, ENNReal.ofReal (meanJetDens (X τ) (Y τ) !₂[ϱ z, 0, z 2]) ^ q :=
      lintegral_congr_ae (ae_not_mem_axis.mono fun z hz => hpt τ z hz)
    rw [heq]
    have h1 := ENNReal.rpow_le_rpow (hB τ) hq0.le
    unfold lqNorm at h1
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at h1
    exact h1
  have hCP := chartPhaseLIntegral R c hR hc G hGm
  have hInt : ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
      ∫⁻ p, G p ∂(ageμ c (-5 / 2)) ≤ B ^ q * ENNReal.ofReal (2 * c / R) := by
    rw [← hCP]
    calc ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z : Space, G (NearInst.chartOf R c z τ)
        ≤ ∫⁻ _ in Ioc 0 (2 * c / R), B ^ q := lintegral_mono fun τ => hslice τ
      _ = B ^ q * ENNReal.ofReal (2 * c / R) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hinv : ENNReal.ofReal (2 * c / R)⁻¹ * ENNReal.ofReal (2 * c / R) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos hP0]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hP0).ne' ENNReal.ofReal_ne_top
  have hM : ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2)) ≤ B ^ q := by
    calc ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))
        = (ENNReal.ofReal (2 * c / R)⁻¹ * ENNReal.ofReal (2 * c / R)) *
            (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal (2 * c / R)⁻¹ *
            (ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
              ∫⁻ p, G p ∂(ageμ c (-5 / 2))) := by ring
      _ ≤ ENNReal.ofReal (2 * c / R)⁻¹ * (B ^ q * ENNReal.ofReal (2 * c / R)) :=
          mul_le_mul_of_nonneg_left hInt zero_le
      _ = (ENNReal.ofReal (2 * c / R)⁻¹ * ENNReal.ofReal (2 * c / R)) * B ^ q := by ring
      _ = B ^ q := by rw [hinv, one_mul]
  rw [hL]
  calc (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) ^ (1 / q)
      ≤ (B ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hM (by positivity)
    _ = B := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

end UnforcedLeray.Short.PartIIIb.Concrete

end
