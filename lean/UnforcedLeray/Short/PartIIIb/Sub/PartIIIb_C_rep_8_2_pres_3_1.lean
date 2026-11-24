import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3

/-!
# `presFlatMeas` (`PartIII-b:C/rep/8/2/pres/3/1`)

Source `the November 2 reference manuscript`,
lines 1205-1225 (`liftP = s p_cyl` is smooth off the axis) and the profile `IsActualLevel.profile`
(`IsExactProfile` of `L.pres`).  Measurability of `τ ↦ presChgDens (L.pres τ) (liftP L τ)` in the
ring chart: the density is continuous on the off-axis set of `ℝ × Space`, and the chart map
`p ↦ (chartTau p, chartY p)` is continuous on `{0 < p.1}`, which carries `ringPhysμ`-almost every
point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The off-axis part of `ℝ × Space` (open). -/
def offAxisSet : Set (ℝ × Space) := {x | x.2 ∉ axis}

theorem isOpen_offAxisSet : IsOpen offAxisSet :=
  isOpen_compl_axis.preimage continuous_snd

theorem physGrad_partial_eq {F : ℝ × Space → ℝ} {x : ℝ × Space}
    (hF : DifferentiableAt ℝ F x) (v : Space) :
    fderiv ℝ (fun y => F (x.1, y)) x.2 v = fderiv ℝ F x (0, v) := by
  have hg : HasFDerivAt (fun y : Space => (x.1, y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hc : HasFDerivAt (fun y : Space => F (x.1, y))
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x.2 :=
    HasFDerivAt.comp x.2 hF.hasFDerivAt hg
  rw [hc.fderiv]
  rfl

theorem physGrad_continuousOn {F : ℝ × Space → ℝ} (hF : ContDiffOn ℝ ∞ F offAxisSet) :
    ContinuousOn (fun x : ℝ × Space => physGrad (fun y => F (x.1, y)) x.2) offAxisSet := by
  have hcont : ContinuousOn (fun x => fderiv ℝ F x) offAxisSet :=
    hF.continuousOn_fderiv_of_isOpen isOpen_offAxisSet (by simp)
  have hG : ContinuousOn (fun x : ℝ × Space =>
      (WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ F x (0, coordinateVector j)) : Space))
      offAxisSet := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn ?_
    refine continuousOn_pi.2 fun j => ?_
    exact hcont.clm_apply continuousOn_const
  refine hG.congr fun x hx => ?_
  have hd : DifferentiableAt ℝ F x :=
    (hF.contDiffAt (isOpen_offAxisSet.mem_nhds hx)).differentiableAt (by simp)
  unfold physGrad
  congr 1
  funext j
  exact physGrad_partial_eq hd (coordinateVector j)

theorem liftP_contDiffOn (L : ReturnLevel) (hε : 0 < L.ε) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Space => liftP L x.1 x.2) offAxisSet := by
  have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hϱ : ContDiffOn ℝ ∞ (fun x : ℝ × Space => ϱ x.2) offAxisSet :=
    contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => age L.ε⁻¹ x.2) offAxisSet := by
    have e : (fun x : ℝ × Space => age L.ε⁻¹ x.2) = fun x => L.ε⁻¹ ^ 2 / ϱ x.2 ^ 2 := rfl
    rw [e]
    exact contDiffOn_const.div (hϱ.pow 2) (fun x hx => pow_ne_zero 2 (ϱ_ne_zero (y := x.2) hx))
  have htrans : ContDiffOn ℝ ∞ (fun x : ℝ × Space => trans L.ε⁻¹ x.2) offAxisSet := by
    have e : (fun x : ℝ × Space => trans L.ε⁻¹ x.2) = fun x => L.ε⁻¹ * x.2 2 / ϱ x.2 := rfl
    rw [e]
    have h2 : ContDiff ℝ ∞ (fun y : Space => y 2) := by fun_prop
    have h2c : ContDiffOn ℝ ∞ (fun x : ℝ × Space => x.2 2) offAxisSet :=
      (h2.comp contDiff_snd).contDiffOn
    exact (contDiffOn_const.mul h2c).div hϱ (fun x hx => ϱ_ne_zero (y := x.2) hx)
  have hlogage : ContDiffOn ℝ ∞ (fun x : ℝ × Space => Real.log (age L.ε⁻¹ x.2)) offAxisSet :=
    hage.log (fun x hx => (age_pos hR (y := x.2) hx).ne')
  have hphase : ContDiffOn ℝ ∞ (fun x : ℝ × Space => phase L.ε⁻¹ x.1 x.2) offAxisSet := by
    have e : (fun x : ℝ × Space => phase L.ε⁻¹ x.1 x.2) =
        fun x => L.ε⁻¹ * x.1 / 2 - (L.ε⁻¹ / 2) * Real.log (age L.ε⁻¹ x.2) := rfl
    rw [e]
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × Space => L.ε⁻¹ * x.1 / 2) offAxisSet :=
      (contDiffOn_const.mul contDiffOn_fst).div_const 2
    exact h1.sub (((contDiffOn_const (c := L.ε⁻¹)).div_const 2).mul hlogage)
  have hPc : ∀ z : ℝ × (ℝ × ℝ), 0 < z.1 →
      ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => L.train.p z.1 z.2) z := by
    intro z hz
    have hn : (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (ℝ × ℝ))) ∈ nhds z :=
      prod_mem_nhds (Ici_mem_nhds hz) Filter.univ_mem
    exact L.train.isTrain.smooth_p.contDiffAt hn
  have hQ : ContDiffOn ℝ ∞
      (fun x : ℝ × Space => (age L.ε⁻¹ x.2, (phase L.ε⁻¹ x.1 x.2, trans L.ε⁻¹ x.2)))
      offAxisSet :=
    hage.prodMk (hphase.prodMk htrans)
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  have hQa : ContDiffAt ℝ ∞
      (fun x : ℝ × Space => (age L.ε⁻¹ x.2, (phase L.ε⁻¹ x.1 x.2, trans L.ε⁻¹ x.2))) x :=
    hQ.contDiffAt (isOpen_offAxisSet.mem_nhds hx)
  have hpos : 0 < (age L.ε⁻¹ x.2, (phase L.ε⁻¹ x.1 x.2, trans L.ε⁻¹ x.2)).1 :=
    age_pos hR (y := x.2) hx
  have hPa := (hPc _ hpos).comp x hQa
  have hA : ContDiffAt ℝ ∞ (fun x : ℝ × Space => age L.ε⁻¹ x.2) x :=
    hage.contDiffAt (isOpen_offAxisSet.mem_nhds hx)
  exact hA.mul hPa

theorem chartY_offAxis {R : ℝ} (hR : 0 < R) (p : Chart) (hp : 0 < p.1) :
    NearInst.chartY R p ∉ axis := by
  intro h
  have h0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := by simp [NearInst.chartY]
  have h1 : (NearInst.chartY R p) 1 = 0 := by simp [NearInst.chartY]
  have hpos : 0 < R / Real.sqrt p.1 := div_pos hR (Real.sqrt_pos.2 hp)
  have hρ : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ
    rw [h0, h1, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hpos.le]
  exact hpos.ne' ((hρ ▸ (mem_axis_iff _).1 h))

theorem presFlat_meas_of (L : ReturnLevel) (hε : 0 < L.ε)
    (hP : ContDiff ℝ ∞ (fun x : ℝ × Space => L.pres x.1 x.2)) :
    AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (liftP L τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
  set R : ℝ := L.ε⁻¹ with hRdef
  have hR : 0 < R := inv_pos.2 hε
  set A : Set Chart := {p | 0 < p.1} with hAdef
  set G : ℝ × Space → ℝ := fun x => presChgDens (L.pres x.1) (liftP L x.1) x.2 with hGdef
  have hGc : ContinuousOn G offAxisSet := by
    have h1 := physGrad_continuousOn (F := fun x => L.pres x.1 x.2)
      (hP.contDiffOn.mono (subset_univ _))
    have h2 := physGrad_continuousOn (F := fun x => liftP L x.1 x.2) (liftP_contDiffOn L hε)
    exact (h1.sub h2).norm
  have hae : ∀ᵐ p ∂(ringPhysμ R (cOf L.ν)), p ∈ A := by
    unfold ringPhysμ
    exact Measure.ae_smul_measure (ae_ageμ_fst_pos _ _) _
  have hτ : ContinuousOn (fun p : Chart => NearInst.chartTau R p) A := by
    have hlog : ContinuousOn (fun p : Chart => Real.log p.1) A :=
      continuous_fst.continuousOn.log (fun p hp => hp.ne')
    unfold NearInst.chartTau
    exact (((continuous_const.mul (continuous_fst.comp continuous_snd)).div_const R).continuousOn).add hlog
  have hY : ContinuousOn (fun p : Chart => NearInst.chartY R p) A := by
    unfold NearInst.chartY
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
      (continuousOn_pi.2 fun i => ?_)
    have hsq : ContinuousOn (fun p : Chart => Real.sqrt p.1) A :=
      (Real.continuous_sqrt.comp continuous_fst).continuousOn
    have hsqne : ∀ p ∈ A, Real.sqrt p.1 ≠ 0 := fun p hp => (Real.sqrt_pos.2 hp).ne'
    fin_cases i
    · show ContinuousOn (fun p : Chart => R / Real.sqrt p.1) A
      exact continuousOn_const.div hsq hsqne
    · show ContinuousOn (fun _ : Chart => (0 : ℝ)) A
      exact continuousOn_const
    · show ContinuousOn (fun p : Chart => p.2.2 / Real.sqrt p.1) A
      exact (continuous_snd.snd.continuousOn).div hsq hsqne
  have hφ : ContinuousOn (fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p)) A :=
    hτ.prodMk hY
  have hmaps : MapsTo (fun p : Chart => (NearInst.chartTau R p, NearInst.chartY R p)) A
      offAxisSet := fun p hp => chartY_offAxis hR p hp
  have hcomp : ContinuousOn (fun p : Chart => G (NearInst.chartTau R p, NearInst.chartY R p)) A :=
    hGc.comp hφ hmaps
  have hAmeas : MeasurableSet A := measurableSet_lt measurable_const measurable_fst
  have hres : AEStronglyMeasurable (fun p : Chart => G (NearInst.chartTau R p, NearInst.chartY R p))
      ((ringPhysμ R (cOf L.ν)).restrict A) :=
    ContinuousOn.aestronglyMeasurable (μ := ringPhysμ R (cOf L.ν)) hcomp hAmeas
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact hres

theorem presFlatMeas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    PresFlatMeas D := by
  filter_upwards [hst.actual] with n hn
  exact presFlat_meas_of (D.level n) (D.level n).ε_pos hn.profile.smoothP

end UnforcedLeray.Short.PartIIIb.Concrete
