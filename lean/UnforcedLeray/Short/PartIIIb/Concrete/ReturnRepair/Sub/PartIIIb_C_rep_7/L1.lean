import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV

/-!
# `newtonVCutBound` (PartIII-b:C/rep/7/1, source 4776-4782, 4870-4900, 4917-4937)

The cut version of `newtonVRegionBound`: the old moment is `oldN0cut`, which keeps the
outward cutoff `χ_o(νu)` inside the moment.  The bound on `∫|Σ_M|` is proved with the same
chain as `sigmaM_lintegral_le`, but the final step uses `B(u) = χ_o(νu) ∫|M|`, which vanishes
for `u ≤ 6/(5ν)`, so the `u`-integral is over `Ioi (6/5/ν)` and equals `oldN0cut`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `oldN0cut` is the integral of `u^{-3/2} B(u)` over `Ioi (6/5/ν)`, `B = phaseB`. -/
theorem oldN0cut_eq_phaseB_integral (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) :
    oldN0cut c ν χo M =
      ∫ u in Ioi (6 / 5 / ν), u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u := rfl

/-- The lower-integral of `u^{-3/2} B(u)` over `(0,∞)` is `ofReal (oldN0cut)`. -/
theorem phaseB_lintegral_eq_cut (c ν : ℝ) (hν : 0 < ν) {χo : ℝ → ℝ} (hχ : IsOutwardCutoff χo)
    (M : Chart → Mat3)
    (hmeas : AEMeasurable (phaseB c ν χo M) (volume.restrict (Ioi (0 : ℝ))))
    (hfin : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) < ⊤) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) =
      ENNReal.ofReal (oldN0cut c ν χo M) := by
  have hpos : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (Set.mem_Ioi.mp hu)) _) (phaseB_nonneg c ν hχ M u)
  have hint : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine ⟨?_, ?_⟩
    · exact ((measurable_id.pow_const _).aemeasurable.mul hmeas).aestronglyMeasurable
    · exact (hasFiniteIntegral_iff_ofReal hpos).2 hfin
  have hsub : Ioi (6 / 5 / ν) ⊆ Ioi (0 : ℝ) :=
    Ioi_subset_Ioi (div_nonneg (by norm_num) hν.le)
  have hzero : ∀ x ∈ Ioi (0 : ℝ) \ Ioi (6 / 5 / ν),
      x ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M x = 0 := by
    intro x hx
    have hx' : x ≤ 6 / 5 / ν := not_lt.mp hx.2
    have hcut : χo (ν * x) = 0 := hχ.zero _ (by
      rw [mul_comm]
      exact (le_div_iff₀ hν).1 hx')
    simp [phaseB, hcut]
  have key : ∫ u in Ioi (0 : ℝ), u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u =
      oldN0cut c ν χo M :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hzero).trans rfl
  refine (ofReal_integral_eq_lintegral_ofReal hint hpos).symm.trans ?_
  congr 1

/-- The lintegral bound `∫⁻ |Σ_M| ≤ ofReal(π oldN0cut)`, by the chain of `sigmaM_lintegral_le`. -/
theorem sigmaM_frob_integral_cut (c ν : ℝ) (χo : ℝ → ℝ) (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x')) ≤
      ENNReal.ofReal (Real.pi * oldN0cut c ν χo M) := by
  obtain ⟨hmeas, hint⟩ := phaseBInt c ν χo hc hν hχ M hM
  have hfin : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) < ⊤ :=
    lt_of_le_of_lt hint ENNReal.ofReal_lt_top
  calc ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))
      ≤ ∫⁻ x' : ℝ × ℝ, ENNReal.ofReal ((Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2))⁻¹ *
          phaseB c ν χo M ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹)) :=
        lintegral_mono_ae ((sigmaPointwise c ν χo hc hν hχ M hM).mono
          fun x' h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) * phaseB c ν χo M u) :=
        planePolar _ (phaseB_nonneg c ν hχ M) hmeas
    _ = ENNReal.ofReal Real.pi * ENNReal.ofReal (oldN0cut c ν χo M) := by
        rw [phaseB_lintegral_eq_cut c ν hν hχ M hmeas hfin]
    _ = ENNReal.ofReal (Real.pi * oldN0cut c ν χo M) :=
        (ENNReal.ofReal_mul Real.pi_pos.le).symm

/-- `∫ |Σ_M| ≤ π oldN0cut` (the real form). -/
theorem sigmaM_l1_cut (c ν : ℝ) (χo : ℝ → ℝ) (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (M : Chart → Mat3) (hM : OldThinFinite c ν M) :
    ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') ≤ Real.pi * oldN0cut c ν χo M := by
  have hS := sigmaMeas c ν χo hc hν hχ M hM
  have hL := sigmaM_frob_integral_cut c ν χo hc hν hχ M hM
  have hN0 := oldN0cut_nonneg c ν hν hχ M
  have hfin' : (∫⁻ x' : ℝ × ℝ, ENNReal.ofReal (frob (sigmaM c ν χo M x'))) < ⊤ :=
    lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  have hg : Integrable (fun x' : ℝ × ℝ => frob (sigmaM c ν χo M x')) :=
    ⟨continuous_frob.comp_aestronglyMeasurable hS,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => frob_nonneg' _)).2 hfin'⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => frob_nonneg' _)
    hg.aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal (Real.pi * oldN0cut c ν χo M)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hL
    _ = Real.pi * oldN0cut c ν χo M := ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le hN0)

open NewtonVGeom in
/-- **Lemma 1 (Newton field on the receiver region, cut moment)**: the `oldN0cut` version of
`newtonVRegionBound`, with the same parametric-integral argument. -/
theorem newtonVCutBound (χo : ℝ → ℝ) : UnforcedLeray.Short.PartIIIb.Concrete.NewtonVCutBound χo := by
  choose K hK0 hK using NewtonVGeom.Fker_bound
  refine ⟨fun n => K n * Real.pi, ?_⟩
  intro c ν μ hc hν hχ hμ M hM
  obtain ⟨-, hint, -⟩ := sigmaM_l1 c ν χo hc hν hχ M hM
  have hl1 := sigmaM_l1_cut c ν χo hc hν hχ M hM
  have hopen := isOpen_regU ν
  have hsm : ∀ᵐ a ∂mu2, ContDiffOn ℝ NewtonD3.ii (Fker c ν μ χo M a)
      {w | ν * (11 / 12) < eucSq w} := by
    filter_upwards [ae_good] with a ha
    exact contDiffOn_Fker hν hχ M ha.1.le ha.2
  have hmeas : ∀ (n : ℕ), ∀ x ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (Fker c ν μ χo M a) x) mu2 :=
    fun n x hx => aesm_iter_Fker n hν hχ M hint.aestronglyMeasurable hx
  have hdom := locDominated_Fker hν hχ hμ M hint
  have heq : ∀ y ∈ {w : Vec3 | ν * (11 / 12) < eucSq w},
      newtonV c ν μ χo M y = ∫ a, Fker c ν μ χo M a y ∂mu2 :=
    fun y hy => newtonV_eq_integral hν hχ hμ M hint hy
  have hcd := UnforcedLeray.L09.contDiffOn_integral hopen hsm hmeas hdom
  have hnv : ContDiffOn ℝ NewtonD3.ii (newtonV c ν μ χo M) {w | ν * (11 / 12) < eucSq w} :=
    hcd.congr heq
  refine ⟨hnv.of_le (by simp [NewtonD3.ii]), fun m _ w hw => ?_⟩
  have hEv : newtonV c ν μ χo M =ᶠ[nhds w] fun y => ∫ a, Fker c ν μ χo M a y ∂mu2 := by
    filter_upwards [hopen.mem_nhds hw] with y hy using heq y hy
  rw [(hEv.iteratedFDeriv ℝ m).eq_of_nhds]
  refine (UnforcedLeray.L09.norm_iteratedFDeriv_integral_le hopen hsm hmeas hdom m hw).trans ?_
  set P := (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hr : ∫ a, ‖iteratedFDeriv ℝ m (Fker c ν μ χo M a) w‖ ∂mu2 ≤
      ∫ a, (K m * P) * frob (sigmaM c ν χo M a.2) ∂mu2 := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun a => norm_nonneg _)
      (integrable_const_frob _ hint) ?_
    filter_upwards [ae_good] with a ha
    have := hK m c ν μ χo M hν hχ hμ a ha.1.le ha.2 w hw
    calc _ ≤ _ := this
      _ = _ := by ring
  have hc' : ∫ a, (K m * P) * frob (sigmaM c ν χo M a.2) ∂mu2 =
      K m * P * ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x') := by
    have := integral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (ν := (volume : Measure (ℝ × ℝ))) (fun _ => (1 : ℝ))
      (fun x' => K m * P * frob (sigmaM c ν χo M x'))
    have e1 : (fun z : ℝ × (ℝ × ℝ) => (fun _ : ℝ => (1 : ℝ)) z.1 *
        (fun x' : ℝ × ℝ => K m * P * frob (sigmaM c ν χo M x')) z.2) =
        fun a => K m * P * frob (sigmaM c ν χo M a.2) := by
      funext a; simp
    rw [e1] at this
    rw [this, integral_const_mul]
    simp
  refine hr.trans (hc'.le.trans ?_)
  calc K m * P * ∫ x' : ℝ × ℝ, frob (sigmaM c ν χo M x')
      ≤ K m * P * (Real.pi * oldN0cut c ν χo M) :=
        mul_le_mul_of_nonneg_left hl1 (mul_nonneg (hK0 m) hP0)
    _ = K m * Real.pi * oldN0cut c ν χo M * P := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
