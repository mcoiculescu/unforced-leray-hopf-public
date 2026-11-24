import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_1.SigmaW
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonV

/-!
# Zero-width Newton field with the cut moment (`PartIII-b:C/rep/6/1`, source 4776-4782, 4917-4937)

Copy of `newtonVRegionBound` (`SourceL/Ambient/NewtonV.lean`) in which the `L¹` input
`sigmaM_l1` is replaced by `sigmaM_l1W`, so the bound carries `oldN0w` in place of `oldN0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Axi
open scoped Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The zero-width Newton field bound with the cut moment `oldN0w`. -/
def NewtonVRegionBoundW (χo : ℝ → ℝ) : Prop :=
  ∃ C : ℕ → ℝ, ∀ (c ν μ : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo → 0 ≤ μ →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ContDiffOn ℝ 7 (newtonV c ν μ χo M) {w | ν * (11 / 12) < eucSq w} ∧
      ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
        ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ ≤
          C m * oldN0w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)

open NewtonVGeom in
/-- Source 4776-4782, 4870-4900, 4917-4937 with the cut moment. -/
theorem newtonVRegionBoundW (χo : ℝ → ℝ) : NewtonVRegionBoundW χo := by
  choose K hK0 hK using NewtonVGeom.Fker_bound
  refine ⟨fun n => K n * Real.pi, ?_⟩
  intro c ν μ hc hν hχ hμ M hM
  obtain ⟨-, hint, hl1⟩ := sigmaM_l1W c ν χo hc hν hχ M hM
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
      ≤ K m * P * (Real.pi * oldN0w c ν χo M) :=
        mul_le_mul_of_nonneg_left hl1 (mul_nonneg (hK0 m) hP0)
    _ = K m * Real.pi * oldN0w c ν χo M * P := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
