import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerVelConv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace KerVelPairAux

theorem cell_eq' (d : ℝ) : B0579.cell d = Cyl.cell d := by
  unfold B0579.cell Cyl.cell
  rw [neg_div]

/-- A translate of a cylinder test by `z` is a cylinder test. -/
theorem transl_test {d : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) (z : ℝ × ℝ) :
    B0579.IsCylTest d (fun x => ψ (x - z)) where
  smooth := hψ.smooth.comp (contDiff_id.sub contDiff_const)
  periodic x := by
    have e : (x.1 + d, x.2) - z = ((x - z).1 + d, (x - z).2) := by
      ext <;> simp <;> ring
    show ψ ((x.1 + d, x.2) - z) = ψ (x - z)
    rw [e]
    exact hψ.periodic (x - z)
  band := by
    obtain ⟨R, hR⟩ := hψ.band
    refine ⟨R + |z.2|, fun x hx => ?_⟩
    show ψ (x - z) = 0
    apply hR
    rw [Prod.snd_sub]
    linarith [abs_sub_abs_le_abs_sub x.2 z.2]

/-- The derivative of a translate: `∂_j (ψ(· - z)) = (∂_jψ)(· - z)`. -/
theorem transl_pd (ψ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (j : Fin 2) :
    B0579.pd j (fun x => ψ (x - z)) = fun x => B0579.pd j ψ (x - z) := by
  funext x
  unfold B0579.pd
  rw [fderiv_comp_sub]

/-- The kernel bound at a transported test, in the form `z ↦ K(z) φ(x - z)` on the cell (copy of
the near/far estimate of `kernel_test_bound`, with the periodic change of variables already made). -/
theorem zform_bound {d : ℝ} (hd : 1 ≤ d) {C B : ℝ}
    (hnear : (∫⁻ z in B0579.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ j, ‖kerD d z j‖ₑ) ≤
      ENNReal.ofReal C)
    (hfar : ∀ z ∈ B0579.cell d, z ∉ Metric.ball (0 : ℝ × ℝ) 1 → ∀ j, |kerD d z j| ≤ C)
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ) (hB : ∀ y, |φ y| ≤ B) (j : Fin 2)
    (x : ℝ × ℝ) :
    ∫⁻ z in B0579.cell d, ‖kerD d z j‖ₑ * ‖φ (x - z)‖ₑ ≤
      ENNReal.ofReal B * ENNReal.ofReal C +
        ENNReal.ofReal C * ∫⁻ y in Cyl.cell d, ‖φ y‖ₑ := by
  have hd0 : 0 < d := by linarith
  rw [cell_eq'] at hnear hfar ⊢
  have hψper : Cyl.IsPeriodic d φ := hφ.periodic
  have hψper' : Cyl.IsPeriodic d (fun y : ℝ × ℝ => ‖φ y‖ₑ) := fun z => by
    simp only [hψper z]
  have hmb : MeasurableSet (Metric.ball (0 : ℝ × ℝ) 1) := Metric.isOpen_ball.measurableSet
  rw [← lintegral_inter_add_diff _ _ hmb]
  gcongr
  · calc ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d w j‖ₑ * ‖φ (x - w)‖ₑ
        ≤ ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1,
            ENNReal.ofReal B * ∑ i, ‖kerD d w i‖ₑ := by
          refine setLIntegral_mono' ((Cyl.measurableSet_cell d).inter hmb) fun w _ => ?_
          rw [mul_comm (ENNReal.ofReal B)]
          refine mul_le_mul' ?_ ?_
          · exact Finset.single_le_sum (f := fun i => ‖kerD d w i‖ₑ) (fun _ _ => bot_le)
              (Finset.mem_univ j)
          · rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_ofReal (hB _)
      _ = ENNReal.ofReal B * ∫⁻ w in Cyl.cell d ∩ Metric.ball (0 : ℝ × ℝ) 1, ∑ i, ‖kerD d w i‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  · calc ∫⁻ w in Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1, ‖kerD d w j‖ₑ * ‖φ (x - w)‖ₑ
        ≤ ∫⁻ w in Cyl.cell d \ Metric.ball (0 : ℝ × ℝ) 1, ENNReal.ofReal C * ‖φ (x - w)‖ₑ := by
          refine setLIntegral_mono' ((Cyl.measurableSet_cell d).diff hmb) fun w hw => ?_
          gcongr
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hfar w hw.1 hw.2 j)
      _ ≤ ∫⁻ w in Cyl.cell d, ENNReal.ofReal C * ‖φ (x - w)‖ₑ :=
          lintegral_mono_set diff_subset
      _ = ENNReal.ofReal C * ∫⁻ w in Cyl.cell d, ‖φ (x - w)‖ₑ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
          rw [Cyl.lintegral_cell_comp_sub_left hd0 (G := fun y => ‖φ y‖ₑ) hψper' x]

/-- Integrability on the product of the cell with the transported kernel and test. -/
theorem prodInt_of {d : ℝ} (l : Fin 2) (hmK : Measurable fun z => kerD d z l) {M : ℝ≥0∞}
    (hM : M ≠ ⊤) {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F (B0579.cell d))
    {φ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest d φ)
    (hbd : ∀ x : ℝ × ℝ, ∫⁻ z in B0579.cell d, ‖kerD d z l‖ₑ * ‖φ (x - z)‖ₑ ≤ M) :
    Integrable (Function.uncurry fun x z => F x * (((kerD d z l : ℝ) : ℂ) * ((φ (x - z) : ℝ) : ℂ)))
      ((volume.restrict (B0579.cell d)).prod (volume.restrict (B0579.cell d))) := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (B0579.cell d) with hμ
  have hF1 : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F p.1) (μ.prod μ) :=
    hF.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hK2 : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((kerD d p.2 l : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hmK.comp measurable_snd)
  have hφ2 : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((φ (p.1 - p.2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_fst.sub continuous_snd))
  have hsm : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F p.1 * (((kerD d p.2 l : ℝ) : ℂ) * ((φ (p.1 - p.2) : ℝ) : ℂ)))
      (μ.prod μ) :=
    hF1.mul (hK2.aestronglyMeasurable.mul hφ2.aestronglyMeasurable)
  refine ⟨hsm, ?_⟩
  show ∫⁻ p, ‖F p.1 * (((kerD d p.2 l : ℝ) : ℂ) * ((φ (p.1 - p.2) : ℝ) : ℂ))‖ₑ ∂(μ.prod μ) < ⊤
  rw [lintegral_prod _ hsm.enorm]
  calc ∫⁻ x, ∫⁻ z, ‖F x * (((kerD d z l : ℝ) : ℂ) * ((φ (x - z) : ℝ) : ℂ))‖ₑ ∂μ ∂μ
      ≤ ∫⁻ x, ‖F x‖ₑ * M ∂μ := by
        refine lintegral_mono fun x => ?_
        calc ∫⁻ z, ‖F x * (((kerD d z l : ℝ) : ℂ) * ((φ (x - z) : ℝ) : ℂ))‖ₑ ∂μ
            = ‖F x‖ₑ * ∫⁻ z, ‖kerD d z l‖ₑ * ‖φ (x - z)‖ₑ ∂μ := by
              rw [← lintegral_const_mul' (‖F x‖ₑ) _ enorm_ne_top]
              refine lintegral_congr fun z => ?_
              simp only [enorm_mul, AdjFubiniAux.enorm_ofReal_complex]
          _ ≤ ‖F x‖ₑ * M := by gcongr; exact hbd x
    _ = (∫⁻ x, ‖F x‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hM
    _ < ⊤ := ENNReal.mul_lt_top hF.2 hM.lt_top

end KerVelPairAux

open KerVelPairAux

/-- **(15) Integration by parts against the kernel velocity** (SP 3052-3058): the weak
derivative passes through the kernel velocity by Fubini on the cell and the translation of the
test, `∂_j(ψ(· - z)) = (∂_jψ)(· - z)`. -/
theorem kerVelPairDeriv : KerVelPairDeriv := by
  intro d hd j F G hF hG hW ψ hψ l
  have hd0 : 0 < d := by linarith
  obtain ⟨C, hC0, hC⟩ := kerNearFar
  obtain ⟨hmeas, -, -, hnear, hfar⟩ := hC d hd
  have hmK : Measurable fun z => kerD d z l := hmeas l
  -- convolution form of the kernel velocity, complex valued
  have hKV : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∀ x : ℝ × ℝ,
      ((kerVel d φ x l : ℝ) : ℂ) = ∫ z in B0579.cell d,
        ((kerD d z l : ℝ) : ℂ) * ((φ (x - z) : ℝ) : ℂ) := by
    intro φ hφ x
    rw [kerVelConv d hd φ hφ x l, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Complex.ofReal_mul]
  -- the weak derivative tested against the translate `ψ(· - z)`
  have hWz : ∀ z : ℝ × ℝ,
      (∫ x in B0579.cell d, F x * ((B0579.pd j ψ (x - z) : ℝ) : ℂ)) =
        -(∫ x in B0579.cell d, G x * ((ψ (x - z) : ℝ) : ℂ)) := by
    intro z
    have h := hW.2 (fun x => ψ (x - z)) (KerVelPairAux.transl_test hψ z)
    rw [KerVelPairAux.transl_pd ψ z j] at h
    exact h
  -- uniform bounds of the transported kernel integrals
  have hbdd : ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest d φ → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ x : ℝ × ℝ, ∫⁻ z in B0579.cell d, ‖kerD d z l‖ₑ * ‖φ (x - z)‖ₑ ≤ M := by
    intro φ hφ
    obtain ⟨B, hB0, hB, hL⟩ := AdjFubiniAux.test_facts hd0 hφ
    refine ⟨ENNReal.ofReal B * ENNReal.ofReal C +
      ENNReal.ofReal C * ∫⁻ y in Cyl.cell d, ‖φ y‖ₑ, ?_,
      fun x => KerVelPairAux.zform_bound hd hnear hfar hφ hB l x⟩
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL⟩).ne
  obtain ⟨M1, hM1, hb1⟩ := hbdd (B0579.pd j ψ) (hψ.pd j)
  obtain ⟨M2, hM2, hb2⟩ := hbdd ψ hψ
  have hI1 := KerVelPairAux.prodInt_of l hmK hM1 hF (hψ.pd j) hb1
  have hI2 := KerVelPairAux.prodInt_of l hmK hM2 hG hψ hb2
  have hL : ∫ x in B0579.cell d, F x * ((kerVel d (B0579.pd j ψ) x l : ℝ) : ℂ) =
      ∫ x in B0579.cell d, ∫ z in B0579.cell d,
        F x * (((kerD d z l : ℝ) : ℂ) * ((B0579.pd j ψ (x - z) : ℝ) : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hKV _ (hψ.pd j) x, ← integral_const_mul]
  have hR : ∫ x in B0579.cell d, G x * ((kerVel d ψ x l : ℝ) : ℂ) =
      ∫ x in B0579.cell d, ∫ z in B0579.cell d,
        G x * (((kerD d z l : ℝ) : ℂ) * ((ψ (x - z) : ℝ) : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hKV ψ hψ x, ← integral_const_mul]
  have hA : ∀ z : ℝ × ℝ,
      ∫ x in B0579.cell d, F x * (((kerD d z l : ℝ) : ℂ) * ((B0579.pd j ψ (x - z) : ℝ) : ℂ)) =
        ((kerD d z l : ℝ) : ℂ) * ∫ x in B0579.cell d, F x * ((B0579.pd j ψ (x - z) : ℝ) : ℂ) := by
    intro z
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  have hB' : ∀ z : ℝ × ℝ,
      ∫ x in B0579.cell d, G x * (((kerD d z l : ℝ) : ℂ) * ((ψ (x - z) : ℝ) : ℂ)) =
        ((kerD d z l : ℝ) : ℂ) * ∫ x in B0579.cell d, G x * ((ψ (x - z) : ℝ) : ℂ) := by
    intro z
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  rw [hL, integral_integral_swap hI1, hR, integral_integral_swap hI2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [hA z, hB' z, hWz z]
  ring

end UnforcedLeray.Short.IIIa
