import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_13
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection

/-!
# `truncSpgStep`: the `spg` step of the truncation

Proves `TruncSpgStep` (defined in `Sub/PartIII-b_IIIb-D2_1_3_1_2_1_13.lean`):
`⟪χₙ curl Ψ, w⟫ = ⟪χₙ g + ∇χₙ × w, Ψ⟫` for phase tests `Ψ`.

Route: `spg.curl` applied to the phase test `χₙ Ψ`, the product rule
`curlT (χₙ Ψ) = χₙ curlT Ψ + ∇χₙ × Ψ` (pointwise), additivity of `pairF` (integrability from
`w` locally integrable, via the Hardy field `|y|⁻¹ w ∈ Y_2`), and the triple product
`(a × Ψ)·w = -Ψ·(a × w)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## Algebra of `crossC` and `dotL` -/

theorem tsg_crossC_zero_left (b : CVec3) : crossC 0 b = 0 := by
  unfold crossC
  ext i
  fin_cases i <;> simp

theorem tsg_triple (a b c : CVec3) : dotL (crossC a b) c = -dotL b (crossC a c) := by
  simp [dotL_apply, crossC, Fin.sum_univ_three] <;> ring

theorem tsg_dotL_rsmul_left (r : ℝ) (a b : CVec3) : dotL (r • a) b = (r : ℂ) * dotL a b := by
  simp [dotL_apply, Finset.mul_sum, Complex.real_smul, mul_assoc]

theorem tsg_dotL_rsmul_right (r : ℝ) (a b : CVec3) : dotL a (r • b) = (r : ℂ) * dotL a b := by
  simp [dotL_apply, Finset.mul_sum, Complex.real_smul, mul_assoc]

/-- The phase-cell integral of a negation. -/
theorem tsg_phaseInt_neg (P : ℝ) (f : ℝ × Space → ℂ) :
    phaseInt P (fun x => -f x) = -phaseInt P f := by
  unfold phaseInt
  simp [integral_neg, smul_neg]

/-! ## Product rule for `curlT` against a cutoff -/

theorem tsg_curl_mul (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) (Ψ : ℝ × Space → CVec3)
    (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) :
    curlT (fun z => χ z.2 • Ψ z) x = χ x.2 • curlT Ψ x + crossC (gradC χ x.2) (Ψ x) := by
  have hd : ∀ j : Fin 3, dy j (fun z => χ z.2 • Ψ z) x =
      χ x.2 • dy j Ψ x + sd j χ x.2 • Ψ x := by
    intro j
    have h := congrFun (dy_mulT (a := χ) (hχ.differentiable (by simp)) (Ψ := Ψ)
      (hΨ.differentiable (by simp)) j) x
    rw [show (fun z : ℝ × Space => χ z.2 • Ψ z) = mulT χ Ψ from rfl, h]
    simp [mulT]
  unfold curlT
  simp only [hd]
  ext i
  fin_cases i <;> simp [crossC, gradC, Fin.sum_univ_three, EuclideanSpace.single_apply] <;> ring

/-! ## Continuity and local integrability -/

theorem tsg_curlT_cont {Ψ : ℝ × Space → CVec3} (hΨ : ContDiff ℝ ∞ Ψ) :
    Continuous (curlT Ψ) := by
  unfold curlT
  exact continuous_finset_sum _ fun j _ =>
    continuous_crossC.comp (continuous_const.prodMk (contDiff_dy hΨ j).continuous)

/-- The complement of the axis `{y = 0}` is of full measure in `ℝ × ℝ³`. -/
theorem tsg_ae_y_ne_zero : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), x.2 ≠ 0 := by
  rw [ae_iff]
  have hnull : (volume : Measure (ℝ × Space)) {x : ℝ × Space | x.2 = 0} = 0 := by
    have hs : {x : ℝ × Space | x.2 = 0} = (univ : Set ℝ) ×ˢ ({0} : Set Space) := by
      ext x
      simp
    rw [hs, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]
  simpa using hnull

/-- A Hardy field `|y|⁻¹ w ∈ Y_2` makes `w` locally integrable. -/
theorem tsg_locInt_of_hardy {P : ℝ} (hP : 0 < P) {w : ℝ × Space → CVec3}
    (hG : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • w x)) :
    LocallyIntegrable w volume := by
  have hne := tsg_ae_y_ne_zero
  have hid : ∀ᵐ x : ℝ × Space ∂volume,
      (‖x.2‖ : ℝ) • ((‖x.2‖⁻¹ : ℝ) • w x) = w x := by
    filter_upwards [hne] with x hx
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
  have hwm : AEStronglyMeasurable w volume := by
    have h1 : AEStronglyMeasurable
        (fun x : ℝ × Space => (‖x.2‖ : ℝ) • ((‖x.2‖⁻¹ : ℝ) • w x)) volume :=
      ((continuous_norm.comp continuous_snd).aestronglyMeasurable).smul hG.meas
    exact h1.congr hid
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Space)).mp hK.isBounded
  have hGK : IntegrableOn (fun x => (‖x.2‖⁻¹ : ℝ) • w x) K volume :=
    (locInt_of_isInYr hP hG).integrableOn_isCompact hK
  have hKm : MeasurableSet K := hK.measurableSet
  have hGn : Integrable (fun x => M * ‖(‖x.2‖⁻¹ : ℝ) • w x‖) (volume.restrict K) :=
    (hGK.norm).const_mul M
  refine Integrable.mono' hGn hwm.restrict ?_
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_of_ae hid, ae_restrict_mem hKm]
    with x hx hidx hxK
  have h1 : ‖w x‖ = ‖x.2‖ * ‖(‖x.2‖⁻¹ : ℝ) • w x‖ := by
    have h2 := congrArg norm hidx
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)] at h2
    exact h2.symm
  have hMx : ‖x.2‖ ≤ M := le_trans (norm_snd_le x) (mem_closedBall_zero_iff.1 (hM hxK))
  rw [h1]
  gcongr

/-! ## Integrability of a bounded-support field against a locally integrable field -/

theorem tsg_integrable_dotL {P : ℝ} {H F : ℝ × Space → CVec3} (hH : Continuous H) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → H (τ, y) = 0) (hF : LocallyIntegrable F volume) :
    Integrable (fun x => dotL (H x) (F x)) (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) := by
  set K : Set (ℝ × Space) := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hKc.measurableSet
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hH.continuousOn
  have hFK : IntegrableOn (fun x => ‖F x‖) K volume := (hF.integrableOn_isCompact hKc).norm
  have hfK : IntegrableOn (fun x => dotL (H x) (F x)) K volume := by
    refine Integrable.mono' (hFK.const_mul (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C)) ?_ ?_
    · exact dotL.aestronglyMeasurable_comp₂ hH.aestronglyMeasurable
        (hF.integrableOn_isCompact hKc).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hKm] with x hx
      calc ‖dotL (H x) (F x)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖H x‖ * ‖F x‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C * ‖F x‖ := by
            gcongr
            exact hC x hx
  have hind : Integrable (K.indicator fun x => dotL (H x) (F x)) volume :=
    hfK.integrable_indicator hKm
  refine (hind.integrableOn).congr_fun ?_
    (measurableSet_Ioc.prod MeasurableSet.univ)
  intro x hx
  obtain ⟨τ, y⟩ := x
  by_cases hxK : (τ, y) ∈ K
  · rw [indicator_of_mem hxK]
  · rw [indicator_of_notMem hxK]
    have hy : R < ‖y‖ := by
      by_contra hcon
      push_neg at hcon
      apply hxK
      refine ⟨⟨hx.1.1.le, hx.1.2⟩, ?_⟩
      simpa using hcon
    dsimp only
    rw [hR τ y hy]
    simp

/-! ## The `spg` step -/

theorem truncSpgStep : TruncSpgStep := by
  intro hCut P ν μ hP hP1 hν hμ D hD n Ψ hΨ
  haveI : Fact (0 < P) := ⟨hP⟩
  obtain ⟨C, -, hcb⟩ := hCut
  have hχc : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  have hΨd : ContDiff ℝ ∞ Ψ := hΨ.smooth
  -- the phase test `χₙ Ψ`
  have hΘ : IsPhaseTest P (fun z => cutχ n z.2 • Ψ z) :=
    { smooth := contDiff_mulT hχc hΨd
      periodic := fun τ y => by simp [hΨ.periodic τ y]
      bounded_support := ⟨2 * ((n : ℝ) + 1), fun τ y hy => by
        simp [cutχ_eq_zero n hy.le]⟩ }
  have hΘc : Continuous (fun z : ℝ × Space => cutχ n z.2 • Ψ z) :=
    ((contDiff_cutχ n).continuous.comp continuous_snd).smul hΨd.continuous
  have hΘsupp : ∀ τ y, 2 * ((n : ℝ) + 1) < ‖y‖ →
      (fun z : ℝ × Space => cutχ n z.2 • Ψ z) (τ, y) = 0 := fun τ y hy => by
    simp [cutχ_eq_zero n hy.le]
  -- the two pieces of the product rule
  have hF1c : Continuous (fun x : ℝ × Space => cutχ n x.2 • curlT Ψ x) :=
    ((contDiff_cutχ n).continuous.comp continuous_snd).smul (tsg_curlT_cont hΨd)
  have hF2c : Continuous (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (Ψ x)) :=
    continuous_crossC.comp
      (((continuous_gradC' fun j => (contDiff_sd hχc j).continuous).comp continuous_snd).prodMk
        hΨd.continuous)
  have hF1supp : ∀ τ y, 2 * ((n : ℝ) + 1) < ‖y‖ →
      (fun x : ℝ × Space => cutχ n x.2 • curlT Ψ x) (τ, y) = 0 := fun τ y hy => by
    simp [cutχ_eq_zero n hy.le]
  have hF2supp : ∀ τ y, 2 * ((n : ℝ) + 1) < ‖y‖ →
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (Ψ x)) (τ, y) = 0 := fun τ y hy => by
    simp [((hcb n y).1 (Or.inr hy)).1, tsg_crossC_zero_left]
  have hSc : Continuous (fun x : ℝ × Space =>
      cutχ n x.2 • curlT Ψ x + crossC (gradC (cutχ n) x.2) (Ψ x)) := hF1c.add hF2c
  have hSsupp : ∀ τ y, 2 * ((n : ℝ) + 1) < ‖y‖ →
      (fun x : ℝ × Space => cutχ n x.2 • curlT Ψ x + crossC (gradC (cutχ n) x.2) (Ψ x))
        (τ, y) = 0 := fun τ y hy => by
    simp [cutχ_eq_zero n hy.le, ((hcb n y).1 (Or.inr hy)).1, tsg_crossC_zero_left]
  have hw_loc : LocallyIntegrable D.w volume := tsg_locInt_of_hardy hP hD.spg.hardy
  have hg_loc : LocallyIntegrable D.g volume := locInt_of_isInYr hP hD.dom.mem_g
  have hI1 : Integrable (fun x : ℝ × Space => dotL (cutχ n x.2 • curlT Ψ x) (D.w x))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) :=
    tsg_integrable_dotL hF1c (R := 2 * ((n : ℝ) + 1)) hF1supp hw_loc
  have hI2 : Integrable (fun x : ℝ × Space => dotL (crossC (gradC (cutχ n) x.2) (Ψ x)) (D.w x))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) :=
    tsg_integrable_dotL hF2c (R := 2 * ((n : ℝ) + 1)) hF2supp hw_loc
  have hI12 : Integrable (fun x : ℝ × Space =>
      dotL (cutχ n x.2 • curlT Ψ x + crossC (gradC (cutχ n) x.2) (Ψ x)) (D.w x))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) :=
    tsg_integrable_dotL hSc (R := 2 * ((n : ℝ) + 1)) hSsupp hw_loc
  -- additivity of the left slot
  have hsplit := UnforcedLeray.Cons.C03.Concrete.pairF_add_left_of_integrable
    (F := fun x : ℝ × Space => cutχ n x.2 • curlT Ψ x)
    (G := fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (Ψ x))
    (H := D.w) hI1 hI2 hI12
  -- the spg identity for the phase test `χₙ Ψ`
  have h1 := hD.spg.curl _ hΘ
  have h2 : curlT (fun z : ℝ × Space => cutχ n z.2 • Ψ z) =
      fun x : ℝ × Space => cutχ n x.2 • curlT Ψ x + crossC (gradC (cutχ n) x.2) (Ψ x) :=
    funext fun x => tsg_curl_mul (cutχ n) hχc Ψ hΨd x
  have h1' : pairF P (fun x : ℝ × Space => cutχ n x.2 • curlT Ψ x +
      crossC (gradC (cutχ n) x.2) (Ψ x)) D.w =
      pairF P (fun z : ℝ × Space => cutχ n z.2 • Ψ z) D.g := by
    rw [h2] at h1
    exact h1
  -- the right slot: `χₙ g` against `Ψ`, and `∇χₙ × w` against `Ψ`
  have hA : Integrable (fun x : ℝ × Space => dotL (Ψ x) (cutχ n x.2 • D.g x))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) := by
    refine (tsg_integrable_dotL hΘc (R := 2 * ((n : ℝ) + 1)) hΘsupp hg_loc).congr
      (ae_of_all _ fun x => ?_)
    dsimp only
    rw [tsg_dotL_rsmul_left, tsg_dotL_rsmul_right]
  have hB : Integrable (fun x : ℝ × Space =>
      dotL (Ψ x) (crossC (gradC (cutχ n) x.2) (D.w x)))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) := by
    refine (hI2.neg).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.neg_apply]
    rw [tsg_triple, neg_neg]
  have hAB : Integrable (fun x : ℝ × Space => dotL (Ψ x)
      (cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x)))
      (volume.restrict (UnforcedLeray.Cons.C03.Concrete.phaseCell P)) := by
    refine (hA.add hB).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    exact (map_add (dotL (Ψ x)) _ _).symm
  have h4 := UnforcedLeray.Cons.C03.Concrete.pairF_add_right_of_integrable
    (H := Ψ)
    (F := fun x : ℝ × Space => cutχ n x.2 • D.g x)
    (G := fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x))
    hA hB hAB
  beta_reduce at h4
  beta_reduce at hsplit
  have e1 : pairF P Ψ (fun x : ℝ × Space => cutχ n x.2 • D.g x) =
      pairF P (fun z : ℝ × Space => cutχ n z.2 • Ψ z) D.g := by
    unfold pairF
    congr 1
    funext x
    dsimp only
    rw [tsg_dotL_rsmul_right, tsg_dotL_rsmul_left]
  have e2 : pairF P Ψ (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x)) =
      -pairF P (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (Ψ x)) D.w := by
    unfold pairF
    rw [← tsg_phaseInt_neg]
    congr 1
    funext x
    dsimp only
    rw [tsg_triple, neg_neg]
  rw [h4, e1, e2]
  linear_combination h1' - hsplit

end UnforcedLeray.Short.PartIIIb.Concrete
