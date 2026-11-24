import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedSchemeTotalConvection
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert

/-!
# `weakCurlMul`: weak product rule for the curl

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
For a phase test `Ψ` and smooth `c = c(y)`, `curl(c u) = c v + ∇c × u` weakly when `curl u = v`
weakly, with `u, v` locally `L²` in the sense of `LocL2`.

Strategy: every pairing is rewritten pointwise so that the (continuous, `y`-compactly supported)
phase-test factor sits in the first slot, and integrability then follows from `LocL2` alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_add_left_of_integrable pairF_add_right_of_integrable)

/-- `crossC a 0 = 0`. -/
theorem wcm_crossC_zero_right (a : CVec3) : crossC a 0 = 0 := by
  ext i
  fin_cases i <;> simp [crossC]

/-- Real scalars pull out of the first slot of `dotL`. -/
theorem wcm_dotL_realsmul_left (r : ℝ) (a b : CVec3) :
    dotL (r • a) b = (r : ℂ) * dotL a b := by
  simp only [dotL_apply, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Real scalars pull out of the second slot of `dotL`. -/
theorem wcm_dotL_realsmul_right (r : ℝ) (a b : CVec3) :
    dotL a (r • b) = (r : ℂ) * dotL a b := by
  simp only [dotL_apply, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Triple product identity `(a × b)·u = -b·(a × u)`. -/
theorem wcm_triple (a b u : CVec3) : dotL (crossC a b) u = -dotL b (crossC a u) := by
  simp [dotL_apply, crossC, Fin.sum_univ_three] <;> ring

/-- Phase integral of a negated integrand. -/
theorem wcm_phaseInt_neg (P : ℝ) (f : ℝ × Space → ℂ) :
    phaseInt P (fun x => -f x) = -phaseInt P f := by
  unfold phaseInt
  simp [integral_neg]

/-- The curl of `c Ψ` is `c curl Ψ + ∇c × Ψ` pointwise. -/
theorem wcm_curlT_mul {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) {Ψ : ℝ × Space → CVec3}
    (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) :
    curlT (mulT c Ψ) x = c x.2 • curlT Ψ x + crossC (gradC c x.2) (Ψ x) := by
  have hd : Differentiable ℝ c := hc.differentiable (by simp)
  have hdΨ : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have h1 : ∀ j : Fin 3, dy j (mulT c Ψ) x = c x.2 • dy j Ψ x + sd j c x.2 • Ψ x := by
    intro j
    rw [dy_mulT hd hdΨ j]
    rfl
  ext i
  fin_cases i <;>
    simp [curlT, h1, crossC, gradC, Fin.sum_univ_three, Complex.real_smul] <;> ring

/-- A phase test times a smooth function of `y` is a phase test. -/
theorem wcm_isPhaseTest_mul {P : ℝ} {c : Space → ℝ} (hc : ContDiff ℝ ∞ c)
    {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) : IsPhaseTest P (mulT c Ψ) := by
  refine ⟨contDiff_mulT hc hΨ.smooth, fun τ y => ?_, ?_⟩
  · simp [mulT, hΨ.periodic τ y]
  · obtain ⟨R, hR⟩ := hΨ.bounded_support
    exact ⟨R, fun τ y hy => by simp [mulT, hR τ y hy]⟩

/-- The curl of a phase test is continuous. -/
theorem wcm_curlT_continuous {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    Continuous (curlT Φ) := by
  unfold curlT
  refine continuous_finset_sum _ fun j _ => ?_
  exact continuous_crossC.comp (continuous_const.prodMk (hΦ.dy j).continuous)

/-- The curl of a phase test has bounded `y`-support. -/
theorem wcm_curlT_support {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ R : ℝ, ∀ τ y, R < ‖y‖ → curlT Φ (τ, y) = 0 := by
  obtain ⟨R0, h0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, h1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, h2⟩ := (hΦ.dy 2).bounded_support
  refine ⟨max R0 (max R1 R2), fun τ y hy => ?_⟩
  have e0 : dy 0 Φ (τ, y) = 0 := h0 τ y (lt_of_le_of_lt (le_max_left _ _) hy)
  have e1 : dy 1 Φ (τ, y) = 0 :=
    h1 τ y (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hy)
  have e2 : dy 2 Φ (τ, y) = 0 :=
    h2 τ y (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hy)
  simp [curlT, Fin.sum_univ_three, e0, e1, e2, wcm_crossC_zero_right]

/-- The complement of `{y = 0}` has full measure in `ℝ × ℝ³`. -/
theorem wcm_null : ∀ᵐ x : ℝ × Space, x.2 ≠ 0 := by
  have h0 : volume {x : ℝ × Space | x.2 = 0} = 0 := by
    have e : {x : ℝ × Space | x.2 = 0} = (univ : Set ℝ) ×ˢ ({0} : Set Space) := by
      ext x
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  exact ae_iff.2 (by simpa using h0)

/-- A locally `L²` field is a.e. strongly measurable. -/
theorem wcm_aesm {P : ℝ} (hP : 0 < P) {w : ℝ × Space → CVec3} (hw : LocL2 P w) :
    AEStronglyMeasurable w volume := by
  rcases hw with hY | hH
  · exact hY.meas
  · have h1 : AEStronglyMeasurable
        (fun x : ℝ × Space => (‖x.2‖ : ℝ) • ((‖x.2‖⁻¹ : ℝ) • w x)) volume :=
      (continuous_snd.norm.aestronglyMeasurable).smul hH.meas
    refine h1.congr ?_
    filter_upwards [wcm_null] with x hx
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) (w x)

/-- A locally `L²` field is integrable on every compact set. -/
theorem wcm_intOn_LocL2 {P : ℝ} (hP : 0 < P) {w : ℝ × Space → CVec3} (hw : LocL2 P w)
    {K : Set (ℝ × Space)} (hK : IsCompact K) : IntegrableOn w K volume := by
  rcases hw with hY | hH
  · exact (locInt_of_isInYr hP hY).integrableOn_isCompact hK
  · obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Space)).1 hK.isBounded
    have hGint : IntegrableOn (fun x : ℝ × Space => ((‖x.2‖⁻¹ : ℝ)) • w x) K volume :=
      (locInt_of_isInYr hP hH).integrableOn_isCompact hK
    have hwm : AEStronglyMeasurable w volume := wcm_aesm hP (Or.inr hH)
    unfold IntegrableOn
    refine Integrable.mono' (Integrable.const_mul (Integrable.norm hGint) M)
      hwm.restrict ?_
    filter_upwards [ae_restrict_of_ae wcm_null, ae_restrict_mem hK.measurableSet] with x hx0 hxK
    have hxM : ‖x.2‖ ≤ M := (norm_snd_le x).trans (by simpa using hM hxK)
    have hn : ‖x.2‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    show ‖w x‖ ≤ M * ‖((‖x.2‖⁻¹ : ℝ)) • w x‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    calc ‖w x‖ = ‖x.2‖ * (‖x.2‖⁻¹ * ‖w x‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
      _ ≤ M * (‖x.2‖⁻¹ * ‖w x‖) := mul_le_mul_of_nonneg_right hxM (by positivity)

/-- Core integrability: a continuous `y`-compactly supported first factor pairs integrably with a
locally `L²` field on the phase cell. -/
theorem wcm_integrable_dotL {P : ℝ} (hP : 0 < P) {F w : ℝ × Space → CVec3}
    (hF : Continuous F) (hFs : ∃ R : ℝ, ∀ τ y, R < ‖y‖ → F (τ, y) = 0)
    (hw : LocL2 P w) :
    Integrable (fun x => dotL (F x) (w x)) (volume.restrict (phaseCell P)) := by
  obtain ⟨R, hR⟩ := hFs
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hint : Integrable
      (fun x => ‖(Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R).indicator w x‖) volume :=
    (Integrable.norm ((integrable_indicator_iff hK.measurableSet).2
      (wcm_intOn_LocL2 hP hw hK)))
  have hmeas : AEStronglyMeasurable (fun x => dotL (F x) (w x))
      (volume.restrict (phaseCell P)) :=
    dotL.aestronglyMeasurable_comp₂ hF.aestronglyMeasurable (wcm_aesm hP hw).restrict
  have hdom : MeasurableSet (phaseCell P) := measurableSet_Ioc.prod MeasurableSet.univ
  have hg : Integrable
      (fun x => (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * max C 0) *
        ‖(Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R).indicator w x‖)
      (volume.restrict (phaseCell P)) :=
    Integrable.const_mul (Integrable.restrict hint) _
  refine Integrable.mono' hg hmeas ?_
  refine (ae_restrict_iff' hdom).2 (ae_of_all _ fun x hx => ?_)
  have hx1 : x.1 ∈ Ioc (0 : ℝ) P := hx.1
  by_cases hxR : ‖x.2‖ ≤ R
  · have hxK : x ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨Set.Ioc_subset_Icc_self hx1, mem_closedBall_zero_iff.2 hxR⟩
    rw [Set.indicator_of_mem hxK]
    have hFx : ‖F x‖ ≤ C := hC x hxK
    have hB : ‖dotL (F x) (w x)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖F x‖ * ‖w x‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    have hC' : ‖F x‖ ≤ max C 0 := hFx.trans (le_max_left _ _)
    calc ‖dotL (F x) (w x)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖F x‖ * ‖w x‖ := hB
      _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * max C 0 * ‖w x‖ := by gcongr
      _ = (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * max C 0) * ‖w x‖ := by ring
  · have hFx : F x = 0 := hR x.1 x.2 (not_le.1 hxR)
    rw [hFx, map_zero, ContinuousLinearMap.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ))
      (le_max_right _ _)) (norm_nonneg _)

/-- **WeakCurlMul** (source 1334-1337, 1351-1362, 1470-1480): weak product rule for the curl. -/
theorem weakCurlMul : WeakCurlMul := by
  intro P hP c hc u v hu hv huv Ψ hΨ
  have : Fact (0 < P) := ⟨hP⟩
  have hΨs : ContDiff ℝ ∞ Ψ := hΨ.smooth
  have hΘ : IsPhaseTest P (mulT c Ψ) := wcm_isPhaseTest_mul hc hΨ
  have hgc : Continuous (gradC c) :=
    continuous_gradC' (fun j => (UnforcedLeray.PhaseSpace.contDiff_sd hc j).continuous)
  have hFa_cont : Continuous (fun x : ℝ × Space => c x.2 • curlT Ψ x) :=
    (hc.continuous.comp continuous_snd).smul (wcm_curlT_continuous hΨ)
  have hFa_supp : ∃ R : ℝ, ∀ τ y, R < ‖y‖ →
      (fun x : ℝ × Space => c x.2 • curlT Ψ x) (τ, y) = 0 := by
    obtain ⟨R, hR⟩ := wcm_curlT_support hΨ
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩
  have hFb_cont : Continuous (fun x : ℝ × Space => crossC (gradC c x.2) (Ψ x)) :=
    continuous_crossC.comp ((hgc.comp continuous_snd).prodMk hΨ.continuous)
  have hFb_supp : ∃ R : ℝ, ∀ τ y, R < ‖y‖ →
      (fun x : ℝ × Space => crossC (gradC c x.2) (Ψ x)) (τ, y) = 0 := by
    obtain ⟨R, hR⟩ := hΨ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy, wcm_crossC_zero_right]⟩
  have JA := wcm_integrable_dotL hP hFa_cont hFa_supp hu
  have JB := wcm_integrable_dotL hP hFb_cont hFb_supp hu
  have JC := wcm_integrable_dotL hP hΘ.continuous hΘ.bounded_support hv
  have hJB' : Integrable (fun x : ℝ × Space => dotL (Ψ x) (crossC (gradC c x.2) (u x)))
      (volume.restrict (phaseCell P)) :=
    Integrable.congr (Integrable.neg JB) (ae_of_all _ fun x => by
      show -dotL (crossC (gradC c x.2) (Ψ x)) (u x) = dotL (Ψ x) (crossC (gradC c x.2) (u x))
      rw [wcm_triple, neg_neg])
  have hJC' : Integrable (fun x : ℝ × Space => dotL (Ψ x) (c x.2 • v x))
      (volume.restrict (phaseCell P)) :=
    Integrable.congr JC (ae_of_all _ fun x => by
      show dotL (c x.2 • Ψ x) (v x) = dotL (Ψ x) (c x.2 • v x)
      rw [wcm_dotL_realsmul_left, wcm_dotL_realsmul_right])
  have hFG : Integrable
      (fun x : ℝ × Space => dotL (Ψ x) (c x.2 • v x + crossC (gradC c x.2) (u x)))
      (volume.restrict (phaseCell P)) :=
    Integrable.congr (Integrable.add hJC' hJB') (ae_of_all _ fun x => by
      show dotL (Ψ x) (c x.2 • v x) + dotL (Ψ x) (crossC (gradC c x.2) (u x))
        = dotL (Ψ x) (c x.2 • v x + crossC (gradC c x.2) (u x))
      rw [map_add])
  have hsum : Integrable
      (fun x : ℝ × Space => dotL (c x.2 • curlT Ψ x + crossC (gradC c x.2) (Ψ x)) (u x))
      (volume.restrict (phaseCell P)) :=
    Integrable.congr (Integrable.add JA JB) (ae_of_all _ fun x => by
      show dotL (c x.2 • curlT Ψ x) (u x) + dotL (crossC (gradC c x.2) (Ψ x)) (u x)
        = dotL (c x.2 • curlT Ψ x + crossC (gradC c x.2) (Ψ x)) (u x)
      rw [map_add, ContinuousLinearMap.add_apply])
  have hsplit : pairF P (curlT (mulT c Ψ)) u =
      pairF P (fun x : ℝ × Space => c x.2 • curlT Ψ x) u +
        pairF P (fun x : ℝ × Space => crossC (gradC c x.2) (Ψ x)) u := by
    have e : curlT (mulT c Ψ) =
        fun x : ℝ × Space => c x.2 • curlT Ψ x + crossC (gradC c x.2) (Ψ x) :=
      funext fun x => wcm_curlT_mul hc hΨs x
    rw [e]
    exact pairF_add_left_of_integrable JA JB hsum
  have hRsplit : pairF P Ψ (fun x : ℝ × Space => c x.2 • v x + crossC (gradC c x.2) (u x)) =
      pairF P Ψ (fun x : ℝ × Space => c x.2 • v x) +
        pairF P Ψ (fun x : ℝ × Space => crossC (gradC c x.2) (u x)) :=
    pairF_add_right_of_integrable hJC' hJB' hFG
  have hL : pairF P Ψ (fun x : ℝ × Space => c x.2 • v x) = pairF P (mulT c Ψ) v := by
    show phaseInt P (fun x => dotL (Ψ x) (c x.2 • v x)) =
      phaseInt P (fun x => dotL (c x.2 • Ψ x) (v x))
    congr 1
    funext x
    rw [wcm_dotL_realsmul_right, wcm_dotL_realsmul_left]
  have hN : pairF P Ψ (fun x : ℝ × Space => crossC (gradC c x.2) (u x)) =
      -pairF P (fun x : ℝ × Space => crossC (gradC c x.2) (Ψ x)) u := by
    have e : (fun x : ℝ × Space => dotL (Ψ x) (crossC (gradC c x.2) (u x))) =
        fun x => -(dotL (crossC (gradC c x.2) (Ψ x)) (u x)) :=
      funext fun x => by rw [wcm_triple, neg_neg]
    show phaseInt P (fun x => dotL (Ψ x) (crossC (gradC c x.2) (u x))) =
      -phaseInt P (fun x => dotL (crossC (gradC c x.2) (Ψ x)) (u x))
    rw [e, wcm_phaseInt_neg]
  have hL' : pairF P (curlT Ψ) (fun x : ℝ × Space => c x.2 • u x) =
      pairF P (fun x : ℝ × Space => c x.2 • curlT Ψ x) u := by
    show phaseInt P (fun x => dotL (curlT Ψ x) (c x.2 • u x)) =
      phaseInt P (fun x => dotL (c x.2 • curlT Ψ x) (u x))
    congr 1
    funext x
    rw [wcm_dotL_realsmul_right, wcm_dotL_realsmul_left]
  have hTv : pairF P (curlT (mulT c Ψ)) u = pairF P (mulT c Ψ) v := huv (mulT c Ψ) hΘ
  rw [hL', hRsplit, hL, hN]
  linear_combination hTv - hsplit

end UnforcedLeray.Short.PartIIIb.Concrete
