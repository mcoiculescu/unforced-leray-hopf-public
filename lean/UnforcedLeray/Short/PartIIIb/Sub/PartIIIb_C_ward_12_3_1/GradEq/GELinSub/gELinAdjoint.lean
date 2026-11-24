import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.Props
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinConvTPhaseTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.gELinPairDeriv
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellQuadraticGuard
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp

/-!
# `GELinAdjoint`: transposition of `convT V` against a phase test (source 2525-2533)

Task `PartIII-b:C/ward/12/3/1/2/6/6`.  With `Θ_k = V_k Φ`, `dy k Θ_k = (∂_kV_k) Φ + V_k ∂_kΦ`, the
pointwise identity
`dotL (convT V Φ) R + ∑_k dotL (dy k Θ_k) R + ∑_k dotL Θ_k R'_k = dotL Φ (convTAdj V v v')`
and the weak derivative `GELinPairDeriv` give the transposition.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (rep phaseCell pairF convT gradUT advT integrable_dotL_of_memLp_compactFirst memLp_rep_periodCell pairF_eq_restrictedProductIntegral)

/-- `V_k Φ`, the phase-test multiple of `Φ` by the real field `V_k`. -/
def gAdjTheta (V : ℝ → UnforcedLeray.SpatialField) (Φ : ℝ × UnforcedLeray.Space → CVec3)
    (k : Fin 3) : ℝ × UnforcedLeray.Space → CVec3 :=
  fun x => ((V x.1 x.2 k : ℝ) : ℂ) • Φ x

/-- The coefficient `∑ₗ Φₗ ∂_kV_ₗ` multiplying the unit vector `e_k`. -/
def gAdjPsi (V : ℝ → UnforcedLeray.SpatialField) (Φ : ℝ × UnforcedLeray.Space → CVec3)
    (k : Fin 3) : ℝ × UnforcedLeray.Space → CVec3 :=
  fun x => (∑ l : Fin 3, Φ x l * ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) l : ℝ) : ℂ)) •
    (EuclideanSpace.single k (1 : ℂ) : CVec3)

/-- The field `(∑ₘ ∂ₘV_ₘ) Φ`. -/
def gAdjPsiD (V : ℝ → UnforcedLeray.SpatialField) (Φ : ℝ × UnforcedLeray.Space → CVec3) :
    ℝ × UnforcedLeray.Space → CVec3 :=
  fun x => (∑ m : Fin 3, ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single m 1) m : ℝ) : ℂ)) • Φ x

theorem gAdj_fderiv_slice {F : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hF : ContDiff ℝ ∞ F) (x : ℝ × UnforcedLeray.Space) (e : UnforcedLeray.Space) :
    fderiv ℝ F x (0, e) = fderiv ℝ (fun y => F (x.1, y)) x.2 e := by
  have hFd : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) :=
    (hF.differentiable (by simp) x).hasFDerivAt
  have hg : HasFDerivAt (fun y : UnforcedLeray.Space => ((x.1, y) : ℝ × UnforcedLeray.Space))
      (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) x.2 :=
    hasFDerivAt_prodMk_right x.1 x.2
  have hc := hFd.comp x.2 hg
  have hfd : fderiv ℝ (fun y => F (x.1, y)) x.2 =
      (fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ UnforcedLeray.Space) := hc.fderiv
  rw [hfd]
  rfl

theorem gAdj_ofReal_dk_cont {V : ℝ → UnforcedLeray.SpatialField}
    (hVc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2)) (k l : Fin 3) :
    Continuous (fun x : ℝ × UnforcedLeray.Space =>
      ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) l : ℝ) : ℂ)) :=
  (gELinConvT_ofReal ((contDiff_piLp 2).1 (gELinConvT_partial hVc k) l)).continuous

theorem gAdj_psi_props {V : ℝ → UnforcedLeray.SpatialField} {P : ℝ}
    {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hVc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    (hΦ : IsPhaseTest P Φ) (k : Fin 3) :
    Continuous (gAdjPsi V Φ k) ∧ ∃ R0 : ℝ, ∀ τ y, R0 < ‖y‖ → gAdjPsi V Φ k (τ, y) = 0 := by
  obtain ⟨R0, hR0⟩ := hΦ.bounded_support
  refine ⟨?_, R0, fun τ y hy => ?_⟩
  · unfold gAdjPsi
    have h1 : Continuous (fun x : ℝ × UnforcedLeray.Space =>
        ∑ l : Fin 3, Φ x l * ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) l : ℝ) : ℂ)) :=
      continuous_finset_sum _ (fun l _ =>
        ((contDiff_piLp 2).1 hΦ.smooth l).continuous.mul (gAdj_ofReal_dk_cont hVc k l))
    exact h1.smul continuous_const
  · simp [gAdjPsi, hR0 τ y hy]

theorem gAdj_psiD_props {V : ℝ → UnforcedLeray.SpatialField} {P : ℝ}
    {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hVc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    (hΦ : IsPhaseTest P Φ) :
    Continuous (gAdjPsiD V Φ) ∧ ∃ R0 : ℝ, ∀ τ y, R0 < ‖y‖ → gAdjPsiD V Φ (τ, y) = 0 := by
  obtain ⟨R0, hR0⟩ := hΦ.bounded_support
  refine ⟨?_, R0, fun τ y hy => ?_⟩
  · unfold gAdjPsiD
    have h1 : Continuous (fun x : ℝ × UnforcedLeray.Space =>
        ∑ m : Fin 3, ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single m 1) m : ℝ) : ℂ)) :=
      continuous_finset_sum _ (fun m _ => gAdj_ofReal_dk_cont hVc m m)
    exact h1.smul hΦ.smooth.continuous
  · simp [gAdjPsiD, hR0 τ y hy]

/-- **`L^{q₀}` integrability on the phase cell** of `Ψ · rep w` for a continuous `Ψ` vanishing
for large `‖y‖`. -/
theorem gAdj_integrable_cont {P : ℝ} [Fact (0 < P)] {Ψ : ℝ × UnforcedLeray.Space → CVec3}
    (hc : Continuous Ψ) {R0 : ℝ} (hs : ∀ τ y, R0 < ‖y‖ → Ψ (τ, y) = 0)
    (w : Yq P UnforcedLeray.B0412.q0E) :
    Integrable (fun x : ℝ × UnforcedLeray.Space => dotL (Ψ x) (rep w x.1 x.2))
      (volume.restrict (phaseCell P)) := by
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0) :=
    hK.measurableSet
  have hKfin : (volume.restrict (phaseCell P))
      (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0) ≠ ⊤ :=
    ne_top_of_le_ne_top hK.measure_lt_top.ne
      (Measure.le_iff'.1 Measure.restrict_le_self _)
  haveI : IsFiniteMeasure ((volume.restrict (phaseCell P)).restrict
      (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0)) :=
    isFiniteMeasure_restrict.2 hKfin
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hΨK : MemLp Ψ UnforcedLeray.B0412.q0E
      ((volume.restrict (phaseCell P)).restrict
        (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0)) := by
    refine MemLp.of_bound hc.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hKm] with x hx
    exact hC x hx
  have hF : MemLp ((Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0).indicator Ψ)
      UnforcedLeray.B0412.q0E (volume.restrict (phaseCell P)) :=
    (memLp_indicator_iff_restrict hKm).2 hΨK
  have hG : MemLp ((Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0).indicator
      (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2))
      UnforcedLeray.B0412.q0E (volume.restrict (phaseCell P)) :=
    (memLp_rep_periodCell UnforcedLeray.B0412.q0E_ne_top w).indicator hKm
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : UnforcedLeray.Space, R0 < ‖y‖ →
      ((Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0).indicator Ψ) (τ, y) = 0 := by
    intro τ _ y hy
    apply Set.indicator_of_notMem
    intro hmem
    have h2 : ‖y‖ ≤ R0 := mem_closedBall_zero_iff.1 hmem.2
    linarith
  have hint := integrable_dotL_of_memLp_compactFirst (P := P) (R := R0) hF hG hzero
  refine hint.congr ?_
  have hcellm : MeasurableSet (phaseCell P) := measurableSet_Ioc.prod MeasurableSet.univ
  filter_upwards [ae_restrict_mem hcellm] with ⟨τ, y⟩ hx
  have hx' : τ ∈ Ioc (0 : ℝ) P := hx.1
  by_cases hxK : ((τ, y) : ℝ × UnforcedLeray.Space) ∈
      (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R0)
  · simp [Set.indicator_of_mem hxK]
  · have hy : R0 < ‖y‖ := by
      by_contra hle
      push_neg at hle
      exact hxK ⟨Ioc_subset_Icc_self hx', mem_closedBall_zero_iff.2 hle⟩
    simp [Set.indicator_of_notMem hxK, hs τ y hy]

theorem gAdj_integrable_phase {P : ℝ} [Fact (0 < P)] {Ψ : ℝ × UnforcedLeray.Space → CVec3}
    (hΨ : IsPhaseTest P Ψ) (w : Yq P UnforcedLeray.B0412.q0E) :
    Integrable (fun x : ℝ × UnforcedLeray.Space => dotL (Ψ x) (rep w x.1 x.2))
      (volume.restrict (phaseCell P)) := by
  obtain ⟨R0, hR0⟩ := hΨ.bounded_support
  exact gAdj_integrable_cont hΨ.smooth.continuous hR0 w

theorem gAdj_theta_phaseTest {P : ℝ} {V : ℝ → UnforcedLeray.SpatialField}
    (hV : IsSmoothPer P V) {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (k : Fin 3) : IsPhaseTest P (gAdjTheta V Φ k) := by
  obtain ⟨hVc, hVp⟩ := hV
  have hf : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2 k) :=
    (contDiff_piLp 2).1 hVc k
  refine { smooth := ?_, periodic := ?_, bounded_support := ?_ }
  · refine (contDiff_piLp 2).2 (fun i => ?_)
    have hc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => ((V x.1 x.2 k : ℝ) : ℂ)) :=
      gELinConvT_ofReal hf
    have hΦi : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => Φ x i) :=
      (contDiff_piLp 2).1 hΦ.smooth i
    simp only [gAdjTheta, PiLp.smul_apply, smul_eq_mul]
    exact hc.mul hΦi
  · intro τ y
    simp [gAdjTheta, hVp, hΦ.periodic]
  · obtain ⟨R0, hR0⟩ := hΦ.bounded_support
    exact ⟨R0, fun τ y hy => by simp [gAdjTheta, hR0 τ y hy]⟩

/-- Product rule for the spatial derivative of `V_k Φ`. -/
theorem gAdj_dy_realSmul {V : ℝ → UnforcedLeray.SpatialField}
    (hVc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 3)
    (x : ℝ × UnforcedLeray.Space) :
    PhaseSpace.dy k (gAdjTheta V Φ k) x =
      ((fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) k : ℝ) : ℂ) • Φ x +
        ((V x.1 x.2 k : ℝ) : ℂ) • PhaseSpace.dy k Φ x := by
  have hFd : HasFDerivAt (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2)
      (fderiv ℝ (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2) x) x :=
    (hVc.differentiable (by simp) x).hasFDerivAt
  have hpk : HasFDerivAt (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2 k)
      ((EuclideanSpace.proj k : UnforcedLeray.Space →L[ℝ] ℝ).comp
        (fderiv ℝ (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2) x)) x :=
    (EuclideanSpace.proj k : UnforcedLeray.Space →L[ℝ] ℝ).hasFDerivAt.comp x hFd
  have hslice : fderiv ℝ (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2) x
      (0, EuclideanSpace.single k 1) =
        fderiv ℝ (V x.1) x.2 (EuclideanSpace.single k 1) :=
    gAdj_fderiv_slice hVc x (EuclideanSpace.single k 1)
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ x) x := (hΦ.differentiable (by simp) x).hasFDerivAt
  have hc : HasFDerivAt (fun y : ℝ × UnforcedLeray.Space => ((V y.1 y.2 k : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((EuclideanSpace.proj k : UnforcedLeray.Space →L[ℝ] ℝ).comp
        (fderiv ℝ (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2) x))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hpk
  have hfd : fderiv ℝ (fun y : ℝ × UnforcedLeray.Space => ((V y.1 y.2 k : ℝ) : ℂ) • Φ y) x =
      ((V x.1 x.2 k : ℝ) : ℂ) • fderiv ℝ Φ x +
        (Complex.ofRealCLM.comp ((EuclideanSpace.proj k : UnforcedLeray.Space →L[ℝ] ℝ).comp
          (fderiv ℝ (fun y : ℝ × UnforcedLeray.Space => V y.1 y.2) x))).smulRight (Φ x) :=
    (hc.smul hΦd).fderiv
  have hcv : (UnforcedLeray.coordinateVector k : UnforcedLeray.Space) =
      EuclideanSpace.single k 1 := rfl
  unfold gAdjTheta PhaseSpace.dy
  rw [hfd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, hcv, hslice]
  rw [add_comm]
  rfl


/-- Pointwise expansion of the transposed field: `⟨Φ, convTAdj⟩` splits into the coefficient
terms `ψ_k`, `ψ_D` and `Θ_m`. -/
theorem gAdj_pointwise_A {P : ℝ} [Fact (0 < P)] (V : ℝ → UnforcedLeray.SpatialField)
    (v : Yq P UnforcedLeray.B0412.q0E) (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E)
    (Φ : ℝ × UnforcedLeray.Space → CVec3) (x : ℝ × UnforcedLeray.Space) :
    dotL (Φ x) (convTAdj V v v' x) =
      (∑ k : Fin 3, dotL (gAdjPsi V Φ k x) (rep v x.1 x.2)) +
        dotL (gAdjPsiD V Φ x) (rep v x.1 x.2) +
        ∑ m : Fin 3, dotL (gAdjTheta V Φ m x) (rep (v' m) x.1 x.2) := by
  simp [gAdjPsi, gAdjPsiD, gAdjTheta, convTAdj, dotL_apply, Fin.sum_univ_three,
    EuclideanSpace.single_apply]
  ring

/-- Pointwise transposition identity: `⟨convT V Φ, R⟩ + ∑ₖ⟨∂_kΘ_k, R⟩ + ∑ₖ⟨Θ_k, R'_k⟩ = ⟨Φ, convTAdj⟩`. -/
theorem gAdj_pointwise_B {P : ℝ} [Fact (0 < P)] {V : ℝ → UnforcedLeray.SpatialField}
    (hVc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2))
    (v : Yq P UnforcedLeray.B0412.q0E) (v' : Fin 3 → Yq P UnforcedLeray.B0412.q0E)
    {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (x : ℝ × UnforcedLeray.Space) :
    dotL (convT V Φ x) (rep v x.1 x.2) +
        (∑ k : Fin 3, dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2)) +
        (∑ k : Fin 3, dotL (gAdjTheta V Φ k x) (rep (v' k) x.1 x.2)) =
      dotL (Φ x) (convTAdj V v v' x) := by
  simp only [gAdj_dy_realSmul hVc hΦ]
  simp [convT, gradUT, advT, gAdjTheta, convTAdj, dotL_apply, Fin.sum_univ_three,
    UnforcedLeray.B0412.realC_apply]
  ring

theorem gELinAdjoint : GELinAdjoint := by
  intro P _ V hV v v' hop Φ hΦ
  have hVc : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => V x.1 x.2) := hV.1
  have hΦd : ContDiff ℝ ∞ Φ := hΦ.smooth
  have hΘ : ∀ k : Fin 3, IsPhaseTest P (gAdjTheta V Φ k) := fun k => gAdj_theta_phaseTest hV hΦ k
  have hdyΘ : ∀ k : Fin 3, IsPhaseTest P (PhaseSpace.dy k (gAdjTheta V Φ k)) :=
    fun k => (hΘ k).dy k
  have hIntA : Integrable (fun x => dotL (Φ x) (convTAdj V v v' x))
      (volume.restrict (phaseCell P)) := by
    have hfun : (fun x => dotL (Φ x) (convTAdj V v v' x)) = fun x =>
        (∑ k : Fin 3, dotL (gAdjPsi V Φ k x) (rep v x.1 x.2)) +
          dotL (gAdjPsiD V Φ x) (rep v x.1 x.2) +
          ∑ m : Fin 3, dotL (gAdjTheta V Φ m x) (rep (v' m) x.1 x.2) :=
      funext fun x => gAdj_pointwise_A V v v' Φ x
    rw [hfun]
    refine ((integrable_finset_sum _ (fun k _ => ?_)).add ?_).add
      (integrable_finset_sum _ (fun m _ => ?_))
    · obtain ⟨hc, R0, hs⟩ := gAdj_psi_props hVc hΦ k
      exact gAdj_integrable_cont hc hs v
    · obtain ⟨hc, R0, hs⟩ := gAdj_psiD_props hVc hΦ
      exact gAdj_integrable_cont hc hs v
    · exact gAdj_integrable_phase (hΘ m) (v' m)
  have hIntDy : Integrable (fun x => ∑ k : Fin 3,
      dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2))
      (volume.restrict (phaseCell P)) :=
    integrable_finset_sum _ (fun k _ => gAdj_integrable_phase (hdyΘ k) v)
  have hIntTh : Integrable (fun x => ∑ k : Fin 3,
      dotL (gAdjTheta V Φ k x) (rep (v' k) x.1 x.2))
      (volume.restrict (phaseCell P)) :=
    integrable_finset_sum _ (fun k _ => gAdj_integrable_phase (hΘ k) (v' k))
  have hIntConv : Integrable (fun x => dotL (convT V Φ x) (rep v x.1 x.2))
      (volume.restrict (phaseCell P)) := by
    have hfun : (fun x => dotL (convT V Φ x) (rep v x.1 x.2)) = fun x =>
        dotL (Φ x) (convTAdj V v v' x) -
          (∑ k : Fin 3, dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2)) -
          ∑ k : Fin 3, dotL (gAdjTheta V Φ k x) (rep (v' k) x.1 x.2) := by
      funext x
      linear_combination gAdj_pointwise_B hVc v v' hΦd x
    rw [hfun]
    exact (hIntA.sub hIntDy).sub hIntTh
  -- the weak derivative on each `Θ_k`
  have hpd : ∀ k : Fin 3,
      ∫ x, dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2)
          ∂(volume.restrict (phaseCell P)) =
        -∫ x, dotL (gAdjTheta V Φ k x) (rep (v' k) x.1 x.2) ∂(volume.restrict (phaseCell P)) := by
    intro k
    have h := gELinPairDeriv P v (v' k) k (hop k) (gAdjTheta V Φ k) (hΘ k)
    have e1 := pairF_eq_restrictedProductIntegral
      (F := PhaseSpace.dy k (gAdjTheta V Φ k)) (G := fun x => rep v x.1 x.2)
      (gAdj_integrable_phase (hdyΘ k) v)
    have e2 := pairF_eq_restrictedProductIntegral
      (F := gAdjTheta V Φ k) (G := fun x => rep (v' k) x.1 x.2)
      (gAdj_integrable_phase (hΘ k) (v' k))
    rw [e1, e2, ← smul_neg] at h
    exact (smul_right_inj (inv_ne_zero (ne_of_gt (Fact.out : (0 : ℝ) < P)))).1 h
  have hsplit : ∫ x, dotL (Φ x) (convTAdj V v v' x) ∂(volume.restrict (phaseCell P)) =
      (∫ x, dotL (convT V Φ x) (rep v x.1 x.2) ∂(volume.restrict (phaseCell P))) +
        (∑ k : Fin 3, ∫ x, dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2)
          ∂(volume.restrict (phaseCell P))) +
        ∑ k : Fin 3, ∫ x, dotL (gAdjTheta V Φ k x) (rep (v' k) x.1 x.2)
          ∂(volume.restrict (phaseCell P)) := by
    have hcongr : (fun x => dotL (Φ x) (convTAdj V v v' x)) = fun x =>
        (dotL (convT V Φ x) (rep v x.1 x.2) +
          ∑ k : Fin 3, dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2)) +
          ∑ k : Fin 3, dotL (gAdjTheta V Φ k x) (rep (v' k) x.1 x.2) := by
      funext x
      linear_combination -(gAdj_pointwise_B hVc v v' hΦd x)
    have hX2 : Integrable (fun x => dotL (convT V Φ x) (rep v x.1 x.2) +
        ∑ k : Fin 3, dotL (PhaseSpace.dy k (gAdjTheta V Φ k) x) (rep v x.1 x.2))
        (volume.restrict (phaseCell P)) := hIntConv.add hIntDy
    rw [hcongr, integral_add hX2 hIntTh, integral_add hIntConv hIntDy,
      integral_finset_sum _ (fun k _ => gAdj_integrable_phase (hdyΘ k) v),
      integral_finset_sum _ (fun k _ => gAdj_integrable_phase (hΘ k) (v' k))]
  have hfinal : ∫ x, dotL (Φ x) (convTAdj V v v' x) ∂(volume.restrict (phaseCell P)) =
      ∫ x, dotL (convT V Φ x) (rep v x.1 x.2) ∂(volume.restrict (phaseCell P)) := by
    rw [hsplit]
    simp only [hpd, Finset.sum_neg_distrib]
    ring
  refine ⟨hIntA, hIntConv, ?_⟩
  rw [pairF_eq_restrictedProductIntegral hIntConv, pairF_eq_restrictedProductIntegral hIntA, hfinal]

end UnforcedLeray.Short.PartIIIb.Concrete
