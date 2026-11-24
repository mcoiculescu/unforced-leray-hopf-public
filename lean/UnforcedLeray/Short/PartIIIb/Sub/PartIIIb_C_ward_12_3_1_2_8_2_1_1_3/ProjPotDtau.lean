import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3`: `∂_τ` commutes with the Newton convolution

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Proves `projPotDtau`: `∂_τ (projPot Φ) = projPot (∂_τ Φ)`.
Route: `projPot Φ` is the Newton convolution of the spatial divergences `projectedPotentialReDiv Φ`
and `projectedPotentialImDiv Φ` (parameter-integral representation); `∂_τ` passes under the
integral by dominated differentiation on a compact window (the divergences are phase tests, so
they vanish for large `|y|` uniformly in `τ`), and `∂_τ` commutes with the spatial divergence
(symmetry of second derivatives of real scalars).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory Metric Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProjPotDtauAux

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PressureAnalysis

/-- Symmetry of second derivatives for real-valued smooth functions on `ℝ × Space`. -/
theorem fderiv_apply_comm_real {g : ℝ × UnforcedLeray.Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (v w p : ℝ × UnforcedLeray.Space) :
    fderiv ℝ (fun q => fderiv ℝ g q w) p v = fderiv ℝ (fun q => fderiv ℝ g q v) p w := by
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h1 : ∀ u a : ℝ × UnforcedLeray.Space,
      fderiv ℝ (fun q => fderiv ℝ g q u) p a = fderiv ℝ (fderiv ℝ g) p a u := by
    intro u a
    have hx : HasFDerivAt (fun q => fderiv ℝ g q u) ((fderiv ℝ (fderiv ℝ g) p).flip u) p := by
      simpa using (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const u p)
    rw [hx.fderiv]
    rfl
  rw [h1 w v, h1 v w]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- Directional derivative of a slice-smooth real function in the phase direction. -/
theorem hasDerivAt_slice {G : ℝ × UnforcedLeray.Space → ℝ} (hG : ContDiff ℝ ∞ G) (τ : ℝ)
    (z : UnforcedLeray.Space) :
    HasDerivAt (fun s : ℝ => G (s, z)) (dτ G (τ, z)) τ := by
  have hpair : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : UnforcedLeray.Space)) τ :=
    (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ z)
  exact (hG.differentiable (by simp) (τ, z)).hasFDerivAt.comp_hasDerivAt τ hpair

/-- Differentiation of the Newton convolution of a real phase test in the phase variable. -/
theorem hasDerivAt_newtonPar {P : ℝ} {G : ℝ × UnforcedLeray.Space → ℝ} (hG : IsPhaseTest P G)
    (y : UnforcedLeray.Space) (τ0 : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x, newtonPotential x * G (τ, y - x))
      (∫ x, newtonPotential x * dτ G (τ0, y - x)) τ0 := by
  obtain ⟨R, hR⟩ := hG.bounded_support
  have hzero : ∀ (τ : ℝ) (z : UnforcedLeray.Space), R < ‖z‖ → dτ G (τ, z) = 0 := by
    intro τ z hz
    have hopen : IsOpen {q : ℝ × UnforcedLeray.Space | R < ‖q.2‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
    have hev : G =ᶠ[𝓝 (τ, z)] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds (show R < ‖(τ, z).2‖ from hz)] with q hq
      exact hR q.1 q.2 hq
    have hfd : fderiv ℝ G (τ, z) = 0 := by
      rw [hev.fderiv_eq]
      simp
    unfold dτ
    rw [hfd]
    simp
  have hcontD : Continuous (dτ G) :=
    (hG.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcont : Continuous (fun q : ℝ × UnforcedLeray.Space => ‖G q‖ + ‖dτ G q‖) :=
    hG.smooth.continuous.norm.add hcontD.norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : UnforcedLeray.Space) R)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hwin : ∀ τ ∈ ball τ0 1, ∀ z : UnforcedLeray.Space, ‖z‖ ≤ R →
      ‖G (τ, z)‖ ≤ |C| ∧ ‖dτ G (τ, z)‖ ≤ |C| := by
    intro τ hτ z hz
    have hτ' : |τ - τ0| < 1 := by
      rw [← Real.dist_eq]
      exact Metric.mem_ball.mp hτ
    have hl := (abs_lt.mp hτ').1
    have hu := (abs_lt.mp hτ').2
    have hmem : (τ, z) ∈ Icc (τ0 - 1) (τ0 + 1) ×ˢ closedBall (0 : UnforcedLeray.Space) R :=
      ⟨⟨by linarith, by linarith⟩, mem_closedBall_zero_iff.mpr hz⟩
    have h0 := hC (τ, z) hmem
    rw [Real.norm_of_nonneg (by positivity)] at h0
    have h3 : ‖G (τ, z)‖ + ‖dτ G (τ, z)‖ ≤ |C| := h0.trans (le_abs_self C)
    have hn1 := norm_nonneg (G (τ, z))
    have hn2 := norm_nonneg (dτ G (τ, z))
    constructor <;> linarith
  have hint : Integrable (fun x : UnforcedLeray.Space =>
      (closedBall y R).indicator (fun x => |C| * ‖newtonPotential x‖) x) := by
    apply (integrable_indicator_iff measurableSet_closedBall).2
    have hNi : IntegrableOn newtonPotential (closedBall y R) volume :=
      newtonPotential_locallyIntegrable.integrableOn_isCompact (isCompact_closedBall y R)
    exact (hNi.norm).const_mul |C|
  have hpt : ∀ τ ∈ ball τ0 1, ∀ x : UnforcedLeray.Space,
      ‖newtonPotential x * dτ G (τ, y - x)‖ ≤
        (closedBall y R).indicator (fun x => |C| * ‖newtonPotential x‖) x ∧
      ‖newtonPotential x * G (τ, y - x)‖ ≤
        (closedBall y R).indicator (fun x => |C| * ‖newtonPotential x‖) x := by
    intro τ hτ x
    by_cases hx : x ∈ closedBall y R
    · have hz : ‖y - x‖ ≤ R := by
        have h' := mem_closedBall.mp hx
        rw [dist_eq_norm] at h'
        rwa [norm_sub_rev]
      obtain ⟨h1, h2⟩ := hwin τ hτ (y - x) hz
      rw [Set.indicator_of_mem hx]
      constructor
      · rw [norm_mul, mul_comm |C|]
        exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      · rw [norm_mul, mul_comm |C|]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    · have hz : R < ‖y - x‖ := by
        have h' : R < dist x y := lt_of_not_ge (fun h => hx (mem_closedBall.mpr h))
        rw [dist_eq_norm] at h'
        rwa [norm_sub_rev]
      rw [Set.indicator_of_notMem hx, hzero τ (y - x) hz, hR τ (y - x) hz]
      simp
  have hcontx : ∀ τ : ℝ, Continuous (fun x : UnforcedLeray.Space => G (τ, y - x)) := fun τ =>
    hG.smooth.continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun τ x => newtonPotential x * G (τ, y - x))
    (F' := fun τ x => newtonPotential x * dτ G (τ, y - x)) (x₀ := τ0) (s := ball τ0 1)
    (bound := fun x => (closedBall y R).indicator (fun x => |C| * ‖newtonPotential x‖) x)
    (Metric.ball_mem_nhds τ0 one_pos)
    (Filter.Eventually.of_forall fun τ =>
      (newtonPotential_measurable.aestronglyMeasurable).mul (hcontx τ).aestronglyMeasurable)
    (Integrable.mono' hint
      ((newtonPotential_measurable.aestronglyMeasurable).mul (hcontx τ0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (hpt τ0 (mem_ball_self one_pos) x).2))
    ((newtonPotential_measurable.aestronglyMeasurable).mul
      (hcontD.comp (continuous_const.prodMk (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a τ hτ => (hpt τ hτ a).1)
    hint
    (Filter.Eventually.of_forall fun a τ _ =>
      (hasDerivAt_slice hG.smooth τ (y - a)).const_mul (newtonPotential a))
  exact hkey.2

/-- The coordinate maps of the real source commute with `∂_τ`. -/
theorem reCoord_dτ {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (i : Fin 3) :
    (fun q => fderiv ℝ (projectedPotentialReCoord Φ i) q (1, 0)) =
      projectedPotentialReCoord (dτ Φ) i := by
  funext q
  have hL : HasFDerivAt (fun q => projectedPotentialReCoordCLM i (Φ q))
      ((projectedPotentialReCoordCLM i).comp (fderiv ℝ Φ q)) q :=
    (projectedPotentialReCoordCLM i).hasFDerivAt.comp q
      (hΦ.smooth.differentiable (by simp) q).hasFDerivAt
  change fderiv ℝ (fun q => projectedPotentialReCoordCLM i (Φ q)) q (1, 0) = _
  rw [hL.fderiv]
  rfl

theorem reCoord_dτ_eq {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (i : Fin 3) :
    (fun q => fderiv ℝ (projectedPotentialImCoord Φ i) q (1, 0)) =
      projectedPotentialImCoord (dτ Φ) i := by
  funext q
  have hL : HasFDerivAt (fun q => projectedPotentialImCoordCLM i (Φ q))
      ((projectedPotentialImCoordCLM i).comp (fderiv ℝ Φ q)) q :=
    (projectedPotentialImCoordCLM i).hasFDerivAt.comp q
      (hΦ.smooth.differentiable (by simp) q).hasFDerivAt
  change fderiv ℝ (fun q => projectedPotentialImCoordCLM i (Φ q)) q (1, 0) = _
  rw [hL.fderiv]
  rfl

/-- `∂_τ` commutes with the spatial divergence of the real source. -/
theorem dτ_reDiv {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (p : ℝ × UnforcedLeray.Space) :
    dτ (projectedPotentialReDiv Φ) p = projectedPotentialReDiv (dτ Φ) p := by
  have hg : ∀ i : Fin 3, ContDiff ℝ ∞ (projectedPotentialReCoord Φ i) := fun i =>
    (hΦ.clm_comp (projectedPotentialReCoordCLM i)).smooth
  have hF : ∀ i : Fin 3, Differentiable ℝ
      (fun q => fderiv ℝ (projectedPotentialReCoord Φ i) q (0, coordinateVector i)) := fun i =>
    (((hg i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hsum : fderiv ℝ (projectedPotentialReDiv Φ) p = ∑ i : Fin 3,
      fderiv ℝ (fun q => fderiv ℝ (projectedPotentialReCoord Φ i) q (0, coordinateVector i)) p :=
    (HasFDerivAt.fun_sum (fun i _ => (hF i p).hasFDerivAt)).fderiv
  show fderiv ℝ (projectedPotentialReDiv Φ) p (1, 0) =
    ∑ i : Fin 3, fderiv ℝ (projectedPotentialReCoord (dτ Φ) i) p (0, coordinateVector i)
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_apply_comm_real (hg i) (1, 0) (0, coordinateVector i) p, reCoord_dτ hΦ i]

/-- `∂_τ` commutes with the spatial divergence of the imaginary source. -/
theorem dτ_imDiv {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (p : ℝ × UnforcedLeray.Space) :
    dτ (projectedPotentialImDiv Φ) p = projectedPotentialImDiv (dτ Φ) p := by
  have hg : ∀ i : Fin 3, ContDiff ℝ ∞ (projectedPotentialImCoord Φ i) := fun i =>
    (hΦ.clm_comp (projectedPotentialImCoordCLM i)).smooth
  have hF : ∀ i : Fin 3, Differentiable ℝ
      (fun q => fderiv ℝ (projectedPotentialImCoord Φ i) q (0, coordinateVector i)) := fun i =>
    (((hg i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have hsum : fderiv ℝ (projectedPotentialImDiv Φ) p = ∑ i : Fin 3,
      fderiv ℝ (fun q => fderiv ℝ (projectedPotentialImCoord Φ i) q (0, coordinateVector i)) p :=
    (HasFDerivAt.fun_sum (fun i _ => (hF i p).hasFDerivAt)).fderiv
  show fderiv ℝ (projectedPotentialImDiv Φ) p (1, 0) =
    ∑ i : Fin 3, fderiv ℝ (projectedPotentialImCoord (dτ Φ) i) p (0, coordinateVector i)
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_apply_comm_real (hg i) (1, 0) (0, coordinateVector i) p, reCoord_dτ_eq hΦ i]

/-- `∂_τ` of the real Newton correction is the Newton correction of `∂_τΦ`. -/
theorem dτ_projectedPotentialRePath {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (p : ℝ × UnforcedLeray.Space) :
    dτ (projectedPotentialRePath Φ) p = projectedPotentialRePath (dτ Φ) p := by
  obtain ⟨τ0, y⟩ := p
  have hfun : (fun τ : ℝ => projectedPotentialRePath Φ (τ, y)) =
      fun τ : ℝ => ∫ x, newtonPotential x * projectedPotentialReDiv Φ (τ, y - x) := by
    funext τ
    exact projectedPotentialRePath_eq_paramIntegral hΦ τ y
  have hG : IsPhaseTest P (projectedPotentialReDiv Φ) := isPhaseTest_projectedPotentialReDiv hΦ
  have hA : HasDerivAt (fun τ : ℝ => projectedPotentialRePath Φ (τ, y))
      (∫ x, newtonPotential x * dτ (projectedPotentialReDiv Φ) (τ0, y - x)) τ0 := by
    rw [hfun]
    exact hasDerivAt_newtonPar hG y τ0
  have hdiff : DifferentiableAt ℝ (projectedPotentialRePath Φ) (τ0, y) :=
    ((contDiff_projectedPotentialRePath hΦ).differentiable (by simp)) _
  have hpair : HasDerivAt (fun τ : ℝ => (τ, y)) ((1 : ℝ), (0 : UnforcedLeray.Space)) τ0 :=
    (hasDerivAt_id' τ0).prodMk (hasDerivAt_const τ0 y)
  have hB : HasDerivAt (fun τ : ℝ => projectedPotentialRePath Φ (τ, y))
      (fderiv ℝ (projectedPotentialRePath Φ) (τ0, y) (1, 0)) τ0 :=
    by
      have h := hdiff.hasFDerivAt.comp_hasDerivAt τ0 hpair
      exact h
  have hval := hB.unique hA
  show fderiv ℝ (projectedPotentialRePath Φ) (τ0, y) (1, 0) = projectedPotentialRePath (dτ Φ) (τ0, y)
  rw [hval]
  have hint : (∫ x, newtonPotential x * dτ (projectedPotentialReDiv Φ) (τ0, y - x)) =
      ∫ x, newtonPotential x * projectedPotentialReDiv (dτ Φ) (τ0, y - x) := by
    congr 1
    funext x
    rw [dτ_reDiv hΦ]
  rw [hint]
  exact (projectedPotentialRePath_eq_paramIntegral hΦ.dτ τ0 y).symm

/-- `∂_τ` of the imaginary Newton correction is the Newton correction of `∂_τΦ`. -/
theorem dτ_projectedPotentialImPath {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (p : ℝ × UnforcedLeray.Space) :
    dτ (projectedPotentialImPath Φ) p = projectedPotentialImPath (dτ Φ) p := by
  obtain ⟨τ0, y⟩ := p
  have hfun : (fun τ : ℝ => projectedPotentialImPath Φ (τ, y)) =
      fun τ : ℝ => ∫ x, newtonPotential x * projectedPotentialImDiv Φ (τ, y - x) := by
    funext τ
    exact projectedPotentialImPath_eq_paramIntegral hΦ τ y
  have hG : IsPhaseTest P (projectedPotentialImDiv Φ) := isPhaseTest_projectedPotentialImDiv hΦ
  have hA : HasDerivAt (fun τ : ℝ => projectedPotentialImPath Φ (τ, y))
      (∫ x, newtonPotential x * dτ (projectedPotentialImDiv Φ) (τ0, y - x)) τ0 := by
    rw [hfun]
    exact hasDerivAt_newtonPar hG y τ0
  have hdiff : DifferentiableAt ℝ (projectedPotentialImPath Φ) (τ0, y) :=
    ((contDiff_projectedPotentialImPath hΦ).differentiable (by simp)) _
  have hpair : HasDerivAt (fun τ : ℝ => (τ, y)) ((1 : ℝ), (0 : UnforcedLeray.Space)) τ0 :=
    (hasDerivAt_id' τ0).prodMk (hasDerivAt_const τ0 y)
  have hB : HasDerivAt (fun τ : ℝ => projectedPotentialImPath Φ (τ, y))
      (fderiv ℝ (projectedPotentialImPath Φ) (τ0, y) (1, 0)) τ0 :=
    by
      have h := hdiff.hasFDerivAt.comp_hasDerivAt τ0 hpair
      exact h
  have hval := hB.unique hA
  show fderiv ℝ (projectedPotentialImPath Φ) (τ0, y) (1, 0) = projectedPotentialImPath (dτ Φ) (τ0, y)
  rw [hval]
  have hint : (∫ x, newtonPotential x * dτ (projectedPotentialImDiv Φ) (τ0, y - x)) =
      ∫ x, newtonPotential x * projectedPotentialImDiv (dτ Φ) (τ0, y - x) := by
    congr 1
    funext x
    rw [dτ_imDiv hΦ]
  rw [hint]
  exact (projectedPotentialImPath_eq_paramIntegral hΦ.dτ τ0 y).symm

/-- `∂_τ` commutes with the complex Newton potential `projPot`. -/
theorem dτ_projPot {P : ℝ} {Φ : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (p : ℝ × UnforcedLeray.Space) :
    dτ (projPot Φ) p = projPot (dτ Φ) p := by
  have hR := ((contDiff_projectedPotentialRePath hΦ).differentiable (by simp)) p
  have hI := ((contDiff_projectedPotentialImPath hΦ).differentiable (by simp)) p
  have h1 : HasFDerivAt (projPot Φ)
      (Complex.ofRealCLM.comp (fderiv ℝ (projectedPotentialRePath Φ) p) +
        Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (projectedPotentialImPath Φ) p)) p := by
    have a := Complex.ofRealCLM.hasFDerivAt.comp p hR.hasFDerivAt
    have b := (Complex.ofRealCLM.hasFDerivAt.comp p hI.hasFDerivAt).const_mul Complex.I
    exact a.add b
  show fderiv ℝ (projPot Φ) p (1, 0) = projPot (dτ Φ) p
  rw [h1.fderiv]
  have hR' : fderiv ℝ (projectedPotentialRePath Φ) p (1, 0) = projectedPotentialRePath (dτ Φ) p :=
    dτ_projectedPotentialRePath hΦ p
  have hI' : fderiv ℝ (projectedPotentialImPath Φ) p (1, 0) = projectedPotentialImPath (dτ Φ) p :=
    dτ_projectedPotentialImPath hΦ p
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [hR', hI']
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.ProjPotDtauAux

open UnforcedLeray.Short.PartIIIb.Concrete.ProjPotDtauAux in
theorem projPotDtau : UnforcedLeray.Short.PartIIIb.Concrete.ProjPotDtau := by
  intro P _ Φ hΦ
  funext p
  exact dτ_projPot hΦ p
