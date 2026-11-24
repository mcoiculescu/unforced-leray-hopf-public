import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.SemigroupAdjointGrad.Grad
import UnforcedLeray.Lib.HeatR3.Admissible
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `AdjSmooth` (task `PartIII-b:C/near/pins/3/5/4/2`, target `adjSmooth`)

For `a > 0`, `t ≥ 0` and a phase test `φ`, the scalar test `χ = adjChi a t φ` is an `L²` test:

* smoothness: `χ = e^{-t/2} • adjAvgC a t (e^{-t/2}) φ`, and `adjAvgC` is `C^n` for every `n`
  (induction on `n`, differentiation under the Gaussian integral at each level, with the derivative
  of a phase test again a phase test);
* periodicity in `τ` from the periodicity of `φ`;
* integrability on one period: a pointwise decay bound `|adjAvgC ψ (τ,y)| ≤ K (1+|y|)^{-2}`
  (the phase test is bounded and supported in a ball, so the Gaussian mass seen by the
  integrand decays like `G_a(w)` with `|w| ≈ |y|`), and `(1+|y|)^{-4}` is integrable on `ℝ³`.
  The gradient is handled through `adjGrad`, which identifies `gradT χ` with `adjGradT`, an
  `e^{-t}`-multiple of the same kind of average of `gradT φ`.

Source: `the November 2 reference manuscript` lines 1339-1362 (free Cartesian
foundation, the Gaussian representation of the adjoint test).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Gaussian

/-- The Gaussian average `x ↦ ∫ G_a(w) ψ(τ+t, c(y-w)) dw`; `adjChi a t φ = e^{-t/2} • adjAvgC a t
(e^{-t/2}) φ` and `adjGradT a t φ = e^{-t} • adjAvgC a t (e^{-t/2}) (gradT φ)`. -/
def adjAvgC (a t c : ℝ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ × Space → E) : ℝ × Space → E :=
  fun x => ∫ w : Euc 3, gaussKernel 3 a w • ψ (x.1 + t, c • (x.2 - w))

theorem adjS_fderiv_far {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ × Space → E} {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → ψ (τ, y) = 0) (p : ℝ × Space)
    (hp : R < ‖p.2‖) : fderiv ℝ ψ p = 0 := by
  have hopen : IsOpen {q : ℝ × Space | R < ‖q.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : ψ =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hR q.1 q.2 hq
  rw [hev.fderiv_eq]
  simp

theorem adjS_bdd {P : ℝ} (hP : 0 < P) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) : ∃ M : ℝ, ∀ p, ‖ψ p‖ ≤ M := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  exact bdd_of_periodic_far hP hψ.smooth.continuous hψ.periodic (fun p hp => hR p.1 p.2 hp)

theorem adjS_fderiv_isPT {P : ℝ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) : IsPhaseTest P (fderiv ℝ ψ) := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  refine ⟨(contDiff_infty_iff_fderiv.1 hψ.smooth).2, fun τ y => ?_, ⟨R, fun τ y hy => ?_⟩⟩
  · exact ContinuousLinearMap.ext fun v => periodic_fderiv_apply hψ.periodic v τ y
  · exact adjS_fderiv_far hR (τ, y) hy

theorem adjS_continuous_avg {P : ℝ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) (x : ℝ × Space) {a : ℝ} (t c : ℝ) :
    Continuous (fun w : Euc 3 => gaussKernel 3 a w • ψ (x.1 + t, c • (x.2 - w))) :=
  (continuous_gaussKernel (d := 3) a).smul (hψ.continuous.comp (continuous_shiftArg t c x))

theorem adjS_integrable_avg {P : ℝ} (hP : 0 < P) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) {a : ℝ} (ha : 0 < a)
    (t c : ℝ) (x : ℝ × Space) :
    Integrable (fun w : Euc 3 => gaussKernel 3 a w • ψ (x.1 + t, c • (x.2 - w))) := by
  obtain ⟨Cφ, hCφ⟩ := adjS_bdd hP hψ
  refine Integrable.mono' ((integrable_gaussKernel (d := 3) ha).mul_const Cφ)
    (adjS_continuous_avg hψ x t c).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
  exact mul_le_mul_of_nonneg_left (hCφ _) (gaussKernel_nonneg ha w)

theorem adjS_hasFDerivAt {P : ℝ} (hP : 0 < P) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) {a : ℝ} (ha : 0 < a)
    (t c : ℝ) (x0 : ℝ × Space) :
    HasFDerivAt (adjAvgC a t c ψ)
      (∫ w : Euc 3, gaussKernel 3 a w • ((fderiv ℝ ψ (x0.1 + t, c • (x0.2 - w))).comp (adjM c)))
      x0 := by
  obtain ⟨Cd, hCd⟩ := adjS_bdd hP (adjS_fderiv_isPT hψ)
  obtain ⟨Cφ, hCφ⟩ := adjS_bdd hP hψ
  have hcontFd : Continuous (fderiv ℝ ψ) := hψ.smooth.continuous_fderiv (by simp)
  have hdiff : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hF_cont : ∀ x : ℝ × Space,
      Continuous (fun w : Euc 3 => gaussKernel 3 a w • ψ (x.1 + t, c • (x.2 - w))) := fun x =>
    adjS_continuous_avg hψ x t c
  have hF_bnd : ∀ (x : ℝ × Space) (w : Euc 3),
      ‖gaussKernel 3 a w • ψ (x.1 + t, c • (x.2 - w))‖ ≤ gaussKernel 3 a w * Cφ := by
    intro x w
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    exact mul_le_mul_of_nonneg_left (hCφ _) (gaussKernel_nonneg ha w)
  have hD_bnd : ∀ (x : ℝ × Space) (w : Euc 3),
      ‖gaussKernel 3 a w • ((fderiv ℝ ψ (x.1 + t, c • (x.2 - w))).comp (adjM c))‖
        ≤ gaussKernel 3 a w * (Cd * ‖adjM c‖) := by
    intro x w
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    refine mul_le_mul_of_nonneg_left ?_ (gaussKernel_nonneg ha w)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hCd _) (norm_nonneg _)
  have hD_cont : ∀ x : ℝ × Space,
      Continuous (fun w : Euc 3 =>
        gaussKernel 3 a w • ((fderiv ℝ ψ (x.1 + t, c • (x.2 - w))).comp (adjM c))) := fun x =>
    (continuous_gaussKernel (d := 3) a).smul
      ((hcontFd.comp (continuous_shiftArg t c x)).clm_comp continuous_const)
  unfold adjAvgC
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x (w : Euc 3) => gaussKernel 3 a w • ψ (x.1 + t, c • (x.2 - w)))
    (F' := fun x (w : Euc 3) =>
      gaussKernel 3 a w • ((fderiv ℝ ψ (x.1 + t, c • (x.2 - w))).comp (adjM c)))
    (bound := fun w : Euc 3 => gaussKernel 3 a w * (Cd * ‖adjM c‖))
    univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => (hF_cont x).aestronglyMeasurable
  · exact Integrable.mono' ((integrable_gaussKernel (d := 3) ha).mul_const Cφ)
      (hF_cont x0).aestronglyMeasurable (Eventually.of_forall fun w => hF_bnd x0 w)
  · exact (hD_cont x0).aestronglyMeasurable
  · exact Eventually.of_forall fun w x _ => hD_bnd x w
  · exact (integrable_gaussKernel (d := 3) ha).mul_const _
  · refine Eventually.of_forall fun w x _ => ?_
    exact (((hdiff _).hasFDerivAt).comp x (hasFDerivAt_shiftArg t c w x)).const_smul
      (gaussKernel 3 a w)

theorem adjS_continuous {P : ℝ} (hP : 0 < P) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ : ℝ × Space → E} (hψ : IsPhaseTest P ψ) {a : ℝ} (ha : 0 < a)
    (t c : ℝ) : Continuous (adjAvgC a t c ψ) := by
  obtain ⟨Cφ, hCφ⟩ := adjS_bdd hP hψ
  unfold adjAvgC
  refine continuous_of_dominated (bound := fun w : Euc 3 => gaussKernel 3 a w * Cφ)
    (fun x => (adjS_continuous_avg hψ x t c).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun w => ?_)
    ((integrable_gaussKernel (d := 3) ha).mul_const Cφ)
    (Eventually.of_forall fun w => ?_)
  · rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    exact mul_le_mul_of_nonneg_left (hCφ _) (gaussKernel_nonneg ha w)
  · exact (hψ.continuous.comp ((continuous_fst.add continuous_const).prodMk
      ((continuous_snd.sub continuous_const).const_smul c))).const_smul (gaussKernel 3 a w)

/-- The `n`-times continuous differentiability of the Gaussian average of a phase test,
for every target space `E`, by induction on `n` (derivative of a phase test is a phase test). -/
theorem adjS_contDiff {P : ℝ} (hP : 0 < P) {a : ℝ} (ha : 0 < a) (t c : ℝ) :
    ∀ n : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (ψ : ℝ × Space → E), IsPhaseTest P ψ → ContDiff ℝ n (adjAvgC a t c ψ) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ ψ hψ
    exact contDiff_zero.2 (adjS_continuous hP hψ ha t c)
  | succ n ih =>
    intro E _ _ _ ψ hψ
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl]
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (adjS_hasFDerivAt hP hψ ha t c x).differentiableAt,
      fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · set K : (ℝ × Space →L[ℝ] E) →L[ℝ] ((ℝ × Space) →L[ℝ] E) :=
        (ContinuousLinearMap.compL ℝ (ℝ × Space) (ℝ × Space) E).flip (adjM c) with hK
      have hKapp : ∀ L : ℝ × Space →L[ℝ] E, K L = L.comp (adjM c) := fun L => rfl
      have hfd : fderiv ℝ (adjAvgC a t c ψ) = fun x => K (adjAvgC a t c (fderiv ℝ ψ) x) := by
        funext x
        rw [(adjS_hasFDerivAt hP hψ ha t c x).fderiv]
        unfold adjAvgC
        rw [← ContinuousLinearMap.integral_comp_comm K
          (adjS_integrable_avg hP (adjS_fderiv_isPT hψ) ha t c x)]
        congr 1
      rw [hfd]
      exact K.contDiff.comp (ih _ (fderiv ℝ ψ) (adjS_fderiv_isPT hψ))

/-- Pointwise decay of the Gaussian average of a phase test: `|adjAvgC ψ (τ,y)| ≤ K (1+|y|)^{-2}`. -/
theorem adjS_decay {P : ℝ} (hP : 0 < P) {a : ℝ} (ha : 0 < a) (t c : ℝ) (hc : 0 < c)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : ℝ × Space → E}
    (hψ : IsPhaseTest P ψ) :
    ∃ K : ℝ, ∀ x : ℝ × Space, ‖adjAvgC a t c ψ x‖ ≤ K * (1 + ‖x.2‖) ^ (-(2:ℝ)) := by
  obtain ⟨M, hM⟩ := adjS_bdd hP hψ
  obtain ⟨R, hR⟩ := hψ.bounded_support
  obtain ⟨C, hC0, hC⟩ := UnforcedLeray.Heat.gaussKernel_le_weight 3 ha (m := 2) (by norm_num)
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set ρ : ℝ := max R 0 / c with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (le_max_right _ _) hc.le
  have hcρ : c * ρ = max R 0 := by
    rw [hρ]; field_simp
  have hvol : ∀ y : Space, volume.real (closedBall y ρ) = volume.real (closedBall (0 : Space) ρ) := by
    intro y
    rw [measureReal_def, measureReal_def, Measure.addHaar_closedBall volume y hρ0,
      Measure.addHaar_closedBall volume 0 hρ0]
  refine ⟨volume.real (closedBall (0 : Space) ρ) * (C * (1 + ρ) ^ (2:ℝ) * M), fun x => ?_⟩
  obtain ⟨τ, y⟩ := x
  have hpt : ∀ w : Space,
      ‖gaussKernel 3 a w • ψ (τ + t, c • (y - w))‖ ≤
        Set.indicator (closedBall y ρ)
          (fun _ => C * (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) * M) w := by
    intro w
    by_cases hw : w ∈ closedBall y ρ
    · rw [Set.indicator_of_mem hw, norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
      have hwy : ‖y - w‖ ≤ ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hw
        rwa [norm_sub_rev]
      have h1 : 1 + ‖y‖ ≤ (1 + ρ) * (1 + ‖w‖) := by
        have : ‖y‖ ≤ ‖w‖ + ‖y - w‖ := by
          have h := norm_add_le (y - w) w
          rw [sub_add_cancel] at h
          linarith
        nlinarith [norm_nonneg w]
      have hYZ : (1 + ρ) ^ (-(2:ℝ)) * (1 + ‖w‖) ^ (-(2:ℝ)) ≤ (1 + ‖y‖) ^ (-(2:ℝ)) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      have hQZ : (1 + ρ) ^ (2:ℝ) * (1 + ρ) ^ (-(2:ℝ)) = 1 := by
        rw [← Real.rpow_add (by positivity)]; norm_num
      have hX : (1 + ‖w‖) ^ (-(2:ℝ)) ≤ (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) := by
        have h2 := mul_le_mul_of_nonneg_left hYZ (show (0:ℝ) ≤ (1 + ρ) ^ (2:ℝ) by positivity)
        rw [← mul_assoc, hQZ, one_mul] at h2
        exact h2
      have hG : gaussKernel 3 a w ≤ C * (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) := by
        have := hC w
        nlinarith
      calc gaussKernel 3 a w * ‖ψ (τ + t, c • (y - w))‖
          ≤ gaussKernel 3 a w * M := mul_le_mul_of_nonneg_left (hM _) (gaussKernel_nonneg ha w)
        _ ≤ C * (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) * M :=
          mul_le_mul_of_nonneg_right hG hMnn
    · rw [Set.indicator_of_notMem hw]
      have hlt : ρ < ‖y - w‖ := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hw
        rwa [norm_sub_rev]
      have hR' : R < ‖c • (y - w)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hc.le]
        have h2 : c * ρ < c * ‖y - w‖ := mul_lt_mul_of_pos_left hlt hc
        have h3 : R ≤ max R 0 := le_max_left _ _
        linarith
      have h0 : ψ (τ + t, c • (y - w)) = 0 := hR _ _ hR'
      simp [h0]
  have hint : Integrable (Set.indicator (closedBall y ρ)
      (fun _ => C * (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) * M)) := by
    refine (integrableOn_const ?_).integrable_indicator measurableSet_closedBall
    exact measure_closedBall_lt_top.ne
  calc ‖adjAvgC a t c ψ (τ, y)‖
      = ‖∫ w : Euc 3, gaussKernel 3 a w • ψ (τ + t, c • (y - w))‖ := rfl
    _ ≤ ∫ w : Euc 3, Set.indicator (closedBall y ρ)
          (fun _ => C * (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) * M) w :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = volume.real (closedBall y ρ) •
          (C * (1 + ρ) ^ (2:ℝ) * (1 + ‖y‖) ^ (-(2:ℝ)) * M) :=
        integral_indicator_const _ measurableSet_closedBall
    _ = volume.real (closedBall (0 : Space) ρ) * (C * (1 + ρ) ^ (2:ℝ) * M) *
          (1 + ‖y‖) ^ (-(2:ℝ)) := by
        rw [hvol y, smul_eq_mul]; ring
    _ = volume.real (closedBall (0 : Space) ρ) * (C * (1 + ρ) ^ (2:ℝ) * M) *
          (1 + ‖(τ, y).2‖) ^ (-(2:ℝ)) := rfl

/-- Square integrability of the Gaussian average over one phase period. -/
theorem adjS_integrableOn {P : ℝ} (hP : 0 < P) {a : ℝ} (ha : 0 < a) (t c : ℝ) (hc : 0 < c)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : ℝ × Space → E}
    (hψ : IsPhaseTest P ψ) :
    IntegrableOn (fun x : ℝ × Space => ‖adjAvgC a t c ψ x‖ ^ 2)
      (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) := by
  obtain ⟨K, hK⟩ := adjS_decay hP ha t c hc hψ
  have hsq : ∀ y : Space, ((1 + ‖y‖) ^ (-(2:ℝ))) ^ 2 = (1 + ‖y‖) ^ (-(4:ℝ)) := by
    intro y
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hint1 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4:ℝ))) := by
    refine integrable_one_add_norm ?_
    simp [finrank_euclideanSpace]
    norm_num
  have hint2 : Integrable (fun τ : ℝ => Set.indicator (Ioc (0:ℝ) P) (fun _ => (1:ℝ)) τ) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  have hprod : Integrable (fun x : ℝ × Space =>
      Set.indicator (Ioc (0:ℝ) P) (fun _ => (1:ℝ)) x.1 * (K ^ 2 * (1 + ‖x.2‖) ^ (-(4:ℝ)))) := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod hint2 (hint1.const_mul (K ^ 2))
  have hmeas : MeasurableSet (Ioc (0:ℝ) P ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  refine Integrable.mono' hprod.integrableOn
    (((adjS_continuous hP hψ ha t c).norm.pow 2).aestronglyMeasurable) ?_
  refine (ae_restrict_mem hmeas).mono fun x hx => ?_
  rw [Set.indicator_of_mem hx.1, one_mul, Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖adjAvgC a t c ψ x‖ ^ 2 ≤ (K * (1 + ‖x.2‖) ^ (-(2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hK x) 2
    _ = K ^ 2 * (1 + ‖x.2‖) ^ (-(4:ℝ)) := by rw [mul_pow, hsq]

/-- **Leaf 1** (`AdjSmooth`): `adjChi a t φ` is an `L²` test. -/
theorem adjSmooth : AdjSmooth := by
  intro P hPf a t ha ht φ hφ
  have hP : 0 < P := hPf.out
  have hc : 0 < Real.exp (-t / 2) := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · have hsm : ContDiff ℝ ∞ (fun x : ℝ × Space =>
        (Real.exp (-t / 2) : ℝ) • adjAvgC a t (Real.exp (-t / 2)) φ x) :=
      contDiff_infty.2 fun n => ContDiff.const_smul (Real.exp (-t / 2))
        (adjS_contDiff hP ha t (Real.exp (-t / 2)) n ℂ φ hφ)
    exact hsm
  · intro τ y
    have hshift : ∀ (c' : ℝ) (z : Space), φ (τ + P + t, c' • z) = φ (τ + t, c' • z) := by
      intro c' z
      rw [show τ + P + t = (τ + t) + P by ring]
      exact hφ.periodic _ _
    show (Real.exp (-t / 2) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w • φ (τ + P + t, Real.exp (-t / 2) • (y - w))
      = (Real.exp (-t / 2) : ℝ) • ∫ w : Euc 3, gaussKernel 3 a w • φ (τ + t, Real.exp (-t / 2) • (y - w))
    simp only [hshift]
  · have hgrad : gradT (adjChi a t φ) = adjGradT a t φ := adjGrad P a t ha ht φ hφ
    have e : (fun x : ℝ × Space => ‖adjChi a t φ x‖ ^ 2 + ‖gradT (adjChi a t φ) x‖ ^ 2) =
        fun x => ‖(Real.exp (-t / 2) : ℝ) • adjAvgC a t (Real.exp (-t / 2)) φ x‖ ^ 2 +
          ‖(Real.exp (-t) : ℝ) • adjAvgC a t (Real.exp (-t / 2)) (gradT φ) x‖ ^ 2 := by
      funext x
      rw [hgrad]
      rfl
    rw [e]
    have hA : IntegrableOn (fun x : ℝ × Space =>
        ‖(Real.exp (-t / 2) : ℝ) • adjAvgC a t (Real.exp (-t / 2)) φ x‖ ^ 2)
        (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) := by
      refine Integrable.congr
        ((adjS_integrableOn hP ha t (Real.exp (-t / 2)) hc hφ).const_mul ((Real.exp (-t / 2)) ^ 2)) ?_
      exact Eventually.of_forall fun x => by
        simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hB : IntegrableOn (fun x : ℝ × Space =>
        ‖(Real.exp (-t) : ℝ) • adjAvgC a t (Real.exp (-t / 2)) (gradT φ) x‖ ^ 2)
        (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) := by
      refine Integrable.congr
        ((adjS_integrableOn hP ha t (Real.exp (-t / 2)) hc hφ.gradT).const_mul ((Real.exp (-t)) ^ 2)) ?_
      exact Eventually.of_forall fun x => by
        simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact hA.add hB

end UnforcedLeray.Short.PartIIIb.NearInst
