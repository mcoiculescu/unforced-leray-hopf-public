import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `AdjGrad` (task `PartIII-b:C/near/pins/3/5/4/2` target `adjGrad`)

For `a > 0`, `t ≥ 0` and a phase test `φ`, the gradient of `χ = adjChi a t φ` is `adjGradT a t φ`.
Differentiation under the Gaussian integral (`hasFDerivAt_integral_of_dominated_of_fderiv_le`,
dominated by `G_a(w) · sup‖∇φ‖`), the chain rule for `y ↦ c(y - w)` with `c = e^{-t/2}`, and the
two factors of `c` giving `e^{-t}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Gaussian

/-- The linear part of the argument map `y ↦ (τ + t, c • (y - w))`. -/
def adjM (c : ℝ) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  (ContinuousLinearMap.fst ℝ ℝ Space).prod (c • ContinuousLinearMap.snd ℝ ℝ Space)

theorem hasFDerivAt_shiftArg (t c : ℝ) (w : Space) (x : ℝ × Space) :
    HasFDerivAt (fun x : ℝ × Space => (x.1 + t, c • (x.2 - w))) (adjM c) x :=
  (hasFDerivAt_fst.add_const t).prodMk ((hasFDerivAt_snd.sub_const w).const_smul c)

theorem continuous_shiftArg (t c : ℝ) (x : ℝ × Space) :
    Continuous (fun w : Space => ((x.1 + t, c • (x.2 - w)) : ℝ × Space)) := by
  fun_prop

/-- A continuous `P`-periodic function vanishing for large `y` is bounded. -/
theorem bdd_of_periodic_far {E : Type*} [NormedAddCommGroup E] {P : ℝ} (hP : 0 < P)
    {g : ℝ × Space → E} (hc : Continuous g) (hper : ∀ τ y, g (τ + P, y) = g (τ, y))
    {R : ℝ} (hfar : ∀ p : ℝ × Space, R < ‖p.2‖ → g p = 0) :
    ∃ M : ℝ, ∀ p, ‖g p‖ ≤ M := by
  obtain ⟨M0, hM0⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := P)).prod
    (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M0 0, fun p => ?_⟩
  obtain ⟨τ', hτ', heq⟩ := (show Function.Periodic (fun τ : ℝ => g (τ, p.2)) P from
    fun τ => hper τ p.2).exists_mem_Ico₀ hP p.1
  have heq' : g p = g (τ', p.2) := heq
  by_cases hy : ‖p.2‖ ≤ R
  · have hmem : (τ', p.2) ∈ Icc (0:ℝ) P ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨⟨hτ'.1, hτ'.2.le⟩, mem_closedBall_zero_iff.2 hy⟩
    rw [heq']
    exact (hM0 _ hmem).trans (le_max_left _ _)
  · push Not at hy
    rw [heq', hfar (τ', p.2) hy]
    simp

theorem fderiv_eq_zero_far' {φ : ℝ × Space → ℂ} {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → φ (τ, y) = 0) (p : ℝ × Space) (hp : R < ‖p.2‖) :
    fderiv ℝ φ p = 0 := by
  have hopen : IsOpen {q : ℝ × Space | R < ‖q.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : φ =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hR q.1 q.2 hq
  rw [hev.fderiv_eq]
  simp

/-- The derivative of a phase test is bounded. -/
theorem fderiv_bdd {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) :
    ∃ C : ℝ, ∀ p, ‖fderiv ℝ φ p‖ ≤ C := by
  obtain ⟨R, hR⟩ := hφ.bounded_support
  have hper : ∀ τ y, fderiv ℝ φ (τ + P, y) = fderiv ℝ φ (τ, y) := fun τ y =>
    ContinuousLinearMap.ext fun v => periodic_fderiv_apply hφ.periodic v τ y
  have hcont : Continuous (fderiv ℝ φ) := hφ.smooth.continuous_fderiv (by simp)
  exact bdd_of_periodic_far hP hcont hper (fun p hp => fderiv_eq_zero_far' hR p hp)

/-- Integrability of `w ↦ G(w) • g(w)` for a bounded continuous `g`. -/
theorem integrable_gauss_smul {a : ℝ} (ha : 0 < a) {g : Euc 3 → ℂ} (hg : Continuous g)
    {C : ℝ} (hC : ∀ w, ‖g w‖ ≤ C) :
    Integrable (fun w : Euc 3 => gaussKernel 3 a w • g w) := by
  refine Integrable.mono' ((integrable_gaussKernel (d := 3) ha).mul_const C) ?_
    (Eventually.of_forall fun w => ?_)
  · exact ((continuous_gaussKernel (d := 3) a).smul hg).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    exact mul_le_mul_of_nonneg_left (hC w) (gaussKernel_nonneg ha w)

/-- Differentiation under the Gaussian integral for the adjoint scalar test. -/
theorem hasFDerivAt_adjInt {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ)
    {a : ℝ} (ha : 0 < a) (t c : ℝ) (x0 : ℝ × Space) :
    HasFDerivAt (fun x : ℝ × Space => ∫ w : Euc 3, gaussKernel 3 a w • φ (x.1 + t, c • (x.2 - w)))
      (∫ w : Euc 3, gaussKernel 3 a w • ((fderiv ℝ φ (x0.1 + t, c • (x0.2 - w))).comp (adjM c)))
      x0 := by
  obtain ⟨Cd, hCd⟩ := fderiv_bdd hP hφ
  obtain ⟨R, hR⟩ := hφ.bounded_support
  obtain ⟨Cφ, hCφ⟩ := bdd_of_periodic_far hP hφ.continuous hφ.periodic
    (fun p hp => hR p.1 p.2 hp)
  have hcontFd : Continuous (fderiv ℝ φ) := hφ.smooth.continuous_fderiv (by simp)
  have hdiff : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hF_cont : ∀ x : ℝ × Space,
      Continuous (fun w : Euc 3 => gaussKernel 3 a w • φ (x.1 + t, c • (x.2 - w))) := fun x =>
    (continuous_gaussKernel (d := 3) a).smul (hφ.continuous.comp (continuous_shiftArg t c x))
  have hF_bnd : ∀ (x : ℝ × Space) (w : Euc 3),
      ‖gaussKernel 3 a w • φ (x.1 + t, c • (x.2 - w))‖ ≤ gaussKernel 3 a w * Cφ := by
    intro x w
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    exact mul_le_mul_of_nonneg_left (hCφ _) (gaussKernel_nonneg ha w)
  have hD_bnd : ∀ (x : ℝ × Space) (w : Euc 3),
      ‖gaussKernel 3 a w • ((fderiv ℝ φ (x.1 + t, c • (x.2 - w))).comp (adjM c))‖
        ≤ gaussKernel 3 a w * (Cd * ‖adjM c‖) := by
    intro x w
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    refine mul_le_mul_of_nonneg_left ?_ (gaussKernel_nonneg ha w)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hCd _) (norm_nonneg _)
  have hD_cont : ∀ x : ℝ × Space,
      Continuous (fun w : Euc 3 =>
        gaussKernel 3 a w • ((fderiv ℝ φ (x.1 + t, c • (x.2 - w))).comp (adjM c))) := fun x =>
    (continuous_gaussKernel (d := 3) a).smul
      ((hcontFd.comp (continuous_shiftArg t c x)).clm_comp continuous_const)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x (w : Euc 3) => gaussKernel 3 a w • φ (x.1 + t, c • (x.2 - w)))
    (F' := fun x (w : Euc 3) =>
      gaussKernel 3 a w • ((fderiv ℝ φ (x.1 + t, c • (x.2 - w))).comp (adjM c)))
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

/-- A uniform bound on a phase derivative `∂_j φ`. -/
theorem norm_dy_le {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (j : Fin 3) :
    ∃ C : ℝ, ∀ p, ‖PhaseSpace.dy j φ p‖ ≤ C := by
  obtain ⟨Cd, hCd⟩ := fderiv_bdd hP hφ
  refine ⟨Cd * ‖(((0 : ℝ), coordinateVector j) : ℝ × Space)‖, fun p => ?_⟩
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hCd p) (norm_nonneg _))

/-- The integrability of the adjoint derivative family. -/
theorem integrable_adjD {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ)
    {a : ℝ} (ha : 0 < a) (t c : ℝ) (x0 : ℝ × Space) :
    Integrable (fun w : Euc 3 =>
      gaussKernel 3 a w • ((fderiv ℝ φ (x0.1 + t, c • (x0.2 - w))).comp (adjM c))) := by
  obtain ⟨Cd, hCd⟩ := fderiv_bdd hP hφ
  have hcontFd : Continuous (fderiv ℝ φ) := hφ.smooth.continuous_fderiv (by simp)
  refine Integrable.mono' ((integrable_gaussKernel (d := 3) ha).mul_const (Cd * ‖adjM c‖)) ?_
    (Eventually.of_forall fun w => ?_)
  · exact ((continuous_gaussKernel (d := 3) a).smul
      ((hcontFd.comp (continuous_shiftArg t c x0)).clm_comp continuous_const)).aestronglyMeasurable
  · rw [norm_smul, Real.norm_of_nonneg (gaussKernel_nonneg ha w)]
    refine mul_le_mul_of_nonneg_left ?_ (gaussKernel_nonneg ha w)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hCd _) (norm_nonneg _)

/-- The partial derivative of the adjoint scalar test. -/
theorem dy_adj {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ)
    {a : ℝ} (ha : 0 < a) (t c : ℝ) (x0 : ℝ × Space) (j : Fin 3) :
    PhaseSpace.dy j (fun x : ℝ × Space =>
        c • ∫ w : Euc 3, gaussKernel 3 a w • φ (x.1 + t, c • (x.2 - w))) x0
      = c • ∫ w : Euc 3, gaussKernel 3 a w • (c • PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w))) := by
  have hfd : fderiv ℝ (fun x : ℝ × Space =>
        c • ∫ w : Euc 3, gaussKernel 3 a w • φ (x.1 + t, c • (x.2 - w))) x0
      = c • ∫ w : Euc 3, gaussKernel 3 a w •
          ((fderiv ℝ φ (x0.1 + t, c • (x0.2 - w))).comp (adjM c)) :=
    ((hasFDerivAt_adjInt hP hφ ha t c x0).const_smul c).fderiv
  simp only [PhaseSpace.dy]
  rw [hfd, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.integral_apply (integrable_adjD hP hφ ha t c x0)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  have hv : adjM c ((0 : ℝ), coordinateVector j) = c • ((0 : ℝ), coordinateVector j) := by
    simp [adjM]
  dsimp only
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hv, map_smul]

/-- The vector gradient of a Gaussian average splits along the coordinate basis. -/
theorem integral_gradT_split {P : ℝ} (hP : 0 < P) {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ)
    {a : ℝ} (ha : 0 < a) (t c : ℝ) (x0 : ℝ × Space) :
    ∫ w : Euc 3, gaussKernel 3 a w • PhaseSpace.gradT φ (x0.1 + t, c • (x0.2 - w))
      = ∑ j : Fin 3, (∫ w : Euc 3, gaussKernel 3 a w • PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w)))
          • EuclideanSpace.single j (1 : ℂ) := by
  have hcont : ∀ j : Fin 3, Continuous
      (fun w : Euc 3 => PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w))) := fun j =>
    ((hφ.dy j).continuous).comp (continuous_shiftArg t c x0)
  choose Cj hCj using fun j => norm_dy_le hP hφ j
  have hint : ∀ j : Fin 3, Integrable (fun w : Euc 3 =>
      (gaussKernel 3 a w • PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w))) •
        EuclideanSpace.single j (1 : ℂ)) := fun j =>
    (integrable_gauss_smul ha (g := fun w : Euc 3 => PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w)))
      (hcont j) (C := Cj j) (fun w => hCj j _)).smul_const _
  calc ∫ w : Euc 3, gaussKernel 3 a w • PhaseSpace.gradT φ (x0.1 + t, c • (x0.2 - w))
      = ∫ w : Euc 3, ∑ j : Fin 3,
          (gaussKernel 3 a w • PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w)))
            • EuclideanSpace.single j (1 : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [PhaseSpace.gradT]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_assoc]
    _ = ∑ j : Fin 3, ∫ w : Euc 3,
          (gaussKernel 3 a w • PhaseSpace.dy j φ (x0.1 + t, c • (x0.2 - w)))
            • EuclideanSpace.single j (1 : ℂ) :=
        integral_finsetSum _ fun j _ => hint j
    _ = _ := Finset.sum_congr rfl fun j _ => integral_smul_const _ _

/-- **Leaf 2** (`AdjGrad`): `∇ (adjChi a t φ) = adjGradT a t φ`. -/
theorem adjGrad : AdjGrad := by
  intro P hPf a t ha _ φ hφ
  have hP : 0 < P := hPf.out
  funext x0
  have hcc : Real.exp (-t / 2) * Real.exp (-t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  have key : ∀ j : Fin 3,
      Real.exp (-t / 2) • ∫ w : Euc 3, gaussKernel 3 a w •
        (Real.exp (-t / 2) • PhaseSpace.dy j φ (x0.1 + t, Real.exp (-t / 2) • (x0.2 - w)))
      = Real.exp (-t) • ∫ w : Euc 3, gaussKernel 3 a w •
        PhaseSpace.dy j φ (x0.1 + t, Real.exp (-t / 2) • (x0.2 - w)) := by
    intro j
    calc _ = Real.exp (-t / 2) • ∫ w : Euc 3, Real.exp (-t / 2) •
          (gaussKernel 3 a w • PhaseSpace.dy j φ (x0.1 + t, Real.exp (-t / 2) • (x0.2 - w))) := by
          congr 1
          exact integral_congr_ae (Eventually.of_forall fun w => smul_comm _ _ _)
      _ = (Real.exp (-t / 2) * Real.exp (-t / 2)) • ∫ w : Euc 3,
          gaussKernel 3 a w • PhaseSpace.dy j φ (x0.1 + t, Real.exp (-t / 2) • (x0.2 - w)) := by
          rw [integral_smul, smul_smul]
      _ = _ := by rw [hcc]
  unfold adjChi adjGradT
  rw [integral_gradT_split hP hφ ha t (Real.exp (-t / 2)) x0]
  simp only [PhaseSpace.gradT, dy_adj hP hφ ha t (Real.exp (-t / 2)) x0]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, smul_assoc]

end UnforcedLeray.Short.PartIIIb.NearInst
