import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatGradIdentity.Reduction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `PartII-a:N01/9/1/2/4/6/2` (decomposition): `HeatGradIdentity`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383.  `HeatGradIdentity` is reduced (via `heatGradIdentity_of`) to the
analytic core `HeatIntDiffCore` (differentiation of the heat integral in `z` under the
`σ`-integral).  The core is proved here from four elementary analytic facts about the
`C¹` slices `Ψ(σ,w) = σ⁻¹ F(σ,w)` and the planar heat `planeHeat`:

* `HGIPsiBounds` : `Ψ` is `C¹`, vanishes for `σ < s₁`, and `Ψ`, `DΨ` are bounded;
* `HGIPlaneHeatNorm` : the planar heat of a bounded `C¹` function with bounded derivative is
  differentiable, with the derivative falling on the function, and all norms stay `≤ K`;
* `HGIPlaneHeatContSigma` : continuity in a parameter `σ` of the planar heat `planeHeat (T σ) (G σ ·) x`
  (dilated Gaussian form `planeHeat_eq_dilate` and dominated convergence).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped Interval

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **(S1)** Bounds for the slice function `Ψ p = p.1⁻¹ • F p` of a smooth force (lines 1684-1689):
`Ψ` is `C¹` (it vanishes for `p.1 < s₁`), and `Ψ` and `DΨ` are bounded on the whole of `Profile`
(`F` is `c`-periodic in `q`, supported in a compact set of `(σ,η)`; compactness of
`[s₁,s₂] × [0,c] × [-R,R]`, as in `HeatSliceBounds`, `hsb_bounded_of_periodic_band`). -/
def HGIPsiBounds : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∃ s₁ K : ℝ, 0 < s₁ ∧ ContDiff ℝ 1 (fun p : Profile => p.1⁻¹ • F p) ∧
      (∀ p : Profile, p.1 < s₁ → p.1⁻¹ • F p = 0) ∧
      ∀ p : Profile, ‖p.1⁻¹ • F p‖ ≤ K ∧
        ‖fderiv ℝ (fun p : Profile => p.1⁻¹ • F p) p‖ ≤ K

/-- **(S2)** The planar heat of a `C¹` function with `‖u‖ ≤ K`, `‖Du‖ ≤ K` is differentiable, keeps
the bounds, and its derivative is the planar heat of the derivative (any `θ`; for `θ ≤ 0` the heat
is the identity, `B0224.planeHeat_of_nonpos`; for `θ > 0` it is the Gaussian average and the
derivative falls on `u`: `planeHeat_fderiv_apply` in `HeatIntRegular/PlaneHeatFderiv.lean`;
`‖planeHeat θ g x‖ ≤ sup ‖g‖` from `Gaussian.integral_gaussKernel`; lines 3373-3383). -/
def HGIPlaneHeatNorm : Prop :=
  ∀ (θ K : ℝ) (u : ℝ × ℝ → MeridC), ContDiff ℝ 1 u → (∀ x, ‖u x‖ ≤ K) →
    (∀ x, ‖fderiv ℝ u x‖ ≤ K) →
      Differentiable ℝ (UnforcedLeray.B0224.planeHeat θ u) ∧
      (∀ x, ‖UnforcedLeray.B0224.planeHeat θ u x‖ ≤ K) ∧
      (∀ x, ‖fderiv ℝ (UnforcedLeray.B0224.planeHeat θ u) x‖ ≤ K) ∧
      ∀ x v : ℝ × ℝ, fderiv ℝ (UnforcedLeray.B0224.planeHeat θ u) x v =
        UnforcedLeray.B0224.planeHeat θ (fun y => fderiv ℝ u y v) x

/-- **(S3)** Continuity in the slice parameter `σ` of the planar heat with time `T σ` of a jointly
continuous bounded family `G(σ,·)`: by `HeatIntRegular.planeHeat_eq_dilate`,
`planeHeat (T σ) (G σ ·) x = ∫ G₁(y) G(σ, x - ι(√(max (T σ) 0) y)) dy`, continuous by
`MeasureTheory.continuous_of_dominated` with bound `G₁ · K` (as `planeHeat_jointContinuous`). -/
def HGIPlaneHeatContSigma : Prop :=
  ∀ (G : ℝ × (ℝ × ℝ) → MeridC) (K : ℝ), Continuous G → (∀ p, ‖G p‖ ≤ K) →
    ∀ T : ℝ → ℝ, Continuous T → ∀ x : ℝ × ℝ,
      Continuous (fun σ : ℝ => UnforcedLeray.B0224.planeHeat (T σ) (fun w => G (σ, w)) x)

/-- The derivative of a slice `w ↦ Ψ (σ,w)` is the derivative of `Ψ` in the direction `(0,v)`. -/
theorem slice_fderiv_apply (Ψ : Profile → MeridC) (hΨ : Differentiable ℝ Ψ) (σ : ℝ)
    (y v : ℝ × ℝ) :
    fderiv ℝ (fun w : ℝ × ℝ => Ψ (σ, w)) y v = fderiv ℝ Ψ (σ, y) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun w : ℝ × ℝ => (σ, w)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y :=
    hasFDerivAt_prodMk_right σ y
  have h2 := (hΨ (σ, y)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun w : ℝ × ℝ => Ψ (σ, w)) y
      = (fderiv ℝ Ψ (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := h2.fderiv
  rw [h3]
  simp

theorem slice_fderiv_norm_le (Ψ : Profile → MeridC) (hΨ : Differentiable ℝ Ψ) (σ : ℝ)
    (y : ℝ × ℝ) : ‖fderiv ℝ (fun w : ℝ × ℝ => Ψ (σ, w)) y‖ ≤ ‖fderiv ℝ Ψ (σ, y)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
  rw [slice_fderiv_apply Ψ hΨ σ y v]
  calc ‖fderiv ℝ Ψ (σ, y) ((0 : ℝ), v)‖ ≤ ‖fderiv ℝ Ψ (σ, y)‖ * ‖((0 : ℝ), v)‖ :=
        (fderiv ℝ Ψ (σ, y)).le_opNorm _
    _ ≤ ‖fderiv ℝ Ψ (σ, y)‖ * ‖v‖ := by
        gcongr
        simp [Prod.norm_def]

/-- **Differentiation of the heat integral in `z`** (the analytic core of `HeatGradIdentity`),
from the three facts `S1`-`S3`. -/
theorem heatIntDiffCore_of (S1 : HGIPsiBounds) (S2 : HGIPlaneHeatNorm)
    (S3 : HGIPlaneHeatContSigma) : HeatIntDiffCore := by
  intro c ν hc hν μ F hF s hs j z0
  obtain ⟨s₁, K, hs₁, hΨC, hΨz, hΨb⟩ := S1 c hc F hF
  set Ψ : Profile → MeridC := fun p => p.1⁻¹ • F p with hΨdef
  have hΨdiff : Differentiable ℝ Ψ := hΨC.differentiable (by norm_num)
  have hΨcont : Continuous Ψ := hΨC.continuous
  have hDΨcont : Continuous (fderiv ℝ Ψ) := hΨC.continuous_fderiv (by norm_num)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hΨb (0, 0, 0)).1
  let T : ℝ → ℝ := fun σ => ν * (s - σ)
  have hTc : Continuous T := continuous_const.mul (continuous_const.sub continuous_id)
  let w : ℝ → ℂ := fun σ => ((σ / s : ℝ) : ℂ) ^ μ
  let U : ℝ → ℝ × ℝ → MeridC := fun σ y => Ψ (σ, y)
  have hUC : ∀ σ, ContDiff ℝ 1 (U σ) := fun σ =>
    hΨC.comp ((contDiff_const).prodMk contDiff_id)
  -- bounds on the slice
  have hUb : ∀ σ y, ‖U σ y‖ ≤ K := fun σ y => (hΨb (σ, y)).1
  have hUd : ∀ σ y, ‖fderiv ℝ (U σ) y‖ ≤ K := fun σ y =>
    (slice_fderiv_norm_le Ψ hΨdiff σ y).trans (hΨb (σ, y)).2
  have hUz : ∀ σ, σ < s₁ → U σ = fun _ => 0 := fun σ hσ => funext fun y => hΨz (σ, y) hσ
  have hS2 : ∀ σ, Differentiable ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) ∧
      (∀ x, ‖UnforcedLeray.B0224.planeHeat (T σ) (U σ) x‖ ≤ K) ∧
      (∀ x, ‖fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) x‖ ≤ K) ∧
      ∀ x v : ℝ × ℝ, fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) x v =
        UnforcedLeray.B0224.planeHeat (T σ) (fun y => fderiv ℝ (U σ) y v) x :=
    fun σ => S2 (T σ) K (U σ) (hUC σ) (hUb σ) (hUd σ)
  have hS2z : ∀ σ, σ < s₁ → (∀ x, ‖UnforcedLeray.B0224.planeHeat (T σ) (U σ) x‖ ≤ 0) ∧
      ∀ x, ‖fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) x‖ ≤ 0 := by
    intro σ hσ
    have := S2 (T σ) 0 (U σ) (hUC σ) (fun y => by rw [hUz σ hσ]; simp)
      (fun y => by rw [hUz σ hσ]; simp)
    exact ⟨this.2.1, this.2.2.1⟩
  -- the heat integral in the slice form
  have hΦ : (fun z' : ℝ × ℝ => smoothHeatInt c ν μ F (s, z')) = fun z' =>
      ∫ σ in (0 : ℝ)..s, w σ • UnforcedLeray.B0224.planeHeat (T σ) (U σ) z' := by
    funext z'
    exact smoothHeatInt_eq_slice c ν μ F hF.2.1 s z'
  -- weight
  have hwmeas : Measurable w := by
    refine Measurable.pow_const ?_ μ
    exact Complex.measurable_ofReal.comp (measurable_id.div_const s)
  have hwcont : ContinuousOn w (Icc s₁ s) := by
    intro σ hσ
    have hσ0 : 0 < σ := lt_of_lt_of_le hs₁ hσ.1
    have hpos : 0 < σ / s := div_pos hσ0 hs
    refine ContinuousAt.continuousWithinAt ?_
    have hdiv : ContinuousAt (fun x : ℝ => x / s) σ := (continuous_id.div_const s).continuousAt
    exact ContinuousAt.comp (f := fun x : ℝ => x / s)
      (Complex.continuousAt_ofReal_cpow_const (σ / s) μ (Or.inr hpos.ne')) hdiv
  obtain ⟨Cw, hCw⟩ := (isCompact_Icc (a := s₁) (b := s)).exists_bound_of_continuousOn hwcont
  let Cw' : ℝ := max Cw 0
  -- continuity of the pieces in σ
  have hcontA : ∀ z' : ℝ × ℝ, Continuous (fun σ : ℝ =>
      UnforcedLeray.B0224.planeHeat (T σ) (U σ) z') := fun z' =>
    S3 Ψ K hΨcont (fun p => (hΨb p).1) T hTc z'
  have hcontB : ∀ v : ℝ × ℝ, Continuous (fun σ : ℝ =>
      UnforcedLeray.B0224.planeHeat (T σ) (fun y => fderiv ℝ (U σ) y v) z0) := by
    intro v
    have hG : Continuous (fun p : Profile => fderiv ℝ Ψ p ((0 : ℝ), v)) :=
      hDΨcont.clm_apply continuous_const
    have hGb : ∀ p : Profile, ‖fderiv ℝ Ψ p ((0 : ℝ), v)‖ ≤ K * ‖v‖ := by
      intro p
      calc ‖fderiv ℝ Ψ p ((0 : ℝ), v)‖ ≤ ‖fderiv ℝ Ψ p‖ * ‖((0 : ℝ), v)‖ :=
            (fderiv ℝ Ψ p).le_opNorm _
        _ ≤ K * ‖v‖ := by
            gcongr
            · exact (hΨb p).2
            · simp [Prod.norm_def]
    have := S3 (fun p => fderiv ℝ Ψ p ((0 : ℝ), v)) (K * ‖v‖) hG hGb T hTc z0
    refine this.congr (fun σ => ?_)
    congr 1
    funext y
    exact (slice_fderiv_apply Ψ hΨdiff σ y v).symm
  -- the derivative as a continuous CLM-valued function of σ
  let A : ℝ → (ℝ × ℝ →L[ℝ] MeridC) := fun σ =>
    fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) z0
  have hAcont : Continuous A := by
    refine continuous_clm_apply.mpr (fun v => ?_)
    refine (hcontB v).congr (fun σ => ?_)
    exact ((hS2 σ).2.2.2 z0 v).symm
  -- integrability / measurability / bound of the derivative
  let F' : ℝ × ℝ → ℝ → (ℝ × ℝ →L[ℝ] MeridC) := fun z' σ =>
    w σ • fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) z'
  have hF'meas : AEStronglyMeasurable (F' z0) (volume.restrict (Ι (0 : ℝ) s)) :=
    hwmeas.aestronglyMeasurable.smul hAcont.aestronglyMeasurable
  have hσs : ∀ σ ∈ Ι (0 : ℝ) s, 0 < σ ∧ σ ≤ s := by
    intro σ hσ
    have h1 := hσ.1
    have h2 := hσ.2
    rw [min_eq_left hs.le] at h1
    rw [max_eq_right hs.le] at h2
    exact ⟨h1, h2⟩
  have hbound : ∀ σ ∈ Ι (0 : ℝ) s, ∀ z' : ℝ × ℝ, ‖F' z' σ‖ ≤ Cw' * K := by
    intro σ hσ z'
    obtain ⟨hσ0, hσs'⟩ := hσs σ hσ
    show ‖w σ • fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) z'‖ ≤ _
    rw [norm_smul]
    by_cases h1 : σ < s₁
    · have h0 : fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) z' = 0 :=
        norm_le_zero_iff.mp ((hS2z σ h1).2 z')
      rw [h0]
      simpa using mul_nonneg (le_max_right Cw 0) hK0
    · have hw1 : ‖w σ‖ ≤ Cw' := (hCw σ ⟨not_lt.mp h1, hσs'⟩).trans (le_max_left _ _)
      exact mul_le_mul hw1 ((hS2 σ).2.2.1 z') (norm_nonneg _) (le_max_right _ _)
  have hF'int : IntervalIntegrable (F' z0) volume 0 s := by
    refine (intervalIntegrable_const (c := Cw' * K)).mono_fun' hF'meas ?_
    exact (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun σ hσ => hbound σ hσ z0)
  have hFmeas : ∀ z' : ℝ × ℝ, AEStronglyMeasurable
      (fun σ : ℝ => w σ • UnforcedLeray.B0224.planeHeat (T σ) (U σ) z')
      (volume.restrict (Ι (0 : ℝ) s)) := fun z' =>
    hwmeas.aestronglyMeasurable.smul (hcontA z').aestronglyMeasurable
  have hFint : IntervalIntegrable
      (fun σ : ℝ => w σ • UnforcedLeray.B0224.planeHeat (T σ) (U σ) z0) volume 0 s := by
    refine (intervalIntegrable_const (c := Cw' * K)).mono_fun' (hFmeas z0) ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun σ hσ => ?_)
    obtain ⟨hσ0, hσs'⟩ := hσs σ hσ
    show ‖w σ • UnforcedLeray.B0224.planeHeat (T σ) (U σ) z0‖ ≤ Cw' * K
    rw [norm_smul]
    by_cases h1 : σ < s₁
    · have := (hS2z σ h1).1 z0
      have h0 : UnforcedLeray.B0224.planeHeat (T σ) (U σ) z0 = 0 := norm_le_zero_iff.mp this
      rw [h0]
      simpa using mul_nonneg (le_max_right Cw 0) hK0
    · have hw1 : ‖w σ‖ ≤ Cw' := (hCw σ ⟨not_lt.mp h1, hσs'⟩).trans (le_max_left _ _)
      exact mul_le_mul hw1 ((hS2 σ).2.1 z0) (norm_nonneg _) (le_max_right _ _)
  have hderiv : HasFDerivAt (fun z' : ℝ × ℝ => ∫ σ in (0 : ℝ)..s,
      w σ • UnforcedLeray.B0224.planeHeat (T σ) (U σ) z') (∫ σ in (0 : ℝ)..s, F' z0 σ) z0 :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (a := 0) (b := s)
      (μ := volume) (F := fun z' σ => w σ • UnforcedLeray.B0224.planeHeat (T σ) (U σ) z')
      (F' := F') (x₀ := z0) (s := Set.univ) (bound := fun _ => Cw' * K)
      Filter.univ_mem (Filter.Eventually.of_forall hFmeas) hFint hF'meas
      (ae_of_all _ fun σ hσ z' _ => hbound σ hσ z') intervalIntegrable_const
      (ae_of_all _ fun σ _ z' _ => ((hS2 σ).1 z').hasFDerivAt.const_smul (w σ))
  rw [hΦ]
  refine ⟨hderiv.differentiableAt, ?_⟩
  rw [hderiv.fderiv, ContinuousLinearMap.intervalIntegral_apply hF'int]
  refine intervalIntegral.integral_congr (fun σ _ => ?_)
  show w σ • (fderiv ℝ (UnforcedLeray.B0224.planeHeat (T σ) (U σ)) z0)
      (UnforcedLeray.B0579.dir j) = _
  have hslice : (fun w' : ℝ × ℝ => UnforcedLeray.B0220.periodize c
      (fun q : Profile => (q.1)⁻¹ • F q) (σ, w')) = U σ :=
    funext fun w' => periodize_slice c F hF.2.1 σ w'
  have hfun : (fun w'' : ℝ × ℝ => fderiv ℝ (fun w' : ℝ × ℝ => UnforcedLeray.B0220.periodize c
      (fun q : Profile => (q.1)⁻¹ • F q) (σ, w')) w'' (UnforcedLeray.B0579.dir j))
      = fun y => fderiv ℝ (U σ) y (UnforcedLeray.B0579.dir j) := by
    funext y
    rw [hslice]
  rw [hfun, (hS2 σ).2.2.2 z0]

/-- **`HeatGradIdentity`** from the cell-derivative smoothness `DerivForceSmooth` and the three
analytic facts `S1`-`S3`. -/
theorem heatGradIdentity_of_subs (hD1 : DerivForceSmooth) (S1 : HGIPsiBounds)
    (S2 : HGIPlaneHeatNorm) (S3 : HGIPlaneHeatContSigma) : HeatGradIdentity :=
  heatGradIdentity_of hD1 (heatIntDiffCore_of S1 S2 S3)

end UnforcedLeray.Short.PartIIa.N01
