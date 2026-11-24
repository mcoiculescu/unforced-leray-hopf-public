import UnforcedLeray.Short.PartIIa.Sub.R02_6
import UnforcedLeray.Lib.Kernels.ParamIntegral

/-!
# Part II-a, task `PartII-a:R02/MeanStress/HmeanEtaDeriv`: the cell average commutes with `∂_η`

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).
The statement `HmeanEtaDeriv` is defined in `Short/PartII-a/Sub/R02_6.lean`.

Route. Fix `c > 0` and `h` globally `C^∞` on the plane. Put `μ = volume.restrict (Ioc (-c/2) (c/2))`,
parameter `η : ℝ`, and `F q η = h (q, η)` with `U = univ`.
* Each slice `η ↦ h (q, η)` is `C^∞` (composition with `η ↦ (q, η)`).
* The `n`-th derivative of the slice at `η` is the `n`-th derivative of `h` at `(q, η)` composed with
  the linear map `η ↦ (0, η)`; hence `q ↦ ∂^n F_q(η)` is continuous, so measurable.
* On the compact box `Icc (-c/2) (c/2) ×ˢ closedBall η₀ 1` the continuous `∂^n h` is bounded, which
  gives a constant dominating bound, integrable for the finite measure `μ`.
Then `Kernels.iteratedFDeriv_integral_eq` gives `∂^a (∫ F_q dμ)(η) = ∫ ∂^a F_q(η) dμ`. Evaluating
on the all-ones vector commutes with the integral (`ContinuousMultilinearMap.integral_apply`), and
`iteratedDeriv_eq_iteratedFDeriv` identifies `∂^a F_q(η)(1, …, 1)` with `iteratedDeriv a (h (q, ·)) η`.
Finally the constant `c⁻¹` is pulled out (`iteratedDeriv_const_smul`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff

open UnforcedLeray.Short.PartI (hmean)

namespace UnforcedLeray.Short.PartIIa

/-- Slice formula: the `n`-th derivative of `η' ↦ H(q, η')` at `η` is the `n`-th derivative of `H`
at `(q, η)` composed with the linear map `η' ↦ (0, η')`. -/
private theorem hmeanEtaDeriv_slice_iteratedFDeriv {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (q : ℝ) (n : ℕ) (y : ℝ) :
    iteratedFDeriv ℝ n (fun y' : ℝ => H (q, y')) y =
      (iteratedFDeriv ℝ n H (q, y)).compContinuousLinearMap
        (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ) := by
  have hτ : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z + (q, (0 : ℝ))) :=
    contDiff_id.add contDiff_const
  have hsmooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => H (z + (q, (0 : ℝ)))) :=
    hH.comp hτ
  have hfun : (fun y' : ℝ => H (q, y')) =
      (fun z : ℝ × ℝ => H (z + (q, (0 : ℝ)))) ∘ (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    funext y'
    simp
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    (ContinuousLinearMap.inr ℝ ℝ ℝ) hsmooth y (mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hy : ContinuousLinearMap.inr ℝ ℝ ℝ y + (q, (0 : ℝ)) = (q, y) := by
    simp
  rw [hy]

/-- Continuity in `q` of the `n`-th derivative of the slice `η' ↦ H(q, η')` at a fixed `η`. -/
private theorem hmeanEtaDeriv_slice_continuous {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (n : ℕ) (y : ℝ) :
    Continuous (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ => H (q, y')) y) := by
  have hcont : Continuous (fun q : ℝ => iteratedFDeriv ℝ n H (q, y)) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ)).continuous
  refine (hT.comp hcont).congr fun q => ?_
  exact (hmeanEtaDeriv_slice_iteratedFDeriv hH q n y).symm

/-- Measurability in `q` of the `n`-th derivative of the slice, for every measure on `ℝ`. -/
private theorem hmeanEtaDeriv_hmeas {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (μ : Measure ℝ) :
    ∀ (n : ℕ) (y : ℝ),
      AEStronglyMeasurable (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ => H (q, y')) y) μ :=
  fun n y => (hmeanEtaDeriv_slice_continuous hH n y).aestronglyMeasurable

/-- Local domination of all iterated slice derivatives, uniformly in `q ∈ Ioc (-c/2) (c/2)`. -/
private theorem hmeanEtaDeriv_locDominated {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (c : ℝ) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (-c / 2) (c / 2)))
      (fun (q : ℝ) (y : ℝ) => H (q, y)) univ := by
  intro n x _
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n H)
      (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ ℝ‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ ℝ‖,
    integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-c / 2) (c / 2)))]
    with q hq y hy
  have hbound : ‖iteratedFDeriv ℝ n H (q, y)‖ ≤ C :=
    hC (q, y) ⟨Ioc_subset_Icc_self hq, hy⟩
  show ‖iteratedFDeriv ℝ n (fun y' : ℝ => H (q, y')) y‖ ≤
    C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ ℝ‖
  rw [hmeanEtaDeriv_slice_iteratedFDeriv hH q n y]
  calc ‖(iteratedFDeriv ℝ n H (q, y)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ ℝ)‖
      ≤ ‖iteratedFDeriv ℝ n H (q, y)‖ *
          ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ ℝ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ ℝ‖ :=
        mul_le_mul_of_nonneg_right hbound hM0

/-- **The `η`-derivative commutes with the cell average** (differentiation under the integral over
the compact interval `(-c/2, c/2]`, `Kernels.iteratedFDeriv_integral_eq` in
`Lib/Kernels/ParamIntegral.lean` with `μ = volume.restrict (Ioc (-c/2) (c/2))`, `U = univ`,
`F q η = h (q, η)`): for `h` globally `C^∞` on the plane,
`∂_η^a \bar h(η) = \overline{∂_η^a h}(η)`. Source lines 397-404. -/
theorem hmeanEtaDeriv : UnforcedLeray.Short.PartIIa.HmeanEtaDeriv := by
  intro c _hc h hh a η
  have hsmooth : ∀ᵐ q ∂(volume.restrict (Ioc (-c / 2) (c / 2))),
      ContDiff ℝ ∞ (fun y : ℝ => h (q, y)) := by
    refine ae_of_all _ fun q => ?_
    have hq : ContDiff ℝ ∞ (fun y : ℝ => ((q, y) : ℝ × ℝ)) := contDiff_const.prodMk contDiff_id
    exact hh.comp hq
  have hmeas := hmeanEtaDeriv_hmeas hh (volume.restrict (Ioc (-c / 2) (c / 2)))
  have hdom := hmeanEtaDeriv_locDominated hh c
  have hG : ContDiff ℝ ∞
      (fun y : ℝ => ∫ q, h (q, y) ∂(volume.restrict (Ioc (-c / 2) (c / 2)))) :=
    contDiffOn_univ.mp (UnforcedLeray.Kernels.contDiffOn_integral
      (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
      (F := fun (q : ℝ) (y : ℝ) => h (q, y)) (U := univ) isOpen_univ hsmooth hmeas hdom)
  have hkey : iteratedFDeriv ℝ a
      (fun y : ℝ => ∫ q, h (q, y) ∂(volume.restrict (Ioc (-c / 2) (c / 2)))) η =
      ∫ q, iteratedFDeriv ℝ a (fun y : ℝ => h (q, y)) η
        ∂(volume.restrict (Ioc (-c / 2) (c / 2))) :=
    UnforcedLeray.Kernels.iteratedFDeriv_integral_eq
      (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
      (F := fun (q : ℝ) (y : ℝ) => h (q, y)) (U := univ) isOpen_univ hsmooth hmeas hdom
      a (mem_univ η)
  have hint : Integrable (fun q : ℝ => iteratedFDeriv ℝ a (fun y : ℝ => h (q, y)) η)
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    hdom.integrable hmeas a (mem_univ η)
  have hcoord : iteratedDeriv a
      (fun y : ℝ => ∫ q, h (q, y) ∂(volume.restrict (Ioc (-c / 2) (c / 2)))) η =
      ∫ q, iteratedDeriv a (fun y : ℝ => h (q, y)) η
        ∂(volume.restrict (Ioc (-c / 2) (c / 2))) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hkey, ContinuousMultilinearMap.integral_apply hint]
    rfl
  have hGa : ContDiffAt ℝ a
      (fun y : ℝ => ∫ q, h (q, y) ∂(volume.restrict (Ioc (-c / 2) (c / 2)))) η :=
    (hG.of_le (mod_cast le_top)).contDiffAt
  have step1 : iteratedDeriv a (fun e : ℝ => hmean c h e) η =
      c⁻¹ • iteratedDeriv a
        (fun y : ℝ => ∫ q, h (q, y) ∂(volume.restrict (Ioc (-c / 2) (c / 2)))) η := by
    have h1 := iteratedDeriv_const_smul (f := fun y : ℝ =>
      ∫ q, h (q, y) ∂(volume.restrict (Ioc (-c / 2) (c / 2)))) hGa c⁻¹
    exact h1
  rw [step1, hcoord]
  rfl

end UnforcedLeray.Short.PartIIa
