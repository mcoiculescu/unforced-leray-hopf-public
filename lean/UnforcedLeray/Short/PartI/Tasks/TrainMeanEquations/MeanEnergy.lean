import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1
import Mathlib.Analysis.Convex.Integral

/-!
# Part I, task `PartI:T01`: finite energy gives the mean-stress and mean-velocity integrability

Source of record: `the November 2 reference manuscript`, lines 397-404 (eq.
`sct:mean`, "the last equality follows from divergence and finite energy").

Route, for `s > 0`, `v = tr.v s`, `N z = ‖v z‖²`, and the cell slice `[-c/2, c/2) × {η}`:

* pointwise: `|v₁ v₂| ≤ N` and `v₁² ≤ N` (`v₁ = v z 0`, `v₂ = v z 1`);
* for each `η`: `|\overline{v₁v₂}(η)| ≤ c⁻¹ ∫_{[-c/2,c/2)} N(q,η) dq` and
  `\bar v₁(η)² ≤ c⁻¹ ∫_{[-c/2,c/2)} N(q,η) dq` (Cauchy-Schwarz on an interval of length `c`);
* `η ↦ c⁻¹ ∫_{[-c/2,c/2)} N(q,η) dq` is integrable on `ℝ` (Fubini on the cell, from
  `IsTrain.finite_energy`);
* `g = \overline{v₁v₂}` and `\bar v₁` are continuous in `η` (parametric integral over a compact
  `q`-interval), so the dominated bounds give `g ∈ L¹(ℝ)`; and `S_η = -\bar v₁` (`TrainMeanV1`)
  gives `S_η ∈ L²(ℝ)` through `memLp_two_iff_integrable_sq`.

The unconditional statement is `trainMeanEnergy : TrainMeanEnergy`; no hypotheses are added.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Pointwise bounds on a velocity vector -/

theorem meanEnergy_coord_sq_add (x : Vec) : x 0 ^ 2 + x 1 ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem meanEnergy_sq_coord_le (x : Vec) : x 0 ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← meanEnergy_coord_sq_add]
  linarith [sq_nonneg (x 1)]

theorem meanEnergy_norm_mul_coord_le (x : Vec) : ‖x 0 * x 1‖ ≤ ‖x‖ ^ 2 := by
  rw [Real.norm_eq_abs, ← meanEnergy_coord_sq_add, abs_le]
  constructor <;> nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]

/-! ### Cauchy-Schwarz on an interval -/

/-- Cauchy-Schwarz on `[a, b)`: `(∫ f)² ≤ (b - a) ∫ f²` for continuous `f`. -/
theorem meanEnergy_cs_Ico {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ q in Ico a b, f q) ^ 2 ≤ (b - a) * ∫ q in Ico a b, f q ^ 2 := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hne : b - a ≠ 0 := hL.ne'
  have : NeZero (volume.restrict (Ico a b)) := ⟨by
    intro h
    rw [Measure.restrict_eq_zero, Real.volume_Ico] at h
    exact (ENNReal.ofReal_pos.2 hL).ne' h⟩
  have hμ : (volume.restrict (Ico a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ico,
      ENNReal.toReal_ofReal hL.le]
  have hi : ∀ g : ℝ → ℝ, Continuous g → Integrable g (volume.restrict (Ico a b)) :=
    fun g hg => (hg.integrableOn_Icc).mono_set Ico_subset_Icc_self
  have hconv : ConvexOn ℝ univ (fun x : ℝ => x ^ 2) := Even.convexOn_pow even_two
  have hJ := hconv.map_average_le (μ := volume.restrict (Ico a b)) (f := f)
    (continuous_pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) (hi f hf) (hi _ ((continuous_pow 2).comp hf))
  simp only [average_eq, hμ, smul_eq_mul] at hJ
  have h2 := mul_le_mul_of_nonneg_left hJ (sq_nonneg (b - a))
  have e1 : (b - a) ^ 2 * ((b - a)⁻¹ * ∫ q in Ico a b, f q) ^ 2 = (∫ q in Ico a b, f q) ^ 2 := by
    field_simp
  have e2 : (b - a) ^ 2 * ((b - a)⁻¹ * ∫ q in Ico a b, f q ^ 2)
      = (b - a) * ∫ q in Ico a b, f q ^ 2 := by
    field_simp
  linarith [h2, e1, e2]

/-! ### The horizontal average -/

/-- The horizontal average over the half-open cell `[-c/2, c/2)`. -/
theorem meanEnergy_hmean_Ico {c : ℝ} (F : Plane → ℝ) (η : ℝ) :
    hmean c F η = c⁻¹ • ∫ q in Ico (-c / 2) (c / 2), F (q, η) := by
  unfold hmean
  rw [← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ico]

/-- Continuity in `η` of the horizontal average of a continuous function. -/
theorem meanEnergy_hmean_continuous {c : ℝ} {F : Plane → ℝ} (hF : Continuous F) :
    Continuous (fun η : ℝ => hmean c F η) := by
  have hF' : Continuous (fun p : ℝ × ℝ => F (p.2, p.1)) :=
    hF.comp (continuous_snd.prodMk continuous_fst)
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun η q : ℝ => F (q, η)) hF' (isCompact_Icc : IsCompact (Icc (-c / 2) (c / 2)))
  have heq : (fun η : ℝ => hmean c F η)
      = fun η : ℝ => c⁻¹ • ∫ y in Icc (-c / 2) (c / 2), F (y, η) := by
    funext η
    unfold hmean
    rw [integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact h.const_smul c⁻¹

/-- Pointwise `L²` bound for the horizontal average: `(\bar f)² ≤ c⁻¹ ∫ G` when `f² ≤ G`. -/
theorem meanEnergy_hmean_sq_le {c : ℝ} (hc : 0 < c) {F G : Plane → ℝ} (hF : Continuous F)
    (hG : Continuous G) (hFG : ∀ z, F z ^ 2 ≤ G z) (η : ℝ) :
    hmean c F η ^ 2 ≤ c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η) := by
  have hline : Continuous (fun q : ℝ => ((q, η) : Plane)) :=
    continuous_id.prodMk continuous_const
  have hF' : Continuous (fun q : ℝ => F (q, η)) := hF.comp hline
  have hG' : Continuous (fun q : ℝ => G (q, η)) := hG.comp hline
  have hcs := meanEnergy_cs_Ico (a := -c / 2) (b := c / 2) (by linarith) hF'
  have hlen : c / 2 - -c / 2 = c := by ring
  rw [hlen] at hcs
  have hsq : ∫ q in Ico (-c / 2) (c / 2), F (q, η) ^ 2
      ≤ ∫ q in Ico (-c / 2) (c / 2), G (q, η) :=
    integral_mono ((hF'.pow 2).integrableOn_Icc.mono_set Ico_subset_Icc_self)
      (hG'.integrableOn_Icc.mono_set Ico_subset_Icc_self) (fun q => hFG _)
  have hc0 : c ≠ 0 := hc.ne'
  rw [meanEnergy_hmean_Ico, smul_eq_mul]
  calc (c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), F (q, η)) ^ 2
      = c⁻¹ ^ 2 * (∫ q in Ico (-c / 2) (c / 2), F (q, η)) ^ 2 := by ring
    _ ≤ c⁻¹ ^ 2 * (c * ∫ q in Ico (-c / 2) (c / 2), G (q, η)) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hsq hc.le)) (sq_nonneg _)
    _ = c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η) := by field_simp

/-- Pointwise bound for the absolute value of the horizontal average: `|\bar f| ≤ c⁻¹ ∫ G`
when `‖f‖ ≤ G`. -/
theorem meanEnergy_norm_hmean_le {c : ℝ} (hc : 0 < c) {F G : Plane → ℝ} (hG : Continuous G)
    (hFG : ∀ z, ‖F z‖ ≤ G z) (η : ℝ) :
    ‖hmean c F η‖ ≤ c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), G (q, η) := by
  have hline : Continuous (fun q : ℝ => ((q, η) : Plane)) :=
    continuous_id.prodMk continuous_const
  have hG' : Continuous (fun q : ℝ => G (q, η)) := hG.comp hline
  rw [meanEnergy_hmean_Ico, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_le_of_norm_le ((hG'.integrableOn_Icc).mono_set Ico_subset_Icc_self)
      (Eventually.of_forall fun q => hFG _)) (inv_nonneg.2 hc.le)

/-! ### Integrability on the cell -/

/-- A function integrable on the cell `[a, b) × ℝ` is integrable for the product measure
`(volume.restrict [a, b)).prod volume`. -/
theorem meanEnergy_integrable_prod {a b : ℝ} {G : Plane → ℝ}
    (hG : IntegrableOn G (Ico a b ×ˢ univ)) :
    Integrable G ((volume.restrict (Ico a b)).prod volume) := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (Ico a b) (univ : Set ℝ)
  rw [Measure.restrict_univ, ← Measure.volume_eq_prod] at h
  rw [h]
  exact hG

/-! ### The main statement -/

/-- **`PartI:T01`, `TrainMeanEnergy`** (source lines 397-404): for `s > 0` the mean stress
`g = \overline{v₁v₂}` is integrable on `ℝ` and `S_η = -\bar v₁` is in `L²(ℝ)`, from the finite
energy of the train. -/
theorem trainMeanEnergy : TrainMeanEnergy := by
  intro ν c hν hc tr s hs
  -- continuity of the velocity on the slice `s > 0`
  have hvc : Continuous (fun z : Plane => tr.v s z) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hmap : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    exact hcont.comp_continuous hmap (fun z => ⟨hs.le, mem_univ z⟩)
  have hv0 : Continuous (fun z : Plane => tr.v s z 0) :=
    (PiLp.continuous_apply _ _ 0).comp hvc
  have hv1 : Continuous (fun z : Plane => tr.v s z 1) :=
    (PiLp.continuous_apply _ _ 1).comp hvc
  have hN : Continuous (fun z : Plane => ‖tr.v s z‖ ^ 2) := hvc.norm.pow 2
  -- finite energy on the cell gives integrability of `N` on the product, hence the bound `G`
  have hprod : Integrable (fun z : Plane => ‖tr.v s z‖ ^ 2)
      ((volume.restrict (Ico (-c / 2) (c / 2))).prod volume) :=
    meanEnergy_integrable_prod (a := -c / 2) (b := c / 2) (tr.isTrain.finite_energy s hs.le)
  have hGη : Integrable (fun η : ℝ => c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖tr.v s (q, η)‖ ^ 2) :=
    hprod.integral_prod_right.const_mul c⁻¹
  -- pointwise bounds in `η`
  have hbound : ∀ η : ℝ, ‖meanStress tr s η‖
      ≤ c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖tr.v s (q, η)‖ ^ 2 :=
    fun η => meanEnergy_norm_hmean_le hc hN (fun z => meanEnergy_norm_mul_coord_le (tr.v s z)) η
  have hsq : ∀ η : ℝ, hmean c (fun z : Plane => tr.v s z 0) η ^ 2
      ≤ c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖tr.v s (q, η)‖ ^ 2 :=
    fun η => meanEnergy_hmean_sq_le hc hv0 hN (fun z => meanEnergy_sq_coord_le (tr.v s z)) η
  -- continuity in `η`
  have hmeasS : Continuous (meanStress tr s) :=
    meanEnergy_hmean_continuous (c := c) (hv0.mul hv1)
  have hH : Continuous (fun η : ℝ => hmean c (fun z : Plane => tr.v s z 0) η) :=
    meanEnergy_hmean_continuous (c := c) hv0
  -- `S_η = -\bar v₁` (TrainMeanV1)
  have hderiv : deriv (fun e => meanStream tr s e)
      = fun η : ℝ => -hmean c (fun z : Plane => tr.v s z 0) η := by
    funext η
    have h := trainMeanV1 ν c hν hc tr s hs η
    linarith
  refine ⟨Integrable.mono' hGη hmeasS.aestronglyMeasurable (Eventually.of_forall hbound), ?_⟩
  rw [hderiv]
  refine (memLp_two_iff_integrable_sq hH.neg.aestronglyMeasurable).2 ?_
  refine Integrable.mono' hGη (hH.neg.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun η => ?_)
  show ‖(-hmean c (fun z : Plane => tr.v s z 0) η) ^ 2‖
      ≤ c⁻¹ * ∫ q in Ico (-c / 2) (c / 2), ‖tr.v s (q, η)‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _), neg_sq]
  exact hsq η

end UnforcedLeray.Short.PartI
