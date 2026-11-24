import UnforcedLeray.Loc.L09CompactDatum.Potential
import UnforcedLeray.Loc.L09CompactDatum.Defect
import UnforcedLeray.Consequences

/-!
# L9 helper: the cutoff and the elementary properties of `u_{0,h} = curl(χ A_loc)`

Helper of `Loc/L09CompactDatum.lean` (step L9, `paper/main.tex` lines 441–453, blueprint
units B0718, B0719).

* `cutoff`: the radial cutoff `χ(x) = S(2 - |x|²)`, `S` Mathlib's smooth transition; `χ = 1`
  on `|x| ≤ 1` and `χ = 0` on `|x| ≥ 3/2` (line 441: "a smooth compactly supported radial
  `χ = 1` near zero").
* `compactDatum_contDiffOn`: `u_{0,h}` is smooth off zero (line 451).
* `compactDatum_eq_near`: `u_{0,h} = curl A_loc = u_dss` on `0 < |x| < 1` (line 451).
* `compactDatum_cutoff_eq_zero`: `u_{0,h} = 0` on `|x| > 3/2`.
* `compactDatum_inverse_bound`: `|u_{0,h}(x)||x| ≤ C` off zero, hence `u_{0,h} ∈ L¹ ∩ L²`
  (line 451: "`u_{0,h} = O(|x|^{-1})` near `0` and is in `L²`").
* `compactDatum_l2Norm_pos`: `u_{0,h} ≠ 0` (line 452).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.L09

open UnforcedLeray.Blueprint

/-! ## The cutoff -/

/-- `χ(x) = S(2 - |x|²)`, `S = Real.smoothTransition`. -/
def cutoff (x : Space) : ℝ := Real.smoothTransition (2 - ‖x‖ ^ 2)

theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem cutoff_eq_one {x : Space} (hx : ‖x‖ ≤ 1) : cutoff x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith [norm_nonneg x]

theorem cutoff_eq_zero {x : Space} (hx : 3 / 2 ≤ ‖x‖) : cutoff x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]

/-- `χ` is a radial cutoff in the sense of line 441. -/
theorem isRadialCutoff_cutoff : IsRadialCutoff cutoff where
  smooth := cutoff_contDiff
  compact := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2) fun x hx => ?_
    apply cutoff_eq_zero
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    linarith
  one_near_zero := ⟨1, one_pos, fun x hx => cutoff_eq_one hx.le⟩
  radial := fun x y h => by simp only [cutoff, h]

/-! ## The curl -/

theorem curl_congr {G H : Space → Space} {x : Space} (h : G =ᶠ[𝓝 x] H) :
    curl G x = curl H x := by
  simp only [curl, h.fderiv_eq]

theorem curl_contDiffOn {G : Space → Space} {U : Set Space} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (curl G) U := by
  have hD : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x) U := hG.fderiv_of_isOpen hU (by simp)
  show ContDiffOn ℝ ∞ (fun x => ∑ j : Fin 3,
    crossProd (coordinateVector j) (fderiv ℝ G x (coordinateVector j))) U
  refine ContDiffOn.sum fun j _ => ?_
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x (coordinateVector j)) U :=
    hD.clm_apply contDiffOn_const
  refine ((crossCLM (coordinateVector j)).contDiff.comp_contDiffOn h1).congr fun x _ => ?_
  simp [crossCLM_apply]

/-! ## The datum -/

theorem compactDatum_cutoff_eq_zero (u : SpatialField) {x : Space} (hx : 3 / 2 < ‖x‖) :
    compactDatum cutoff u x = 0 := by
  have h : (fun y => cutoff y • homotopyPotential u y) =ᶠ[𝓝 x] fun _ => (0 : Space) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    have hy' : 3 / 2 < ‖y‖ := hy
    rw [cutoff_eq_zero hy'.le, zero_smul]
  rw [compactDatum, curl_congr h]
  simp [curl]

theorem compactDatum_hasCompactSupport (u : SpatialField) :
    HasCompactSupport (compactDatum cutoff u) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) 2) fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact compactDatum_cutoff_eq_zero u (by linarith)

/-- Local smoothness on an open set and one nonzero value give nonzero `L²` mass (copied from
-/
theorem l2Norm_pos_of_continuousOn_open_nonzero {f : SpatialField}
    (hf : MemLp f 2 volume) {U : Set Space} (hU : IsOpen U)
    (hcont : ContinuousOn f U) {x : Space} (hx : x ∈ U)
    (hfx : f x ≠ 0) : 0 < l2Norm f := by
  have hnonzero : ¬ f =ᵐ[volume] (0 : SpatialField) := by
    intro hae
    have hrestrict : f =ᵐ[volume.restrict U] (0 : SpatialField) :=
      ae_restrict_of_ae hae
    have heq := Measure.eqOn_open_of_ae_eq hrestrict hU hcont continuous_const.continuousOn
    exact hfx (heq hx)
  have hn : l2Norm f ≠ 0 := by
    intro hn
    exact hnonzero ((l2Norm_eq_zero_iff hf).mp hn)
  exact lt_of_le_of_ne (l2Norm_nonneg f) (Ne.symm hn)

variable {q : ℝ} {u : SpatialField}

namespace DSSField

/-- `A_loc` is smooth off zero. -/
theorem potential_contDiffOn (hu : DSSField q u) :
    ContDiffOn ℝ ∞ (homotopyPotential u) {0}ᶜ := by
  have h : ContDiffOn ℝ ∞ (fun x => crossCLM x (radialMean q u x)) {0}ᶜ :=
    crossCLM.contDiff.contDiffOn.clm_apply hu.radialMean_contDiffOn
  rw [hu.homotopyPotential_eq]
  refine (h.const_smul (-dssConst q)).congr fun x _ => ?_
  simp only [crossCLM_apply]

theorem compactDatum_contDiffOn (hu : DSSField q u) {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiffOn ℝ ∞ (compactDatum χ u) {0}ᶜ :=
  curl_contDiffOn isOpen_compl_singleton (hχ.contDiffOn.smul hu.potential_contDiffOn)

/-- `u_{0,h} = u_dss` on the punctured unit ball (line 451). -/
theorem compactDatum_eq_near (hu : DSSField q u) {x : Space} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    compactDatum cutoff u x = u x := by
  have h : (fun y => cutoff y • homotopyPotential u y) =ᶠ[𝓝 x] homotopyPotential u := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx1] with y hy
    have hy' : ‖y‖ < 1 := hy
    rw [cutoff_eq_one hy'.le, one_smul]
  rw [compactDatum, curl_congr h, hu.curl_homotopyPotential hx]

/-- `|u_{0,h}(x)||x| ≤ C` off zero. -/
theorem compactDatum_inverse_bound (hu : DSSField q u) :
    ∃ C : ℝ, ∀ x : Space, x ≠ 0 → ‖compactDatum cutoff u x‖ * ‖x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hu.bound
  set K : Set Space := {y | 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 2} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space) 2).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro y hy; simpa [Metric.mem_closedBall, dist_zero_right] using hy.2
  have hK0 : K ⊆ {0}ᶜ := by
    intro y hy h0
    rw [mem_singleton_iff] at h0
    have := hy.1
    rw [h0, norm_zero] at this
    linarith
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    ((hu.compactDatum_contDiffOn cutoff_contDiff).continuousOn.mono hK0)
  refine ⟨max (max C (M * 2)) 0, fun x hx => ?_⟩
  by_cases h1 : ‖x‖ < 1
  · rw [hu.compactDatum_eq_near hx h1]
    exact le_max_of_le_left (le_max_of_le_left (hC x hx))
  by_cases h2 : ‖x‖ ≤ 2
  · have hxK : x ∈ K := ⟨not_lt.mp h1, h2⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hxK)
    refine le_max_of_le_left (le_max_of_le_right ?_)
    exact mul_le_mul (hM x hxK) h2 (norm_nonneg _) hM0
  · rw [compactDatum_cutoff_eq_zero u (by linarith [not_le.mp h2]), norm_zero, zero_mul]
    exact le_max_right _ _

theorem compactDatum_memLp (hu : DSSField q u) : MemLp (compactDatum cutoff u) 2 volume := by
  obtain ⟨C, hC⟩ := hu.compactDatum_inverse_bound
  exact memLp_two_of_inverse_bound (hu.compactDatum_contDiffOn cutoff_contDiff).continuousOn hC
    (fun x hx => compactDatum_cutoff_eq_zero u hx)

theorem compactDatum_integrable (hu : DSSField q u) :
    Integrable (compactDatum cutoff u) volume := by
  obtain ⟨C, hC⟩ := hu.compactDatum_inverse_bound
  exact integrable_of_inverse_bound (hu.compactDatum_contDiffOn cutoff_contDiff).continuousOn hC
    (fun x hx => compactDatum_cutoff_eq_zero u hx)

/-- `u_{0,h} ≠ 0` (line 452: it equals `u_dss ≠ 0` near zero). -/
theorem compactDatum_l2Norm_pos (hu : DSSField q u) : 0 < l2Norm (compactDatum cutoff u) := by
  obtain ⟨y, hy0, hy1, huy⟩ := hu.exists_small_ne_zero one_pos
  refine l2Norm_pos_of_continuousOn_open_nonzero hu.compactDatum_memLp isOpen_compl_singleton
    (hu.compactDatum_contDiffOn cutoff_contDiff).continuousOn (x := y) hy0 ?_
  rw [hu.compactDatum_eq_near hy0 hy1]
  exact huy

end DSSField

end UnforcedLeray.L09
