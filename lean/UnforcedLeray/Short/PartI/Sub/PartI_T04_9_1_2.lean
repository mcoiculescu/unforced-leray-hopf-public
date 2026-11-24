import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont

/-!
# Part I, `PartI:T04/9/1/2`: `APLevel2CutIneq`, reduced to regularity and a pointwise-in-time
differential inequality

Source of record: `the November 2 reference manuscript`,
lines 285-288.

* `APL2Reg`: `G¹_R` is continuous on `[0,T]`, differentiable on `(0,T)`, with integrable derivative;
* `APL2Diff`: the integrated differential inequality
  `∫_0^s (∂_r G¹_R + 2ν G²_R - 2 Tri_R) ≤ C R^{-1/2}`; this is the PDE core (differentiated vorticity
  equation, cell integration by parts, pointwise bounds
  `Σ(∂_i∂_jω)² ≥ ‖D²ω‖²`, `|Σ ∂_iω ∂_iv_j ∂_jω| ≤ 2‖Dω‖²‖Dv‖`, strip error `O(R^{-1/2})`).

`apLevel2CutIneq_of` is the fundamental theorem of calculus assembly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- **Leaf (regularity of the cutoff enstrophy `G¹_R`)** (lines 285-288): for `R ≥ 1`, `G¹_R` is
continuous on `[0,T]`, differentiable on `(0,T)`, and its derivative is integrable on `[0,T]`.
Route: `G¹_R(s) = ∫_cell χ_R |Dω(s)|²`; the continuity is as in `APLevel2CutCont`
(`Tasks/TrainGlobalExistence/APLevel2/CutCont.lean`); differentiability by differentiating under
the integral (compact support of `χ_R` in `η`, `C^∞` of `v`); the derivative is continuous on
`(0,T)` and bounded by the jets (`jet_l2`, `HasBoundedDerivsOn`), hence integrable. -/
def APL2Reg : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (apCutG c 1 v R) (Icc (0 : ℝ) T) ∧
      DifferentiableOn ℝ (apCutG c 1 v R) (Ioo (0 : ℝ) T) ∧
      IntervalIntegrable (deriv (apCutG c 1 v R)) volume 0 T

/-- **Leaf (integrated differential inequality, PDE core)** (lines 285-288): there is `C ≥ 0` with,
for all `R ≥ 1` and `s ∈ [0,T]`,
`∫_0^s (∂_r G¹_R + 2ν G²_R - 2 Tri_R) dr ≤ C R^{-1/2}`.
Route: `∂_r G¹_R = -2ν Σ_{ij} ∫χ_R (∂_i∂_jω)² - 2 ∫χ_R ∂_iω ∂_iv_j ∂_jω + E_R` on `(0,T)`
(`localVorticityEquation`, `Sub/T02_4.lean:71`, differentiated once; transport term
`-½∫∂_ηχ_R v_η |Dω|²`, viscous cross terms with `∂_ηχ_R`), then `apCutG c 2` is exactly `Σ_{ij}∫χ_R(∂_i∂_jω)²` (Euclidean `eucJet2`),
`|Σ ∂_iω ∂_iv_j ∂_jω| ≤ 2|Dω|²‖Dv‖` (so `-2X ≤ ½ Tri ≤ 2 Tri`), and
`|∫_0^s E_R| ≤ C R^{-1/2}` (strip `R ≤ |η| ≤ 2R`, `|χ_R'| ≤ C₀ R^{-1} √χ_R`, measure `≤ 2cR`,
`jet_l2`, `HasBoundedDerivsOn`; template `APEnstrophy/RhsEstimate.lean`, `apRE_key`). -/
def APL2Diff : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      ∫ r in (0 : ℝ)..s, (deriv (apCutG c 1 v R) r + 2 * ν * apCutG c 2 v R r
        - 2 * apCutTri c v R r) ≤ C / Real.sqrt R

theorem apLevel2CutIneq_of (hA : APL2Reg) (hB : APL2Diff) : APLevel2CutIneq := by
  intro ν c T v p hν hc hcls
  obtain ⟨C, hC0, hC⟩ := hB ν c T v p hν hc hcls
  refine ⟨C, hC0, fun R hR s hs => ?_⟩
  obtain ⟨hcont, hdiff, hint⟩ := hA ν c T v p hν hc hcls R hR
  obtain ⟨hcG2, hcTri⟩ := apLevel2CutCont ν c T v p hν hc hcls R hR
  have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hs.2
  have huIcc : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := by
    rw [uIcc_of_le hs.1]; exact hsub
  have hT0 : (0 : ℝ) ≤ T := hs.1.trans hs.2
  have huT : uIcc (0 : ℝ) s ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT0]; exact huIcc
  have hd : IntervalIntegrable (deriv (apCutG c 1 v R)) volume 0 s := hint.mono_set huT
  have hi2 : IntervalIntegrable (fun r => apCutG c 2 v R r) volume 0 s :=
    (hcG2.mono huIcc).intervalIntegrable
  have hiT : IntervalIntegrable (fun r => apCutTri c v R r) volume 0 s :=
    (hcTri.mono huIcc).intervalIntegrable
  have hftc : ∫ r in (0 : ℝ)..s, deriv (apCutG c 1 v R) r
      = apCutG c 1 v R s - apCutG c 1 v R 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 (hcont.mono hsub)
      (fun x hx => ?_) hd
    have hxT : x ∈ Ioo (0 : ℝ) T := ⟨hx.1, hx.2.trans_le hs.2⟩
    exact ((hdiff x hxT).differentiableAt (Ioo_mem_nhds hxT.1 hxT.2)).hasDerivAt
  have hsplit : ∫ r in (0 : ℝ)..s, (deriv (apCutG c 1 v R) r + 2 * ν * apCutG c 2 v R r
        - 2 * apCutTri c v R r)
      = (apCutG c 1 v R s - apCutG c 1 v R 0)
        + 2 * ν * (∫ r in (0 : ℝ)..s, apCutG c 2 v R r)
        - 2 * (∫ r in (0 : ℝ)..s, apCutTri c v R r) := by
    rw [intervalIntegral.integral_sub (hd.add (hi2.const_mul (2 * ν))) (hiT.const_mul 2),
      intervalIntegral.integral_add hd (hi2.const_mul (2 * ν)), hftc,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have := hC R hR s hs
  rw [hsplit] at this
  linarith

end UnforcedLeray.Short.PartI
