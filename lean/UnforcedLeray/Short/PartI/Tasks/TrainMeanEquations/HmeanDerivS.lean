import UnforcedLeray.Short.PartI.Sub.T01
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Part I, task `PartI:T01/HmeanDerivS`: the age derivative commutes with the horizontal average

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).

Route. For `f : ℝ → Plane → ℝ` jointly `C^∞` on `(0, ∞) × Plane`, `hmean c (f r) η` is
`c⁻¹ ∫_{(-c/2, c/2]} f r (q, η) dq`. Differentiation under the integral in the age variable `r`
at `s > 0` (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) needs an integrable
bound on the `r`-derivative for `r` near `s`. That bound comes from continuity of `fderiv` on the
open set `(0, ∞) × Plane`, evaluated over the compact box `[s/2, 2s] × [-c/2, c/2]`. The age
derivative of a slice is the `fderiv` value in the direction `(1, 0)`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The age slice `r ↦ f r z` has derivative `∂_r F (r, z)` at each `r > 0`, where
`F x = f x.1 x.2`. -/
private theorem hmeanDerivS_slice {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) (z : Plane) :
    HasDerivAt (fun r' => f r' z)
      (fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (r, z) (1, 0)) r := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ((r, z) : ℝ × Plane) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hr, mem_univ z⟩
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × Plane => f x.1 x.2) (r, z) :=
    (hf.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
  have hpath : HasDerivAt (fun r' : ℝ => ((r', z) : ℝ × Plane)) ((1, 0) : ℝ × Plane) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r z)
  exact hdiff.hasFDerivAt.comp_hasDerivAt r hpath

/-- Continuity in `q` of the slice `q ↦ f r (q, η)` for `r > 0`. -/
private theorem hmeanDerivS_cont_slice {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) (η : ℝ) :
    ContinuousOn (fun q : ℝ => f r (q, η)) univ := by
  have hpt : Continuous (fun q : ℝ => ((r, (q, η)) : ℝ × Plane)) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hmaps : MapsTo (fun q : ℝ => ((r, (q, η)) : ℝ × Plane)) univ (Ioi 0 ×ˢ univ) := by
    intro q _
    exact ⟨hr, mem_univ _⟩
  exact hf.continuousOn.comp hpt.continuousOn hmaps

/-- Continuity in `q` of the age derivative `q ↦ ∂_r F (r, q, η)` for `r > 0`. -/
private theorem hmeanDerivS_cont_deriv {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) (η : ℝ) :
    ContinuousOn (fun q : ℝ => fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (r, (q, η)) (1, 0))
      univ := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    hf.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hpt : Continuous (fun q : ℝ => ((r, (q, η)) : ℝ × Plane)) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hmaps : MapsTo (fun q : ℝ => ((r, (q, η)) : ℝ × Plane)) univ (Ioi 0 ×ˢ univ) := by
    intro q _
    exact ⟨hr, mem_univ _⟩
  have hcomp : ContinuousOn
      (fun q : ℝ => fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (r, (q, η))) univ :=
    hfd.comp hpt.continuousOn hmaps
  exact hcomp.clm_apply continuousOn_const

/-- Differentiation under the horizontal integral: for `s > 0`, the age derivative at `s` of
`r ↦ ∫_{(-c/2, c/2]} f r (q, η) dq` is the integral of `∂_r F (s, q, η)`. -/
private theorem hmeanDerivS_integral {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ))
    {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (η : ℝ) :
    HasDerivAt (fun r => ∫ q in (-c / 2)..(c / 2), f r (q, η))
      (∫ q in (-c / 2)..(c / 2),
        fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (s, (q, η)) (1, 0)) s := by
  have hab : -c / 2 ≤ c / 2 := by linarith
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2)) (Ioi 0 ×ˢ univ) :=
    hf.continuousOn_fderiv_of_isOpen hopen (by simp)
  -- the compact box `[s/2, 2s] × [-c/2, c/2]` in the `(r, q)` variables
  have hKc : IsCompact (Icc (s / 2) (2 * s) ×ˢ Icc (-c / 2) (c / 2)) :=
    isCompact_Icc.prod isCompact_Icc
  have hKmaps : MapsTo (fun p : ℝ × ℝ => ((p.1, (p.2, η)) : ℝ × Plane))
      (Icc (s / 2) (2 * s) ×ˢ Icc (-c / 2) (c / 2)) (Ioi 0 ×ˢ univ) := by
    intro p hp
    have hp1 : s / 2 ≤ p.1 := hp.1.1
    refine ⟨?_, mem_univ _⟩
    show (0 : ℝ) < p.1
    linarith
  have hcontK : ContinuousOn
      (fun p : ℝ × ℝ => fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (p.1, (p.2, η)) (1, 0))
      (Icc (s / 2) (2 * s) ×ˢ Icc (-c / 2) (c / 2)) := by
    have hpt : Continuous (fun p : ℝ × ℝ => ((p.1, (p.2, η)) : ℝ × Plane)) :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (p.1, (p.2, η)))
        (Icc (s / 2) (2 * s) ×ˢ Icc (-c / 2) (c / 2)) :=
      hfd.comp hpt.continuousOn hKmaps
    exact hcomp.clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcontK
  -- the neighbourhood of `s` on which the uniform bound is used
  have hnhds : Ioo (s / 2) (2 * s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (fun q : ℝ => f x (q, η))
        (volume.restrict (Set.uIoc (-c / 2) (c / 2))) :=
    Filter.eventually_of_mem hnhds fun x hx =>
      ((hmeanDerivS_cont_slice (r := x) hf (by linarith [hx.1]) η).mono
        (subset_univ (Set.uIoc (-c / 2) (c / 2)))).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun q : ℝ => f s (q, η)) volume (-c / 2) (c / 2) :=
    ((hmeanDerivS_cont_slice (r := s) hf hs η).mono
      (subset_univ (Set.uIcc (-c / 2) (c / 2)))).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable
      (fun q : ℝ => fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (s, (q, η)) (1, 0))
      (volume.restrict (Set.uIoc (-c / 2) (c / 2))) :=
    ((hmeanDerivS_cont_deriv (r := s) hf hs η).mono
      (subset_univ (Set.uIoc (-c / 2) (c / 2)))).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-c / 2) (c / 2) →
      ∀ x ∈ Ioo (s / 2) (2 * s),
        ‖fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (x, (t, η)) (1, 0)‖ ≤ C := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have ht' : t ∈ Icc (-c / 2) (c / 2) := by
      rw [Set.uIoc_of_le hab] at ht
      exact Ioc_subset_Icc_self ht
    exact hC (x, t) ⟨⟨hx.1.le, hx.2.le⟩, ht'⟩
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume (-c / 2) (c / 2) :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-c / 2) (c / 2) →
      ∀ x ∈ Ioo (s / 2) (2 * s),
        HasDerivAt (fun r => f r (t, η))
          (fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (x, (t, η)) (1, 0)) x := by
    refine Filter.Eventually.of_forall fun t _ x hx => ?_
    exact hmeanDerivS_slice hf (r := x) (by linarith [hx.1]) (t, η)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun r q => f r (q, η))
    (F' := fun r q => fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (r, (q, η)) (1, 0))
    (x₀ := s) (s := Ioo (s / 2) (2 * s)) (bound := fun _ => C) (a := -c / 2) (b := c / 2)
    hnhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact key.2

/-- **Age derivative commutes with the horizontal average** (source lines 397-404): for `f`
jointly `C^∞` on `(0, ∞) × Plane` and `s > 0`, `∂_s \bar f = \overline{∂_s f}`. -/
theorem hmeanDerivS : HmeanDerivS := by
  intro c hc f hf s hs η
  have hab : -c / 2 ≤ c / 2 := by linarith
  have hfun : (fun r => hmean c (f r) η) =
      fun r => c⁻¹ • ∫ q in (-c / 2)..(c / 2), f r (q, η) := by
    funext r
    unfold hmean
    rw [intervalIntegral.integral_of_le hab]
  have hL : deriv (fun r => hmean c (f r) η) s =
      c⁻¹ • ∫ q in (-c / 2)..(c / 2),
        fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (s, (q, η)) (1, 0) := by
    rw [hfun]
    exact ((hmeanDerivS_integral hf hc hs η).const_smul c⁻¹).deriv
  have hR : hmean c (fun z => deriv (fun r => f r z) s) η =
      c⁻¹ • ∫ q in (-c / 2)..(c / 2),
        fderiv ℝ (fun x : ℝ × Plane => f x.1 x.2) (s, (q, η)) (1, 0) := by
    unfold hmean
    rw [intervalIntegral.integral_of_le hab]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun q _ => ?_)
    exact (hmeanDerivS_slice hf hs (q, η)).deriv
  rw [hL, hR]

end UnforcedLeray.Short.PartI
