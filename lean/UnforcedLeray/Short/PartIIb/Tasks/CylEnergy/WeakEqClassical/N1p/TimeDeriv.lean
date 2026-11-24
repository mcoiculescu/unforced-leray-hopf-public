import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2

/-!
# Part II-b, task `PartII-b:T22/2/2/2`: the age derivative of a test (`rtdTimeDeriv`)

Source of record: `the November 2 reference manuscript`, lines 2100-2105.
Inside `(t₀, t₁)` the joint smoothness gives, for each `x`, a derivative in the age `r` equal to
`fderiv Φ (r, x) (1, 0)` (chain rule along `r' ↦ (r', x)`), which is continuous in `x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem rtdTimeDeriv : UnforcedLeray.Short.IIb.RtdTimeDeriv := by
  intro c t₀ t₁ φ hφ r hr
  have hUopen : IsOpen (Ioo t₀ t₁ ×ˢ (univ : Set B0579.Plane)) := isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo t₀ t₁ ×ˢ (univ : Set B0579.Plane) ⊆ Icc t₀ t₁ ×ˢ univ :=
    prod_mono Ioo_subset_Icc_self Subset.rfl
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => φ z.1 z.2)
      (Ioo t₀ t₁ ×ˢ univ) := hφ.smooth.mono hsub
  have hcont : ContinuousOn (fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2))
      (Ioo t₀ t₁ ×ˢ univ) :=
    hU.continuousOn_fderiv_of_isOpen hUopen (by first | simp | exact_mod_cast (top_ne_zero : (⊤:ℕ∞) ≠ 0))
  have hx : ∀ x : B0579.Plane, HasDerivAt (fun r' => φ r' x)
      (fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) ((1 : ℝ), (0 : B0579.Plane))) r := by
    intro x
    have hmem : (r, x) ∈ Ioo t₀ t₁ ×ˢ (univ : Set B0579.Plane) := ⟨hr, mem_univ x⟩
    have hdiff : DifferentiableAt ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) :=
      (hU.contDiffAt (hUopen.mem_nhds hmem)).differentiableAt
        (by first | simp | exact_mod_cast (top_ne_zero : (⊤:ℕ∞) ≠ 0))
    have hγ : HasDerivAt (fun r' : ℝ => (r', x)) ((1 : ℝ), (0 : B0579.Plane)) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
    exact (hdiff.hasFDerivAt).comp_hasDerivAt r hγ
  have hcx : Continuous (fun x : B0579.Plane =>
      fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x) ((1 : ℝ), (0 : B0579.Plane))) := by
    have h1 : Continuous (fun x : B0579.Plane =>
        fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x)) :=
      hcont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hr, mem_univ x⟩)
    exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : B0579.Plane))).continuous.comp h1
  refine ⟨fun x => ?_, ?_⟩
  · rw [(hx x).deriv]
    exact hx x
  · have heq : (fun x : B0579.Plane => deriv (fun r' => φ r' x) r) =
        fun x => fderiv ℝ (fun z : ℝ × B0579.Plane => φ z.1 z.2) (r, x)
          ((1 : ℝ), (0 : B0579.Plane)) :=
      funext fun x => (hx x).deriv
    rw [heq]
    exact hcx

end UnforcedLeray.Short.IIb
