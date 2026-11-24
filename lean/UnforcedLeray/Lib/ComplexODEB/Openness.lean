import UnforcedLeray.Lib.ComplexODEB.Coercive
import UnforcedLeray.Analysis.Rayleigh.Evans.ParameterDependence
import UnforcedLeray.Lib.ComplexODEB.MinModulus
import Mathlib.Analysis.Complex.Convex

/-!
# B0034 helper: openness of the unstable wavenumbers (Hurwitz by minimum modulus)

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of Lin's continuation argument behind B0034 (`paper/main.tex`, lines
1012–1014; Lin 2003, Lemma 5.8): if `D(β₀,·)` has a zero `c₀` with `Im c₀ > 0`
and `β₀ ≠ 0`, then `D(β,·)` has a zero in the upper half-plane for every `β`
near `β₀`.

Proof. `D(β₀,·)` is holomorphic on the connected upper half-plane and not
identically zero (`exists_evansFunction_ne_zero`), so `c₀` is an isolated zero.
On a small circle around `c₀` inside the half-plane, `|D(β₀,·)| ≥ m > 0`. By joint
continuity on the compact closed disc, `|D(β,·) - D(β₀,·)| < m/2` there for `β`
near `β₀`; then `|D(β,c₀)| < m/2 < |D(β,z)|` on the circle, and the
minimum-modulus lemma `exists_zero_of_center_norm_lt_sphere` gives a zero.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology Metric
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans

theorem isPreconnected_upperHalfPlane : IsPreconnected upperHalfPlane :=
  (convex_halfSpace_im_gt 0).isPreconnected

/-- Hurwitz persistence of an upper-half-plane Evans zero under a change of the
real wavenumber. -/
theorem eventually_exists_zero {a b β₀ : ℝ} (hab : a < b) (hβ₀ : β₀ ≠ 0) {c₀ : ℂ}
    (hc₀ : 0 < c₀.im) (hz : evansFunction β₀ a b c₀ = 0) :
    ∀ᶠ β in 𝓝 β₀, ∃ c : ℂ, 0 < c.im ∧ evansFunction β a b c = 0 := by
  set f : ℂ → ℂ := evansFunction β₀ a b with hf_def
  have hfa : AnalyticOnNhd ℂ f upperHalfPlane := analyticOnNhd_evansFunction β₀ a b
  -- `c₀` is an isolated zero
  have hiso : ∀ᶠ z in 𝓝[≠] c₀, f z ≠ 0 := by
    rw [← Filter.not_frequently]
    intro hfreq
    have hzero := hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_upperHalfPlane hc₀ hfreq
    obtain ⟨c₁, hc₁, hne⟩ := exists_evansFunction_ne_zero (β := β₀) hab hβ₀
    exact hne (hzero hc₁)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨r₁, hr₁, hr₁'⟩ := hiso
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.isOpen_iff.mp isOpen_upperHalfPlane c₀ hc₀
  set ρ : ℝ := min r₁ r₂ / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρ₁ : ρ < r₁ := by have := min_le_left r₁ r₂; linarith
  have hρ₂ : ρ < r₂ := by have := min_le_right r₁ r₂; linarith
  have hball : closedBall c₀ ρ ⊆ upperHalfPlane := fun z hz =>
    hr₂' (lt_of_le_of_lt (mem_closedBall.mp hz) hρ₂)
  -- the minimum modulus on the circle
  have hfc : ContinuousOn f upperHalfPlane := (differentiableOn_evansFunction β₀ a b).continuousOn
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c₀ ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    ((hfc.mono (sphere_subset_closedBall.trans hball)).norm)
  set m : ℝ := ‖f z₁‖ with hm_def
  have hm : 0 < m := by
    have hd : dist z₁ c₀ = ρ := mem_sphere.mp hz₁
    have hne : z₁ ≠ c₀ := by
      intro h
      rw [h, dist_self] at hd
      linarith
    exact norm_pos_iff.mpr (hr₁' (by rw [hd]; exact hρ₁) hne)
  -- uniform closeness on the closed disc for nearby wavenumbers
  have hU : IsOpen {p : ℝ × ℂ | p.2 ∈ upperHalfPlane} :=
    isOpen_upperHalfPlane.preimage continuous_snd
  have hclose : ∀ᶠ β in 𝓝 β₀, ∀ z ∈ closedBall c₀ ρ,
      ‖evansFunction β a b z - f z‖ < m / 2 := by
    apply (isCompact_closedBall c₀ ρ).eventually_forall_of_forall_eventually
    intro y hy
    have hyU : y ∈ upperHalfPlane := hball hy
    have h1 : ContinuousAt (fun p : ℝ × ℂ => evansFunction p.1 a b p.2) (β₀, y) :=
      (continuousOn_evansFunction_parameters a b).continuousAt (hU.mem_nhds hyU)
    have h2 : ContinuousAt (fun p : ℝ × ℂ => f p.2) (β₀, y) :=
      ContinuousAt.comp (g := f) (f := Prod.snd) (x := (β₀, y))
        (hfc.continuousAt (isOpen_upperHalfPlane.mem_nhds hyU)) continuous_snd.continuousAt
    have h3 : ContinuousAt (fun p : ℝ × ℂ => evansFunction p.1 a b p.2 - f p.2) (β₀, y) :=
      h1.sub h2
    have h4 : Tendsto (fun p : ℝ × ℂ => evansFunction p.1 a b p.2 - f p.2) (𝓝 (β₀, y))
        (𝓝 0) := by
      have := h3.tendsto
      simpa [hf_def] using this
    have h5 := (h4.norm).eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < m / 2 by simpa using hm))
    exact h5
  filter_upwards [hclose] with β hβ
  have hdiff : DiffContOnCl ℂ (evansFunction β a b) (ball c₀ ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c₀ hρ.ne']
    exact (differentiableOn_evansFunction β a b).mono hball
  obtain ⟨z, hzb, hz0⟩ := exists_zero_of_center_norm_lt_sphere hρ hdiff (by
    intro z hzs
    have hc0 : ‖evansFunction β a b c₀‖ < m / 2 := by
      have := hβ c₀ (mem_closedBall_self hρ.le)
      rwa [show f c₀ = 0 from hz, sub_zero] at this
    have hzc := hβ z (sphere_subset_closedBall hzs)
    have hzm : m ≤ ‖f z‖ := hmin hzs
    have htri : ‖f z‖ ≤ ‖evansFunction β a b z - f z‖ + ‖evansFunction β a b z‖ := by
      have := norm_sub_le (evansFunction β a b z) (evansFunction β a b z - f z)
      simp only [sub_sub_cancel] at this
      linarith [norm_sub_rev (evansFunction β a b z) (evansFunction β a b z - f z)]
    linarith)
  exact ⟨z, hball hzb, hz0⟩

/-- The set of nonzero real wavenumbers carrying an upper-half-plane Evans zero is open. -/
theorem isOpen_unstableWavenumbers {a b : ℝ} (hab : a < b) :
    IsOpen {β : ℝ | β ≠ 0 ∧ ∃ c : ℂ, 0 < c.im ∧ evansFunction β a b c = 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro β₀ ⟨hβ₀, c₀, hc₀, hz⟩
  filter_upwards [isOpen_ne.mem_nhds hβ₀, eventually_exists_zero hab hβ₀ hc₀ hz] with β h1 h2
  exact ⟨h1, h2⟩

end UnforcedLeray.ComplexODEB
