import UnforcedLeray.Lib.PhaseTrace.ChartTest
import UnforcedLeray.Lib.BochnerTime.Basic
import UnforcedLeray.Lib.BochnerTime.Duhamel
import UnforcedLeray.Lib.PhaseSpace.Graph

/-!
# The comoving pullback has a weak time derivative (INF14 T6, `comoving_hasWeakDerivTime`)

Tex 7609–7616 (`sec:st18-9174`, unit B0434; blueprint B0434/B0435/B0451/B1006 via T6):
"On any bounded phase interval, the pullback `V(t, x) = w(τ₀ + t, e^{-t/2} x)` belongs to
`W^{1,q}` with values in spatial `L^q`, with derivative equal to the pullback of `T₀w`. This
follows ... by changing variables in distributional tests."

Here `w, b ∈ Y_q` with `T₀w = b` in distributions (`HasPhaseOp driftT w b`, the second
condition of the free graph `D_(ν,q)`, tex 7322–7327), and

  `comoving f τ₀ t = dil t (f(τ₀ + t)) ∈ L^q(ℝ³; ℂ³)`,   `(dil t g)(x) = g(e^{-t/2} x)`.

`comoving_hasWeakDerivTime` proves `HasWeakDerivTime a b (comoving w τ₀) (comoving b τ₀)` on
every bounded interval `(a, b)` for `1 ≤ q < ∞` (the manuscript has `1 < q < ∞`). The proof
tests against the separating functionals `g ↦ ∫ ψ e · g` (`ChartTest.exists_ell`): for each,
the chart test `chartTest τ₀ φ ψ e`, periodized in the phase (`Periodize.perT`), is a phase
test whose transpose drift is the chart test of `-φ'` (`driftT_chartTest`, `driftT_perT`),
and the unfolded pairing (`phasePair_perT`) followed by the change of variables
(`pairing_chartTest`) turns `⟪T₀ᵗΦ, w⟫ = ⟪Φ, b⟫` into
`∫ φ' ℓ(V_w) = -∫ φ ℓ(V_b)`.

Status: infrastructure (target T6, first half). No manuscript unit is closed by this file.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseTrace

open UnforcedLeray.PhaseSpace UnforcedLeray.BochnerTime

/-- **Separating-family criterion, Banach-valued functionals.** Adapted from

(`hasWeakDerivTime_of_separating`), with continuous linear maps into any Banach space `Y`
in place of real functionals. -/
theorem hasWeakDerivTime_of_separating' {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {a b : ℝ} {u u' : ℝ → X} {Λ : Set (X →L[ℝ] Y)}
    (hsep : ∀ x : X, (∀ ℓ ∈ Λ, ℓ x = 0) → x = 0)
    (hint : IntegrableOn u (Ioo a b)) (hint' : IntegrableOn u' (Ioo a b))
    (h : ∀ ℓ ∈ Λ, HasWeakDerivTime a b (fun t => ℓ (u t)) (fun t => ℓ (u' t))) :
    HasWeakDerivTime a b u u' := by
  refine ⟨hint, hint', fun φ hφ hφs hφt => ?_⟩
  have h1 := integrable_deriv_smul hφ hφs hφt hint
  have h2 := integrable_smul hφ hφs hφt hint'
  refine eq_neg_of_add_eq_zero_left (hsep _ fun ℓ hℓ => ?_)
  rw [map_add, ← ℓ.integral_comp_comm h1, ← ℓ.integral_comp_comm h2]
  simp only [map_smul]
  have := (h ℓ hℓ).identity φ hφ hφs hφt
  rw [this, neg_add_cancel]

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **The comoving pullback** `t ↦ f(τ₀ + t)(e^{-t/2} ·)` of `f ∈ Y_q` (tex 7612–7614). -/
def comoving (f : Yq P q) (τ₀ t : ℝ) : Lp CVec3 q (volume : Measure Space) :=
  dil CVec3 q t (f ((τ₀ + t : ℝ) : AddCircle P))

theorem norm_comoving (f : Yq P q) (τ₀ t : ℝ) :
    ‖comoving f τ₀ t‖ = dilConst q t * ‖f ((τ₀ + t : ℝ) : AddCircle P)‖ :=
  norm_dil _ _

theorem comoving_add_period (f : Yq P q) (τ₀ : ℝ) :
    comoving f (τ₀ + P) = comoving f τ₀ := by
  funext t
  simp only [comoving]
  rw [show τ₀ + P + t = (τ₀ + t) + P by ring, AddCircle.coe_add_period]

theorem aestronglyMeasurable_comoving (hq : q ≠ ⊤) (f : Yq P q) (τ₀ : ℝ) :
    AEStronglyMeasurable (comoving f τ₀) volume := by
  have h1 : AEStronglyMeasurable (fun t : ℝ => f ((τ₀ + t : ℝ) : AddCircle P)) volume :=
    (aestronglyMeasurable_comp_mk f).comp_measurePreserving (measurePreserving_add_left volume τ₀)
  exact aestronglyMeasurable_apply (U := dil CVec3 q) (fun x => continuous_dil_apply hq x) h1

theorem intervalIntegrable_norm_shift (f : Yq P q) (τ₀ a b : ℝ) :
    IntervalIntegrable (fun t => ‖f ((τ₀ + t : ℝ) : AddCircle P)‖) volume a b := by
  have h := ((intervalIntegrable_comp_mk f (τ₀ + a) (τ₀ + b)).comp_add_left τ₀).norm
  simpa using h

theorem integrableOn_comoving (hq : q ≠ ⊤) (f : Yq P q) (τ₀ a b : ℝ) :
    IntegrableOn (comoving f τ₀) (Ioo a b) := by
  rcases le_or_gt b a with hba | hab
  · rw [Ioo_eq_empty_of_le hba]; exact integrableOn_empty
  have hg : IntegrableOn (fun t => dilConst q b * ‖f ((τ₀ + t : ℝ) : AddCircle P)‖) (Ioo a b) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp
      (intervalIntegrable_norm_shift f τ₀ a b)).const_mul _
  refine Integrable.mono' hg (aestronglyMeasurable_comoving hq f τ₀).restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [norm_comoving]
  gcongr
  exact dilConst_mono q ht.2.le

/-- The chart-test identity behind T6: for each separating functional `ℓ`,
`∫ φ' ℓ(V_w) = -∫ φ ℓ(V_b)`. -/
theorem hasWeakDerivTime_ell (hq : q ≠ ⊤) {w b : Yq P q} (h : HasPhaseOp driftT w b)
    (τ₀ a a' : ℝ) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (e : CVec3) (L : Lp CVec3 q (volume : Measure Space) →L[ℝ] ℂ)
    (hL : ∀ g, L g = ∫ x, ψ x • dotL e ((g : Space → CVec3) x)) :
    HasWeakDerivTime a a' (fun t => L (comoving w τ₀ t)) (fun t => L (comoving b τ₀ t)) := by
  refine ⟨L.integrable_comp (integrableOn_comoving hq w τ₀ a a'),
    L.integrable_comp (integrableOn_comoving hq b τ₀ a a'), fun φ hφ hφs _ => ?_⟩
  have hφ' : ContDiff ℝ ∞ (fun σ => -deriv φ σ) := (contDiff_infty_iff_deriv.mp hφ).2.neg
  have hφ's : HasCompactSupport (fun σ => -deriv φ σ) := hφs.deriv.comp_left neg_zero
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_of_hasCompactSupport hφs
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_of_hasCompactSupport hφ's
  set G₁ := chartTest τ₀ φ ψ e with hG₁
  set G₂ := chartTest τ₀ (fun σ => -deriv φ σ) ψ e with hG₂
  have hG₁0 : IsPhaseTest 0 G₁ := isPhaseTest_chartTest hφ hφs hψ hψc e
  have hG₂0 : IsPhaseTest 0 G₂ := isPhaseTest_chartTest hφ' hφ's hψ hψc e
  have hT₁ : TimeSupp (τ₀ - M₁) (τ₀ + M₁) G₁ := timeSupp_chartTest (fun σ hσ => hM₁ σ hσ) e
  have hT₂ : TimeSupp (τ₀ - M₂) (τ₀ + M₂) G₂ := timeSupp_chartTest (fun σ hσ => hM₂ σ hσ) e
  have hΦ := isPhaseTest_perT hP.out hT₁ hG₁0
  have hid := h (perT P G₁) hΦ
  rw [driftT_perT hP.out hT₁ hG₁0.smooth, hG₁, driftT_chartTest hφ hψ e, ← hG₂,
    phasePair_perT hG₂0 (by linarith) hT₂, phasePair_perT hG₁0 (by linarith) hT₁] at hid
  have hid' : ∫ t, pairH hG₂0 w t = ∫ t, pairH hG₁0 b t := by
    have hP0 : (P⁻¹ : ℂ) ≠ 0 := inv_ne_zero (by exact_mod_cast hP.out.ne')
    have := hid
    rw [show ((P⁻¹ : ℝ) • ∫ t, pairH hG₂0 w t) = (P⁻¹ : ℂ) * ∫ t, pairH hG₂0 w t by
        rw [Complex.real_smul]; push_cast; ring,
      show ((P⁻¹ : ℝ) • ∫ t, pairH hG₁0 b t) = (P⁻¹ : ℂ) * ∫ t, pairH hG₁0 b t by
        rw [Complex.real_smul]; push_cast; ring] at this
    exact mul_left_cancel₀ hP0 this
  have hpair : ∀ (G : ℝ × Space → CVec3) (hG0 : IsPhaseTest 0 G) (χ : ℝ → ℝ)
      (_ : G = chartTest τ₀ χ ψ e) (f : Yq P q),
      ∫ t, pairH hG0 f t = ∫ σ, χ σ • L (comoving f τ₀ σ) := by
    intro G hG0 χ hGχ f
    have hshift := integral_add_left_eq_self (μ := (volume : Measure ℝ)) (pairH hG0 f) τ₀
    rw [← hshift]
    refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
    simp only
    rw [pairH_eq, hGχ, pairing_chartTest, hL]
    rfl
  rw [hpair G₂ hG₂0 _ hG₂ w, hpair G₁ hG₁0 φ hG₁ b] at hid'
  simp only [neg_smul, integral_neg] at hid'
  rw [← hid', neg_neg]

/-- **T6, comoving half** (`comoving_hasWeakDerivTime`). If `T₀w = b` in distributions on
`Y_q`, `1 ≤ q < ∞`, then for every base phase `τ₀` and every bounded interval `(a, a')` the
comoving pullback `t ↦ w(τ₀ + t)(e^{-t/2} ·)` has weak time derivative
`t ↦ b(τ₀ + t)(e^{-t/2} ·)` in `L^q(ℝ³; ℂ³)` (tex 7612–7616, unit B0434). -/
theorem comoving_hasWeakDerivTime (hq : q ≠ ⊤) {w b : Yq P q} (h : HasPhaseOp driftT w b)
    (τ₀ a a' : ℝ) : HasWeakDerivTime a a' (comoving w τ₀) (comoving b τ₀) := by
  refine hasWeakDerivTime_of_separating'
    (Λ := {L : Lp CVec3 q (volume : Measure Space) →L[ℝ] ℂ | ∃ ψ : Space → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ∃ e : CVec3,
        ∀ g, L g = ∫ x, ψ x • dotL e ((g : Space → CVec3) x)})
    ?_ (integrableOn_comoving hq w τ₀ a a') (integrableOn_comoving hq b τ₀ a a') ?_
  · intro x hx
    refine eq_zero_of_ell x fun ψ hψ hψc e => ?_
    obtain ⟨L, hL⟩ := exists_ell (q := q) hψ.continuous hψc e
    rw [← hL]
    exact hx L ⟨ψ, hψ, hψc, e, hL⟩
  · rintro L ⟨ψ, hψ, hψc, e, hL⟩
    exact hasWeakDerivTime_ell hq h τ₀ a a' hψ hψc e L hL

end UnforcedLeray.PhaseTrace
