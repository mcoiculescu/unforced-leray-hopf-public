import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub

/-!
# Classical and weak spatial derivatives agree where the field is `C¹` (`WeakDerivClassicalOn`)

Source of record: `the November 2 reference manuscript`, used for the
representatives of 2607-2609.  Generic real analysis: a continuous weak `i`-th derivative of a field
`f` that is `C¹` on an open set `O` equals the classical partial `physPd f i` on `O`.

Proof: for a test `φ` with `tsupport φ ⊆ O`, integration by parts (Mathlib
`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`) gives `∫ φ • ∂_if = ∫ φ • g`; the fundamental
lemma on `O` gives `∂_if = g` a.e. on `O`; both sides are continuous on `O`, so they agree there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem weakDerivClassicalOn : WeakDerivClassicalOn := by
  intro i f g O hw hg hO hf
  -- the classical partial is continuous on `O`
  have hcontD : ContinuousOn (fun y => physPd f i y) O := by
    have h1 : ContinuousOn (fun y => fderiv ℝ f y) O :=
      hf.continuousOn_fderiv_of_isOpen hO le_rfl
    show ContinuousOn (fun y => fderiv ℝ f y (UnforcedLeray.coordinateVector i)) O
    exact h1.clm_apply continuousOn_const
  have hcontf : ContinuousOn f O := hf.continuousOn
  -- integrability of `φ • F` for a field `F` continuous on the support of the test `φ`
  have hint : ∀ (F : Space → Space) (φ : Space → ℝ), UnforcedLeray.IsSpatialTest φ →
      ContinuousOn F (tsupport φ) → Integrable (fun x => φ x • F x) := by
    intro F φ hφ hF
    have hsub : Function.support (fun x => φ x • F x) ⊆ tsupport φ :=
      (Function.support_smul_subset_left φ F).trans (subset_tsupport φ)
    exact (integrableOn_iff_integrable_of_support_subset hsub).mp
      ((hφ.smooth.continuous.continuousOn.smul hF).integrableOn_compact hφ.compact.isCompact)
  -- integration by parts against a test supported in `O`
  have hIBP : ∀ φ : Space → ℝ, UnforcedLeray.IsSpatialTest φ → tsupport φ ⊆ O →
      ∫ x, φ x • physPd f i x = ∫ x, φ x • g x := by
    intro φ hφ hsub
    have hφc : ContinuousOn f (tsupport φ) := hcontf.mono hsub
    have hφD : ContinuousOn (fun y => physPd f i y) (tsupport φ) := hcontD.mono hsub
    have hfd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ f x := fun x hx =>
      (hf.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds (hsub hx))
    have ibp : ∫ x, φ x • fderiv ℝ f x (UnforcedLeray.coordinateVector i) =
        -∫ x, fderiv ℝ φ x (UnforcedLeray.coordinateVector i) • f x :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
        (v := UnforcedLeray.coordinateVector i)
        (hw.left_integrable φ hφ)
        (hint (fun y => fderiv ℝ f y (UnforcedLeray.coordinateVector i)) φ hφ hφD)
        (hint f φ hφ hφc)
        (fun x _ => hφ.smooth.differentiable (by simp) x)
        hfd
    have h1 : ∫ x, fderiv ℝ φ x (UnforcedLeray.coordinateVector i) • f x =
        -∫ x, φ x • g x := hw.identity φ hφ
    calc ∫ x, φ x • physPd f i x
        = -∫ x, fderiv ℝ φ x (UnforcedLeray.coordinateVector i) • f x := ibp
      _ = -(-∫ x, φ x • g x) := by rw [h1]
      _ = ∫ x, φ x • g x := neg_neg _
  -- the fundamental lemma on the open set `O`
  have hfund : ∀ᵐ x ∂(volume : Measure Space), x ∈ O → physPd f i x - g x = 0 := by
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact (hcontD.sub hg.continuousOn).locallyIntegrableOn hO.measurableSet
    · intro φ hφs hφc hsub
      have hφ : UnforcedLeray.IsSpatialTest φ := ⟨hφs, hφc⟩
      have hI1 : Integrable (fun x => φ x • physPd f i x) :=
        hint (fun y => physPd f i y) φ hφ (hcontD.mono hsub)
      have hI2 : Integrable (fun x => φ x • g x) := hw.right_integrable φ hφ
      have hI := hIBP φ hφ hsub
      show ∫ x, φ x • (physPd f i x - g x) = 0
      simp only [smul_sub]
      rw [integral_sub hI1 hI2, hI, sub_self]
  -- equality a.e. on `O`, then everywhere on `O` by continuity
  have hae : (fun y => physPd f i y) =ᵐ[volume.restrict O] g := by
    refine (ae_restrict_iff' hO.measurableSet).mpr ?_
    filter_upwards [hfund] with x hx hxO
    exact sub_eq_zero.mp (hx hxO)
  exact fun y hy => MeasureTheory.Measure.eqOn_open_of_ae_eq hae hO hcontD hg.continuousOn hy

end UnforcedLeray.Short.PartIIIb.Concrete
