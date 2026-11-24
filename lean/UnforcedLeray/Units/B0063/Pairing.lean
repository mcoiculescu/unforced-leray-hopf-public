import UnforcedLeray.Units.B0063.Strong
import UnforcedLeray.Units.B0009

/-!
# B0063 helper: the group tested against compact smooth functions

Helper file of blueprint unit **B0063** (`paper/main.tex` lines 1238–1243): "It follows first by
testing against compact smooth functions and changing variables in the flow".

* `pairing j M φ : H^j_M →L[ℂ] ℂ`, `X ↦ ∫ X φ dy` for a test function `φ`; `eq_of_pairing`:
  these functionals separate points of `H^j_M`.
* `pairing_transport`: change of variables in the flow,
  `∫ (T(t)f) φ = ∫ f (φ ∘ Φ_{-t})`.
* `hasDerivAt_comp_flow_neg`: `d/ds ψ(Φ_{-s}x) = (Ω∂_ϑψ)(Φ_{-s}x)`, with `Ω∂_ϑψ` the classical
  transport derivative `B0009.transportOf ψ` of unit B0009 (`paper/main.tex:668-670`).
* `transportOf_comp_flow_neg`: `Ω∂_ϑ(ψ ∘ Φ_{-s}) = (Ω∂_ϑψ) ∘ Φ_{-s}` (the field commutes with
  its flow).
* `hasDerivAt_integral_comp_flow_neg`: differentiation under the integral sign,
  `d/ds ∫ f (ψ ∘ Φ_{-s}) = ∫ f ((Ω∂_ϑψ) ∘ Φ_{-s})` for locally integrable `f`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff ENNReal NNReal Topology
open Set Filter MeasureTheory NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0062

namespace UnforcedLeray.B0063

/-! ### The angular derivative along the flow -/

/-- The two Gaussian profiles agree: `B0009.Omega z = Ω(|z|)`. -/
theorem omega_B0009 (z : ℂ) : B0009.Omega z = Omega ‖z‖ := rfl

/-- `d/ds Φ_{-s}(x) = Ω(|x|) i Φ_{-s}(x)`. -/
theorem hasDerivAt_flow_neg (x : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => flow (-s) x) ((Omega ‖x‖ : ℂ) * (Complex.I * flow (-s) x)) s := by
  have e : (fun s : ℝ => flow (-s) x) = fun s => gexp (Omega ‖x‖ * s) * x := by
    funext s
    simp only [flow, phase]
    congr 2
    ring
  have h1 : HasDerivAt (fun s : ℝ => Omega ‖x‖ * s) (Omega ‖x‖) s := by
    simpa using (hasDerivAt_id s).const_mul (Omega ‖x‖)
  have h2 := ((hasDerivAt_gexp _).scomp s h1).mul_const x
  rw [e]
  refine HasDerivAt.congr_deriv h2 ?_
  rw [congrFun e s, Complex.real_smul]
  ring

/-- `d/ds ψ(Φ_{-s}x) = (Ω∂_ϑψ)(Φ_{-s}x)`. -/
theorem hasDerivAt_comp_flow_neg {ψ : ℂ → ℂ} (hψ : Differentiable ℝ ψ) (x : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (flow (-s) x)) (B0009.transportOf ψ (flow (-s) x)) s := by
  have h := (hψ (flow (-s) x)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_flow_neg x s)
  refine HasDerivAt.congr_deriv h ?_
  show _ = (B0009.Omega (flow (-s) x) : ℂ) * fderiv ℝ ψ (flow (-s) x) (Complex.I * flow (-s) x)
  rw [omega_B0009, norm_flow]
  have e : ((Omega ‖x‖ : ℝ) : ℂ) * (Complex.I * flow (-s) x) =
      (Omega ‖x‖) • (Complex.I * flow (-s) x) := (Complex.real_smul ..).symm
  rw [e, map_smul, Complex.real_smul]

/-- `Ω∂_ϑ(ψ ∘ Φ_{-s}) = (Ω∂_ϑψ) ∘ Φ_{-s}`. -/
theorem transportOf_comp_flow_neg {ψ : ℂ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (s : ℝ) (x : ℂ) :
    B0009.transportOf (fun y => ψ (flow (-s) y)) x = B0009.transportOf ψ (flow (-s) x) := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hd' : Differentiable ℝ (fun y => ψ (flow (-s) y)) :=
    hd.comp ((contDiff_flow (-s)).differentiable (by simp))
  have h1 := hasDerivAt_comp_flow_neg hd' x 0
  have h2 := (hasDerivAt_comp_flow_neg hd x (s + 0)).scomp (0 : ℝ)
    ((hasDerivAt_id' (0 : ℝ)).const_add s)
  have e : (fun τ : ℝ => ψ (flow (-s) (flow (-τ) x))) =
      (fun s : ℝ => ψ (flow (-s) x)) ∘ fun τ : ℝ => s + τ := by
    funext τ
    simp only [Function.comp_apply, flow_flow, neg_add]
  rw [e] at h1
  have := h1.unique h2
  simpa [flow_zero] using this

/-! ### Testing against compact smooth functions -/

variable {j : ℕ} {M : ℝ}

variable (j M) in
/-- The pairing `X ↦ ∫ X φ dy` with a test function `φ`, a bounded functional on `H^j_M`. -/
def pairing (φ : TestFn) : HjM j M →L[ℂ] ℂ :=
  (innerSL ℂ (testVec M φ)).comp (HjM.valueCLM j M)

theorem pairing_apply (φ : TestFn) (X : HjM j M) :
    pairing j M φ X = ∫ y, X.value y * φ.1 y := by
  simp only [pairing, ContinuousLinearMap.comp_apply, innerSL_apply_apply, HjM.valueCLM_apply]
  exact inner_testVec M φ X.value

/-- The pairings with test functions separate points of `H^j_M`. -/
theorem eq_of_pairing {X Y : HjM j M} (h : ∀ φ : TestFn, pairing j M φ X = pairing j M φ Y) :
    X = Y := by
  have hae : ∀ᵐ y ∂volume, (X.value : ℂ → ℂ) y - Y.value y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrable_L2w M X.value).sub (locallyIntegrable_L2w M Y.value)) ?_
    intro g hg hgc
    have hφ := B0009.isTestFn_ofReal hg hgc
    have hXY := h ⟨_, hφ⟩
    rw [pairing_apply, pairing_apply] at hXY
    have hfun : (fun y => g y • ((X.value : ℂ → ℂ) y - Y.value y)) =
        fun y => X.value y * (g y : ℂ) - Y.value y * (g y : ℂ) := by
      funext y
      rw [Complex.real_smul]
      ring
    rw [hfun, integral_sub (B0009.integrable_value_mul X hφ) (B0009.integrable_value_mul Y hφ)]
    rw [sub_eq_zero]
    exact hXY
  apply HjM.ext
  apply Lp.ext
  refine (wMeasure_ac M).ae_le ?_
  filter_upwards [hae] with y hy
  exact sub_eq_zero.1 hy

/-- Change of variables in the flow: `∫ (T(t)f) φ = ∫ f (φ ∘ Φ_{-t})`. -/
theorem pairing_transport (φ : TestFn) (t : ℝ) (X : HjM j M) :
    pairing j M φ (transport j M t X) = ∫ x, X.value x * φ.1 (flow (-t) x) := by
  rw [pairing_apply]
  calc ∫ y, (transport j M t X).value y * φ.1 y =
        ∫ y, X.value (flow t y) * φ.1 (flow (-t) (flow t y)) := by
        refine integral_congr_ae ?_
        filter_upwards [transport_value t X] with y hy
        rw [hy, flow_neg_flow]
    _ = ∫ x, X.value x * φ.1 (flow (-t) x) :=
        (smoothMP_flow t).integral_comp (fun x => X.value x * φ.1 (flow (-t) x))

/-- Differentiation under the integral sign:
`d/ds ∫ f(x) ψ(Φ_{-s}x) dx = ∫ f(x) (Ω∂_ϑψ)(Φ_{-s}x) dx` for `f ∈ L¹_loc` and a test function
`ψ`. -/
theorem hasDerivAt_integral_comp_flow_neg {f : ℂ → ℂ} (hf : LocallyIntegrable f) {ψ : ℂ → ℂ}
    (hψ : IsTestFn univ ψ) (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ x, f x * ψ (flow (-s) x))
      (∫ x, f x * B0009.transportOf ψ (flow (-s₀) x)) s₀ := by
  have hψd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hT := B0009.isTestFn_transportOf hψ
  obtain ⟨B, hB⟩ := hT.smooth.continuous.bounded_above_of_compact_support hT.compact
  obtain ⟨R, hR⟩ := hT.compact.isBounded.subset_closedBall (0 : ℂ)
  have hion : IntegrableOn (fun x => B * ‖f x‖) (Metric.closedBall (0 : ℂ) R) :=
    (hf.integrableOn_isCompact (isCompact_closedBall 0 R)).norm.const_mul B
  have hbound_int : Integrable ((Metric.closedBall (0 : ℂ) R).indicator fun x => B * ‖f x‖) :=
    hion.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hψs : IsTestFn univ (fun y => ψ (flow (-s₀) y)) := (smoothMP_flow (-s₀)).testFn_comp hψ
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => f x * ψ (flow (-s) x))
    (F' := fun s x => f x * B0009.transportOf ψ (flow (-s) x))
    (bound := (Metric.closedBall (0 : ℂ) R).indicator fun x => B * ‖f x‖)
    (x₀ := s₀) univ_mem ?_ ?_ ?_ ?_ hbound_int ?_).2
  · exact Eventually.of_forall fun s => hf.aestronglyMeasurable.mul
      (hψ.smooth.continuous.comp (contDiff_flow (-s)).continuous).aestronglyMeasurable
  · have := hf.integrable_smul_right_of_hasCompactSupport hψs.smooth.continuous hψs.compact
    simpa [smul_eq_mul] using this
  · exact hf.aestronglyMeasurable.mul
      (hT.smooth.continuous.comp (contDiff_flow (-s₀)).continuous).aestronglyMeasurable
  · refine Eventually.of_forall fun x s _ => ?_
    by_cases hx : x ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hx, norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · have h0 : B0009.transportOf ψ (flow (-s) x) = 0 := by
        by_contra hne
        apply hx
        have h1 := hR (subset_tsupport _ hne)
        rw [Metric.mem_closedBall, dist_zero_right, norm_flow] at h1
        rwa [Metric.mem_closedBall, dist_zero_right]
      rw [Set.indicator_of_notMem hx]
      simp [h0]
  · exact Eventually.of_forall fun x s _ => (hasDerivAt_comp_flow_neg hψd x s).const_mul (f x)

end UnforcedLeray.B0063
