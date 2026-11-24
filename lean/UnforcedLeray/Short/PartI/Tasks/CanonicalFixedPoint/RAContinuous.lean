import UnforcedLeray.Short.PartI.Sub.PartI_C06
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!


Source of record: `the November 2 reference manuscript`, lines 1106-1116 (`r_A` for
`A ∈ C_b([b,∞))`; needed so that `𝒯` maps `C_b` into `C_b`).

Method. For `θ ≥ b`, `r_A(θ) = ∫_{(b,∞)} 1_{(θ,∞)}(s) (A(s)/s) S(θ,s)y ds`. Dominated convergence
(`continuousWithinAt_of_dominated`) within `[b,∞)` at `θ₀`: for `θ ≤ θ₀+1` the integrand is bounded
by `(M/b) C‖y‖ e^{g(θ₀+1)} e^{-gs}`, which is integrable on `(b,∞)`. For `s ≠ θ₀` the integrand is
continuous in `θ` at `θ₀` within `[b,∞)`: for `s > θ₀` by `cont_fst` (`S(·,s)y` continuous on `[b,s]`),
and for `s < θ₀` it vanishes near `θ₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Pointwise bound on the integrand for `b ≤ θ ≤ θ₀+1` and `θ < s`. -/
theorem cra_bound_pt {l : B0010.XG →L[ℂ] ℂ} {b C g : ℝ}
    {S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 < g) (hS : IsComplementPropagator l b C g S)
    {y : B0010.XG} (hy : l y = 0) {A : ℝ → ℂ} {M : ℝ} (hM : ∀ θ, b ≤ θ → ‖A θ‖ ≤ M)
    {θ0 θ s : ℝ} (hθ : b ≤ θ) (hθ' : θ ≤ θ0 + 1) (hθs : θ < s) :
    ‖(A s / (s : ℂ)) • S θ s y‖ ≤
      (M / b * (C * ‖y‖) * Real.exp (g * (θ0 + 1))) * Real.exp ((-g) * s) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b le_rfl)
  have hsp : 0 < s := lt_trans (lt_of_lt_of_le hb hθ) hθs
  have hbs : b ≤ s := le_trans hθ hθs.le
  have hAs : ‖A s‖ ≤ M := hM s hbs
  have hns : ‖(s : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_of_nonneg hsp.le]
  have hdec := hS.decay θ s y hθ hθs.le hy
  have hq : ‖A s‖ / s ≤ M / b := by
    rw [div_le_div_iff₀ hsp hb]
    exact mul_le_mul hAs hbs hb.le hM0
  have hE : Real.exp (-(g * (s - θ))) ≤ Real.exp (g * (θ0 + 1)) * Real.exp ((-g) * s) := by
    have e1 : -(g * (s - θ)) = g * θ + (-g) * s := by ring
    rw [e1, Real.exp_add]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hθ' hg.le)) (Real.exp_pos _).le
  rw [norm_smul, norm_div, hns]
  calc ‖A s‖ / s * ‖S θ s y‖ ≤ (M / b) * (C * Real.exp (-(g * (s - θ))) * ‖y‖) :=
        mul_le_mul hq hdec (norm_nonneg _) (div_nonneg hM0 hb.le)
    _ ≤ (M / b) * (C * (Real.exp (g * (θ0 + 1)) * Real.exp ((-g) * s)) * ‖y‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hC) (norm_nonneg _))
          (div_nonneg hM0 hb.le)
    _ = (M / b * (C * ‖y‖) * Real.exp (g * (θ0 + 1))) * Real.exp ((-g) * s) := by ring

/-- Dominating bound on the (indicator) integrand, for all `s`. -/
theorem cra_bound_all {l : B0010.XG →L[ℂ] ℂ} {b C g : ℝ}
    {S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 < g) (hS : IsComplementPropagator l b C g S)
    {y : B0010.XG} (hy : l y = 0) {A : ℝ → ℂ} {M : ℝ} (hM : ∀ θ, b ≤ θ → ‖A θ‖ ≤ M)
    {θ0 θ s : ℝ} (hθ : b ≤ θ) (hθ' : θ ≤ θ0 + 1) :
    ‖(Ioi θ).indicator (fun s => (A s / (s : ℂ)) • S θ s y) s‖ ≤
      (M / b * (C * ‖y‖) * Real.exp (g * (θ0 + 1))) * Real.exp ((-g) * s) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b le_rfl)
  have hK : 0 ≤ M / b * (C * ‖y‖) * Real.exp (g * (θ0 + 1)) :=
    mul_nonneg (mul_nonneg (div_nonneg hM0 hb.le) (mul_nonneg hC (norm_nonneg _)))
      (Real.exp_pos _).le
  by_cases h : θ < s
  · rw [Set.indicator_of_mem (show s ∈ Ioi θ from h)]
    exact cra_bound_pt hb hC hg hS hy hM hθ hθ' h
  · rw [Set.indicator_of_notMem (show s ∉ Ioi θ from h), norm_zero]
    exact mul_nonneg hK (Real.exp_pos _).le

/-- Continuity of the indicator form of `r_A` at `θ₀ ≥ b` within `[b,∞)`. -/
theorem cra_continuousWithinAt {l : B0010.XG →L[ℂ] ℂ} {b C g : ℝ}
    {S : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 < g) (hS : IsComplementPropagator l b C g S)
    {y : B0010.XG} (hy : l y = 0) {A : ℝ → ℂ} {M : ℝ} (hA : ContinuousOn A (Ici b))
    (hM : ∀ θ, b ≤ θ → ‖A θ‖ ≤ M) {θ0 : ℝ} (hθ0 : b ≤ θ0) :
    ContinuousWithinAt (fun θ => ∫ s in Ioi b,
      (Ioi θ).indicator (fun s => (A s / (s : ℂ)) • S θ s y) s) (Ici b) θ0 := by
  refine continuousWithinAt_of_dominated
    (bound := fun s => (M / b * (C * ‖y‖) * Real.exp (g * (θ0 + 1))) * Real.exp ((-g) * s))
    ?_ ?_ ?_ ?_
  · -- measurability of the indicator integrands near `θ₀`
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθb : b ≤ θ := hθ
    have hfc : ContinuousOn (fun s : ℝ => (A s / (s : ℂ)) • S θ s y) (Ici θ) :=
      ContinuousOn.smul
        (ContinuousOn.div (hA.mono (Ici_subset_Ici.2 hθb)) Complex.continuous_ofReal.continuousOn
          (fun s hs => Complex.ofReal_ne_zero.2 (lt_of_lt_of_le (lt_of_lt_of_le hb hθb) hs).ne'))
        (hS.cont_snd θ y hθb)
    refine (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2 ?_
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hθb)]
    exact (hfc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · -- uniform domination for `θ ∈ [b, θ₀+1)`
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_add_one θ0)),
      self_mem_nhdsWithin] with θ hθ1 hθ2
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s _ => ?_)
    exact cra_bound_all hb hC hg hS hy hM (show b ≤ θ from hθ2) hθ1.le
  · -- the dominating function is integrable on `(b,∞)`
    exact Integrable.const_mul (integrableOn_exp_mul_Ioi (a := -g) (by linarith) b) _
  · -- pointwise continuity in `θ` at `θ₀`, for a.e. `s`
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ θ0 := Measure.ae_ne volume θ0
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioi] with s hs1 hs2
    rcases lt_or_gt_of_ne hs1 with hlt | hgt
    · -- `s < θ₀`: the integrand vanishes for `θ` near `θ₀`
      have hev : ∀ᶠ θ in 𝓝[Ici b] θ0, s < θ :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hlt)
      refine (continuousWithinAt_const (b := (0 : B0010.XG))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hev] with θ hθ
        exact Set.indicator_of_notMem (show s ∉ Ioi θ from not_lt.2 hθ.le) _
      · exact Set.indicator_of_notMem (show s ∉ Ioi θ0 from not_lt.2 hlt.le) _
    · -- `θ₀ < s`: the integrand is `(A s/s) S(θ,s)y`, continuous in `θ ∈ [b,s]`
      have hlt' : ∀ᶠ θ in 𝓝 θ0, θ < s := eventually_lt_nhds hgt
      have hmem : Icc b s ∈ 𝓝[Ici b] θ0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds hlt', self_mem_nhdsWithin]
          with θ h1 h2
        exact ⟨h2, h1.le⟩
      have hcS : ContinuousWithinAt (fun θ => S θ s y) (Icc b s) θ0 :=
        (hS.cont_fst s y).continuousWithinAt ⟨hθ0, hgt.le⟩
      have hcS' : ContinuousWithinAt (fun θ => S θ s y) (Ici b) θ0 :=
        hcS.mono_of_mem_nhdsWithin hmem
      have hcF : ContinuousWithinAt (fun θ => (A s / (s : ℂ)) • S θ s y) (Ici b) θ0 :=
        hcS'.const_smul (A s / (s : ℂ))
      refine hcF.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds hlt'] with θ hθ
        exact Set.indicator_of_mem (show s ∈ Ioi θ from hθ) _
      · exact Set.indicator_of_mem (show s ∈ Ioi θ0 from hgt) _

/-- **Target `PartI:C06/4`** (source lines 1106-1116): `θ ↦ r_A(θ)` is continuous on `[b,∞)`. -/
theorem canonicalRAContinuous : CanonicalRAContinuous := by
  intro l b C g S hb hC hg hS y hy A M hA hM
  intro θ0 hθ0
  have hrep : ∀ θ, b ≤ θ → canonicalRA S y A θ = ∫ s in Ioi b,
      (Ioi θ).indicator (fun s => (A s / (s : ℂ)) • S θ s y) s := by
    intro θ hθ
    rw [setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.2 (Ioi_subset_Ioi hθ)]
    rfl
  exact ContinuousWithinAt.congr (cra_continuousWithinAt hb hC hg hS hy hA hM hθ0)
    (fun θ hθ => hrep θ hθ) (hrep θ0 hθ0)

end UnforcedLeray.Short.PartI
