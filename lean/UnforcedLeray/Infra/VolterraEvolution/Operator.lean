import UnforcedLeray.Infra.VolterraEvolution.Kernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc

/-!
# The singular Volterra operator with square-root smoothing

Abstract setting of `paper/main.tex`, lines 292-306 (Section `sec:st18-265`): Banach spaces
`X`, `Y` over `𝕜 = ℝ` or `ℂ` (any `RCLike` field), a free evolution `S₀ : ℝ → (X →L X)`,
a smoothing family `S : ℝ → (Y →L X)` with `‖S t‖ ≤ C₀ t^{-1/2}` for `0 < t ≤ 1`, and a
coefficient family `B : ℝ → (X →L Y)`.  In the manuscript `X = H¹_div`, `Y = L²_div`,
`S₀` is the free similarity evolution, `S` the same evolution viewed as a map `L² → H¹`,
and `B = 𝓑_*`.

This file bundles the hypotheses as `VolterraData` and studies the Volterra integral
`D.vol s f τ = ∫ r in s..τ, S (τ - r) (B r (f r))` on the unit strip `s ≤ τ ≤ s + 1`:
integrability, the exponentially weighted bound, linearity, and continuity in `τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

/-- Strong continuity plus a local operator-norm bound gives continuity along continuous
paths: `t ↦ K t (v t)` is continuous on `U`. -/
theorem continuousOn_clm_apply {α 𝕜 E F : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {K : α → E →L[𝕜] F} {v : α → E} {U : Set α}
    (hK : ∀ e, ContinuousOn (fun t => K t e) U)
    (hb : ∀ t₀ ∈ U, ∃ C, ∀ᶠ t in 𝓝[U] t₀, ‖K t‖ ≤ C)
    (hv : ContinuousOn v U) : ContinuousOn (fun t => K t (v t)) U := by
  intro t₀ ht₀
  obtain ⟨C, hC⟩ := hb t₀ ht₀
  have h1 : Tendsto (fun t => K t (v t₀)) (𝓝[U] t₀) (𝓝 (K t₀ (v t₀))) := hK (v t₀) t₀ ht₀
  have hv0 : Tendsto (fun t => ‖v t - v t₀‖) (𝓝[U] t₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hv t₀ ht₀)
  have h2 : Tendsto (fun t => K t (v t) - K t (v t₀)) (𝓝[U] t₀) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hv0.const_mul C)
    filter_upwards [hC] with t ht
    rw [← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have := h2.add h1
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-- Almost every real number avoids a given point. -/
theorem ae_ne_real (c : ℝ) : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ c := by
  rw [ae_iff]
  simp

/-- Data of the abstract Volterra problem with square-root smoothing
(`paper/main.tex`, lines 292-306).

* `S₀ : ℝ → (X →L X)` is the free evolution, bounded by `M₀` and strongly continuous on
  `[0, 1]`;
* `S : ℝ → (Y →L X)` is the smoothing family, `‖S t‖ ≤ C₀ t^{-1/2}` and strongly continuous
  on `(0, 1]` (only these elapsed times enter the strip construction; the value `S 0` is
  never used);
* `B : ℝ → (X →L Y)` is the coefficient family, uniformly bounded by `β` and strongly
  continuous on `ℝ`. -/
structure VolterraData (𝕜 : Type*) [RCLike 𝕜] (X Y : Type*) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  /-- The free evolution. -/
  S₀ : ℝ → X →L[𝕜] X
  /-- The smoothing family `Y → X`. -/
  S : ℝ → Y →L[𝕜] X
  /-- The coefficient family `X → Y`. -/
  B : ℝ → X →L[𝕜] Y
  /-- Bound for the free evolution on `[0, 1]`. -/
  M₀ : ℝ
  /-- Constant of the square-root smoothing bound. -/
  C₀ : ℝ
  /-- Uniform bound for the coefficients. -/
  β : ℝ
  norm_S₀_le : ∀ t, 0 ≤ t → t ≤ 1 → ‖S₀ t‖ ≤ M₀
  norm_S_le : ∀ t, 0 < t → t ≤ 1 → ‖S t‖ ≤ C₀ * t ^ (-(1 / 2 : ℝ))
  norm_B_le : ∀ t, ‖B t‖ ≤ β
  continuousOn_S₀ : ∀ x, ContinuousOn (fun t => S₀ t x) (Icc 0 1)
  continuousOn_S : ∀ y, ContinuousOn (fun t => S t y) (Ioc 0 1)
  continuous_B : ∀ x, Continuous (fun t => B t x)

namespace VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (D : VolterraData 𝕜 X Y)

theorem M₀_nonneg : 0 ≤ D.M₀ := (norm_nonneg _).trans (D.norm_S₀_le 0 le_rfl zero_le_one)

theorem β_nonneg : 0 ≤ D.β := (norm_nonneg _).trans (D.norm_B_le 0)

theorem C₀_nonneg : 0 ≤ D.C₀ := by
  have h := D.norm_S_le 1 one_pos le_rfl
  rw [one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

/-- Near a positive time `t₀`, the smoothing family is bounded by `C₀ (t₀/2)^{-1/2}`. -/
theorem eventually_norm_S_le {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∀ᶠ t in 𝓝 t₀, t ≤ 1 → ‖D.S t‖ ≤ D.C₀ * (t₀ / 2) ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [lt_mem_nhds (half_lt_self ht₀)] with t ht ht1
  have htpos : 0 < t := lt_trans (half_pos ht₀) ht
  refine (D.norm_S_le t htpos ht1).trans ?_
  exact mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_nonpos (half_pos ht₀) ht.le (by norm_num)) D.C₀_nonneg

/-- `r ↦ B r (f r)` is continuous wherever `f` is. -/
theorem continuousOn_B_apply {U : Set ℝ} {f : ℝ → X} (hf : ContinuousOn f U) :
    ContinuousOn (fun r => D.B r (f r)) U :=
  continuousOn_clm_apply (fun x => (D.continuous_B x).continuousOn)
    (fun _ _ => ⟨D.β, Eventually.of_forall fun t => D.norm_B_le t⟩) hf

/-- The Volterra integrand is continuous on `[s, τ)` when `f` is. -/
theorem continuousOn_integrand {s τ : ℝ} (hτ : τ ≤ s + 1) {f : ℝ → X}
    (hf : ContinuousOn f (Ico s τ)) :
    ContinuousOn (fun r => D.S (τ - r) (D.B r (f r))) (Ico s τ) := by
  refine continuousOn_clm_apply (K := fun r => D.S (τ - r)) ?_ ?_ (D.continuousOn_B_apply hf)
  · intro y
    refine (D.continuousOn_S y).comp (continuousOn_const.sub continuousOn_id) ?_
    intro r hr
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
  · intro r₀ hr₀
    have hpos : 0 < τ - r₀ := by linarith [hr₀.2]
    refine ⟨D.C₀ * ((τ - r₀) / 2) ^ (-(1 / 2 : ℝ)), ?_⟩
    have ht : Tendsto (fun r => τ - r) (𝓝 r₀) (𝓝 (τ - r₀)) := tendsto_const_nhds.sub tendsto_id
    have h1 := nhdsWithin_le_nhds (s := Ico s τ) (ht.eventually (D.eventually_norm_S_le hpos))
    filter_upwards [h1, self_mem_nhdsWithin] with r hr hrU
    exact hr (by linarith [hrU.1])

/-- Pointwise bound of the Volterra integrand on `[s, τ)`. -/
theorem norm_integrand_le {s τ r : ℝ} (hτ : τ ≤ s + 1) (hr : r ∈ Ico s τ) (f : ℝ → X) :
    ‖D.S (τ - r) (D.B r (f r))‖ ≤ D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * ‖f r‖ := by
  have h1 : ‖D.S (τ - r)‖ ≤ D.C₀ * (τ - r) ^ (-(1 / 2 : ℝ)) :=
    D.norm_S_le _ (by linarith [hr.2]) (by linarith [hr.1])
  calc ‖D.S (τ - r) (D.B r (f r))‖ ≤ ‖D.S (τ - r)‖ * ‖D.B r (f r)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (D.C₀ * (τ - r) ^ (-(1 / 2 : ℝ))) * (D.β * ‖f r‖) := by
        refine mul_le_mul h1 ?_ (norm_nonneg _) ((norm_nonneg _).trans h1)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (D.norm_B_le r) (norm_nonneg _))
    _ = D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * ‖f r‖ := by ring

section Integral

variable [NormedSpace ℝ X]

/-- The Volterra integral `∫ r in s..τ, S (τ - r) (B r (f r))`. -/
def vol (s : ℝ) (f : ℝ → X) (τ : ℝ) : X :=
  ∫ r in s..τ, D.S (τ - r) (D.B r (f r))

omit [NormedSpace ℝ X] in
/-- The Volterra integrand is interval integrable on `[s, τ]` for `f` continuous there. -/
theorem intervalIntegrable_integrand {s τ : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ s + 1) {f : ℝ → X}
    (hf : ContinuousOn f (Icc s τ)) :
    IntervalIntegrable (fun r => D.S (τ - r) (D.B r (f r))) volume s τ := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hsτ]
  have hg : IntervalIntegrable (fun r => D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * A)
      volume s τ := ((intervalIntegrable_kernel τ s τ).const_mul (D.C₀ * D.β)).mul_const A
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hsτ] at hg
  refine Integrable.mono' hg ?_ ?_
  · exact ((D.continuousOn_integrand hτ (hf.mono Ico_subset_Icc_self)).mono
      Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun r hr => ?_)
    refine (D.norm_integrand_le hτ (Ioo_subset_Ico_self hr) f).trans ?_
    refine mul_le_mul_of_nonneg_left (hA r (Ioo_subset_Icc_self hr)) ?_
    have : 0 ≤ (τ - r) ^ (-(1 / 2 : ℝ)) := rpow_nonneg (by linarith [hr.2]) _
    exact mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg) this

/-- Exponentially weighted bound for the Volterra integral: if `‖f r‖ ≤ A e^{λ(r-s)}` on
`[s, τ]` then `‖vol f τ‖ ≤ C₀ β A (1/λ)^{1/2} Γ(1/2) e^{λ(τ-s)}`. -/
theorem norm_vol_le {s τ lam A : ℝ} (hlam : 0 < lam) (hsτ : s ≤ τ) (hτ : τ ≤ s + 1)
    {f : ℝ → X} (hfA : ∀ r ∈ Icc s τ, ‖f r‖ ≤ A * exp (lam * (r - s))) :
    ‖D.vol s f τ‖ ≤
      D.C₀ * D.β * A * ((1 / lam) ^ (1 / 2 : ℝ) * Gamma (1 / 2) * exp (lam * (τ - s))) := by
  have hA : 0 ≤ A := by
    have := hfA s ⟨le_rfl, hsτ⟩
    rw [sub_self, mul_zero, exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hK : 0 ≤ D.C₀ * D.β * A := mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg) hA
  have hg : IntervalIntegrable
      (fun r => D.C₀ * D.β * A * ((τ - r) ^ (-(1 / 2 : ℝ)) * exp (lam * (r - s)))) volume s τ :=
    (intervalIntegrable_kernel_mul_exp τ s lam s τ).const_mul _
  refine (norm_integral_le_of_norm_le hsτ ?_ hg).trans ?_
  · filter_upwards [ae_ne_real τ] with r hrτ hr
    have hr' : r ∈ Ico s τ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrτ⟩
    refine (D.norm_integrand_le hτ hr' f).trans ?_
    have hk : 0 ≤ (τ - r) ^ (-(1 / 2 : ℝ)) := rpow_nonneg (by linarith [hr'.2]) _
    calc D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * ‖f r‖
        ≤ D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * (A * exp (lam * (r - s))) :=
          mul_le_mul_of_nonneg_left (hfA r ⟨hr'.1, hr'.2.le⟩)
            (mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg) hk)
      _ = D.C₀ * D.β * A * ((τ - r) ^ (-(1 / 2 : ℝ)) * exp (lam * (r - s))) := by ring
  · rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_kernel_mul_exp_le hlam hsτ) hK

/-- The Volterra integral only depends on `f` on `[s, τ]`. -/
theorem vol_congr {s τ : ℝ} (hsτ : s ≤ τ) {f g : ℝ → X} (h : EqOn f g (Icc s τ)) :
    D.vol s f τ = D.vol s g τ := by
  unfold vol
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hsτ] at hr
  simp only [h hr]

theorem vol_add {s τ : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ s + 1) {f g : ℝ → X}
    (hf : ContinuousOn f (Icc s τ)) (hg : ContinuousOn g (Icc s τ)) :
    D.vol s (fun r => f r + g r) τ = D.vol s f τ + D.vol s g τ := by
  unfold vol
  simp only [map_add]
  exact intervalIntegral.integral_add (D.intervalIntegrable_integrand hsτ hτ hf)
    (D.intervalIntegrable_integrand hsτ hτ hg)

theorem vol_sub {s τ : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ s + 1) {f g : ℝ → X}
    (hf : ContinuousOn f (Icc s τ)) (hg : ContinuousOn g (Icc s τ)) :
    D.vol s (fun r => f r - g r) τ = D.vol s f τ - D.vol s g τ := by
  unfold vol
  simp only [map_sub]
  exact intervalIntegral.integral_sub (D.intervalIntegrable_integrand hsτ hτ hf)
    (D.intervalIntegrable_integrand hsτ hτ hg)

theorem vol_smul [SMulCommClass ℝ 𝕜 X] (s τ : ℝ) (c : 𝕜) (f : ℝ → X) :
    D.vol s (fun r => c • f r) τ = c • D.vol s f τ := by
  unfold vol
  simp only [map_smul]
  exact intervalIntegral.integral_smul c _

/-- Continuity in the upper limit: for `f` continuous on `[s, T]` with `T ≤ s + 1`,
`τ ↦ ∫ r in s..τ, S (τ - r) (B r (f r))` is continuous on `[s, T]`.  The proof substitutes
`σ = τ - r` and applies dominated convergence with the `τ`-independent majorant
`C₀ β A σ^{-1/2}`. -/
theorem continuousOn_vol {s T : ℝ} (hsT : s ≤ T) (hT : T ≤ s + 1) {f : ℝ → X}
    (hf : ContinuousOn f (Icc s T)) : ContinuousOn (D.vol s f) (Icc s T) := by
  set f' : ℝ → X := fun r => f (projIcc s T hsT r) with hf'
  have hf'c : Continuous f' :=
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun r => (projIcc s T hsT r).2)
  obtain ⟨A₀, hA₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  set A := max A₀ 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hA' : ∀ r, ‖f' r‖ ≤ A := fun r => (hA₀ _ (projIcc s T hsT r).2).trans (le_max_left _ _)
  set g : ℝ → Y := fun r => D.B r (f' r) with hgdef
  have hgc : Continuous g := continuousOn_univ.mp (D.continuousOn_B_apply hf'c.continuousOn)
  have hgA : ∀ r, ‖g r‖ ≤ D.β * A := fun r =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (D.norm_B_le r) (hA' r) (norm_nonneg _) D.β_nonneg)
  set F : ℝ → ℝ → X := fun τ => indicator {σ | σ ≤ τ - s} (fun σ => D.S σ (g (τ - σ)))
    with hFdef
  have hrep : ∀ τ ∈ Icc s T, D.vol s f τ = ∫ σ in (0 : ℝ)..1, F τ σ := by
    intro τ hτ
    have h1 : D.vol s f τ = ∫ r in s..τ, D.S (τ - r) (g r) := by
      unfold vol
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hτ.1] at hr
      simp only [hgdef, hf', projIcc_of_mem hsT ⟨hr.1, hr.2.trans hτ.2⟩]
    rw [h1]
    have h2 := intervalIntegral.integral_comp_sub_left
      (fun σ => D.S σ (g (τ - σ))) (a := s) (b := τ) τ
    simp only [sub_sub_cancel, sub_self] at h2
    rw [h2, hFdef]
    exact (intervalIntegral.integral_indicator ⟨by linarith [hτ.1], by linarith [hτ.2]⟩).symm
  have hScont : ∀ τ, ContinuousOn (fun σ => D.S σ (g (τ - σ))) (Ioc 0 1) := by
    intro τ
    refine continuousOn_clm_apply D.continuousOn_S ?_
      (hgc.comp (continuous_const.sub continuous_id)).continuousOn
    intro t₀ ht₀
    refine ⟨D.C₀ * (t₀ / 2) ^ (-(1 / 2 : ℝ)), ?_⟩
    filter_upwards [nhdsWithin_le_nhds (D.eventually_norm_S_le ht₀.1), self_mem_nhdsWithin]
      with t h1 h2
    exact h1 h2.2
  have hcont : Continuous (fun τ => ∫ σ in (0 : ℝ)..1, F τ σ) := by
    refine continuous_iff_continuousAt.mpr fun τ₀ => ?_
    refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun σ => D.C₀ * σ ^ (-(1 / 2 : ℝ)) * (D.β * A)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun τ => ?_
      rw [uIoc_of_le zero_le_one]
      exact ((hScont τ).aestronglyMeasurable measurableSet_Ioc).indicator
        (measurableSet_Iic (a := τ - s))
    · refine Eventually.of_forall fun τ => Eventually.of_forall fun σ hσ => ?_
      rw [uIoc_of_le zero_le_one] at hσ
      refine le_trans (norm_indicator_le_norm_self _ _) ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have hk : 0 ≤ D.C₀ * σ ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg D.C₀_nonneg (rpow_nonneg hσ.1.le _)
      exact mul_le_mul (D.norm_S_le σ hσ.1 hσ.2) (hgA _) (norm_nonneg _) hk
    · exact ((intervalIntegrable_rpow_neg_half 0 1).const_mul D.C₀).mul_const (D.β * A)
    · filter_upwards [ae_ne_real (τ₀ - s)] with σ hσne _
      rcases lt_or_gt_of_ne hσne with h | h
      · have hev : ∀ᶠ τ in 𝓝 τ₀, σ < τ - s :=
          continuousAt_const.eventually_lt (continuousAt_id.sub continuousAt_const) h
        have hc : ContinuousAt (fun τ => D.S σ (g (τ - σ))) τ₀ :=
          ((D.S σ).continuous.comp (hgc.comp (continuous_id.sub continuous_const))).continuousAt
        refine hc.congr (hev.mono fun τ hτ => ?_)
        simp only [hFdef]
        rw [indicator_of_mem (show σ ∈ {σ | σ ≤ τ - s} from hτ.le)]
      · have hev : ∀ᶠ τ in 𝓝 τ₀, τ - s < σ :=
          (continuousAt_id.sub continuousAt_const).eventually_lt continuousAt_const h
        refine (continuousAt_const (y := (0 : X))).congr (hev.mono fun τ hτ => ?_)
        simp only [hFdef]
        rw [indicator_of_notMem (show σ ∉ {σ | σ ≤ τ - s} from fun h' => by
          exact absurd h' (not_le.mpr hτ))]
  exact hcont.continuousOn.congr hrep

end Integral

end VolterraData

end UnforcedLeray.Infra.VolterraEvolution
