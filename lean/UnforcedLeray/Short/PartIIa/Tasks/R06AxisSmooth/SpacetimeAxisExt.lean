import UnforcedLeray.Lib.AxisymmetricB.FlatExtension
import UnforcedLeray.Units.B0185

/-!
# Part II-a, task `PartII-a:R06` helper: spacetime `C^k` and `C^∞` extension across `{t > 0} × axis`

Adapts `Axi.contDiff_of_tendsto_axis` and `Axi.contDiff_flat_extension`
(`Lib/AxisymmetricB/FlatExtension.lean`) from `Space` to the open positive-time half-space
`posTime = {z : ℝ × Space | 0 < z.1}` with singular set `posTimeAxis = {z | 0 < z.1 ∧ z.2 ∈ Axi.axis}`.

Main results:
1. `contDiffOn_posTime_of_tendsto_axis`: if `g : ℝ × Space → F` vanishes on `posTimeAxis`, is `C^k`
   on `posTimeOffAxis = {z | 0 < z.1 ∧ z.2 ∉ Axi.axis}`, and `‖iteratedFDeriv ℝ n g z‖ → 0` as
   `z → z₀ ∈ posTimeAxis` within `posTimeOffAxis` for all `n ≤ k`, then `ContDiffOn ℝ k g posTime`.
2. `contDiffOn_posTime_of_poly_bound`: if `‖iteratedFDeriv ℝ n g z‖ ≤ C * ϱ(z.2)` on every local
   positive-time cylinder `{t₀ / 2 < t < 2 t₀, |z₂| < M, 0 < ϱ < 1}` for `n ≤ k`, then
   `ContDiffOn ℝ k g posTime` (used for the order-`N` mean remainder velocity lift).
3. `contDiffOn_posTime_of_flat_bound`: if `‖iteratedFDeriv ℝ n g z‖ ≤ C / ϱ(z.2)^N * exp(-κ / ϱ(z.2)²)`
   on every local positive-time cylinder for every `n : ℕ`, then `ContDiffOn ℝ ∞ g posTime`
   (used for the fluctuation velocity and pressure lifts).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

universe u

namespace UnforcedLeray.Short.PartIIa

/-- The open positive-time half-space `{z : ℝ × Space | 0 < z.1}`. -/
def posTime : Set (ℝ × Space) := {z : ℝ × Space | 0 < z.1}

/-- Positive-time points off the symmetry axis. -/
def posTimeOffAxis : Set (ℝ × Space) := {z : ℝ × Space | 0 < z.1 ∧ z.2 ∉ Axi.axis}

/-- Positive-time points on the symmetry axis. -/
def posTimeAxis : Set (ℝ × Space) := {z : ℝ × Space | 0 < z.1 ∧ z.2 ∈ Axi.axis}

/-- Local positive-time cylindrical box off the axis around `(t₀, y₀)`:
`t₀ / 2 < t < 2 t₀`, `|x₂| < M`, `0 < ϱ(x) < 1`. -/
def localCylBox (t₀ M : ℝ) : Set (ℝ × Space) :=
  {z : ℝ × Space | t₀ / 2 < z.1 ∧ z.1 < 2 * t₀ ∧ |z.2 2| < M ∧ z.2 ∉ Axi.axis ∧ Axi.ϱ z.2 < 1}

theorem isOpen_posTime : IsOpen posTime :=
  isOpen_lt continuous_const continuous_fst

theorem isOpen_posTimeOffAxis : IsOpen posTimeOffAxis :=
  isOpen_posTime.inter (Axi.isOpen_compl_axis.preimage continuous_snd)

theorem posTimeOffAxis_subset_posTime : posTimeOffAxis ⊆ posTime :=
  fun _ hz => hz.1

theorem posTimeAxis_subset_posTime : posTimeAxis ⊆ posTime :=
  fun _ hz => hz.1

/-- The segment in `ℝ × Space` from `z ∈ posTimeOffAxis` to `z₀ ∈ posTimeAxis` stays in
`posTimeOffAxis` for `t ∈ [0, 1)`. -/
theorem segment_mem_posTimeOffAxis {z₀ z : ℝ × Space} (hz₀ : z₀ ∈ posTimeAxis)
    (hz : z ∈ posTimeOffAxis) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    z + s • (z₀ - z) ∈ posTimeOffAxis := by
  refine ⟨?_, ?_⟩
  · change 0 < z.1 + s * (z₀.1 - z.1)
    have h1 : z.1 + s * (z₀.1 - z.1) = (1 - s) * z.1 + s * z₀.1 := by ring
    rw [h1]
    have hpos1 : 0 < (1 - s) * z.1 := mul_pos (by linarith) hz.1
    have hpos2 : 0 ≤ s * z₀.1 := mul_nonneg hs0 hz₀.1.le
    linarith
  · change z.2 + s • (z₀.2 - z.2) ∉ Axi.axis
    exact Axi.add_smul_sub_not_mem_axis hz₀.2 hz.2 (ne_of_lt hs1)

section General

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- Continuity across `posTimeAxis` on the open set `posTime`. -/
theorem continuousAt_posTime_of_tendsto_axis {g : ℝ × Space → F}
    (h0 : ∀ z ∈ posTimeAxis, g z = 0)
    (hc : ContinuousOn g posTimeOffAxis)
    (ht : ∀ z₀ ∈ posTimeAxis, Tendsto g (𝓝[posTimeOffAxis] z₀) (𝓝 0))
    {z : ℝ × Space} (hz : z ∈ posTime) :
    ContinuousAt g z := by
  by_cases hza : z.2 ∈ Axi.axis
  · have hz_ax : z ∈ posTimeAxis := ⟨hz, hza⟩
    rw [ContinuousAt, h0 z hz_ax]
    set S₁ : Set (ℝ × Space) := {w | w.2 ∈ Axi.axis}
    set S₂ : Set (ℝ × Space) := {w | w.2 ∉ Axi.axis}
    have h1 : Tendsto g (𝓝[S₁] z) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards [isOpen_posTime.mem_nhds hz] with w hw hwa
      exact (h0 w ⟨hw, hwa⟩).symm
    have h2 : Tendsto g (𝓝[S₂] z) (𝓝 0) := by
      have heq : 𝓝[posTimeOffAxis] z = 𝓝[S₂] z := by
        have hinter : posTimeOffAxis = posTime ∩ S₂ := rfl
        rw [hinter]
        exact nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (isOpen_posTime.mem_nhds hz))
      rw [← heq]
      exact ht z hz_ax
    have h3 := h1.sup h2
    have hunion : S₁ ∪ S₂ = univ := by
      ext w; simp [S₁, S₂, em]
    rwa [← nhdsWithin_union, hunion, nhdsWithin_univ] at h3
  · exact hc.continuousAt (isOpen_posTimeOffAxis.mem_nhds ⟨hz, hza⟩)

/-- The Fréchet derivative on `posTimeAxis` vanishes when `fderiv ℝ g` tends to `0` at the axis. -/
theorem hasFDerivAt_zero_posTime_of_tendsto_axis {g : ℝ × Space → F}
    (hcont : ∀ z ∈ posTime, ContinuousAt g z)
    (h0 : ∀ z ∈ posTimeAxis, g z = 0)
    (hd : DifferentiableOn ℝ g posTimeOffAxis)
    {z₀ : ℝ × Space} (hz₀ : z₀ ∈ posTimeAxis)
    (ht : Tendsto (fun z => ‖fderiv ℝ g z‖) (𝓝[posTimeOffAxis] z₀) (𝓝 0)) :
    HasFDerivAt g (0 : (ℝ × Space) →L[ℝ] F) z₀ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hev : ∀ᶠ z in 𝓝[posTimeOffAxis] z₀, ‖fderiv ℝ g z‖ ≤ ε :=
    ((tendsto_order.1 ht).2 ε hε).mono fun z hz => hz.le
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₁, hδ₁, hball⟩ := hev
  set δ := min δ₁ (z₀.1 / 2)
  have hδ : 0 < δ := lt_min hδ₁ (half_pos hz₀.1)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hz_pos : z ∈ posTime := by
    change 0 < z.1
    have hz₀1 : 0 < z₀.1 := hz₀.1
    have hdist1 : |z.1 - z₀.1| ≤ dist z z₀ := by
      rw [← Real.dist_eq, Prod.dist_eq]
      exact le_max_left _ _
    have hlt : |z.1 - z₀.1| < z₀.1 / 2 :=
      lt_of_le_of_lt hdist1 (lt_of_lt_of_le hz (min_le_right _ _))
    linarith [(abs_lt.1 hlt).1]
  simp only [h0 z₀ hz₀, sub_zero, zero_apply]
  by_cases hza : z.2 ∈ Axi.axis
  · rw [h0 z ⟨hz_pos, hza⟩, norm_zero]
    positivity
  · have hz_off : z ∈ posTimeOffAxis := ⟨hz_pos, hza⟩
    set φ : ℝ → F := fun s => g (z + s • (z₀ - z)) with hφ
    have hline : Continuous fun s : ℝ => z + s • (z₀ - z) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hφc : ContinuousOn φ (Icc 0 1) := by
      intro s hs
      have hseg_pos : z + s • (z₀ - z) ∈ posTime := by
        rcases eq_or_lt_of_le hs.2 with rfl | hs1
        · simp only [one_smul, add_sub_cancel]
          exact hz₀.1
        · exact (segment_mem_posTimeOffAxis hz₀ hz_off hs.1 hs1).1
      exact ContinuousAt.comp_continuousWithinAt (g := g) (f := fun s => z + s • (z₀ - z))
        (hcont _ hseg_pos) hline.continuousWithinAt
    have hφd : ∀ s ∈ Ico (0 : ℝ) 1,
        HasDerivWithinAt φ (fderiv ℝ g (z + s • (z₀ - z)) (z₀ - z)) (Ici s) s := by
      intro s hs
      have hw : z + s • (z₀ - z) ∈ posTimeOffAxis :=
        segment_mem_posTimeOffAxis hz₀ hz_off hs.1 hs.2
      have hgd : HasFDerivAt g (fderiv ℝ g (z + s • (z₀ - z))) (z + s • (z₀ - z)) :=
        (hd.differentiableAt (isOpen_posTimeOffAxis.mem_nhds hw)).hasFDerivAt
      have hl : HasDerivAt (fun r : ℝ => z + r • (z₀ - z)) (z₀ - z) s := by
        simpa using ((hasDerivAt_id s).smul_const (z₀ - z)).const_add z
      exact (hgd.comp_hasDerivAt s hl).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
        ‖fderiv ℝ g (z + s • (z₀ - z)) (z₀ - z)‖ ≤ ε * ‖z - z₀‖ := by
      intro s hs
      have hw : z + s • (z₀ - z) ∈ posTimeOffAxis :=
        segment_mem_posTimeOffAxis hz₀ hz_off hs.1 hs.2
      have hdist : dist (z + s • (z₀ - z)) z₀ < δ₁ := by
        rw [dist_eq_norm]
        have e : z + s • (z₀ - z) - z₀ = (1 - s) • (z - z₀) := by
          rw [sub_smul, one_smul, smul_sub, smul_sub]
          abel
        rw [e, norm_smul, Real.norm_of_nonneg (by linarith [hs.2])]
        calc (1 - s) * ‖z - z₀‖ ≤ 1 * ‖z - z₀‖ :=
              mul_le_mul_of_nonneg_right (by linarith [hs.1]) (norm_nonneg _)
          _ = dist z z₀ := by rw [one_mul, dist_eq_norm]
          _ < δ := hz
          _ ≤ δ₁ := min_le_left _ _
      calc ‖fderiv ℝ g (z + s • (z₀ - z)) (z₀ - z)‖
          ≤ ‖fderiv ℝ g (z + s • (z₀ - z))‖ * ‖z₀ - z‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * ‖z - z₀‖ := by
          rw [norm_sub_rev z₀ z]
          exact mul_le_mul_of_nonneg_right (hball hdist hw) (norm_nonneg _)
    have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hφc hφd hbound 1
      ⟨zero_le_one, le_rfl⟩
    have e1 : φ 1 = 0 := by
      simp only [hφ, one_smul, add_sub_cancel]
      exact h0 z₀ hz₀
    have e0 : φ 0 = g z := by simp only [hφ, zero_smul, add_zero]
    rw [e1, e0, zero_sub, norm_neg, sub_zero, mul_one] at hmvt
    exact hmvt

end General

/-- **Spacetime `C^k` smoothness across `{t > 0} × axis`.** -/
theorem contDiffOn_posTime_of_tendsto_axis : ∀ (k : ℕ) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ × Space → F},
    (∀ z ∈ posTimeAxis, g z = 0) →
    ContDiffOn ℝ k g posTimeOffAxis →
    (∀ n ≤ k, ∀ z₀ ∈ posTimeAxis,
      Tendsto (fun z => ‖iteratedFDeriv ℝ n g z‖) (𝓝[posTimeOffAxis] z₀) (𝓝 0)) →
    ContDiffOn ℝ k g posTime := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g h0 hc ht
    rw [Nat.cast_zero, contDiffOn_zero]
    intro z hz
    refine (continuousAt_posTime_of_tendsto_axis h0 hc.continuousOn (fun z₀ hz₀ => ?_) hz).continuousWithinAt
    have := ht 0 le_rfl z₀ hz₀
    simp only [norm_iteratedFDeriv_zero] at this
    exact tendsto_zero_iff_norm_tendsto_zero.2 this
  | succ k ih =>
    intro F _ _ g h0 hc ht
    have hcont : ∀ z ∈ posTime, ContinuousAt g z := by
      intro z hz
      refine continuousAt_posTime_of_tendsto_axis h0 hc.continuousOn (fun z₀ hz₀ => ?_) hz
      have := ht 0 (Nat.zero_le _) z₀ hz₀
      simp only [norm_iteratedFDeriv_zero] at this
      exact tendsto_zero_iff_norm_tendsto_zero.2 this
    have hdiff : DifferentiableOn ℝ g posTimeOffAxis := hc.differentiableOn (by simp)
    have hfd0 : ∀ z₀ ∈ posTimeAxis, HasFDerivAt g (0 : (ℝ × Space) →L[ℝ] F) z₀ := by
      intro z₀ hz₀
      refine hasFDerivAt_zero_posTime_of_tendsto_axis hcont h0 hdiff hz₀ ?_
      have := ht 1 (by omega) z₀ hz₀
      simpa only [norm_iteratedFDeriv_one] using this
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_posTime]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      by_cases hza : z.2 ∈ Axi.axis
      · exact (hfd0 z ⟨hz, hza⟩).differentiableAt.differentiableWithinAt
      · exact (hdiff.differentiableAt (isOpen_posTimeOffAxis.mem_nhds ⟨hz, hza⟩)).differentiableWithinAt
    · simp
    · refine ih (g := fderiv ℝ g) (fun z hz => (hfd0 z hz).fderiv) ?_ ?_
      · exact hc.fderiv_of_isOpen isOpen_posTimeOffAxis (by rw [hcast])
      · intro n hn z₀ hz₀
        have := ht (n + 1) (by omega) z₀ hz₀
        simpa only [norm_iteratedFDeriv_fderiv] using this

/-- Every point `z₀ ∈ posTimeAxis` has `localCylBox z₀.1 (|z₀.2 2| + 1)` in `𝓝[posTimeOffAxis] z₀`. -/
theorem eventually_mem_localCylBox {z₀ : ℝ × Space} (hz₀ : z₀ ∈ posTimeAxis) :
    ∀ᶠ z in 𝓝[posTimeOffAxis] z₀, z ∈ localCylBox z₀.1 (|z₀.2 2| + 1) := by
  have ht0 : 0 < z₀.1 := hz₀.1
  have hρ0 : Axi.ϱ z₀.2 = 0 := (Axi.mem_axis_iff z₀.2).1 hz₀.2
  have h1 : ∀ᶠ z : ℝ × Space in 𝓝 z₀, z₀.1 / 2 < z.1 :=
    continuousAt_const.eventually_lt continuous_fst.continuousAt (half_lt_self ht0)
  have h2 : ∀ᶠ z : ℝ × Space in 𝓝 z₀, z.1 < 2 * z₀.1 :=
    continuous_fst.continuousAt.eventually_lt continuousAt_const (by linarith)
  have h3 : ∀ᶠ z : ℝ × Space in 𝓝 z₀, |z.2 2| < |z₀.2 2| + 1 := by
    have hc : Continuous fun z : ℝ × Space => |z.2 2| := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by linarith)
  have h4 : ∀ᶠ z : ℝ × Space in 𝓝 z₀, Axi.ϱ z.2 < 1 := by
    have hc : Continuous fun z : ℝ × Space => Axi.ϱ z.2 := Axi.continuous_ϱ.comp continuous_snd
    exact hc.continuousAt.eventually_lt continuousAt_const (by rw [hρ0]; exact one_pos)
  filter_upwards [(h1.and (h2.and (h3.and h4))).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z ⟨ht1, ht2, hz2, hρ⟩ hz_off
  exact ⟨ht1, ht2, hz2, hz_off.2, hρ⟩

/-- **Polynomial axis extension criterion** (for the order-`N` mean remainder): if `g` vanishes on
`posTimeAxis`, is `C^k` on `posTimeOffAxis`, and `‖iteratedFDeriv ℝ n g z‖ ≤ C * ϱ(z.2)` on every
`localCylBox t₀ M` for `n ≤ k`, then `ContDiffOn ℝ k g posTime`. -/
theorem contDiffOn_posTime_of_poly_bound {k : ℕ} {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ × Space → F}
    (h0 : ∀ z ∈ posTimeAxis, g z = 0)
    (hc : ContDiffOn ℝ k g posTimeOffAxis)
    (hpoly : ∀ n ≤ k, ∀ t₀ M : ℝ, 0 < t₀ → 0 < M → ∃ C : ℝ,
      ∀ z ∈ localCylBox t₀ M, ‖iteratedFDeriv ℝ n g z‖ ≤ C * Axi.ϱ z.2) :
    ContDiffOn ℝ k g posTime := by
  refine contDiffOn_posTime_of_tendsto_axis k h0 hc fun n hn z₀ hz₀ => ?_
  have hM : 0 < |z₀.2 2| + 1 := by positivity
  obtain ⟨C, hC⟩ := hpoly n hn z₀.1 (|z₀.2 2| + 1) hz₀.1 hM
  have hρ0 : Axi.ϱ z₀.2 = 0 := (Axi.mem_axis_iff z₀.2).1 hz₀.2
  have hlim : Tendsto (fun z : ℝ × Space => C * Axi.ϱ z.2) (𝓝[posTimeOffAxis] z₀) (𝓝 0) := by
    have hc_rho : Continuous fun z : ℝ × Space => C * Axi.ϱ z.2 :=
      continuous_const.mul (Axi.continuous_ϱ.comp continuous_snd)
    have h0' := hc_rho.tendsto z₀
    rw [hρ0, mul_zero] at h0'
    exact h0'.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_mem_localCylBox hz₀] with z hz
  exact hC z hz

/-- **Exponentially flat axis extension criterion** (for the fluctuation velocity and pressure):
if `g` vanishes on `posTimeAxis`, is `C^∞` on `posTimeOffAxis`, and on every `localCylBox t₀ M`
has `‖iteratedFDeriv ℝ n g z‖ ≤ C / ϱ(z.2)^N * exp(-κ / ϱ(z.2)²)` for all `n : ℕ`, then
`ContDiffOn ℝ ∞ g posTime`. -/
theorem contDiffOn_posTime_of_flat_bound {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ × Space → F}
    (h0 : ∀ z ∈ posTimeAxis, g z = 0)
    (hc : ContDiffOn ℝ ∞ g posTimeOffAxis)
    (hflat : ∀ n : ℕ, ∀ t₀ M : ℝ, 0 < t₀ → 0 < M → ∃ (C : ℝ) (N : ℕ) (κ : ℝ), 0 < κ ∧
      ∀ z ∈ localCylBox t₀ M,
        ‖iteratedFDeriv ℝ n g z‖ ≤ C / Axi.ϱ z.2 ^ N * Real.exp (-κ / Axi.ϱ z.2 ^ 2)) :
    ContDiffOn ℝ ∞ g posTime := by
  rw [contDiffOn_infty]
  intro k
  refine contDiffOn_posTime_of_poly_bound h0 (hc.of_le (by exact_mod_cast le_top)) ?_
  intro n _ t₀ M ht₀ hM
  obtain ⟨C, N, κ, hκ, hbd⟩ := hflat n t₀ M ht₀ hM
  refine ⟨|C| * ((N + 1).factorial / κ ^ (N + 1)), fun z hz => ?_⟩
  have hρ : 0 < Axi.ϱ z.2 := Axi.ϱ_pos hz.2.2.2.1
  have hρ1 : Axi.ϱ z.2 ≤ 1 := hz.2.2.2.2.le
  have hexp := Axi.inv_pow_mul_exp_le hρ hκ N
  have hpow : Axi.ϱ z.2 ^ (N + 2) ≤ Axi.ϱ z.2 := by
    calc Axi.ϱ z.2 ^ (N + 2) ≤ Axi.ϱ z.2 ^ 1 :=
          pow_le_pow_of_le_one hρ.le hρ1 (by omega)
      _ = Axi.ϱ z.2 := pow_one _
  calc ‖iteratedFDeriv ℝ n g z‖
      ≤ C / Axi.ϱ z.2 ^ N * Real.exp (-κ / Axi.ϱ z.2 ^ 2) := hbd z hz
    _ ≤ |C| * ((Axi.ϱ z.2 ^ N)⁻¹ * Real.exp (-κ / Axi.ϱ z.2 ^ 2)) := by
        rw [div_eq_mul_inv, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((N + 1).factorial / κ ^ (N + 1) * Axi.ϱ z.2 ^ (N + 2)) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg C)
    _ ≤ |C| * ((N + 1).factorial / κ ^ (N + 1) * Axi.ϱ z.2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (abs_nonneg C)
    _ = |C| * ((N + 1).factorial / κ ^ (N + 1)) * Axi.ϱ z.2 := by ring

/-! ### Off-axis spacetime smoothness of `liftVelocity` and `liftPressure` -/

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185

/-- `z ↦ ϱ(z.2)` is `C^∞` on `posTimeOffAxis`. -/
theorem contDiffOn_rho_posTimeOffAxis :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Axi.ϱ z.2) posTimeOffAxis :=
  Axi.contDiffOn_ϱ.comp contDiff_snd.contDiffOn fun _ hz => hz.2

/-- `z ↦ (ϱ(z.2))⁻¹` is `C^∞` on `posTimeOffAxis`. -/
theorem contDiffOn_inv_rho_posTimeOffAxis :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => (Axi.ϱ z.2)⁻¹) posTimeOffAxis :=
  contDiffOn_rho_posTimeOffAxis.inv fun _ hz => (Axi.ϱ_pos hz.2).ne'

/-- `z ↦ radialScale R (ϱ(z.2)) = R / ϱ(z.2)` is `C^∞` on `posTimeOffAxis`. -/
theorem contDiffOn_radialScale_posTimeOffAxis (R : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => radialScale R (Axi.ϱ z.2)) posTimeOffAxis := by
  have h := contDiffOn_const (c := R).mul contDiffOn_inv_rho_posTimeOffAxis
  exact h.congr fun _ _ => by simp [radialScale, div_eq_mul_inv]

/-- `z ↦ eR(z.2)` is `C^∞` on `posTimeOffAxis`. -/
theorem contDiffOn_eR_posTimeOffAxis :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Axi.eR z.2) posTimeOffAxis :=
  Axi.contDiffOn_eR.comp contDiff_snd.contDiffOn fun _ hz => hz.2

/-- The spacetime chart map `z = (t, x) ↦ profileChart R (ϱ x) (x 2) t` is `C^∞` on `posTimeOffAxis`. -/
theorem contDiffOn_spacetimeChart {R : ℝ} (hR : R ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => profileChart R (Axi.ϱ z.2) (z.2 2) z.1)
      posTimeOffAxis := by
  have hρ := contDiffOn_rho_posTimeOffAxis
  have ha := contDiffOn_radialScale_posTimeOffAxis R
  have hz2 : ContDiffOn ℝ ∞ (fun z : ℝ × Space => z.2 2) posTimeOffAxis := by
    have hm : ContDiff ℝ ∞ (fun z : ℝ × Space => z.2 2) := by fun_prop
    exact hm.contDiffOn
  have ht : ContDiffOn ℝ ∞ (fun z : ℝ × Space => z.1) posTimeOffAxis :=
    contDiff_fst.contDiffOn
  have hq : ContDiffOn ℝ ∞ (fun z : ℝ × Space => R * Real.log (Axi.ϱ z.2 / R)) posTimeOffAxis :=
    contDiffOn_const.mul ((hρ.div_const R).log fun _ hz =>
      div_ne_zero (Axi.ϱ_pos hz.2).ne' hR)
  have hη : ContDiffOn ℝ ∞ (fun z : ℝ × Space => radialScale R (Axi.ϱ z.2) * z.2 2)
      posTimeOffAxis :=
    ha.mul hz2
  have hs : ContDiffOn ℝ ∞ (fun z : ℝ × Space => radialScale R (Axi.ϱ z.2) ^ 2 * z.1)
      posTimeOffAxis :=
    (ha.pow 2).mul ht
  exact hq.prodMk (hη.prodMk hs)

/-- `spacetimeChart` maps `posTimeOffAxis` into `ageDomain = {y | 0 < y.2.2}`. -/
theorem mapsTo_spacetimeChart {R : ℝ} (hR : R ≠ 0) :
    MapsTo (fun z : ℝ × Space => profileChart R (Axi.ϱ z.2) (z.2 2) z.1)
      posTimeOffAxis ageDomain := by
  intro z hz
  exact mapsTo_profileChart_mer R z.1 hR hz.1 (x := (Axi.ϱ z.2, z.2 2))
    ⟨Axi.ϱ_pos hz.2, trivial⟩

/-- If `p` is `C^∞` on `ageDomain` and `R ≠ 0`, then `z ↦ liftPressure R p z.1 z.2` is `C^∞` on
`posTimeOffAxis`. -/
theorem contDiffOn_liftPressure_offAxis {R : ℝ} (hR : R ≠ 0) {p : ProfilePoint → ℝ}
    (hp : ContDiffOn ℝ ∞ p ageDomain) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => liftPressure R p z.1 z.2) posTimeOffAxis := by
  have ha := contDiffOn_radialScale_posTimeOffAxis R
  have hc := hp.comp (contDiffOn_spacetimeChart hR) (mapsTo_spacetimeChart hR)
  exact (ha.pow 2).mul hc

/-- If `ψ` is `C^∞` on `ageDomain` and `R ≠ 0`, then `z ↦ liftVelocity R ψ z.1 z.2` is `C^∞` on
`posTimeOffAxis`. -/
theorem contDiffOn_liftVelocity_offAxis {R : ℝ} (hR : R ≠ 0) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => liftVelocity R ψ z.1 z.2) posTimeOffAxis := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ ψ) ageDomain :=
    hψ.fderiv_of_isOpen isOpen_ageDomain (m := ∞) (by simp)
  have hq : ContDiffOn ℝ ∞ (partialQ ψ) ageDomain := hD.clm_apply contDiffOn_const
  have he : ContDiffOn ℝ ∞ (partialEta ψ) ageDomain := hD.clm_apply contDiffOn_const
  have hs : ContDiffOn ℝ ∞ (partialAge ψ) ageDomain := hD.clm_apply contDiffOn_const
  have hη : ContDiffOn ℝ ∞ (fun y : ProfilePoint => y.2.1) ageDomain :=
    contDiff_snd.fst.contDiffOn
  have hσ : ContDiffOn ℝ ∞ (fun y : ProfilePoint => y.2.2) ageDomain :=
    contDiff_snd.snd.contDiffOn
  have hK : ContDiffOn ℝ ∞ (ageOperator ψ) ageDomain :=
    (hη.mul he).add ((contDiffOn_const.mul hσ).mul hs)
  have hv1 : ContDiffOn ℝ ∞ (streamV1 ψ) ageDomain := he.neg
  have hax : ContDiffOn ℝ ∞ (axialProfile R ψ) ageDomain :=
    hq.add (contDiffOn_const.mul (hψ.sub hK))
  have ha := contDiffOn_radialScale_posTimeOffAxis R
  have hch := contDiffOn_spacetimeChart hR
  have hm := mapsTo_spacetimeChart hR
  have hur : ContDiffOn ℝ ∞ (fun z : ℝ × Space => liftUr R ψ (Axi.ϱ z.2) (z.2 2) z.1)
      posTimeOffAxis := by
    have h := ha.mul (hv1.comp hch hm)
    exact h.congr fun z _ => liftUr_apply R ψ (Axi.ϱ z.2) (z.2 2) z.1
  have huz : ContDiffOn ℝ ∞ (fun z : ℝ × Space => liftUz R ψ (Axi.ϱ z.2) (z.2 2) z.1)
      posTimeOffAxis := by
    have h := ha.mul (hax.comp hch hm)
    exact h.congr fun z _ => liftUz_apply R ψ (Axi.ϱ z.2) (z.2 2) z.1
  have hvel := (hur.smul contDiffOn_eR_posTimeOffAxis).add
    (huz.smul (contDiffOn_const (c := Axi.e3)))
  exact hvel.congr fun z _ => liftVelocity_apply R ψ z.1 z.2

end UnforcedLeray.Short.PartIIa
