import UnforcedLeray.Infra.EvolutionContinuity.Abstract
import UnforcedLeray.Infra.VolterraEvolution

/-!
# Joint strong continuity of the Volterra evolution

`paper/main.tex`, lines 292-296: "Volterra iteration … constructs a jointly strongly continuous
evolution `E(τ,s)`". For `D : VolterraData 𝕜 X Y` with `D.Compatible` and `S₀ 0 = 1`, the
global evolution `E = D.evolution` of `UnforcedLeray.Infra.VolterraEvolution` is a
`ForwardEvolution` (`forwardEvolution_volterra`):

* evolution law: `VolterraData.evolution_comp`;
* strip bounds: from `‖E(τ,s)‖ ≤ M e^{(log M)(τ - s)}` (`VolterraData.norm_evolution_le`);
* continuity in `τ`: `VolterraData.continuousOn_evolution`;
* continuity at the diagonal (`tendsto_evolution_diag`): on the strip `s ≤ τ ≤ s + 1`,
  `‖E(τ,s) x - x‖ ≤ ‖E(τ,s) - S₀(τ-s)‖ ‖x‖ + ‖S₀(τ-s) x - x‖
     ≤ 2 C₀ β (2 M₀ e^λ) (τ-s)^{1/2} ‖x‖ + ‖S₀(τ-s) x - S₀(0) x‖`,
  by the short-time estimate `VolterraData.norm_stripEvolution_sub_apply_le` and strong
  continuity of `S₀` on `[0, 1]`.

Consequences (with the abstract results of `EvolutionContinuity/Abstract.lean`):

* (a) `continuousOn_evolution_snd`: `s ↦ E(τ,s) x` is continuous on `(-∞, τ]`;
* (b) `continuousOn_evolution_prod`: `(τ,s) ↦ E(τ,s) x` is continuous on `{s ≤ τ}`;
* (c) `continuousOn_evolution_comp`, `continuousOn_evolution_snd_comp`,
  `continuousOn_evolution_comp_periodic`, `continuousOn_evolution_snd_comp_periodic`:
  the same for `E(τ,s) Q(s) x` with `Q` strongly continuous (on a set `U`, or `P`-periodic and
  strongly continuous on `[0, P]`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Infra.EvolutionContinuity

open UnforcedLeray.Infra.VolterraEvolution

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X]
  [CompleteSpace X]

/-- **Strong continuity at the diagonal**, uniformly in the base point: `E(τ,s) x → x` as
`(τ,s) → (t,t)` with `s ≤ τ`. -/
theorem tendsto_evolution_diag {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) (t : ℝ) (x : X) :
    Tendsto (fun p : ℝ × ℝ => D.evolution p.1 p.2 x) (𝓝[{p : ℝ × ℝ | p.2 ≤ p.1}] (t, t))
      (𝓝 x) := by
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ≤ p.1} with hSdef
  -- the elapsed time `τ - s` tends to `0` within `[0, 1]`
  have hd0 : Tendsto (fun p : ℝ × ℝ => p.1 - p.2) (𝓝[S] (t, t)) (𝓝 0) := by
    have h : Tendsto (fun p : ℝ × ℝ => p.1 - p.2) (𝓝 (t, t)) (𝓝 (t - t)) :=
      (continuous_fst.sub continuous_snd).tendsto (t, t)
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun p : ℝ × ℝ => p.1 - p.2) (𝓝[S] (t, t)) (𝓝[Icc 0 1] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hd0, ?_⟩
    have h1 : ∀ᶠ p in 𝓝[S] (t, t), (fun p : ℝ × ℝ => p.1 - p.2) p < 1 :=
      hd0.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [h1, self_mem_nhdsWithin] with p hp hp'
    have hp1 : p.1 - p.2 < 1 := hp
    have hp2 : p.2 ≤ p.1 := hp'
    exact ⟨sub_nonneg.2 hp2, hp1.le⟩
  -- the free part: `S₀(τ - s) x → S₀(0) x = x`
  have hS : Tendsto (fun p : ℝ × ℝ => D.S₀ (p.1 - p.2) x) (𝓝[S] (t, t)) (𝓝 x) := by
    have h0 : ContinuousWithinAt (fun h => D.S₀ h x) (Icc 0 1) 0 :=
      D.continuousOn_S₀ x 0 ⟨le_rfl, zero_le_one⟩
    have h := h0.tendsto.comp hd
    rw [hS₀, one_apply_eq_self] at h
    exact h
  -- the Volterra correction: `‖E(τ,s) x - S₀(τ-s) x‖ ≤ c (τ-s)^{1/2} ‖x‖`
  have hc : Tendsto (fun p : ℝ × ℝ => D.evolution p.1 p.2 x - D.S₀ (p.1 - p.2) x)
      (𝓝[S] (t, t)) (𝓝 0) := by
    have hb : Tendsto (fun p : ℝ × ℝ => 2 * D.C₀ * D.β * D.stripBound *
        (p.1 - p.2) ^ (1 / 2 : ℝ) * ‖x‖) (𝓝[S] (t, t)) (𝓝 0) := by
      have h1 : Tendsto (fun h : ℝ => h ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
        have h := (Real.continuous_rpow_const (show (0 : ℝ) ≤ 1 / 2 by norm_num)).tendsto 0
        rwa [Real.zero_rpow (by norm_num)] at h
      have h3 := ((h1.comp hd0).const_mul (2 * D.C₀ * D.β * D.stripBound)).mul_const ‖x‖
      rw [mul_zero, zero_mul] at h3
      exact h3
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hd self_mem_nhdsWithin, self_mem_nhdsWithin] with p hp hp'
    have hp1 : p.1 - p.2 ≤ 1 := hp.2
    have hp2 : p.2 ≤ p.1 := hp'
    have hτ : p.1 ∈ Icc p.2 (p.2 + 1) := ⟨hp2, by linarith⟩
    rw [VolterraData.evolution_eq_stripEvolution hD hτ]
    exact D.norm_stripEvolution_sub_apply_le hτ x
  have h := hc.add hS
  simp only [sub_add_cancel, zero_add] at h
  exact h

/-- **The Volterra evolution is a `ForwardEvolution`** (compatible data, `S₀ 0 = 1`). -/
theorem forwardEvolution_volterra {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) : ForwardEvolution D.evolution where
  comp _ _ _ hsr hrτ := VolterraData.evolution_comp hD hsr hrτ
  bounded T := by
    refine ⟨D.evolutionBound * Real.exp (Real.log D.evolutionBound * T),
      fun s τ hsτ hτ => (D.norm_evolution_le hsτ).trans ?_⟩
    have h1 : 0 ≤ Real.log D.evolutionBound := Real.log_nonneg D.one_le_evolutionBound
    have h0 : 0 ≤ D.evolutionBound := zero_le_one.trans D.one_le_evolutionBound
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) h1)) h0
  continuousOn_fst s x := VolterraData.continuousOn_evolution hD s x
  tendsto_diag t x := tendsto_evolution_diag hD hS₀ t x

/-- `E(t,t) = 1` for the Volterra evolution. -/
theorem evolution_self {D : VolterraData 𝕜 X Y} (hD : D.Compatible) (hS₀ : D.S₀ 0 = 1)
    (t : ℝ) : D.evolution t t = 1 :=
  (forwardEvolution_volterra hD hS₀).self_eq t

/-- **(a)** For fixed `τ` and `x`, `s ↦ E(τ,s) x` is continuous on `(-∞, τ]`. -/
theorem continuousOn_evolution_snd {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => D.evolution τ s x) (Iic τ) :=
  (forwardEvolution_volterra hD hS₀).continuousOn_snd τ x

/-- **(b) Joint strong continuity** of `(τ,s) ↦ E(τ,s) x` on `{s ≤ τ}`. -/
theorem continuousOn_evolution_prod {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 x) {p : ℝ × ℝ | p.2 ≤ p.1} :=
  (forwardEvolution_volterra hD hS₀).continuousOn x

/-- **(c)** For `Q` strongly continuous on `U`, `(τ,s) ↦ E(τ,s) Q(s) x` is continuous on
`{s ≤ τ, s ∈ U}`. -/
theorem continuousOn_evolution_comp {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) {Q : ℝ → X →L[𝕜] X} {U : Set ℝ}
    (hQ : ∀ y, ContinuousOn (fun s => Q s y) U) (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (Q p.2 x))
      {p : ℝ × ℝ | p.2 ≤ p.1 ∧ p.2 ∈ U} :=
  (forwardEvolution_volterra hD hS₀).continuousOn_comp hQ x

/-- **(c), initial-time form.** `s ↦ E(τ,s) Q(s) x` is continuous on `(-∞, τ] ∩ U`. -/
theorem continuousOn_evolution_snd_comp {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) {Q : ℝ → X →L[𝕜] X} {U : Set ℝ}
    (hQ : ∀ y, ContinuousOn (fun s => Q s y) U) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => D.evolution τ s (Q s x)) (Iic τ ∩ U) :=
  (forwardEvolution_volterra hD hS₀).continuousOn_snd_comp hQ τ x

/-- **(c) for periodic families.** If `Q` is `P`-periodic and strongly continuous on `[0, P]`,
`(τ,s) ↦ E(τ,s) Q(s) x` is continuous on `{s ≤ τ}`. -/
theorem continuousOn_evolution_comp_periodic {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) {Q : ℝ → X →L[𝕜] X} {P : ℝ} (hP : 0 < P)
    (hper : ∀ t, Q (t + P) = Q t) (hc : ∀ y, ContinuousOn (fun t => Q t y) (Icc 0 P)) (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (Q p.2 x)) {p : ℝ × ℝ | p.2 ≤ p.1} :=
  (forwardEvolution_volterra hD hS₀).continuousOn_comp_periodic hP hper hc x

/-- **(c) for periodic families, initial-time form.** -/
theorem continuousOn_evolution_snd_comp_periodic {D : VolterraData 𝕜 X Y} (hD : D.Compatible)
    (hS₀ : D.S₀ 0 = 1) {Q : ℝ → X →L[𝕜] X} {P : ℝ} (hP : 0 < P)
    (hper : ∀ t, Q (t + P) = Q t) (hc : ∀ y, ContinuousOn (fun t => Q t y) (Icc 0 P))
    (τ : ℝ) (x : X) : ContinuousOn (fun s => D.evolution τ s (Q s x)) (Iic τ) :=
  (forwardEvolution_volterra hD hS₀).continuousOn_snd_comp_periodic hP hper hc τ x

end UnforcedLeray.Infra.EvolutionContinuity
