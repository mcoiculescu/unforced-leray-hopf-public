import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits uniform on compact parameter sets (INF29, target T29.4)


§5, Level 4, target T29.4; bypass B12 (ζ-free envelopes instead of compactness arguments).

* `tendstoUniformlyOn_integral_of_envelope`: if `‖F_n(p, x) - G(p, x)‖ ≤ h_n(x)` for all `p` in
  the parameter set, with `h_n → 0` pointwise and `|h_n| ≤ H` integrable, then
  `∫ F_n(p, ·) → ∫ G(p, ·)` uniformly in `p` (B0137 tex 1917–1941, B0379 tex 6922–6933, B0835
  tex 12335–12342, B0868/B0873 tex 12647–12671 and 13086–13131). The filter is any countably
  generated filter, in particular `𝓝[>] 0` in `ν`.
* `tendstoUniformlyOn_of_continuousOn_Icc_prod`: the Heine–Cantor alternative of B12, when the
  family extends jointly continuously to `ν = 0` on `[0, ν₀] × K` with `K` compact.
* `tendsto_sSup_norm_sub_of_tendstoUniformlyOn`: the modulus
  `ω(ν) = sup_{p ∈ K} ‖F_ν(p) - G(p)‖` tends to zero (B0887 tex 13424–13455: `ω_A`, `ω_D` and
  `ω_can → 0`, "no rate is asserted").

Junk values. Every Bochner integral in `tendstoUniformlyOn_integral_of_envelope` is of an
integrable function: `G p` is assumed integrable (`hG`), and `F n p` eventually integrable
(`hF`). The real `sSup` in `tendsto_sSup_norm_sub_of_tendstoUniformlyOn` is only used where the
set is bounded (eventually below `ε`); for an empty `K` it is `sSup ∅ = 0`, consistent with
the claim.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Budget

/-- **Uniform convergence of parametric integrals through a parameter-free envelope** (T29.4,
bypass B12). -/
theorem tendstoUniformlyOn_integral_of_envelope {ι P α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter ι}
    [l.IsCountablyGenerated] {K : Set P} {F : ι → P → α → E} {G : P → α → E}
    {h : ι → α → ℝ} {H : α → ℝ} (hH : Integrable H μ) (hG : ∀ p ∈ K, Integrable (G p) μ)
    (hF : ∀ᶠ n in l, ∀ p ∈ K, Integrable (F n p) μ ∧ ∀ᵐ x ∂μ, ‖F n p x - G p x‖ ≤ h n x)
    (hh : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) l (𝓝 0))
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂μ, |h n x| ≤ H x)
    (hmeas : ∀ᶠ n in l, AEStronglyMeasurable (h n) μ) :
    TendstoUniformlyOn (fun n p => ∫ x, F n p x ∂μ) (fun p => ∫ x, G p x ∂μ) l K := by
  have hdom' : ∀ᶠ n in l, ∀ᵐ x ∂μ, ‖h n x‖ ≤ H x :=
    hdom.mono fun n hn => hn.mono fun x hx => by rwa [Real.norm_eq_abs]
  have hlim : Tendsto (fun n => ∫ x, h n x ∂μ) l (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence H hmeas hdom' hH hh
    simpa using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev := (Metric.tendsto_nhds.1 hlim) ε hε
  filter_upwards [hev, hF, hdom', hmeas] with n hn hFn hdomn hmeasn p hp
  obtain ⟨hFi, hFh⟩ := hFn p hp
  have hhi : Integrable (h n) μ := hH.mono' hmeasn hdomn
  rw [dist_eq_norm, ← integral_sub (hG p hp) hFi]
  have hle : ‖∫ x, (G p x - F n p x) ∂μ‖ ≤ ∫ x, h n x ∂μ :=
    norm_integral_le_of_norm_le hhi (hFh.mono fun x hx => by rwa [norm_sub_rev])
  rw [Real.dist_eq, sub_zero] at hn
  exact hle.trans_lt ((le_abs_self _).trans_lt hn)

/-- **Heine–Cantor alternative** (T29.4): a family jointly continuous on `[0, ν₀] × K`, `K`
compact, converges to its value at `ν = 0` uniformly on `K` as `ν → 0⁺`. -/
theorem tendstoUniformlyOn_of_continuousOn_Icc_prod {P E : Type*} [PseudoMetricSpace P]
    [PseudoMetricSpace E] {K : Set P} (hK : IsCompact K) {f : ℝ → P → E} {ν₀ : ℝ}
    (hν₀ : 0 < ν₀) (h : ContinuousOn (Function.uncurry f) (Icc 0 ν₀ ×ˢ K)) :
    TendstoUniformlyOn f (f 0) (𝓝[>] 0) K := by
  have hUC := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous h
  rw [Metric.uniformContinuousOn_iff] at hUC
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hUC ε hε
  filter_upwards [Ioo_mem_nhdsGT (lt_min hν₀ hδ)] with ν hν p hp
  have h0 : ((0 : ℝ), p) ∈ Icc 0 ν₀ ×ˢ K := ⟨left_mem_Icc.2 hν₀.le, hp⟩
  have h1 : (ν, p) ∈ Icc 0 ν₀ ×ˢ K := ⟨⟨hν.1.le, hν.2.le.trans (min_le_left _ _)⟩, hp⟩
  have hd : dist ((0 : ℝ), p) (ν, p) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hν.1]
    exact max_lt (hν.2.trans_le (min_le_right _ _)) hδ
  exact hδ' _ h0 _ h1 hd

/-- **The uniform modulus tends to zero** (T29.4; B0887 tex 13424–13455). -/
theorem tendsto_sSup_norm_sub_of_tendstoUniformlyOn {ι P E : Type*} [SeminormedAddCommGroup E]
    {l : Filter ι} {K : Set P} {F : ι → P → E} {G : P → E} (h : TendstoUniformlyOn F G l K) :
    Tendsto (fun n => sSup ((fun p => ‖F n p - G p‖) '' K)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := Metric.tendstoUniformlyOn_iff.1 h (ε / 2) (by linarith)
  filter_upwards [hev] with n hn
  have hle : sSup ((fun p => ‖F n p - G p‖) '' K) ≤ ε / 2 := by
    refine Real.sSup_le ?_ (by linarith)
    rintro _ ⟨p, hp, rfl⟩
    have := hn p hp
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le
  have hge : 0 ≤ sSup ((fun p => ‖F n p - G p‖) '' K) := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨p, _, rfl⟩
    exact norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hge]
  linarith

/-- The composite modulus `ω_can = ω_A + ω_D + P δ_base` of B0887 tends to zero once each
summand does. -/
theorem tendsto_add_add_nhds_zero {ι : Type*} {l : Filter ι} {ωA ωD r : ι → ℝ}
    (hA : Tendsto ωA l (𝓝 0)) (hD : Tendsto ωD l (𝓝 0)) (hr : Tendsto r l (𝓝 0)) :
    Tendsto (fun n => ωA n + ωD n + r n) l (𝓝 0) := by
  simpa using (hA.add hD).add hr

end UnforcedLeray.Budget
