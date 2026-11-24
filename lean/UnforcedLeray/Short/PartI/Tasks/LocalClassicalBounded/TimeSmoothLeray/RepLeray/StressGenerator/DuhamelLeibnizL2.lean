import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4

/-!
# Part I, task `PartI:T02/1/4/6/4`, leaf 4: the Leibniz rule for the Duhamel integral

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `duhamelLeibnizL2 : DuhamelLeibnizL2` (leaf 4 of `Sub/T02_1_4_6_4.lean`).

Route. Write `f s r = ⟪G r, P(ν(s-r)) ψL⟫` with `P θ = centeredHeatVecL2CLM hc θ`.

* For fixed `G'` the map `θ ↦ ⟪G', P θ ψL⟫` has derivative bounded by `‖G'‖ ‖ψ'L‖` on `(0,∞)`
  and is constant on `(-∞,0]` (since `P θ = id` there). Hence it is Lipschitz on `ℝ`
  (`dl_lip_gen`, `dl_age_lip`). With `‖G r‖ ≤ M` on `[0,T]`, the integrand satisfies a uniform
  bound `|f s₂ r - f s₁ r| ≤ K |s₂ - s₁|` for all `r ∈ [0,T]`.
* For `s ≠ τ`, the Duhamel pairing splits as `F s = ∫₀^τ f s r dr + ∫_τ^s f s r dr`.
  The first piece is a difference quotient with a uniform bound and a.e. limit `∂_s f(τ,r)`
  (dominated convergence, `dl_leibniz_abstract`). The second piece is an average over a
  shrinking interval of a function continuous at `(τ,τ)` (`dl_avg_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-! ### Scalar Lipschitz lemma -/

/-- A real function on `ℝ` whose derivative is bounded by `K` on `(0,∞)` and which is constant on
`(-∞,0]` is `K`-Lipschitz. -/
theorem dl_lip_gen (g g' : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hcont : Continuous g)
    (hconst : ∀ θ : ℝ, θ ≤ 0 → g θ = g 0)
    (hderiv : ∀ θ : ℝ, 0 < θ → HasDerivAt g (g' θ) θ)
    (hbd : ∀ θ : ℝ, 0 < θ → ‖g' θ‖ ≤ K) (θ1 θ2 : ℝ) :
    ‖g θ2 - g θ1‖ ≤ K * |θ2 - θ1| := by
  have hpp : ∀ a b : ℝ, 0 < a → 0 < b → ‖g b - g a‖ ≤ K * ‖b - a‖ := by
    intro a b ha hb
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hderiv x hx).hasDerivWithinAt) (fun x hx => hbd x hx)
      (convex_Ioi (0:ℝ)) (show a ∈ Ioi (0:ℝ) from ha) (show b ∈ Ioi (0:ℝ) from hb)
  have hlim : ∀ b : ℝ, 0 < b → ‖g b - g 0‖ ≤ K * b := by
    intro b hb
    have hg0 : Tendsto (fun a : ℝ => g a) (𝓝[>] (0:ℝ)) (𝓝 (g 0)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun a : ℝ => ‖g b - g a‖) (𝓝[>] (0:ℝ)) (𝓝 ‖g b - g 0‖) :=
      (tendsto_const_nhds.sub hg0).norm
    have h2 : Tendsto (fun a : ℝ => K * |b - a|) (𝓝[>] (0:ℝ)) (𝓝 (K * |b - 0|)) :=
      ((by fun_prop : Continuous fun a : ℝ => K * |b - a|).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have h3 : ∀ᶠ a in 𝓝[>] (0:ℝ), ‖g b - g a‖ ≤ K * |b - a| := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      have := hpp a b ha hb
      simpa only [Real.norm_eq_abs] using this
    have := le_of_tendsto_of_tendsto h1 h2 h3
    rwa [sub_zero, abs_of_pos hb] at this
  have hge : ∀ b : ℝ, 0 < b → ∀ a : ℝ, a ≤ 0 → ‖g b - g a‖ ≤ K * |b - a| := by
    intro b hb a ha
    have hab : 0 < b - a := by linarith
    rw [hconst a ha, abs_of_pos hab]
    have h1 := hlim b hb
    have h2 : K * b ≤ K * (b - a) := mul_le_mul_of_nonneg_left (by linarith) hK
    linarith
  by_cases h1 : 0 < θ1 <;> by_cases h2 : 0 < θ2
  · have := hpp θ1 θ2 h1 h2
    simpa only [Real.norm_eq_abs] using this
  · rw [norm_sub_rev, abs_sub_comm]
    exact hge θ1 h1 θ2 (not_lt.1 h2)
  · exact hge θ2 h2 θ1 (not_lt.1 h1)
  · rw [hconst θ1 (not_lt.1 h1), hconst θ2 (not_lt.1 h2), sub_self, norm_zero]
    exact mul_nonneg hK (abs_nonneg _)

/-! ### The centered heat orbit on the age variable -/

/-- The centered heat projection is a contraction on every vector. -/
theorem dl_P_norm_le {c : ℝ} (hc : 0 < c) (θ : ℝ) (x : Cyl.L2v c) :
    ‖centeredHeatVecL2CLM hc θ x‖ ≤ ‖x‖ := by
  by_cases h : θ ≤ 0
  · rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc h]
    simp
  · have hθ : 0 < θ := not_le.1 h
    have h1 : ‖centeredHeatVecL2CLM hc θ‖ ≤ 1 := norm_centeredHeatVecL2CLM_le_one hc hθ
    calc ‖centeredHeatVecL2CLM hc θ x‖ ≤ ‖centeredHeatVecL2CLM hc θ‖ * ‖x‖ :=
          (centeredHeatVecL2CLM hc θ).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
      _ = ‖x‖ := one_mul _

/-- For a fixed class `G'` the age orbit `θ ↦ ⟪G', e^{θΔ} ψL⟫` is Lipschitz with constant
`M ‖ψ'L‖`, when `‖G'‖ ≤ M` and the age derivative is the heat of `ψ'L`. -/
theorem dl_age_lip {c : ℝ} (hc : 0 < c) (ψL ψ'L G' : Cyl.L2v c) (M : ℝ) (hG' : ‖G'‖ ≤ M)
    (hD : ∀ θ : ℝ, 0 < θ → HasDerivAt (fun s : ℝ => inner ℝ G' (centeredHeatVecL2CLM hc s ψL))
      (inner ℝ G' (centeredHeatVecL2CLM hc θ ψ'L)) θ)
    (hcont : Continuous (fun θ : ℝ => centeredHeatVecL2CLM hc θ ψL)) (θ1 θ2 : ℝ) :
    ‖inner ℝ G' (centeredHeatVecL2CLM hc θ2 ψL) - inner ℝ G' (centeredHeatVecL2CLM hc θ1 ψL)‖
      ≤ M * ‖ψ'L‖ * |θ2 - θ1| := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hG'
  refine dl_lip_gen (fun θ => inner ℝ G' (centeredHeatVecL2CLM hc θ ψL))
    (fun θ => inner ℝ G' (centeredHeatVecL2CLM hc θ ψ'L)) (M * ‖ψ'L‖)
    (mul_nonneg hM (norm_nonneg _)) (continuous_const.inner hcont) ?_ (fun θ hθ => hD θ hθ) ?_
    θ1 θ2
  · intro θ hθ
    show inner ℝ G' (centeredHeatVecL2CLM hc θ ψL) = inner ℝ G' (centeredHeatVecL2CLM hc 0 ψL)
    rw [centeredHeatVecL2CLM_eq_id_of_nonpos hc hθ,
      centeredHeatVecL2CLM_eq_id_of_nonpos hc (le_refl (0:ℝ))]
  · intro θ hθ
    show ‖inner ℝ G' (centeredHeatVecL2CLM hc θ ψ'L)‖ ≤ M * ‖ψ'L‖
    calc ‖inner ℝ G' (centeredHeatVecL2CLM hc θ ψ'L)‖
        ≤ ‖G'‖ * ‖centeredHeatVecL2CLM hc θ ψ'L‖ := norm_inner_le_norm _ _
      _ ≤ M * ‖ψ'L‖ :=
          mul_le_mul hG' (dl_P_norm_le hc θ ψ'L) (norm_nonneg _) (le_trans (norm_nonneg _) hG')

/-! ### The average of a function continuous at the center -/

/-- The average of `s ↦ ∫_τ^s F s r dr` over `s - τ` tends to `F τ τ`, when `(s,r) ↦ F s r` is
continuous at `(τ,τ)`. -/
theorem dl_avg_tendsto (F : ℝ → ℝ → ℝ) (τ : ℝ)
    (hF : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (τ, τ))
    (hint : ∀ᶠ s in 𝓝 τ, IntervalIntegrable (fun r => F s r) volume τ s) :
    Tendsto (fun s => (∫ r in τ..s, F s r) / (s - τ)) (𝓝[≠] τ) (𝓝 (F τ τ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hF (ε / 2) (by linarith)
  have hev : ∀ᶠ s in 𝓝[≠] τ, dist s τ < δ ∧ IntervalIntegrable (fun r => F s r) volume τ s
      ∧ s ≠ τ := by
    have h1 : ∀ᶠ s in 𝓝 τ, dist s τ < δ :=
      Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun y hy => hy⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1,
      eventually_nhdsWithin_of_eventually_nhds hint,
      (self_mem_nhdsWithin : ({τ}ᶜ : Set ℝ) ∈ 𝓝[≠] τ)] with s hs1 hs2 hs3
    exact ⟨hs1, hs2, hs3⟩
  filter_upwards [hev] with s hs
  obtain ⟨hs1, hs2, hs3⟩ := hs
  show dist ((∫ r in τ..s, F s r) / (s - τ)) (F τ τ) < ε
  have hsτ : s - τ ≠ 0 := sub_ne_zero.2 hs3
  have habs : 0 < |s - τ| := abs_pos.2 hsτ
  have hs1' : |s - τ| < δ := by rw [← Real.dist_eq]; exact hs1
  have hbd : ‖∫ r in τ..s, (F s r - F τ τ)‖ ≤ (ε / 2) * |s - τ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro r hr
    have hr' : |r - τ| ≤ |s - τ| := by
      rcases Set.mem_uIoc.1 hr with h | h
      · rw [abs_of_pos (sub_pos.2 h.1), abs_of_pos (by linarith [h.1, h.2] : (0:ℝ) < s - τ)]
        linarith [h.2]
      · rw [abs_of_nonpos (by linarith [h.1, h.2] : r - τ ≤ 0),
          abs_of_neg (by linarith [h.1, h.2] : s - τ < 0)]
        linarith [h.1]
    have hdist : dist (s, r) (τ, τ) < δ := by
      rw [Prod.dist_eq]
      exact max_lt hs1 (show dist r τ < δ by rw [Real.dist_eq]; linarith)
    have hh : dist (F s r) (F τ τ) < ε / 2 := hball hdist
    rw [Real.dist_eq] at hh
    show ‖F s r - F τ τ‖ ≤ ε / 2
    rw [Real.norm_eq_abs]
    exact hh.le
  have key : (∫ r in τ..s, F s r) / (s - τ) - F τ τ
      = (∫ r in τ..s, (F s r - F τ τ)) / (s - τ) := by
    rw [intervalIntegral.integral_sub hs2 intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, sub_div, mul_div_cancel_left₀ _ hsτ]
  rw [Real.dist_eq, key, abs_div, div_lt_iff₀ habs]
  have h3 := hbd
  rw [Real.norm_eq_abs] at h3
  nlinarith [mul_pos hε habs]

/-! ### The Leibniz rule for an abstract integrand -/

/-- The Leibniz rule for `σ ↦ ∫_0^σ F σ r dr` at `τ ∈ (0,T)`, for an integrand that is continuous
in `r`, jointly continuous at `(τ,τ)`, uniformly Lipschitz in the first variable, and has the
partial derivative `D r` in the first variable at `τ` for `r < τ`. -/
theorem dl_leibniz_abstract (F : ℝ → ℝ → ℝ) (D : ℝ → ℝ) (K T τ : ℝ) (hτ : τ ∈ Ioo (0:ℝ) T)
    (hcontr : ∀ s : ℝ, ContinuousOn (fun r => F s r) (Icc (0:ℝ) T))
    (hjoint : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (τ, τ))
    (hlip : ∀ r ∈ Icc (0:ℝ) T, ∀ s1 s2 : ℝ, ‖F s2 r - F s1 r‖ ≤ K * |s2 - s1|)
    (hD : ∀ r ∈ Ioo (0:ℝ) τ, HasDerivAt (fun s => F s r) (D r) τ) :
    HasDerivAt (fun σ : ℝ => ∫ r in Ioo (0:ℝ) σ, F σ r) (F τ τ + ∫ r in Ioo (0:ℝ) τ, D r) τ := by
  have hτI : τ ∈ Icc (0:ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hT0 : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_rfl, (hτ.1.trans hτ.2).le⟩
  have hsub' : Set.uIoc (0:ℝ) τ ⊆ Icc (0:ℝ) T := by
    rw [Set.uIoc_of_le hτ.1.le]
    exact fun r hr => ⟨hr.1.le, hr.2.trans hτI.2⟩
  -- uniform bound on the difference quotient
  have hbound : ∀ s : ℝ, s ≠ τ → ∀ r ∈ Icc (0:ℝ) T, ‖(F s r - F τ r) / (s - τ)‖ ≤ K := by
    intro s hs r hr
    rw [norm_div, Real.norm_eq_abs (s - τ), div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hs))]
    exact hlip r hr τ s
  -- term 1: dominated convergence on `(0,τ)`
  have hT1 : Tendsto (fun s : ℝ => ∫ r in (0:ℝ)..τ, (F s r - F τ r) / (s - τ)) (𝓝[≠] τ)
      (𝓝 (∫ r in (0:ℝ)..τ, D r)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
    · exact Eventually.of_forall fun s =>
        ((((hcontr s).sub (hcontr τ)).div_const (s - τ)).mono hsub').aestronglyMeasurable
          measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ae_of_all _ fun r hr => hbound s hs r (hsub' hr)
    · exact intervalIntegrable_const
    · have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ τ := by
        rw [ae_iff]
        simp
      filter_upwards [hae] with r hr hrI
      rw [Set.uIoc_of_le hτ.1.le] at hrI
      have hr' : r ∈ Ioo (0:ℝ) τ := ⟨hrI.1, lt_of_le_of_ne hrI.2 hr⟩
      have h := (hD r hr').tendsto_slope
      exact Tendsto.congr (fun s => slope_def_field (fun s => F s r) τ s) h
  -- term 2: the boundary average
  have hint : ∀ᶠ s in 𝓝 τ, IntervalIntegrable (fun r => F s r) volume τ s := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with s hs
    exact ((hcontr s).mono (uIcc_subset_Icc hτI ⟨hs.1.le, hs.2.le⟩)).intervalIntegrable
  have hT2 := dl_avg_tendsto F τ hjoint hint
  -- identities for the Ioo and interval integrals
  have hF_Ioo : ∀ σ : ℝ, 0 < σ → ∫ r in Ioo (0:ℝ) σ, F σ r = ∫ r in (0:ℝ)..σ, F σ r := by
    intro σ hσ
    rw [intervalIntegral.integral_of_le hσ.le, integral_Ioc_eq_integral_Ioo]
  have hDint : ∫ r in (0:ℝ)..τ, D r = ∫ r in Ioo (0:ℝ) τ, D r := by
    rw [intervalIntegral.integral_of_le hτ.1.le, integral_Ioc_eq_integral_Ioo]
  have hslope : ∀ s : ℝ, s ∈ Ioo (0:ℝ) T → s ≠ τ →
      (∫ r in (0:ℝ)..τ, (F s r - F τ r) / (s - τ)) + (∫ r in τ..s, F s r) / (s - τ)
        = slope (fun σ : ℝ => ∫ r in Ioo (0:ℝ) σ, F σ r) τ s := by
    intro s hs hsτ
    have hsI : s ∈ Icc (0:ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hI1 : IntervalIntegrable (fun r => F s r) volume 0 τ :=
      ((hcontr s).mono (uIcc_subset_Icc hT0 hτI)).intervalIntegrable
    have hI0 : IntervalIntegrable (fun r => F τ r) volume 0 τ :=
      ((hcontr τ).mono (uIcc_subset_Icc hT0 hτI)).intervalIntegrable
    have hI2 : IntervalIntegrable (fun r => F s r) volume τ s :=
      ((hcontr s).mono (uIcc_subset_Icc hτI hsI)).intervalIntegrable
    simp only [slope_def_field]
    rw [hF_Ioo s hs.1, hF_Ioo τ hτ.1]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hI1 hI0,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    ring
  -- assemble
  have hL : F τ τ + ∫ r in Ioo (0:ℝ) τ, D r = (∫ r in (0:ℝ)..τ, D r) + F τ τ := by
    rw [hDint]
    ring
  rw [hasDerivAt_iff_tendsto_slope, hL]
  have hev : ∀ᶠ s in 𝓝[≠] τ, s ∈ Ioo (0:ℝ) T ∧ s ≠ τ := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds hτ.1 hτ.2),
      (self_mem_nhdsWithin : ({τ}ᶜ : Set ℝ) ∈ 𝓝[≠] τ)] with s hs1 hs2
    exact ⟨hs1, hs2⟩
  refine Tendsto.congr' ?_ (hT1.add hT2)
  filter_upwards [hev] with s hs
  exact hslope s hs.1 hs.2

/-! ### The Leibniz rule for the Duhamel integrand -/

/-- The Duhamel integrand `⟪G r, e^{ν(s-r)Δ} ψL⟫`. -/
def dlIntegrand {c : ℝ} (hc : 0 < c) (ν : ℝ) (G : ℝ → Cyl.L2v c) (ψL : Cyl.L2v c) (s r : ℝ) :
    ℝ :=
  inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (s - r)) ψL)

/-- **Leaf 4** (`DuhamelLeibnizL2`).  The Leibniz rule for the Duhamel integral with moving upper
limit, from the continuity of `G` on `[0,T]`, the age derivative of the centered heat, and the
continuity of the centered heat orbit. -/
theorem duhamelLeibnizL2 : DuhamelLeibnizL2 := by
  intro c ν T hc hν G ψL ψ'L hG hD hC τ hτ
  have hcomp : IsCompact (Icc (0:ℝ) T) := isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hG
  have hτI : τ ∈ Icc (0:ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  have hcontr : ∀ s : ℝ, ContinuousOn (fun r => dlIntegrand hc ν G ψL s r) (Icc (0:ℝ) T) := by
    intro s
    have hPr : Continuous (fun r : ℝ => centeredHeatVecL2CLM hc (ν * (s - r)) ψL) :=
      (hC ψL).comp (show Continuous (fun r : ℝ => ν * (s - r)) by fun_prop)
    exact hG.inner hPr.continuousOn
  have hjoint : ContinuousAt (fun p : ℝ × ℝ => dlIntegrand hc ν G ψL p.1 p.2) (τ, τ) := by
    have hGτ : ContinuousAt G τ := hG.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
    have hGp : ContinuousAt (fun p : ℝ × ℝ => G p.2) (τ, τ) :=
      hGτ.comp (continuousAt_snd : ContinuousAt (fun p : ℝ × ℝ => p.2) (τ, τ))
    have hPp : Continuous (fun p : ℝ × ℝ => centeredHeatVecL2CLM hc (ν * (p.1 - p.2)) ψL) :=
      (hC ψL).comp (show Continuous (fun p : ℝ × ℝ => ν * (p.1 - p.2)) by fun_prop)
    exact ContinuousAt.inner hGp hPp.continuousAt
  have hlip : ∀ r ∈ Icc (0:ℝ) T, ∀ s1 s2 : ℝ,
      ‖dlIntegrand hc ν G ψL s2 r - dlIntegrand hc ν G ψL s1 r‖
        ≤ (M * ‖ψ'L‖ * ν) * |s2 - s1| := by
    intro r hr s1 s2
    have h := dl_age_lip hc ψL ψ'L (G r) M (hM r hr) (fun θ hθ => hD (G r) θ hθ) (hC ψL)
      (ν * (s1 - r)) (ν * (s2 - r))
    have e : |ν * (s2 - r) - ν * (s1 - r)| = ν * |s2 - s1| := by
      rw [show ν * (s2 - r) - ν * (s1 - r) = ν * (s2 - s1) by ring, abs_mul, abs_of_pos hν]
    unfold dlIntegrand
    refine h.trans (le_of_eq ?_)
    rw [e]
    ring
  have hDr : ∀ r ∈ Ioo (0:ℝ) τ, HasDerivAt (fun s => dlIntegrand hc ν G ψL s r)
      (ν * inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (τ - r)) ψ'L)) τ := by
    intro r hr
    have hθ : 0 < ν * (τ - r) := mul_pos hν (sub_pos.2 hr.2)
    have h1 := hD (G r) (ν * (τ - r)) hθ
    have h2 : HasDerivAt (fun s : ℝ => ν * (s - r)) ν τ := by
      have := ((hasDerivAt_id τ).sub_const r).const_mul ν
      simpa using this
    have h4 := h1.comp τ h2
    exact h4.congr_deriv (mul_comm _ _)
  have key := dl_leibniz_abstract (dlIntegrand hc ν G ψL)
    (fun r => ν * inner ℝ (G r) (centeredHeatVecL2CLM hc (ν * (τ - r)) ψ'L))
    ((M * ‖ψ'L‖) * ν) T τ hτ hcontr hjoint hlip hDr
  have hτ0 : dlIntegrand hc ν G ψL τ τ = inner ℝ (G τ) ψL := by
    unfold dlIntegrand
    simp [centeredHeatVecL2CLM_eq_id_of_nonpos hc (le_refl (0:ℝ))]
  rw [hτ0, MeasureTheory.integral_const_mul] at key
  exact key

end UnforcedLeray.Short.PartI
