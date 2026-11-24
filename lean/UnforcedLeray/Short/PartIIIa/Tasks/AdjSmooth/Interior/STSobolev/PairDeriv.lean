import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSobolev.PairBound

/-!
# `PartIII-a:T21/2/7/2/1/1/7/2`: the tested time derivative `PairDeriv`

Source: `the November 2 reference manuscript` lines 3060-3061.
The pairing `h(r) = ∫ Θ(r,x) Φ j r x dx` is differentiated by splitting the difference quotient
into three pieces, each controlled by `pairBound` (the pairing bound on the box `sliceBox R`):
the `X`-limit of the difference quotient of `Φ j`, the uniform continuity of `Θ`, and the mean
value bound for the `r`-partial derivative of `Θ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem pairDeriv : UnforcedLeray.Short.IIIa.PairDeriv := by
  intro c m t s Φ j Θ hc _hts hΦ hΘ hΘsupp _hΘts
  have hΘc : Continuous Θ := hΘ.continuous
  -- the box carrying the spatial supports of Θ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ p ∈ tsupport Θ, ‖p.2‖ ≤ R := by
    obtain ⟨R, hR⟩ := hΘsupp.isCompact.exists_bound_of_continuousOn
      (f := fun p : ℝ × (ℝ × ℝ) => p.2) continuous_snd.continuousOn
    exact ⟨R, hR⟩
  have hbox : ∀ p : ℝ × (ℝ × ℝ), p ∈ tsupport Θ → p.2 ∈ sliceBox R := by
    intro p hp
    have h1 : ‖p.2‖ ≤ R := hR p hp
    have h2 : |p.2.1| ≤ R := by
      rw [← Real.norm_eq_abs]; exact (norm_fst_le p.2).trans h1
    have h3 : |p.2.2| ≤ R := by
      rw [← Real.norm_eq_abs]; exact (norm_snd_le p.2).trans h1
    unfold sliceBox
    exact ⟨⟨(abs_le.1 h2).1, (abs_le.1 h2).2⟩, ⟨(abs_le.1 h3).1, (abs_le.1 h3).2⟩⟩
  have hΘ0 : ∀ p : ℝ × (ℝ × ℝ), p.2 ∉ sliceBox R → Θ p = 0 := by
    intro p hp
    by_contra hne
    exact hp (hbox p (subset_tsupport _ (Function.mem_support.2 hne)))
  have hD0 : ∀ p : ℝ × (ℝ × ℝ), p.2 ∉ sliceBox R → fderiv ℝ Θ p (1, (0, 0)) = 0 := by
    intro p hp
    have hn : p ∉ tsupport (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Θ q (1, (0, 0))) :=
      fun hmem => hp (hbox p (tsupport_fderiv_apply_subset ℝ (1, (0, 0)) hmem))
    exact image_eq_zero_of_notMem_tsupport (f := fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Θ q (1, (0, 0))) hn
  have hD1c : Continuous (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Θ q (1, (0, 0))) :=
    (hΘ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hD1s : HasCompactSupport (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Θ q (1, (0, 0))) :=
    hΘsupp.fderiv_apply ℝ (1, (0, 0))
  have hUΘ : UniformContinuous Θ := hΘsupp.uniformContinuous_of_continuous hΘc
  have hUD : UniformContinuous (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Θ q (1, (0, 0))) :=
    hD1s.uniformContinuous_of_continuous hD1c
  obtain ⟨MΘ, hMΘ⟩ := hΘc.bounded_above_of_compact_support hΘsupp
  obtain ⟨MD, hMD⟩ := hD1c.bounded_above_of_compact_support hD1s
  have hMΘ0 : 0 ≤ MΘ := le_trans (norm_nonneg _) (hMΘ 0)
  have hMD0 : 0 ≤ MD := le_trans (norm_nonneg _) (hMD 0)
  have hbT : ∀ (r : ℝ) (x : ℝ × ℝ), ‖((Θ (r, x) : ℝ) : ℂ)‖ ≤ MΘ := fun r x => by
    rw [Complex.norm_real]; exact hMΘ _
  have hbD : ∀ (r : ℝ) (x : ℝ × ℝ), ‖((fderiv ℝ Θ (r, x) (1, (0, 0)) : ℝ) : ℂ)‖ ≤ MD :=
    fun r x => by
      rw [Complex.norm_real]; exact hMD _
  have hsT : ∀ (r : ℝ) (x : ℝ × ℝ), x ∉ sliceBox R → ((Θ (r, x) : ℝ) : ℂ) = 0 := fun r x hx => by
    rw [hΘ0 (r, x) hx]; simp
  have hsD : ∀ (r : ℝ) (x : ℝ × ℝ), x ∉ sliceBox R →
      ((fderiv ℝ Θ (r, x) (1, (0, 0)) : ℝ) : ℂ) = 0 := fun r x hx => by
    rw [hD0 (r, x) hx]; simp
  have hmeasT : ∀ r : ℝ, Measurable (fun x : ℝ × ℝ => ((Θ (r, x) : ℝ) : ℂ)) := fun r => by
    apply Continuous.measurable; apply Complex.continuous_ofReal.comp; fun_prop
  have hmeasD : ∀ r : ℝ,
      Measurable (fun x : ℝ × ℝ => ((fderiv ℝ Θ (r, x) (1, (0, 0)) : ℝ) : ℂ)) := fun r => by
    apply Continuous.measurable; apply Complex.continuous_ofReal.comp; fun_prop
  -- the pairing bound, with the constant made nonnegative
  obtain ⟨C, hC⟩ := pairBound c m R hc
  have hP : ∀ (θ h : ℝ × ℝ → ℂ) (B : ℝ), 0 ≤ B → Periodic1 c h →
      MemLp h 2 (B0579.cellMeasure c (-m)) → Measurable θ →
      (∀ x, x ∉ sliceBox R → θ x = 0) → (∀ x, ‖θ x‖ ≤ B) →
      Integrable (fun x => θ x * h x) ∧
        ‖∫ x, θ x * h x‖ ≤ |C| * B * (xNorm c (-m) h).toReal := by
    intro θ h B hB hper hmem hmeas hsupp hbd
    obtain ⟨hint, hb⟩ := hC h θ B hper hmem hmeas hsupp hbd
    refine ⟨hint, hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hB)
      ENNReal.toReal_nonneg
  -- periodicity and integrability of the time jets
  have hΦp : ∀ k : ℕ, ∀ r ∈ Ioo t s,
      Periodic1 c (Φ k r) ∧ MemLp (Φ k r) 2 (B0579.cellMeasure c (-m)) := by
    intro k r hr
    obtain ⟨D, hD, -⟩ := hΦ.1 k 0
    have h0 := hD r hr
    have hb : D r [] = Φ k r := h0.base
    constructor
    · intro x
      have := h0.periodic [] (by simp) x
      rwa [hb] at this
    · have := h0.memX [] (by simp)
      rwa [hb] at this
  have hΦc : ∀ k : ℕ, ∀ r0 ∈ Ioo t s,
      Tendsto (fun r => xNorm c (-m) (Φ k r - Φ k r0)) (𝓝[Ioo t s] r0) (𝓝 0) := by
    intro k r0 hr0
    obtain ⟨D, hD, hDc⟩ := hΦ.1 k 0
    have hT := hDc [] (by simp) r0 hr0
    refine Tendsto.congr' ?_ hT
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [(hD r hr).base, (hD r0 hr0).base]
  have hΦdq : ∀ r0 ∈ Ioo t s,
      Tendsto (fun r' => xNorm c (-m) (fun x => (((r' - r0)⁻¹ : ℝ) : ℂ) *
        (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x)) (𝓝[≠] r0) (𝓝 0) := by
    intro r0 hr0
    refine (hΦ.2 j r0 hr0).mono_left (nhdsWithin_le_of_mem ?_)
    have h1 : Ioo t s ∈ 𝓝[≠] r0 := nhdsWithin_le_nhds (Ioo_mem_nhds hr0.1 hr0.2)
    filter_upwards [h1, self_mem_nhdsWithin] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  -- linear combinations and periodicity
  have hPerSub : ∀ f g : ℝ × ℝ → ℂ, Periodic1 c f → Periodic1 c g →
      Periodic1 c (fun x => f x - g x) := by
    intro f g hf hg x
    simp only [hf x, hg x]
  have hPerLin : ∀ (a : ℂ) (f g k : ℝ × ℝ → ℂ), Periodic1 c f → Periodic1 c g →
      Periodic1 c k → Periodic1 c (fun x => a * (f x - g x) - k x) := by
    intro a f g k hf hg hk x
    simp only [hf x, hg x, hk x]
  have hMemLin : ∀ (a : ℂ) (f g k : ℝ × ℝ → ℂ), MemLp f 2 (B0579.cellMeasure c (-m)) →
      MemLp g 2 (B0579.cellMeasure c (-m)) → MemLp k 2 (B0579.cellMeasure c (-m)) →
      MemLp (fun x => a * (f x - g x) - k x) 2 (B0579.cellMeasure c (-m)) :=
    fun a f g k hf hg hk => ((hf.sub hg).const_mul a).sub hk
  -- the scalar uniform-continuity and the mean value bound
  have hCplx : ∀ u v : ℝ, ‖((u : ℝ) : ℂ) - ((v : ℝ) : ℂ)‖ = |u - v| := fun u v => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hUCg : ∀ g : ℝ × (ℝ × ℝ) → ℝ, UniformContinuous g → ∀ r0 : ℝ, ∀ ε > 0,
      ∀ᶠ r in 𝓝 r0, ∀ x : ℝ × ℝ, |g (r, x) - g (r0, x)| ≤ ε := by
    intro g hg r0 ε hε
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 hg ε hε
    filter_upwards [Metric.ball_mem_nhds r0 hδ] with r hr x
    have hd : dist ((r, x) : ℝ × (ℝ × ℝ)) (r0, x) < δ := by
      rw [dist_prod_same_right]; exact hr
    have := hδg hd
    rw [Real.dist_eq] at this
    exact this.le
  have hUCCg : ∀ g : ℝ × (ℝ × ℝ) → ℝ, UniformContinuous g → ∀ r0 : ℝ, ∀ S : Set ℝ, ∀ ε > 0,
      ∀ᶠ r in 𝓝[S] r0, ∀ x : ℝ × ℝ, ‖((g (r, x) : ℝ) : ℂ) - ((g (r0, x) : ℝ) : ℂ)‖ ≤ ε := by
    intro g hg r0 S ε hε
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [hUCg g hg r0 ε hε] with r hr x
    rw [hCplx]; exact hr x
  have hMVTr : ∀ r0 : ℝ, ∀ ε > 0, ∀ᶠ r in 𝓝[≠] r0, ∀ x : ℝ × ℝ,
      |(r - r0)⁻¹ * (Θ (r, x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0))| ≤ ε := by
    intro r0 ε hε
    obtain ⟨η, hη, hηD⟩ := Metric.eventually_nhds_iff.1 (hUCg _ hUD r0 ε hε)
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds r0 hη),
      eventually_mem_nhdsWithin] with r hr hrne x
    have hrne' : r ≠ r0 := hrne
    have hrb : r ∈ Metric.ball r0 η := hr
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = fderiv ℝ Θ (r0, x) (1, (0, 0)) := ⟨_, rfl⟩
    rw [← ha]
    have hder : ∀ τ : ℝ, HasDerivAt (fun τ => Θ (τ, x) - a * τ)
        (fderiv ℝ Θ (τ, x) (1, (0, 0)) - a) τ := by
      intro τ
      have h1 : HasDerivAt (fun τ : ℝ => (τ, x)) ((1 : ℝ), (0 : ℝ × ℝ)) τ :=
        (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ x)
      have h2 : HasFDerivAt Θ (fderiv ℝ Θ (τ, x)) (τ, x) :=
        ((hΘ.differentiable (by simp)) (τ, x)).hasFDerivAt
      have h3 : HasDerivAt (fun τ => Θ (τ, x)) (fderiv ℝ Θ (τ, x) (1, (0, 0))) τ :=
        h2.comp_hasDerivAt τ h1
      have h4 : HasDerivAt (fun τ => Θ (τ, x) - a * τ)
          (fderiv ℝ Θ (τ, x) (1, (0, 0)) - a * 1) τ :=
        h3.sub ((hasDerivAt_id' τ).const_mul a)
      rw [mul_one] at h4
      exact h4
    have hbd : ∀ τ ∈ Metric.ball r0 η, ‖fderiv ℝ Θ (τ, x) (1, (0, 0)) - a‖ ≤ ε := by
      intro τ hτ
      have h5 := hηD (Metric.mem_ball.1 hτ) x
      rw [ha, Real.norm_eq_abs]
      exact h5
    have hconv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => Θ (τ, x) - a * τ) (f' := fun τ => fderiv ℝ Θ (τ, x) (1, (0, 0)) - a)
      (s := Metric.ball r0 η) (C := ε)
      (fun τ _ => (hder τ).hasDerivWithinAt) (fun τ hτ => hbd τ hτ) (convex_ball r0 η)
      (Metric.mem_ball_self hη) hrb
    simp only [Real.norm_eq_abs] at hconv
    have hdne : r - r0 ≠ 0 := sub_ne_zero.2 hrne'
    have hadne : |r - r0| ≠ 0 := abs_ne_zero.2 hdne
    have hkey : (r - r0)⁻¹ * (Θ (r, x) - Θ (r0, x)) - a
        = (r - r0)⁻¹ * ((Θ (r, x) - a * r) - (Θ (r0, x) - a * r0)) := by
      field_simp
      ring
    rw [hkey, abs_mul, abs_inv]
    calc |r - r0|⁻¹ * |(Θ (r, x) - a * r) - (Θ (r0, x) - a * r0)|
        ≤ |r - r0|⁻¹ * (ε * |r - r0|) :=
          mul_le_mul_of_nonneg_left hconv (inv_nonneg.2 (abs_nonneg _))
      _ = ε := by field_simp
  have hMVTC : ∀ r0 : ℝ, ∀ ε > 0, ∀ᶠ r in 𝓝[≠] r0, ∀ x : ℝ × ℝ,
      ‖(((r - r0)⁻¹ * (Θ (r, x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ) : ℂ)‖ ≤ ε := by
    intro r0 ε hε
    filter_upwards [hMVTr r0 ε hε] with r hr x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hr x
  -- the two abstract pairing limits
  have hSL1 : ∀ (F : Filter ℝ) (θf : ℝ → ℝ × ℝ → ℂ) (h : ℝ × ℝ → ℂ), Periodic1 c h →
      MemLp h 2 (B0579.cellMeasure c (-m)) → (∀ r, Measurable (θf r)) →
      (∀ r x, x ∉ sliceBox R → θf r x = 0) → (∀ ε > 0, ∀ᶠ r in F, ∀ x, ‖θf r x‖ ≤ ε) →
      Tendsto (fun r => ∫ x, θf r x * h x) F (𝓝 0) := by
    intro F θf h hper hmemh hmeas hsupp hunif
    have hX : 0 ≤ (xNorm c (-m) h).toReal := ENNReal.toReal_nonneg
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hden : 0 < 2 * (|C| * (xNorm c (-m) h).toReal + 1) := by
      have := mul_nonneg (abs_nonneg C) hX
      linarith
    obtain ⟨B, hBpos, hBeq⟩ : ∃ B : ℝ, 0 < B ∧ B * (|C| * (xNorm c (-m) h).toReal + 1) = ε / 2 :=
      ⟨ε / (2 * (|C| * (xNorm c (-m) h).toReal + 1)), div_pos hε hden, by
        have hne : |C| * (xNorm c (-m) h).toReal + 1 ≠ 0 := by
          have := mul_nonneg (abs_nonneg C) hX
          linarith
        field_simp⟩
    filter_upwards [hunif B hBpos] with r hr
    rw [dist_zero_right]
    obtain ⟨-, hb⟩ := hP (θf r) h B hBpos.le hper hmemh (hmeas r) (hsupp r) hr
    have h1 : |C| * B * (xNorm c (-m) h).toReal ≤ B * (|C| * (xNorm c (-m) h).toReal + 1) := by
      nlinarith [hBpos, hX, abs_nonneg C]
    linarith
  have hSL2 : ∀ (F : Filter ℝ) (θf : ℝ → ℝ × ℝ → ℂ) (hf : ℝ → ℝ × ℝ → ℂ) (M : ℝ), 0 ≤ M →
      (∀ᶠ r in F, Periodic1 c (hf r) ∧ MemLp (hf r) 2 (B0579.cellMeasure c (-m))) →
      (∀ r, Measurable (θf r)) → (∀ r x, x ∉ sliceBox R → θf r x = 0) →
      (∀ r x, ‖θf r x‖ ≤ M) → Tendsto (fun r => xNorm c (-m) (hf r)) F (𝓝 0) →
      Tendsto (fun r => ∫ x, θf r x * hf r x) F (𝓝 0) := by
    intro F θf hf M hM hev hmeas hsupp hbd hxn
    have hX : Tendsto (fun r => |C| * M * (xNorm c (-m) (hf r)).toReal) F (𝓝 0) := by
      have h1 : Tendsto (fun r => (xNorm c (-m) (hf r)).toReal) F (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hxn
        rw [ENNReal.toReal_zero] at this
        exact this
      simpa using h1.const_mul (|C| * M)
    refine squeeze_zero_norm' ?_ hX
    filter_upwards [hev] with r hr
    exact (hP (θf r) (hf r) M hM hr.1 hr.2 (hmeas r) (hsupp r) (hbd r)).2
  -- continuity of the pairings `r ↦ ∫ g(r,·) Φ k r`
  have hContGen : ∀ (g : ℝ × (ℝ × ℝ) → ℝ) (k : ℕ) (r0 : ℝ), r0 ∈ Ioo t s → Continuous g →
      UniformContinuous g → (∀ p : ℝ × (ℝ × ℝ), p.2 ∉ sliceBox R → g p = 0) → ∀ Mg : ℝ,
      0 ≤ Mg → (∀ p, ‖g p‖ ≤ Mg) →
      Tendsto (fun r => (∫ x : ℝ × ℝ, ((g (r, x) : ℝ) : ℂ) * Φ k r x) -
        ∫ x : ℝ × ℝ, ((g (r0, x) : ℝ) : ℂ) * Φ k r0 x) (𝓝[Ioo t s] r0) (𝓝 0) := by
    intro g k r0 hr0 hgc hgu hg0 Mg hMg0 hgM
    have hmeas : ∀ r : ℝ, Measurable (fun x : ℝ × ℝ => ((g (r, x) : ℝ) : ℂ)) := fun r => by
      apply Continuous.measurable; apply Complex.continuous_ofReal.comp; fun_prop
    have hsup : ∀ (r : ℝ) (x : ℝ × ℝ), x ∉ sliceBox R → ((g (r, x) : ℝ) : ℂ) = 0 :=
      fun r x hx => by rw [hg0 (r, x) hx]; simp
    have hbd : ∀ (r : ℝ) (x : ℝ × ℝ), ‖((g (r, x) : ℝ) : ℂ)‖ ≤ Mg := fun r x => by
      rw [Complex.norm_real]; exact hgM _
    have hev2 : ∀ᶠ r in 𝓝[Ioo t s] r0, Periodic1 c (fun x => Φ k r x - Φ k r0 x) ∧
        MemLp (fun x => Φ k r x - Φ k r0 x) 2 (B0579.cellMeasure c (-m)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨hPerSub _ _ (hΦp k r hr).1 (hΦp k r0 hr0).1,
        (hΦp k r hr).2.sub (hΦp k r0 hr0).2⟩
    have e1 := hSL1 (𝓝[Ioo t s] r0) (fun r x => ((g (r, x) : ℝ) : ℂ) - ((g (r0, x) : ℝ) : ℂ))
      (Φ k r0) (hΦp k r0 hr0).1 (hΦp k r0 hr0).2 (fun r => (hmeas r).sub (hmeas r0))
      (fun r x hx => by simp [hsup r x hx, hsup r0 x hx]) (fun ε hε => hUCCg g hgu r0 _ ε hε)
    have e2 := hSL2 (𝓝[Ioo t s] r0) (fun r x => ((g (r, x) : ℝ) : ℂ))
      (fun r x => Φ k r x - Φ k r0 x) Mg hMg0 hev2 hmeas (fun r x hx => hsup r x hx) hbd
      (hΦc k r0 hr0)
    have hsum := e1.add e2
    rw [add_zero] at hsum
    refine Tendsto.congr' ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hI1 : Integrable (fun x : ℝ × ℝ => (((g (r, x) : ℝ) : ℂ) - ((g (r0, x) : ℝ) : ℂ)) *
        Φ k r0 x) := (hP (fun x => ((g (r, x) : ℝ) : ℂ) - ((g (r0, x) : ℝ) : ℂ)) (Φ k r0)
          (2 * Mg) (by linarith) (hΦp k r0 hr0).1 (hΦp k r0 hr0).2
          ((hmeas r).sub (hmeas r0)) (fun x hx => by simp [hsup r x hx, hsup r0 x hx])
          (fun x => (norm_sub_le _ _).trans (by linarith [hbd r x, hbd r0 x]))).1
    have hI2 : Integrable (fun x : ℝ × ℝ => ((g (r, x) : ℝ) : ℂ) * (Φ k r x - Φ k r0 x)) :=
      (hP (fun x => ((g (r, x) : ℝ) : ℂ)) (fun x => Φ k r x - Φ k r0 x) Mg hMg0
        (hPerSub _ _ (hΦp k r hr).1 (hΦp k r0 hr0).1)
        ((hΦp k r hr).2.sub (hΦp k r0 hr0).2) (hmeas r) (fun x hx => hsup r x hx) (hbd r)).1
    have hI3 : Integrable (fun x : ℝ × ℝ => ((g (r, x) : ℝ) : ℂ) * Φ k r x) :=
      (hP (fun x => ((g (r, x) : ℝ) : ℂ)) (Φ k r) Mg hMg0 (hΦp k r hr).1 (hΦp k r hr).2
        (hmeas r) (fun x hx => hsup r x hx) (hbd r)).1
    have hI4 : Integrable (fun x : ℝ × ℝ => ((g (r0, x) : ℝ) : ℂ) * Φ k r0 x) :=
      (hP (fun x => ((g (r0, x) : ℝ) : ℂ)) (Φ k r0) Mg hMg0 (hΦp k r0 hr0).1 (hΦp k r0 hr0).2
        (hmeas r0) (fun x hx => hsup r0 x hx) (hbd r0)).1
    rw [← integral_add hI1 hI2, ← integral_sub hI3 hI4]
    congr 1
    funext x
    ring
  -- the derivative of the pairing
  have hder : ∀ r0 ∈ Ioo t s, HasDerivAt (fun r' => ∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) * Φ j r' x)
      ((∫ x : ℝ × ℝ, (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x) +
        ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x) r0 := by
    intro r0 hr0
    rw [hasDerivAt_iff_tendsto_slope]
    have hlin1 : ∀ r' ∈ Ioo t s,
        Periodic1 c (fun x => (((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) ∧
        MemLp (fun x => (((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) 2
          (B0579.cellMeasure c (-m)) := fun r' hr' =>
      ⟨hPerLin _ _ _ _ (hΦp j r' hr').1 (hΦp j r0 hr0).1 (hΦp (j + 1) r0 hr0).1,
        hMemLin _ _ _ _ (hΦp j r' hr').2 (hΦp j r0 hr0).2 (hΦp (j + 1) r0 hr0).2⟩
    have meas3 : ∀ r' : ℝ, Measurable (fun x : ℝ × ℝ =>
        ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ)) :=
      fun r' => by
        apply Continuous.measurable; apply Complex.continuous_ofReal.comp; fun_prop
    have supp3 : ∀ (r' : ℝ) (x : ℝ × ℝ), x ∉ sliceBox R →
        ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) = 0 :=
      fun r' x hx => by simp [hΘ0 (r', x) hx, hΘ0 (r0, x) hx, hD0 (r0, x) hx]
    have hevI : ∀ᶠ r' in 𝓝[≠] r0, r' ∈ Ioo t s := nhdsWithin_le_nhds (Ioo_mem_nhds hr0.1 hr0.2)
    have hevN : ∀ᶠ r' in 𝓝[≠] r0, r' ∈ ({r0}ᶜ : Set ℝ) := eventually_mem_nhdsWithin
    have hE1 : Tendsto (fun r' => ∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) *
        ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x)) (𝓝[≠] r0) (𝓝 0) := by
      refine hSL2 (𝓝[≠] r0) (fun r' x => ((Θ (r', x) : ℝ) : ℂ))
        (fun r' x => (((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x)
        MΘ hMΘ0 ?_ (fun r => hmeasT r) (fun r x hx => hsT r x hx) (fun r x => hbT r x) ?_
      · filter_upwards [hevI] with r' hr' using hlin1 r' hr'
      · exact hΦdq r0 hr0
    have hE2 : Tendsto (fun r' => ∫ x : ℝ × ℝ,
        (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x) (𝓝[≠] r0) (𝓝 0) :=
      hSL1 (𝓝[≠] r0) (fun r' x => ((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ))
        (Φ (j + 1) r0) (hΦp (j + 1) r0 hr0).1 (hΦp (j + 1) r0 hr0).2
        (fun r => (hmeasT r).sub (hmeasT r0))
        (fun r x hx => by simp [hsT r x hx, hsT r0 x hx])
        (fun ε hε => hUCCg Θ hUΘ r0 _ ε hε)
    have hE3 : Tendsto (fun r' => ∫ x : ℝ × ℝ,
        ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) *
          Φ j r0 x) (𝓝[≠] r0) (𝓝 0) :=
      hSL1 (𝓝[≠] r0) (fun r' x =>
          ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ))
        (Φ j r0) (hΦp j r0 hr0).1 (hΦp j r0 hr0).2 meas3 supp3
        (fun ε hε => hMVTC r0 ε hε)
    -- the algebraic identity on a punctured neighbourhood
    have hid : ∀ r' ∈ Ioo t s, r' ≠ r0 →
        (∀ x : ℝ × ℝ, ‖((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
          fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ)‖ ≤ 1) →
        slope (fun r => ∫ x : ℝ × ℝ, ((Θ (r, x) : ℝ) : ℂ) * Φ j r x) r0 r' -
          ((∫ x : ℝ × ℝ, (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x) +
            ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x)
        = (∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) *
              ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x)) +
          (∫ x : ℝ × ℝ, (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x) +
          ∫ x : ℝ × ℝ, ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
              fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) * Φ j r0 x := by
      intro r' hr' hne hb3
      have hΦ' := hΦp j r' hr'
      have hΦ0 := hΦp j r0 hr0
      have hΦ1 := hΦp (j + 1) r0 hr0
      have iF' : Integrable (fun x : ℝ × ℝ => ((Θ (r', x) : ℝ) : ℂ) * Φ j r' x) :=
        (hP (fun x => ((Θ (r', x) : ℝ) : ℂ)) (Φ j r') MΘ hMΘ0 hΦ'.1 hΦ'.2 (hmeasT r')
          (fun x hx => hsT r' x hx) (fun x => hbT r' x)).1
      have iF0 : Integrable (fun x : ℝ × ℝ => ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x) :=
        (hP (fun x => ((Θ (r0, x) : ℝ) : ℂ)) (Φ j r0) MΘ hMΘ0 hΦ0.1 hΦ0.2 (hmeasT r0)
          (fun x hx => hsT r0 x hx) (fun x => hbT r0 x)).1
      have iD0 : Integrable (fun x : ℝ × ℝ =>
          ((fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ) : ℂ) * Φ j r0 x) :=
        (hP (fun x => ((fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ) : ℂ)) (Φ j r0) MD hMD0 hΦ0.1 hΦ0.2
          (hmeasD r0) (fun x hx => hsD r0 x hx) (fun x => hbD r0 x)).1
      have iT0 : Integrable (fun x : ℝ × ℝ => ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x) :=
        (hP (fun x => ((Θ (r0, x) : ℝ) : ℂ)) (Φ (j + 1) r0) MΘ hMΘ0 hΦ1.1 hΦ1.2 (hmeasT r0)
          (fun x hx => hsT r0 x hx) (fun x => hbT r0 x)).1
      have I1 : Integrable (fun x : ℝ × ℝ => ((Θ (r', x) : ℝ) : ℂ) *
          ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x)) :=
        (hP (fun x => ((Θ (r', x) : ℝ) : ℂ))
          (fun x => (((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) MΘ hMΘ0
          (hlin1 r' hr').1 (hlin1 r' hr').2 (hmeasT r') (fun x hx => hsT r' x hx)
          (fun x => hbT r' x)).1
      have I2 : Integrable (fun x : ℝ × ℝ =>
          (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x) :=
        (hP (fun x => ((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) (Φ (j + 1) r0) (2 * MΘ)
          (by linarith) hΦ1.1 hΦ1.2 ((hmeasT r').sub (hmeasT r0))
          (fun x hx => by simp [hsT r' x hx, hsT r0 x hx])
          (fun x => (norm_sub_le _ _).trans (by linarith [hbT r' x, hbT r0 x]))).1
      have I3 : Integrable (fun x : ℝ × ℝ =>
          ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) - fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) *
            Φ j r0 x) :=
        (hP (fun x => ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
              fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ)) (Φ j r0) 1 zero_le_one hΦ0.1 hΦ0.2
          (meas3 r') (fun x hx => supp3 r' x hx) hb3).1
      have iFF : Integrable (fun x : ℝ × ℝ => (((r' - r0)⁻¹ : ℝ) : ℂ) *
          (((Θ (r', x) : ℝ) : ℂ) * Φ j r' x - ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x)) :=
        (iF'.sub iF0).const_mul _
      have iX : Integrable (fun x : ℝ × ℝ => (((r' - r0)⁻¹ : ℝ) : ℂ) *
          (((Θ (r', x) : ℝ) : ℂ) * Φ j r' x - ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x) -
            (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x) := iFF.sub iD0
      have hslope : slope (fun r => ∫ x : ℝ × ℝ, ((Θ (r, x) : ℝ) : ℂ) * Φ j r x) r0 r' =
          (((r' - r0)⁻¹ : ℝ) : ℂ) * ((∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) * Φ j r' x) -
            ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x) := by
        rw [slope_def_module, Complex.real_smul]
      have hJ : ∫ x : ℝ × ℝ, ((((r' - r0)⁻¹ : ℝ) : ℂ) *
          (((Θ (r', x) : ℝ) : ℂ) * Φ j r' x - ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x) -
            (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x -
            ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x)
          = (((r' - r0)⁻¹ : ℝ) : ℂ) * ((∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) * Φ j r' x) -
              ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x)
            - (∫ x : ℝ × ℝ, (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x)
            - ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x := by
        rw [integral_sub iX (iT0), integral_sub iFF iD0, integral_const_mul,
          integral_sub iF' iF0]
      have hpt : ∀ x : ℝ × ℝ, ((((r' - r0)⁻¹ : ℝ) : ℂ) *
          (((Θ (r', x) : ℝ) : ℂ) * Φ j r' x - ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x) -
            (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x -
            ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x)
          = ((Θ (r', x) : ℝ) : ℂ) *
              ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) +
            (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x +
            ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
              fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) * Φ j r0 x := by
        intro x
        push_cast
        ring
      have hsum : ∫ x : ℝ × ℝ, (((Θ (r', x) : ℝ) : ℂ) *
              ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) +
            (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x +
            ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
              fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) * Φ j r0 x)
          = (∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) *
              ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x)) +
            (∫ x : ℝ × ℝ, (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x) +
            ∫ x : ℝ × ℝ, ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
              fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) * Φ j r0 x := by
        have hI12 : Integrable (fun x : ℝ × ℝ =>
            ((Θ (r', x) : ℝ) : ℂ) * ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) +
              (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x) := I1.add I2
        rw [integral_add hI12 I3, integral_add I1 I2]
      calc slope (fun r => ∫ x : ℝ × ℝ, ((Θ (r, x) : ℝ) : ℂ) * Φ j r x) r0 r' -
            ((∫ x : ℝ × ℝ, (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x) +
              ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x)
          = (((r' - r0)⁻¹ : ℝ) : ℂ) * ((∫ x : ℝ × ℝ, ((Θ (r', x) : ℝ) : ℂ) * Φ j r' x) -
              ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x)
            - (∫ x : ℝ × ℝ, (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x)
            - ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x := by
              rw [hslope]; ring
        _ = ∫ x : ℝ × ℝ, ((((r' - r0)⁻¹ : ℝ) : ℂ) *
              (((Θ (r', x) : ℝ) : ℂ) * Φ j r' x - ((Θ (r0, x) : ℝ) : ℂ) * Φ j r0 x) -
                (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x -
                ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x) := hJ.symm
        _ = ∫ x : ℝ × ℝ, (((Θ (r', x) : ℝ) : ℂ) *
              ((((r' - r0)⁻¹ : ℝ) : ℂ) * (Φ j r' x - Φ j r0 x) - Φ (j + 1) r0 x) +
            (((Θ (r', x) : ℝ) : ℂ) - ((Θ (r0, x) : ℝ) : ℂ)) * Φ (j + 1) r0 x +
            ((((r' - r0)⁻¹ * (Θ (r', x) - Θ (r0, x)) -
              fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℝ)) : ℂ) * Φ j r0 x) := by
              congr 1
              funext x
              exact hpt x
        _ = _ := hsum
    -- the derivative: the punctured limit of the difference quotient
    have hfin : Tendsto (fun r' => slope (fun r => ∫ x : ℝ × ℝ, ((Θ (r, x) : ℝ) : ℂ) * Φ j r x)
        r0 r' - ((∫ x : ℝ × ℝ, (fderiv ℝ Θ (r0, x) (1, (0, 0)) : ℂ) * Φ j r0 x) +
          ∫ x : ℝ × ℝ, ((Θ (r0, x) : ℝ) : ℂ) * Φ (j + 1) r0 x)) (𝓝[≠] r0) (𝓝 0) := by
      have hs := (hE1.add hE2).add hE3
      rw [add_zero, add_zero] at hs
      refine Tendsto.congr' ?_ hs
      filter_upwards [hevI, hevN, hMVTC r0 1 one_pos] with r' h1 h2 h3
      exact (hid r' h1 h2 h3).symm
    rw [← tendsto_sub_nhds_zero_iff]
    exact hfin
  -- continuity of the derivative
  have hcont : ContinuousOn (fun r => (∫ x : ℝ × ℝ, (fderiv ℝ Θ (r, x) (1, (0, 0)) : ℂ) * Φ j r x) +
      ∫ x : ℝ × ℝ, ((Θ (r, x) : ℝ) : ℂ) * Φ (j + 1) r x) (Ioo t s) := by
    intro r0 hr0
    have hA := hContGen (fun p => fderiv ℝ Θ p (1, (0, 0))) j r0 hr0 hD1c hUD
      (fun p hp => hD0 p hp) MD hMD0 (fun p => hMD p)
    have hB := hContGen Θ (j + 1) r0 hr0 hΘc hUΘ (fun p hp => hΘ0 p hp) MΘ hMΘ0
      (fun p => hMΘ p)
    have hsum := hA.add hB
    rw [add_zero] at hsum
    rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
    exact hsum.congr (fun r => by ring)
  exact ⟨fun r hr => hder r hr, hcont⟩
