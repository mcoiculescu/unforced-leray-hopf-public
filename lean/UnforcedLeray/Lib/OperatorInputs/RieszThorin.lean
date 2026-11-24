import UnforcedLeray.Lib.OperatorInputs.RieszThorinBound

/-!
# The Riesz–Thorin interpolation bound for one consistent operator (ExternalInputs E10)


(Grafakos, *Classical Fourier Analysis*, Thm. 1.3.4); Wave 1 block 1G part 4. Blueprint units
**B0529** (`paper/main.tex` 3827–3856, eq. `free-background-c-1`: interpolation of
`M B_loc (T_ε - T₀) M⁻¹` on `L^r(dm)` between `r = 2` and `r = 23/8`, at `p = 11/4`),
**B0534** (5251–5262) and **B0544** (5636–5646), which consume that bound.

Let `F` be a complex inner product space (for the manuscript, `ℂ³` or `ℂ`), `(α, μ)` any
measure space, `1 ≤ p₀, p₁ < ∞`, `θ ∈ [0, 1]` and `1/p = (1-θ)/p₀ + θ/p₁`. Let
`T₀ : L^{p₀} → L^{p₀}`, `T₁ : L^{p₁} → L^{p₁}` and `T : L^p → L^p` be bounded complex-linear
operators that agree on simple functions with finite-measure support. Then

  `‖T‖ ≤ ‖T₀‖^{1-θ} ‖T₁‖^θ`  (`norm_le_of_rieszThorin`).

As in the scoping note, `T` is assumed bounded a priori: the theorem compares norms and does not
construct the interpolated operator. This is the form used at B0529, where `T_ε` and `T₀` are
bounded on `H_{11/4}` by the graph theory (B0430, B0443). The agreement of the three
realizations on simple functions is B0430's "operators agree across `r`" and is a hypothesis
(`hcons`), to be proved for `M B_loc (T_ε - T₀) M⁻¹` (scoping note §6, risk 7).

Compared with the signature proposed in the scoping note: `[SigmaFinite μ]` and
`[FiniteDimensional ℂ F]` are not needed and are dropped; `θ ∈ [0, 1]` instead of `(0, 1)`; the
consistency hypothesis quantifies over simple functions `s` together with proofs that `s` lies
in the three `L^q` spaces (the proposed `s.toLp p` needs such a proof to typecheck). For simple
functions these memberships are equivalent to `μ (support s) < ∞`.

Proof: `RieszThorinCore.lean` and `RieszThorinBound.lean` (three lines on step functions,
including the `L¹` endpoints), `norm_le_of_forall_stepFun` (norming by step functions), density
of simple functions; the degenerate case `p = 1` (`p₀ = 1` or `p₁ = 1` with weight one, or both)
reduces to `T = T₀` or `T = T₁` (`norm_le_of_rieszThorin_degenerate`).

Main statements:
* `norm_le_of_forall_stepFun`: `L^p` norming by step functions, `1 < p < ∞`;
* `norm_apply_le_of_rieszThorin_of_indicator`: `‖T f‖ ≤ ‖T₀‖^{1-θ} ‖T₁‖^θ ‖f‖` for every `f`;
* `norm_le_of_rieszThorin_of_indicator`: the bound, with consistency on indicator atoms `1_A v`;
* `norm_le_of_rieszThorin`: the bound, with consistency on simple functions (the form of the
  scoping note; `θ ∈ (0, 1)` there, `θ ∈ [0, 1]` here).

The manuscript's instance `p₀ = 2`, `p₁ = 23/8`, `θ = 69/77`, `p = 11/4` is checked in
`rieszThorin_instance_exponents`.

No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Complex
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.ExternalInputs

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section Norming

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} [Fintype ι]

theorem integrable_inner_stepFun {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (w : ι → F)
    {φ : α → F} (hφ : ∀ i, IntegrableOn φ (A i) μ) :
    Integrable (fun x => ⟪stepFun A w x, φ x⟫_ℂ) μ := by
  have h : ∀ x, ⟪stepFun A w x, φ x⟫_ℂ = ∑ i, (A i).indicator (fun y => ⟪w i, φ y⟫_ℂ) x := by
    intro x
    unfold stepFun
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => inner_indicator_const _ _ _ _
  simp_rw [h]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_indicator_iff (hA i)).2 (Integrable.const_inner (𝕜 := ℂ) (w i) (hφ i))

/-- The pairing of a step function with itself, weighted: for disjoint steps,
`∫ ⟪Σₖ 1_{Bₖ} ‖wₖ‖^{P-2} wₖ, u⟫ = Σₖ ‖wₖ‖^P μ(Bₖ)` when `u = Σₖ 1_{Bₖ} wₖ` a.e. -/
theorem integral_inner_dual_stepFun {B : ι → Set α} (hB : ∀ k, MeasurableSet (B k))
    (hBd : Pairwise (Function.onFun Disjoint B)) (w : ι → F)
    (hw : ∀ k, w k ≠ 0) {u : α → F} (hu : u =ᵐ[μ] stepFun B w)
    (hui : ∀ k, IntegrableOn u (B k) μ) (P : ℝ) :
    ∫ x, ⟪stepFun B (fun k => ((‖w k‖ ^ (P - 2) : ℝ) : ℂ) • w k) x, u x⟫_ℂ ∂μ =
      ((∑ k, ‖w k‖ ^ P * μ.real (B k) : ℝ) : ℂ) := by
  rw [integral_inner_stepFun hB _ hui, ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∀ᵐ x ∂μ, x ∈ B k → ⟪((‖w k‖ ^ (P - 2) : ℝ) : ℂ) • w k, u x⟫_ℂ =
      ⟪((‖w k‖ ^ (P - 2) : ℝ) : ℂ) • w k, w k⟫_ℂ := by
    filter_upwards [hu] with x hx hxB
    rw [hx, stepFun_apply_of_mem hBd w hxB]
  have hr : 0 < ‖w k‖ := norm_pos_iff.2 (hw k)
  have : ‖w k‖ ^ (P - 2) * ‖w k‖ ^ 2 = ‖w k‖ ^ P := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    norm_num
  rw [setIntegral_congr_ae (hB k) hk, setIntegral_const, inner_smul_left, conj_ofReal,
    inner_self_eq_norm_sq_to_K, Complex.real_smul, ← this]
  push_cast
  ring_nf
  rfl

/-- **`L^p` norming by step functions** (`1 < p < ∞`, `s = 1/p`): if
`|∫ ⟪g, h⟫| ≤ C ‖g‖_{L^{p'}}` for every step function `g` with disjoint finite-measure steps and
nonzero values, then `‖h‖_{L^p} ≤ C`. The step functions are indexed by finsets of values. -/
theorem norm_le_of_forall_stepFun {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hp : p = ENNReal.ofReal s⁻¹) (h : Lp F p μ) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ (K : Finset F) (B : K → Set α) (_ : ∀ k, MeasurableSet (B k))
      (_ : ∀ k, μ (B k) ≠ ∞) (_ : Pairwise (Function.onFun Disjoint B)) (w : K → F),
      (∀ k, w k ≠ 0) →
        ‖∫ x, ⟪stepFun B w x, h x⟫_ℂ ∂μ‖ ≤
          C * (∑ k, ‖w k‖ₑ ^ (1 - s)⁻¹ * μ (B k)).toReal ^ (1 - s)) :
    ‖h‖ ≤ C := by
  have hp0 : p ≠ 0 := by
    rw [hp, Ne, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hs0
  have hpt : p ≠ ∞ := by rw [hp]; exact ENNReal.ofReal_ne_top
  have hpr : p.toReal = s⁻¹ := by rw [hp, ENNReal.toReal_ofReal (inv_pos.2 hs0).le]
  have hPQ : (s⁻¹).HolderConjugate (1 - s)⁻¹ := Real.HolderConjugate.inv_one_sub_inv hs0 hs1
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  -- the key estimate for one step function `u`
  have key : ∀ u : Lp.simpleFunc F p μ, ‖(u : Lp F p μ)‖ ≤ C + ‖(u : Lp F p μ) - h‖ := by
    intro u
    obtain ⟨K, B, hB, hBμ, hBd, hK, hu⟩ := exists_stepFun_ae_eq hp0 hpt u
    set w : K → F := fun k => (k : F)
    have hui : ∀ k, IntegrableOn (u : α → F) (B k) μ := fun k =>
      integrableOn_of_memLp (Fact.out) (Lp.memLp _) (hBμ k)
    have hhi : ∀ k, IntegrableOn (h : α → F) (B k) μ := fun k =>
      integrableOn_of_memLp (Fact.out) (Lp.memLp _) (hBμ k)
    set w' : K → F := fun k => ((‖w k‖ ^ (s⁻¹ - 2) : ℝ) : ℂ) • w k
    have hw' : ∀ k, w' k ≠ 0 := by
      intro k
      refine smul_ne_zero ?_ (hK k)
      exact ofReal_ne_zero.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 (hK k)) _).ne'
    set S := ∑ k, ‖w k‖ₑ ^ s⁻¹ * μ (B k)
    have hS_ne : S ≠ ∞ := RieszThorin.sum_enorm_rpow_mul_ne_top hBμ w (inv_pos.2 hs0).le
    -- the dual sum equals `S`
    have hSdual : ∑ k, ‖w' k‖ₑ ^ (1 - s)⁻¹ * μ (B k) = S := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hr : 0 < ‖w k‖ := norm_pos_iff.2 (hK k)
      have hnorm : ‖w' k‖ = ‖w k‖ ^ (s⁻¹ - 1) := by
        rw [norm_smul, norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
        rw [← Real.rpow_add_one hr.ne']
        congr 1
        ring
      rw [← ofReal_norm, ← ofReal_norm, hnorm,
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ENNReal.ofReal_rpow_of_pos hr,
        ← Real.rpow_mul hr.le]
      congr 3
      field_simp
    -- `‖u‖ = S^s`
    have hnorm_u : ‖(u : Lp F p μ)‖ = S.toReal ^ s := by
      rw [Lp.norm_def, eLpNorm_congr_ae hu, eLpNorm_stepFun hB hBd w hp0 hpt, hpr,
        ← ENNReal.toReal_rpow, one_div, inv_inv]
    -- `∫ ⟪g, u⟫ = S`
    have hpair : ∫ x, ⟪stepFun B w' x, (u : α → F) x⟫_ℂ ∂μ = ((S.toReal : ℝ) : ℂ) := by
      rw [integral_inner_dual_stepFun hB hBd w hK hu hui s⁻¹]
      congr 1
      rw [ENNReal.toReal_sum fun k _ => ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (inv_pos.2 hs0).le enorm_ne_top) (hBμ k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm, measureReal_def]
    -- splitting `u = h + (u - h)`
    have hsplit : ∫ x, ⟪stepFun B w' x, (u : α → F) x⟫_ℂ ∂μ =
        ∫ x, ⟪stepFun B w' x, (h : α → F) x⟫_ℂ ∂μ +
          ∫ x, ⟪stepFun B w' x, ((u : Lp F p μ) - h : Lp F p μ) x⟫_ℂ ∂μ := by
      rw [← integral_add (integrable_inner_stepFun hB w' hhi)
        (integrable_inner_stepFun hB w' fun k =>
          integrableOn_of_memLp (Fact.out) (Lp.memLp _) (hBμ k))]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (u : Lp F p μ) h] with x hx
      rw [hx, Pi.sub_apply, inner_sub_right]
      ring
    -- Hölder for the remainder
    have hrem : ‖∫ x, ⟪stepFun B w' x, ((u : Lp F p μ) - h : Lp F p μ) x⟫_ℂ ∂μ‖ ≤
        S.toReal ^ (1 - s) * ‖(u : Lp F p μ) - h‖ := by
      have h1 := enorm_integral_inner_stepFun_le hB hBd w'
        (Lp.aestronglyMeasurable ((u : Lp F p μ) - h)) hPQ
      rw [one_div, inv_inv, hSdual, ← hp] at h1
      have hne : S ^ (1 - s) * eLpNorm (((u : Lp F p μ) - h : Lp F p μ) : α → F) p μ ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hs1'.le hS_ne) (Lp.eLpNorm_ne_top _)
      have h2 := ENNReal.toReal_mono hne h1
      rw [toReal_enorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def] at h2
      exact h2
    have hmain := H K B hB hBμ hBd w' hw'
    rw [hSdual] at hmain
    have hle : S.toReal ≤ (C + ‖(u : Lp F p μ) - h‖) * S.toReal ^ (1 - s) := by
      have := congrArg norm hpair
      rw [norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, hsplit] at this
      calc S.toReal = _ := this.symm
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := by linarith
    rw [hnorm_u]
    rcases (ENNReal.toReal_nonneg (a := S)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hs0.ne']
      linarith [norm_nonneg ((u : Lp F p μ) - h)]
    · have hpow : S.toReal ^ s * S.toReal ^ (1 - s) = S.toReal := by
        rw [← Real.rpow_add hpos]
        simp
      have hpos' : 0 < S.toReal ^ (1 - s) := Real.rpow_pos_of_pos hpos _
      have : S.toReal ^ s * S.toReal ^ (1 - s) ≤
          (C + ‖(u : Lp F p μ) - h‖) * S.toReal ^ (1 - s) := by rw [hpow]; exact hle
      exact le_of_mul_le_mul_right this hpos'
  -- density of simple functions
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨u, hu⟩ := (Lp.simpleFunc.denseRange (E := F) (μ := μ) hpt).exists_dist_lt h
    (half_pos hε)
  rw [dist_eq_norm] at hu
  have h1 := key u
  have h2 : ‖h‖ ≤ ‖(u : Lp F p μ)‖ + ‖h - (u : Lp F p μ)‖ := by
    have := norm_add_le (u : Lp F p μ) (h - (u : Lp F p μ))
    rwa [add_sub_cancel] at this
  rw [← norm_neg ((u : Lp F p μ) - h), neg_sub] at h1
  linarith

end Norming

section Main

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Exponent bookkeeping for one endpoint: `1 ≤ q < ∞` gives `s = 1/q ∈ (0, 1]`,
`q = 1/s` and `q⁻¹ = s`. -/
theorem exponent_facts {q : ℝ≥0∞} (h1 : 1 ≤ q) (ht : q ≠ ∞) :
    0 < q.toReal⁻¹ ∧ q.toReal⁻¹ ≤ 1 ∧ q = ENNReal.ofReal (q.toReal⁻¹)⁻¹ ∧
      q⁻¹ = ENNReal.ofReal q.toReal⁻¹ := by
  have hq1 : 1 ≤ q.toReal := by
    have := ENNReal.toReal_mono ht h1
    simpa using this
  have hq0 : 0 < q.toReal := zero_lt_one.trans_le hq1
  refine ⟨inv_pos.2 hq0, inv_le_one_of_one_le₀ hq1, ?_, ?_⟩
  · rw [inv_inv, ENNReal.ofReal_toReal ht]
  · rw [ENNReal.ofReal_inv_of_pos hq0, ENNReal.ofReal_toReal ht]

/-- The interpolated exponent: `s = (1-θ)/p₀ + θ/p₁ ∈ (0, 1]` and `p = 1/s`. -/
theorem interp_exponent_facts {p₀ p₁ p : ℝ≥0∞} (h₀ : 1 ≤ p₀) (hp₀ : p₀ ≠ ∞) (h₁ : 1 ≤ p₁)
    (hp₁ : p₁ ≠ ∞) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    0 < (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ ∧ (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ ≤ 1 ∧
      p = ENNReal.ofReal ((1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹)⁻¹ := by
  obtain ⟨a0, a1, -, ha⟩ := exponent_facts h₀ hp₀
  obtain ⟨b0, b1, -, hb⟩ := exponent_facts h₁ hp₁
  set s₀ := p₀.toReal⁻¹
  set s₁ := p₁.toReal⁻¹
  have hs0 : 0 < (1 - θ) * s₀ + θ * s₁ := by
    rcases hθ0.eq_or_lt with h | h
    · subst h; linarith
    · nlinarith [mul_pos h b0, mul_nonneg (sub_nonneg.2 hθ1) a0.le]
  have hs1 : (1 - θ) * s₀ + θ * s₁ ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left a1 (sub_nonneg.2 hθ1), mul_le_mul_of_nonneg_left b1 hθ0]
  refine ⟨hs0, hs1, ?_⟩
  rw [ha, hb, ← ENNReal.ofReal_mul (sub_nonneg.2 hθ1), ← ENNReal.ofReal_mul hθ0,
    ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.2 hθ1) a0.le) (mul_nonneg hθ0 b0.le)] at hp
  rw [ENNReal.ofReal_inv_of_pos hs0, ← hp, inv_inv]

/-- Every simple function in `L^q` (`0 < q < ∞`) is a step element `Σᵢ 1_{Aᵢ} vᵢ`. -/
theorem exists_eq_stepLp {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) (u : Lp.simpleFunc F q μ) :
    ∃ (K : Finset F) (A : K → Set α) (hA : ∀ k, MeasurableSet (A k))
      (hAμ : ∀ k, μ (A k) ≠ ∞) (_ : Pairwise (Function.onFun Disjoint A)),
      (∀ k : K, (k : F) ≠ 0) ∧ (u : Lp F q μ) = stepLp q A hA hAμ 1 (fun k : K => (k : F)) := by
  obtain ⟨K, A, hA, hAμ, hAd, hK, hu⟩ := exists_stepFun_ae_eq hq0 hqt u
  refine ⟨K, A, hA, hAμ, hAd, hK, ?_⟩
  have h2 := coeFn_stepLp q hA hAμ 1 (fun k : K => (k : F))
  simp only [Pi.one_apply, one_smul] at h2
  exact Lp.ext (hu.trans h2.symm)

/-- Two bounded operators on `L^q` (`1 ≤ q < ∞`) that agree a.e. on indicator atoms are
equal (simple functions are dense). -/
theorem eq_of_indicatorConstLp {q : ℝ≥0∞} [Fact (1 ≤ q)] (hqt : q ≠ ∞)
    (S₁ S₂ : Lp F q μ →L[ℂ] Lp F q μ)
    (h : ∀ (A : Set α) (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F),
      (S₁ (indicatorConstLp q hA hAμ v) : α → F) =ᵐ[μ] S₂ (indicatorConstLp q hA hAμ v)) :
    S₁ = S₂ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  ext1 f
  refine (Lp.simpleFunc.denseRange (E := F) (μ := μ) hqt).induction_on f
    (isClosed_eq S₁.continuous S₂.continuous) ?_
  intro u
  obtain ⟨K, A, hA, hAμ, -, -, hu⟩ := exists_eq_stepLp hq0 hqt u
  rw [hu]
  simp only [stepLp, map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [Lp.ext (h (A i) (hA i) (hAμ i) (i : F))]

/-- The degenerate case `p = 1` of Riesz–Thorin: then `T` coincides with `T₀` or `T₁` on the same
space (`p₀ = 1` if `θ < 1`, `p₁ = 1` if `θ > 0`). -/
theorem norm_le_of_rieszThorin_degenerate {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
    [Fact (1 ≤ p)] {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hp₀1 : θ < 1 → p₀ = 1)
    (hp₁1 : 0 < θ → p₁ = 1) (hp1 : p = 1)
    (T₀ : Lp F p₀ μ →L[ℂ] Lp F p₀ μ) (T₁ : Lp F p₁ μ →L[ℂ] Lp F p₁ μ)
    (T : Lp F p μ →L[ℂ] Lp F p μ)
    (hcons : ∀ (A : Set α) (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F),
      (T (indicatorConstLp p hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v) ∧
      (T₁ (indicatorConstLp p₁ hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v)) :
    ‖T‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ := by
  subst hp1
  rcases hθ.2.lt_or_eq with hθ1 | hθ1
  · have h0 := hp₀1 hθ1
    subst h0
    have hT : T = T₀ := eq_of_indicatorConstLp ENNReal.one_ne_top T T₀
      (fun A hA hAμ v => (hcons A hA hAμ v).1)
    rcases hθ.1.eq_or_lt with hθ0 | hθ0
    · subst hθ0
      rw [hT, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    · have h1 := hp₁1 hθ0
      subst h1
      have hT1 : T₁ = T₀ := eq_of_indicatorConstLp ENNReal.one_ne_top T₁ T₀
        (fun A hA hAμ v => (hcons A hA hAμ v).2)
      rw [hT, hT1, ← Real.rpow_add' (norm_nonneg T₀) (by rw [sub_add_cancel]; exact one_ne_zero),
        sub_add_cancel, Real.rpow_one]
  · subst hθ1
    have h1 := hp₁1 one_pos
    subst h1
    have hT : T = T₁ := eq_of_indicatorConstLp ENNReal.one_ne_top T T₁
      (fun A hA hAμ v => (hcons A hA hAμ v).1.trans (hcons A hA hAμ v).2.symm)
    rw [hT, sub_self, Real.rpow_zero, Real.rpow_one, one_mul]

/-- **Riesz–Thorin, pointwise form** (Grafakos 1.3.4; B0529): `‖T f‖ ≤ ‖T₀‖^{1-θ} ‖T₁‖^θ ‖f‖`
for every `f ∈ L^p`, when `T, T₀, T₁` agree on indicator atoms `1_A v` (`μ A < ∞`). -/
theorem norm_apply_le_of_rieszThorin_of_indicator {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)]
    [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] (hp₀ : p₀ ≠ ∞) (hp₁ : p₁ ≠ ∞)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (T₀ : Lp F p₀ μ →L[ℂ] Lp F p₀ μ) (T₁ : Lp F p₁ μ →L[ℂ] Lp F p₁ μ)
    (T : Lp F p μ →L[ℂ] Lp F p μ)
    (hcons : ∀ (A : Set α) (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F),
      (T (indicatorConstLp p hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v) ∧
      (T₁ (indicatorConstLp p₁ hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v))
    (f : Lp F p μ) : ‖T f‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ * ‖f‖ := by
  obtain ⟨a0, a1, ha, -⟩ := exponent_facts (Fact.out : (1 : ℝ≥0∞) ≤ p₀) hp₀
  obtain ⟨b0, b1, hb, -⟩ := exponent_facts (Fact.out : (1 : ℝ≥0∞) ≤ p₁) hp₁
  obtain ⟨hs0, hs1', hps⟩ := interp_exponent_facts (Fact.out : (1 : ℝ≥0∞) ≤ p₀) hp₀
    (Fact.out : (1 : ℝ≥0∞) ≤ p₁) hp₁ hθ.1 hθ.2 hp
  set s := (1 - θ) * p₀.toReal⁻¹ + θ * p₁.toReal⁻¹ with hs
  have hM : 0 ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg T₀) _) (Real.rpow_nonneg (norm_nonneg T₁) _)
  rcases hs1'.lt_or_eq with hs1 | hs1
  swap
  · -- the degenerate case `p = 1`
    have hzero : (1 - θ) * (1 - p₀.toReal⁻¹) + θ * (1 - p₁.toReal⁻¹) = 0 := by linarith
    have hA0 : 0 ≤ (1 - θ) * (1 - p₀.toReal⁻¹) := mul_nonneg (sub_nonneg.2 hθ.2) (sub_nonneg.2 a1)
    have hB0 : 0 ≤ θ * (1 - p₁.toReal⁻¹) := mul_nonneg hθ.1 (sub_nonneg.2 b1)
    have hT : ‖T‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ := by
      refine norm_le_of_rieszThorin_degenerate hθ (fun hθ1 => ?_) (fun hθ0 => ?_) ?_ T₀ T₁ T
        hcons
      · have h : (1 - θ) * (1 - p₀.toReal⁻¹) = 0 := by linarith
        have h' : p₀.toReal⁻¹ = 1 := by
          rcases mul_eq_zero.1 h with h | h <;> linarith
        rw [ha, h', inv_one, ENNReal.ofReal_one]
      · have h : θ * (1 - p₁.toReal⁻¹) = 0 := by linarith
        have h' : p₁.toReal⁻¹ = 1 := by
          rcases mul_eq_zero.1 h with h | h <;> linarith
        rw [hb, h', inv_one, ENNReal.ofReal_one]
      · rw [hps, hs1, inv_one, ENNReal.ofReal_one]
    exact (T.le_opNorm f).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg f))
  have hp0 : p ≠ 0 := by
    rw [hps, Ne, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hs0
  have hpt : p ≠ ∞ := by rw [hps]; exact ENNReal.ofReal_ne_top
  have hpr : p.toReal = s⁻¹ := by rw [hps, ENNReal.toReal_ofReal (inv_pos.2 hs0).le]
  refine (Lp.simpleFunc.denseRange (E := F) (μ := μ) hpt).induction_on f
    (isClosed_le (continuous_norm.comp T.continuous) (continuous_const.mul continuous_norm)) ?_
  intro u
  obtain ⟨K, A, hA, hAμ, hAd, hK, hu'⟩ := exists_eq_stepLp hp0 hpt u
  rw [hu']
  have hnorm : ‖stepLp p A hA hAμ 1 (fun k : K => (k : F))‖ =
      (∑ k : K, ‖(k : F)‖ₑ ^ s⁻¹ * μ (A k)).toReal ^ s := by
    rw [← toReal_enorm, enorm_stepLp hp0 hpt hA hAμ hAd, hpr, ← ENNReal.toReal_rpow, one_div,
      inv_inv]
    simp only [Pi.one_apply, one_smul]
  refine norm_le_of_forall_stepFun hs0 hs1 hps _ (mul_nonneg hM (norm_nonneg _)) ?_
  intro K' B hB hBμ hBd w hw
  have h := RieszThorin.core_bound a0 a1 b0 b1 hθ.1 hθ.2 hs hs1 ha hb T₀ T₁ T hcons hA hAμ hAd
    (fun k : K => (k : F)) hK hB hBμ hBd w hw
  rw [hnorm]
  refine h.trans_eq ?_
  ring

/-- **Riesz–Thorin with consistency on indicator atoms** (Grafakos 1.3.4; B0529). -/
theorem norm_le_of_rieszThorin_of_indicator {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)]
    [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] (hp₀ : p₀ ≠ ∞) (hp₁ : p₁ ≠ ∞)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (T₀ : Lp F p₀ μ →L[ℂ] Lp F p₀ μ) (T₁ : Lp F p₁ μ →L[ℂ] Lp F p₁ μ)
    (T : Lp F p μ →L[ℂ] Lp F p μ)
    (hcons : ∀ (A : Set α) (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F),
      (T (indicatorConstLp p hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v) ∧
      (T₁ (indicatorConstLp p₁ hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v)) :
    ‖T‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ :=
  T.opNorm_le_bound
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg T₀) _) (Real.rpow_nonneg (norm_nonneg T₁) _))
    (norm_apply_le_of_rieszThorin_of_indicator hp₀ hp₁ hθ hp T₀ T₁ T hcons)

/-- The indicator atom `1_A v` as a simple function, in every `L^q`. -/
theorem indicatorConstLp_eq_toLp {A : Set α} (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F)
    (q : ℝ≥0∞)
    (hq : MemLp (SimpleFunc.piecewise A hA (SimpleFunc.const α v) (SimpleFunc.const α 0)) q μ) :
    hq.toLp _ = indicatorConstLp q hA hAμ v := by
  refine Lp.ext (hq.coeFn_toLp.trans (Filter.EventuallyEq.trans ?_ indicatorConstLp_coeFn.symm))
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ A <;> simp [SimpleFunc.piecewise_apply, hx]

theorem memLp_piecewise_const {A : Set α} (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F)
    (q : ℝ≥0∞) :
    MemLp (SimpleFunc.piecewise A hA (SimpleFunc.const α v) (SimpleFunc.const α 0)) q μ := by
  have h : ⇑(SimpleFunc.piecewise A hA (SimpleFunc.const α v) (SimpleFunc.const α 0)) =
      A.indicator fun _ => v := by
    funext x
    by_cases hx : x ∈ A <;> simp [SimpleFunc.piecewise_apply, hx]
  rw [h]
  exact memLp_indicator_const q hA v (Or.inr hAμ)

/-- **E10: Riesz–Thorin for one consistent operator** (scoping note §5.2 E10; Grafakos,
*Classical Fourier Analysis*, Thm. 1.3.4; B0529, `paper/main.tex` 3836–3850, eq.
`free-background-c-1`). Let `F` be a complex inner product space, `1 ≤ p₀, p₁ < ∞`,
`θ ∈ [0, 1]` and `1/p = (1-θ)/p₀ + θ/p₁`. If the bounded operators `T₀` on `L^{p₀}`, `T₁` on
`L^{p₁}` and `T` on `L^p` agree a.e. on every simple function lying in the three spaces, then
`‖T‖ ≤ ‖T₀‖^{1-θ} ‖T₁‖^θ`. -/
theorem norm_le_of_rieszThorin {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (hp₀ : p₀ ≠ ∞) (hp₁ : p₁ ≠ ∞)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (T₀ : Lp F p₀ μ →L[ℂ] Lp F p₀ μ) (T₁ : Lp F p₁ μ →L[ℂ] Lp F p₁ μ)
    (T : Lp F p μ →L[ℂ] Lp F p μ)
    (hcons : ∀ (s : SimpleFunc α F) (hs : MemLp s p μ) (hs₀ : MemLp s p₀ μ) (hs₁ : MemLp s p₁ μ),
      (T (hs.toLp s) : α → F) =ᵐ[μ] T₀ (hs₀.toLp s) ∧
        (T₀ (hs₀.toLp s) : α → F) =ᵐ[μ] T₁ (hs₁.toLp s)) :
    ‖T‖ ≤ ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ := by
  refine norm_le_of_rieszThorin_of_indicator hp₀ hp₁ hθ hp T₀ T₁ T ?_
  intro A hA hAμ v
  have h := hcons _ (memLp_piecewise_const hA hAμ v p) (memLp_piecewise_const hA hAμ v p₀)
    (memLp_piecewise_const hA hAμ v p₁)
  rw [indicatorConstLp_eq_toLp hA hAμ v p, indicatorConstLp_eq_toLp hA hAμ v p₀,
    indicatorConstLp_eq_toLp hA hAμ v p₁] at h
  exact ⟨h.1, h.2.symm⟩

/-- The exponents of the manuscript's instance (B0529, `paper/main.tex` 3843–3850):
`p₀ = 2`, `p₁ = 23/8`, `θ = 69/77` give `p = 11/4` (the `L²` weight is `1 - θ = 8/77`). -/
theorem rieszThorin_instance_exponents :
    ((11 / 4 : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (1 - 69 / 77) * (2 : ℝ≥0∞)⁻¹ +
        ENNReal.ofReal (69 / 77) * ((23 / 8 : ℝ≥0∞))⁻¹ := by
  have e1 : ((11 / 4 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (4 / 11) := by
    rw [show (4 / 11 : ℝ) = (11 / 4 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have e2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have e3 : ((23 / 8 : ℝ≥0∞))⁻¹ = ENNReal.ofReal (8 / 23) := by
    rw [show (8 / 23 : ℝ) = (23 / 8 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [e1, e2, e3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

end Main

end UnforcedLeray.ExternalInputs
