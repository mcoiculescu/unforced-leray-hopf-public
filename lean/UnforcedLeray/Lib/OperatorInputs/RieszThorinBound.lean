import UnforcedLeray.Lib.OperatorInputs.RieszThorinCore

/-!
# Riesz–Thorin: the bilinear bound on step functions (helpers for ExternalInputs E10)


Grafakos, *Classical Fourier Analysis*, Thm. 1.3.4; blueprint units B0529, B0534, B0544
(`paper/main.tex` 3827–3856).

`core_bound`: with `1/p_j = s_j ∈ (0, 1]`, `θ ∈ [0, 1]`, `s = (1-θ)s₀ + θs₁ < 1` and `1/p = s`, for
operators `T₀, T₁, T` on `L^{p₀}, L^{p₁}, L^p` that agree on indicator atoms, and step functions
`f = Σᵢ 1_{Aᵢ} vᵢ`, `g = Σₖ 1_{Bₖ} wₖ` (disjoint finite-measure steps, nonzero values),

  `|∫ ⟪g, T f⟫| ≤ ‖T₀‖^{1-θ} ‖T₁‖^θ (Σᵢ ‖vᵢ‖^{1/s} μ(Aᵢ))^s (Σₖ ‖wₖ‖^{1/(1-s)} μ(Bₖ))^{1-s}`.

The proof is the three-lines argument described in `RieszThorinCore.lean`; an `L¹` endpoint
(`s_j = 1`, dual exponent `∞`) is handled by `endpoint_bound_one`.

No `sorry`, no axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Complex
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.ExternalInputs

namespace RieszThorin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The endpoint estimate in the form used on the lines `Re z = 0, 1`. -/
theorem endpoint_bound' {q : ℝ≥0∞} [Fact (1 ≤ q)] {sq : ℝ} (hsq0 : 0 < sq) (hsq1 : sq < 1)
    (hq : q = ENNReal.ofReal sq⁻¹) (S : Lp F q μ →L[ℂ] Lp F q μ)
    {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hAμ : ∀ i, μ (A i) ≠ ∞)
    (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → F) (hv : ∀ i, v i ≠ 0)
    {B : κ → Set α} (hB : ∀ k, MeasurableSet (B k)) (hBd : Pairwise (Function.onFun Disjoint B))
    (w : κ → F) (hw : ∀ k, w k ≠ 0) (Ψ : ι → α → F)
    (hΨ : ∀ i, Ψ i =ᵐ[μ] ⇑(S (indicatorConstLp q (hA i) (hAμ i) (v i)))) (ea eb : ℂ)
    {P Q : ℝ} (hea : ea.re * sq⁻¹ = P) (heb : eb.re * (1 - sq)⁻¹ = Q) :
    ‖∫ x, ⟪stepFun B (fun k => conj ((‖w k‖ : ℂ) ^ (eb - 1)) • w k) x,
        ∑ i, ((‖v i‖ : ℂ) ^ (ea - 1)) • Ψ i x⟫_ℂ ∂μ‖ₑ ≤
      (∑ k, ‖w k‖ₑ ^ Q * μ (B k)) ^ (1 - sq) *
        (‖S‖ₑ * (∑ i, ‖v i‖ₑ ^ P * μ (A i)) ^ sq) := by
  refine (endpoint_bound hsq0 hsq1 hq S hA hAμ hAd v hB hBd _ Ψ hΨ _).trans_eq ?_
  simp_rw [enorm_conj_cpow_smul_rpow (hw _), enorm_cpow_smul_rpow (hv _), hea, heb]

theorem norm_stepFun_le_one {E : Type*} [NormedAddCommGroup E] {B : κ → Set α}
    (hBd : Pairwise (Function.onFun Disjoint B)) (w : κ → E) (hw : ∀ k, ‖w k‖ ≤ 1) (x : α) :
    ‖stepFun B w x‖ ≤ 1 := by
  by_cases h : ∃ j, x ∈ B j
  · obtain ⟨j, hj⟩ := h
    rw [stepFun_apply_of_mem hBd w hj]
    exact hw j
  · push Not at h
    rw [stepFun_apply_of_forall_notMem w h, norm_zero]
    exact zero_le_one

/-- The endpoint estimate on `L¹` (`p_j = 1`, `p_j' = ∞`): on `Re z = j` the dual step function
has values of norm one, and Hölder becomes `|∫ ⟪g, φ⟫| ≤ ‖φ‖_{L¹}`. -/
theorem endpoint_bound_one (S : Lp F 1 μ →L[ℂ] Lp F 1 μ)
    {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hAμ : ∀ i, μ (A i) ≠ ∞)
    (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → F) (hv : ∀ i, v i ≠ 0)
    {B : κ → Set α} (hBd : Pairwise (Function.onFun Disjoint B))
    (w : κ → F) (hw : ∀ k, w k ≠ 0) (Ψ : ι → α → F)
    (hΨ : ∀ i, Ψ i =ᵐ[μ] ⇑(S (indicatorConstLp 1 (hA i) (hAμ i) (v i)))) (ea eb : ℂ)
    {P : ℝ} (hea : ea.re = P) (heb : eb.re = 0) :
    ‖∫ x, ⟪stepFun B (fun k => conj ((‖w k‖ : ℂ) ^ (eb - 1)) • w k) x,
        ∑ i, ((‖v i‖ : ℂ) ^ (ea - 1)) • Ψ i x⟫_ℂ ∂μ‖ₑ ≤
      ‖S‖ₑ * ∑ i, ‖v i‖ₑ ^ P * μ (A i) := by
  set a : ι → ℂ := fun i => (‖v i‖ : ℂ) ^ (ea - 1)
  have hw1 : ∀ k, ‖conj ((‖w k‖ : ℂ) ^ (eb - 1)) • w k‖ ≤ 1 := by
    intro k
    rw [norm_smul, RCLike.norm_conj, ← norm_smul, norm_cpow_smul (hw k), heb, Real.rpow_zero]
  have hφ : (fun x => ∑ i, a i • Ψ i x) =ᵐ[μ] ⇑(S (stepLp 1 A hA hAμ a v)) := by
    have hall : ∀ᵐ x ∂μ, ∀ i, Ψ i x = S (indicatorConstLp 1 (hA i) (hAμ i) (v i)) x :=
      ae_all_iff.2 hΨ
    filter_upwards [hall, coeFn_apply_stepLp S hA hAμ a v] with x h1 h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]
  calc ‖∫ x, ⟪stepFun B (fun k => conj ((‖w k‖ : ℂ) ^ (eb - 1)) • w k) x,
        ∑ i, a i • Ψ i x⟫_ℂ ∂μ‖ₑ
      ≤ ∫⁻ x, ‖⟪stepFun B (fun k => conj ((‖w k‖ : ℂ) ^ (eb - 1)) • w k) x,
          ∑ i, a i • Ψ i x⟫_ℂ‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ‖∑ i, a i • Ψ i x‖ₑ ∂μ := by
        refine lintegral_mono fun x => (enorm_inner_le_enorm_mul_enorm _ _).trans ?_
        refine (mul_le_of_le_one_left (zero_le) ?_)
        rw [← ofReal_norm, ENNReal.ofReal_le_one]
        exact norm_stepFun_le_one hBd _ hw1 x
    _ = ‖S (stepLp 1 A hA hAμ a v)‖ₑ := by
        rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_congr_ae hφ, Lp.enorm_def]
    _ ≤ ‖S‖ₑ * ‖stepLp 1 A hA hAμ a v‖ₑ := S.le_opENorm _
    _ = ‖S‖ₑ * ∑ i, ‖v i‖ₑ ^ P * μ (A i) := by
        rw [enorm_stepLp one_ne_zero ENNReal.one_ne_top hA hAμ hAd a v]
        simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have h := enorm_cpow_smul_rpow (hv i) ea 1
        rw [ENNReal.rpow_one, mul_one, hea] at h
        rw [h]

/-- Exponent algebra for the interpolated bound. -/
theorem interp_algebra {f g t₀ t₁ s₀ s₁ θ : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (hs : (1 - θ) * s₀ + θ * s₁ ≠ 0)
    (hs' : (1 - θ) * (1 - s₀) + θ * (1 - s₁) ≠ 0) :
    (g ^ (1 - s₀) * (t₀ * f ^ s₀)) ^ (1 - θ) * (g ^ (1 - s₁) * (t₁ * f ^ s₁)) ^ θ =
      t₀ ^ (1 - θ) * t₁ ^ θ * f ^ ((1 - θ) * s₀ + θ * s₁) *
        g ^ ((1 - θ) * (1 - s₀) + θ * (1 - s₁)) := by
  have hgp : ∀ e : ℝ, 0 ≤ g ^ e := fun e => Real.rpow_nonneg hg e
  have hfp : ∀ e : ℝ, 0 ≤ f ^ e := fun e => Real.rpow_nonneg hf e
  rw [Real.mul_rpow (hgp _) (mul_nonneg ht₀ (hfp _)), Real.mul_rpow ht₀ (hfp _),
    Real.mul_rpow (hgp _) (mul_nonneg ht₁ (hfp _)), Real.mul_rpow ht₁ (hfp _),
    Real.rpow_add' hf hs, Real.rpow_add' hg hs', mul_comm (1 - θ) s₀, mul_comm θ s₁,
    mul_comm (1 - θ) (1 - s₀), mul_comm θ (1 - s₁), Real.rpow_mul hf, Real.rpow_mul hf,
    Real.rpow_mul hg, Real.rpow_mul hg]
  ring

theorem sum_enorm_rpow_mul_ne_top {E : Type*} [NormedAddCommGroup E] {A : ι → Set α}
    (hAμ : ∀ i, μ (A i) ≠ ∞) (v : ι → E) {r : ℝ} (hr : 0 ≤ r) :
    ∑ i, ‖v i‖ₑ ^ r * μ (A i) ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr enorm_ne_top) (hAμ i)

/-- **The bilinear Riesz–Thorin bound on step functions** (Grafakos 1.3.4, the three-lines
step; B0529). The exponent `p` of `T` enters only through the consistency hypothesis; the
identification `p = 1/s` is used when the bound is converted into an operator norm bound. -/
theorem core_bound {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    {s₀ s₁ θ s : ℝ} (hs₀0 : 0 < s₀) (hs₀1 : s₀ ≤ 1) (hs₁0 : 0 < s₁) (hs₁1 : s₁ ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hs : s = (1 - θ) * s₀ + θ * s₁) (hs1 : s < 1)
    (hp₀ : p₀ = ENNReal.ofReal s₀⁻¹) (hp₁ : p₁ = ENNReal.ofReal s₁⁻¹)
    (T₀ : Lp F p₀ μ →L[ℂ] Lp F p₀ μ) (T₁ : Lp F p₁ μ →L[ℂ] Lp F p₁ μ)
    (T : Lp F p μ →L[ℂ] Lp F p μ)
    (hcons : ∀ (A : Set α) (hA : MeasurableSet A) (hAμ : μ A ≠ ∞) (v : F),
      (T (indicatorConstLp p hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v) ∧
      (T₁ (indicatorConstLp p₁ hA hAμ v) : α → F) =ᵐ[μ] T₀ (indicatorConstLp p₀ hA hAμ v))
    {A : ι → Set α} (hA : ∀ i, MeasurableSet (A i)) (hAμ : ∀ i, μ (A i) ≠ ∞)
    (hAd : Pairwise (Function.onFun Disjoint A)) (v : ι → F) (hv : ∀ i, v i ≠ 0)
    {B : κ → Set α} (hB : ∀ k, MeasurableSet (B k)) (hBμ : ∀ k, μ (B k) ≠ ∞)
    (hBd : Pairwise (Function.onFun Disjoint B)) (w : κ → F) (hw : ∀ k, w k ≠ 0) :
    ‖∫ x, ⟪stepFun B w x, T (stepLp p A hA hAμ 1 v) x⟫_ℂ ∂μ‖ ≤
      ‖T₀‖ ^ (1 - θ) * ‖T₁‖ ^ θ * (∑ i, ‖v i‖ₑ ^ s⁻¹ * μ (A i)).toReal ^ s *
        (∑ k, ‖w k‖ₑ ^ (1 - s)⁻¹ * μ (B k)).toReal ^ (1 - s) := by
  -- the interpolated exponent
  have hs0 : 0 < s := by
    rcases hθ0.eq_or_lt with h | h
    · subst h; rw [hs]; linarith
    · rw [hs]; nlinarith [mul_pos h hs₁0, mul_nonneg (sub_nonneg.2 hθ1) hs₀0.le]
  have hs1' : 0 < 1 - s := sub_pos.2 hs1
  -- the analytic family
  set α' := affExp s₀ s₁ s with hα'
  set β' := affExp (1 - s₀) (1 - s₁) (1 - s) with hβ'
  set Φ : ι → α → F := fun i => ⇑(T₀ (indicatorConstLp p₀ (hA i) (hAμ i) (v i))) with hΦ
  have hΦint : ∀ i k, IntegrableOn (Φ i) (B k) μ := fun i k =>
    integrableOn_of_memLp (Fact.out) (Lp.memLp _) (hBμ k)
  set c : ι → κ → ℂ := fun i k => ∫ x in B k, ⟪w k, Φ i x⟫_ℂ ∂μ with hc
  set H := rtFun (fun i => ‖v i‖) (fun k => ‖w k‖) c α' β' with hH
  have hrep : ∀ z, H z = ∫ x, ⟪stepFun B (fun k => conj ((‖w k‖ : ℂ) ^ (β' z - 1)) • w k) x,
      ∑ i, ((‖v i‖ : ℂ) ^ (α' z - 1)) • Φ i x⟫_ℂ ∂μ := by
    intro z
    rw [← sum_sum_eq_integral hB w Φ hΦint]
    rfl
  set Sf := ∑ i, ‖v i‖ₑ ^ s⁻¹ * μ (A i) with hSf
  set Sg := ∑ k, ‖w k‖ₑ ^ (1 - s)⁻¹ * μ (B k) with hSg
  have hSf_ne : Sf ≠ ∞ := sum_enorm_rpow_mul_ne_top hAμ v (inv_pos.2 hs0).le
  have hSg_ne : Sg ≠ ∞ := sum_enorm_rpow_mul_ne_top hBμ w (inv_pos.2 hs1').le
  -- the endpoint estimates
  have hend : ∀ {q : ℝ≥0∞} [Fact (1 ≤ q)] {sq : ℝ}, 0 < sq → sq ≤ 1 →
      q = ENNReal.ofReal sq⁻¹ → ∀ (S : Lp F q μ →L[ℂ] Lp F q μ),
      (∀ i, Φ i =ᵐ[μ] ⇑(S (indicatorConstLp q (hA i) (hAμ i) (v i)))) →
      ∀ z : ℂ, (α' z).re = sq / s → (β' z).re = (1 - sq) / (1 - s) →
      ‖H z‖ ≤ (Sg.toReal ^ (1 - sq) * (‖S‖ * Sf.toReal ^ sq)) := by
    intro q _ sq hsq0 hsq1' hq S hS z hα hβ
    rcases hsq1'.lt_or_eq with hsq1 | hsq1
    · have h := endpoint_bound' hsq0 hsq1 hq S hA hAμ hAd v hv hB hBd w hw Φ hS (α' z) (β' z)
        (P := s⁻¹) (Q := (1 - s)⁻¹) (by rw [hα]; field_simp)
        (by rw [hβ]; field_simp [(sub_pos.2 hsq1).ne'])
      rw [← hrep z] at h
      have hne : (Sg ^ (1 - sq) * (‖S‖ₑ * Sf ^ sq)) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (sub_pos.2 hsq1).le hSg_ne)
          (ENNReal.mul_ne_top enorm_ne_top (ENNReal.rpow_ne_top_of_nonneg hsq0.le hSf_ne))
      have h2 := ENNReal.toReal_mono hne h
      rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm,
        ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h2
      exact h2
    · subst hsq1
      have hq1 : q = 1 := by rw [hq, inv_one, ENNReal.ofReal_one]
      subst hq1
      have h := endpoint_bound_one S hA hAμ hAd v hv hBd w hw Φ hS (α' z) (β' z)
        (P := s⁻¹) (by rw [hα, one_div]) (by rw [hβ, sub_self, zero_div])
      rw [← hrep z] at h
      have hne : ‖S‖ₑ * Sf ≠ ∞ := ENNReal.mul_ne_top enorm_ne_top hSf_ne
      have h2 := ENNReal.toReal_mono hne h
      rw [toReal_enorm, ENNReal.toReal_mul, toReal_enorm] at h2
      rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_one]
      exact h2
  have h0 : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖H z‖ ≤ Sg.toReal ^ (1 - s₀) * (‖T₀‖ * Sf.toReal ^ s₀) := by
    intro z hz
    have hz' : z.re = 0 := hz
    exact hend hs₀0 hs₀1 hp₀ T₀ (fun i => EventuallyEq.rfl) z
      (by rw [hα', affExp_re, hz']; ring) (by rw [hβ', affExp_re, hz']; ring)
  have h1 : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖H z‖ ≤ Sg.toReal ^ (1 - s₁) * (‖T₁‖ * Sf.toReal ^ s₁) := by
    intro z hz
    have hz' : z.re = 1 := hz
    exact hend hs₁0 hs₁1 hp₁ T₁ (fun i => ((hcons (A i) (hA i) (hAμ i) (v i)).2).symm) z
      (by rw [hα', affExp_re, hz']; ring) (by rw [hβ', affExp_re, hz']; ring)
  -- the three-lines theorem
  have hdiff : Differentiable ℂ H :=
    differentiable_rtFun (fun i => norm_pos_iff.2 (hv i)) (fun k => norm_pos_iff.2 (hw k)) c
      (differentiable_affExp _ _ _) (differentiable_affExp _ _ _)
  have hbdd : BddAbove ((norm ∘ H) '' HadamardThreeLines.verticalClosedStrip 0 1) :=
    bddAbove_rtFun (fun i => norm_pos_iff.2 (hv i)) (fun k => norm_pos_iff.2 (hw k)) c
      (fun z h0 h1 => abs_affExp_re_sub_one_le hs0 h0 h1)
      (fun z h0 h1 => abs_affExp_re_sub_one_le hs1' h0 h1)
  have hθmem : (θ : ℂ) ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    change 0 ≤ (θ : ℂ).re ∧ (θ : ℂ).re ≤ 1
    simp only [ofReal_re]
    exact ⟨hθ0, hθ1⟩
  have h3 := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' H hθmem
    hdiff.diffContOnCl hbdd h0 h1
  simp only [ofReal_re] at h3
  -- the value at `θ`
  have hαθ : α' θ = 1 := by
    rw [hα', affExp_ofReal, ← hs, div_self hs0.ne', ofReal_one]
  have hβθ : β' θ = 1 := by
    rw [hβ', affExp_ofReal]
    have : (1 - θ) * (1 - s₀) + θ * (1 - s₁) = 1 - s := by rw [hs]; ring
    rw [this, div_self hs1'.ne', ofReal_one]
  have hval : H θ = ∫ x, ⟪stepFun B w x, T (stepLp p A hA hAμ 1 v) x⟫_ℂ ∂μ := by
    rw [hrep, hαθ, hβθ, sub_self]
    simp only [cpow_zero, map_one, one_smul]
    refine integral_congr_ae ?_
    have hall : ∀ᵐ x ∂μ, ∀ i, T (indicatorConstLp p (hA i) (hAμ i) (v i)) x = Φ i x :=
      ae_all_iff.2 fun i => (hcons (A i) (hA i) (hAμ i) (v i)).1
    filter_upwards [hall, coeFn_apply_stepLp T hA hAμ 1 v] with x h1 h2
    rw [h2]
    simp only [Pi.one_apply, one_smul, h1]
  rw [← hval]
  refine h3.trans_eq ?_
  have hexp : (1 - θ) * (1 - s₀) + θ * (1 - s₁) = 1 - s := by rw [hs]; ring
  rw [interp_algebra (f := Sf.toReal) (g := Sg.toReal) (t₀ := ‖T₀‖) (t₁ := ‖T₁‖)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg (norm_nonneg T₀) (norm_nonneg T₁)
    (by rw [← hs]; exact hs0.ne') (by rw [hexp]; exact hs1'.ne'), ← hs, hexp]

end RieszThorin

end UnforcedLeray.ExternalInputs
