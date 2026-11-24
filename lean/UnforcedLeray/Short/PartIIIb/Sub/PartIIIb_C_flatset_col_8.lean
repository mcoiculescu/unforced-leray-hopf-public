import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_2

/-!
# `PartIII-b:C/flatset/col/8`: `FlatForceDecay` from a decaying lattice-term bound

Source of record: `the November 2 reference manuscript`, lines 4594-4596, 4988
("the sums and their required derivatives converge by Gaussian decay"), 3426-3440 (the force of
the causal problem lies in `𝒯`).

On an age band `s₁ ≤ s ≤ s₂`, `s₁ > 0`, every lattice term of `f_A` at `x_j = (q - jc, η)` is
`≤ M_j/(1 + η²)` with `∑ M_j < ∞`, uniformly for `|q| ≤ c/2` and `B = B(s)` bounded
(`FlatTermDecay`); summing, `|f_A| ≤ (∑ M_j)/(1 + η²)` on the band (`flatForceDecay_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Decaying domination of the lattice terms** (source 4988, 4991: Gaussian decay): for `ν > 0`,
`0 < s₁` and bounds `X₀`, `Bb` there is a summable `M : ℤ → ℝ` with
`‖j-th term at (s, x)‖ ≤ M j / (1 + x₂²)` uniformly over `s ∈ [s₁,s₂]`, all matrices with entries
`≤ Bb`, `|x₁| ≤ X₀` and ALL `x₂`.  Route: as `Proofs/FlatTermBound.lean` (`ft_term_pt`: the term is
`≤ 13 Bb e^{-|y|²/(4a)}(1+|y|)³`, `y = x_j`, `1 ≤ a = 1 + νs ≤ a₂ = 1 + ν max(s₂,s₁)`), now
splitting `|y|² = (x₁ - jc)² + x₂²`, `(1+|y|)³ ≤ (1 + |x₁ - jc|)³(1 + |x₂|)³`:
`e^{-(x₁-jc)²/(4a)}(1+|x₁-jc|)³ ≤ e^{X₀²/4}(1+X₀)³(1+|jc|)³e^{-(jc)²/(8a₂)}` (`ft_E_bound`-type
estimate) and `(1 + x₂²)(1 + |x₂|)³ e^{-x₂²/(4a₂)} ≤ K` (a continuous function tending to `0`, or
`t^k e^{-t²/(4a₂)} ≤ (2k a₂)^{k/2}`); summability of `(1+|jc|)³ e^{-(jc)²/(8a₂)}` is
`gp_poly_summable`. -/
def FlatTermDecay : Prop :=
  ∀ (ν s₁ s₂ X₀ Bb : ℝ), 0 < ν → 0 < s₁ →
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ s ∈ Icc s₁ s₂, ∀ B : Mat3, (∀ a b, |B a b| ≤ Bb) →
      ∀ x : ℝ × ℝ, |x.1| ≤ X₀ → ∀ j : ℤ,
        ‖emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))‖ ≤
          M j / (1 + x.2 ^ 2)

theorem flatForceDecay_of (h1 : FlatBmatCont) (h2 : FlatTermDecay) : FlatForceDecay := by
  intro ν μ as χ A hν hχ hA s₁ s₂ hs₁
  have hBI : ContinuousOn (Bmat ν μ χ A) (Icc s₁ s₂) :=
    (h1 ν μ as χ A hχ hA).mono fun s hs => lt_of_lt_of_le hs₁ hs.1
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hBI
  obtain ⟨M, hMs, hM⟩ := h2 ν s₁ s₂ (cOf ν / 2) Cb hν hs₁
  refine ⟨∑' j, M j, fun s hs x hx i => ?_⟩
  set g : ℤ → Vec3 := fun j =>
    emb (fderiv ℝ (Vj ν s j) x (merApply (Bmat ν μ χ A s) (xj ν j x)))
      + mv (Bmat ν μ χ A s) (emb (Vj ν s j x)) with hg
  have hb : ∀ j, ‖g j‖ ≤ M j / (1 + x.2 ^ 2) := by
    intro j
    refine hM s hs (Bmat ν μ χ A s) (fun a b => ?_) x ?_ j
    · have h := ((norm_le_pi_norm ((Bmat ν μ χ A s) a) b).trans
        (norm_le_pi_norm ((Bmat ν μ χ A s)) a)).trans (hCb s hs)
      simpa [Real.norm_eq_abs] using h
    · exact abs_le.2 ⟨hx.1.1, hx.1.2.le⟩
  have hMs' : Summable (fun j => M j / (1 + x.2 ^ 2)) := hMs.div_const _
  have hgs : Summable (fun j => ‖g j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb hMs'
  have hF : ‖fA ν μ χ A s x‖ ≤ (∑' j, M j) / (1 + x.2 ^ 2) := by
    have e : fA ν μ χ A s x = -∑' j, g j := rfl
    rw [e, norm_neg]
    calc ‖∑' j, g j‖ ≤ ∑' j, ‖g j‖ := norm_tsum_le_tsum_norm hgs
      _ ≤ ∑' j, M j / (1 + x.2 ^ 2) := hgs.tsum_le_tsum hb hMs'
      _ = (∑' j, M j) / (1 + x.2 ^ 2) := tsum_div_const
  have hc : ‖forceC ν μ χ A (s, x) i‖ ≤ ‖fA ν μ χ A s x‖ := by
    simp only [forceC, NearInst.velC, Complex.norm_real]
    fin_cases i
    · simpa [merOf] using norm_le_pi_norm (fA ν μ χ A s x) 0
    · simpa [merOf] using norm_le_pi_norm (fA ν μ χ A s x) 2
  exact hc.trans hF

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
