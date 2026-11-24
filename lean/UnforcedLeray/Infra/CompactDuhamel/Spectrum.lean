import UnforcedLeray.Infra.CompactDuhamel.Global
import UnforcedLeray.Infra.AnalyticFredholm
import UnforcedLeray.Infra.FiniteRankApprox
import UnforcedLeray.Infra.RieszProjection

/-!
# Essential spectrum of the period map and the choice of the weight

`paper/main.tex`, lines 340-357: "In the Calkin algebra, therefore,
`‖π(𝓜ⁿ)‖ ≤ C_h e^{-n𝒯/4}`, and `r_ess(𝓜) ≤ e^{-𝒯/4} < 1` … [Glück, Theorem 6.2.9] gives
finitely many spectral points outside each circle of radius larger than `e^{-𝒯/4}` … We may
choose `σ < β < 2σ < 1/2`, `{|ξ| = e^{β𝒯}} ∩ spec(𝓜) = ∅`."

The Calkin algebra is not needed: the period map is `𝓜 = S₀(P) + K` with `K` compact
(`isCompactOperator_evolution_sub`), hence a norm limit of finite-rank operators on a Hilbert
space (`FiniteRankApprox`), and `spectralRadius (S₀ P) ≤ e^{-κP}` from
`‖S₀(P)ⁿ‖ = ‖S₀(nP)‖ ≤ M e^{-κnP}`; the analytic Fredholm corollary
`finite_spectrum_add_inter_of_spectralRadius_lt` then gives the finiteness.

* `FreeSemigroupDecay D M κ`: `S₀` is a semigroup on `[0, ∞)` with `‖S₀ t‖ ≤ M e^{-κt}`
  (the `VolterraData` only bounds `S₀` on `[0, 1]`);
* `spectralRadius_S₀_le`: `spectralRadius ℂ (S₀ P) ≤ e^{-κP}`;
* `monodromy_decomposition`: `E(P,0) - S₀(P)` is compact and approximable;
* `finite_spectrum_monodromy_inter` (Part 3): `spectrum ℂ (E(P,0)) ∩ {r ≤ |z|}` is finite for
  every `r > e^{-κP}`;
* `exists_weight_sphere_subset_resolventSet` (abstract) and `exists_weight_monodromy` (Part 4):
  for `σ₁ < σ₂` with `e^{σ₁P} > e^{-κP}` there is `β ∈ (σ₁, σ₂)` with the circle
  `|z| = e^{βP}` in the resolvent set of `E(P,0)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real Metric
open scoped NNReal ENNReal

namespace UnforcedLeray.Infra.CompactDuhamel

open UnforcedLeray.Infra.VolterraEvolution UnforcedLeray.Infra.VolterraEvolution.VolterraData

section General

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The free evolution of `D` is a semigroup on `[0, ∞)` with exponential bound
`‖S₀ t‖ ≤ M e^{-κ t}` (`paper/main.tex`, line 297: "Its `X → X` norm is at most
`C_h e^{-s/4}`"). -/
structure FreeSemigroupDecay (D : VolterraData 𝕜 X Y) (M κ : ℝ) : Prop where
  S₀_comp_S₀ : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (D.S₀ a).comp (D.S₀ b) = D.S₀ (a + b)
  norm_S₀_le : ∀ t : ℝ, 0 ≤ t → ‖D.S₀ t‖ ≤ M * exp (-(κ * t))

variable {D : VolterraData 𝕜 X Y} {M κ : ℝ}

/-- `S₀(P)^{n+1} = S₀((n+1) P)`. -/
theorem FreeSemigroupDecay.pow_succ_eq (hF : FreeSemigroupDecay D M κ) {P : ℝ} (hP : 0 ≤ P)
    (n : ℕ) : D.S₀ P ^ (n + 1) = D.S₀ ((n + 1) * P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ContinuousLinearMap.mul_def, hF.S₀_comp_S₀ _ _ (by positivity) hP]
    congr 1
    push_cast
    ring

/-- `‖S₀(P)ⁿ‖ ≤ max M 1 · (e^{-κP})ⁿ`. -/
theorem FreeSemigroupDecay.norm_pow_le (hF : FreeSemigroupDecay D M κ) {P : ℝ} (hP : 0 ≤ P)
    (n : ℕ) : ‖D.S₀ P ^ n‖ ≤ max M 1 * exp (-(κ * P)) ^ n := by
  cases n with
  | zero =>
    rw [pow_zero, pow_zero, mul_one, ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
  | succ n =>
    rw [hF.pow_succ_eq hP n]
    refine (hF.norm_S₀_le _ (by positivity)).trans ?_
    have he : exp (-(κ * ((n + 1) * P))) = exp (-(κ * P)) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end General

section ComplexBanach

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] {D : VolterraData ℂ X Y} {M κ : ℝ}

/-- **Spectral radius of the free period map**: `spectralRadius ℂ (S₀ P) ≤ e^{-κP}` (on a
complex Banach space; from `‖S₀(P)ⁿ‖ ≤ max M 1 · e^{-κnP}`). -/
theorem spectralRadius_S₀_le (hF : FreeSemigroupDecay D M κ) {P : ℝ} (hP : 0 ≤ P) :
    spectralRadius ℂ (D.S₀ P) ≤ ENNReal.ofReal (exp (-(κ * P))) := by
  have hsub := RieszProjection.spectrum_subset_closedBall_of_norm_pow_le (D.S₀ P)
    (exp_pos _).le (hF.norm_pow_le hP)
  refine iSup₂_le fun k hk => ?_
  have hk' : ‖k‖ ≤ exp (-(κ * P)) := mem_closedBall_zero_iff.mp (hsub hk)
  exact ENNReal.coe_le_coe.mpr ((Real.le_toNNReal_iff_coe_le (exp_pos _).le).mpr hk')

end ComplexBanach

section Complex

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] {D : VolterraData ℂ X Y} {M κ : ℝ}

/-- **Decomposition of the period map** `𝓜 = E(P,0) = S₀(P) + K`: `K = E(P,0) - S₀(P)` is
compact and a norm limit of finite-rank operators, and `spectralRadius ℂ (S₀ P) ≤ e^{-κP}`. -/
theorem monodromy_decomposition (hD : D.Compatible) (hF : FreeSemigroupDecay D M κ)
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {P : ℝ} (hP : 0 ≤ P) :
    IsCompactOperator (D.evolution P 0 - D.S₀ P) ∧
      AnalyticFredholm.IsApproximable (D.evolution P 0 - D.S₀ P) ∧
      spectralRadius ℂ (D.S₀ P) ≤ ENNReal.ofReal (exp (-(κ * P))) := by
  have hcomp : IsCompactOperator (D.evolution P 0 - D.S₀ P) := by
    have := isCompactOperator_evolution_sub D hD hF.S₀_comp_S₀ hK hP
    simpa only [sub_zero] using this
  refine ⟨hcomp, ?_, spectralRadius_S₀_le hF hP⟩
  exact AnalyticFredholm.isApproximable_iff.mpr fun ε hε =>
    FiniteRankApprox.mem_approximable_iff.mp
      (FiniteRankApprox.mem_approximable_of_isCompactOperator hcomp) ε hε

/-- **Finite spectrum outside the essential spectral radius** (`paper/main.tex`,
lines 340-351). Let `X` be a complex Hilbert space and `D : VolterraData ℂ X Y` compatible,
with `S₀` a semigroup on `[0, ∞)`, `‖S₀ t‖ ≤ M e^{-κt}`, and `S t ∘ B r` compact for
`0 < t ≤ 1`. Then for the period map `𝓜 = E(P,0)` (`P ≥ 0`) and every `r > e^{-κP}`, the
spectrum of `𝓜` meets `{z | r ≤ |z|}` in a finite set. -/
theorem finite_spectrum_monodromy_inter (hD : D.Compatible) (hF : FreeSemigroupDecay D M κ)
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {P : ℝ} (hP : 0 ≤ P) {r : ℝ} (hr : exp (-(κ * P)) < r) :
    (spectrum ℂ (D.evolution P 0) ∩ {z : ℂ | r ≤ ‖z‖}).Finite := by
  obtain ⟨-, happrox, hrad⟩ := monodromy_decomposition hD hF hK hP
  have hr0 : 0 < r := (exp_pos _).trans hr
  have hρ : spectralRadius ℂ (D.S₀ P) < (r.toNNReal : ℝ≥0∞) :=
    hrad.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr0).mpr hr)
  have h := AnalyticFredholm.finite_spectrum_add_inter_of_spectralRadius_lt happrox hρ
  have hsum : D.S₀ P + (D.evolution P 0 - D.S₀ P) = D.evolution P 0 := by abel
  rw [hsum, Real.coe_toNNReal r hr0.le] at h
  exact h

end Complex

/-! ### Choice of the weight -/

section Weight

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **A spectrum-free circle of exponential radius.** If the spectrum of `a` has only finitely
many points with `|z| ≥ e^{σ₁P}` (`P > 0`), then for every `σ₂ > σ₁` some `β ∈ (σ₁, σ₂)` has
the circle `|z| = e^{βP}` in the resolvent set: only finitely many `β` are excluded, one for
each spectral point, namely `log |z| / P`. -/
theorem exists_weight_sphere_subset_resolventSet (a : A) {P σ₁ σ₂ : ℝ} (hP : 0 < P)
    (h12 : σ₁ < σ₂) (hfin : (spectrum ℂ a ∩ {z : ℂ | exp (σ₁ * P) ≤ ‖z‖}).Finite) :
    ∃ β ∈ Ioo σ₁ σ₂, sphere (0 : ℂ) (exp (β * P)) ⊆ resolventSet ℂ a := by
  have hbad := hfin.image (fun z : ℂ => Real.log ‖z‖ / P)
  obtain ⟨β, hβ, hβbad⟩ := ((Set.Ioo_infinite h12).sdiff hbad).nonempty
  refine ⟨β, hβ, fun z hz => ?_⟩
  rw [mem_sphere_zero_iff_norm] at hz
  by_contra hzs
  refine hβbad ⟨z, ⟨hzs, ?_⟩, ?_⟩
  · show exp (σ₁ * P) ≤ ‖z‖
    rw [hz]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ.1.le hP.le)
  · show Real.log ‖z‖ / P = β
    rw [hz, Real.log_exp, mul_div_cancel_right₀ _ hP.ne']

end Weight

section WeightMonodromy

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] {D : VolterraData ℂ X Y} {M κ : ℝ}

/-- **Choice of the weight** (`paper/main.tex`, lines 352-356, `σ < β < 2σ`,
`{|ξ| = e^{β𝒯}} ∩ spec(𝓜) = ∅`). Under the hypotheses of `finite_spectrum_monodromy_inter`,
with `P > 0` and `σ₁ < σ₂`, `e^{σ₁P} > e^{-κP}`, there is `β ∈ (σ₁, σ₂)` such that the circle
`|z| = e^{βP}` lies in the resolvent set of the period map `𝓜 = E(P,0)` (the hypothesis of
`RieszProjection.riesz_projection`), i.e. no spectral point has modulus `e^{βP}`. -/
theorem exists_weight_monodromy (hD : D.Compatible) (hF : FreeSemigroupDecay D M κ)
    (hK : ∀ t r : ℝ, 0 < t → t ≤ 1 → IsCompactOperator ((D.S t).comp (D.B r)))
    {P : ℝ} (hP : 0 < P) {σ₁ σ₂ : ℝ} (h12 : σ₁ < σ₂) (hσ : exp (-(κ * P)) < exp (σ₁ * P)) :
    ∃ β ∈ Ioo σ₁ σ₂, sphere (0 : ℂ) (exp (β * P)) ⊆ resolventSet ℂ (D.evolution P 0) ∧
      ∀ z ∈ spectrum ℂ (D.evolution P 0), ‖z‖ ≠ exp (β * P) := by
  obtain ⟨β, hβ, hsph⟩ := exists_weight_sphere_subset_resolventSet (D.evolution P 0) hP h12
    (finite_spectrum_monodromy_inter hD hF hK hP.le hσ)
  refine ⟨β, hβ, hsph, fun z hz hzn => hz (hsph ?_)⟩
  rw [mem_sphere_zero_iff_norm]
  exact hzn

end WeightMonodromy

end UnforcedLeray.Infra.CompactDuhamel
