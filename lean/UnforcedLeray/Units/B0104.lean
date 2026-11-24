import UnforcedLeray.Units.B0104.Evolution
import UnforcedLeray.Units.B0104.Compactness
import UnforcedLeray.Units.B0104.Dyson
import UnforcedLeray.Units.B0104.Necessity

/-!
# B0104: compact Duhamel comparison on bounded intervals (`lem:compact-duhamel`)

Blueprint unit `B0104`, `paper/main.tex` lines 1586-1621 (statement 1586-1601, proof 1602-1621):

> On intervals of length at most `B`, let `F_n, F_0` be uniformly bounded free evolutions
> converging strongly, together with their adjoints, uniformly in both times and any auxiliary
> parameters. Let `A_n(t)` be strongly measurable, uniformly bounded interactions with
> `sup_t ‖A_n(t) - A_0(t)‖ → 0`, and suppose the family of limiting `A_0(t)`, including the
> auxiliary parameters, is a norm-precompact family of compact operators. Then the full
> evolutions `U_n`, defined by bounded-perturbation Duhamel iteration, converge strongly with
> their adjoints, and `sup_{t-s ≤ B} ‖(U_n - F_n)(t,s) - (U_0 - F_0)(t,s)‖ → 0`. All these
> conclusions have the same parameter uniformity.

## Formal setting

All operators act on one complex Hilbert space `H` (line 1584: "on one Hilbert space, after any
specified isometric ambient identification"). The auxiliary parameters range over an arbitrary
type `ι`; times are real; a *block* is a pair `(t,s)` with `s ≤ t ≤ s + B`. The sequence is
indexed by `n : ℕ` and its limit carries the subscript `₀` (`F₀`, `A₀`, `U₀`).

* `StrongTendstoOnBlocks B G G₀`: `G n (p,t,s) x → G₀ (p,t,s) x` for every `x`, uniformly over all
  parameters `p` and blocks;
* `NormTendstoOnBlocks B G G₀`: `sup_{p, blocks} ‖G n (p,t,s) - G₀ (p,t,s)‖ → 0`;
* `IsDuhamelEvolution B F A U` (`B0104/Evolution.lean`): `U` is the bounded strong solution of
  the Duhamel equation `U(t,s) = F(t,s) + ∫_s^t F(t,r) A(r) U(r,s) dr` on blocks, with Bochner
  integrable integrand. It is unique (`IsDuhamelEvolution.unique`), so it is the evolution
  "defined by bounded-perturbation Duhamel iteration".
* `IsDysonSum B F A U` (`B0104/Dyson.lean`): `U(t,s)x = Σ_k V_k(t,s)x`, the sum of the Dyson
  iterates `V₀ = F`, `V_{k+1}(t,s)x = ∫_s^t F(t,r) A(r) V_k(r,s)x dr`, under `DysonDefined B F A`
  (every iterated integrand is integrable, i.e. the iteration is defined). The Dyson terms obey
  the uniform exponential majorant `‖V_k(t,s)x‖ ≤ M (MK(t-s))^k/k! ‖x‖` (`norm_dysonTerm_le`,
  line 1608), the series converges to a bounded operator (`exists_isDysonSum`), and its sum is
  the Duhamel evolution (`IsDysonSum.isDuhamelEvolution`). `compact_duhamel_dyson` is the lemma
  with `U_n` given literally as Dyson sums.

The convergence `sup ‖A_n - A_0‖ → 0` is taken over the time and the auxiliary parameters (the
manuscript writes `sup_t`; uniformity in the parameters is what the parameter-uniform conclusion
and the application at lines 1680-1690, where `‖β R_f‖ = O(β_*)` uniformly in `β`, use).
This reading is forced: `exists_counterexample_pointwise_interaction` (`B0104/Necessity.lean`)
gives families on `ℂ²` satisfying every other hypothesis, with `A_n → A_0` uniformly in time for
each fixed parameter only, for which neither parameter-uniform conclusion holds.

The hypothesis "strongly measurable" on `A_n` is not needed separately: the integrability of the
Duhamel integrands, part of `IsDuhamelEvolution`, is all the proof uses. Omitting it only
weakens the hypotheses. The bound on `A₀` and the evolution law of `F_n` are not assumed either.

## Proof

* uniform exponential majorant `‖U_n(t,s)‖ ≤ 2 M e^{(2MK+1)B}` (`IsDuhamelEvolution.norm_le`,
  a Gronwall iteration replacing the termwise Dyson majorant);
* `W = {A₀(p,r)* u : ‖u‖ ≤ 1}` and `S = {A₀(p,r) v : ‖v‖ ≤ C_U}` are totally bounded
  (`totallyBounded_biUnion_image`, with Schauder's theorem `isCompactOperator_adjoint` proved by
  finite-rank approximation): this is the "finite norm-net … followed by finite-rank
  approximation" of lines 1613-1615;
* strong convergence of `F_n`, `F_n*` is uniform on `S`, `W`
  (`eventually_forall_mem_of_totallyBounded`);
* Gronwall on the reversed-order adjoint Duhamel identity (`adjoint_step`) gives
  `sup_{w ∈ W} ‖(U_n - U_0)(t,s)* w‖ → 0` uniformly (`tendsto_adjoint_on_W`, the adjoint-strong
  convergence of the right factors on the `v_j` of line 1610);
* integrating the Duhamel identity (`remainder_step`) gives the operator-norm convergence of the
  remainders, and the strong and adjoint-strong convergence of `U_n` follow from it and the
  hypotheses on `F_n`.

No free evolution is asserted to converge in operator norm.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace UnforcedLeray.B0104

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option linter.unusedSectionVars false

/-- Strong convergence `G n (p,t,s) → G₀ (p,t,s)`, uniform in the auxiliary parameter `p` and in
both times over the blocks `s ≤ t ≤ s + B` (`paper/main.tex` lines 1588-1590; unit `B0104`). -/
def StrongTendstoOnBlocks (B : ℝ) (G : ℕ → ι → ℝ → ℝ → H →L[ℂ] H)
    (G₀ : ι → ℝ → ℝ → H →L[ℂ] H) : Prop :=
  ∀ x : H, ∀ ε > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + B → ‖G n p t s x - G₀ p t s x‖ < ε

/-- Operator-norm convergence `sup_{p, s ≤ t ≤ s + B} ‖G n (p,t,s) - G₀ (p,t,s)‖ → 0`
(`paper/main.tex` line 1599; unit `B0104`). -/
def NormTendstoOnBlocks (B : ℝ) (G : ℕ → ι → ℝ → ℝ → H →L[ℂ] H)
    (G₀ : ι → ℝ → ℝ → H →L[ℂ] H) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + B → ‖G n p t s - G₀ p t s‖ < ε

/-- `StrongTendstoOnBlocks` is uniform convergence on the set of blocks, for every vector. -/
theorem strongTendstoOnBlocks_iff {B : ℝ} {G : ℕ → ι → ℝ → ℝ → H →L[ℂ] H}
    {G₀ : ι → ℝ → ℝ → H →L[ℂ] H} :
    StrongTendstoOnBlocks B G G₀ ↔ ∀ x : H,
      TendstoUniformlyOn (fun n (q : ι × ℝ × ℝ) => G n q.1 q.2.1 q.2.2 x)
        (fun q => G₀ q.1 q.2.1 q.2.2 x) atTop {q | q.2.2 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 + B} := by
  simp only [StrongTendstoOnBlocks, Metric.tendstoUniformlyOn_iff, dist_eq_norm, norm_sub_rev,
    mem_ofPred_eq, Prod.forall]
  refine forall_congr' fun x => forall₂_congr fun ε _ => ?_
  exact eventually_congr (Eventually.of_forall fun n => by
    exact ⟨fun h p t s hq => h p t s hq.1 hq.2, fun h p t s h1 h2 => h p t s ⟨h1, h2⟩⟩)

/-- `NormTendstoOnBlocks` is uniform operator-norm convergence on the set of blocks. -/
theorem normTendstoOnBlocks_iff {B : ℝ} {G : ℕ → ι → ℝ → ℝ → H →L[ℂ] H}
    {G₀ : ι → ℝ → ℝ → H →L[ℂ] H} :
    NormTendstoOnBlocks B G G₀ ↔
      TendstoUniformlyOn (fun n (q : ι × ℝ × ℝ) => G n q.1 q.2.1 q.2.2)
        (fun q => G₀ q.1 q.2.1 q.2.2) atTop {q | q.2.2 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 + B} := by
  simp only [NormTendstoOnBlocks, Metric.tendstoUniformlyOn_iff, dist_eq_norm, norm_sub_rev,
    mem_ofPred_eq, Prod.forall]
  refine forall₂_congr fun ε _ => ?_
  exact eventually_congr (Eventually.of_forall fun n => by
    exact ⟨fun h p t s hq => h p t s hq.1 hq.2, fun h p t s h1 h2 => h p t s ⟨h1, h2⟩⟩)

/-- The vectors `A₀(p,r) v`, `‖v‖ ≤ R`. -/
def ballImage (A₀ : ι → ℝ → H →L[ℂ] H) (R : ℝ) : Set H :=
  {v | ∃ p r, ∃ u : H, ‖u‖ ≤ R ∧ A₀ p r u = v}

/-- The vectors `A₀(p,r)* u`, `‖u‖ ≤ 1`. -/
def adjBallImage (A₀ : ι → ℝ → H →L[ℂ] H) : Set H :=
  {w | ∃ p r, ∃ u : H, ‖u‖ ≤ 1 ∧ ((A₀ p r)†) u = w}

theorem totallyBounded_ballImage {A₀ : ι → ℝ → H →L[ℂ] H}
    (hc : ∀ p r, IsCompactOperator (A₀ p r))
    (hp : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2)) (R : ℝ) :
    TotallyBounded (ballImage A₀ R) := by
  refine (totallyBounded_biUnion_image hp (by rintro _ ⟨q, rfl⟩; exact hc q.1 q.2) R).subset ?_
  rintro _ ⟨p, r, u, hu, rfl⟩
  exact mem_iUnion₂.2 ⟨A₀ p r, ⟨(p, r), rfl⟩, u, mem_closedBall_zero_iff.2 hu, rfl⟩

theorem totallyBounded_adjBallImage {A₀ : ι → ℝ → H →L[ℂ] H}
    (hc : ∀ p r, IsCompactOperator (A₀ p r))
    (hp : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2)) :
    TotallyBounded (adjBallImage A₀) := by
  refine (totallyBounded_biUnion_image (totallyBounded_adjoint_image hp) ?_ 1).subset ?_
  · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact isCompactOperator_adjoint (hc q.1 q.2)
  · rintro _ ⟨p, r, u, hu, rfl⟩
    exact mem_iUnion₂.2 ⟨((A₀ p r)†), ⟨A₀ p r, ⟨(p, r), rfl⟩, rfl⟩, u,
      mem_closedBall_zero_iff.2 hu, rfl⟩

/-- **Lemma `lem:compact-duhamel`** (`paper/main.tex` lines 1586-1621, blueprint unit `B0104`).

Let `H` be a complex Hilbert space, `B : ℝ`, and let `ι` index the auxiliary parameters. Let
`F n, F₀` be free evolutions, uniformly bounded on the blocks `s ≤ t ≤ s + B`, with `F n → F₀`
and `(F n)* → F₀*` strongly, uniformly in the parameter and both times. Let `A n` be uniformly
bounded interactions with `sup_{p,r} ‖A n p r - A₀ p r‖ → 0`, where `{A₀ p r}` is a
norm-totally-bounded family of compact operators. Let `U n`, `U₀` be the Duhamel evolutions of
`(F n, A n)` and `(F₀, A₀)`. Then, uniformly in the parameter and in both times on blocks,

1. `U n → U₀` strongly;
2. `(U n)* → U₀*` strongly;
3. `‖(U n - F n)(t,s) - (U₀ - F₀)(t,s)‖ → 0` in operator norm.

No operator-norm convergence of the free evolutions is assumed or asserted. -/
theorem compact_duhamel {B : ℝ}
    {F : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {F₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    {A : ℕ → ι → ℝ → H →L[ℂ] H} {A₀ : ι → ℝ → H →L[ℂ] H}
    {U : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {U₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : StrongTendstoOnBlocks B F F₀)
    (hFadj : StrongTendstoOnBlocks B (fun n p t s => ((F n p t s)†)) (fun p t s => ((F₀ p t s)†)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in atTop, ∀ p r, ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2))
    (hU : ∀ n, IsDuhamelEvolution B (F n) (A n) (U n)) (hU₀ : IsDuhamelEvolution B F₀ A₀ U₀) :
    StrongTendstoOnBlocks B U U₀ ∧
      StrongTendstoOnBlocks B (fun n p t s => ((U n p t s)†)) (fun p t s => ((U₀ p t s)†)) ∧
      NormTendstoOnBlocks B (fun n p t s => U n p t s - F n p t s)
        (fun p t s => U₀ p t s - F₀ p t s) := by
  obtain ⟨M₁, hFb⟩ := hFb
  obtain ⟨K₁, hAb⟩ := hAb
  obtain ⟨M, hM, hFn, hF0⟩ : ∃ M : ℝ, 0 ≤ M ∧
      (∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M) ∧
      (∀ p t s, s ≤ t → t ≤ s + B → ‖F₀ p t s‖ ≤ M) :=
    ⟨max M₁ 0, le_max_right _ _,
      fun n p t s h1 h2 => (hFb n p t s h1 h2).1.trans (le_max_left _ _),
      fun p t s h1 h2 => (hFb 0 p t s h1 h2).2.trans (le_max_left _ _)⟩
  obtain ⟨K, hK, hAn, hA0⟩ : ∃ K : ℝ, 0 ≤ K ∧ (∀ n p r, ‖A n p r‖ ≤ K) ∧
      (∀ p r, ‖A₀ p r‖ ≤ K) := by
    obtain ⟨n, hn⟩ := (hA 1 one_pos).exists
    refine ⟨max K₁ 0 + 1, by positivity,
      fun n p r => (hAb n p r).trans (by linarith [le_max_left K₁ 0]), fun p r => ?_⟩
    calc ‖A₀ p r‖ = ‖A n p r - (A n p r - A₀ p r)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A n p r‖ + ‖A n p r - A₀ p r‖ := norm_sub_le _ _
      _ ≤ K₁ + 1 := add_le_add (hAb n p r) (hn p r).le
      _ ≤ max K₁ 0 + 1 := by linarith [le_max_left K₁ 0]
  obtain ⟨CU, hCU, hUn, hU0⟩ : ∃ CU : ℝ, 0 ≤ CU ∧
      (∀ n p t s, s ≤ t → t ≤ s + B → ‖U n p t s‖ ≤ CU) ∧
      (∀ p t s, s ≤ t → t ≤ s + B → ‖U₀ p t s‖ ≤ CU) :=
    ⟨_, by positivity, fun n => (hU n).norm_le (hFn n) (hAn n), hU₀.norm_le hF0 hA0⟩
  have hS := totallyBounded_ballImage hA₀c hA₀p CU
  have hW := totallyBounded_adjBallImage hA₀c hA₀p
  have hW_norm : ∀ w ∈ adjBallImage A₀, ‖w‖ ≤ K := by
    rintro _ ⟨p, r, u, hu, rfl⟩
    calc ‖((A₀ p r)†) u‖ ≤ ‖A₀ p r‖ * ‖u‖ := norm_adjoint_apply_le _ _
      _ ≤ K * 1 := mul_le_mul (hA0 p r) hu (norm_nonneg _) hK
      _ = K := mul_one K
  -- Step Ψ: uniform convergence of `(U n - U₀)*` on `W`, by Gronwall.
  obtain ⟨CΨ, hCΨ, hΨ⟩ : ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ η > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t →
      t ≤ s + B → ∀ w ∈ adjBallImage A₀, ‖((U n p t s - U₀ p t s)†) w‖ ≤ CΨ * η := by
    by_cases hB : 0 ≤ B
    swap
    · exact ⟨0, le_rfl, fun η _ => Eventually.of_forall fun n p t s h1 h2 => by
        exfalso; linarith⟩
    refine ⟨2 * (1 + B * (CU * (M * K + K))) * exp ((2 * (M * K) + 1) * B), by positivity, ?_⟩
    intro η hη
    have h1 := eventually_forall_mem_of_totallyBounded (J := ι × ℝ × ℝ)
      (P := fun q => q.2.2 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 + B)
      (G := fun n q => ((F n q.1 q.2.1 q.2.2 - F₀ q.1 q.2.1 q.2.2)†)) (M := M + M)
      (fun n q hq => by
        rw [norm_adjoint_eq]
        exact (norm_sub_le _ _).trans (add_le_add (hFn n _ _ _ hq.1 hq.2) (hF0 _ _ _ hq.1 hq.2)))
      (fun x ε hε => by
        filter_upwards [hFadj x ε hε] with n hn q hq
        simpa only [map_sub, sub_apply] using hn q.1 q.2.1 q.2.2 hq.1 hq.2)
      hW η hη
    filter_upwards [h1, hA η hη] with n hn1 hn2
    intro p t s hst hts
    have ha : 0 ≤ η * (1 + B * (CU * (M * K + K))) := by positivity
    have G := gronwall_family (I := adjBallImage A₀)
      (fun w t' => ‖((U n p t' s - U₀ p t' s)†) (w : H)‖) (s := s) (B := B)
      (a := η * (1 + B * (CU * (M * K + K)))) (L := M * K) (C := (CU + CU) * K) ha
      (by positivity)
      (fun w t' h1 h2 => (norm_adjoint_apply_le _ _).trans (mul_le_mul
        ((norm_sub_le _ _).trans (add_le_add (hUn n p t' s h1 h2) (hU0 p t' s h1 h2)))
        (hW_norm w w.2) (norm_nonneg _) (by positivity)))
      (fun g hg t' h1 h2 hg0 hφ w => by
        have hstep := adjoint_step (hU n) hU₀ (p := p) h1 h2 (M := M) (K := K) (CU := CU)
          (η := η) (ρ := K) (fun r _ hr2 => hFn n p t' r hr2 (by linarith))
          (fun r _ hr2 => hF0 p t' r hr2 (by linarith)) (hA0 p)
          (fun r hr1 hr2 => hUn n p r s hr1 (by linarith)) (fun r => (hn2 p r).le)
          (hW_norm w w.2) (fun r _ hr2 => (hn1 (p, t', r) ⟨hr2, by linarith⟩ w w.2).le)
          (hg.intervalIntegrable _ _) hg0
          (fun r hr1 hr2 v => norm_apply_apply_le_of_unit (hg0 r hr1 hr2)
            (fun u hu => hφ ⟨_, ⟨p, r, u, hu, rfl⟩⟩ r hr1 hr2) v)
        have hle : (t' - s) * (CU * (M * K + K) * η) ≤ B * (CU * (M * K + K) * η) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        calc _ ≤ _ := hstep
          _ ≤ η * (1 + B * (CU * (M * K + K))) + M * K * ∫ r in s..t', g r := by
            nlinarith)
    intro w hw
    calc _ ≤ 2 * (η * (1 + B * (CU * (M * K + K)))) * exp ((2 * (M * K) + 1) * (t - s)) :=
          G ⟨w, hw⟩ t hst hts
      _ ≤ 2 * (η * (1 + B * (CU * (M * K + K)))) * exp ((2 * (M * K) + 1) * B) := by
          gcongr
          linarith
      _ = _ := by ring
  -- Step 3: operator-norm convergence of the Duhamel remainders.
  obtain ⟨C₃, h3⟩ : ∃ C₃ : ℝ, ∀ η > 0, ∀ᶠ n in atTop, ∀ p t s, s ≤ t → t ≤ s + B →
      ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ ≤ C₃ * η := by
    refine ⟨B * (M * CU + 1 + M * CΨ), fun η hη => ?_⟩
    have h1 := eventually_forall_mem_of_totallyBounded (J := ι × ℝ × ℝ)
      (P := fun q => q.2.2 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 + B)
      (G := fun n q => F n q.1 q.2.1 q.2.2 - F₀ q.1 q.2.1 q.2.2) (M := M + M)
      (fun n q hq =>
        (norm_sub_le _ _).trans (add_le_add (hFn n _ _ _ hq.1 hq.2) (hF0 _ _ _ hq.1 hq.2)))
      (fun x ε hε => by
        filter_upwards [hF x ε hε] with n hn q hq
        simpa only [sub_apply] using hn q.1 q.2.1 q.2.2 hq.1 hq.2)
      hS η hη
    filter_upwards [h1, hA η hη, hΨ η hη] with n hn1 hn2 hn3
    intro p t s hst hts
    have hB : 0 ≤ B := by linarith
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun x hx => ?_
    have hUx : ∀ r, s ≤ r → r ≤ t → ‖U n p r s x‖ ≤ CU := fun r hr1 hr2 =>
      ((U n p r s).le_opNorm x).trans (by rw [hx, mul_one]; exact hUn n p r s hr1 (by linarith))
    have hstep := remainder_step (hU n) hU₀ (p := p) hst hts (M := M) (η := η) (CU := CU)
      (ψ := CΨ * η) (fun r _ hr2 => hFn n p t r hr2 (by linarith))
      (fun r _ hr2 => hF0 p t r hr2 (by linarith)) (fun r => (hn2 p r).le) hUx
      (fun r hr1 hr2 => (hn1 (p, t, r) ⟨hr2, by linarith⟩ _
        ⟨p, r, U n p r s x, hUx r hr1 hr2, rfl⟩).le)
      (fun r hr1 hr2 => (norm_apply_apply_le_of_adjoint (by positivity)
        (fun u hu => hn3 p r s hr1 (by linarith) _ ⟨p, r, u, hu, rfl⟩) x).trans
          (by rw [hx, mul_one]))
    calc _ ≤ _ := hstep
      _ = (t - s) * ((M * CU + 1 + M * CΨ) * η) := by ring
      _ ≤ B * ((M * CU + 1 + M * CΨ) * η) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = B * (M * CU + 1 + M * CΨ) * η := by ring
  -- Conclusions.
  have hnorm : NormTendstoOnBlocks B (fun n p t s => U n p t s - F n p t s)
      (fun p t s => U₀ p t s - F₀ p t s) := by
    intro ε hε
    filter_upwards [h3 _ (small_pos (C := C₃) hε)] with n hn p t s h1 h2
    exact (hn p t s h1 h2).trans_lt (mul_div_small C₃ hε)
  refine ⟨fun x ε hε => ?_, fun y ε hε => ?_, hnorm⟩
  · have hpos : 0 < ε / 2 / (‖x‖ + 1) := by positivity
    filter_upwards [hF x (ε / 2) (half_pos hε), hnorm _ hpos] with n hn1 hn2 p t s h1 h2
    have hdec : U n p t s x - U₀ p t s x = (F n p t s x - F₀ p t s x) +
        ((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)) x := by
      simp only [sub_apply]; abel
    have hR : ‖((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)) x‖ ≤ ε / 2 := by
      calc _ ≤ ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε / 2 / (‖x‖ + 1) * ‖x‖ :=
            mul_le_mul_of_nonneg_right (hn2 p t s h1 h2).le (norm_nonneg _)
        _ ≤ ε / 2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg x]
    rw [hdec]
    calc _ ≤ ‖F n p t s x - F₀ p t s x‖ + ‖((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)) x‖ :=
          norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (hn1 p t s h1 h2) hR
      _ = ε := add_halves ε
  · have hpos : 0 < ε / 2 / (‖y‖ + 1) := by positivity
    filter_upwards [hFadj y (ε / 2) (half_pos hε), hnorm _ hpos] with n hn1 hn2 p t s h1 h2
    have hdec : ((U n p t s)†) y - ((U₀ p t s)†) y = (((F n p t s)†) y - ((F₀ p t s)†) y) +
        (((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s))†) y := by
      simp only [map_sub, sub_apply]; abel
    have hR : ‖(((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s))†) y‖ ≤ ε / 2 := by
      calc _ ≤ ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ * ‖y‖ :=
            norm_adjoint_apply_le _ _
        _ ≤ ε / 2 / (‖y‖ + 1) * ‖y‖ :=
            mul_le_mul_of_nonneg_right (hn2 p t s h1 h2).le (norm_nonneg _)
        _ ≤ ε / 2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg y]
    show ‖((U n p t s)†) y - ((U₀ p t s)†) y‖ < ε
    rw [hdec]
    calc _ ≤ ‖((F n p t s)†) y - ((F₀ p t s)†) y‖ +
          ‖(((U n p t s - F n p t s) - (U₀ p t s - F₀ p t s))†) y‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (hn1 p t s h1 h2) hR
      _ = ε := add_halves ε

/-- **Lemma `lem:compact-duhamel` with Dyson-series evolutions** (`paper/main.tex` lines
1586-1621, blueprint unit `B0104`). The hypotheses on `F n, F₀, A n, A₀` are those of
`compact_duhamel`; the full evolutions are the Dyson sums ("defined by bounded-perturbation
Duhamel iteration", line 1597), the iteration being defined on blocks (`DysonDefined`). Then,
uniformly in the parameter and in both times on blocks, `U n → U₀` strongly, `(U n)* → U₀*`
strongly, and `‖(U n - F n)(t,s) - (U₀ - F₀)(t,s)‖ → 0`. -/
theorem compact_duhamel_dyson {B : ℝ}
    {F : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {F₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    {A : ℕ → ι → ℝ → H →L[ℂ] H} {A₀ : ι → ℝ → H →L[ℂ] H}
    {U : ℕ → ι → ℝ → ℝ → H →L[ℂ] H} {U₀ : ι → ℝ → ℝ → H →L[ℂ] H}
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : StrongTendstoOnBlocks B F F₀)
    (hFadj : StrongTendstoOnBlocks B (fun n p t s => ((F n p t s)†)) (fun p t s => ((F₀ p t s)†)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in atTop, ∀ p r, ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2))
    (hD : ∀ n, DysonDefined B (F n) (A n)) (hD₀ : DysonDefined B F₀ A₀)
    (hU : ∀ n, IsDysonSum B (F n) (A n) (U n)) (hU₀ : IsDysonSum B F₀ A₀ U₀) :
    StrongTendstoOnBlocks B U U₀ ∧
      StrongTendstoOnBlocks B (fun n p t s => ((U n p t s)†)) (fun p t s => ((U₀ p t s)†)) ∧
      NormTendstoOnBlocks B (fun n p t s => U n p t s - F n p t s)
        (fun p t s => U₀ p t s - F₀ p t s) := by
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨K₁, hK₁⟩ := hAb
  obtain ⟨n₁, hn₁⟩ := (hA 1 one_pos).exists
  have hA₀b : ∀ p r, ‖A₀ p r‖ ≤ K₁ + 1 := fun p r =>
    calc ‖A₀ p r‖ = ‖A n₁ p r - (A n₁ p r - A₀ p r)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A n₁ p r‖ + ‖A n₁ p r - A₀ p r‖ := norm_sub_le _ _
      _ ≤ K₁ + 1 := add_le_add (hK₁ n₁ p r) (hn₁ p r).le
  exact compact_duhamel ⟨M, hM⟩ hF hFadj ⟨K₁, hK₁⟩ hA hA₀c hA₀p
    (fun n => (hU n).isDuhamelEvolution (fun p t s h1 h2 => (hM n p t s h1 h2).1) (hK₁ n) (hD n))
    (hU₀.isDuhamelEvolution (fun p t s h1 h2 => (hM 0 p t s h1 h2).2) hA₀b hD₀)

end UnforcedLeray.B0104
