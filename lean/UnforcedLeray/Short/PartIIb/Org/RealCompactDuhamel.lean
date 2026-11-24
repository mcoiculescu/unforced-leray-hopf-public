import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel.Evolution
import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel.Compactness
import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel.Dyson
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Compact Duhamel comparison over `RCLike 𝕜`, in particular over `ℝ` (`ORG:real-compact-duhamel`)

Source: `lem:short-compact-duhamel`, the November 2 reference manuscript
lines 978-1003, used for the Part II-b blocks at lines 2104-2166 (the free comparison 2104-2115,
"the common compact-Duhamel lemma gives `U(t+L,t) = W_{ν,t} e^{L L_{νt}} + o(1)`" 2141-2150).

> Fix a finite time length `B`. Suppose uniformly bounded free evolutions `F_n` converge strongly
> to `F_0`, and their adjoints converge strongly, uniformly in both times and any auxiliary
> parameters. Suppose the bounded strongly measurable interactions `A_n(t)` converge uniformly in
> operator norm to `A_0(t)`, and all the latter form a norm-precompact family of compact operators.
> The full evolutions `U_n` and their adjoints converge strongly, and
> `sup_{0 ≤ t-s ≤ B} ‖(U_n - F_n)(t,s) - (U_0 - F_0)(t,s)‖ → 0`.

The complex-field unit `UnforcedLeray.B0104` (`B0104.compact_duhamel`) proves this on a complex
Hilbert space; the Part II-b spaces `Xm m`, `Xmc c m` are real. This file is the same proof over
an arbitrary `RCLike` field `𝕜` (the scalar structure `[NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]`
is the one the Bochner integral needs; for `𝕜 = ℝ` it is the inner-product one), and with the
sequence `n → ∞` replaced by an arbitrary nontrivial filter `l`. No complexification is used: the
proof only needs Hilbert adjoints, Schauder's theorem (`isCompactOperator_adjoint`, by finite-rank
approximation) and Gronwall, all of which hold over `ℝ`.

* `compact_duhamel`: the lemma for Duhamel evolutions `IsDuhamelEvolution` on all blocks
  `s ≤ t ≤ s + B` (helpers ported in `RealCompactDuhamel/{Evolution,Compactness,Dyson}.lean`:
  `IsDuhamelEvolution.norm_le` (uniform exponential majorant), `IsDuhamelEvolution.unique`,
  `isCompactOperator_adjoint` (Schauder), the real Dyson series `exists_isDysonSum`,
  `IsDysonSum.isDuhamelEvolution`);
* `compact_duhamel_dyson`: the same with the evolutions given as Dyson sums;
* section `Window`, the forms used in Part II-b, where `Sc`, `Ac`, `U` live only on `[0, p.H]`:
  `IsDuhamelEvolutionOn a b` (Duhamel evolution on the blocks `a ≤ s ≤ t ≤ b`),
  `IsDuhamelEvolution.toOn`, `IsDuhamelEvolutionOn.ext` (clamped extension to all blocks),
  `IsDuhamelEvolutionOn.norm_le`, `IsDuhamelEvolutionOn.unique`, and `compact_duhamel_window`;
  the semigroup form `isDuhamelEvolution_of_semigroup` (`E τ = T τ + ∫_0^τ T(τ-r) A E r dr` gives
  the two-parameter evolution `(t,s) ↦ E(t-s)` of `(t,s) ↦ T(t-s)`, as for the frozen planar
  `E_pl σ`, `T_pl σ`), and `exists_norm_le_of_continuousOn` (uniform boundedness on compact time
  intervals);
* section `Real`: `real_compact_duhamel`, `real_compact_duhamel_window`, the statements with
  `𝕜 = ℝ` for the real spaces `Xm m`, `Xmc c m`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Real Metric MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace UnforcedLeray.Short.IIb.RCDuhamel

open UnforcedLeray.B0104 (gronwall_family mul_div_small small_pos)

variable {𝕜 : Type*} [RCLike 𝕜] {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] {N : Type*}

set_option linter.unusedSectionVars false

/-- Strong convergence `G n (p,t,s) → G₀ (p,t,s)`, uniform in the auxiliary parameter `p` and in
both times over the blocks `s ≤ t ≤ s + B` (SP 978–1003). -/
def StrongTendstoOnBlocks (l : Filter N) (B : ℝ) (G : N → ι → ℝ → ℝ → H →L[𝕜] H)
    (G₀ : ι → ℝ → ℝ → H →L[𝕜] H) : Prop :=
  ∀ x : H, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, s ≤ t → t ≤ s + B → ‖G n p t s x - G₀ p t s x‖ < ε

/-- Operator-norm convergence `sup_{p, s ≤ t ≤ s + B} ‖G n (p,t,s) - G₀ (p,t,s)‖ → 0`
(SP 978–1003). -/
def NormTendstoOnBlocks (l : Filter N) (B : ℝ) (G : N → ι → ℝ → ℝ → H →L[𝕜] H)
    (G₀ : ι → ℝ → ℝ → H →L[𝕜] H) : Prop :=
  ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, s ≤ t → t ≤ s + B → ‖G n p t s - G₀ p t s‖ < ε

/-- `StrongTendstoOnBlocks` is uniform convergence on the set of blocks, for every vector. -/
theorem strongTendstoOnBlocks_iff {l : Filter N} {B : ℝ} {G : N → ι → ℝ → ℝ → H →L[𝕜] H}
    {G₀ : ι → ℝ → ℝ → H →L[𝕜] H} :
    StrongTendstoOnBlocks l B G G₀ ↔ ∀ x : H,
      TendstoUniformlyOn (fun n (q : ι × ℝ × ℝ) => G n q.1 q.2.1 q.2.2 x)
        (fun q => G₀ q.1 q.2.1 q.2.2 x) l {q | q.2.2 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 + B} := by
  simp only [StrongTendstoOnBlocks, Metric.tendstoUniformlyOn_iff, dist_eq_norm, norm_sub_rev,
    mem_ofPred_eq, Prod.forall]
  refine forall_congr' fun x => forall₂_congr fun ε _ => ?_
  exact eventually_congr (Eventually.of_forall fun n => by
    exact ⟨fun h p t s hq => h p t s hq.1 hq.2, fun h p t s h1 h2 => h p t s ⟨h1, h2⟩⟩)

/-- `NormTendstoOnBlocks` is uniform operator-norm convergence on the set of blocks. -/
theorem normTendstoOnBlocks_iff {l : Filter N} {B : ℝ} {G : N → ι → ℝ → ℝ → H →L[𝕜] H}
    {G₀ : ι → ℝ → ℝ → H →L[𝕜] H} :
    NormTendstoOnBlocks l B G G₀ ↔
      TendstoUniformlyOn (fun n (q : ι × ℝ × ℝ) => G n q.1 q.2.1 q.2.2)
        (fun q => G₀ q.1 q.2.1 q.2.2) l {q | q.2.2 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 + B} := by
  simp only [NormTendstoOnBlocks, Metric.tendstoUniformlyOn_iff, dist_eq_norm, norm_sub_rev,
    mem_ofPred_eq, Prod.forall]
  refine forall₂_congr fun ε _ => ?_
  exact eventually_congr (Eventually.of_forall fun n => by
    exact ⟨fun h p t s hq => h p t s hq.1 hq.2, fun h p t s h1 h2 => h p t s ⟨h1, h2⟩⟩)

/-- The vectors `A₀(p,r) v`, `‖v‖ ≤ R`. -/
def ballImage (A₀ : ι → ℝ → H →L[𝕜] H) (R : ℝ) : Set H :=
  {v | ∃ p r, ∃ u : H, ‖u‖ ≤ R ∧ A₀ p r u = v}

/-- The vectors `A₀(p,r)* u`, `‖u‖ ≤ 1`. -/
def adjBallImage (A₀ : ι → ℝ → H →L[𝕜] H) : Set H :=
  {w | ∃ p r, ∃ u : H, ‖u‖ ≤ 1 ∧ ((A₀ p r)†) u = w}

theorem totallyBounded_ballImage {A₀ : ι → ℝ → H →L[𝕜] H}
    (hc : ∀ p r, IsCompactOperator (A₀ p r))
    (hp : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2)) (R : ℝ) :
    TotallyBounded (ballImage A₀ R) := by
  refine (totallyBounded_biUnion_image hp (by rintro _ ⟨q, rfl⟩; exact hc q.1 q.2) R).subset ?_
  rintro _ ⟨p, r, u, hu, rfl⟩
  exact mem_iUnion₂.2 ⟨A₀ p r, ⟨(p, r), rfl⟩, u, mem_closedBall_zero_iff.2 hu, rfl⟩

theorem totallyBounded_adjBallImage {A₀ : ι → ℝ → H →L[𝕜] H}
    (hc : ∀ p r, IsCompactOperator (A₀ p r))
    (hp : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2)) :
    TotallyBounded (adjBallImage A₀) := by
  refine (totallyBounded_biUnion_image (totallyBounded_adjoint_image hp) ?_ 1).subset ?_
  · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact isCompactOperator_adjoint (hc q.1 q.2)
  · rintro _ ⟨p, r, u, hu, rfl⟩
    exact mem_iUnion₂.2 ⟨((A₀ p r)†), ⟨A₀ p r, ⟨(p, r), rfl⟩, rfl⟩, u,
      mem_closedBall_zero_iff.2 hu, rfl⟩

/-- **Lemma `lem:short-compact-duhamel`** (SP 978–1003`lem:short-compact-duhamel`).

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
theorem compact_duhamel {l : Filter N} [l.NeBot] {B : ℝ}
    {F : N → ι → ℝ → ℝ → H →L[𝕜] H} {F₀ : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : N → ι → ℝ → H →L[𝕜] H} {A₀ : ι → ℝ → H →L[𝕜] H}
    {U : N → ι → ℝ → ℝ → H →L[𝕜] H} {U₀ : ι → ℝ → ℝ → H →L[𝕜] H}
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : StrongTendstoOnBlocks l B F F₀)
    (hFadj : StrongTendstoOnBlocks l B (fun n p t s => ((F n p t s)†)) (fun p t s => ((F₀ p t s)†)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in l, ∀ p r, ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2))
    (hU : ∀ n, IsDuhamelEvolution B (F n) (A n) (U n)) (hU₀ : IsDuhamelEvolution B F₀ A₀ U₀) :
    StrongTendstoOnBlocks l B U U₀ ∧
      StrongTendstoOnBlocks l B (fun n p t s => ((U n p t s)†)) (fun p t s => ((U₀ p t s)†)) ∧
      NormTendstoOnBlocks l B (fun n p t s => U n p t s - F n p t s)
        (fun p t s => U₀ p t s - F₀ p t s) := by
  obtain ⟨M₁, hFb⟩ := hFb
  obtain ⟨n₀⟩ := Filter.nonempty_of_neBot l
  obtain ⟨K₁, hAb⟩ := hAb
  obtain ⟨M, hM, hFn, hF0⟩ : ∃ M : ℝ, 0 ≤ M ∧
      (∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M) ∧
      (∀ p t s, s ≤ t → t ≤ s + B → ‖F₀ p t s‖ ≤ M) :=
    ⟨max M₁ 0, le_max_right _ _,
      fun n p t s h1 h2 => (hFb n p t s h1 h2).1.trans (le_max_left _ _),
      fun p t s h1 h2 => (hFb n₀ p t s h1 h2).2.trans (le_max_left _ _)⟩
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
  obtain ⟨CΨ, hCΨ, hΨ⟩ : ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ η > 0, ∀ᶠ n in l, ∀ p t s, s ≤ t →
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
  obtain ⟨C₃, h3⟩ : ∃ C₃ : ℝ, ∀ η > 0, ∀ᶠ n in l, ∀ p t s, s ≤ t → t ≤ s + B →
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
  have hnorm : NormTendstoOnBlocks l B (fun n p t s => U n p t s - F n p t s)
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

/-- **Lemma `lem:short-compact-duhamel` with Dyson-series evolutions** (SP 978-1003). The hypotheses on `F n, F₀, A n, A₀` are those of
`compact_duhamel`; the full evolutions are the Dyson sums ("defined by bounded-perturbation
Duhamel iteration", SP 991-992), the iteration being defined on blocks (`DysonDefined`). Then,
uniformly in the parameter and in both times on blocks, `U n → U₀` strongly, `(U n)* → U₀*`
strongly, and `‖(U n - F n)(t,s) - (U₀ - F₀)(t,s)‖ → 0`. -/
theorem compact_duhamel_dyson {l : Filter N} [l.NeBot] {B : ℝ}
    {F : N → ι → ℝ → ℝ → H →L[𝕜] H} {F₀ : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : N → ι → ℝ → H →L[𝕜] H} {A₀ : ι → ℝ → H →L[𝕜] H}
    {U : N → ι → ℝ → ℝ → H →L[𝕜] H} {U₀ : ι → ℝ → ℝ → H →L[𝕜] H}
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : StrongTendstoOnBlocks l B F F₀)
    (hFadj : StrongTendstoOnBlocks l B (fun n p t s => ((F n p t s)†)) (fun p t s => ((F₀ p t s)†)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in l, ∀ p r, ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2))
    (hD : ∀ n, DysonDefined B (F n) (A n)) (hD₀ : DysonDefined B F₀ A₀)
    (hU : ∀ n, IsDysonSum B (F n) (A n) (U n)) (hU₀ : IsDysonSum B F₀ A₀ U₀) :
    StrongTendstoOnBlocks l B U U₀ ∧
      StrongTendstoOnBlocks l B (fun n p t s => ((U n p t s)†)) (fun p t s => ((U₀ p t s)†)) ∧
      NormTendstoOnBlocks l B (fun n p t s => U n p t s - F n p t s)
        (fun p t s => U₀ p t s - F₀ p t s) := by
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨n₀⟩ := Filter.nonempty_of_neBot l
  obtain ⟨K₁, hK₁⟩ := hAb
  obtain ⟨n₁, hn₁⟩ := (hA 1 one_pos).exists
  have hA₀b : ∀ p r, ‖A₀ p r‖ ≤ K₁ + 1 := fun p r =>
    calc ‖A₀ p r‖ = ‖A n₁ p r - (A n₁ p r - A₀ p r)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A n₁ p r‖ + ‖A n₁ p r - A₀ p r‖ := norm_sub_le _ _
      _ ≤ K₁ + 1 := add_le_add (hK₁ n₁ p r) (hn₁ p r).le
  exact compact_duhamel ⟨M, hM⟩ hF hFadj ⟨K₁, hK₁⟩ hA hA₀c hA₀p
    (fun n => (hU n).isDuhamelEvolution (fun p t s h1 h2 => (hM n p t s h1 h2).1) (hK₁ n) (hD n))
    (hU₀.isDuhamelEvolution (fun p t s h1 h2 => (hM n₀ p t s h1 h2).2) hA₀b hD₀)


/-! ## Window and semigroup forms (the Part II-b applications, SP 2104-2166)

In Part II-b the free cylinder propagator `Sc`, the interactions `Ac` and the coupled propagator
`U` are given only on the window `[0, p.H]`, and the frozen planar evolutions are one-parameter
families `T_pl σ τ`, `E_pl σ τ`. `compact_duhamel_window` is the lemma for families given only on
the blocks `a ≤ s ≤ t ≤ b` of a window: it extends them to all blocks by clamping both times to
`[a, b]` and cutting the interaction off outside `[a, b]`, which preserves the Duhamel identity.
`isDuhamelEvolution_of_semigroup` turns a mild equation `E τ = T τ + ∫_0^τ T(τ-r) A E r dr` into the
two-parameter Duhamel evolution `(t,s) ↦ E(t-s)` of `(t,s) ↦ T(t-s)` (SP 2147-2150: the frozen
evolution `e^{L L_{νt}}` and the frozen radial transport). -/

section Window

/-- `t` clamped to the window `[a, b]`. -/
def clampW (a b t : ℝ) : ℝ := max a (min t b)

theorem le_clampW (a b t : ℝ) : a ≤ clampW a b t := le_max_left _ _

theorem clampW_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clampW a b t ≤ b :=
  max_le hab (min_le_right _ _)

theorem clampW_mono {a b s t : ℝ} (hst : s ≤ t) : clampW a b s ≤ clampW a b t :=
  max_le_max le_rfl (min_le_min hst le_rfl)

theorem clampW_of_mem {a b t : ℝ} (ht1 : a ≤ t) (ht2 : t ≤ b) : clampW a b t = t := by
  simp only [clampW, min_eq_left ht2, max_eq_right ht1]

/-- `U` is the Duhamel evolution of `(F, A)` on the window `a ≤ s ≤ t ≤ b`: the Duhamel integrand
is integrable, the Duhamel identity holds and `U(·, s)` is bounded, on the blocks of the window. -/
structure IsDuhamelEvolutionOn (a b : ℝ) (F : ι → ℝ → ℝ → H →L[𝕜] H) (A : ι → ℝ → H →L[𝕜] H)
    (U : ι → ℝ → ℝ → H →L[𝕜] H) : Prop where
  integrable : ∀ p s t, a ≤ s → s ≤ t → t ≤ b → ∀ x : H,
    IntervalIntegrable (fun r => F p t r (A p r (U p r s x))) volume s t
  duhamel : ∀ p s t, a ≤ s → s ≤ t → t ≤ b → ∀ x : H,
    U p t s x = F p t s x + ∫ r in s..t, F p t r (A p r (U p r s x))
  bounded : ∀ p s, a ≤ s → s ≤ b → ∃ C, ∀ t, s ≤ t → t ≤ b → ‖U p t s‖ ≤ C

/-- A Duhamel evolution on all blocks of length `b - a` is one on the window `[a, b]`. -/
theorem IsDuhamelEvolution.toOn {a b : ℝ} {F : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : ι → ℝ → H →L[𝕜] H} {U : ι → ℝ → ℝ → H →L[𝕜] H}
    (hU : IsDuhamelEvolution (b - a) F A U) : IsDuhamelEvolutionOn a b F A U where
  integrable p s t h1 h2 h3 x := hU.integrable p s t h2 (by linarith) x
  duhamel p s t h1 h2 h3 x := hU.duhamel p s t h2 (by linarith) x
  bounded p s _ _ := by
    obtain ⟨C, hC⟩ := hU.bounded p s
    exact ⟨C, fun t h3 h4 => hC t h3 (by linarith)⟩

theorem clampW_eq_of_not_le {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t)
    (h : ¬ max a s ≤ min b t) : clampW a b s = clampW a b t := by
  simp only [clampW, max_def, min_def] at h ⊢
  split_ifs at h ⊢ <;> linarith

theorem integral_indicator_Icc_eq {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t) (h : ℝ → H) :
    ∫ r in s..t, (Icc a b).indicator h r = ∫ r in clampW a b s..clampW a b t, h r := by
  rw [intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Icc_inter_Icc]
  by_cases hne : max a s ≤ min b t
  · have hsb : s ≤ b := (le_max_right a s).trans (hne.trans (min_le_left b t))
    have hat : a ≤ t := (le_max_left a s).trans (hne.trans (min_le_right b t))
    have hs : clampW a b s = max a s := by simp only [clampW, min_eq_left hsb]
    have ht : clampW a b t = min b t := by
      simp only [clampW]
      rw [max_eq_right (le_min hat hab), min_comm]
    rw [hs, ht, intervalIntegral.integral_of_le hne, integral_Icc_eq_integral_Ioc]
  · rw [Icc_eq_empty hne, Measure.restrict_empty, integral_zero_measure,
      clampW_eq_of_not_le hab hst hne, intervalIntegral.integral_same]

theorem intervalIntegrable_indicator_Icc {a b s t : ℝ} (hst : s ≤ t) {h : ℝ → H}
    (hh : IntervalIntegrable h volume (clampW a b s) (clampW a b t)) :
    IntervalIntegrable ((Icc a b).indicator h) volume s t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (clampW_mono hst)] at hh
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Icc]
  have hsub : Icc a b ∩ Ioc s t ⊆ Icc (clampW a b s) (clampW a b t) := by
    rintro r ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨max_le h1 ((min_le_left _ _).trans h3.le), le_max_of_le_right (le_min h4 h2)⟩
  exact ((integrableOn_Icc_iff_integrableOn_Ioc (f := h) (a := clampW a b s) (b := clampW a b t)
    enorm_ne_top).2 hh).mono_set hsub

/-- Window families extended to all times: both times clamped to `[a, b]`. -/
def extW (a b : ℝ) (G : ι → ℝ → ℝ → H →L[𝕜] H) : ι → ℝ → ℝ → H →L[𝕜] H :=
  fun p t s => G p (clampW a b t) (clampW a b s)

/-- Window interactions extended by zero outside `[a, b]`. -/
def extA (a b : ℝ) (A : ι → ℝ → H →L[𝕜] H) : ι → ℝ → H →L[𝕜] H :=
  fun p r => (Icc a b).indicator (A p) r

theorem extW_integrand (a b : ℝ) (F U : ι → ℝ → ℝ → H →L[𝕜] H) (A : ι → ℝ → H →L[𝕜] H)
    (p : ι) (t s : ℝ) (x : H) :
    (fun r => extW a b F p t r (extA a b A p r (extW a b U p r s x))) =
      (Icc a b).indicator (fun r => F p (clampW a b t) r (A p r (U p r (clampW a b s) x))) := by
  funext r
  by_cases hr : r ∈ Icc a b
  · simp only [extW, extA, Set.indicator_of_mem hr, clampW_of_mem hr.1 hr.2]
  · simp only [extW, extA, Set.indicator_of_notMem hr, zero_apply, map_zero]

/-- The clamped extension of a window Duhamel evolution is a Duhamel evolution on all blocks. -/
theorem IsDuhamelEvolutionOn.ext {a b : ℝ} (hab : a ≤ b) {F : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : ι → ℝ → H →L[𝕜] H} {U : ι → ℝ → ℝ → H →L[𝕜] H}
    (hU : IsDuhamelEvolutionOn a b F A U) :
    IsDuhamelEvolution (b - a) (extW a b F) (extA a b A) (extW a b U) where
  integrable p s t hst _ x := by
    rw [extW_integrand]
    exact intervalIntegrable_indicator_Icc hst
      (hU.integrable p _ _ (le_clampW a b s) (clampW_mono hst) (clampW_le hab t) x)
  duhamel p s t hst _ x := by
    rw [extW_integrand, integral_indicator_Icc_eq hab hst]
    exact hU.duhamel p _ _ (le_clampW a b s) (clampW_mono hst) (clampW_le hab t) x
  bounded p s := by
    obtain ⟨C, hC⟩ := hU.bounded p (clampW a b s) (le_clampW a b s) (clampW_le hab s)
    exact ⟨C, fun t hst _ => hC _ (clampW_mono hst) (clampW_le hab t)⟩

theorem extA_norm_le {a b K : ℝ} {A : ι → ℝ → H →L[𝕜] H} (hK : 0 ≤ K)
    (hA : ∀ p r, r ∈ Icc a b → ‖A p r‖ ≤ K) (p : ι) (r : ℝ) : ‖extA a b A p r‖ ≤ K := by
  by_cases hr : r ∈ Icc a b
  · simp only [extA, Set.indicator_of_mem hr]
    exact hA p r hr
  · simp only [extA, Set.indicator_of_notMem hr, norm_zero]
    exact hK

/-- **Uniform exponential majorant on a window**: if `‖F(t,s)‖ ≤ M` on the blocks of `[a, b]` and
`‖A(r)‖ ≤ K` on `[a, b]`, then `‖U(t,s)‖ ≤ 2 M e^{(2MK+1)(b-a)}` there (SP 991-992). -/
theorem IsDuhamelEvolutionOn.norm_le {a b M K : ℝ} {F : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : ι → ℝ → H →L[𝕜] H} {U : ι → ℝ → ℝ → H →L[𝕜] H}
    (hU : IsDuhamelEvolutionOn a b F A U)
    (hF : ∀ p t s, a ≤ s → s ≤ t → t ≤ b → ‖F p t s‖ ≤ M)
    (hA : ∀ p r, r ∈ Icc a b → ‖A p r‖ ≤ K) :
    ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
      ‖U p t s‖ ≤ 2 * M * exp ((2 * (M * K) + 1) * (b - a)) := by
  intro p t s hs hst ht
  have hab : a ≤ b := hs.trans (hst.trans ht)
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA p a ⟨le_rfl, hab⟩)
  have h := (hU.ext hab).norm_le (M := M) (K := K)
    (fun p t s hst' _ => hF p _ _ (le_clampW a b s) (clampW_mono hst') (clampW_le hab t))
    (extA_norm_le hK hA) p t s hst (by linarith)
  simpa only [extW, clampW_of_mem hs (hst.trans ht), clampW_of_mem (hs.trans hst) ht] using h

/-- **Uniqueness on a window**: two Duhamel evolutions of the same `(F, A)` on `[a, b]` agree on
its blocks, so `IsDuhamelEvolutionOn` determines the Duhamel-iteration evolution. -/
theorem IsDuhamelEvolutionOn.unique {a b M K : ℝ} {F : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : ι → ℝ → H →L[𝕜] H} {U U' : ι → ℝ → ℝ → H →L[𝕜] H}
    (hU : IsDuhamelEvolutionOn a b F A U) (hU' : IsDuhamelEvolutionOn a b F A U')
    (hF : ∀ p t s, a ≤ s → s ≤ t → t ≤ b → ‖F p t s‖ ≤ M)
    (hA : ∀ p r, r ∈ Icc a b → ‖A p r‖ ≤ K) :
    ∀ p t s, a ≤ s → s ≤ t → t ≤ b → U p t s = U' p t s := by
  intro p t s hs hst ht
  have hab : a ≤ b := hs.trans (hst.trans ht)
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA p a ⟨le_rfl, hab⟩)
  have h := (hU.ext hab).unique (hU'.ext hab) (M := M) (K := K)
    (fun p t s hst' _ => hF p _ _ (le_clampW a b s) (clampW_mono hst') (clampW_le hab t))
    (extA_norm_le hK hA) p t s hst (by linarith)
  simpa only [extW, clampW_of_mem hs (hst.trans ht), clampW_of_mem (hs.trans hst) ht] using h

/-- **Compact Duhamel comparison on a window** (SP 978-1003, in the form used at SP 2141-2150).
Let `F n, F₀` be free evolutions, `A n, A₀` interactions and `U n, U₀` Duhamel evolutions
(`IsDuhamelEvolutionOn a b`), all given only on the blocks `a ≤ s ≤ t ≤ b` of a window, along a
nontrivial filter `l` and with an auxiliary parameter `p : ι`. Suppose `F n` is uniformly bounded,
`F n → F₀` and `(F n)* → F₀*` strongly, uniformly in the parameter and the blocks, `A n` is
uniformly bounded with `sup_{p, r ∈ [a,b]} ‖A n p r - A₀ p r‖ → 0`, and `{A₀ p r : r ∈ [a, b]}`
is a norm-totally-bounded family of compact operators. Then, uniformly in the parameter and the
blocks of the window, `U n → U₀` and `(U n)* → U₀*` strongly and
`‖(U n - F n)(t,s) - (U₀ - F₀)(t,s)‖ → 0`. -/
theorem compact_duhamel_window {l : Filter N} [l.NeBot] {a b : ℝ}
    {F : N → ι → ℝ → ℝ → H →L[𝕜] H} {F₀ : ι → ℝ → ℝ → H →L[𝕜] H}
    {A : N → ι → ℝ → H →L[𝕜] H} {A₀ : ι → ℝ → H →L[𝕜] H}
    {U : N → ι → ℝ → ℝ → H →L[𝕜] H} {U₀ : ι → ℝ → ℝ → H →L[𝕜] H}
    (hFb : ∃ M, ∀ n p t s, a ≤ s → s ≤ t → t ≤ b → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : ∀ x : H, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
      ‖F n p t s x - F₀ p t s x‖ < ε)
    (hFadj : ∀ x : H, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
      ‖((F n p t s)†) x - ((F₀ p t s)†) x‖ < ε)
    (hAb : ∃ K, ∀ n p r, r ∈ Icc a b → ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in l, ∀ p r, r ∈ Icc a b → ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, r ∈ Icc a b → IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded {K : H →L[𝕜] H | ∃ p, ∃ r ∈ Icc a b, A₀ p r = K})
    (hU : ∀ n, IsDuhamelEvolutionOn a b (F n) (A n) (U n))
    (hU₀ : IsDuhamelEvolutionOn a b F₀ A₀ U₀) :
    (∀ x : H, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
        ‖U n p t s x - U₀ p t s x‖ < ε) ∧
      (∀ x : H, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
        ‖((U n p t s)†) x - ((U₀ p t s)†) x‖ < ε) ∧
      (∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
        ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ < ε) := by
  by_cases hab : a ≤ b
  swap
  · refine ⟨fun x ε _ => Eventually.of_forall fun n p t s h1 h2 h3 =>
        absurd (h1.trans (h2.trans h3)) hab,
      fun x ε _ => Eventually.of_forall fun n p t s h1 h2 h3 =>
        absurd (h1.trans (h2.trans h3)) hab,
      fun ε _ => Eventually.of_forall fun n p t s h1 h2 h3 =>
        absurd (h1.trans (h2.trans h3)) hab⟩
  have hcl : ∀ {s t : ℝ}, s ≤ t →
      a ≤ clampW a b s ∧ clampW a b s ≤ clampW a b t ∧ clampW a b t ≤ b :=
    fun hst => ⟨le_clampW a b _, clampW_mono hst, clampW_le hab _⟩
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨K, hK⟩ := hAb
  have hFe : StrongTendstoOnBlocks l (b - a) (fun n => extW a b (F n)) (extW a b F₀) := by
    intro x ε hε
    filter_upwards [hF x ε hε] with n hn p t s hst _
    exact hn p _ _ (hcl hst).1 (hcl hst).2.1 (hcl hst).2.2
  have hFadje : StrongTendstoOnBlocks l (b - a) (fun n p t s => ((extW a b (F n) p t s)†))
      (fun p t s => ((extW a b F₀ p t s)†)) := by
    intro x ε hε
    filter_upwards [hFadj x ε hε] with n hn p t s hst _
    exact hn p _ _ (hcl hst).1 (hcl hst).2.1 (hcl hst).2.2
  have hAbe : ∃ K', ∀ n p r, ‖extA a b (A n) p r‖ ≤ K' := by
    refine ⟨max K 0, fun n p r => ?_⟩
    by_cases hr : r ∈ Icc a b
    · simp only [extA, Set.indicator_of_mem hr]
      exact (hK n p r hr).trans (le_max_left _ _)
    · simp only [extA, Set.indicator_of_notMem hr, norm_zero]
      exact le_max_right _ _
  have hAe : ∀ ε > 0, ∀ᶠ n in l, ∀ p r, ‖extA a b (A n) p r - extA a b A₀ p r‖ < ε := by
    intro ε hε
    filter_upwards [hA ε hε] with n hn p r
    by_cases hr : r ∈ Icc a b
    · simp only [extA, Set.indicator_of_mem hr]
      exact hn p r hr
    · simp only [extA, Set.indicator_of_notMem hr, sub_zero, norm_zero]
      exact hε
  have hA₀ce : ∀ p r, IsCompactOperator (extA a b A₀ p r) := by
    intro p r
    by_cases hr : r ∈ Icc a b
    · simp only [extA, Set.indicator_of_mem hr]
      exact hA₀c p r hr
    · simp only [extA, Set.indicator_of_notMem hr]
      exact isCompactOperator_zero
  have hA₀pe : TotallyBounded (range fun q : ι × ℝ => extA a b A₀ q.1 q.2) := by
    refine (hA₀p.union (Set.finite_singleton (0 : H →L[𝕜] H)).totallyBounded).subset ?_
    rintro _ ⟨⟨p, r⟩, rfl⟩
    by_cases hr : r ∈ Icc a b
    · left
      exact ⟨p, r, hr, by simp only [extA, Set.indicator_of_mem hr]⟩
    · right
      simp only [extA, Set.indicator_of_notMem hr, Set.mem_singleton_iff]
  obtain ⟨h1, h2, h3⟩ := compact_duhamel (l := l) (B := b - a)
    (F := fun n => extW a b (F n)) (F₀ := extW a b F₀)
    (A := fun n => extA a b (A n)) (A₀ := extA a b A₀)
    (U := fun n => extW a b (U n)) (U₀ := extW a b U₀)
    ⟨M, fun n p t s hst _ => hM n p _ _ (hcl hst).1 (hcl hst).2.1 (hcl hst).2.2⟩
    hFe hFadje hAbe hAe hA₀ce hA₀pe (fun n => (hU n).ext hab) (hU₀.ext hab)
  have hblk : ∀ {s t : ℝ}, a ≤ s → s ≤ t → t ≤ b →
      clampW a b s = s ∧ clampW a b t = t ∧ t ≤ s + (b - a) :=
    fun hs hst ht => ⟨clampW_of_mem hs (hst.trans ht), clampW_of_mem (hs.trans hst) ht,
      by linarith⟩
  refine ⟨fun x ε hε => ?_, fun x ε hε => ?_, fun ε hε => ?_⟩
  · filter_upwards [h1 x ε hε] with n hn p t s hs hst ht
    obtain ⟨e1, e2, e3⟩ := hblk hs hst ht
    have := hn p t s hst e3
    simp only [extW, e1, e2] at this
    exact this
  · filter_upwards [h2 x ε hε] with n hn p t s hs hst ht
    obtain ⟨e1, e2, e3⟩ := hblk hs hst ht
    have := hn p t s hst e3
    simp only [extW, e1, e2] at this
    exact this
  · filter_upwards [h3 ε hε] with n hn p t s hs hst ht
    obtain ⟨e1, e2, e3⟩ := hblk hs hst ht
    have := hn p t s hst e3
    simp only [extW, e1, e2] at this
    exact this

/-- **Semigroup (difference-kernel) form.** If `E p τ = T p τ + ∫_0^τ T p (τ - r) A p E p r dr`
(with integrable integrand) for `0 ≤ τ ≤ B`, and `E p` is bounded on `[0, B]`, then
`(t, s) ↦ E p (t - s)` is the Duhamel evolution of `(t, s) ↦ T p (t - s)` and the
time-independent interaction `A p` on all blocks `s ≤ t ≤ s + B`. -/
theorem isDuhamelEvolution_of_semigroup {B : ℝ} {T E : ι → ℝ → H →L[𝕜] H}
    {A : ι → H →L[𝕜] H}
    (hE : ∀ p τ, 0 ≤ τ → τ ≤ B → ∀ f : H,
      IntervalIntegrable (fun r => T p (τ - r) (A p (E p r f))) volume 0 τ ∧
        E p τ f = T p τ f + ∫ r in (0 : ℝ)..τ, T p (τ - r) (A p (E p r f)))
    (hbd : ∀ p, ∃ C, ∀ τ, 0 ≤ τ → τ ≤ B → ‖E p τ‖ ≤ C) :
    IsDuhamelEvolution B (fun p t s => T p (t - s)) (fun p _ => A p)
      (fun p t s => E p (t - s)) where
  integrable p s t hst hts x := by
    show IntervalIntegrable (fun r => T p (t - r) (A p (E p (r - s) x))) volume s t
    have h := ((hE p (t - s) (sub_nonneg.2 hst) (by linarith) x).1).comp_sub_right s
    simp only [zero_add, sub_add_cancel, sub_sub_sub_cancel_right] at h
    exact h
  duhamel p s t hst hts x := by
    show E p (t - s) x = T p (t - s) x + ∫ r in s..t, T p (t - r) (A p (E p (r - s) x))
    rw [(hE p (t - s) (sub_nonneg.2 hst) (by linarith) x).2]
    congr 1
    have hcv := intervalIntegral.integral_comp_sub_right (a := s) (b := t)
      (fun r => T p (t - s - r) (A p (E p r x))) s
    simp only [sub_self, sub_sub_sub_cancel_right] at hcv
    exact hcv.symm
  bounded p s := by
    obtain ⟨C, hC⟩ := hbd p
    exact ⟨C, fun t h1 h2 => hC (t - s) (sub_nonneg.2 h1) (by linarith)⟩

/-- A strongly continuous operator family is bounded on a compact interval (uniform boundedness
principle). -/
theorem exists_norm_le_of_continuousOn {E : ℝ → H →L[𝕜] H} {c d : ℝ}
    (h : ∀ f : H, ContinuousOn (fun τ => E τ f) (Icc c d)) :
    ∃ C, ∀ τ ∈ Icc c d, ‖E τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun τ : Icc c d => E τ) fun f => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (h f)
    exact ⟨C, fun τ => hC τ τ.2⟩
  exact ⟨C, fun τ hτ => hC ⟨τ, hτ⟩⟩

end Window

/-! ## The real case -/

section Real

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **Compact Duhamel comparison on a window, real Hilbert space** (SP 978-1003, 2141-2150):
`compact_duhamel_window` with `𝕜 = ℝ`, for the real spaces `Xm m`, `Xmc c m` of Part II-b. -/
theorem real_compact_duhamel_window {l : Filter N} [l.NeBot] {a b : ℝ}
    {F : N → ι → ℝ → ℝ → X →L[ℝ] X} {F₀ : ι → ℝ → ℝ → X →L[ℝ] X}
    {A : N → ι → ℝ → X →L[ℝ] X} {A₀ : ι → ℝ → X →L[ℝ] X}
    {U : N → ι → ℝ → ℝ → X →L[ℝ] X} {U₀ : ι → ℝ → ℝ → X →L[ℝ] X}
    (hFb : ∃ M, ∀ n p t s, a ≤ s → s ≤ t → t ≤ b → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : ∀ x : X, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
      ‖F n p t s x - F₀ p t s x‖ < ε)
    (hFadj : ∀ x : X, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
      ‖ContinuousLinearMap.adjoint (F n p t s) x - ContinuousLinearMap.adjoint (F₀ p t s) x‖ < ε)
    (hAb : ∃ K, ∀ n p r, r ∈ Icc a b → ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in l, ∀ p r, r ∈ Icc a b → ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, r ∈ Icc a b → IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded {K : X →L[ℝ] X | ∃ p, ∃ r ∈ Icc a b, A₀ p r = K})
    (hU : ∀ n, IsDuhamelEvolutionOn a b (F n) (A n) (U n))
    (hU₀ : IsDuhamelEvolutionOn a b F₀ A₀ U₀) :
    (∀ x : X, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
        ‖U n p t s x - U₀ p t s x‖ < ε) ∧
      (∀ x : X, ∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
        ‖ContinuousLinearMap.adjoint (U n p t s) x -
          ContinuousLinearMap.adjoint (U₀ p t s) x‖ < ε) ∧
      (∀ ε > 0, ∀ᶠ n in l, ∀ p t s, a ≤ s → s ≤ t → t ≤ b →
        ‖(U n p t s - F n p t s) - (U₀ p t s - F₀ p t s)‖ < ε) :=
  compact_duhamel_window hFb hF hFadj hAb hA hA₀c hA₀p hU hU₀

/-- **Compact Duhamel comparison, real Hilbert space, all blocks** (SP 978-1003):
`compact_duhamel` with `𝕜 = ℝ`. -/
theorem real_compact_duhamel {l : Filter N} [l.NeBot] {B : ℝ}
    {F : N → ι → ℝ → ℝ → X →L[ℝ] X} {F₀ : ι → ℝ → ℝ → X →L[ℝ] X}
    {A : N → ι → ℝ → X →L[ℝ] X} {A₀ : ι → ℝ → X →L[ℝ] X}
    {U : N → ι → ℝ → ℝ → X →L[ℝ] X} {U₀ : ι → ℝ → ℝ → X →L[ℝ] X}
    (hFb : ∃ M, ∀ n p t s, s ≤ t → t ≤ s + B → ‖F n p t s‖ ≤ M ∧ ‖F₀ p t s‖ ≤ M)
    (hF : StrongTendstoOnBlocks l B F F₀)
    (hFadj : StrongTendstoOnBlocks l B (fun n p t s => ContinuousLinearMap.adjoint (F n p t s))
      (fun p t s => ContinuousLinearMap.adjoint (F₀ p t s)))
    (hAb : ∃ K, ∀ n p r, ‖A n p r‖ ≤ K)
    (hA : ∀ ε > 0, ∀ᶠ n in l, ∀ p r, ‖A n p r - A₀ p r‖ < ε)
    (hA₀c : ∀ p r, IsCompactOperator (A₀ p r))
    (hA₀p : TotallyBounded (range fun q : ι × ℝ => A₀ q.1 q.2))
    (hU : ∀ n, IsDuhamelEvolution B (F n) (A n) (U n)) (hU₀ : IsDuhamelEvolution B F₀ A₀ U₀) :
    StrongTendstoOnBlocks l B U U₀ ∧
      StrongTendstoOnBlocks l B (fun n p t s => ContinuousLinearMap.adjoint (U n p t s))
        (fun p t s => ContinuousLinearMap.adjoint (U₀ p t s)) ∧
      NormTendstoOnBlocks l B (fun n p t s => U n p t s - F n p t s)
        (fun p t s => U₀ p t s - F₀ p t s) :=
  compact_duhamel hFb hF hFadj hAb hA hA₀c hA₀p hU hU₀

end Real

end UnforcedLeray.Short.IIb.RCDuhamel
