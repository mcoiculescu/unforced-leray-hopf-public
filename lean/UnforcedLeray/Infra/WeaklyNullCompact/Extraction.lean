import UnforcedLeray.Infra.WeaklyNullCompact.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Weak sequential compactness of bounded sets in a Hilbert space over `RCLike`

Every bounded sequence in a Hilbert space `E` over `𝕜` (`RCLike`) has a weakly convergent
subsequence (`exists_subseq_weakTendsto`), with a weak limit of norm `≤` the bound. No
separability is assumed.

Proof structure (adapted from the real-scalar reference
`NonUniqueEuler/lean/NonUniqueEuler/P/Infra/WeakL2/Compact.lean`, which is copied for the
diagonal extraction `exists_diagonal_subseq` and adapted to `RCLike 𝕜` for the rest).
* `exists_diagonal_subseq`: the nested subsequences `φ_0 = ψ_0`, `φ_{k+1} = φ_k ∘ ψ_{k+1}` and the
  diagonal `n ↦ φ_n n`.
* `exists_subseq_tendsto_forall`: diagonal extraction + Bolzano–Weierstrass in `𝕜`.
* `exists_tendsto_inner_of_dense`: under a uniform bound, convergence of `⟪d, v n⟫` for `d` in a
  dense set gives convergence of `⟪y, v n⟫` for every `y` (Cauchy sequences in `𝕜`).
* `exists_weakTendsto_of_forall_tendsto`: the limit `y ↦ lim ⟪v n, y⟫` is a bounded linear
  functional, represented by a vector (Riesz, `InnerProductSpace.toDual`).
* `exists_subseq_weakTendsto`: extract a subsequence along which `⟪u k, u (φ n)⟫` converges for
  every `k`; the `y` with `⟪y, u (φ n)⟫` convergent form a submodule containing
  `S = span (range u)` and `Sᗮ`, and `S ⊔ Sᗮ` is dense. (This is the "closed span of the
  sequence is separable" argument, with `Sᗮ` handling the complement.)
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Infra.WeaklyNullCompact

/-! ### Diagonal extraction (copied from the reference formalization) -/

/-- The nested subsequences built from a choice function `ψ`:
`nestSeq ψ 0 = ψ 0 id`, `nestSeq ψ (k + 1) = nestSeq ψ k ∘ ψ (k + 1) (nestSeq ψ k)`. -/
private def nestSeq (ψ : ℕ → (ℕ → ℕ) → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => ψ 0 id
  | k + 1 => nestSeq ψ k ∘ ψ (k + 1) (nestSeq ψ k)

/-- Re-indexing: if `φ` and `f` are strictly monotone, `φ k = f k` and `φ n ∈ range f` for all
`n ≥ k`, then `φ = f ∘ θ` on `[k, ∞)` for a strictly monotone `θ`. -/
private lemma exists_strictMono_reindex {φ f : ℕ → ℕ} (hφ : StrictMono φ) (hf : StrictMono f)
    (k : ℕ) (hk : φ k = f k) (hr : ∀ n, k ≤ n → ∃ m, f m = φ n) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ n, k ≤ n → φ n = f (θ n) := by
  choose! g hg using hr
  refine ⟨fun n => if k ≤ n then g n else n, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun n => ?_
    by_cases h : k ≤ n
    · have h1 : k ≤ n + 1 := h.trans n.le_succ
      simp only [h, h1, ↓reduceIte]
      rw [← hf.lt_iff_lt, hg n h, hg (n + 1) h1]
      exact hφ n.lt_succ_self
    · simp only [h, ↓reduceIte]
      by_cases h1 : k ≤ n + 1
      · simp only [h1, ↓reduceIte]
        have hkn : k = n + 1 := by omega
        subst hkn
        have : g (n + 1) = n + 1 := hf.injective (by rw [hg _ le_rfl, hk])
        omega
      · simp only [h1, ↓reduceIte]
        omega
  · intro n hn
    simp only [hn, ↓reduceIte, hg n hn]

/-- **Diagonal extraction.** Let `Q k φ` be countably many properties of subsequences `φ`, each
stable under passing to a further subsequence (`hsub`) and under changing finitely many terms
(`htail`). If every subsequence has a further subsequence with property `Q k` (`hex`), then
some subsequence has all the properties `Q k`. -/
theorem exists_diagonal_subseq (Q : ℕ → (ℕ → ℕ) → Prop)
    (htail : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → (∀ᶠ n in atTop, φ n = ψ n) → Q k ψ)
    (hsub : ∀ (k : ℕ) (φ ψ : ℕ → ℕ), Q k φ → StrictMono ψ → Q k (φ ∘ ψ))
    (hex : ∀ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Q k (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, Q k φ := by
  choose! ψ hψm hψQ using hex
  have hmono : ∀ k, StrictMono (nestSeq ψ k) := by
    intro k
    induction k with
    | zero => exact hψm 0 id strictMono_id
    | succ k ih => exact ih.comp (hψm (k + 1) _ ih)
  have hQ : ∀ k, Q k (nestSeq ψ k) := by
    intro k
    cases k with
    | zero => exact hψQ 0 id strictMono_id
    | succ k => exact hψQ (k + 1) _ (hmono k)
  have hrange : ∀ k n, k ≤ n → ∀ m, ∃ m', nestSeq ψ k m' = nestSeq ψ n m := by
    intro k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact fun m => ⟨m, rfl⟩
    | succ n _ ih => exact fun m => ih _
  have hdiag : StrictMono fun n => nestSeq ψ n n := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    show nestSeq ψ n n < nestSeq ψ n (ψ (n + 1) (nestSeq ψ n) (n + 1))
    exact hmono n (lt_of_lt_of_le n.lt_succ_self ((hψm (n + 1) _ (hmono n)).id_le _))
  refine ⟨fun n => nestSeq ψ n n, hdiag, fun k => ?_⟩
  obtain ⟨θ, hθ, hθeq⟩ := exists_strictMono_reindex hdiag (hmono k) k rfl
    (fun n hn => hrange k n hn n)
  refine htail k _ _ (hsub k _ θ (hQ k) hθ) ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (hθeq n hn).symm

/-- **Bolzano–Weierstrass, diagonal form.** Countably many bounded sequences in a proper metric
space (e.g. `𝕜`) have a common subsequence along which all of them converge. -/
theorem exists_subseq_tendsto_forall {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (a : ℕ → ℕ → X) (ha : ∀ k, Bornology.IsBounded (range (a k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ∃ c : X, Tendsto (fun n => a k (φ n)) atTop (𝓝 c) := by
  refine exists_diagonal_subseq
    (fun k φ => ∃ c : X, Tendsto (fun n => a k (φ n)) atTop (𝓝 c)) ?_ ?_ ?_
  · rintro k φ ψ ⟨c, hc⟩ hφψ
    refine ⟨c, hc.congr' ?_⟩
    filter_upwards [hφψ] with n hn
    rw [hn]
  · rintro k φ ψ ⟨c, hc⟩ hψ
    exact ⟨c, hc.comp hψ.tendsto_atTop⟩
  · intro k φ _
    obtain ⟨c, -, ψ, hψ, hc⟩ := tendsto_subseq_of_bounded (x := fun n => a k (φ n))
      (ha k) (fun n => mem_range_self (φ n))
    exact ⟨ψ, hψ, c, hc⟩

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Weak limits from a dense set -/

/-- Under a uniform bound, convergence of `⟪d, v n⟫` for `d` in a dense set implies convergence
of `⟪y, v n⟫` for every `y`. -/
theorem exists_tendsto_inner_of_dense {v : ℕ → E} {M : ℝ} (hv : ∀ n, ‖v n‖ ≤ M) {D : Set E}
    (hD : Dense D) (h : ∀ d ∈ D, ∃ c : 𝕜, Tendsto (fun n => ⟪d, v n⟫_𝕜) atTop (𝓝 c))
    (y : E) : ∃ c : 𝕜, Tendsto (fun n => ⟪y, v n⟫_𝕜) atTop (𝓝 c) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hv 0)
  have hM1 : 0 < M + 1 := by linarith
  set δ := ε / (4 * (M + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hMδ' : (M + 1) * δ = ε / 4 := by
    rw [hδ]
    field_simp
  have hMδ : M * δ < ε / 4 := by nlinarith
  obtain ⟨d, hdD, hyd⟩ := hD.exists_dist_lt y hδpos
  obtain ⟨c, hc⟩ := h d hdD
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hc.cauchySeq (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have key : ∀ k, ‖⟪y, v k⟫_𝕜 - ⟪d, v k⟫_𝕜‖ ≤ M * δ := by
    intro k
    rw [← inner_sub_left]
    calc ‖⟪y - d, v k⟫_𝕜‖ ≤ ‖y - d‖ * ‖v k‖ := norm_inner_le_norm _ _
      _ ≤ δ * M := by
        refine mul_le_mul ?_ (hv k) (norm_nonneg _) hδpos.le
        rw [← dist_eq_norm]
        exact hyd.le
      _ = M * δ := mul_comm _ _
  have h1 := key n
  have h2 := key N
  have h3 := hN n hn
  rw [dist_eq_norm] at h3 ⊢
  calc ‖⟪y, v n⟫_𝕜 - ⟪y, v N⟫_𝕜‖
      = ‖(⟪y, v n⟫_𝕜 - ⟪d, v n⟫_𝕜) + (⟪d, v n⟫_𝕜 - ⟪d, v N⟫_𝕜)
          - (⟪y, v N⟫_𝕜 - ⟪d, v N⟫_𝕜)‖ := by congr 1; ring
    _ ≤ ‖⟪y, v n⟫_𝕜 - ⟪d, v n⟫_𝕜‖ + ‖⟪d, v n⟫_𝕜 - ⟪d, v N⟫_𝕜‖
          + ‖⟪y, v N⟫_𝕜 - ⟪d, v N⟫_𝕜‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < ε := by linarith

/-- **Existence of the weak limit (Riesz).** A bounded sequence `v` such that `⟪y, v n⟫`
converges for every `y` converges weakly, to a vector of norm `≤ M`. -/
theorem exists_weakTendsto_of_forall_tendsto [CompleteSpace E] {v : ℕ → E} {M : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ M) (h : ∀ y : E, ∃ c : 𝕜, Tendsto (fun n => ⟪y, v n⟫_𝕜) atTop (𝓝 c)) :
    ∃ x : E, ‖x‖ ≤ M ∧ WeakTendsto 𝕜 v atTop x := by
  choose c hc using h
  have hM : 0 ≤ M := (norm_nonneg _).trans (hv 0)
  -- the conjugate limit `y ↦ conj (c y) = lim ⟪v n, y⟫` is linear in `y`
  have hc' : ∀ y, Tendsto (fun n => ⟪v n, y⟫_𝕜) atTop (𝓝 (conj (c y))) := fun y => by
    have := ((RCLike.continuous_conj (K := 𝕜)).tendsto _).comp (hc y)
    simpa only [Function.comp_def, inner_conj_symm] using this
  let f : E →ₗ[𝕜] 𝕜 :=
    { toFun := fun y => conj (c y)
      map_add' := fun y z => tendsto_nhds_unique (hc' (y + z))
        (by simpa only [inner_add_right] using (hc' y).add (hc' z))
      map_smul' := fun r y => tendsto_nhds_unique (hc' (r • y))
        (by simpa only [inner_smul_right, smul_eq_mul, RingHom.id_apply] using
          (hc' y).const_mul r) }
  have hbound : ∀ y, ‖f y‖ ≤ M * ‖y‖ := by
    intro y
    refine le_of_tendsto (hc' y).norm (Eventually.of_forall fun n => ?_)
    calc ‖⟪v n, y⟫_𝕜‖ ≤ ‖v n‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ M * ‖y‖ := mul_le_mul_of_nonneg_right (hv n) (norm_nonneg _)
  let F : StrongDual 𝕜 E := f.mkContinuous M hbound
  refine ⟨(InnerProductSpace.toDual 𝕜 E).symm F, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le f hM hbound
  · rw [weakTendsto_iff_inner_left]
    intro y
    rw [InnerProductSpace.toDual_symm_apply]
    exact hc' y

/-! ### Weak sequential compactness -/

/-- **Weak sequential compactness of closed balls** of a Hilbert space over `RCLike 𝕜`: a
sequence bounded by `M` has a subsequence converging weakly to a vector of norm `≤ M`. -/
theorem exists_subseq_weakTendsto [CompleteSpace E] {u : ℕ → E} {M : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : E, ‖x‖ ≤ M ∧ WeakTendsto 𝕜 (u ∘ φ) atTop x := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hu 0)
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto_forall (fun k n => ⟪u k, u n⟫_𝕜)
    (fun k => isBounded_iff_forall_norm_le.mpr ⟨M * M, by
      rintro _ ⟨n, rfl⟩
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hu k) (hu n) (norm_nonneg _) hM)⟩)
  -- the submodule of the `y` along which the inner products converge
  let C : Submodule 𝕜 E :=
    { carrier := {y | ∃ c : 𝕜, Tendsto (fun n => ⟪y, u (φ n)⟫_𝕜) atTop (𝓝 c)}
      add_mem' := by
        rintro y z ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by simpa only [inner_add_left] using ha.add hb⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r y ⟨a, ha⟩
        exact ⟨conj r * a, by simpa only [inner_smul_left] using ha.const_mul (conj r)⟩ }
  let S : Submodule 𝕜 E := Submodule.span 𝕜 (range u)
  have hSC : S ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hconv k
  have hSoC : Sᗮ ≤ C := by
    intro y hy
    refine ⟨0, ?_⟩
    have h0 : ∀ n, ⟪y, u (φ n)⟫_𝕜 = 0 := fun n =>
      Submodule.inner_left_of_mem_orthogonal
        (Submodule.subset_span (mem_range_self (φ n)) : u (φ n) ∈ S) hy
    simp only [h0]
    exact tendsto_const_nhds
  have hdense : Dense ((S ⊔ Sᗮ : Submodule 𝕜 E) : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      ← Submodule.inf_orthogonal]
    exact Sᗮ.inf_orthogonal_eq_bot
  have hall := exists_tendsto_inner_of_dense (v := u ∘ φ) (fun n => hu (φ n)) hdense
    (fun d hd => sup_le hSC hSoC hd)
  obtain ⟨x, hx, hw⟩ := exists_weakTendsto_of_forall_tendsto (fun n => hu (φ n)) hall
  exact ⟨φ, hφ, x, hx, hw⟩

/-- Weak sequential compactness, for a sequence that is only eventually bounded by `M`. -/
theorem exists_subseq_weakTendsto_of_eventually [CompleteSpace E] {u : ℕ → E} {M : ℝ}
    (hu : ∀ᶠ n in atTop, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : E, ‖x‖ ≤ M ∧ WeakTendsto 𝕜 (u ∘ φ) atTop x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  obtain ⟨φ, hφ, x, hx, hw⟩ := exists_subseq_weakTendsto (𝕜 := 𝕜) (u := fun n => u (n + N))
    (M := M) (fun n => hN _ (Nat.le_add_left N n))
  refine ⟨fun n => φ n + N, fun a b hab => Nat.add_lt_add_right (hφ hab) N, x, hx, ?_⟩
  exact hw

end UnforcedLeray.Infra.WeaklyNullCompact
