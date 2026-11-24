import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `PartII-a:R02/2/2` (`kExpansion_of`): the expansion of `K^ℓ`

Source of record: `the November 2 reference manuscript`, lines 438-446 (Lemma
`sct:heat`, route step (i)). Target: `KExpansion` (`Sub/R02_2.lean`).

Write `K = ageOperator` and `T_{ik} G y = η^i s^k (∂_η^i ∂_s^k G)(y)` (`kxT`). The proof is by
induction on `ℓ`, with the explicit recursion

`n_{ℓ+1}(i,k) = (i+2k) n_ℓ(i,k) + [i ≥ 1] n_ℓ(i-1,k) + 2 [k ≥ 1] n_ℓ(i,k-1)`.

The induction hypothesis carries the support bound `n_ℓ(i,k) = 0` for `i > ℓ` or `k > ℓ`, and the
expansion over `range N` for every `N > ℓ`, so that the final sums can be taken over `range (ℓ+1)`.

The pointwise identity `K T_{ik} G = (i+2k) T_{ik} G + T_{i+1,k} G + 2 T_{i,k+1} G` on `{s > 0}`
uses the commutation hypothesis `ProfileIterComm` for `∂_s ∂_η^i = ∂_η^i ∂_s`.  The slice
derivative lemmas follow the pattern of `ProfileDict.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184

/-! ### Slice derivatives -/

theorem kx_slice_eta {f : ProfilePoint → ℝ} {x : ProfilePoint} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x.1, (t, x.2.2))) (partialEta f x) x.2.1 := by
  have hline : HasDerivAt (fun t : ℝ => ((x.1, (t, x.2.2)) : ProfilePoint)) eηDir x.2.1 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  exact hf.hasFDerivAt.comp_hasDerivAt x.2.1 hline

theorem kx_slice_age {f : ProfilePoint → ℝ} {x : ProfilePoint} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x.1, (x.2.1, t))) (partialAge f x) x.2.2 := by
  have hline : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : ProfilePoint)) esDir x.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact hf.hasFDerivAt.comp_hasDerivAt x.2.2 hline

/-! ### Leibniz rules for a monomial `η^i s^k` times a differentiable factor -/

theorem kx_pow_pred (t : ℝ) (i : ℕ) : t * ((i : ℝ) * t ^ (i - 1)) = (i : ℝ) * t ^ i := by
  cases i with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel]
    push_cast
    ring

theorem kx_eta_mul (F : ProfilePoint → ℝ) (x : ProfilePoint) (i k : ℕ)
    (hF : DifferentiableAt ℝ F x) :
    partialEta (fun y : ProfilePoint => y.2.1 ^ i * y.2.2 ^ k * F y) x =
      ((i : ℝ) * x.2.1 ^ (i - 1)) * x.2.2 ^ k * F x + x.2.1 ^ i * x.2.2 ^ k * partialEta F x := by
  have hm : DifferentiableAt ℝ (fun y : ProfilePoint => y.2.1 ^ i * y.2.2 ^ k) x := by fun_prop
  have hs := kx_slice_eta (hm.mul hF)
  have hc : HasDerivAt (fun t : ℝ => t ^ i * x.2.2 ^ k * F (x.1, (t, x.2.2)))
      (((i : ℝ) * x.2.1 ^ (i - 1)) * x.2.2 ^ k * F x + x.2.1 ^ i * x.2.2 ^ k * partialEta F x)
      x.2.1 :=
    ((hasDerivAt_pow i x.2.1).mul_const (x.2.2 ^ k)).mul (kx_slice_eta hF)
  exact hs.unique hc

theorem kx_age_mul (F : ProfilePoint → ℝ) (x : ProfilePoint) (i k : ℕ)
    (hF : DifferentiableAt ℝ F x) :
    partialAge (fun y : ProfilePoint => y.2.1 ^ i * y.2.2 ^ k * F y) x =
      x.2.1 ^ i * ((k : ℝ) * x.2.2 ^ (k - 1)) * F x + x.2.1 ^ i * x.2.2 ^ k * partialAge F x := by
  have hm : DifferentiableAt ℝ (fun y : ProfilePoint => y.2.1 ^ i * y.2.2 ^ k) x := by fun_prop
  have hs := kx_slice_age (hm.mul hF)
  have hc : HasDerivAt (fun t : ℝ => x.2.1 ^ i * t ^ k * F (x.1, (x.2.1, t)))
      (x.2.1 ^ i * ((k : ℝ) * x.2.2 ^ (k - 1)) * F x + x.2.1 ^ i * x.2.2 ^ k * partialAge F x)
      x.2.2 :=
    ((hasDerivAt_pow k x.2.2).const_mul (x.2.1 ^ i)).mul (kx_slice_age hF)
  exact hs.unique hc

/-- The `K`-action on a monomial times a differentiable factor. -/
theorem kx_ageMul (F : ProfilePoint → ℝ) (x : ProfilePoint) (i k : ℕ)
    (hF : DifferentiableAt ℝ F x) :
    ageOperator (fun y : ProfilePoint => y.2.1 ^ i * y.2.2 ^ k * F y) x =
      ((i : ℝ) + 2 * (k : ℝ)) * (x.2.1 ^ i * x.2.2 ^ k * F x)
        + x.2.1 ^ (i + 1) * x.2.2 ^ k * partialEta F x
        + 2 * (x.2.1 ^ i * x.2.2 ^ (k + 1) * partialAge F x) := by
  unfold ageOperator
  rw [kx_eta_mul F x i k hF, kx_age_mul F x i k hF]
  have h1 := kx_pow_pred x.2.1 i
  have h2 := kx_pow_pred x.2.2 k
  linear_combination (x.2.2 ^ k * F x) * h1 + (2 * x.2.1 ^ i * F x) * h2

/-! ### The basis terms `T_{ik} G = η^i s^k ∂_η^i ∂_s^k G` -/

/-- The basis term `η^i s^k ∂_η^i ∂_s^k G` of the expansion of `K^ℓ`. -/
def kxT (G : ProfilePoint → ℝ) (i k : ℕ) : ProfilePoint → ℝ :=
  fun y => y.2.1 ^ i * y.2.2 ^ k * (partialEta^[i] (partialAge^[k] G)) y

theorem kx_contDiffOn_partialAge_iter {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (k : ℕ) :
    ContDiffOn ℝ ∞ (partialAge^[k] G) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_iterate partialAge (fun _ h => contDiffOn_fderiv_apply h esDir) hG k

theorem kx_F_diff {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2})
    (i k : ℕ) {x : ProfilePoint} (hx : 0 < x.2.2) :
    DifferentiableAt ℝ (partialEta^[i] (partialAge^[k] G)) x := by
  have hx' : x ∈ {y : ProfilePoint | 0 < y.2.2} := hx
  exact ((contDiffOn_partialEta_iter (kx_contDiffOn_partialAge_iter hG k) i).contDiffAt
    (isOpen_late.mem_nhds hx')).differentiableAt (by simp)

theorem kx_diffT {G : ProfilePoint → ℝ} (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2})
    (i k : ℕ) {x : ProfilePoint} (hx : 0 < x.2.2) :
    DifferentiableAt ℝ (kxT G i k) x := by
  have hm : DifferentiableAt ℝ (fun y : ProfilePoint => y.2.1 ^ i * y.2.2 ^ k) x := by fun_prop
  exact hm.mul (kx_F_diff hG i k hx)

/-- Mixed partials commute: `∂_s ∂_η^i H = ∂_η^i ∂_s H` for `H = ∂_s^k G`, from `ProfileIterComm`. -/
theorem kx_age_comm (hC : ProfileIterComm) {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (i k : ℕ) (x : ProfilePoint)
    (hx : 0 < x.2.2) :
    partialAge (partialEta^[i] (partialAge^[k] G)) x = partialEta^[i] (partialAge^[k + 1] G) x := by
  have h := hC (partialAge^[k] G) (kx_contDiffOn_partialAge_iter hG k) 0 i 0 1 x hx
  simpa [Function.iterate_succ_apply'] using h

/-- The pointwise action of `K` on a basis term. -/
theorem kx_ageTm (hC : ProfileIterComm) {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2}) (i k : ℕ) {x : ProfilePoint}
    (hx : 0 < x.2.2) :
    ageOperator (kxT G i k) x =
      ((i : ℝ) + 2 * (k : ℝ)) * kxT G i k x + kxT G (i + 1) k x + 2 * kxT G i (k + 1) x := by
  have hFd := kx_F_diff hG i k hx
  have hE : partialEta (partialEta^[i] (partialAge^[k] G)) x =
      partialEta^[i + 1] (partialAge^[k] G) x := by
    rw [Function.iterate_succ_apply']
  have hA := kx_age_comm hC hG i k x hx
  have key := kx_ageMul (partialEta^[i] (partialAge^[k] G)) x i k hFd
  rw [hE, hA] at key
  unfold kxT
  exact key

/-! ### Linearity of `ageOperator` on finite sums -/

theorem kx_ageOp_congr {f g : ProfilePoint → ℝ} {x : ProfilePoint} (h : f =ᶠ[𝓝 x] g) :
    ageOperator f x = ageOperator g x := by
  unfold ageOperator partialEta partialAge
  rw [h.fderiv_eq]

theorem kx_ageOp_const_mul (c : ℝ) {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : DifferentiableAt ℝ f x) :
    ageOperator (fun y => c * f y) x = c * ageOperator f x := by
  have h := (hf.hasFDerivAt.const_mul c).fderiv
  unfold ageOperator partialEta partialAge
  rw [h]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem kx_diffAt_sum {ι : Type*} (u : Finset ι) (F : ι → ProfilePoint → ℝ) {x : ProfilePoint}
    (hF : ∀ p ∈ u, DifferentiableAt ℝ (F p) x) :
    DifferentiableAt ℝ (fun y => ∑ p ∈ u, F p y) x :=
  DifferentiableAt.fun_sum (fun p hp => hF p hp)

theorem kx_ageOp_sum {ι : Type*} (u : Finset ι) (F : ι → ProfilePoint → ℝ) {x : ProfilePoint}
    (hF : ∀ p ∈ u, DifferentiableAt ℝ (F p) x) :
    ageOperator (fun y => ∑ p ∈ u, F p y) x = ∑ p ∈ u, ageOperator (F p) x := by
  have hD : HasFDerivAt (fun y => ∑ p ∈ u, F p y) (∑ p ∈ u, fderiv ℝ (F p) x) x :=
    HasFDerivAt.fun_sum (fun p hp => (hF p hp).hasFDerivAt)
  unfold ageOperator partialEta partialAge
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

theorem kx_ageOp_dsum (R : Finset ℕ) (c : ℕ → ℕ → ℝ) (f : ℕ → ℕ → ProfilePoint → ℝ)
    {x : ProfilePoint} (hf : ∀ i ∈ R, ∀ k ∈ R, DifferentiableAt ℝ (f i k) x) :
    ageOperator (fun y => ∑ i ∈ R, ∑ k ∈ R, c i k * f i k y) x =
      ∑ i ∈ R, ∑ k ∈ R, c i k * ageOperator (f i k) x := by
  have hin : ∀ i ∈ R, DifferentiableAt ℝ (fun y => ∑ k ∈ R, c i k * f i k y) x := fun i hi =>
    kx_diffAt_sum R (fun k y => c i k * f i k y)
      (fun k hk => (hf i hi k hk).const_mul (c i k))
  refine (kx_ageOp_sum R (fun i y => ∑ k ∈ R, c i k * f i k y) hin).trans ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  refine (kx_ageOp_sum R (fun k y => c i k * f i k y)
    (fun k hk => (hf i hi k hk).const_mul (c i k))).trans ?_
  exact Finset.sum_congr rfl fun k hk => kx_ageOp_const_mul (c i k) (hf i hi k hk)

/-! ### Reindexing the shifts -/

theorem kx_reindex_fst (n : ℕ → ℕ → ℝ) (T : ℕ → ℕ → ℝ) (M : ℕ) (hM : ∀ k, n M k = 0) :
    ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1), n i k * T (i + 1) k =
      ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
        (if i = 0 then (0 : ℝ) else n (i - 1) k) * T i k := by
  rw [Finset.sum_range_succ (fun i => ∑ k ∈ Finset.range (M + 1), n i k * T (i + 1) k),
    Finset.sum_range_succ' (fun i => ∑ k ∈ Finset.range (M + 1),
      (if i = 0 then (0 : ℝ) else n (i - 1) k) * T i k)]
  simp [hM]

theorem kx_reindex_snd (n : ℕ → ℕ → ℝ) (T : ℕ → ℕ → ℝ) (M : ℕ) (hM : ∀ i, n i M = 0) :
    ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1), (2 * n i k) * T i (k + 1) =
      ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
        (if k = 0 then (0 : ℝ) else 2 * n i (k - 1)) * T i k := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_succ (fun k => (2 * n i k) * T i (k + 1)),
    Finset.sum_range_succ' (fun k => (if k = 0 then (0 : ℝ) else 2 * n i (k - 1)) * T i k)]
  simp [hM i]

/-! ### The expansion by induction on `ℓ` -/

theorem kx_key (hC : ProfileIterComm) (ℓ : ℕ) :
    ∃ n : ℕ → ℕ → ℝ, (∀ i k : ℕ, ℓ < i ∨ ℓ < k → n i k = 0) ∧
      ∀ N : ℕ, ℓ < N → ∀ G : ProfilePoint → ℝ,
        ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2} → ∀ x : ProfilePoint, 0 < x.2.2 →
          (ageOperator^[ℓ] G) x =
            ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, n i k * kxT G i k x := by
  induction ℓ with
  | zero =>
    refine ⟨fun i k => if i = 0 then (if k = 0 then (1 : ℝ) else 0) else 0, ?_, ?_⟩
    · intro i k h
      dsimp only
      split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
    · intro N hN G hG x hx
      dsimp only
      rw [Function.iterate_zero_apply]
      rw [Finset.sum_eq_single 0]
      · rw [Finset.sum_eq_single 0]
        · simp [kxT]
        · intro k _ hk
          simp [hk]
        · intro h
          exact absurd (Finset.mem_range.2 hN) h
      · intro i _ hi
        simp [hi]
      · intro h
        exact absurd (Finset.mem_range.2 hN) h
  | succ ℓ ih =>
    obtain ⟨n, hsupp, hexp⟩ := ih
    refine ⟨fun i k => ((i : ℝ) + 2 * (k : ℝ)) * n i k
        + (if i = 0 then (0 : ℝ) else n (i - 1) k)
        + (if k = 0 then (0 : ℝ) else 2 * n i (k - 1)), ?_, ?_⟩
    · intro i k h
      dsimp only
      have hA : n i k = 0 := hsupp i k (by omega)
      have hB : (if i = 0 then (0 : ℝ) else n (i - 1) k) = 0 := by
        split_ifs with h0
        · rfl
        · exact hsupp (i - 1) k (by omega)
      have hD : (if k = 0 then (0 : ℝ) else 2 * n i (k - 1)) = 0 := by
        split_ifs with h0
        · rfl
        · rw [hsupp i (k - 1) (by omega), mul_zero]
      rw [hA, hB, hD]
      ring
    · intro N hN G hG x hx
      dsimp only
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hM1 : ∀ k, n M k = 0 := fun k => hsupp M k (Or.inl (by omega))
      have hM2 : ∀ i, n i M = 0 := fun i => hsupp i M (Or.inr (by omega))
      have hx' : x ∈ {y : ProfilePoint | 0 < y.2.2} := hx
      have hcongr : ageOperator^[ℓ] G =ᶠ[𝓝 x]
          (fun y => ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1), n i k * kxT G i k y) :=
        Filter.eventually_of_mem (isOpen_late.mem_nhds hx')
          (fun y hy => hexp (M + 1) (by omega) G hG y hy)
      rw [Function.iterate_succ_apply', kx_ageOp_congr hcongr]
      refine (kx_ageOp_dsum (Finset.range (M + 1)) n (fun i k => kxT G i k)
        (fun i _ k _ => kx_diffT hG i k hx)).trans ?_
      have hpt : ∀ i k : ℕ, ageOperator (kxT G i k) x =
          ((i : ℝ) + 2 * (k : ℝ)) * kxT G i k x + kxT G (i + 1) k x + 2 * kxT G i (k + 1) x :=
        fun i k => kx_ageTm hC hG i k hx
      have e : ∀ i k : ℕ, n i k * (((i : ℝ) + 2 * (k : ℝ)) * kxT G i k x + kxT G (i + 1) k x
          + 2 * kxT G i (k + 1) x)
          = (((i : ℝ) + 2 * (k : ℝ)) * n i k) * kxT G i k x + n i k * kxT G (i + 1) k x
            + (2 * n i k) * kxT G i (k + 1) x :=
        fun i k => by ring
      have hB : ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1), n i k * kxT G (i + 1) k x =
          ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
            (if i = 0 then (0 : ℝ) else n (i - 1) k) * kxT G i k x :=
        kx_reindex_fst n (fun i k => kxT G i k x) M hM1
      have hD : ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
          (2 * n i k) * kxT G i (k + 1) x =
          ∑ i ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
            (if k = 0 then (0 : ℝ) else 2 * n i (k - 1)) * kxT G i k x :=
        kx_reindex_snd n (fun i k => kxT G i k x) M hM2
      simp only [hpt, e, Finset.sum_add_distrib]
      rw [hB, hD]
      simp only [add_mul, Finset.sum_add_distrib]

/-- **Expansion of `K^ℓ`** (`KExpansion`, `Sub/R02_2.lean`): the target of this task. -/
theorem kExpansion_of (hC : UnforcedLeray.Short.PartIIa.ProfileIterComm) :
    UnforcedLeray.Short.PartIIa.KExpansion := by
  unfold UnforcedLeray.Short.PartIIa.KExpansion
  intro ℓ
  obtain ⟨n, -, hexp⟩ := kx_key hC ℓ
  refine ⟨n, fun G hG x hx => ?_⟩
  rw [hexp (ℓ + 1) (Nat.lt_succ_self ℓ) G hG x hx]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  unfold kxT
  ring

end UnforcedLeray.Short.PartIIa
