import UnforcedLeray.Short.PartI.Sub.C09
import UnforcedLeray.Short.PartI.Sub.C09.PlanarEllipticH2
import UnforcedLeray.Short.PartI.Sub.C09.PlanarLapOfDeriv

/-!
# Part I, task `PartI:C09`: all orders of planar elliptic regularity (`PlanarBootstrap j`)

Source of record: `the November 2 reference manuscript`, lines 1141-1142
("elliptic regularity iterated to all Sobolev orders").

Proves `planarBootstrap (j : ℕ) : PlanarBootstrap j` (the definition is in
`Short/PartI/Sub/C09.lean`) from `planarEllipticH2 : PlanarEllipticH2` and
`planarLapOfDeriv : PlanarLapOfDeriv`.

Notation. `U = ∫‖u‖²`, `F_m = ∑_{|α|≤m} ∫‖gF α‖²`, `H_m = ∑_{|β|≤m} ∫‖gu β‖²`.

* Step (`pbs_step`). If `gu γ` are weak derivatives of `u` for `|γ| ≤ m` and `gF α` are weak
  derivatives of `f` for `|α| ≤ m`, then `Δ(gu γ) = gF γ` (`planarLapOfDeriv`), and
  `planarEllipticH2` applied to `(gu γ, gF γ)` gives second derivatives `v γ δ`, `|δ| ≤ 2`.
  The composed weak derivative of `u` along `γ + δ` (`pbs_comp_add`) is an entry of order
  `|β| ≤ m + 2`. Every `β` in `multiIdx (m+2)` is `γ + δ` for a chosen pair (`pbs_split`), and
  the choice is injective, so `H_{m+2} ≤ C_H (H_m + F_m)`.
* Base (`pbs_h2`). `planarEllipticH2` with `g = f` gives order `2` with `C_H (U + ∫‖f‖²)`, and
  `∫‖f‖² ≤ F_n` for every `n` (`pbs_sq_f_le`, using `B0122.ae_eq_zero_index`).
* Induction (`pbs_boot_all`). `PBSE m` (order `m` for `u`, bound `F_m + U`) and `PBSE' m`
  (order `m + 2`, bound `F_m + U`). `PBSE' m ⇒ PBSE (m + 2)` by monotonicity of `F`;
  `PBSE m ⇒ PBSE' m` by the step and `pbs_arith`. Base: `PBSE 1` and `PBSE' 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

/-! ### Direction lists and weak derivatives of compositions -/

/-- `pdListR (γ + δ)` is a permutation of `pdListR γ ++ pdListR δ`. -/
theorem pbs_perm (γ δ : ℕ × ℕ) :
    (pdListR γ ++ pdListR δ).Perm (pdListR (γ + δ)) := by
  rw [List.perm_iff_count]
  intro a
  simp only [pdListR, Prod.fst_add, Prod.snd_add, List.replicate_add, List.count_append]
  omega

/-- Composition of weak derivatives on `ℝ²`: `∂_{vs} u = g` and `∂_{ws} g = v` give
`∂_{vs ++ ws} u = v`. -/
theorem pbs_comp {vs ws : List (ℝ × ℝ)} {u g v : ℝ × ℝ → ℂ}
    (h1 : HasWeakDerivOn univ vs u g) (h2 : HasWeakDerivOn univ ws g v) :
    HasWeakDerivOn univ (vs ++ ws) u v := by
  intro φ hφ
  rw [UnforcedLeray.PlanarBS.Sob.iterDirDeriv_append, h1 _ (hφ.iterDirDeriv ws), h2 φ hφ,
    List.length_append, pow_add]
  ring

/-- Composition along multi-indices: `∂^γ u = g` and `∂^δ g = v` give `∂^{γ+δ} u = v`. -/
theorem pbs_comp_add {γ δ : ℕ × ℕ} {u g v : ℝ × ℝ → ℂ}
    (h1 : HasWeakDerivOn univ (pdListR γ) u g) (h2 : HasWeakDerivOn univ (pdListR δ) g v) :
    HasWeakDerivOn univ (pdListR (γ + δ)) u v :=
  hasWeakDerivOn_perm (pbs_perm γ δ) (pbs_comp h1 h2)

/-! ### Zero order and monotonicity -/

/-- The order-zero weak derivative of `f` is `f` a.e., so `∫‖g‖² = ∫‖f‖²`. -/
theorem pbs_sq_gF0 {f g : ℝ × ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (h : HasWeakDerivOn univ (pdListR (0, 0)) f g) :
    ∫ z, ‖g z‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have hae : g =ᵐ[volume] f :=
    UnforcedLeray.B0122.ae_eq_zero_index (G := fun _ => g)
      (hf.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num)) h
  exact integral_congr_ae (hae.mono fun z hz => by simp only [hz])

/-- `∫‖f‖² ≤ F_n` whenever `f` has the weak derivative data of order `n`. -/
theorem pbs_sq_f_le {n : ℕ} {f : ℝ × ℝ → ℂ} {gF : ℕ × ℕ → ℝ × ℝ → ℂ} (hf : MemLp f 2 volume)
    (hF : ∀ α ∈ multiIdx n, MemLp (gF α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) f (gF α)) :
    ∫ z, ‖f z‖ ^ 2 ≤ ∑ α ∈ multiIdx n, ∫ z, ‖gF α z‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hF (0, 0) (zero_mem_multiIdx n)
  rw [← pbs_sq_gF0 hf h1 h2]
  exact Finset.single_le_sum (f := fun α => ∫ z, ‖gF α z‖ ^ 2)
    (fun α _ => integral_nonneg fun z => sq_nonneg _) (zero_mem_multiIdx n)

/-- Monotonicity of the `F`-sums in the order. -/
theorem pbs_sum_mono {a b : ℕ} (hab : a ≤ b) (gF : ℕ × ℕ → ℝ × ℝ → ℂ) :
    ∑ α ∈ multiIdx a, ∫ z, ‖gF α z‖ ^ 2 ≤ ∑ α ∈ multiIdx b, ∫ z, ‖gF α z‖ ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (multiIdx_mono hab)
    (fun α _ _ => integral_nonneg fun z => sq_nonneg _)

/-- Arithmetic of the induction: `H₂ ≤ C_H (H₁ + a)` and `H₁ ≤ C_k (a + c)` give
`H₂ ≤ C_H (C_k + 1) (a + c)`. -/
theorem pbs_arith {H1 H2 a c Ck CH : ℝ} (hCk : 0 ≤ Ck) (hCH : 0 ≤ CH) (hc : 0 ≤ c)
    (h1 : H1 ≤ Ck * (a + c)) (h2 : H2 ≤ CH * (H1 + a)) :
    H2 ≤ CH * (Ck + 1) * (a + c) := by
  have e : (Ck + 1) * (a + c) = Ck * (a + c) + (a + c) := by ring
  have h3 : CH * (H1 + a) ≤ CH * (Ck * (a + c) + a) :=
    mul_le_mul_of_nonneg_left (by linarith) hCH
  have h4 : CH * (Ck * (a + c) + a) ≤ CH * ((Ck + 1) * (a + c)) :=
    mul_le_mul_of_nonneg_left (by linarith) hCH
  calc H2 ≤ CH * (H1 + a) := h2
    _ ≤ CH * (Ck * (a + c) + a) := h3
    _ ≤ CH * ((Ck + 1) * (a + c)) := h4
    _ = CH * (Ck + 1) * (a + c) := by ring

/-! ### Splitting multi-indices -/

/-- Every `β` with `|β| ≤ m + 2` is `γ + δ` with `|γ| ≤ m` and `|δ| ≤ 2`. -/
theorem pbs_split (m : ℕ) (β : ℕ × ℕ) (hβ : β ∈ multiIdx (m + 2)) :
    ∃ p : (ℕ × ℕ) × (ℕ × ℕ), p.1 ∈ multiIdx m ∧ p.2 ∈ multiIdx 2 ∧ p.1 + p.2 = β := by
  rw [mem_multiIdx] at hβ
  rcases le_or_gt (β.1 + β.2) m with h | h
  · refine ⟨(β, (0, 0)), ?_, ?_, ?_⟩
    · simp only [mem_multiIdx]
      omega
    · simp only [mem_multiIdx]
      omega
    · simp
  · rcases le_or_gt (β.1 + β.2 - m) β.1 with hk | hk
    · refine ⟨((β.1 - (β.1 + β.2 - m), β.2), (β.1 + β.2 - m, 0)), ?_, ?_, ?_⟩
      · simp only [mem_multiIdx]
        omega
      · simp only [mem_multiIdx]
        omega
      · ext <;> simp <;> omega
    · refine ⟨((0, m), (β.1, β.1 + β.2 - m - β.1)), ?_, ?_, ?_⟩
      · simp only [mem_multiIdx]
        omega
      · simp only [mem_multiIdx]
        omega
      · ext <;> simp <;> omega

/-! ### Elliptic regularity with a nonnegative constant -/

/-- `planarEllipticH2` with a nonnegative constant. -/
theorem pbs_ell : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ u g : ℝ × ℝ → ℂ, MemLp u 2 volume → MemLp g 2 volume →
    WeakLapOn univ u g → ∃ v : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ β ∈ multiIdx 2, MemLp (v β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (v β)) ∧
      ∑ β ∈ multiIdx 2, ∫ z, ‖v β z‖ ^ 2 ≤ CH * ((∫ z, ‖u z‖ ^ 2) + ∫ z, ‖g z‖ ^ 2) := by
  have hE := planarEllipticH2
  unfold PlanarEllipticH2 at hE
  obtain ⟨C, hC⟩ := hE
  refine ⟨max C 0, le_max_right _ _, fun u g hu hg hW => ?_⟩
  obtain ⟨v, hv1, hv2⟩ := hC u g hu hg hW
  refine ⟨v, hv1, hv2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left C 0)
    (add_nonneg (integral_nonneg fun z => sq_nonneg _) (integral_nonneg fun z => sq_nonneg _))

/-! ### The step: order `m` to order `m + 2` -/

/-- One step of the bootstrap. -/
theorem pbs_step (CH : ℝ) (hCH0 : 0 ≤ CH)
    (hCH : ∀ u g : ℝ × ℝ → ℂ, MemLp u 2 volume → MemLp g 2 volume → WeakLapOn univ u g →
      ∃ v : ℕ × ℕ → ℝ × ℝ → ℂ,
        (∀ β ∈ multiIdx 2, MemLp (v β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (v β)) ∧
        ∑ β ∈ multiIdx 2, ∫ z, ‖v β z‖ ^ 2 ≤ CH * ((∫ z, ‖u z‖ ^ 2) + ∫ z, ‖g z‖ ^ 2))
    (m : ℕ) (u f : ℝ × ℝ → ℂ) (hW : WeakLapOn univ u f) (gF gu : ℕ × ℕ → ℝ × ℝ → ℂ)
    (hF : ∀ α ∈ multiIdx m, MemLp (gF α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) f (gF α))
    (hG : ∀ γ ∈ multiIdx m, MemLp (gu γ) 2 volume ∧ HasWeakDerivOn univ (pdListR γ) u (gu γ)) :
    ∃ gu' : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ β ∈ multiIdx (m + 2), MemLp (gu' β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (gu' β)) ∧
      ∑ β ∈ multiIdx (m + 2), ∫ z, ‖gu' β z‖ ^ 2 ≤
        CH * ((∑ γ ∈ multiIdx m, ∫ z, ‖gu γ z‖ ^ 2) + ∑ α ∈ multiIdx m, ∫ z, ‖gF α z‖ ^ 2) := by
  -- the Laplacian of every derivative of order `≤ m`
  have hL : ∀ γ ∈ multiIdx m, WeakLapOn univ (gu γ) (gF γ) := fun γ hγ =>
    planarLapOfDeriv γ u f (gu γ) (gF γ) hW (hG γ hγ).2 (hF γ hγ).2
  -- second derivatives of each `gu γ`
  have hV : ∀ γ : ℕ × ℕ, ∃ v : ℕ × ℕ → ℝ × ℝ → ℂ, γ ∈ multiIdx m →
      (∀ δ ∈ multiIdx 2, MemLp (v δ) 2 volume ∧ HasWeakDerivOn univ (pdListR δ) (gu γ) (v δ)) ∧
        ∑ δ ∈ multiIdx 2, ∫ z, ‖v δ z‖ ^ 2 ≤
          CH * ((∫ z, ‖gu γ z‖ ^ 2) + ∫ z, ‖gF γ z‖ ^ 2) := by
    intro γ
    by_cases hγ : γ ∈ multiIdx m
    · obtain ⟨v, hv⟩ := hCH (gu γ) (gF γ) (hG γ hγ).1 (hF γ hγ).1 (hL γ hγ)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hγ⟩
  choose V hV using hV
  -- every `β ∈ multiIdx (m+2)` is `p.1 + p.2` for a chosen pair
  have hsplit : ∀ β : ℕ × ℕ, ∃ p : (ℕ × ℕ) × (ℕ × ℕ), β ∈ multiIdx (m + 2) →
      (p.1 ∈ multiIdx m ∧ p.2 ∈ multiIdx 2 ∧ p.1 + p.2 = β) := by
    intro β
    by_cases hβ : β ∈ multiIdx (m + 2)
    · obtain ⟨p, hp⟩ := pbs_split m β hβ
      exact ⟨p, fun _ => hp⟩
    · exact ⟨((0, 0), (0, 0)), fun h => absurd h hβ⟩
  choose p hp using hsplit
  refine ⟨fun β => V (p β).1 (p β).2, ?_, ?_⟩
  · intro β hβ
    obtain ⟨h1, h2, h3⟩ := hp β hβ
    obtain ⟨hVd, _⟩ := hV (p β).1 h1
    obtain ⟨hmem, hwd⟩ := hVd (p β).2 h2
    have hc := pbs_comp_add (hG (p β).1 h1).2 hwd
    rw [h3] at hc
    exact ⟨hmem, hc⟩
  · have hinj : Set.InjOn p (multiIdx (m + 2) : Set (ℕ × ℕ)) := by
      intro x hx y hy hxy
      have hx' : x ∈ multiIdx (m + 2) := Finset.mem_coe.1 hx
      have hy' : y ∈ multiIdx (m + 2) := Finset.mem_coe.1 hy
      calc x = (p x).1 + (p x).2 := (hp x hx').2.2.symm
        _ = (p y).1 + (p y).2 := by rw [hxy]
        _ = y := (hp y hy').2.2
    have hsum1 : ∑ β ∈ multiIdx (m + 2), ∫ z, ‖V (p β).1 (p β).2 z‖ ^ 2 =
        ∑ q ∈ (multiIdx (m + 2)).image p, ∫ z, ‖V q.1 q.2 z‖ ^ 2 := by
      rw [Finset.sum_image hinj]
    have hsub : (multiIdx (m + 2)).image p ⊆ multiIdx m ×ˢ multiIdx 2 := by
      intro q hq
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hq
      exact Finset.mem_product.2 ⟨(hp β hβ).1, (hp β hβ).2.1⟩
    have hsum2 : ∑ q ∈ (multiIdx (m + 2)).image p, ∫ z, ‖V q.1 q.2 z‖ ^ 2 ≤
        ∑ q ∈ multiIdx m ×ˢ multiIdx 2, ∫ z, ‖V q.1 q.2 z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => integral_nonneg fun z => sq_nonneg _)
    have hsum3 : ∑ γ ∈ multiIdx m, ∑ δ ∈ multiIdx 2, ∫ z, ‖V γ δ z‖ ^ 2 ≤
        ∑ γ ∈ multiIdx m, CH * ((∫ z, ‖gu γ z‖ ^ 2) + ∫ z, ‖gF γ z‖ ^ 2) :=
      Finset.sum_le_sum fun γ hγ => (hV γ hγ).2
    calc ∑ β ∈ multiIdx (m + 2), ∫ z, ‖V (p β).1 (p β).2 z‖ ^ 2
        = ∑ q ∈ (multiIdx (m + 2)).image p, ∫ z, ‖V q.1 q.2 z‖ ^ 2 := hsum1
      _ ≤ ∑ q ∈ multiIdx m ×ˢ multiIdx 2, ∫ z, ‖V q.1 q.2 z‖ ^ 2 := hsum2
      _ = ∑ γ ∈ multiIdx m, ∑ δ ∈ multiIdx 2, ∫ z, ‖V γ δ z‖ ^ 2 := Finset.sum_product _ _ _
      _ ≤ ∑ γ ∈ multiIdx m, CH * ((∫ z, ‖gu γ z‖ ^ 2) + ∫ z, ‖gF γ z‖ ^ 2) := hsum3
      _ = CH * ((∑ γ ∈ multiIdx m, ∫ z, ‖gu γ z‖ ^ 2) + ∑ α ∈ multiIdx m, ∫ z, ‖gF α z‖ ^ 2) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-! ### The base case: order `2` -/

/-- Order `2` for `u` from `planarEllipticH2`, with the `f`-data of any order `n`. -/
theorem pbs_h2 (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u f : ℝ × ℝ → ℂ, MemLp u 2 volume →
    MemLp f 2 volume → WeakLapOn univ u f → ∀ gF : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ α ∈ multiIdx n, MemLp (gF α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) f (gF α)) →
      ∃ gu : ℕ × ℕ → ℝ × ℝ → ℂ,
        (∀ β ∈ multiIdx 2, MemLp (gu β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (gu β)) ∧
        ∑ β ∈ multiIdx 2, ∫ z, ‖gu β z‖ ^ 2 ≤
          C * ((∑ α ∈ multiIdx n, ∫ z, ‖gF α z‖ ^ 2) + ∫ z, ‖u z‖ ^ 2) := by
  obtain ⟨CH, hCH0, hCH⟩ := pbs_ell
  refine ⟨CH, hCH0, fun u f hu hf hW gF hF => ?_⟩
  obtain ⟨v, hv1, hv2⟩ := hCH u f hu hf hW
  refine ⟨v, hv1, hv2.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hCH0
  have := pbs_sq_f_le hf hF
  linarith

/-! ### Induction on the order -/

/-- Order `m` for `u`, with the `f`-data of order `m`, bound `F_m + U`. -/
def PBSE (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u f : ℝ × ℝ → ℂ, MemLp u 2 volume → MemLp f 2 volume →
    WeakLapOn univ u f → ∀ gF : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ α ∈ multiIdx m, MemLp (gF α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) f (gF α)) →
      ∃ gu : ℕ × ℕ → ℝ × ℝ → ℂ,
        (∀ β ∈ multiIdx m, MemLp (gu β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (gu β)) ∧
        ∑ β ∈ multiIdx m, ∫ z, ‖gu β z‖ ^ 2 ≤
          C * ((∑ α ∈ multiIdx m, ∫ z, ‖gF α z‖ ^ 2) + ∫ z, ‖u z‖ ^ 2)

/-- Order `m + 2` for `u`, with the `f`-data of order `m`, bound `F_m + U`. -/
def PBSE' (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u f : ℝ × ℝ → ℂ, MemLp u 2 volume → MemLp f 2 volume →
    WeakLapOn univ u f → ∀ gF : ℕ × ℕ → ℝ × ℝ → ℂ,
      (∀ α ∈ multiIdx m, MemLp (gF α) 2 volume ∧ HasWeakDerivOn univ (pdListR α) f (gF α)) →
      ∃ gu : ℕ × ℕ → ℝ × ℝ → ℂ,
        (∀ β ∈ multiIdx (m + 2), MemLp (gu β) 2 volume ∧ HasWeakDerivOn univ (pdListR β) u (gu β)) ∧
        ∑ β ∈ multiIdx (m + 2), ∫ z, ‖gu β z‖ ^ 2 ≤
          C * ((∑ α ∈ multiIdx m, ∫ z, ‖gF α z‖ ^ 2) + ∫ z, ‖u z‖ ^ 2)

/-- `PBSE' m` gives `PBSE (m + 2)`, using monotonicity of the `F`-sums. -/
theorem pbs_E_of_E' (k : ℕ) (h : PBSE' k) : PBSE (k + 2) := by
  unfold PBSE' at h
  obtain ⟨C, hC0, hC⟩ := h
  unfold PBSE
  refine ⟨C, hC0, fun u f hu hf hW gF hF => ?_⟩
  obtain ⟨gu, hgu, hgub⟩ := hC u f hu hf hW gF
    (fun α hα => hF α (multiIdx_mono (Nat.le_add_right k 2) hα))
  refine ⟨gu, hgu, le_trans hgub ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC0
  have := pbs_sum_mono (Nat.le_add_right k 2) gF
  linarith

/-- `PBSE m` gives `PBSE' m`, by one step and `pbs_arith`. -/
theorem pbs_E'_of_E (m : ℕ) (h : PBSE m) : PBSE' m := by
  unfold PBSE at h
  obtain ⟨CE, hCE0, hCE⟩ := h
  obtain ⟨CH, hCH0, hCH⟩ := pbs_ell
  unfold PBSE'
  refine ⟨CH * (CE + 1), mul_nonneg hCH0 (by linarith), fun u f hu hf hW gF hF => ?_⟩
  obtain ⟨gu, hgu, hgub⟩ := hCE u f hu hf hW gF hF
  obtain ⟨gu', hgu', hgu'b⟩ := pbs_step CH hCH0 hCH m u f hW gF gu hF hgu
  refine ⟨gu', hgu', ?_⟩
  have hU : 0 ≤ ∫ z, ‖u z‖ ^ 2 := integral_nonneg fun z => sq_nonneg _
  exact pbs_arith hCE0 hCH0 hU hgub hgu'b

/-- Base `PBSE 1`: the order-two base restricted to order one. -/
theorem pbs_E_one : PBSE 1 := by
  obtain ⟨C, hC0, hC⟩ := pbs_h2 1
  unfold PBSE
  refine ⟨C, hC0, fun u f hu hf hW gF hF => ?_⟩
  obtain ⟨gu, hgu, hgub⟩ := hC u f hu hf hW gF hF
  refine ⟨gu, fun β hβ => hgu β (multiIdx_mono (by norm_num : (1 : ℕ) ≤ 2) hβ), ?_⟩
  refine le_trans ?_ hgub
  exact Finset.sum_le_sum_of_subset_of_nonneg (multiIdx_mono (by norm_num : (1 : ℕ) ≤ 2))
    (fun β _ _ => integral_nonneg fun z => sq_nonneg _)

/-- Base `PBSE' 0`: the order-two base. -/
theorem pbs_E'_zero : PBSE' 0 := by
  unfold PBSE'
  obtain ⟨C, hC0, hC⟩ := pbs_h2 0
  exact ⟨C, hC0, hC⟩

/-- All orders, by induction in steps of one. -/
theorem pbs_boot_all (n : ℕ) : PBSE (n + 1) ∧ PBSE' n := by
  induction n with
  | zero => exact ⟨pbs_E_one, pbs_E'_zero⟩
  | succ k ih => exact ⟨pbs_E_of_E' k ih.2, pbs_E'_of_E (k + 1) ih.1⟩

/-! ### Main theorem -/

/-- **`PartI:C09` (source lines 1141-1142)**: elliptic regularity iterated to all orders. -/
theorem planarBootstrap (j : ℕ) : PlanarBootstrap j := by
  rcases le_or_gt j 2 with hj | hj
  · obtain ⟨C, hC0, hC⟩ := pbs_h2 (j - 2)
    unfold PlanarBootstrap
    refine ⟨C, fun u f hu hf hW gF hF => ?_⟩
    obtain ⟨gu, hgu, hgub⟩ := hC u f hu hf hW gF hF
    refine ⟨gu, fun β hβ => hgu β (multiIdx_mono hj hβ), ?_⟩
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (multiIdx_mono hj)
      (fun β _ _ => integral_nonneg fun z => sq_nonneg _)) hgub
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
    have h2 := (pbs_boot_all n).2
    unfold PBSE' at h2
    obtain ⟨C, _, hC⟩ := h2
    unfold PlanarBootstrap
    rw [Nat.add_sub_cancel]
    exact ⟨C, hC⟩

end UnforcedLeray.Short.PartI
