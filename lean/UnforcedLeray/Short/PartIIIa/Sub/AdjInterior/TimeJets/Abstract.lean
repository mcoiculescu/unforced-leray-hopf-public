import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/6`: the time jets from an operator family (abstract induction)

Source: `the November 2 reference manuscript` (SP) line 3060
(`∂_rφ = L(r)φ`, `L(r) = -(νΔ + v(r)·∇ - K_c^T(·∇E(r)))`).

For an operator family `L i r` acting on derivative fields (`L i` is the `i`-th age derivative of
`L`), the candidate jets are `Φ 0 = φ`, `Φ (j + 1) = Σ_{i ≤ j} (j choose i) L i (Φ (j - i))`
(`tjSeq`, with the chosen fields `jetOf` of each `Φ k`).  `tjSeq_spec`: if `L i` preserves
`C(I; H^∞_{-m,c})`, satisfies the product rule `∂_r(L i Ψ) = L (i+1) Ψ + L i ∂_rΨ`, `∂_rφ = L 0 φ`,
and `X`-derivatives upgrade to the fields, then `tjSeq` is a family of time jets
(`IsAdjTimeJets`): strong induction on `j`, the Pascal step is `Finset.sum_choose_succ_mul`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The chosen all-orders fields of `f` on `I` (`fun r _ => f r` if there are none). -/
def jetOf (c m : ℝ) (I : Set ℝ) (f : ℝ → ℝ × ℝ → ℂ) : ℝ → List (Fin 2) → ℝ × ℝ → ℂ := by
  classical
  exact if h : ∃ D, AdjHkAll c m I f D then h.choose else fun r _ => f r

theorem jetOf_spec {c m : ℝ} {I : Set ℝ} {f : ℝ → ℝ × ℝ → ℂ} (h : ∃ D, AdjHkAll c m I f D) :
    AdjHkAll c m I f (jetOf c m I f) := by
  unfold jetOf
  split
  · next h' => exact h'.choose_spec
  · next h' => exact absurd h h'

/-- **The candidate time jets** `Φ 0 = φ`, `Φ (j + 1) = Σ_{i ≤ j} (j choose i) L i (Φ (j - i))`. -/
def tjSeq (jet : (ℝ → ℝ × ℝ → ℂ) → ℝ → List (Fin 2) → ℝ × ℝ → ℂ)
    (L : ℕ → ℝ → (List (Fin 2) → ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) :
    ℕ → ℝ → ℝ × ℝ → ℂ
  | 0 => φ
  | j + 1 => fun r x => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℂ) * L i r (jet (tjSeq jet L φ (j - i)) r) x
termination_by j => j
decreasing_by omega

theorem tjSeq_zero (jet : (ℝ → ℝ × ℝ → ℂ) → ℝ → List (Fin 2) → ℝ × ℝ → ℂ)
    (L : ℕ → ℝ → (List (Fin 2) → ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) :
    tjSeq jet L φ 0 = φ := by
  rw [tjSeq]

theorem tjSeq_succ (jet : (ℝ → ℝ × ℝ → ℂ) → ℝ → List (Fin 2) → ℝ × ℝ → ℂ)
    (L : ℕ → ℝ → (List (Fin 2) → ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (j : ℕ) :
    tjSeq jet L φ (j + 1) = fun r x => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℂ) * L i r (jet (tjSeq jet L φ (j - i)) r) x := by
  rw [tjSeq]

/-! ## Congruence and finite sums -/

theorem adjHkAll_congr {c m : ℝ} {I : Set ℝ} {f g : ℝ → ℝ × ℝ → ℂ}
    {D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} (h : AdjHkAll c m I f D) (hfg : ∀ r ∈ I, f r = g r) :
    AdjHkAll c m I g D := by
  refine ⟨fun r hr k => ?_, h.2⟩
  have hj := h.1 r hr k
  exact { base := hj.base.trans (hfg r hr), periodic := hj.periodic, memX := hj.memX,
          deriv := hj.deriv }

theorem hasXDerivOn_congr {c m : ℝ} {I : Set ℝ} {f f' g g' : ℝ → ℝ × ℝ → ℂ}
    (h : HasXDerivOn c m I f f') (hf : ∀ r ∈ I, f r = g r) (hf' : ∀ r ∈ I, f' r = g' r) :
    HasXDerivOn c m I g g' := by
  intro r hr
  refine (h r hr).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  rw [hf r' hr'.1, hf r hr, hf' r hr]

/-- The memberships `f r ∈ X_{-m,c}` of a `C(I; H^∞_{-m,c})` family. -/
theorem AdjHkAll.memLp {c m : ℝ} {I : Set ℝ} {f : ℝ → ℝ × ℝ → ℂ}
    {D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ} (h : AdjHkAll c m I f D) {r : ℝ} (hr : r ∈ I) :
    MemLp (f r) 2 (B0579.cellMeasure c (-m)) := by
  have hm := (h.1 r hr 0).memX [] (by simp)
  rwa [(h.1 r hr 0).base] at hm

theorem adjHkAll_sum (hL : AdjHkAllLinear) {c m : ℝ} {I : Set ℝ} (s : Finset ℕ) (α : ℕ → ℂ)
    (F : ℕ → ℝ → ℝ × ℝ → ℂ) (DF : ℕ → ℝ → List (Fin 2) → ℝ × ℝ → ℂ)
    (h : ∀ i ∈ s, AdjHkAll c m I (F i) (DF i)) :
    AdjHkAll c m I (fun r x => ∑ i ∈ s, α i * F i r x)
      (fun r w x => ∑ i ∈ s, α i * DF i r w x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (hL c m I).1
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h3 := (hL c m I).2 _ _ _ _ (α i) 1 h1 h2
    simpa [Finset.sum_insert hi] using h3

theorem hasXDerivOn_sum (hL : HasXDerivOnLinear) {c m : ℝ} {I : Set ℝ} (s : Finset ℕ)
    (α : ℕ → ℂ) (F F' : ℕ → ℝ → ℝ × ℝ → ℂ)
    (hm : ∀ i ∈ s, ∀ r ∈ I, MemLp (F i r) 2 (B0579.cellMeasure c (-m)) ∧
      MemLp (F' i r) 2 (B0579.cellMeasure c (-m)))
    (h : ∀ i ∈ s, HasXDerivOn c m I (F i) (F' i)) :
    HasXDerivOn c m I (fun r x => ∑ i ∈ s, α i * F i r x)
      (fun r x => ∑ i ∈ s, α i * F' i r x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (hL c m I).1
  | insert i s hi ih =>
    have hm' : ∀ j ∈ s, ∀ r ∈ I, MemLp (F j r) 2 (B0579.cellMeasure c (-m)) ∧
        MemLp (F' j r) 2 (B0579.cellMeasure c (-m)) :=
      fun j hj => hm j (Finset.mem_insert_of_mem hj)
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih hm' (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have hmem : ∀ r ∈ I, MemLp (F i r) 2 (B0579.cellMeasure c (-m)) ∧
        MemLp (F' i r) 2 (B0579.cellMeasure c (-m)) ∧
        MemLp (fun x => ∑ j ∈ s, α j * F j r x) 2 (B0579.cellMeasure c (-m)) ∧
        MemLp (fun x => ∑ j ∈ s, α j * F' j r x) 2 (B0579.cellMeasure c (-m)) := by
      intro r hr
      refine ⟨(hm i (Finset.mem_insert_self i s) r hr).1,
        (hm i (Finset.mem_insert_self i s) r hr).2, ?_, ?_⟩
      · exact memLp_finsetSum s (fun j hj => (hm' j hj r hr).1.const_mul (α j))
      · exact memLp_finsetSum s (fun j hj => (hm' j hj r hr).2.const_mul (α j))
    have h3 := (hL c m I).2 _ _ _ _ (α i) 1 hmem h1 h2
    simpa [Finset.sum_insert hi] using h3

/-! ## The abstract induction -/

/-- **Time jets from an operator family.** -/
theorem tjSeq_spec {c m : ℝ} {I : Set ℝ}
    (L : ℕ → ℝ → (List (Fin 2) → ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ)
    (hLin : AdjHkAllLinear) (hXLin : HasXDerivOnLinear)
    (hφ : ∃ D, AdjHkAll c m I φ D)
    (hS : ∀ (i : ℕ) (f : ℝ → ℝ × ℝ → ℂ) (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll c m I f D → ∃ D', AdjHkAll c m I (fun r => L i r (D r)) D')
    (hD : ∀ (i : ℕ) (f f' : ℝ → ℝ × ℝ → ℂ) (D D' : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll c m I f D → AdjHkAll c m I f' D' →
      (∀ w : List (Fin 2), HasXDerivOn c m I (fun r => D r w) (fun r => D' r w)) →
      HasXDerivOn c m I (fun r => L i r (D r))
        (fun r x => L (i + 1) r (D r) x + L i r (D' r) x))
    (hB : ∀ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ, AdjHkAll c m I φ D →
      HasXDerivOn c m I φ (fun r => L 0 r (D r)))
    (hU : ∀ (f f' : ℝ → ℝ × ℝ → ℂ) (D D' : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll c m I f D → AdjHkAll c m I f' D' → HasXDerivOn c m I f f' →
      ∀ w : List (Fin 2), HasXDerivOn c m I (fun r => D r w) (fun r => D' r w)) :
    IsAdjTimeJets c m I (tjSeq (jetOf c m I) L φ) := by
  have hsucc : ∀ n : ℕ, tjSeq (jetOf c m I) L φ (n + 1) = fun r x =>
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * L i r (jetOf c m I (tjSeq (jetOf c m I) L φ (n - i)) r) x :=
    fun n => tjSeq_succ _ _ _ n
  have h0 : tjSeq (jetOf c m I) L φ 0 = φ := tjSeq_zero _ _ _
  have hJ : ∀ f : ℝ → ℝ × ℝ → ℂ, (∃ D, AdjHkAll c m I f D) →
      AdjHkAll c m I f (jetOf c m I f) := fun f h => jetOf_spec h
  generalize tjSeq (jetOf c m I) L φ = Φ at hsucc h0 ⊢
  generalize jetOf c m I = J at hsucc hJ
  -- smoothness of every jet
  have hsm : ∀ j : ℕ, ∃ D, AdjHkAll c m I (Φ j) D := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases j with _ | n
      · rw [h0]; exact hφ
      · have hex : ∀ i ∈ Finset.range (n + 1), ∃ D', AdjHkAll c m I
            (fun r x => L i r (J (Φ (n - i)) r) x) D' :=
          fun i _ => hS i _ _ (hJ _ (ih (n - i) (by omega)))
        choose! DD hDD using hex
        rw [hsucc n]
        exact ⟨_, adjHkAll_sum hLin (Finset.range (n + 1)) (fun i => (n.choose i : ℂ))
          (fun i r x => L i r (J (Φ (n - i)) r) x) DD hDD⟩
  have hjet : ∀ j : ℕ, AdjHkAll c m I (Φ j) (J (Φ j)) := fun j => hJ _ (hsm j)
  have hTmem : ∀ (i k : ℕ), ∀ r ∈ I,
      MemLp (L i r (J (Φ k) r)) 2 (B0579.cellMeasure c (-m)) := by
    intro i k r hr
    obtain ⟨D', hD'⟩ := hS i _ _ (hjet k)
    exact hD'.memLp hr
  -- the derivatives
  have hder : ∀ j : ℕ, HasXDerivOn c m I (Φ j) (Φ (j + 1)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases j with _ | n
      · have hB0 := hB _ (h0 ▸ hjet 0)
        refine hasXDerivOn_congr hB0 (fun r _ => h0.symm ▸ rfl) (fun r _ => ?_)
        rw [hsucc 0]
        funext x
        simp [h0]
      · have hk : ∀ k ≤ n, ∀ w : List (Fin 2),
            HasXDerivOn c m I (fun r => J (Φ k) r w) (fun r => J (Φ (k + 1)) r w) :=
          fun k hk => hU _ _ _ _ (hjet k) (hjet (k + 1)) (ih k (by omega))
        have hterm : ∀ i ∈ Finset.range (n + 1), HasXDerivOn c m I
            (fun r x => L i r (J (Φ (n - i)) r) x)
            (fun r x => L (i + 1) r (J (Φ (n - i)) r) x + L i r (J (Φ (n - i + 1)) r) x) :=
          fun i hi => hD i _ _ _ _ (hjet (n - i)) (hjet (n - i + 1)) (hk (n - i) (by omega))
        have hmem : ∀ i ∈ Finset.range (n + 1), ∀ r ∈ I,
            MemLp (L i r (J (Φ (n - i)) r)) 2 (B0579.cellMeasure c (-m)) ∧
            MemLp (fun x => L (i + 1) r (J (Φ (n - i)) r) x + L i r (J (Φ (n - i + 1)) r) x) 2
              (B0579.cellMeasure c (-m)) :=
          fun i _ r hr => ⟨hTmem i (n - i) r hr,
            (hTmem (i + 1) (n - i) r hr).add (hTmem i (n - i + 1) r hr)⟩
        have hsum := hasXDerivOn_sum hXLin (Finset.range (n + 1)) (fun i => (n.choose i : ℂ))
          (fun i r x => L i r (J (Φ (n - i)) r) x)
          (fun i r x => L (i + 1) r (J (Φ (n - i)) r) x + L i r (J (Φ (n - i + 1)) r) x)
          hmem hterm
        have hr2 : Φ (n + 1 + 1) = fun r x => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
            (L (i + 1) r (J (Φ (n - i)) r) x + L i r (J (Φ (n - i + 1)) r) x) := by
          rw [hsucc (n + 1)]
          funext r x
          have key := Finset.sum_choose_succ_mul (R := ℂ) (fun i k => L i r (J (Φ k) r) x) n
          have hc : ∀ i ∈ Finset.range (n + 1),
              (n.choose i : ℂ) * L i r (J (Φ (n - i + 1)) r) x =
                (n.choose i : ℂ) * L i r (J (Φ (n + 1 - i)) r) x := by
            intro i hi
            have hi' := Finset.mem_range.1 hi
            have : n - i + 1 = n + 1 - i := by omega
            rw [this]
          rw [Finset.sum_congr rfl (fun i _ => mul_add _ _ _), Finset.sum_add_distrib,
            Finset.sum_congr rfl hc]
          exact key.trans (add_comm _ _)
        rw [hsucc n, hr2]
        exact hsum
  exact (isAdjTimeJets_iff c m I Φ).2 ⟨fun j k => adjHkOn_of_adjHkAll (hjet j) k, hder⟩

end UnforcedLeray.Short.IIIa
