import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Defs

/-!
# `KTOrderMinusOne` by induction on the level (assembly)

Source of record: `the November 2 reference manuscript` lines 3052-3058
(the localized adjoint interaction is of order `-1`; derivatives commute with the translation
invariant kernel and fall on `f B` by Leibniz).  See `KT/Defs.lean` for the design.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Operations on cell jets -/

theorem IsCellJet.mono {c m : ℝ} {k k' : ℕ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (h : IsCellJet c m k f D) (hk : k' ≤ k) : IsCellJet c m k' f D where
  base := h.base
  periodic w hw := h.periodic w (hw.trans hk)
  memX w hw := h.memX w (hw.trans hk)
  deriv j w hw := h.deriv j w (lt_of_lt_of_le hw hk)

/-- The jet of `∂_i f`: `w ↦ ∂^w ∂_i f = D (w ++ [i])` (the convention `D (j :: w) = ∂_j (D w)`). -/
theorem IsCellJet.shift {c m : ℝ} {k : ℕ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (h : IsCellJet c m (k + 1) f D) (i : Fin 2) :
    IsCellJet c m k (D [i]) (fun w => D (w ++ [i])) where
  base := rfl
  periodic w hw := h.periodic (w ++ [i]) (by simpa using Nat.succ_le_succ hw)
  memX w hw := h.memX (w ++ [i]) (by simpa using Nat.succ_le_succ hw)
  deriv j w hw := h.deriv j (w ++ [i]) (by simpa using Nat.succ_lt_succ hw)

theorem IsCellJet.add {c m : ℝ} {k : ℕ} {f f' : ℝ × ℝ → ℂ} {D D' : List (Fin 2) → ℝ × ℝ → ℂ}
    (hAdd : KTWeakAdd) (h : IsCellJet c m k f D) (h' : IsCellJet c m k f' D') :
    IsCellJet c m k (f + f') (D + D') where
  base := by
    funext x
    have e1 := congrFun h.base x
    have e2 := congrFun h'.base x
    simp [e1, e2]
  periodic w hw x := by
    have e1 := h.periodic w hw x
    have e2 := h'.periodic w hw x
    simp [e1, e2]
  memX w hw := (h.memX w hw).add (h'.memX w hw)
  deriv j w hw := hAdd c j _ _ _ _ (h.deriv j w hw) (h'.deriv j w hw)

theorem jetNorm_mono (c m : ℝ) {k k' : ℕ} (hk : k ≤ k') (D : List (Fin 2) → ℝ × ℝ → ℂ) :
    jetNorm c m k D ≤ jetNorm c m k' D := by
  unfold jetNorm
  exact Finset.sum_le_sum_of_subset fun w hw => mem_wordsLE.2 ((mem_wordsLE.1 hw).trans hk)

theorem jetNorm_shift_le (c m : ℝ) (k : ℕ) (i : Fin 2) (D : List (Fin 2) → ℝ × ℝ → ℂ) :
    jetNorm c m k (fun w => D (w ++ [i])) ≤ jetNorm c m (k + 1) D := by
  unfold jetNorm
  have : ∑ w ∈ wordsLE k, xNorm c (-m) (D (w ++ [i])) =
      ∑ w ∈ (wordsLE k).image (fun w => w ++ [i]), xNorm c (-m) (D w) := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact List.append_cancel_right h
  rw [this]
  refine Finset.sum_le_sum_of_subset fun w hw => ?_
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  exact mem_wordsLE.2 (by simpa using Nat.succ_le_succ (mem_wordsLE.1 hv))

theorem ktSplit (w : List (Fin 2)) : w = [] ∨ ∃ (L : List (Fin 2)) (k : Fin 2), w = L ++ [k] := by
  rcases List.eq_nil_or_concat w with h | ⟨L, k, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, k, by simpa using h⟩

/-- Gluing: the jet `∂^{w'} ∂_k χ = G k w'` of the derivatives into a jet of `χ`
(`D (w' ++ [k]) = G k w'`, `D [] = χ`). -/
def ktGlue (χ : ℝ × ℝ → ℂ) (G : Fin 2 → List (Fin 2) → ℝ × ℝ → ℂ) :
    List (Fin 2) → ℝ × ℝ → ℂ := fun w =>
  match w.getLast? with
  | none => χ
  | some k => G k w.dropLast

theorem ktGlue_nil (χ : ℝ × ℝ → ℂ) (G : Fin 2 → List (Fin 2) → ℝ × ℝ → ℂ) :
    ktGlue χ G [] = χ := rfl

theorem ktGlue_append (χ : ℝ × ℝ → ℂ) (G : Fin 2 → List (Fin 2) → ℝ × ℝ → ℂ) (L : List (Fin 2))
    (k : Fin 2) : ktGlue χ G (L ++ [k]) = G k L := by
  simp [ktGlue]

/-! ## The induction -/

theorem ktAt_succ {m c : ℝ} (hm : 1 < m) (hc : 1 ≤ c) (hBase : KTBase m) (hComm : KTCommute m)
    (hCD : KTCoeffDeriv) (hAdd : KTWeakAdd) (j : ℕ) (ih : KTAt m c j) : KTAt m c (j + 1) := by
  intro B A hBs hBp hBb
  have hb0 : KTCoeffBound m 0 B A := fun l i hi x => hBb l i (hi.trans (Nat.zero_le _ |>.trans
    (Nat.le_succ _))) x
  have hbj : KTCoeffBound m j B A := fun l i hi x => hBb l i (hi.trans (Nat.le_succ _)) x
  have hb1 : KTCoeffBound m 1 B A := fun l i hi x => hBb l i (by omega) x
  obtain ⟨C0, hC0, H0⟩ := hBase hm c hc B A hBs hBp hb0
  obtain ⟨C1, hC1, H1⟩ := ih B A hBs hBp hbj
  have hder := fun k : Fin 2 => hCD m c j B A k hBs hBp hBb
  choose C2 hC2 H2 using fun k : Fin 2 =>
    ih (fun l => B0579.pd k (B l)) A (hder k).1 (hder k).2.1 (hder k).2.2
  refine ⟨C0 + C1 + C2 0 + C2 1, by linarith [hC2 0, hC2 1], ?_⟩
  intro f D hJ
  obtain ⟨χ, Dχ, hχJ, hχN, hχP⟩ := H0 f D (hJ.mono (Nat.zero_le _))
  -- the two summands for each direction
  have hex : ∀ k : Fin 2, ∃ (χ₁ χ₂ : ℝ × ℝ → ℂ) (E₁ E₂ : List (Fin 2) → ℝ × ℝ → ℂ),
      IsCellJet c m (j + 1) χ₁ E₁ ∧ IsCellJet c m (j + 1) χ₂ E₂ ∧
      (∀ w : List (Fin 2), w.length ≤ j + 1 →
        xNorm c (-m) (E₁ w) ≤ ENNReal.ofReal C1 * jetNorm c m j (fun w => D (w ++ [k]))) ∧
      (∀ w : List (Fin 2), w.length ≤ j + 1 →
        xNorm c (-m) (E₂ w) ≤ ENNReal.ofReal (C2 k) * jetNorm c m j D) ∧
      KTPairing c (D [k]) B χ₁ ∧ KTPairing c f (fun l => B0579.pd k (B l)) χ₂ := by
    intro k
    obtain ⟨χ₁, E₁, a1, a2, a3⟩ := H1 (D [k]) (fun w => D (w ++ [k])) (hJ.shift k)
    obtain ⟨χ₂, E₂, b1, b2, b3⟩ := H2 k f D (hJ.mono (Nat.le_succ _))
    exact ⟨χ₁, χ₂, E₁, E₂, a1, b1, a2, b2, a3, b3⟩
  choose χ₁ χ₂ E₁ E₂ hE₁ hE₂ hN₁ hN₂ hP₁ hP₂ using hex
  have hperiod0 : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
    intro x
    have := hJ.periodic [] (Nat.zero_le _) x
    rwa [hJ.base] at this
  -- the weak commutation
  have hcomm : ∀ k : Fin 2, HasWeakCellDerivC c k χ (χ₁ k + χ₂ k) := by
    intro k
    have hχ0 : MemLp χ 2 (B0579.cellMeasure c (-m)) := by
      have := hχJ.memX [] (Nat.zero_le _)
      rwa [hχJ.base] at this
    have hf0 : MemLp f 2 (B0579.cellMeasure c (-m)) := by
      have := hJ.memX [] (Nat.zero_le _)
      rwa [hJ.base] at this
    exact hComm hm c hc B A k hBs hBp hb1 f (D [k]) χ (χ₁ k) (χ₂ k) hf0
      (by simpa using hJ.memX [k] (by simp)) hχ0
      (by simpa [(hE₁ k).base] using (hE₁ k).memX [] (Nat.zero_le _))
      (by simpa [(hE₂ k).base] using (hE₂ k).memX [] (Nat.zero_le _))
      (by simpa [hJ.base] using hJ.deriv k [] (Nat.succ_pos _)) hχP (hP₁ k) (hP₂ k)
  refine ⟨χ, ktGlue χ (fun k => E₁ k + E₂ k), ?_, ?_, hχP⟩
  · have hJk : ∀ k : Fin 2, IsCellJet c m (j + 1) (χ₁ k + χ₂ k) (E₁ k + E₂ k) :=
      fun k => (hE₁ k).add hAdd (hE₂ k)
    have hbase : ∀ k : Fin 2, (E₁ k + E₂ k) [] = χ₁ k + χ₂ k := fun k => (hJk k).base
    have hχ0 : ktGlue χ (fun k => E₁ k + E₂ k) [] = χ := rfl
    refine ⟨hχ0, ?_, ?_, ?_⟩
    · intro w hw x
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hχJ.periodic [] (Nat.zero_le _) x
        rwa [hχJ.base] at this
      · rw [ktGlue_append]
        exact (hJk k).periodic L (by simpa using hw) x
    · intro w hw
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hχJ.memX [] (Nat.zero_le _)
        rwa [hχJ.base] at this
      · rw [ktGlue_append]
        exact (hJk k).memX L (by simpa using hw)
    · intro i w hw
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hcomm i
        rw [show [i] = [] ++ [i] from rfl, ktGlue_append, ktGlue_nil]
        simpa [← hbase i] using this
      · rw [show i :: (L ++ [k]) = (i :: L) ++ [k] from rfl, ktGlue_append, ktGlue_append]
        exact (hJk k).deriv i L (by simpa using hw)
  · intro w hw
    rcases ktSplit w with rfl | ⟨w', k, rfl⟩
    · calc xNorm c (-m) (ktGlue χ (fun k => E₁ k + E₂ k) []) = xNorm c (-m) χ := rfl
        _ ≤ ENNReal.ofReal C0 * jetNorm c m 0 D := by
          have := hχN [] (Nat.zero_le _)
          rwa [hχJ.base] at this
        _ ≤ ENNReal.ofReal (C0 + C1 + C2 0 + C2 1) * jetNorm c m (j + 1) D := by
          refine mul_le_mul' ?_ (jetNorm_mono c m (Nat.zero_le _) D)
          exact ENNReal.ofReal_le_ofReal (by linarith [hC1, hC2 0, hC2 1])
    · rw [ktGlue_append]
      have hw' : w'.length ≤ j + 1 := by simpa using hw
      have e : xNorm c (-m) ((E₁ k + E₂ k) w') ≤
          xNorm c (-m) (E₁ k w') + xNorm c (-m) (E₂ k w') := by
        unfold xNorm
        exact eLpNorm_add_le ((hE₁ k).memX w' hw').aestronglyMeasurable
          ((hE₂ k).memX w' hw').aestronglyMeasurable (by norm_num)
      have j1 : jetNorm c m j (fun w => D (w ++ [k])) ≤ jetNorm c m (j + 1) D :=
        jetNorm_shift_le c m j k D
      have j2 : jetNorm c m j D ≤ jetNorm c m (j + 1) D := jetNorm_mono c m (Nat.le_succ _) D
      have hk : ENNReal.ofReal C1 ≤ ENNReal.ofReal (C0 + C1 + C2 0 + C2 1) ∧
          ENNReal.ofReal (C2 k) ≤ ENNReal.ofReal (C0 + C1 + C2 0 + C2 1) := by
        constructor
        · exact ENNReal.ofReal_le_ofReal (by linarith [hC0, hC2 0, hC2 1])
        · refine ENNReal.ofReal_le_ofReal ?_
          fin_cases k
          · simp; linarith [hC0, hC1, hC2 1]
          · simp; linarith [hC0, hC1, hC2 0]
      have hsum : ENNReal.ofReal C1 + ENNReal.ofReal (C2 k) ≤
          ENNReal.ofReal (C0 + C1 + C2 0 + C2 1) := by
        rw [← ENNReal.ofReal_add hC1 (hC2 k)]
        refine ENNReal.ofReal_le_ofReal ?_
        fin_cases k
        · simp; linarith [hC0, hC2 1]
        · simp; linarith [hC0, hC2 0]
      calc xNorm c (-m) ((E₁ k + E₂ k) w')
          ≤ xNorm c (-m) (E₁ k w') + xNorm c (-m) (E₂ k w') := e
        _ ≤ ENNReal.ofReal C1 * jetNorm c m j (fun w => D (w ++ [k])) +
            ENNReal.ofReal (C2 k) * jetNorm c m j D :=
          add_le_add (hN₁ k w' hw') (hN₂ k w' hw')
        _ ≤ ENNReal.ofReal C1 * jetNorm c m (j + 1) D +
            ENNReal.ofReal (C2 k) * jetNorm c m (j + 1) D :=
          add_le_add (mul_le_mul' le_rfl j1) (mul_le_mul' le_rfl j2)
        _ = (ENNReal.ofReal C1 + ENNReal.ofReal (C2 k)) * jetNorm c m (j + 1) D := by
          rw [add_mul]
        _ ≤ _ := mul_le_mul' hsum le_rfl

theorem kTOrderMinusOne_of (m : ℝ) (hBase : KTBase m) (hComm : KTCommute m) (hCD : KTCoeffDeriv)
    (hAdd : KTWeakAdd) : KTOrderMinusOne m := by
  intro hm c hc j
  induction j with
  | zero => exact hBase hm c hc
  | succ j ih => exact ktAt_succ hm hc hBase hComm hCD hAdd j ih

end UnforcedLeray.Short.IIIa
