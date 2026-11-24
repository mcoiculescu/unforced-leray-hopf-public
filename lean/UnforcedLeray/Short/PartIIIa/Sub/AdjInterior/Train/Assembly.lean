import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq

/-!
# `PartIII-a:T21/2/7/2/1/1/2`: `TrainSTJetsOfBUC` from its leaves

Source: `the November 2 reference manuscript` (SP) lines 270-288 (the `BUC` train,
the scalar vorticity equation, zero circulation, oddness), 438-461 (`sct:heat`), 2866-2870 (every
fixed weighted derivative norm), 2081-2084 (`K_c`). Vocabulary and leaves: `Train/Defs.lean`.

* `tjAbstractInduction_of`: the induction on the number of age letters (from `TjWPerm`,
  `TjWLeibniz`, `TjWLinear`);
* `tjTrainSpace_of`: the words with no age letter (from `TjTrainVort`, `TjSliceNorm`,
  `TjSpatialInterp`, `TjVortDecay`, `TjLadGrad`, `TjWLinear`);
* `tjTrainKc_of`: the velocity words from the vorticity words (from `TjTrainBSRep`, `TjKcBound`,
  `TjKcDerivSpace`, `TjKcDerivTime`, `TjWPeriodic`, `TjWLinear`);
* `trainSTJetsOfBUC_of`: `TrainSTJetsOfBUC m` (with `TjJetNorm`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Algebra of the bounds -/

section Bounds

variable {m : ℝ} {f g : ℝ × (ℝ × ℝ) → ℝ}

theorem TjWBdd.congr (hf : TjWBdd m f) (h : ∀ ρ : ℝ, 0 ≤ ρ → ∀ x, f (ρ, x) = g (ρ, x)) :
    TjWBdd m g := by
  intro S hS
  obtain ⟨C, hC⟩ := hf S hS
  exact ⟨C, fun ρ hρ x => by rw [← h ρ hρ.1 x]; exact hC ρ hρ x⟩

theorem TjUBdd.congr (hf : TjUBdd f) (h : ∀ ρ : ℝ, 0 ≤ ρ → ∀ x, f (ρ, x) = g (ρ, x)) :
    TjUBdd g := by
  intro S hS
  obtain ⟨C, hC⟩ := hf S hS
  exact ⟨C, fun ρ hρ x => by rw [← h ρ hρ.1 x]; exact hC ρ hρ x⟩

theorem TjWBdd.add (hf : TjWBdd m f) (hg : TjWBdd m g) : TjWBdd m (fun p => f p + g p) := by
  intro S hS
  obtain ⟨C₁, h₁⟩ := hf S hS
  obtain ⟨C₂, h₂⟩ := hg S hS
  refine ⟨C₁ + C₂, fun ρ hρ x => ?_⟩
  have hw := (tjWt_pos m x).le
  calc tjWt m x * |f (ρ, x) + g (ρ, x)| ≤ tjWt m x * (|f (ρ, x)| + |g (ρ, x)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
    _ = tjWt m x * |f (ρ, x)| + tjWt m x * |g (ρ, x)| := mul_add _ _ _
    _ ≤ C₁ + C₂ := add_le_add (h₁ ρ hρ x) (h₂ ρ hρ x)

theorem TjWBdd.sub (hf : TjWBdd m f) (hg : TjWBdd m g) : TjWBdd m (fun p => f p - g p) := by
  intro S hS
  obtain ⟨C₁, h₁⟩ := hf S hS
  obtain ⟨C₂, h₂⟩ := hg S hS
  refine ⟨C₁ + C₂, fun ρ hρ x => ?_⟩
  have hw := (tjWt_pos m x).le
  calc tjWt m x * |f (ρ, x) - g (ρ, x)| ≤ tjWt m x * (|f (ρ, x)| + |g (ρ, x)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hw
    _ = tjWt m x * |f (ρ, x)| + tjWt m x * |g (ρ, x)| := mul_add _ _ _
    _ ≤ C₁ + C₂ := add_le_add (h₁ ρ hρ x) (h₂ ρ hρ x)

theorem TjWBdd.const_mul (r : ℝ) (hf : TjWBdd m f) : TjWBdd m (fun p => r * f p) := by
  intro S hS
  obtain ⟨C, hC⟩ := hf S hS
  refine ⟨|r| * C, fun ρ hρ x => ?_⟩
  rw [abs_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC ρ hρ x) (abs_nonneg r)

theorem TjWBdd.mul_left (hf : TjUBdd f) (hg : TjWBdd m g) :
    TjWBdd m (fun p => f p * g p) := by
  intro S hS
  obtain ⟨C₁, h₁⟩ := hf S hS
  obtain ⟨C₂, h₂⟩ := hg S hS
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (h₁ 0 ⟨le_rfl, hS⟩ (0, 0))
  refine ⟨C₁ * C₂, fun ρ hρ x => ?_⟩
  have hw := (tjWt_pos m x).le
  calc tjWt m x * |f (ρ, x) * g (ρ, x)| = |f (ρ, x)| * (tjWt m x * |g (ρ, x)|) := by
        rw [abs_mul]; ring
    _ ≤ C₁ * (tjWt m x * |g (ρ, x)|) :=
        mul_le_mul_of_nonneg_right (h₁ ρ hρ x) (mul_nonneg hw (abs_nonneg _))
    _ ≤ C₁ * C₂ := mul_le_mul_of_nonneg_left (h₂ ρ hρ x) hC₁

theorem TjWBdd.list_sum {α : Type*} (l : List α) (F : α → ℝ × (ℝ × ℝ) → ℝ)
    (hF : ∀ a ∈ l, TjWBdd m (F a)) : TjWBdd m (fun p => (l.map (fun a => F a p)).sum) := by
  induction l with
  | nil =>
    intro S _
    exact ⟨0, fun ρ _ x => by simp⟩
  | cons a l ih =>
    have h1 := hF a (by simp)
    have h2 := ih (fun b hb => hF b (by simp [hb]))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem TjUBdd.sub (hf : TjUBdd f) (hg : TjUBdd g) : TjUBdd (fun p => f p - g p) := by
  intro S hS
  obtain ⟨C₁, h₁⟩ := hf S hS
  obtain ⟨C₂, h₂⟩ := hg S hS
  exact ⟨C₁ + C₂, fun ρ hρ x => (abs_sub _ _).trans (add_le_add (h₁ ρ hρ x) (h₂ ρ hρ x))⟩

end Bounds

/-- `‖w‖ ≤ |w₀| + |w₁|` in `ℝ²`. -/
theorem tjVec2_norm_le (w : UnforcedLeray.Cyl.Vec2) : ‖w‖ ≤ |w 0| + |w 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (w 0), abs_nonneg (w 1), sq_abs (w 0), sq_abs (w 1)]

/-- `|w_j| ≤ ‖w‖` in `ℝ²`. -/
theorem tjVec2_abs_le (w : UnforcedLeray.Cyl.Vec2) (j : Fin 2) : |w j| ≤ ‖w‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w j

/-! ## The induction on the number of age letters -/

/-- **`TjAbstractInduction` from the calculus of words.** -/
theorem tjAbstractInduction_of (hP : TjWPerm) (hLb : TjWLeibniz) (hLin : TjWLinear) :
    TjAbstractInduction := by
  intro m ν E V₀ V₁ hE hV₀ hV₁ hvort hspace hkc
  have hE1 : ContDiffOn ℝ ∞ (tjW [1] E) tjU := tjW_contDiffOn hE [1]
  have hE2 : ContDiffOn ℝ ∞ (tjW [2] E) tjU := tjW_contDiffOn hE [2]
  have hE11 : ContDiffOn ℝ ∞ (tjW [1, 1] E) tjU := tjW_contDiffOn hE [1, 1]
  have hE22 : ContDiffOn ℝ ∞ (tjW [2, 2] E) tjU := tjW_contDiffOn hE [2, 2]
  have key : ∀ j : ℕ, ∀ L : List (Fin 3), L.count 0 ≤ j →
      TjWBdd m (tjW L E) ∧ TjUBdd (tjW L V₀) ∧ TjUBdd (tjW L V₁) := by
    intro j
    induction j with
    | zero =>
      intro L hL
      exact hspace L (List.count_eq_zero.1 (Nat.le_zero.1 hL))
    | succ j ih =>
      have hEp : ∀ L : List (Fin 3), L.count 0 ≤ j + 1 → TjWBdd m (tjW L E) := by
        intro L hL
        rcases Nat.lt_or_ge (L.count 0) (j + 1) with hlt | hge
        · exact (ih L (Nat.lt_succ_iff.1 hlt)).1
        · have hcount : L.count 0 = j + 1 := le_antisymm hL hge
          have hmem : (0 : Fin 3) ∈ L := List.count_pos_iff.1 (by omega)
          have hperm : L.Perm (L.erase 0 ++ [0]) :=
            (List.perm_cons_erase hmem).trans (List.perm_append_singleton 0 (L.erase 0)).symm
          have hcL' : (L.erase 0).count 0 = j := by rw [List.count_erase_self]; omega
          set L' := L.erase 0 with hL'def
          have hsplit : ∀ (i : Fin 3), i ≠ 0 → ∀ (V : ℝ × (ℝ × ℝ) → ℝ),
              (∀ L₁ : List (Fin 3), L₁.count 0 ≤ j → TjUBdd (tjW L₁ V)) →
              TjWBdd m (fun p => ((tjSplits L').map
                (fun s => tjW s.1 V p * tjW (s.2 ++ [i]) E p)).sum) := by
            intro i hi V hV
            refine TjWBdd.list_sum _ _ (fun s hs => ?_)
            have hc := tjSplits_count (0 : Fin 3) L' s hs
            have hi0 : ([i] : List (Fin 3)).count 0 = 0 := by simp [hi]
            have hc2 : (s.2 ++ [i]).count 0 ≤ j := by rw [List.count_append]; omega
            exact TjWBdd.mul_left (hV s.1 (by omega)) (ih _ hc2).1
          have h11 : (L' ++ [1, 1]).count 0 ≤ j := by
            have : ([1, 1] : List (Fin 3)).count 0 = 0 := by decide
            rw [List.count_append]; omega
          have h22 : (L' ++ [2, 2]).count 0 ≤ j := by
            have : ([2, 2] : List (Fin 3)).count 0 = 0 := by decide
            rw [List.count_append]; omega
          have hΦ : TjWBdd m (fun p => ν * (tjW (L' ++ [1, 1]) E p + tjW (L' ++ [2, 2]) E p) -
              (((tjSplits L').map (fun s => tjW s.1 V₀ p * tjW (s.2 ++ [1]) E p)).sum +
                ((tjSplits L').map (fun s => tjW s.1 V₁ p * tjW (s.2 ++ [2]) E p)).sum)) :=
            TjWBdd.sub (TjWBdd.const_mul ν ((ih _ h11).1.add (ih _ h22).1))
              ((hsplit 1 (by decide) V₀ (fun L₁ h => (ih L₁ h).2.1)).add
                (hsplit 2 (by decide) V₁ (fun L₁ h => (ih L₁ h).2.2)))
          refine hΦ.congr (fun ρ hρ x => ?_)
          have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ, mem_univ x⟩
          have hA : ContDiffOn ℝ ∞ (fun q => ν * (tjW [1, 1] E q + tjW [2, 2] E q)) tjU :=
            contDiffOn_const.mul (hE11.add hE22)
          have hB : ContDiffOn ℝ ∞ (fun q => V₀ q * tjW [1] E q + V₁ q * tjW [2] E q) tjU :=
            (hV₀.mul hE1).add (hV₁.mul hE2)
          have e1 : tjW L E (ρ, x) = tjW L' (fun q => ν * (tjW [1, 1] E q + tjW [2, 2] E q) -
              (V₀ q * tjW [1] E q + V₁ q * tjW [2] E q)) (ρ, x) := by
            rw [hP E hE L (L' ++ [0]) hperm (ρ, x) hp, tjW_append L' [0] E]
            exact tjW_congr (fun q hq => hvort q hq) L' hp
          rw [e1, hLin.2.1 _ _ hA hB L' (ρ, x) hp, hLin.2.2.1 ν _ (hE11.add hE22) L' (ρ, x) hp,
            hLin.1 _ _ hE11 hE22 L' (ρ, x) hp,
            hLin.1 _ _ (hV₀.mul hE1) (hV₁.mul hE2) L' (ρ, x) hp,
            hLb V₀ (tjW [1] E) hV₀ hE1 L' (ρ, x) hp, hLb V₁ (tjW [2] E) hV₁ hE2 L' (ρ, x) hp]
          simp only [tjW_append]
      refine fun L hL => ⟨hEp L hL, hkc L (fun L₁ hsuf => hEp L₁ ?_)⟩
      exact (hsuf.sublist.count_le 0).trans hL
  intro L
  exact key (L.count 0) L le_rfl

/-! ## The decay of the vorticity -/

/-- **`TjVortDecay m` from its leaves**: at every age `ρ ∈ [0, S]` the slice `E(ρ)` is `C^∞`,
`c`-periodic, has the weighted gradient of `TjLadGrad` (the slice partials are the words `[1]`,
`[2]`, `tjW_one_apply`, `tjW_two_apply`) and bounded strip circulation (`TjCirculationBdd` with
`M = sup |v|`, `IsBUCTrain.sup_bound`); `TjDecayOfGrad` with `β = m + 2`. -/
theorem tjVortDecay_of (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hG : TjLadGrad m)
    (hDG : TjDecayOfGrad) (hCi : TjCirculationBdd) : TjVortDecay m := by
  intro ν hν hν1 tr hbuc hB S hS
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨K, -, hK⟩ := hDG (m + 2) (ν ^ (-2 : ℝ)) (by linarith) hc
  obtain ⟨hEs, -, -⟩ := hV ν (ν ^ (-2 : ℝ)) tr
  obtain ⟨A₁, hA₁⟩ := hG ν (ν ^ (-2 : ℝ)) tr hc hB 1 (by decide) S hS
  obtain ⟨A₂, hA₂⟩ := hG ν (ν ^ (-2 : ℝ)) tr hc hB 2 (by decide) S hS
  obtain ⟨M, hM⟩ := hbuc.sup_bound hS
  refine ⟨K * max A₁ A₂, fun ρ hρ x => ?_⟩
  have hslice : ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr ρ) :=
    hEs.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun y => ⟨mem_Ici.2 hρ.1, mem_univ _⟩)
  have hE1 : ContDiff ℝ 1 (UnforcedLeray.B0238.Ec tr ρ) := hslice.of_le (by exact_mod_cast le_top)
  have hper : ∀ y : ℝ × ℝ, UnforcedLeray.B0238.Ec tr ρ (y.1 + ν ^ (-2 : ℝ), y.2) =
      UnforcedLeray.B0238.Ec tr ρ y := UnforcedLeray.Short.PartI.vjl_curl_periodic tr hρ.1
  have hq : ∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ ((m + 2) / 2) *
      |UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) y| ≤ max A₁ A₂ := by
    intro y
    have hp : ((ρ, y) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.1, mem_univ y⟩
    have e : UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) y =
        tjW [1] (tjE tr) (ρ, y) := (tjW_one_apply hEs hρ.1 y).symm
    rw [e]
    exact (hA₁ ρ hρ y).trans (le_max_left _ _)
  have hη : ∀ y : ℝ × ℝ, (1 + y.2 ^ 2) ^ ((m + 2) / 2) *
      |UnforcedLeray.Cyl.partialEta (UnforcedLeray.B0238.Ec tr ρ) y| ≤ max A₁ A₂ := by
    intro y
    have hp : ((ρ, y) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.1, mem_univ y⟩
    have e : UnforcedLeray.Cyl.partialEta (UnforcedLeray.B0238.Ec tr ρ) y =
        tjW [2] (tjE tr) (ρ, y) := (tjW_two_apply hEs hρ.1 y).symm
    rw [e]
    exact (hA₂ ρ hρ y).trans (le_max_right _ _)
  have hstrip := hCi ν (ν ^ (-2 : ℝ)) tr hc ρ hρ.1 M (fun y => hM ρ hρ y)
  have h := hK (UnforcedLeray.B0238.Ec tr ρ) (max A₁ A₂) _ hE1 hper hq hη hstrip x
  have e2 : (m + 2 - 1) / 2 = (m + 1) / 2 := by ring
  rw [e2] at h
  exact h

/-! ## The words with no age letter -/

/-- **`TjTrainSpace m` from its leaves.** -/
theorem tjTrainSpace_of (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hSl : TjSliceNorm)
    (hI : TjSpatialInterp) (hD : TjVortDecay m) (hG : TjLadGrad m) (hLin : TjWLinear) :
    TjTrainSpace m := by
  intro ν hν hν1 tr hbuc hB
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨hEs, hcurl, -⟩ := hV ν (ν ^ (-2 : ℝ)) tr
  have hVs : ∀ j : Fin 2, ContDiffOn ℝ ∞ (tjV tr j) tjU := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  have hVb : ∀ j : Fin 2, ∀ L : List (Fin 3), 0 ∉ L → TjUBdd (tjW L (tjV tr j)) := by
    intro j L hL S hS
    obtain ⟨M, hM⟩ := hbuc.deriv_bound hS L.length
    refine ⟨M, fun ρ hρ x => ?_⟩
    have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ.1
    have hproj : ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by
        simpa using PiLp.norm_apply_le w j)
    have hn : ((L.length : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have h2 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (f := tr.v ρ) (x := x) (n := L.length) hv.contDiffAt hn
    calc |tjW L (tjV tr j) (ρ, x)|
        ≤ ‖iteratedFDeriv ℝ L.length (fun y => tjV tr j (ρ, y)) x‖ :=
          hSl _ (hVs j) L hL ρ hρ.1 x
      _ = ‖iteratedFDeriv ℝ L.length
            ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ tr.v ρ) x‖ := rfl
      _ ≤ ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ L.length (tr.v ρ) x‖ := h2
      _ ≤ 1 * ‖iteratedFDeriv ℝ L.length (tr.v ρ) x‖ :=
            mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hM ρ hρ x
  have hEu : ∀ L : List (Fin 3), 0 ∉ L → TjUBdd (tjW L (tjE tr)) := by
    intro L hL
    have h1 : (0 : Fin 3) ∉ L ++ [1] := by simp [hL]
    have h2 : (0 : Fin 3) ∉ L ++ [2] := by simp [hL]
    refine ((hVb 1 _ h1).sub (hVb 0 _ h2)).congr (fun ρ hρ x => ?_)
    have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ, mem_univ x⟩
    have e1 : tjW L (tjE tr) (ρ, x) =
        tjW L (fun q => tjW [1] (tjV tr 1) q - tjW [2] (tjV tr 0) q) (ρ, x) :=
      tjW_congr (fun q hq => hcurl q hq) L hp
    rw [e1, hLin.2.1 _ _ (tjW_contDiffOn (hVs 1) [1]) (tjW_contDiffOn (hVs 0) [2]) L (ρ, x) hp,
      tjW_append, tjW_append]
  intro L hL
  refine ⟨?_, hVb 0 L hL, hVb 1 L hL⟩
  rcases L.eq_nil_or_concat' with rfl | ⟨L₀, a, rfl⟩
  · exact hD ν hν hν1 tr hbuc hB
  · have ha : a ≠ 0 := fun h => hL (by simp [h])
    have hL₀ : (0 : Fin 3) ∉ L₀ := fun h => hL (List.mem_append_left _ h)
    intro S hS
    obtain ⟨A, hA⟩ := hG ν (ν ^ (-2 : ℝ)) tr hc hB a ha S hS
    have hM : ∀ L'' : List (Fin 3), 0 ∉ L'' → ∃ M : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
        |tjW L'' (tjW [a] (tjE tr)) (ρ, x)| ≤ M := by
      intro L'' hL''
      have h0 : (0 : Fin 3) ∉ L'' ++ [a] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hL'', fun h => ha h.symm⟩
      obtain ⟨M, hM⟩ := hEu (L'' ++ [a]) h0 S hS
      exact ⟨M, fun ρ hρ x => by rw [← tjW_append]; exact hM ρ hρ x⟩
    obtain ⟨C, hC⟩ := hI (m + 2) (m + 1) (by linarith) (by linarith) (tjW [a] (tjE tr))
      (tjW_contDiffOn hEs [a]) S hS ⟨A, hA⟩ hM L₀ hL₀
    refine ⟨C, fun ρ hρ x => ?_⟩
    rw [tjW_append]
    exact hC ρ hρ x

/-! ## The velocity words from the vorticity words -/

/-- **`TjTrainKc m` from its leaves**: by induction on the word, `tjW L v = K_c(tjW L E)` on `tjU`
(`TjTrainBSRep`, then `TjKcDerivSpace`/`TjKcDerivTime` letter by letter), and `K_c` of a
weighted-bounded field is bounded (`TjKcBound`). -/
theorem tjTrainKc_of (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hR : TjTrainBSRep m)
    (hKb : TjKcBound) (hKs : TjKcDerivSpace) (hKt : TjKcDerivTime) (hW : TjWPeriodic)
    (hLin : TjWLinear) : TjTrainKc m := by
  intro ν hν hν1 tr hbuc hB
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨hEs, -, -⟩ := hV ν (ν ^ (-2 : ℝ)) tr
  have hVv : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) tjU := tr.isTrain.smooth_v
  have hEper : ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ,
      tjE tr (ρ, (x.1 + ν ^ (-2 : ℝ), x.2)) = tjE tr (ρ, x) :=
    fun ρ hρ x => UnforcedLeray.Short.PartI.vjl_curl_periodic tr hρ x
  have hper : ∀ L : List (Fin 3), ∀ ρ : ℝ, 0 ≤ ρ → ∀ x : ℝ × ℝ,
      tjW L (tjE tr) (ρ, (x.1 + ν ^ (-2 : ℝ), x.2)) = tjW L (tjE tr) (ρ, x) :=
    hW _ _ hEs hEper
  have hrep : ∀ L : List (Fin 3), (∀ L' : List (Fin 3), L' <:+ L → TjWBdd m (tjW L' (tjE tr))) →
      EqOn (tjW L (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2))
        (tjKc (ν ^ (-2 : ℝ)) (tjW L (tjE tr))) tjU := by
    intro L
    induction L with
    | nil => intro _ p hp; exact hR ν hν hν1 tr hbuc hB p hp
    | cons a L ih =>
      intro hsuf
      have hL : ∀ L' : List (Fin 3), L' <:+ L → TjWBdd m (tjW L' (tjE tr)) :=
        fun L' h => hsuf L' (h.trans (List.suffix_cons a L))
      have hEq := ih hL
      have hg := tjW_contDiffOn hEs L
      have hh := tjW_contDiffOn hVv L
      have hbg : TjWBdd m (tjW L (tjE tr)) := hL L (List.suffix_refl L)
      have hbag : TjWBdd m (tjW [a] (tjW L (tjE tr))) := hsuf (a :: L) (List.suffix_refl _)
      by_cases ha : a = 0
      · subst ha
        exact hKt _ m hc1 hm0 _ _ hg hh (hper L) hbg hbag hEq
      · exact hKs _ m hc1 hm0 _ _ hg hh (hper L) hbg a ha hbag hEq
  intro L hsuf
  have hEq := hrep L hsuf
  have hcomp : ∀ j : Fin 2, TjUBdd (tjW L (tjV tr j)) := by
    intro j S hS
    obtain ⟨C, hC⟩ := hKb _ m hc1 hm0 _ (tjW_contDiffOn hEs L).continuousOn (hper L)
      (hsuf L (List.suffix_refl L)) S hS
    refine ⟨C, fun ρ hρ x => ?_⟩
    have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.1, mem_univ x⟩
    have e := hLin.2.2.2 _ hVv j L (ρ, x) hp
    calc |tjW L (tjV tr j) (ρ, x)|
        = |tjW L (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (ρ, x) j| := by rw [← e]
      _ = |tjKc (ν ^ (-2 : ℝ)) (tjW L (tjE tr)) (ρ, x) j| := by rw [hEq hp]
      _ ≤ ‖tjKc (ν ^ (-2 : ℝ)) (tjW L (tjE tr)) (ρ, x)‖ := tjVec2_abs_le _ j
      _ ≤ C := hC ρ hρ x
  exact ⟨hcomp 0, hcomp 1⟩

/-! ## The assembly -/

/-- **`TrainSTJetsOfBUC m` from its leaves**: the abstract induction bounds every word of `E`
(weighted) and of `v` on every `[0, S] × ℝ²`; `TjJetNorm` turns the words into the joint jets of
`TrainSTJets`. -/
theorem trainSTJetsOfBUC_of (m : ℝ) (hm : 8 < m) (hJ : TjJetNorm) (hP : TjWPerm)
    (hLb : TjWLeibniz) (hLin : TjWLinear) (hV : TjTrainVort) (hSl : TjSliceNorm)
    (hI : TjSpatialInterp) (hDG : TjDecayOfGrad) (hCi : TjCirculationBdd) (hG : TjLadGrad m)
    (hR : TjTrainBSRep m) (hKb : TjKcBound) (hKs : TjKcDerivSpace) (hKt : TjKcDerivTime)
    (hW : TjWPeriodic) : TrainSTJetsOfBUC m := by
  have hInd := tjAbstractInduction_of hP hLb hLin
  have hD := tjVortDecay_of m hm hV hG hDG hCi
  have hSp := tjTrainSpace_of m hm hV hSl hI hD hG hLin
  have hKc := tjTrainKc_of m hm hV hR hKb hKs hKt hW hLin
  intro ν hν hν1 tr hbuc hB S hS n
  obtain ⟨hEs, -, hvort⟩ := hV ν (ν ^ (-2 : ℝ)) tr
  have hVv : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) tjU := tr.isTrain.smooth_v
  have hVs : ∀ j : Fin 2, ContDiffOn ℝ ∞ (tjV tr j) tjU := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn hVv
  have hall := hInd m ν (tjE tr) (tjV tr 0) (tjV tr 1) hEs (hVs 0) (hVs 1) hvort
    (hSp ν hν hν1 tr hbuc hB) (hKc ν hν hν1 tr hbuc hB)
  have hCV : ∀ L : Fin n → Fin 3, ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ‖tjW (List.ofFn L) (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (ρ, x)‖ ≤ C := by
    intro L
    obtain ⟨C₀, h₀⟩ := (hall (List.ofFn L)).2.1 S hS
    obtain ⟨C₁, h₁⟩ := (hall (List.ofFn L)).2.2 S hS
    refine ⟨C₀ + C₁, fun ρ hρ x => ?_⟩
    have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.1, mem_univ x⟩
    have e0 := hLin.2.2.2 _ hVv 0 (List.ofFn L) (ρ, x) hp
    have e1 := hLin.2.2.2 _ hVv 1 (List.ofFn L) (ρ, x) hp
    have hn := tjVec2_norm_le (tjW (List.ofFn L) (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (ρ, x))
    rw [← e0, ← e1] at hn
    exact hn.trans (add_le_add (h₀ ρ hρ x) (h₁ ρ hρ x))
  choose CV hCV using hCV
  have hCE : ∀ L : Fin (n + 1) → Fin 3, ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      tjWt m x * |tjW (List.ofFn L) (tjE tr) (ρ, x)| ≤ C := fun L => (hall (List.ofFn L)).1 S hS
  choose CE hCE using hCE
  obtain ⟨K₁, hK₁, hJ₁⟩ := hJ n
  obtain ⟨K₂, hK₂, hJ₂⟩ := hJ (n + 1)
  refine ⟨max (K₁ * ∑ L, CV L) (K₂ * ∑ L, CE L), fun ρ hρ x => ⟨?_, ?_⟩⟩
  · have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.1, mem_univ x⟩
    have h1 := hJ₁ UnforcedLeray.Cyl.Vec2 (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) hVv (ρ, x) hp
    refine le_trans h1 (le_trans ?_ (le_max_left _ _))
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun L _ => hCV L ρ hρ x) hK₁
  · have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.1, mem_univ x⟩
    have h1 := hJ₂ ℝ (tjE tr) hEs (ρ, x) hp
    have hw := (tjWt_pos m x).le
    refine le_trans ?_ (le_max_right _ _)
    calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) *
          ‖iteratedFDerivWithin ℝ (n + 1) (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
            (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖
        ≤ tjWt m x * (K₂ * ∑ L : Fin (n + 1) → Fin 3, ‖tjW (List.ofFn L) (tjE tr) (ρ, x)‖) :=
          mul_le_mul_of_nonneg_left h1 hw
      _ = K₂ * ∑ L : Fin (n + 1) → Fin 3, tjWt m x * |tjW (List.ofFn L) (tjE tr) (ρ, x)| := by
          rw [mul_left_comm, Finset.mul_sum]
          simp only [Real.norm_eq_abs]
      _ ≤ K₂ * ∑ L, CE L :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun L _ => hCE L ρ hρ x) hK₂

end UnforcedLeray.Short.IIIa
