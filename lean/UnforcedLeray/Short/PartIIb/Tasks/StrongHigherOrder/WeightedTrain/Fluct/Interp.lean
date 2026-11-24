import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct.Calc
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanStress.FluctVelSliceBound.Calc

/-!
# Step (c): from the Gaussian tail of `ω` to the tails of all its jets (unit-patch interpolation)

Helper of `Tail.lean`.  Source
`the November 2 reference manuscript` 487-494:
"`|ω| ≤ C exp[-b(|η|-C/ν)₊²/(C₀+νs)]`. ... Unit-patch interpolation with the fixed higher smooth
bounds from Lemma `sct:train` gives the same tail, with reduced exponent, for every required spatial
derivative of `ω`."  At fixed parameters (427-435) the higher bounds are `PartI.TrainJetsBoundedFixed`.

The interpolation is done one direction at a time along words of directions (`AgeDeriv.dW`), with
the one-sided Landau inequality `|g'(0)| ≤ 2T/h + M h` on `[0, h]` (`landau`), `h = min(1, √T)`:
each derivative halves the exponent `b`, shifts the threshold by `1` and the age by `≤ 1`
(`interp_tail`).  Age derivatives are words containing the age direction `(1, 0, 0)` (forward
segments, so `s > 0` is kept).

* `VortGaussTailFixed` (leaf (a), source line 489): the Gaussian tail of `ω` itself.
* `vortJetTailFixed_of`: `VortGaussTailFixed` and `PartI.TrainJetsBoundedFixed` give
  `VortJetTailFixed`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIb.WeightedTrainFluctAux

open UnforcedLeray
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartI.AgeDeriv
open UnforcedLeray.Cyl (Plane)

/-- **Leaf (a): the Gaussian transverse tail of the vorticity at fixed parameters** (SP 482-490:
`∫₀^∞ ‖v₂‖_∞ ≤ C/ν` from `sct:train`; the vorticity drift-diffusion equation, the Gaussian datum
and the supersolutions `C exp{-λ(η - A(s)) + (C₀+νs)λ²}`, `A(s) = ∫₀ˢ ‖v₂‖_∞`, with both transverse
signs, give `|ω| ≤ C exp[-b(|η| - C/ν)₊²/(C₀+νs)]`; fixed parameters 427-435).  For `ρ > 1/2` one
`ν₀`; for every BUC train with `ν ≤ ν₀` there are constants (depending on the train) with
`|ω(s, z)| ≤ C exp[-b (|η| - C'/ν)₊² / (C₀ + ν s)]` for all `s > 0`. -/
def VortGaussTailFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
      ∃ b C₀ C' C : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧
        ∀ s : ℝ, 0 < s → ∀ z : Plane,
          |Cyl.curl (tr.v s) z| ≤
            C * Real.exp (-(b * (max (|z.2| - C' / ν) 0) ^ 2 / (C₀ + ν * s)))

namespace FluctTail

/-- **One-sided Landau inequality** on `[0, h]`. -/
theorem landau {g g' g'' : ℝ → ℝ} {h T M : ℝ} (hh : 0 < h)
    (hg : ∀ t ∈ Icc 0 h, HasDerivAt g (g' t) t) (hg' : ∀ t ∈ Icc 0 h, HasDerivAt g' (g'' t) t)
    (hT : ∀ t ∈ Icc 0 h, |g t| ≤ T) (hM : ∀ t ∈ Icc 0 h, |g'' t| ≤ M) :
    |g' 0| ≤ 2 * T / h + M * h := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hh.le⟩)
  have h1 : ∀ t ∈ Icc (0 : ℝ) h, ‖g' t - g' 0‖ ≤ M * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht => (hg' t ht).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hM t (Ico_subset_Icc_self ht))
  have hφ : ∀ t ∈ Icc (0 : ℝ) h,
      HasDerivWithinAt (fun t => g t - t * g' 0) (g' t - g' 0) (Icc 0 h) t := by
    intro t ht
    have h2 := (hg t ht).sub ((hasDerivAt_id t).mul_const (g' 0))
    exact (h2.congr_deriv (by simp)).hasDerivWithinAt
  have h2 : ∀ t ∈ Icc (0 : ℝ) h,
      ‖(g t - t * g' 0) - (g 0 - 0 * g' 0)‖ ≤ (M * h) * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hφ (fun t ht => by
      have := h1 t (Ico_subset_Icc_self ht)
      have hth : t ≤ h := ht.2.le
      calc ‖g' t - g' 0‖ ≤ M * (t - 0) := this
        _ ≤ M * h := by nlinarith [ht.1])
  have hh' := h2 h ⟨hh.le, le_rfl⟩
  rw [Real.norm_eq_abs] at hh'
  have hgh := hT h ⟨hh.le, le_rfl⟩
  have hg0 := hT 0 ⟨le_rfl, hh.le⟩
  have key : h * |g' 0| ≤ 2 * T + M * h * h := by
    have e : h * g' 0 = (g h - g 0) - ((g h - h * g' 0) - (g 0 - 0 * g' 0)) := by ring
    have : |h * g' 0| ≤ |g h| + |g 0| + M * h * (h - 0) := by
      rw [e]
      calc |(g h - g 0) - ((g h - h * g' 0) - (g 0 - 0 * g' 0))|
          ≤ |g h - g 0| + |(g h - h * g' 0) - (g 0 - 0 * g' 0)| := abs_sub _ _
        _ ≤ (|g h| + |g 0|) + M * h * (h - 0) := add_le_add (abs_sub _ _) hh'
    rw [abs_mul, abs_of_pos hh] at this
    linarith
  rw [div_add' _ _ _ hh.ne', le_div_iff₀ hh]
  nlinarith

/-- **One Landau step along a word.** -/
theorem word_step {Ω : ℝ × Plane → ℝ} (hΩ : ContDiffOn ℝ ∞ Ω UU) (w : List (ℝ × Plane))
    (v : ℝ × Plane) (hv : 0 ≤ v.1) {x : ℝ × Plane} (hx : x ∈ UU) {h T M : ℝ} (hh : 0 < h)
    (hT : ∀ t ∈ Icc 0 h, |dW w Ω (x + t • v)| ≤ T)
    (hM : ∀ t ∈ Icc 0 h, |dW (v :: v :: w) Ω (x + t • v)| ≤ M) :
    |dW (v :: w) Ω x| ≤ 2 * T / h + M * h := by
  have hmem : ∀ t : ℝ, 0 ≤ t → x + t • v ∈ UU := by
    intro t ht
    refine ⟨?_, mem_univ _⟩
    show 0 < (x + t • v).1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    have := hx.1
    simp only [Set.mem_Ioi] at this
    nlinarith
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    have := ((hasDerivAt_id t).smul_const v).const_add x
    simpa using this
  have hd : ∀ (L : List (ℝ × Plane)) (t : ℝ), 0 ≤ t →
      HasDerivAt (fun t => dW L Ω (x + t • v)) (dW (v :: L) Ω (x + t • v)) t := by
    intro L t ht
    have h1 := (dW_diffAt hΩ L (hmem t ht)).hasFDerivAt.comp_hasDerivAt t (hline t)
    exact h1
  have hl := landau (g := fun t => dW w Ω (x + t • v)) (g' := fun t => dW (v :: w) Ω (x + t • v))
    (g'' := fun t => dW (v :: v :: w) Ω (x + t • v)) hh
    (fun t ht => hd w t ht.1) (fun t ht => hd (v :: w) t ht.1) hT hM
  simpa using hl

/-- The coordinate vectors of the plane. -/
def E2 : Fin 2 → Plane := ![((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))]

/-- The coordinates of a point of the plane. -/
def cd2 : Fin 2 → Plane → ℝ := fun c x => ![x.1, x.2] c

theorem cd2_abs_le (c : Fin 2) (x : Plane) : |cd2 c x| ≤ ‖x‖ := by
  fin_cases c
  · simp only [cd2]
    rw [← Real.norm_eq_abs]
    exact norm_fst_le x
  · simp only [cd2]
    rw [← Real.norm_eq_abs]
    exact norm_snd_le x

theorem E2_decomp (x : Plane) : x = ∑ c : Fin 2, cd2 c x • E2 c := by
  rcases x with ⟨a, b⟩
  simp [Fin.sum_univ_two, cd2, E2]

theorem norm_E2 (c : Fin 2) : ‖E2 c‖ = 1 := by
  fin_cases c <;> simp [E2]

/-- The norm of a multilinear form on the plane is at most the sum of its values on coordinate
tuples. -/
theorem norm_le_sum2 {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Plane) ℝ) :
    ‖A‖ ≤ ∑ r : Fin j → Fin 2, |A (fun i => E2 (r i))| := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun r _ => abs_nonneg _)) ?_
  intro m
  have hexp : A m = ∑ r : Fin j → Fin 2, (∏ i, cd2 (r i) (m i)) * A (fun i => E2 (r i)) := by
    have h1 : A m = A (fun i => ∑ c : Fin 2, cd2 c (m i) • E2 c) := by
      congr 1
      funext i
      exact E2_decomp (m i)
    rw [h1, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    show A (fun i => cd2 (r i) (m i) • E2 (r i)) = _
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hbound : ∀ r : Fin j → Fin 2, |∏ i, cd2 (r i) (m i)| ≤ ∏ i, ‖m i‖ := by
    intro r
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => cd2_abs_le _ _)
  rw [hexp, Real.norm_eq_abs]
  calc |∑ r : Fin j → Fin 2, (∏ i, cd2 (r i) (m i)) * A (fun i => E2 (r i))|
      ≤ ∑ r : Fin j → Fin 2, |(∏ i, cd2 (r i) (m i)) * A (fun i => E2 (r i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin j → Fin 2, (∏ i, ‖m i‖) * |A (fun i => E2 (r i))| := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound r) (abs_nonneg _)
    _ = (∑ r : Fin j → Fin 2, |A (fun i => E2 (r i))|) * ∏ i, ‖m i‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        ring

/-- `√` of the tail form: `T ≤ Y²` for the halved exponent. -/
theorem tail_sq_le {K b C₀ ν S l : ℝ} {N : ℕ} (hK : 0 < K) (hS : 0 ≤ S) (hν : 0 < ν)
    (hC₀ : 0 < C₀) :
    K * (1 + (S + 1)) ^ N *
        (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * (S + 1))))) ≤
      (Real.sqrt K * 2 ^ N * (1 + S) ^ N *
        (Real.exp (-(b / 2 * l)) + Real.exp (-(b / 2 * l ^ 2 / ((C₀ + ν) + ν * S))))) ^ 2 := by
  set e1 := Real.exp (-(b / 2 * l)) with he1
  set e2 := Real.exp (-(b / 2 * l ^ 2 / ((C₀ + ν) + ν * S))) with he2
  have hE1 : Real.exp (-(b * l)) = e1 ^ 2 := by
    rw [he1, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hD : C₀ + ν * (S + 1) = (C₀ + ν) + ν * S := by ring
  have hE2 : Real.exp (-(b * l ^ 2 / (C₀ + ν * (S + 1)))) = e2 ^ 2 := by
    rw [he2, ← Real.exp_nat_mul, hD]; congr 1; push_cast; ring
  rw [hE1, hE2]
  have he1p : 0 ≤ e1 := (Real.exp_pos _).le
  have he2p : 0 ≤ e2 := (Real.exp_pos _).le
  have hS1 : (1 : ℝ) ≤ (1 + S) ^ N := one_le_pow₀ (by linarith)
  have hpow : (1 + (S + 1)) ^ N ≤ 2 ^ N * (1 + S) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) N
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have hpow2 : 2 ^ N * (1 + S) ^ N ≤ (2 ^ N * (1 + S) ^ N) ^ 2 := by
    have h1 : (1 : ℝ) ≤ 2 ^ N * (1 + S) ^ N := by nlinarith
    nlinarith
  have hsum : e1 ^ 2 + e2 ^ 2 ≤ (e1 + e2) ^ 2 := by nlinarith
  have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  calc K * (1 + (S + 1)) ^ N * (e1 ^ 2 + e2 ^ 2)
      ≤ K * (2 ^ N * (1 + S) ^ N) ^ 2 * (e1 + e2) ^ 2 := by
        apply mul_le_mul _ hsum (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (hpow.trans hpow2) hK.le
    _ = (Real.sqrt K * 2 ^ N * (1 + S) ^ N * (e1 + e2)) ^ 2 := by
        rw [show (Real.sqrt K * 2 ^ N * (1 + S) ^ N * (e1 + e2)) ^ 2 =
          Real.sqrt K ^ 2 * ((2 ^ N * (1 + S) ^ N) ^ 2 * (e1 + e2) ^ 2) by ring, hsq]
        ring

/-- **Interpolation along words.**  If `Ω` is smooth on `U`, all its word derivatives (directions of
norm `≤ 1`) are bounded on `U`, and `Ω` has the tail form beyond `R`, then every word derivative
of length `n` along directions `v` with `v.1 ≥ 0`, `‖v‖ ≤ 1` has the tail form (with smaller
`b`, larger `C₀, K`) beyond `R + n`. -/
theorem interp_tail {Ω : ℝ × Plane → ℝ} (hΩ : ContDiffOn ℝ ∞ Ω UU) {ν R : ℝ} (hν : 0 < ν)
    (hunif : ∀ m : ℕ, ∃ B : ℝ, ∀ w : List (ℝ × Plane), w.length = m → (∀ v ∈ w, ‖v‖ ≤ 1) →
      ∀ y ∈ UU, |dW w Ω y| ≤ B)
    (hbase : ∃ K b C₀ : ℝ, ∃ N : ℕ, 0 < K ∧ 0 < b ∧ 0 < C₀ ∧
      ∀ S l s : ℝ, ∀ z : Plane, 0 ≤ S → 0 ≤ l → 0 < s → s ≤ S → R + l ≤ |z.2| →
        |Ω (s, z)| ≤ K * (1 + S) ^ N *
          (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S))))) :
    ∀ n : ℕ, ∃ K b C₀ : ℝ, ∃ N : ℕ, 0 < K ∧ 0 < b ∧ 0 < C₀ ∧
      ∀ w : List (ℝ × Plane), w.length = n → (∀ v ∈ w, 0 ≤ v.1 ∧ ‖v‖ ≤ 1) →
        ∀ S l s : ℝ, ∀ z : Plane, 0 ≤ S → 0 ≤ l → 0 < s → s ≤ S → R + n + l ≤ |z.2| →
          |dW w Ω (s, z)| ≤ K * (1 + S) ^ N *
            (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S)))) := by
  intro n
  induction n with
  | zero =>
    obtain ⟨K, b, C₀, N, hK, hb, hC₀, hB⟩ := hbase
    refine ⟨K, b, C₀, N, hK, hb, hC₀, fun w hw _ S l s z hS hl hs hsS hz => ?_⟩
    rw [List.length_eq_zero_iff] at hw
    subst hw
    exact hB S l s z hS hl hs hsS (by simpa using hz)
  | succ n ih =>
    obtain ⟨K, b, C₀, N, hK, hb, hC₀, hB⟩ := ih
    obtain ⟨B₀, hB₀⟩ := hunif n
    obtain ⟨B₂, hB₂⟩ := hunif (n + 2)
    set B₀' := max B₀ 0 with hB₀'
    set B₂' := max B₂ 0 with hB₂'
    have hB₀'0 : 0 ≤ B₀' := le_max_right _ _
    have hB₂'0 : 0 ≤ B₂' := le_max_right _ _
    set A : ℝ := 2 + 2 * B₀' + B₂' with hA
    have hA0 : 0 < A := by positivity
    refine ⟨A * (Real.sqrt K * 2 ^ N), b / 2, C₀ + ν, N, by positivity, by positivity,
      by positivity, fun w hw hadm S l s z hS hl hs hsS hz => ?_⟩
    obtain ⟨v, w', rfl⟩ : ∃ v w', w = v :: w' := by
      cases w with
      | nil => simp at hw
      | cons v w' => exact ⟨v, w', rfl⟩
    have hw' : w'.length = n := by simpa using hw
    have hv := hadm v List.mem_cons_self
    have hadm' : ∀ u ∈ w', 0 ≤ u.1 ∧ ‖u‖ ≤ 1 := fun u hu => hadm u (List.mem_cons_of_mem v hu)
    have hx : ((s, z) : ℝ × Plane) ∈ UU := mem_UU hs z
    -- the segment stays in the region
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ((s, z) + t • v) ∈ UU ∧ 0 < ((s, z) + t • v).1 ∧
        ((s, z) + t • v).1 ≤ S + 1 ∧ R + n + l ≤ |((s, z) + t • v).2.2| := by
      intro t ht
      have hv1 : v.1 ≤ 1 := (le_abs_self _).trans ((norm_fst_le v).trans hv.2)
      have hv22 : |v.2.2| ≤ 1 := by
        rw [← Real.norm_eq_abs]
        exact (norm_snd_le v.2).trans ((norm_snd_le v).trans hv.2)
      have h1 : 0 < s + t * v.1 := by nlinarith [ht.1, hv.1]
      have h2 : s + t * v.1 ≤ S + 1 := by nlinarith [ht.1, ht.2]
      have h3 : |t * v.2.2| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg ht.1]
        nlinarith [ht.2, abs_nonneg v.2.2]
      have h4 : |z.2| - 1 ≤ |z.2 + t * v.2.2| := by
        have := abs_add_le (z.2 + t * v.2.2) (-(t * v.2.2))
        rw [add_neg_cancel_right, abs_neg] at this
        linarith
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      refine ⟨⟨h1, mem_univ _⟩, h1, h2, ?_⟩
      push_cast at hz
      linarith
    -- the tail at the shifted age
    set T : ℝ := K * (1 + (S + 1)) ^ N *
      (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * (S + 1))))) with hT
    have hTpos : 0 < T := by positivity
    have hgT : ∀ t ∈ Icc (0 : ℝ) 1, |dW w' Ω ((s, z) + t • v)| ≤ T := by
      intro t ht
      obtain ⟨_, hp1, hp2, hp3⟩ := hseg t ht
      have := hB w' hw' hadm' (S + 1) l (((s, z) + t • v).1) (((s, z) + t • v).2) (by linarith) hl
        hp1 hp2 hp3
      exact this
    have hgB : ∀ t ∈ Icc (0 : ℝ) 1, |dW w' Ω ((s, z) + t • v)| ≤ B₀' := by
      intro t ht
      exact (hB₀ w' hw' (fun u hu => (hadm' u hu).2) _ (hseg t ht).1).trans (le_max_left _ _)
    have hg2 : ∀ t ∈ Icc (0 : ℝ) 1, |dW (v :: v :: w') Ω ((s, z) + t • v)| ≤ B₂' := by
      intro t ht
      refine (hB₂ (v :: v :: w') (by simp [hw']) (fun u hu => ?_) _ (hseg t ht).1).trans
        (le_max_left _ _)
      rcases List.mem_cons.1 hu with h | h
      · rw [h]; exact hv.2
      rcases List.mem_cons.1 h with h | h
      · rw [h]; exact hv.2
      · exact (hadm' u h).2
    set X : ℝ := Real.sqrt T with hX
    have hXpos : 0 < X := Real.sqrt_pos.2 hTpos
    have hXsq : X ^ 2 = T := Real.sq_sqrt hTpos.le
    -- the Landau step
    have hstep : |dW (v :: w') Ω (s, z)| ≤ A * X := by
      rcases le_or_gt X 1 with hX1 | hX1
      · have h := word_step hΩ w' v hv.1 hx hXpos
          (fun t ht => hgT t ⟨ht.1, ht.2.trans hX1⟩) (fun t ht => hg2 t ⟨ht.1, ht.2.trans hX1⟩)
        have e : 2 * T / X = 2 * X := by
          rw [← hXsq]; field_simp
        rw [e] at h
        calc |dW (v :: w') Ω (s, z)| ≤ 2 * X + B₂' * X := h
          _ ≤ A * X := by rw [hA]; nlinarith
      · have h := word_step hΩ w' v hv.1 hx one_pos hgB hg2
        calc |dW (v :: w') Ω (s, z)| ≤ 2 * B₀' / 1 + B₂' * 1 := h
          _ ≤ (2 * B₀' + B₂') * X := by
              rw [div_one, mul_one]; nlinarith
          _ ≤ A * X := by rw [hA]; nlinarith
    -- `X` is at most the halved tail
    have hXle : X ≤ Real.sqrt K * 2 ^ N * (1 + S) ^ N *
        (Real.exp (-(b / 2 * l)) + Real.exp (-(b / 2 * l ^ 2 / ((C₀ + ν) + ν * S)))) := by
      rw [hX, Real.sqrt_le_left (by positivity)]
      exact tail_sq_le hK hS hν hC₀
    calc |dW (v :: w') Ω (s, z)| ≤ A * X := hstep
      _ ≤ A * (Real.sqrt K * 2 ^ N * (1 + S) ^ N *
          (Real.exp (-(b / 2 * l)) + Real.exp (-(b / 2 * l ^ 2 / ((C₀ + ν) + ν * S))))) :=
          mul_le_mul_of_nonneg_left hXle hA0.le
      _ = A * (Real.sqrt K * 2 ^ N) * (1 + S) ^ N *
          (Real.exp (-(b / 2 * l)) + Real.exp (-(b / 2 * l ^ 2 / ((C₀ + ν) + ν * S)))) := by ring


/-! ### The train: velocity components, the uniform word bounds, the Gaussian base -/

/-- The velocity components are smooth on `U`. -/
theorem vel_comp_smooth {ν c : ℝ} (tr : B0140.TrainSol ν c) (k : Fin 2) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) UU := by
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) UU :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)
  exact (contDiffOn_piLp 2).1 hsm k

/-- `ω = ∂_q v₂ - ∂_η v₁` as word derivatives. -/
theorem curl_eq_dW_vel {ν c : ℝ} (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 < r) (z : Plane) :
    Cyl.curl (tr.v r) z = dW [eQ] (fun x : ℝ × Plane => tr.v x.1 x.2 1) (r, z) -
      dW [eH] (fun x : ℝ × Plane => tr.v x.1 x.2 0) (r, z) := by
  have hq := partialQ_dW (vel_comp_smooth tr 1) [] hr
  have hη := partialEta_dW (vel_comp_smooth tr 0) [] hr
  have e1 : (fun w : Plane => tr.v r w 1) =
      fun w => dW [] (fun x : ℝ × Plane => tr.v x.1 x.2 1) (r, w) := rfl
  have e0 : (fun w : Plane => tr.v r w 0) =
      fun w => dW [] (fun x : ℝ × Plane => tr.v x.1 x.2 0) (r, w) := rfl
  unfold Cyl.curl
  rw [e1, e0, hq, hη]

/-- The vorticity is smooth on `U`. -/
theorem vort_smooth {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) UU := by
  have h : ContDiffOn ℝ ∞ (fun x : ℝ × Plane =>
      dW [eQ] (fun x : ℝ × Plane => tr.v x.1 x.2 1) x -
        dW [eH] (fun x : ℝ × Plane => tr.v x.1 x.2 0) x) UU :=
    (dW_contDiffOn isOpen_UU (vel_comp_smooth tr 1) _).sub
      (dW_contDiffOn isOpen_UU (vel_comp_smooth tr 0) _)
  exact h.congr (fun x hx => curl_eq_dW_vel tr hx.1 x.2)

/-- Uniform bounds of the word derivatives of the velocity components, from the bounded age jets
(`PartI.TrainJetsBoundedFixed` at the train) through `PartI.jointFromAgeJets`. -/
theorem vel_word_bound {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hA1 : ∀ ℓ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane, ‖ageJet ℓ j tr.v s z‖ ≤ M)
    (m : ℕ) :
    ∃ B : ℝ, ∀ k : Fin 2, ∀ w : List (ℝ × Plane), w.length = m → (∀ v ∈ w, ‖v‖ ≤ 1) →
      ∀ y ∈ UU, |dW w (fun x : ℝ × Plane => tr.v x.1 x.2 k) y| ≤ B := by
  choose M hM using hA1
  obtain ⟨K, hK0, hK⟩ := jointFromAgeJets m
  refine ⟨K * ∑ ℓ ∈ Finset.range (m + 1), |M ℓ (m - ℓ)|, fun k w hw hwn y hy => ?_⟩
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)
  have hJ := hK (fun r z => tr.v r z k) ((contDiffOn_piLp 2).1 hsm k) y hy.1
  have hage : ∀ ℓ ∈ Finset.range (m + 1),
      ‖ageJet ℓ (m - ℓ) (fun r z => tr.v r z k) y.1 y.2‖ ≤ |M ℓ (m - ℓ)| := by
    intro ℓ _
    exact (UnforcedLeray.Short.PartIIa.fvs_ageJet_proj_le hsm k (fun r z => tr.v r z k)
      (fun _ _ _ => rfl) (m - ℓ) ℓ hy.1 y.2).trans ((hM ℓ (m - ℓ) y.1 hy.1 y.2).trans
        (le_abs_self _))
  have hJ' : ‖iteratedFDeriv ℝ m (fun x : ℝ × Plane => tr.v x.1 x.2 k) y‖ ≤
      K * ∑ ℓ ∈ Finset.range (m + 1), |M ℓ (m - ℓ)| :=
    hJ.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hage) hK0)
  subst hw
  have h1 := dW_ofFn_eq isOpen_UU (vel_comp_smooth tr k) w.length w.get y hy
  rw [List.ofFn_get] at h1
  rw [h1]
  have h2 := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ w.length (fun x : ℝ × Plane => tr.v x.1 x.2 k) y) w.get
  have h3 : ∏ i, ‖w.get i‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hwn _ (List.get_mem w i))
  rw [← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ w.length (fun x : ℝ × Plane => tr.v x.1 x.2 k) y w.get‖
      ≤ ‖iteratedFDeriv ℝ w.length (fun x : ℝ × Plane => tr.v x.1 x.2 k) y‖ *
          ∏ i, ‖w.get i‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ w.length (fun x : ℝ × Plane => tr.v x.1 x.2 k) y‖ * 1 :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hJ'

theorem norm_eQ : ‖eQ‖ = 1 := by simp [eQ]

theorem norm_eH : ‖eH‖ = 1 := by simp [eH]

/-- Uniform bounds of the word derivatives of the vorticity. -/
theorem vort_word_bound {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hA1 : ∀ ℓ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane, ‖ageJet ℓ j tr.v s z‖ ≤ M)
    (m : ℕ) :
    ∃ B : ℝ, ∀ w : List (ℝ × Plane), w.length = m → (∀ v ∈ w, ‖v‖ ≤ 1) →
      ∀ y ∈ UU, |dW w (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) y| ≤ B := by
  obtain ⟨B, hB⟩ := vel_word_bound tr hA1 (m + 1)
  refine ⟨2 * B, fun w hw hwn y hy => ?_⟩
  rw [dW_congr (g := fun x => dW [eQ] (fun x : ℝ × Plane => tr.v x.1 x.2 1) x -
      dW [eH] (fun x : ℝ × Plane => tr.v x.1 x.2 0) x)
    (fun x hx => curl_eq_dW_vel tr hx.1 x.2) w y hy]
  rw [dW_sub (dW_contDiffOn isOpen_UU (vel_comp_smooth tr 1) _)
    (dW_contDiffOn isOpen_UU (vel_comp_smooth tr 0) _) w y hy]
  rw [← dW_append, ← dW_append]
  have hn : ∀ e : ℝ × Plane, ‖e‖ = 1 → ∀ v ∈ w ++ [e], ‖v‖ ≤ 1 := by
    intro e he v hv
    rcases List.mem_append.1 hv with h | h
    · exact hwn v h
    · rw [List.mem_singleton.1 h, he]
  have b1 := hB 1 (w ++ [eQ]) (by simp [hw]) (hn eQ norm_eQ) y hy
  have b0 := hB 0 (w ++ [eH]) (by simp [hw]) (hn eH norm_eH) y hy
  calc |dW (w ++ [eQ]) (fun x : ℝ × Plane => tr.v x.1 x.2 1) y -
        dW (w ++ [eH]) (fun x : ℝ × Plane => tr.v x.1 x.2 0) y|
      ≤ |dW (w ++ [eQ]) (fun x : ℝ × Plane => tr.v x.1 x.2 1) y| +
        |dW (w ++ [eH]) (fun x : ℝ × Plane => tr.v x.1 x.2 0) y| := abs_sub _ _
    _ ≤ 2 * B := by linarith

end FluctTail

/-- **Step (c) at a fixed train**: a tail of `ω` itself beyond `C'/ν + 2` (in the tail form)
and the bounded age jets of `v` give the tails of all jets of `ω`. -/
theorem FluctTail.vortJet_of_base {ν c : ℝ} (hν : 0 < ν) (tr : B0140.TrainSol ν c)
    (hA : ∀ ℓ j : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane, ‖ageJet ℓ j tr.v s z‖ ≤ M)
    {C' : ℝ} (hC' : 0 < C')
    (hbase : ∃ K b C₀ : ℝ, ∃ N : ℕ, 0 < K ∧ 0 < b ∧ 0 < C₀ ∧
      ∀ S l s : ℝ, ∀ z : Plane, 0 ≤ S → 0 ≤ l → 0 < s → s ≤ S → C' / ν + 2 + l ≤ |z.2| →
        |(fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) (s, z)| ≤ K * (1 + S) ^ N *
          (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S)))))
    (ℓ j : ℕ) :
    ∃ b C₀ C' C : ℝ, ∃ N : ℕ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧
      ∀ S_ : ℝ, 0 ≤ S_ → ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane,
        C' / ν + 2 + l ≤ |z.2| →
          ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
            C * (1 + S_) ^ N *
              (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))) := by
  have hΩ := FluctTail.vort_smooth tr
  have hunif := FluctTail.vort_word_bound tr hA
  obtain ⟨K, b', C₀', N, hK, hb', hC₀', hT⟩ := FluctTail.interp_tail hΩ hν hunif hbase (j + ℓ)
  refine ⟨b', C₀', C' + ν * ((j : ℝ) + ℓ), 2 ^ j * K, N, hb', hC₀', by positivity,
    by positivity, fun S hS l hl s hs hsS z hz => ?_⟩
  refine (FluctTail.norm_le_sum2 _).trans ?_
  have hthr : C' / ν + 2 + ((j + ℓ : ℕ) : ℝ) + l ≤ |z.2| := by
    have e : (C' + ν * ((j : ℝ) + ℓ)) / ν = C' / ν + ((j : ℝ) + ℓ) := by
      field_simp
    rw [e] at hz
    push_cast
    linarith
  have hterm : ∀ r : Fin j → Fin 2,
      |ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z (fun i => FluctTail.E2 (r i))| ≤
        K * (1 + S) ^ N * (Real.exp (-(b' * l)) + Real.exp (-(b' * l ^ 2 / (C₀' + ν * S)))) := by
    intro r
    rw [FluctTail.ageJet_eq_dW (F := fun r w => Cyl.curl (tr.v r) w) hΩ ℓ j hs z]
    refine hT _ (by simp) ?_ S l s z hS hl hs hsS hthr
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      refine ⟨le_rfl, ?_⟩
      simp [FluctTail.norm_E2]
    · rw [List.eq_of_mem_replicate h]
      refine ⟨by simp [LL], ?_⟩
      simp [LL]
  calc ∑ r : Fin j → Fin 2,
        |ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z (fun i => FluctTail.E2 (r i))|
      ≤ ∑ _r : Fin j → Fin 2, K * (1 + S) ^ N *
          (Real.exp (-(b' * l)) + Real.exp (-(b' * l ^ 2 / (C₀' + ν * S)))) :=
        Finset.sum_le_sum (fun r _ => hterm r)
    _ = 2 ^ j * K * (1 + S) ^ N *
          (Real.exp (-(b' * l)) + Real.exp (-(b' * l ^ 2 / (C₀' + ν * S)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring


/-- **Step (c): `VortJetTailFixed` from the Gaussian tail of `ω`** and the bounded age jets of
`v` (`PartI.TrainJetsBoundedFixed`), by unit-patch interpolation along words (SP 491-494). -/
theorem vortJetTailFixed_of (hG : VortGaussTailFixed) (hA1 : TrainJetsBoundedFixed) :
    VortJetTailFixed := by
  intro ρ hρ
  obtain ⟨ν1, hν1, HG⟩ := hG ρ hρ
  obtain ⟨ν2, hν2, HA⟩ := hA1 ρ hρ
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun ν hν hle tr htr ℓ j => ?_⟩
  obtain ⟨b, C₀, C', C, hb, hC₀, hC', hC, hgauss⟩ :=
    HG ν hν (hle.trans (min_le_left _ _)) tr htr
  have hA := HA ν hν (hle.trans (min_le_right _ _)) tr htr
  have hbase : ∃ K b C₀ : ℝ, ∃ N : ℕ, 0 < K ∧ 0 < b ∧ 0 < C₀ ∧
      ∀ S l s : ℝ, ∀ z : Plane, 0 ≤ S → 0 ≤ l → 0 < s → s ≤ S → C' / ν + 2 + l ≤ |z.2| →
        |(fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) (s, z)| ≤ K * (1 + S) ^ N *
          (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S)))) := by
    refine ⟨C, b, C₀, 0, hC, hb, hC₀, fun S l s z hS hl hs hsS hz => ?_⟩
    have h := hgauss s hs z
    have hm : l ≤ max (|z.2| - C' / ν) 0 := le_max_of_le_left (by linarith)
    have hm2 : l ^ 2 ≤ (max (|z.2| - C' / ν) 0) ^ 2 := pow_le_pow_left₀ hl hm 2
    have hD : 0 < C₀ + ν * s := add_pos_of_pos_of_nonneg hC₀ (mul_nonneg hν.le hs.le)
    have hDS : C₀ + ν * s ≤ C₀ + ν * S := by nlinarith
    have hq : b * l ^ 2 / (C₀ + ν * S) ≤ b * (max (|z.2| - C' / ν) 0) ^ 2 / (C₀ + ν * s) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hm2 hb.le) hD hDS
    have he : Real.exp (-(b * (max (|z.2| - C' / ν) 0) ^ 2 / (C₀ + ν * s))) ≤
        Real.exp (-(b * l ^ 2 / (C₀ + ν * S))) := Real.exp_le_exp.2 (by linarith)
    have hpos := Real.exp_pos (-(b * l))
    show |Cyl.curl (tr.v s) z| ≤ _
    rw [pow_zero, mul_one]
    calc |Cyl.curl (tr.v s) z| ≤ C * Real.exp (-(b * (max (|z.2| - C' / ν) 0) ^ 2 /
          (C₀ + ν * s))) := h
      _ ≤ C * (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S)))) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          linarith
  exact FluctTail.vortJet_of_base hν tr hA hC' hbase ℓ j

/-- **`FluctTransverseTailFixed` from the Gaussian vorticity tail** and the two existing Part I
leaves `TrainJetsBoundedFixed` (bounded age jets of `v`) and `TrainFluctAgeJetFixed`. -/
theorem fluctTransverseTailFixed_of_gauss (hG : VortGaussTailFixed)
    (hA1 : TrainJetsBoundedFixed) (hA2 : TrainFluctAgeJetFixed) : FluctTransverseTailFixed :=
  FluctTail.fluctTransverseTailFixed_of_vort (vortJetTailFixed_of hG hA1) hA2

end UnforcedLeray.Short.IIb.WeightedTrainFluctAux
