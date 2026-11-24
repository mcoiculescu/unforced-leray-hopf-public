import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.AdvCommutator

/-!
# Part I, task `PartI:T08/7/2/3` (`JTBoundB`): decomposition

Source: `the November 2 reference manuscript` lines 352-358 (differentiated
transport, `‖[D^j, e·∇]e‖₂ ≤ C_j ‖∇e‖_∞ ‖D^j e‖₂`).

The Leibniz expansion over `wacSplits` (`jai_expand`, `AdvInt.lean`) already exists. The leaves are

* `JTExpand`: the integrated Leibniz expansion of `⟨D^j f, D^j (u·∇)h⟩` (shared with `JTBoundQ`),
* `JTBTerm`: Cauchy-Schwarz bound of one term (`V`-factor bounded by `M`),
* `JTBCount`: the pure counting/Cauchy-Schwarz bound of the sum of all terms.

`jtBoundB_of` assembles `JTBoundB`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)

/-- **Leaf (integrated Leibniz expansion)** (lines 352-358): under the hypotheses of `JTAdvInt`,
`⟨D^j f, D^j (u·∇)h⟩ = ∑_{|w|=j} ∑_k ∑_{(a,b) ∈ wacSplits w} ∑_m ∫_cell ∂_w f_k · ∂_a u_m · ∂_{b m} h_k`
(`b m` is `b` followed by the letter `dirOf m`). Route: `jai_expand` (`AdvInt.lean`) inside the
integral, `integral_finset_sum`, and integrability of each product as in `jtAdvInt_proof`
(`jai_int3`, `jai_list_integrable`), `m = 0, 1` matching `[true]`, `[false]` (`dirOf`). -/
def JTExpand : Prop :=
  ∀ (j : ℕ) (c : ℝ) (u h f : Plane → Vec), ContDiff ℝ ∞ u → ContDiff ℝ ∞ h → CellSmoothL2 c f →
    (CellSmoothL2 c u ∨ CellSmoothL2 c h) →
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w u k z| ≤ M) →
    (∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w h k z| ≤ M) →
    jetPair c j f (advB u h) =
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ((wacSplits w).map (fun p =>
        ∑ m : Fin 2, ∫ z in Cyl.cell c,
          wordComp w f k z * (wordComp p.1 u m z * wordComp (p.2 ++ [dirOf m]) h k z))).sum

/-- **Leaf (one term)** (lines 352-358): `|∫_cell ∂_w f_k · ∂_a f_m · ∂_{b m} V_k| ≤
M_{|b|+1} √(∫ (∂_a f_m)²) √(∫ (∂_w f_k)²)`: the `V`-word `b m` has length `|b|+1`, so
`|∂_{b m} V_k| ≤ M_{|b|+1}` (`JTHyp`; `M ≥ 0` follows); then `abs_int_cs` (`ForcingIBP.lean`) for
`a = ∂_w f_k`, `b = ∂_a f_m · ∂_{b m} V_k`, with `∫ b² ≤ M² ∫ (∂_a f_m)²`. Integrability of the
squares and products: `CellSmoothL2` (`MemLp.integrable_mul`, `Integrable.mul_bdd`). -/
def JTBTerm : Prop :=
  ∀ (c : ℝ) (V f : Plane → Vec) (G : ℝ) (M : ℕ → ℝ), JTHyp c V f G M →
    ∀ (w : List Bool) (p : List Bool × List Bool) (m k : Fin 2),
      |∫ z in Cyl.cell c,
          wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)| ≤
        M (p.2.length + 1) * Real.sqrt (∫ z in Cyl.cell c, wordComp p.1 f m z * wordComp p.1 f m z) *
          Real.sqrt (∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z)

/-- **Leaf (counting)** (lines 352-358): a pure inequality for nonnegative reals, no analysis.
For `w` of length `j` and `(a,b) ∈ wacSplits w`: `|a|+|b| = j` (`wac_splits_len_sum`), so with
`s = |a|` the weight is `M_{j-s+1}`, `i = j+1-s ∈ [1,j+1]`, and `a ∈ wordsOfLength s`. For each `s`,
Cauchy-Schwarz over the finite index set `(w, split, m, k)` (`Real.sum_sqrt_mul_sqrt_le`) gives
`∑ √(I a m) √(I w k) ≤ √(∑ I a m over the index set) √(∑ I w k over the index set)`, and each
index set sums over a word `a` of length `s` at most `4^j` times (there are `4^j` pairs
`(w, split)` altogether; `wac_splits_length`), resp. over each `w` at most `2^j · 2`
times. So `A = 2 · 4^j · 2^j` (or any constant depending only on `j`) works. -/
def JTBCount : Prop :=
  ∀ j : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ → ℝ) (I : List Bool → Fin 2 → ℝ),
    (∀ i, 0 ≤ M i) → (∀ a m, 0 ≤ I a m) →
    ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ((wacSplits w).map (fun p =>
        ∑ m : Fin 2, M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k))).sum ≤
      A * ∑ i ∈ Finset.Icc 1 (j + 1),
        M i * Real.sqrt (∑ a ∈ wordsOfLength (j + 1 - i), ∑ m : Fin 2, I a m) *
          Real.sqrt (∑ w ∈ wordsOfLength j, ∑ k : Fin 2, I w k)

/-- `⟨D^s f, D^s f⟩` as a sum of integrals of squares. -/
theorem jetEnergy_eq_sum {c : ℝ} {f : Plane → Vec} (hf : CellSmoothL2 c f) (s : ℕ) :
    jetEnergy c s f = ∑ a ∈ wordsOfLength s, ∑ m : Fin 2,
      ∫ z in Cyl.cell c, wordComp a f m z * wordComp a f m z := by
  unfold jetEnergy jetPair
  have hI : ∀ (a : List Bool) (m : Fin 2),
      Integrable (fun z => wordComp a f m z * wordComp a f m z) (volume.restrict (Cyl.cell c)) :=
    fun a m => (hf.2.2 a m).integrable_mul (hf.2.2 a m)
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun m _ => hI a m))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun m _ => hI a m)]

theorem list_sum_abs_le {α : Type*} (φ ψ : α → ℝ) :
    ∀ L : List α, (∀ x ∈ L, |φ x| ≤ ψ x) → |(L.map φ).sum| ≤ (L.map ψ).sum
  | [], _ => by simp
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans
      (add_le_add (h x (by simp)) (list_sum_abs_le φ ψ L (fun y hy => h y (by simp [hy]))))

theorem jtBoundB_of (h1 : JTExpand) (h2 : JTBTerm) (h3 : JTBCount) : JTBoundB := by
  intro j
  obtain ⟨A, hA, hC⟩ := h3 j
  refine ⟨A, hA, ?_⟩
  intro c V f G M H
  have H' := H
  obtain ⟨hc, hV, hVp, hVd, hf, hfd, hfb, hG, hM⟩ := H'
  have hfs : ContDiff ℝ ∞ f := hf.1
  have bV : ∀ (w : List Bool) (k : Fin 2), ∃ M' : ℝ, ∀ z : Plane, |wordComp w V k z| ≤ M' :=
    fun w k => ⟨M w.length, hM w k⟩
  have hM0 : ∀ i, 0 ≤ M i := fun i =>
    le_trans (abs_nonneg _) (by simpa using hM (List.replicate i true) 0 (0, 0))
  rw [h1 j c f V f hfs hV hf (Or.inl hf) hfb bV]
  set I : List Bool → Fin 2 → ℝ := fun a m => ∫ z in Cyl.cell c, wordComp a f m z * wordComp a f m z
    with hIdef
  have hI0 : ∀ a m, 0 ≤ I a m := fun a m => integral_nonneg fun z => mul_self_nonneg _
  have hterm : ∀ (w : List Bool) (k : Fin 2) (p : List Bool × List Bool),
      |∑ m : Fin 2, ∫ z in Cyl.cell c,
          wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z)| ≤
        ∑ m : Fin 2, M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k) := by
    intro w k p
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    exact h2 c V f G M H w p m k
  have hcalc : |∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ((wacSplits w).map (fun p =>
        ∑ m : Fin 2, ∫ z in Cyl.cell c,
          wordComp w f k z * (wordComp p.1 f m z * wordComp (p.2 ++ [dirOf m]) V k z))).sum| ≤
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ((wacSplits w).map (fun p =>
        ∑ m : Fin 2, M (p.2.length + 1) * Real.sqrt (I p.1 m) * Real.sqrt (I w k))).sum := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    exact list_sum_abs_le _ _ _ (fun p _ => hterm w k p)
  refine hcalc.trans ((hC M I hM0 hI0).trans (le_of_eq ?_))
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← jetEnergy_eq_sum hf, ← jetEnergy_eq_sum hf]

end UnforcedLeray.Short.PartI
