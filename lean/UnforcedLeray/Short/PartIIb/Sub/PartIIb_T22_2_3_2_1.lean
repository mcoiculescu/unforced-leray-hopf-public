import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2

/-!


Source: `the November 2 reference manuscript` lines 2085-2093 (train comparison
`TrainClose`, bounded drift) and 2100-2105 (weighted maximum principle for the backward problem).

Plan (Phragmen-Lindelof with a decaying barrier plus a growing barrier):
* `BwdDriftBound`: the train drift `tr.v` is bounded on `[0, Σ/ν] × ℝ²` (`TrainClose.plane_bound`
  for `v - V_c`, plus boundedness of `V_c`).
* `BwdBarrier`: explicit calculus: `A e^{K₁(t-r)} (1+η²)^{-N} + ε e^{K₂(t-r)} (1+η²)^{1/2}` is a
  backward supersolution for any drift bounded by `V`.
* `BwdMaxPrinciple`: weak maximum principle on the periodic strip for a bounded solution against a
  coercive supersolution.
`bwdWeightedSup_of` assembles them (letting `ε → 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- `W` is a `C²`, `q`-periodic backward supersolution of `W_r + νΔW + b·∇W ≤ 0` on `(s,t)`. -/
def IsBwdSuper (ν c s t : ℝ) (b0 b1 W : ℝ → B0579.Plane → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun z : ℝ × B0579.Plane => W z.1 z.2) (Icc s t ×ˢ univ) ∧
  (∀ r ∈ Icc s t, ∀ x : B0579.Plane, W r (x.1 + c, x.2) = W r x) ∧
  ∀ r ∈ Ioo s t, ∀ x : B0579.Plane, ∃ D : ℝ, HasDerivAt (fun r' => W r' x) D r ∧
    D + ν * lapP (W r) x + (b0 r x * B0579.pd 0 (W r) x + b1 r x * B0579.pd 1 (W r) x) ≤ 0

/-- **Leaf `/1`** (SP 2085-2093): the train drift is bounded on `[0, Σ/ν] × ℝ²`. -/
def BwdDriftBound : Prop :=
  ∀ (Sg ν c δ : ℝ), 0 < Sg → 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∃ V : ℝ, 0 ≤ V ∧ ∀ r ∈ Icc (0 : ℝ) (Sg / ν), ∀ x : B0579.Plane,
      |tr.v r x 0| ≤ V ∧ |tr.v r x 1| ≤ V

/-- **Leaf `/2`** (SP 2100-2105): explicit barrier.  With `g = (1+η²)^{-N}`:
`|g'/g| ≤ |N|`, `g''/g ≤ 2|N| + 4|N(N+1)|`, similarly for `(1+η²)^{1/2}`; choose `K₁, K₂` larger
than `ν·(second-derivative ratio) + V·(first-derivative ratio)`. -/
def BwdBarrier : Prop :=
  ∀ (ν V N : ℝ), 0 < ν → 0 ≤ V → ∃ K1 K2 : ℝ, ∀ (c s t : ℝ) (b0 b1 : ℝ → B0579.Plane → ℝ),
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane, |b0 r x| ≤ V ∧ |b1 r x| ≤ V) → ∀ A ε : ℝ, 0 ≤ A → 0 ≤ ε →
    IsBwdSuper ν c s t b0 b1 (fun r x => A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N) +
      ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2))

/-- **Leaf `/3`**: weak maximum principle on the periodic strip (Phragmen-Lindelof form):
a bounded `C²` periodic solution `U` of `U_r + νΔU + b·∇U = 0` on `(s,t)` lies below a coercive
supersolution `W` if it does at the terminal time.  Proof: for `δ > 0` the function
`U - W - δ e^{...}` has a nonpositive maximum on the compact box `{|η| ≤ L}` (periodicity in `q`),
since it is `< 0` for `|η| ≥ L` by coercivity and boundedness of `U`. -/
def BwdMaxPrinciple : Prop :=
  ∀ (ν c s t : ℝ) (b0 b1 U W : ℝ → B0579.Plane → ℝ), 0 < ν → 0 < c → s ≤ t →
    ContDiffOn ℝ 2 (fun z : ℝ × B0579.Plane => U z.1 z.2) (Icc s t ×ˢ univ) →
    (∀ r ∈ Icc s t, ∀ x : B0579.Plane, U r (x.1 + c, x.2) = U r x) →
    (∃ M : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |U r x| ≤ M) →
    (∀ r ∈ Ioo s t, ∀ x : B0579.Plane, HasDerivAt (fun r' => U r' x)
      (-(ν * lapP (U r) x + (b0 r x * B0579.pd 0 (U r) x + b1 r x * B0579.pd 1 (U r) x))) r) →
    IsBwdSuper ν c s t b0 b1 W →
    (∀ M : ℝ, ∃ L : ℝ, ∀ r ∈ Icc s t, ∀ x : B0579.Plane, L ≤ |x.2| → M ≤ W r x) →
    (∀ x : B0579.Plane, |U t x| ≤ W t x) →
    ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |U r x| ≤ W r x

/-- `Σ/ν`-drift bounded on `[s,t] ⊆ [0, Σ/ν]`, barrier, and maximum principle give the target. -/
theorem bwdWeightedSup_of (h1 : BwdDriftBound) (h2 : BwdBarrier) (h3 : BwdMaxPrinciple) :
    BwdWeightedSup := by
  intro Sg ν c δ hSg hν hc hδ tr htr s t hs hst ht ψ hψ φ hφ N
  obtain ⟨V, hV0, hV⟩ := h1 Sg ν c δ hSg hν hc hδ tr htr
  set N' : ℝ := max N 0 with hN'
  obtain ⟨K1, K2, hK⟩ := h2 ν V N' hν hV0
  obtain ⟨M, hM⟩ := hφ.bounded
  have hMt : ∀ x, |ψ x| ≤ M := fun x => by simpa [hφ.terminal] using hM t ⟨hst, le_rfl⟩ x
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMt (0, 0))
  obtain ⟨R, hR⟩ := hψ.band
  set A : ℝ := M * (1 + R ^ 2) ^ N' with hA
  have hA0 : 0 ≤ A := by positivity
  have hbdd : ∀ r ∈ Icc s t, ∀ x : B0579.Plane, |tr.v r x 0| ≤ V ∧ |tr.v r x 1| ≤ V :=
    fun r hr x => hV r ⟨le_trans hs hr.1, le_trans hr.2 ht⟩ x
  have key : ∀ ε : ℝ, 0 < ε → ∀ r ∈ Icc s t, ∀ x : B0579.Plane,
      |φ r x| ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') +
        ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
    intro ε hε
    refine h3 ν c s t (fun r x => tr.v r x 0) (fun r x => tr.v r x 1) φ _ hν hc hst
      (hφ.smooth.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 le_top | simp | norm_cast)) hφ.periodic ⟨M, hM⟩ hφ.pde
      (hK c s t _ _ hbdd A ε hA0 hε.le) ?_ ?_
    · intro M'
      set m : ℝ := Real.exp (-(|K2| * (t - s))) with hm
      have hm0 : 0 < m := Real.exp_pos _
      have hεm : 0 < ε * m := mul_pos hε hm0
      refine ⟨|M'| / (ε * m), fun r hr x hx => ?_⟩
      have hexp : m ≤ Real.exp (K2 * (t - r)) := by
        apply Real.exp_le_exp.2
        have h1 : -|K2| ≤ K2 := neg_abs_le K2
        have h2 : K2 ≤ |K2| := le_abs_self K2
        have h3 : 0 ≤ t - r := by linarith [hr.2]
        have h4 : t - r ≤ t - s := by linarith [hr.1]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) h3, mul_nonneg (abs_nonneg K2) (sub_nonneg.2 h4),
          mul_nonneg (sub_nonneg.2 h1) h3]
      have hsq : |x.2| ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow]
        calc |x.2| = Real.sqrt (x.2 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
      have hg : 0 ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') := by positivity
      have hL : 0 ≤ |M'| / (ε * m) := by positivity
      have h5 : |M'| / (ε * m) ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := le_trans hx hsq
      have h6 : |M'| ≤ ε * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
        have : |M'| ≤ (ε * m) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by
          have := (div_le_iff₀ hεm).1 h5
          linarith
        refine le_trans this ?_
        have hp : 0 ≤ (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by positivity
        have : ε * m ≤ ε * Real.exp (K2 * (t - r)) := by gcongr
        exact mul_le_mul_of_nonneg_right this hp
      show M' ≤ _
      linarith [le_abs_self M']
    · intro x
      have e1 : Real.exp (K1 * (t - t)) = 1 := by simp
      have e2 : Real.exp (K2 * (t - t)) = 1 := by simp
      show |φ t x| ≤ A * Real.exp (K1 * (t - t)) * (1 + x.2 ^ 2) ^ (-N') +
        ε * Real.exp (K2 * (t - t)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2)
      rw [e1, e2, hφ.terminal]
      have hp : 0 ≤ ε * 1 * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) := by positivity
      by_cases hx : R < |x.2|
      · rw [hR x hx]; simp only [abs_zero]; positivity
      · rw [not_lt] at hx
        have hx2 : x.2 ^ 2 ≤ R ^ 2 := by
          have := sq_abs x.2
          nlinarith [abs_nonneg x.2, mul_nonneg (sub_nonneg.2 hx) (add_nonneg (abs_nonneg x.2) (le_trans (abs_nonneg _) hx))]
        have hpos : 0 < 1 + x.2 ^ 2 := by positivity
        have hle : (1 + R ^ 2) ^ (-N') ≤ (1 + x.2 ^ 2) ^ (-N') :=
          Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by
            have : 0 ≤ N' := le_max_right _ _
            linarith)
        have hMx := hMt x
        have hRpos : 0 < (1 + R ^ 2) := by positivity
        have hid : (1 + R ^ 2) ^ N' * (1 + R ^ 2) ^ (-N') = 1 := by
          rw [← Real.rpow_add hRpos]; simp
        calc |ψ x| ≤ M := hMx
          _ = A * (1 + R ^ 2) ^ (-N') := by rw [hA, mul_assoc, hid, mul_one]
          _ ≤ A * (1 + x.2 ^ 2) ^ (-N') := by gcongr
          _ ≤ _ := by linarith
  refine ⟨A * Real.exp (|K1| * (t - s)), fun r hr x => ?_⟩
  have hpos : 0 < 1 + x.2 ^ 2 := by positivity
  have hb : |φ r x| ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') := by
    set Phi : ℝ := Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) with hPhi
    have hPhi0 : 0 ≤ Phi := by positivity
    refine le_of_forall_pos_le_add fun e he => ?_
    have := key (e / (Phi + 1)) (by positivity) r hr x
    have h2 : e / (Phi + 1) * Real.exp (K2 * (t - r)) * (1 + x.2 ^ 2) ^ ((1 : ℝ) / 2) ≤ e := by
      rw [mul_assoc, ← hPhi, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hN : (1 + x.2 ^ 2) ^ N ≤ (1 + x.2 ^ 2) ^ N' :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x.2]) (le_max_left _ _)
  have hid : (1 + x.2 ^ 2) ^ (-N') * (1 + x.2 ^ 2) ^ N' = 1 := by
    rw [← Real.rpow_add hpos]; simp
  have hK1 : Real.exp (K1 * (t - r)) ≤ Real.exp (|K1| * (t - s)) := by
    apply Real.exp_le_exp.2
    have h3 : 0 ≤ t - r := by linarith [hr.2]
    have h4 : t - r ≤ t - s := by linarith [hr.1]
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self K1)) h3, mul_nonneg (abs_nonneg K1) (sub_nonneg.2 h4)]
  calc |φ r x| * (1 + x.2 ^ 2) ^ N ≤ |φ r x| * (1 + x.2 ^ 2) ^ N' := by gcongr
    _ ≤ A * Real.exp (K1 * (t - r)) * (1 + x.2 ^ 2) ^ (-N') * (1 + x.2 ^ 2) ^ N' := by gcongr
    _ = A * Real.exp (K1 * (t - r)) := by rw [mul_assoc, hid, mul_one]
    _ ≤ A * Real.exp (|K1| * (t - s)) := by gcongr

end UnforcedLeray.Short.IIb
