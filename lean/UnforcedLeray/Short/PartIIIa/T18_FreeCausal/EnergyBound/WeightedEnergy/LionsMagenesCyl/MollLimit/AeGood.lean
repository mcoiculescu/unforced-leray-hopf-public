import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/13` (`MollLimit`): almost every slice is good

Source of record: `the November 2 reference manuscript` lines 3427-3440 (energy
class) and 3541-3552. Target: `lmAeGoodSlice : LMAeGoodSlice`, i.e. for a.e. `s > 0` the slice
`b(s)` and the columns of `G(s)`, `F(s)` lie in `L²(cell)`.

Route. Cover `(0,∞)` by the countable family `[1/(n+1), n+1]`. On each such interval, Tonelli
(`lintegral_prod`) turns the finiteness of `∫⁻ over [s₁,s₂] × cell` (`energyLoc`, `L2locTensor`)
into the finiteness of the inner cell integral for a.e. `s`. For such `s`, each component is
measurable and its squared norm is dominated by the finite integrand, hence `MemLp 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Measurability of the Euclidean norm of a `ℂ²`-valued function. -/
theorem aeg_measurable_vnorm2 {β : Type*} [MeasurableSpace β] {f : β → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun p => f p i) : Measurable fun p => vnorm2 (f p) := by
  unfold vnorm2
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => ((hf i).norm).pow_const 2)

/-- Measurability of the Frobenius norm of a `ℂ²ˣ²`-valued function. -/
theorem aeg_measurable_tnorm2 {β : Type*} [MeasurableSpace β] {T : β → Fin 2 → Fin 2 → ℂ}
    (hT : ∀ i j, Measurable fun p => T p i j) : Measurable fun p => tnorm2 (T p) := by
  unfold tnorm2
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ((hT i j).norm).pow_const 2)

/-- A component of a vector is bounded by the Euclidean norm. -/
theorem aeg_norm_sq_le_vnorm2 (v : Fin 2 → ℂ) (i : Fin 2) : ‖v i‖ ^ 2 ≤ vnorm2 v ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  exact Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

/-- An entry of a matrix is bounded by the Frobenius norm. -/
theorem aeg_norm_sq_le_tnorm2 (T : Fin 2 → Fin 2 → ℂ) (i j : Fin 2) :
    ‖T i j‖ ^ 2 ≤ tnorm2 T ^ 2 := by
  unfold tnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _)]
  calc ‖T i j‖ ^ 2 ≤ ∑ l, ‖T i l‖ ^ 2 :=
        Finset.single_le_sum (f := fun l => ‖T i l‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ k, ∑ l, ‖T k l‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ∑ l, ‖T k l‖ ^ 2)
          (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)

/-- A real function whose square is pointwise dominated by an integrable-type integrand is
`L²(cell)`-integrable: if `‖g x‖² ≤ X x` and `∫⁻ ofReal X < ∞`, then `g ∈ L²`. -/
theorem aeg_memLp_of_sq {μ : Measure (ℝ × ℝ)} {g : ℝ × ℝ → ℂ} (hg : Measurable g)
    {X : ℝ × ℝ → ℝ} (hX : ∀ x, ‖g x‖ ^ 2 ≤ X x) (hfin : ∫⁻ x, ENNReal.ofReal (X x) ∂μ < ⊤) :
    MemLp g 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 ⟨(hg.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  rw [Real.enorm_eq_ofReal (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hX x)

/-- Tonelli on `[a,b] × cell`: if the integral over the product is finite, then for a.e. `s` in
`[a,b]` the inner cell integral is finite. -/
theorem aeg_slice_finite {c a b : ℝ} {Φ : ℝ × (ℝ × ℝ) → ℝ≥0∞} (hΦ : Measurable Φ)
    (h : ∫⁻ p in Icc a b ×ˢ B0579.cell c, Φ p < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Icc a b)), ∫⁻ x in B0579.cell c, Φ (s, x) < ⊤ := by
  have hT : ∫⁻ p in Icc a b ×ˢ B0579.cell c, Φ p
      = ∫⁻ s in Icc a b, ∫⁻ x in B0579.cell c, Φ (s, x) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
      lintegral_prod _ hΦ.aemeasurable]
  rw [hT] at h
  exact ae_lt_top' (Measurable.lintegral_prod_right' hΦ).aemeasurable h.ne

/-- `(0,∞)` is the countable union of the intervals `[1/(n+1), n+1]`. -/
theorem aeg_Ioi_eq : Ioi (0 : ℝ) = ⋃ n : ℕ, Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
  ext s
  simp only [mem_Ioi, mem_iUnion, mem_Icc]
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := exists_nat_gt (max s (1 / s))
    have hs1 : s < n := lt_of_le_of_lt (le_max_left _ _) hn
    have hs2 : 1 / s < n := lt_of_le_of_lt (le_max_right _ _) hn
    rw [div_lt_iff₀ hs] at hs2
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine ⟨n, ?_, by linarith⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rintro ⟨n, h1, -⟩
    exact lt_of_lt_of_le (by positivity) h1

/-- Almost every slice is good (SP 3427-3440, the energy class `b, ∇b, F ∈ L²_loc((0,∞); L²)`). -/
theorem lmAeGoodSlice : LMAeGoodSlice := by
  intro c ν μ F b G hD
  have hΦb : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((aeg_measurable_vnorm2 hD.sol.measurable).pow_const 2).add
        ((aeg_measurable_tnorm2 hD.sol.gradMeasurable).pow_const 2))
  have hΦF : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (tnorm2 (F p) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_tnorm2 hD.meas).pow_const 2)
  rw [aeg_Ioi_eq, ae_restrict_iUnion_iff]
  intro n
  have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hnab : 1 / ((n : ℝ) + 2) < (n : ℝ) + 2 := by
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hA := aeg_slice_finite hΦb (hD.sol.energyLoc _ _ hn0 hnab)
  have hB := aeg_slice_finite hΦF (hD.l2loc _ _ hn0 hnab)
  filter_upwards [hA, hB] with s hsA hsB
  unfold LMGoodSlice LMCellL2
  refine ⟨fun i => ?_, fun j i => ?_, fun j i => ?_⟩
  · -- `b(s)`
    refine aeg_memLp_of_sq ((hD.sol.measurable i).comp measurable_prodMk_left)
      (X := fun x => vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) (fun x => ?_) hsA
    exact le_trans (aeg_norm_sq_le_vnorm2 _ i) (le_add_of_nonneg_right (sq_nonneg _))
  · -- columns of `G(s)`
    refine aeg_memLp_of_sq ((hD.sol.gradMeasurable i j).comp measurable_prodMk_left)
      (X := fun x => vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) (fun x => ?_) hsA
    exact le_trans (aeg_norm_sq_le_tnorm2 _ i j) (le_add_of_nonneg_left (sq_nonneg _))
  · -- columns of `F(s)`
    refine aeg_memLp_of_sq ((hD.meas i j).comp measurable_prodMk_left)
      (X := fun x => tnorm2 (F (s, x)) ^ 2) (fun x => ?_) hsB
    exact aeg_norm_sq_le_tnorm2 _ i j

end UnforcedLeray.Short.IIIa
