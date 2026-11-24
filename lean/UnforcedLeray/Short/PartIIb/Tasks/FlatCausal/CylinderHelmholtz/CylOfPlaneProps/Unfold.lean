import UnforcedLeray.Short.PartIIb.Sub.T12_1_5
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# Leaf `PartII-b:T12/1/5/1`: unfolding against a compactly supported weight (`CylUnfold`)

Target `cylUnfold : CylUnfold` (definition in `Sub/T12_1_5.lean`). Source of record:
`the November 2 reference manuscript`, line 1670 (the planar cylinder projection)
and lines 1727-1731 (the zero-frequency remark).

Proof. Let `w` have support in `|x| ≤ A` and choose `N` with `A < N c`. For `q` in the cell
`-c/2 ≤ q < c/2`, only the translates with `n ∈ [-N, N]` meet the support of `w(q + n c)`.
* Integrability: lattice unfolding (`Cyl.lintegral_eq_tsum_cell`) leaves finitely many nonzero
  terms, each integrable on the cell since `w` is bounded and `h` is integrable on the cell.
* Value: lattice unfolding (`Cyl.integral_eq_tsum_cell`) leaves the finite sum
  `∑_{n ∈ [-N, N]} w(q + n c) h(z)`, and `∑_{n ∈ [-N, N]} w(q + n c) = s` on the cell
  (reindex the `HasSum` by `n ↦ -n`, then uniqueness of sums of finitely supported families).

Helper lemmas carry the prefix `cuf_`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A compactly supported real function vanishes outside some ball. -/
theorem cuf_exists_radius {w : ℝ → ℝ} (hsupp : HasCompactSupport w) :
    ∃ A : ℝ, ∀ x : ℝ, A < |x| → w x = 0 := by
  obtain ⟨R, hR⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨R, fun x hx => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have h1 : x ∈ Metric.closedBall (0 : ℝ) R := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  linarith

/-- Outside the window `|n| ≤ N`, the shifted weight `w (q + n c)` vanishes for
`-c/2 ≤ q < c/2`, provided `A < N c` and `w` vanishes beyond `A`. -/
theorem cuf_zero_outside {w : ℝ → ℝ} {c A : ℝ} (hc : 0 < c) (hA : ∀ x : ℝ, A < |x| → w x = 0)
    {N : ℕ} (hN : A < (N : ℝ) * c) {q : ℝ} (hq1 : -c / 2 ≤ q) (hq2 : q < c / 2)
    {n : ℤ} (hn : n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) : w (q + n * c) = 0 := by
  apply hA
  rw [Finset.mem_Icc] at hn
  rcases (show n < -(N : ℤ) ∨ (N : ℤ) < n by omega) with h1 | h1
  · have h2 : (n : ℝ) + 1 ≤ -(N : ℝ) := by
      exact_mod_cast (show n + 1 ≤ -(N : ℤ) by omega)
    have h3 : ((n : ℝ) + 1) * c ≤ -(N : ℝ) * c := mul_le_mul_of_nonneg_right h2 hc.le
    have h4 : q + n * c < -A := by nlinarith
    exact lt_of_lt_of_le (show A < -(q + n * c) by linarith) (neg_le_abs _)
  · have h2 : (N : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (show (N : ℤ) + 1 ≤ n by omega)
    have h3 : ((N : ℝ) + 1) * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right h2 hc.le
    have h4 : A < q + n * c := by nlinarith
    exact lt_of_lt_of_le h4 (le_abs_self _)

/-- Reindexing `n ↦ -n` in the `HasSum` over `ℤ`. -/
theorem cuf_hasSum_shift {w : ℝ → ℝ} {c s : ℝ}
    (hsum : ∀ q : ℝ, HasSum (fun n : ℤ => w (q - n * c)) s) (q : ℝ) :
    HasSum (fun n : ℤ => w (q + n * c)) s := by
  have key : (fun n : ℤ => w (q + n * c)) = (fun n : ℤ => w (q - n * c)) ∘ (Equiv.neg ℤ) := by
    funext n
    simp [Function.comp_apply, Equiv.neg_apply, Int.cast_neg, neg_mul, sub_neg_eq_add]
  rw [key]
  exact (Equiv.neg ℤ).hasSum_iff.mpr (hsum q)

/-- On the cell, the finite window `|n| ≤ N` already carries the whole sum `s`. -/
theorem cuf_window_sum {w : ℝ → ℝ} {c s A : ℝ} (hc : 0 < c) (hA : ∀ x : ℝ, A < |x| → w x = 0)
    {N : ℕ} (hN : A < (N : ℝ) * c)
    (hsum : ∀ q : ℝ, HasSum (fun n : ℤ => w (q - n * c)) s) {q : ℝ} (hq1 : -c / 2 ≤ q)
    (hq2 : q < c / 2) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), w (q + n * c) = s := by
  have hfin : HasSum (fun n : ℤ => w (q + n * c))
      (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), w (q + n * c)) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => cuf_zero_outside hc hA hN hq1 hq2 hn)
  exact (HasSum.unique (cuf_hasSum_shift hsum q) hfin).symm

/-- **Leaf `PartII-b:T12/1/5/1`** (unfolding against a compactly supported weight). -/
theorem cylUnfold : CylUnfold := by
  unfold CylUnfold
  intro c w s hc hwc hsupp hsum h hh
  obtain ⟨hP, hmeas, hint⟩ := hh
  have hP' : UnforcedLeray.Cyl.IsPeriodic c h := hP
  have hshift : ∀ (n : ℤ) (z : ℝ × ℝ), h (z.1 + n * c, z.2) = h z :=
    fun n z => UnforcedLeray.Cyl.IsPeriodic.add_int_mul hP' n z
  obtain ⟨A, hA⟩ := cuf_exists_radius hsupp
  obtain ⟨N, hN0⟩ := exists_nat_gt (A / c)
  have hN : A < (N : ℝ) * c := (div_lt_iff₀ hc).mp hN0
  obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support hsupp
  -- continuity of the shifted weights
  have hcontn : ∀ n : ℤ, Continuous (fun z : ℝ × ℝ => (w (z.1 + n * c) : ℂ)) := by
    intro n
    have hl : Continuous (fun z : ℝ × ℝ => z.1 + (n : ℝ) * c) :=
      continuous_fst.add continuous_const
    exact Complex.continuous_ofReal.comp (hwc.comp hl)
  -- each shifted term is integrable on the cell
  have hintn : ∀ n : ℤ, Integrable (fun z : ℝ × ℝ => (w (z.1 + n * c) : ℂ) * h z)
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    intro n
    exact Integrable.bdd_mul (c := C) hint (hcontn n).aestronglyMeasurable
      (ae_of_all _ fun z => by simpa using hC (z.1 + n * c))
  -- a.e. measurability on the plane
  have hmeasF : AEStronglyMeasurable (fun z : ℝ × ℝ => (w z.1 : ℂ) * h z) volume := by
    have hc1 : Continuous (fun z : ℝ × ℝ => (w z.1 : ℂ)) :=
      Complex.continuous_ofReal.comp (hwc.comp continuous_fst)
    exact hc1.aestronglyMeasurable.mul hmeas
  -- the lattice-shifted summands of the unfolding identity
  have hterm : ∀ n : ℤ,
      ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖(w (z.1 + n * c, z.2).1 : ℂ) * h (z.1 + n * c, z.2)‖ₑ
        = ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖(w (z.1 + n * c) : ℂ) * h z‖ₑ := by
    intro n
    simp only [hshift]
  -- integrability on the plane: finitely many nonzero lattice terms
  have hfin : ∫⁻ z, ‖(w z.1 : ℂ) * h z‖ₑ < (⊤ : ENNReal) := by
    rw [UnforcedLeray.Cyl.lintegral_eq_tsum_cell hc, tsum_congr hterm,
      tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) ?_]
    · exact ENNReal.sum_lt_top.mpr fun n _ => (hintn n).2
    · intro n hn
      have hEq : EqOn (fun z : ℝ × ℝ => ‖(w (z.1 + n * c) : ℂ) * h z‖ₑ) (fun _ => (0 : ENNReal))
          (UnforcedLeray.Cyl.cell c) := by
        intro z hz'
        obtain ⟨hz1, hz2⟩ := UnforcedLeray.Cyl.mem_cell.mp hz'
        simp [cuf_zero_outside hc hA hN hz1 hz2 hn]
      rw [setLIntegral_congr_fun (UnforcedLeray.Cyl.measurableSet_cell c) hEq, lintegral_zero]
  have hIntPlane : Integrable (fun z : ℝ × ℝ => (w z.1 : ℂ) * h z) volume := ⟨hmeasF, hfin⟩
  -- the lattice-shifted integrands equal the shifted weights times `h` on the cell
  have hsplit : ∀ n : ℤ,
      ∫ z in UnforcedLeray.Cyl.cell c, (w (z.1 + n * c, z.2).1 : ℂ) * h (z.1 + n * c, z.2)
        = ∫ z in UnforcedLeray.Cyl.cell c, (w (z.1 + n * c) : ℂ) * h z := by
    intro n
    simp only [hshift]
  -- the terms outside the window vanish
  have hzeroI : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      ∫ z in UnforcedLeray.Cyl.cell c, (w (z.1 + n * c) : ℂ) * h z = 0 := by
    intro n hn
    have hEq : EqOn (fun z : ℝ × ℝ => (w (z.1 + n * c) : ℂ) * h z) (fun _ => (0 : ℂ))
        (UnforcedLeray.Cyl.cell c) := by
      intro z hz'
      obtain ⟨hz1, hz2⟩ := UnforcedLeray.Cyl.mem_cell.mp hz'
      simp [cuf_zero_outside hc hA hN hz1 hz2 hn]
    rw [setIntegral_congr_fun (UnforcedLeray.Cyl.measurableSet_cell c) hEq, integral_zero]
  -- pull the finite sum of integrals inside the integral
  have hsumint : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∫ z in UnforcedLeray.Cyl.cell c, (w (z.1 + n * c) : ℂ) * h z
        = ∫ z in UnforcedLeray.Cyl.cell c,
            ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (w (z.1 + n * c) : ℂ) * h z :=
    (integral_finsetSum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n _ => hintn n)).symm
  -- on the cell, the window sum is `s`
  have hpt : ∀ z ∈ UnforcedLeray.Cyl.cell c,
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (w (z.1 + n * c) : ℂ) * h z = (s : ℂ) * h z := by
    intro z hz'
    obtain ⟨hz1, hz2⟩ := UnforcedLeray.Cyl.mem_cell.mp hz'
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, cuf_window_sum hc hA hN hsum hz1 hz2]
  refine ⟨hIntPlane, ?_⟩
  rw [UnforcedLeray.Cyl.integral_eq_tsum_cell hc hIntPlane, tsum_congr hsplit,
    tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => hzeroI n hn), hsumint,
    setIntegral_congr_fun (UnforcedLeray.Cyl.measurableSet_cell c) hpt, integral_const_mul]

end UnforcedLeray.Short.IIb
