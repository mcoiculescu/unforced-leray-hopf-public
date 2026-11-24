import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatTermBound

/-!
# `PartIII-b:C/inst/9/4/2`: locally uniform summable majorant of the `f_A` lattice terms

Source of record: `the November 2 reference manuscript`, lines 4963-4970, 5063-5079.

Route. Fix `ν > 0` and `q0 = (s0, (x0, B0))` with `s0 > 0`.  On the open neighbourhood
`T = {q | s0/2 < q.1 < 2 s0 + 1, |x.1| < X, |x.2| < R, ‖B - B0‖ < 1}` (with `X = |x0.1| + 1`,
`R = |x0.2| + 1`) the age `a = 1 + ν s` lies in `[1, 1 + ν (2 s0 + 1)]`, the entries of `B` are
bounded by `Bb = ∑ |B0 i k| + 1`, and `|x.1| ≤ X`, `|x.2| ≤ R`.  The pointwise bound
`FlatSettingInst.ft_term_pt`, the uniform Gaussian domination `FlatSettingInst.ft_E_bound`
and `FlatSettingInst.ft_Y_bound` (all with constants uniform in `s` and `x`) give
`‖faTerm ν j q‖ ≤ C (1 + |jc|)³ exp(-(jc)²/(8 a₂))` with `a₂ = 1 + ν (2 s0 + 1)`, which is
summable in `j` by `gp_poly_summable`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem faTermLocBound : FAtermLocBound := by
  intro ν hν q0 hq0
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = |q0.2.1.1| + 1 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |q0.2.1.2| + 1 := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℝ, Bb = (∑ i, ∑ k, |q0.2.2 i k|) + 1 := ⟨_, rfl⟩
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hBbnn : 0 ≤ Bb := by
    rw [hBb]
    have : 0 ≤ ∑ i, ∑ k, |q0.2.2 i k| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  -- every entry of `q0.2.2` is bounded by the total sum
  have hent : ∀ a b : Fin 3, |q0.2.2 a b| ≤ ∑ i, ∑ k, |q0.2.2 i k| := fun a b =>
    le_trans (Finset.single_le_sum (f := fun k => |q0.2.2 a k|) (fun k _ => abs_nonneg _)
        (Finset.mem_univ b))
      (Finset.single_le_sum (f := fun i => ∑ k, |q0.2.2 i k|)
        (fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _) (Finset.mem_univ a))
  have hs0 : 0 < q0.1 := hq0
  -- the neighbourhood
  obtain ⟨T, hTdef⟩ : ∃ T : Set (ℝ × (ℝ × ℝ) × Mat3),
      T = {q | q0.1 / 2 < q.1 ∧ q.1 < 2 * q0.1 + 1 ∧ |q.2.1.1| < X ∧ |q.2.1.2| < R ∧
        ‖q.2.2 - q0.2.2‖ < 1} := ⟨_, rfl⟩
  have hopen : IsOpen T := by
    rw [hTdef]
    have h1 : IsOpen {q : ℝ × (ℝ × ℝ) × Mat3 | q0.1 / 2 < q.1} :=
      isOpen_lt continuous_const continuous_fst
    have h2 : IsOpen {q : ℝ × (ℝ × ℝ) × Mat3 | q.1 < 2 * q0.1 + 1} :=
      isOpen_lt continuous_fst continuous_const
    have h3 : IsOpen {q : ℝ × (ℝ × ℝ) × Mat3 | |q.2.1.1| < X} :=
      isOpen_lt (by fun_prop) continuous_const
    have h4 : IsOpen {q : ℝ × (ℝ × ℝ) × Mat3 | |q.2.1.2| < R} :=
      isOpen_lt (by fun_prop) continuous_const
    have h5 : IsOpen {q : ℝ × (ℝ × ℝ) × Mat3 | ‖q.2.2 - q0.2.2‖ < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))
  have hmemT : q0 ∈ T := by
    rw [hTdef]
    refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [hX]; linarith
    · rw [hR]; linarith
    · simp
  refine ⟨T, hopen.mem_nhds hmemT, ?_, ?_⟩
  · intro q hq
    rw [hTdef] at hq
    exact lt_trans (by linarith) hq.1
  · -- the summable majorant
    have hα : 0 < 1 / (8 * (1 + ν * (2 * q0.1 + 1))) := div_pos one_pos (by nlinarith [mul_pos hν hs0])
    have hc : 0 < cOf ν := by
      unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
    refine ⟨fun j => (13 * Bb * Real.exp (X ^ 2 / 4) * (1 + X + R) ^ 3) *
        ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (8 * (1 + ν * (2 * q0.1 + 1)))) * (0 - (j : ℝ) * cOf ν) ^ 2)), ?_, ?_⟩
    · exact (gp_poly_summable 0 (1 / (8 * (1 + ν * (2 * q0.1 + 1)))) (cOf ν) hα hc).mul_left _
    · intro j q hq
      rw [hTdef] at hq
      obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
      have hsp : 0 < q.1 := lt_trans (by linarith) hq1
      have hss : q.1 ≤ 2 * q0.1 + 1 := hq2.le
      have hx1 : |q.2.1.1| ≤ X := hq3.le
      have hx2 : |q.2.1.2| ≤ R := hq4.le
      -- entrywise bound on `B = q.2.2`
      have hB : ∀ a b : Fin 3, |q.2.2 a b| ≤ Bb := by
        intro a b
        have e1 : ‖(q.2.2 - q0.2.2) a‖ ≤ ‖q.2.2 - q0.2.2‖ := norm_le_pi_norm _ a
        have e2 : ‖(q.2.2 - q0.2.2) a b‖ ≤ ‖(q.2.2 - q0.2.2) a‖ := norm_le_pi_norm _ b
        have h3 : |q.2.2 a b - q0.2.2 a b| < 1 := by
          have := e2.trans_lt (e1.trans_lt hq5)
          simpa [Real.norm_eq_abs] using this
        have h4 := abs_sub_abs_le_abs_sub (q.2.2 a b) (q0.2.2 a b)
        have h5 := hent a b
        rw [hBb]
        linarith
      have hT := FlatSettingInst.ft_term_pt ν q.1 Bb q.2.2 hν hsp hB q.2.1 j
      have hE := FlatSettingInst.ft_E_bound ν q.1 (2 * q0.1 + 1) X q.2.1 j hν hsp hss hx1
      have hY := FlatSettingInst.ft_Y_bound ν X R q.2.1 j hXnn hRnn hx1 hx2
      unfold faTerm
      calc ‖emb (fderiv ℝ (Vj ν q.1 j) q.2.1 (merApply q.2.2 (xj ν j q.2.1))) +
            mv q.2.2 (emb (Vj ν q.1 j q.2.1))‖
          ≤ 13 * Bb * (Real.exp (-(sq2 (xj ν j q.2.1)) / (4 * ageA ν q.1)) *
              (1 + ‖xj ν j q.2.1‖) ^ 3) := hT
        _ ≤ 13 * Bb * ((Real.exp (X ^ 2 / 4) *
              Real.exp (-(1 / (8 * (1 + ν * (2 * q0.1 + 1)))) * (0 - (j : ℝ) * cOf ν) ^ 2)) *
              ((1 + X + R) ^ 3 * (1 + |0 - (j : ℝ) * cOf ν|) ^ 3)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hE hY (by positivity) (by positivity))
              (by linarith)
        _ = (13 * Bb * Real.exp (X ^ 2 / 4) * (1 + X + R) ^ 3) *
              ((1 + |0 - (j : ℝ) * cOf ν|) ^ 3 *
                Real.exp (-(1 / (8 * (1 + ν * (2 * q0.1 + 1)))) * (0 - (j : ℝ) * cOf ν) ^ 2)) := by
            ring

end UnforcedLeray.Short.PartIIIb.Concrete
