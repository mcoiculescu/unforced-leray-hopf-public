import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.L223.Meas
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung

/-!
# `PartIII-b:C/rep/4/4/1/org/3/3`: the `L^{22/3}` kernel of the transition majorant

Source `the November 2 reference manuscript` 3631-3646 (`sep:young`, `p = 22/19`,
`q = 22/3`, `b = 11/3`: `D^{-4+3/b} = D^{-35/11}`), 5338-5341, 4176-4194.  Order zero and one:
`sepDomYoung`; primitive: `outMajAnnulusL223`; sum: Minkowski (`L223.ltauLq_add_le`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The `L^{11/3}` kernel for the transition majorant** (source 3631-3646, 5338-5341). -/
theorem transMajL223 : TransMajL223 := by
  obtain ⟨C0, hC0, h0⟩ := sepDomYoung 0 (22 / 19) (22 / 3) (11 / 3) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C1, hC1, h1⟩ := sepDomYoung 1 (22 / 19) (22 / 3) (11 / 3) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, hS⟩ := outMajAnnulusL223
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ s = Real.sqrt (5 / 6) := by
    refine ⟨_, Real.sqrt_nonneg _, ?_, rfl⟩
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hκ : 0 < 1 - s := by linarith
  have a1 := Real.rpow_nonneg hκ.le (-(35 / 11) : ℝ)
  have a2 := Real.rpow_nonneg hκ.le (-(46 / 11) : ℝ)
  refine ⟨C0 * (1 - s) ^ (-(35 / 11) : ℝ) + C1 * (1 - s) ^ (-(46 / 11) : ℝ) + Cs, 3, ?_, ?_⟩
  · positivity
  intro ν R P hν hν1 hR1 hP g hgm hgp hgs
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := mul_pos hR hsq
  have hro : R * Real.sqrt (5 * ν / 6) = s * L := by
    rw [hLdef, hs, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hD : transGap ν R = (1 - s) * L := by
    unfold transGap; rw [hro]; ring
  have hDpos : 0 < transGap ν R := by rw [hD]; positivity
  have hN : ∀ D' : ℝ, 0 < D' → ∀ (j : ℕ), True := fun _ _ _ => trivial
  have hy0 : ∀ D' : ℝ, 0 < D' →
      IIIa.ltauLq P (22 / 3) (IIIa.sepDom 0 0 D' g) ≤
        ENNReal.ofReal (C0 * D' ^ (-(35 / 11) : ℝ)) * IIIa.ltauLq P (22 / 19) g := by
    intro D' hD'
    have := h0 0 le_rfl (by norm_num) D' P hD' hP g hgm hgp
    have e : (-4 - ((0 : ℕ) : ℝ) + 3 / (11 / 3) : ℝ) = -(35 / 11) := by norm_num
    rw [e] at this
    exact this
  have hy1 : ∀ D' : ℝ, 0 < D' →
      IIIa.ltauLq P (22 / 3) (IIIa.sepDom 0 1 D' g) ≤
        ENNReal.ofReal (C1 * D' ^ (-(46 / 11) : ℝ)) * IIIa.ltauLq P (22 / 19) g := by
    intro D' hD'
    have := h1 0 le_rfl (by norm_num) D' P hD' hP g hgm hgp
    have e : (-4 - ((1 : ℕ) : ℝ) + 3 / (11 / 3) : ℝ) = -(46 / 11) := by norm_num
    rw [e] at this
    exact this
  have hann := L223.measurableSet_ann ν R
  have mW : Measurable (Function.uncurry (transMajW ν R g)) := by
    have : Function.uncurry (transMajW ν R g) =
        (Prod.snd ⁻¹' streamAnn ν R).indicator (Function.uncurry (IIIa.sepDom 0 0 (transGap ν R) g)) := by
      funext p; by_cases h : p.2 ∈ streamAnn ν R <;>
        simp [transMajW, Set.indicator, Function.uncurry, h]
    rw [this]
    exact (sd_measurable_sepDom 0 0 _ g hgm).indicator (measurable_snd hann)
  have mD : Measurable (Function.uncurry (transMajD ν R g)) := by
    have : Function.uncurry (transMajD ν R g) =
        (Prod.snd ⁻¹' streamAnn ν R).indicator (fun p : ℝ × Space =>
          ENNReal.ofReal (transLen ν R)⁻¹ * (Function.uncurry (IIIa.sepDom 0 1 (transGap ν R) g)) p) := by
      funext p; by_cases h : p.2 ∈ streamAnn ν R <;>
        simp [transMajD, Set.indicator, Function.uncurry, h]
    rw [this]
    exact (measurable_const.mul (sd_measurable_sepDom 0 1 _ g hgm)).indicator (measurable_snd hann)
  have mS : Measurable (Function.uncurry (transMajS ν R g)) := by
    have hm := L223.measurable_outMaj3 0 (transGap ν R) hgm
    have h2 : Measurable (fun p : ℝ × Space => outMaj 0 (transGap ν R) g p.1 (ϱ p.2) (p.2 2)) :=
      hm.comp (measurable_fst.prodMk ((measurable_ϱ.comp measurable_snd).prodMk
        ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd)))
    have : Function.uncurry (transMajS ν R g) =
        (Prod.snd ⁻¹' streamAnn ν R).indicator (fun p : ℝ × Space =>
          ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
            outMaj 0 (transGap ν R) g p.1 (ϱ p.2) (p.2 2)) := by
      funext p; by_cases h : p.2 ∈ streamAnn ν R <;>
        simp [transMajS, Set.indicator, Function.uncurry, h]
    rw [this]
    exact (measurable_const.mul h2).indicator (measurable_snd hann)
  set N := IIIa.ltauLq P (22 / 19) g with hNdef
  set A : ℝ := ν⁻¹ ^ 3 * R ^ (-(35 / 11) : ℝ) with hAdef
  have hA : 0 ≤ A := mul_nonneg (by positivity) (Real.rpow_nonneg hR.le _)
  have bW : IIIa.ltauLq P (22 / 3) (transMajW ν R g) ≤
      ENNReal.ofReal (C0 * (1 - s) ^ (-(35 / 11) : ℝ) * A) * N := by
    refine (IIIa.ltauLq_mono P _ (by norm_num) (fun τ y => ?_)).trans
      ((hy0 _ hDpos).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl))
    · exact Set.indicator_le_self' (fun _ _ => zero_le) y
    · rw [hD, Real.mul_rpow hκ.le hL.le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (PL2.Lpow hν hν1 hR (by norm_num) (by norm_num)) (by positivity)
  have bD : IIIa.ltauLq P (22 / 3) (transMajD ν R g) ≤
      ENNReal.ofReal (C1 * (1 - s) ^ (-(46 / 11) : ℝ) * A) * N := by
    have h1' : transMajD ν R g ≤ fun τ y => ENNReal.ofReal L⁻¹ * IIIa.sepDom 0 1 (transGap ν R) g τ y :=
      fun τ y => by
        simp only [transMajD, transLen, hLdef]
        exact Set.indicator_le_self' (fun _ _ => zero_le) y
    refine (IIIa.ltauLq_mono P _ (by norm_num) h1').trans ?_
    rw [IIIa.ltauLq_const_mul P _ (by norm_num) _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (hy1 _ hDpos)).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hc1 : 0 ≤ C1 * (1 - s) ^ (-(46 / 11) : ℝ) := mul_nonneg hC1 a2
    have e0 : L⁻¹ * L ^ (-(46 / 11) : ℝ) = L ^ (-(57 / 11) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hL]; norm_num
    have e3 := PL2.Lpow hν hν1 hR (e := -(57 / 11)) (by norm_num) (by norm_num)
    have e5 : R ^ (-(57 / 11) : ℝ) ≤ R ^ (-(35 / 11) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
    rw [hD, Real.mul_rpow hκ.le hL.le]
    calc L⁻¹ * (C1 * ((1 - s) ^ (-(46 / 11) : ℝ) * L ^ (-(46 / 11) : ℝ)))
        = C1 * (1 - s) ^ (-(46 / 11) : ℝ) * (L⁻¹ * L ^ (-(46 / 11) : ℝ)) := by ring
      _ = C1 * (1 - s) ^ (-(46 / 11) : ℝ) * L ^ (-(57 / 11) : ℝ) := by rw [e0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (e3.trans (mul_le_mul_of_nonneg_left e5 (by positivity))) hc1
  have bS : IIIa.ltauLq P (22 / 3) (transMajS ν R g) ≤
      ENNReal.ofReal (Cs * A) * N := by
    have hS' : transMajS ν R g = fun τ y => ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
        (streamAnn ν R).indicator
          (fun y => outMaj 0 (transGap ν R) g τ (ϱ y) (y 2)) y := by
      funext τ y
      by_cases hy : y ∈ streamAnn ν R <;> simp [transMajS, Set.indicator, hy]
    rw [hS', IIIa.ltauLq_const_mul P _ (by norm_num) _ ENNReal.ofReal_ne_top]
    have hO := hS ν R P 0 hν hR hP le_rfl g hgm hgp hgs
    refine (mul_le_mul' le_rfl hO).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e1 : (L⁻¹) ^ 2 * L ^ (-(13 / 11) : ℝ) = L ^ (-(35 / 11) : ℝ) := by
      rw [show (L⁻¹) ^ 2 = L ^ (-2 : ℝ) by rw [Real.rpow_neg hL.le, inv_pow]; norm_num,
        ← Real.rpow_add hL]
      norm_num
    have e3 := PL2.Lpow hν hν1 hR (e := -(35 / 11)) (by norm_num) (by norm_num)
    simp only [transLen]
    calc (R * Real.sqrt ν)⁻¹ ^ 2 * (Cs * (R * Real.sqrt ν) ^ (-(13 / 11) : ℝ))
        = Cs * (L⁻¹ ^ 2 * L ^ (-(13 / 11) : ℝ)) := by rw [hLdef]; ring
      _ = Cs * L ^ (-(35 / 11) : ℝ) := by rw [e1]
      _ ≤ _ := mul_le_mul_of_nonneg_left e3 hCs
  have hsum : IIIa.ltauLq P (22 / 3) (transMaj ν R g) ≤
      IIIa.ltauLq P (22 / 3) (transMajW ν R g) + IIIa.ltauLq P (22 / 3) (transMajD ν R g) +
        IIIa.ltauLq P (22 / 3) (transMajS ν R g) := by
    have hWD : Measurable (Function.uncurry (fun τ y => transMajW ν R g τ y + transMajD ν R g τ y)) :=
      mW.add mD
    refine (L223.ltauLq_add_le (P := P) (by norm_num) hWD mS).trans ?_
    exact add_le_add (L223.ltauLq_add_le (by norm_num) mW mD) le_rfl
  refine hsum.trans ((add_le_add (add_le_add bW bD) bS).trans_eq ?_)
  have hna : 0 ≤ C0 * (1 - s) ^ (-(35 / 11) : ℝ) * A := mul_nonneg (mul_nonneg hC0 a1) hA
  have hnb : 0 ≤ C1 * (1 - s) ^ (-(46 / 11) : ℝ) * A := mul_nonneg (mul_nonneg hC1 a2) hA
  have hnc : 0 ≤ Cs * A := mul_nonneg hCs hA
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hna hnb,
    ← ENNReal.ofReal_add (add_nonneg hna hnb) hnc]
  congr 2
  rw [hAdef]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
