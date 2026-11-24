import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.PointL2.Out
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T17

/-!
# `PartIII-b:C/rep/4/4/1/org/3/1`: the pointwise exponent `79/22` of the transition majorant

Source `the November 2 reference manuscript` 3647 (`sep:young`, pointwise, `p = 22/19`,
`b = 22/3`), 5337-5341, 4176-4194.  Order zero and one: `IIIa.sepDomPointwise` at gap
`D = (1-√(5/6))R√ν`.  Primitive: Minkowski in `ρ` (`PL2.outMaj_ltauAt_le`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PL2

theorem Lpow {ν R : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hR : 0 < R) {e : ℝ} (_he0 : e ≤ 0)
    (he6 : -6 ≤ e) : (R * Real.sqrt ν) ^ e ≤ ν⁻¹ ^ 3 * R ^ e := by
  rw [Real.mul_rpow hR.le (Real.sqrt_nonneg _), mul_comm, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hν.le]
  have h1 : ν ^ (1 / 2 * e) ≤ ν ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
  have h2 : ν ^ (-3 : ℝ) = ν⁻¹ ^ 3 := by
    rw [Real.rpow_neg hν.le, inv_pow]; norm_num
  rw [h2] at h1
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hR.le _)

theorem measurable_outMaj (D : ℝ) {g : ℝ → Space → ℝ≥0∞} (hg : Measurable (Function.uncurry g))
    (r z : ℝ) : Measurable (fun τ => outMaj 0 D g τ r z) := by
  unfold outMaj
  have h1 : Measurable (Function.uncurry (IIIa.sepDom 0 0 D g)) := sd_measurable_sepDom 0 0 D g hg
  have h2 : Measurable (fun p : ℝ × ℝ => (p.1, (!₂[p.2, 0, z] : Space))) :=
    measurable_fst.prodMk ((measurable_halfline z).comp measurable_snd)
  have h3 : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.2 * (Function.uncurry (IIIa.sepDom 0 0 D g)) (p.1, (!₂[p.2, 0, z] : Space))) :=
    (ENNReal.measurable_ofReal.comp measurable_snd).mul (h1.comp h2)
  exact h3.lintegral_prod_right' (ν := volume.restrict (Ioi r))

end PL2

/-- **The pointwise exponent `79/22` for the transition majorant** (source 3647, 5337-5341). -/
theorem transMajPointL2 : TransMajPointL2 := by
  obtain ⟨C0, hC0, h0⟩ := IIIa.sepDomPointwise 0 (22 / 19) (22 / 3) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C1, hC1, h1⟩ := IIIa.sepDomPointwise 1 (22 / 19) (22 / 3) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨s, hs0, hs1, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ s = Real.sqrt (5 / 6) := by
    refine ⟨_, Real.sqrt_nonneg _, ?_, rfl⟩
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hκ : 0 < 1 - s := by linarith
  refine ⟨C0 * (1 - s) ^ (-(79 / 22) : ℝ) + C1 * (1 - s) ^ (-(101 / 22) : ℝ) +
      C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (22 / 35), 3, ?_, ?_⟩
  · have a1 := Real.rpow_nonneg hκ.le (-(79 / 22) : ℝ)
    have a2 := Real.rpow_nonneg hκ.le (-(101 / 22) : ℝ)
    positivity
  intro ν R P hν hν1 hR1 hP g hgm hgp hgs y
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  by_cases hy : y ∈ streamAnn ν R
  swap
  · have : (fun τ => transMaj ν R g τ y) = fun _ => 0 := by
      funext τ
      simp [transMaj, transMajW, transMajD, transMajS, Set.indicator, hy]
    rw [this]
    simp [IIIa.ltauAt]
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  set L : ℝ := R * Real.sqrt ν with hLdef
  have hL : 0 < L := mul_pos hR hsq
  have hyL : L ≤ ϱ y := hy.1
  have hro : R * Real.sqrt (5 * ν / 6) = s * L := by
    rw [hLdef, hs, show 5 * ν / 6 = 5 / 6 * ν by ring, Real.sqrt_mul (by norm_num)]; ring
  have hgs' : ∀ τ (z : Space), s * L < ϱ z → g τ z = 0 := by
    intro τ z hz; exact hgs τ z (by rw [hro]; exact hz)
  have hD : transGap ν R = (1 - s) * L := by
    unfold transGap; rw [hro]; ring
  have hDpos : 0 < transGap ν R := by rw [hD]; positivity
  have hpt0 : ∀ D' : ℝ, 0 < D' → ∀ y : Space,
      IIIa.ltauAt P (fun τ => IIIa.sepDom 0 0 D' g τ y) ≤
        ENNReal.ofReal (C0 * D' ^ (-(79 / 22) : ℝ)) * IIIa.ltauLq P (22 / 19) g := by
    intro D' hD' y'
    have := h0 0 le_rfl (by norm_num) D' P hD' hP g hgm hgp y'
    have e : (-4 - ((0 : ℕ) : ℝ) + 3 / (22 / 3) : ℝ) = -(79 / 22) := by norm_num
    rw [e] at this
    exact this
  have hpt1 : ∀ D' : ℝ, 0 < D' → ∀ y : Space,
      IIIa.ltauAt P (fun τ => IIIa.sepDom 0 1 D' g τ y) ≤
        ENNReal.ofReal (C1 * D' ^ (-(101 / 22) : ℝ)) * IIIa.ltauLq P (22 / 19) g := by
    intro D' hD' y'
    have := h1 0 le_rfl (by norm_num) D' P hD' hP g hgm hgp y'
    have e : (-4 - ((1 : ℕ) : ℝ) + 3 / (22 / 3) : ℝ) = -(101 / 22) := by norm_num
    rw [e] at this
    exact this
  have eW : ∀ τ, transMajW ν R g τ y = IIIa.sepDom 0 0 (transGap ν R) g τ y := fun τ => by
    simp [transMajW, Set.indicator_of_mem hy]
  have eD : ∀ τ, transMajD ν R g τ y =
      ENNReal.ofReal L⁻¹ * IIIa.sepDom 0 1 (transGap ν R) g τ y := fun τ => by
    simp [transMajD, Set.indicator_of_mem hy, transLen, hLdef]
  have eS : ∀ τ, transMajS ν R g τ y =
      ENNReal.ofReal (L⁻¹ ^ 2) * outMaj 0 (transGap ν R) g τ (ϱ y) (y 2) := fun τ => by
    simp [transMajS, Set.indicator_of_mem hy, transLen, hLdef]
  have mW : Measurable (fun τ => transMajW ν R g τ y) := by
    simp_rw [eW]
    exact PmStep.slice_meas (f := IIIa.sepDom 0 0 (transGap ν R) g)
      (sd_measurable_sepDom 0 0 _ g hgm) y
  have mD : Measurable (fun τ => transMajD ν R g τ y) := by
    simp_rw [eD]
    exact measurable_const.mul (PmStep.slice_meas (f := IIIa.sepDom 0 1 (transGap ν R) g)
      (sd_measurable_sepDom 0 1 _ g hgm) y)
  have mS : Measurable (fun τ => transMajS ν R g τ y) := by
    simp_rw [eS]
    exact measurable_const.mul (PL2.measurable_outMaj _ hgm _ _)
  -- the three pieces
  have bW : IIIa.ltauAt P (fun τ => transMajW ν R g τ y) ≤
      ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ))) *
        IIIa.ltauLq P (22 / 19) g := by
    simp_rw [eW]
    refine (hpt0 _ hDpos y).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [hD, Real.mul_rpow hκ.le hL.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (PL2.Lpow hν hν1 hR (by norm_num) (by norm_num)) (by positivity)
  have hA : 0 ≤ ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hR.le _)
  have a1 := Real.rpow_nonneg hκ.le (-(79 / 22) : ℝ)
  have a2 := Real.rpow_nonneg hκ.le (-(101 / 22) : ℝ)
  have bD : IIIa.ltauAt P (fun τ => transMajD ν R g τ y) ≤
      ENNReal.ofReal (C1 * (1 - s) ^ (-(101 / 22) : ℝ) * (ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ))) *
        IIIa.ltauLq P (22 / 19) g := by
    simp_rw [eD]
    rw [IIIa.ltauAt_const_mul P _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (hpt1 _ hDpos y)).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hc1 : 0 ≤ C1 * (1 - s) ^ (-(101 / 22) : ℝ) := mul_nonneg hC1 a2
    have e0 : L⁻¹ * L ^ (-(101 / 22) : ℝ) = L ^ (-(123 / 22) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hL]; norm_num
    have e3 := PL2.Lpow hν hν1 hR (e := -(123 / 22)) (by norm_num) (by norm_num)
    have e5 : R ^ (-(123 / 22) : ℝ) ≤ R ^ (-(79 / 22) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
    rw [hD, Real.mul_rpow hκ.le hL.le]
    calc L⁻¹ * (C1 * ((1 - s) ^ (-(101 / 22) : ℝ) * L ^ (-(101 / 22) : ℝ)))
        = C1 * (1 - s) ^ (-(101 / 22) : ℝ) * (L⁻¹ * L ^ (-(101 / 22) : ℝ)) := by ring
      _ = C1 * (1 - s) ^ (-(101 / 22) : ℝ) * L ^ (-(123 / 22) : ℝ) := by rw [e0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (e3.trans (mul_le_mul_of_nonneg_left e5 (by positivity))) hc1
  have bS : IIIa.ltauAt P (fun τ => transMajS ν R g τ y) ≤
      ENNReal.ofReal (C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (22 / 35) *
        (ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ))) * IIIa.ltauLq P (22 / 19) g := by
    simp_rw [eS]
    rw [IIIa.ltauAt_const_mul P _ ENNReal.ofReal_ne_top]
    have hO := PL2.outMaj_ltauAt_le (N := IIIa.ltauLq P (22 / 19) g) hs0 hs1 hL hD hyL hP hC0
      g hgm hgs' hpt0 (y 2)
    refine (mul_le_mul' le_rfl hO).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e1 : L⁻¹ ^ 2 * L ^ (-(35 / 22) : ℝ) = L ^ (-(79 / 22) : ℝ) := by
      rw [show L⁻¹ ^ 2 = L ^ (-2 : ℝ) by rw [Real.rpow_neg hL.le, inv_pow]; norm_num,
        ← Real.rpow_add hL]
      norm_num
    have e2 : ϱ y ^ (-(35 / 22) : ℝ) ≤ L ^ (-(35 / 22) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hL hyL (by norm_num)
    have e3 := PL2.Lpow hν hν1 hR (e := -(79 / 22)) (by norm_num) (by norm_num)
    have e4 : L⁻¹ ^ 2 * ϱ y ^ (-(35 / 22) : ℝ) ≤ ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ) := by
      calc L⁻¹ ^ 2 * ϱ y ^ (-(35 / 22) : ℝ) ≤ L⁻¹ ^ 2 * L ^ (-(35 / 22) : ℝ) :=
            mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = L ^ (-(79 / 22) : ℝ) := e1
        _ ≤ _ := e3
    have hc : 0 ≤ C0 * (1 - s) ^ (-(79 / 22) : ℝ) := mul_nonneg hC0 a1
    calc L⁻¹ ^ 2 * (C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (22 / 35 * ϱ y ^ (-(35 / 22) : ℝ)))
        = C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (22 / 35) *
            (L⁻¹ ^ 2 * ϱ y ^ (-(35 / 22) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
  have hsum : IIIa.ltauAt P (fun τ => transMaj ν R g τ y) ≤
      IIIa.ltauAt P (fun τ => transMajW ν R g τ y) + IIIa.ltauAt P (fun τ => transMajD ν R g τ y) +
        IIIa.ltauAt P (fun τ => transMajS ν R g τ y) := by
    show IIIa.ltauAt P (fun τ => (transMajW ν R g τ y + transMajD ν R g τ y) +
      transMajS ν R g τ y) ≤ _
    refine (IIIa.ltauAt_add_le P (mW.add mD) mS).trans ?_
    exact add_le_add (IIIa.ltauAt_add_le P mW mD) le_rfl
  refine hsum.trans ((add_le_add (add_le_add bW bD) bS).trans_eq ?_)
  have hna : 0 ≤ C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ)) :=
    mul_nonneg (mul_nonneg hC0 a1) hA
  have hnb : 0 ≤ C1 * (1 - s) ^ (-(101 / 22) : ℝ) * (ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ)) :=
    mul_nonneg (mul_nonneg hC1 a2) hA
  have hnc : 0 ≤ C0 * (1 - s) ^ (-(79 / 22) : ℝ) * (22 / 35) *
      (ν⁻¹ ^ 3 * R ^ (-(79 / 22) : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 a1) (by norm_num)) hA
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hna hnb,
    ← ENNReal.ofReal_add (add_nonneg hna hnb) hnc]
  congr 2
  ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
