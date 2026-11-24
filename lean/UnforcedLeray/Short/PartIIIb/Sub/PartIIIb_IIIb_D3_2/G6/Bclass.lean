import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org

/-!
# `PartIII-b:IIIb-D3/2/G6/3`: `B_{μ,ν}[A] ∈ 𝓑_{a_s}` with `‖B_{μ,ν}[A]‖_{a_s} ≤ C‖A‖_𝒜`

Source of record: `the November 2 reference manuscript`, lines 4755-4760 and
4582-4592.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

open ConcreteYF

private theorem matNorm_zero : matNorm (0 : Mat3) = 0 := by
  unfold matNorm
  simp

private theorem matNorm_le_nine_frob (M : Mat3) : matNorm M ≤ 9 * frob M := by
  unfold matNorm
  calc ∑ i : Fin 3, ∑ j : Fin 3, |M i j|
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, frob M :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_entry_le_frob M i j
    _ = 9 * frob M := by simp; ring

private theorem deriv_apply_eq (F : ℝ → Mat3) (s : ℝ) (i j : Fin 3)
    (hd : DifferentiableAt ℝ F s) :
    deriv F s i j = deriv (fun t => F t i j) s := by
  have h1 : HasDerivAt (fun t => F t i) (deriv F s i) s :=
    (hasDerivAt_pi.1 hd.hasDerivAt) i
  have h2 : HasDerivAt (fun t => F t i j) (deriv F s i j) s :=
    (hasDerivAt_pi.1 h1) j
  exact h2.deriv.symm

private theorem deriv_eq_zero_of_forall_entry_zero (F : ℝ → Mat3) (s : ℝ) (i j : Fin 3)
    (hz : ∀ t, F t i j = 0) : deriv F s i j = 0 := by
  by_cases hd : DifferentiableAt ℝ F s
  · rw [deriv_apply_eq F s i j hd]
    have hfun : (fun t => F t i j) = fun _ => (0 : ℝ) := funext hz
    rw [hfun, deriv_const]
  · rw [deriv_zero_of_not_differentiableAt hd]
    rfl

private theorem deriv_trace_eq_zero (F : ℝ → Mat3) (s : ℝ)
    (htr : ∀ t, F t 0 0 + F t 1 1 + F t 2 2 = 0) :
    deriv F s 0 0 + deriv F s 1 1 + deriv F s 2 2 = 0 := by
  by_cases hd : DifferentiableAt ℝ F s
  · have h0 : HasDerivAt (fun t => F t 0 0) (deriv F s 0 0) s :=
      (hasDerivAt_pi.1 ((hasDerivAt_pi.1 hd.hasDerivAt) 0)) 0
    have h1 : HasDerivAt (fun t => F t 1 1) (deriv F s 1 1) s :=
      (hasDerivAt_pi.1 ((hasDerivAt_pi.1 hd.hasDerivAt) 1)) 1
    have h2 : HasDerivAt (fun t => F t 2 2) (deriv F s 2 2) s :=
      (hasDerivAt_pi.1 ((hasDerivAt_pi.1 hd.hasDerivAt) 2)) 2
    have hsum : HasDerivAt (fun t => F t 0 0 + F t 1 1 + F t 2 2)
        (deriv F s 0 0 + deriv F s 1 1 + deriv F s 2 2) s :=
      (h0.add h1).add h2
    have hfun : (fun t => F t 0 0 + F t 1 1 + F t 2 2) = fun _ => (0 : ℝ) := funext htr
    rw [hfun] at hsum
    exact hsum.unique (hasDerivAt_const s (0 : ℝ))
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

private theorem deriv_eq_zero_of_eq_zero_Iic (F : ℝ → Mat3) (s : ℝ)
    (hz : ∀ t ≤ s, F t = 0) : deriv F s = 0 := by
  by_cases hd : DifferentiableAt ℝ F s
  · have h1 : HasDerivWithinAt F (deriv F s) (Iic s) s := hd.hasDerivAt.hasDerivWithinAt
    have h2 : HasDerivWithinAt F 0 (Iic s) s :=
      (hasDerivWithinAt_const s (Iic s) (0 : Mat3)).congr (fun t ht => hz t ht) (hz s le_rfl)
    exact (h1.derivWithin (uniqueDiffWithinAt_Iic s)).symm.trans
      (h2.derivWithin (uniqueDiffWithinAt_Iic s))
  · exact deriv_zero_of_not_differentiableAt hd

private theorem deriv_eq_zero_of_eq_zero_Ici (F : ℝ → Mat3) (s : ℝ)
    (hz : ∀ t, s ≤ t → F t = 0) : deriv F s = 0 := by
  by_cases hd : DifferentiableAt ℝ F s
  · have h1 : HasDerivWithinAt F (deriv F s) (Ici s) s := hd.hasDerivAt.hasDerivWithinAt
    have h2 : HasDerivWithinAt F 0 (Ici s) s :=
      (hasDerivWithinAt_const s (Ici s) (0 : Mat3)).congr (fun t ht => hz t ht) (hz s le_rfl)
    exact (h1.derivWithin (uniqueDiffWithinAt_Ici s)).symm.trans
      (h2.derivWithin (uniqueDiffWithinAt_Ici s))
  · exact deriv_zero_of_not_differentiableAt hd

private theorem measurable_affElem {as : ℝ} {A : ℝ → Mat3} (hA : IsAffElem as A) :
    Measurable A := by
  classical
  have hpw : A = (Ioi (0 : ℝ)).piecewise A (fun _ => 0) := by
    funext s
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · exact (piecewise_eq_of_mem _ _ _ hs).symm
    · rw [piecewise_eq_of_notMem _ _ _ hs]
      exact hA.zeroOff s (not_lt.1 hs)
  rw [hpw]
  exact hA.smooth.continuousOn.measurable_piecewise continuousOn_const measurableSet_Ioi

private theorem bmat_measurable_entry {as ν μ : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ)
    {A : ℝ → Mat3} (hA : IsAffElem as A) (i j : Fin 3) :
    Measurable (fun s => Bmat ν μ χ A s i j) := by
  have hAm : Measurable A := measurable_affElem hA
  have hAij : Measurable (fun s => A s i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hAm)
  have hχm : Measurable (fun s => χ (ν * s)) :=
    hχ.smooth.continuous.measurable.comp (measurable_const.mul measurable_id)
  have hAyij : Measurable (fun s => Ay ν χ A s i j) := by
    change Measurable (fun s => χ (ν * s) * A s i j)
    exact hχm.mul hAij
  have hd : Measurable (fun s => deriv (Ay ν χ A) s i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_deriv (Ay ν χ A)))
  have hdiv : Measurable (fun s : ℝ => μ / s) := measurable_const.div measurable_id
  change Measurable (fun s => deriv (Ay ν χ A) s i j + (μ / s) * Ay ν χ A s i j)
  exact hd.add (hdiv.mul hAyij)

private theorem ay_traceFree {as : ℝ} (ν : ℝ) (χ : ℝ → ℝ) {A : ℝ → Mat3} (hA : IsAffElem as A)
    (s : ℝ) : Ay ν χ A s 0 0 + Ay ν χ A s 1 1 + Ay ν χ A s 2 2 = 0 := by
  change χ (ν * s) * A s 0 0 + χ (ν * s) * A s 1 1 + χ (ν * s) * A s 2 2 = 0
  have h : A s 0 0 + A s 1 1 + A s 2 2 = 0 := by
    rcases lt_or_ge 0 s with hs | hs
    · exact hA.traceFree s hs
    · simp [hA.zeroOff s hs]
  calc χ (ν * s) * A s 0 0 + χ (ν * s) * A s 1 1 + χ (ν * s) * A s 2 2
      = χ (ν * s) * (A s 0 0 + A s 1 1 + A s 2 2) := by ring
    _ = 0 := by rw [h, mul_zero]

private theorem bmat_traceFree {as : ℝ} (ν μ : ℝ) (χ : ℝ → ℝ) {A : ℝ → Mat3}
    (hA : IsAffElem as A) (s : ℝ) :
    Bmat ν μ χ A s 0 0 + Bmat ν μ χ A s 1 1 + Bmat ν μ χ A s 2 2 = 0 := by
  change (deriv (Ay ν χ A) s 0 0 + (μ / s) * Ay ν χ A s 0 0) +
      (deriv (Ay ν χ A) s 1 1 + (μ / s) * Ay ν χ A s 1 1) +
      (deriv (Ay ν χ A) s 2 2 + (μ / s) * Ay ν χ A s 2 2) = 0
  have hd := deriv_trace_eq_zero (Ay ν χ A) s (ay_traceFree ν χ hA)
  have hay := ay_traceFree ν χ hA s
  calc (deriv (Ay ν χ A) s 0 0 + (μ / s) * Ay ν χ A s 0 0) +
        (deriv (Ay ν χ A) s 1 1 + (μ / s) * Ay ν χ A s 1 1) +
        (deriv (Ay ν χ A) s 2 2 + (μ / s) * Ay ν χ A s 2 2)
      = (deriv (Ay ν χ A) s 0 0 + deriv (Ay ν χ A) s 1 1 + deriv (Ay ν χ A) s 2 2) +
          (μ / s) * (Ay ν χ A s 0 0 + Ay ν χ A s 1 1 + Ay ν χ A s 2 2) := by ring
    _ = 0 := by rw [hd, hay, mul_zero, add_zero]

private theorem bmat_entry_zero_of_forall {ν μ : ℝ} {χ : ℝ → ℝ} {A : ℝ → Mat3} {i j : Fin 3}
    (h : ∀ s, A s i j = 0) (s : ℝ) : Bmat ν μ χ A s i j = 0 := by
  have hay : ∀ t, Ay ν χ A t i j = 0 := fun t => by
    change χ (ν * t) * A t i j = 0
    rw [h t, mul_zero]
  have hd := deriv_eq_zero_of_forall_entry_zero (Ay ν χ A) s i j hay
  change deriv (Ay ν χ A) s i j + (μ / s) * Ay ν χ A s i j = 0
  rw [hd, hay s, mul_zero, add_zero]

private theorem bmat_noMixedAzimuth {as : ℝ} (ν μ : ℝ) (χ : ℝ → ℝ) {A : ℝ → Mat3}
    (hA : IsAffElem as A) (s : ℝ) :
    Bmat ν μ χ A s 0 1 = 0 ∧ Bmat ν μ χ A s 1 0 = 0 ∧
      Bmat ν μ χ A s 1 2 = 0 ∧ Bmat ν μ χ A s 2 1 = 0 := by
  have h01 : ∀ t, A t 0 1 = 0 := fun t => by
    rcases lt_or_ge 0 t with ht | ht
    · exact (hA.noMixedAzimuth t ht).1
    · simp [hA.zeroOff t ht]
  have h10 : ∀ t, A t 1 0 = 0 := fun t => by
    rcases lt_or_ge 0 t with ht | ht
    · exact (hA.noMixedAzimuth t ht).2.1
    · simp [hA.zeroOff t ht]
  have h12 : ∀ t, A t 1 2 = 0 := fun t => by
    rcases lt_or_ge 0 t with ht | ht
    · exact (hA.noMixedAzimuth t ht).2.2.1
    · simp [hA.zeroOff t ht]
  have h21 : ∀ t, A t 2 1 = 0 := fun t => by
    rcases lt_or_ge 0 t with ht | ht
    · exact (hA.noMixedAzimuth t ht).2.2.2
    · simp [hA.zeroOff t ht]
  exact ⟨bmat_entry_zero_of_forall h01 s, bmat_entry_zero_of_forall h10 s,
    bmat_entry_zero_of_forall h12 s, bmat_entry_zero_of_forall h21 s⟩

private theorem bmat_support_outside {as ν μ : ℝ} {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ)
    (hν : 0 < ν) {A : ℝ → Mat3} (hA : IsAffElem as A) (s : ℝ)
    (hs : s ∉ Ioo 0 (1.1 / ν)) : Bmat ν μ χ A s = 0 := by
  by_cases hs0 : s ≤ 0
  · have hay : ∀ t ≤ s, Ay ν χ A t = 0 := fun t ht => by
      unfold Ay
      rw [hA.zeroOff t (ht.trans hs0), smul_zero]
    have hd : deriv (Ay ν χ A) s = 0 := deriv_eq_zero_of_eq_zero_Iic (Ay ν χ A) s hay
    unfold Bmat
    rw [hd, hay s le_rfl, smul_zero, add_zero]
  · have hs_pos : 0 < s := not_le.1 hs0
    have hs_ge : 1.1 / ν ≤ s := by
      by_contra hlt
      exact hs ⟨hs_pos, not_le.1 hlt⟩
    have hay : ∀ t, s ≤ t → Ay ν χ A t = 0 := fun t ht => by
      have h11 : 11 / 10 ≤ ν * t := by
        have hge : (11 / 10 : ℝ) / ν ≤ t := by
          calc (11 / 10 : ℝ) / ν = 1.1 / ν := by norm_num
            _ ≤ s := hs_ge
            _ ≤ t := ht
        have := (div_le_iff₀ hν).1 hge
        linarith [mul_comm ν t]
      unfold Ay
      rw [hχ.zero (ν * t) h11, zero_smul]
    have hd : deriv (Ay ν χ A) s = 0 := deriv_eq_zero_of_eq_zero_Ici (Ay ν χ A) s hay
    unfold Bmat
    rw [hd, hay s le_rfl, smul_zero, add_zero]

/-- `PartIII-b:IIIb-D3/2/G6/3`: `B_{μ,ν}[A] ∈ 𝓑_{a_s}` with `‖B_{μ,ν}[A]‖_{a_s} ≤ C‖A‖_𝒜`. -/
theorem bmatBclass : FlatUnif.G6.BmatBclass := by
  intro χ hχ as
  obtain ⟨C0, hC0, hpt⟩ := bmat_pointwise hχ
  refine ⟨18 * C0, by positivity, ?_⟩
  intro ν μ hν hμ0 hμ1 A
  have hA : IsAffElem as (affIota as A) := affIota_mem as A
  have hCb_nn : 0 ≤ (18 * C0) * ‖A‖ := mul_nonneg (by positivity) (norm_nonneg A)
  have hbound : ∀ s : ℝ, 0 < s →
      Real.exp (-as * s) * s ^ (-(3 / 2 : ℝ)) * matNorm (Bmat ν μ χ (affIota as A) s) ≤
        (18 * C0) * ‖A‖ := by
    intro s hs
    by_cases hsT : s ≤ (11 / 10) / ν
    · have hfrob := hpt as ν μ (affIota as A) hν hμ0 hA s hs hsT
      rw [affNorm_affIota] at hfrob
      have hm := (matNorm_le_nine_frob (Bmat ν μ χ (affIota as A) s)).trans
        (mul_le_mul_of_nonneg_left hfrob (by norm_num))
      have hμ2 : 1 + μ ≤ 2 := by linarith
      have hpos_w : 0 ≤ (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖ :=
        mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hs _).le (Real.exp_pos _).le) (norm_nonneg A)
      have hm2 : matNorm (Bmat ν μ χ (affIota as A) s) ≤
          18 * C0 * (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖ := by
        calc matNorm (Bmat ν μ χ (affIota as A) s)
            ≤ 9 * ((1 + μ) * C0 * (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖) := hm
          _ = 9 * (1 + μ) * C0 * ((s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖) := by ring
          _ ≤ 9 * 2 * C0 * ((s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖) := by
              apply mul_le_mul_of_nonneg_right _ hpos_w
              apply mul_le_mul_of_nonneg_right _ hC0
              linarith
          _ = 18 * C0 * (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖ := by ring
      have hw_nn : 0 ≤ Real.exp (-as * s) * s ^ (-(3 / 2 : ℝ)) :=
        mul_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hs _).le
      have hexp : Real.exp (-as * s) * Real.exp (as * s) = 1 := by
        rw [← Real.exp_add, show -as * s + as * s = 0 by ring, Real.exp_zero]
      have hrpow : s ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hs, show -(3 / 2 : ℝ) + 3 / 2 = 0 by ring, Real.rpow_zero]
      calc Real.exp (-as * s) * s ^ (-(3 / 2 : ℝ)) * matNorm (Bmat ν μ χ (affIota as A) s)
          ≤ Real.exp (-as * s) * s ^ (-(3 / 2 : ℝ)) *
              (18 * C0 * (s ^ (3 / 2 : ℝ) * Real.exp (as * s)) * ‖A‖) :=
            mul_le_mul_of_nonneg_left hm2 hw_nn
        _ = (Real.exp (-as * s) * Real.exp (as * s)) *
              (s ^ (-(3 / 2 : ℝ)) * s ^ (3 / 2 : ℝ)) * ((18 * C0) * ‖A‖) := by ring
        _ = (18 * C0) * ‖A‖ := by rw [hexp, hrpow]; ring
    · have hnot : s ∉ Ioo 0 (1.1 / ν) := by
        intro hmem
        apply hsT
        calc s ≤ 1.1 / ν := hmem.2.le
          _ = (11 / 10) / ν := by norm_num
      rw [bmat_support_outside hχ hν hA s hnot, matNorm_zero, mul_zero]
      exact hCb_nn
  have hess : essSup (fun s => ENNReal.ofReal
      (Real.exp (-as * s) * s ^ (-(3 / 2 : ℝ)) * matNorm (Bmat ν μ χ (affIota as A) s)))
      (volume.restrict (Ioi 0)) ≤ ENNReal.ofReal ((18 * C0) * ‖A‖) := by
    refine essSup_le_of_ae_le _ ?_
    apply (ae_restrict_iff' measurableSet_Ioi).2
    exact Filter.Eventually.of_forall fun s hs => ENNReal.ofReal_le_ofReal (hbound s hs)
  unfold IsBclass bNorm
  refine ⟨⟨fun i j => bmat_measurable_entry hχ hA i j, bmat_traceFree ν μ χ hA,
    bmat_noMixedAzimuth ν μ χ hA, bmat_support_outside hχ hν hA,
    lt_of_le_of_lt hess ENNReal.ofReal_lt_top⟩,
    ENNReal.toReal_le_of_le_ofReal hCb_nn hess⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
