import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.EFar

/-!
# Order-4 far-field homogeneity of the inlet column (`PartIII-b:C/ward/12/3/2/2/2/3`,
target `inletEFarHom4 : InletEFarHom4`)

Source `the November 2 reference manuscript`,
lines 2542-2549 (complete sources, unprojected derivatives) and 1206-1222 (ring lift).

Order-4 analogue of `inletEFarHom` (`EFar.lean`), extending `chartJetBound` (`ChartJet.lean`) and
`chartLiftJets` (`ChartLift.lean`) to derivative orders `≤ 4` and applying `inletJetAll` at `j = 4`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Order-4 analogue of `chartJetBound` (`ChartJet.lean:43`). -/
theorem chartJetBound4 (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y →
      ∀ m : ℕ, 1 ≤ m → m ≤ 4 →
        ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
  have key : ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤
        C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
    intro m hm
    obtain ⟨Ca, hCa0, hCa⟩ := ageJet R hR m hm
    obtain ⟨Cp, hCp0, hCp⟩ := phaseJet R hR m hm
    obtain ⟨Ct, hCt0, hCt⟩ := transJet R hR m
    have hL1 : 0 ≤ ‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg hCa0 (inv_nonneg.2 (sq_nonneg R)))
    have hL2 : 0 ≤ ‖chartJetL2‖ * Cp := mul_nonneg (norm_nonneg _) hCp0
    have hL3 : 0 ≤ ‖chartJetL3‖ * Ct := mul_nonneg (norm_nonneg _) hCt0
    refine ⟨‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct,
      add_nonneg (add_nonneg hL1 hL2) hL3, ?_⟩
    intro τ y hy
    have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
    have hyax : y ∉ Axi.axis := by
      intro h
      rw [Axi.mem_axis_iff] at h
      linarith
    have hU : IsOpen (Axi.axisᶜ : Set UnforcedLeray.Space) := Axi.isOpen_compl_axis
    have hmem : (Axi.axisᶜ : Set UnforcedLeray.Space) ∈ nhds y := hU.mem_nhds hyax
    have hAgeS : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => R ^ 2 / Axi.ϱ z ^ 2) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
        (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hLogS : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => Real.log (Axi.age R z)) Axi.axisᶜ :=
      ContDiffOn.log hAgeS (fun z hz => (Axi.age_pos hR.ne' hz).ne')
    have hPhaseS : ContDiffOn ℝ ∞
        (fun z : UnforcedLeray.Space => R * τ / 2 - (R / 2) * Real.log (Axi.age R z)) Axi.axisᶜ :=
      contDiffOn_const.sub (contDiffOn_const.mul hLogS)
    have hTransS : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Space => R * z 2 / Axi.ϱ z) Axi.axisᶜ :=
      ((show ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => R * z 2) by fun_prop).contDiffOn).div
        Axi.contDiffOn_ϱ (fun z hz => Axi.ϱ_ne_zero hz)
    have hAgeA : ContDiffAt ℝ ∞ (Axi.age R) y := hAgeS.contDiffAt hmem
    have hPhaseA : ContDiffAt ℝ ∞ (Axi.phase R τ) y := hPhaseS.contDiffAt hmem
    have hTransA : ContDiffAt ℝ ∞ (Axi.trans R) y := hTransS.contDiffAt hmem
    have hm' : (m : WithTop ℕ∞) ≤ ∞ := hjLe m
    have hA : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R) y := chartJetL1.contDiff.comp_contDiffAt y hAgeA
    have hB : ContDiffAt ℝ ∞ (chartJetL2 ∘ Axi.phase R τ) y :=
      chartJetL2.contDiff.comp_contDiffAt y hPhaseA
    have hC : ContDiffAt ℝ ∞ (chartJetL3 ∘ Axi.trans R) y :=
      chartJetL3.contDiff.comp_contDiffAt y hTransA
    have hAB : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R + chartJetL2 ∘ Axi.phase R τ) y := hA.add hB
    have hDA : ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ ≤
        ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ)))) :=
      le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL1 hAgeA hm')
        (mul_le_mul_of_nonneg_left (hCa y hyax) (norm_nonneg _))
    have hDB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
        ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ))) :=
      le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL2 hPhaseA hm')
        (mul_le_mul_of_nonneg_left (hCp τ y hyax) (norm_nonneg _))
    have hDC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
        ‖chartJetL3‖ * (Ct * Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
      le_trans (ContinuousLinearMap.norm_iteratedFDeriv_comp_left chartJetL3 hTransA hm')
        (mul_le_mul_of_nonneg_left (hCt y hyax) (norm_nonneg _))
    have hq0 : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) := Real.rpow_nonneg hp.le _
    have hs0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
    have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
    have hage : Axi.ϱ y ^ (-(2 + (m : ℝ))) ≤ (R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) := by
      have e : -(2 + (m : ℝ)) = -(m : ℝ) + -2 := by ring
      have h2 : Axi.ϱ y ^ (-2 : ℝ) = (Axi.ϱ y ^ 2)⁻¹ := by
        rw [Real.rpow_neg hp.le, Real.rpow_two]
      have hinv : (Axi.ϱ y ^ 2)⁻¹ ≤ (R ^ 2)⁻¹ :=
        inv_anti₀ (pow_pos hR 2) (by nlinarith [mul_nonneg (sub_nonneg.2 hy) (add_nonneg hR.le hp.le)])
      rw [e, Real.rpow_add hp, h2]
      calc Axi.ϱ y ^ (-(m : ℝ)) * (Axi.ϱ y ^ 2)⁻¹ = (Axi.ϱ y ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) :=
            mul_comm _ _
        _ ≤ (R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)) := mul_le_mul_of_nonneg_right hinv hq0
    have eA : ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ ≤
        (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
          (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDA ?_
      calc ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ))))
          ≤ ‖chartJetL1‖ * (Ca * ((R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hage hCa0) (norm_nonneg _)
        _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
        _ ≤ (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq0 hs1) hL1
    have eB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
        (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDB ?_
      calc ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ)))
          = (‖chartJetL2‖ * Cp) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
        _ ≤ (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq0 hs1) hL2
    have eC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
        (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDC (le_of_eq ?_)
      ring
    rw [chartJet_decomp R τ, iteratedFDeriv_add_apply (hAB.of_le hm') (hC.of_le hm'),
      iteratedFDeriv_add_apply (hA.of_le hm') (hB.of_le hm')]
    calc ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
            iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y +
          iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖
        ≤ ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
            iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ +
          ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ := norm_add_le _ _
      _ ≤ (‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ +
            ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖) +
          ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ :=
            add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) +
          (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y))) +
          (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            add_le_add (add_le_add eA eB) eC
      _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by ring
  obtain ⟨C1, hC10, hC1⟩ := key 1 le_rfl
  obtain ⟨C2, hC20, hC2⟩ := key 2 (by norm_num)
  obtain ⟨C3, hC30, hC3⟩ := key 3 (by norm_num)
  obtain ⟨C4, hC40, hC4⟩ := key 4 (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + C1 + C2 + C3 + C4 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by linarith
  refine ⟨K, by linarith, fun τ y hy m hm1 hm4 => ?_⟩
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have hs0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hq0 : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) := Real.rpow_nonneg hp.le _
  have hqs : 0 ≤ Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y) :=
    mul_nonneg hq0 (by linarith)
  have hfin : ∀ C : ℝ, C ≤ K →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤
        (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
    intro C hCK hb
    have hq' : Axi.ϱ y ^ (-(m : ℝ)) = (Axi.ϱ y ^ m)⁻¹ := by
      rw [Real.rpow_neg hp.le, Real.rpow_natCast]
    have hKm : K ≤ K ^ m := le_self_pow₀ hK1 (by omega)
    have hsm : 1 + |y 2| / Axi.ϱ y ≤ (1 + |y 2| / Axi.ϱ y) ^ m := le_self_pow₀ hs1 (by omega)
    have hKnn : 0 ≤ K ^ m := pow_nonneg (by linarith) m
    have hinv : 0 ≤ (Axi.ϱ y ^ m)⁻¹ := inv_nonneg.2 (pow_nonneg hp.le m)
    calc ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖
        ≤ C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := hb
      _ ≤ K * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
          mul_le_mul_of_nonneg_right hCK hqs
      _ = K * ((Axi.ϱ y ^ m)⁻¹ * (1 + |y 2| / Axi.ϱ y)) := by rw [hq']
      _ ≤ K ^ m * ((Axi.ϱ y ^ m)⁻¹ * (1 + |y 2| / Axi.ϱ y) ^ m) :=
          mul_le_mul hKm (mul_le_mul_of_nonneg_left hsm hinv) (mul_nonneg hinv (by linarith)) hKnn
      _ = (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
          rw [div_pow, mul_pow]
          ring
  interval_cases m
  · exact hfin C1 (by linarith) (hC1 τ y hy)
  · exact hfin C2 (by linarith) (hC2 τ y hy)
  · exact hfin C3 (by linarith) (hC3 τ y hy)
  · exact hfin C4 (by linarith) (hC4 τ y hy)

theorem clf_choose_fact4 (k i : ℕ) (hk : k ≤ 4) (hi : i ≤ k) :
    k.choose i * (k - i).factorial ≤ 48 := by
  interval_cases k <;> interval_cases i <;> first | decide | norm_num [Nat.choose, Nat.factorial]

/-- Faà di Bruno for `b ∘ chart` on the axis complement, orders `j ≤ 4`. -/
theorem clf_comp_jet4 (R : ℝ) (hR : 0 < R) (K : ℝ)
    (hKb : ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y →
      ∀ m : ℕ, 1 ≤ m → m ≤ 4 →
        ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m)
    (b : ℝ × (ℝ × ℝ) → Axi.Merid) (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (τ : ℝ) (y : UnforcedLeray.Space) (hy : R ≤ Axi.ϱ y) (j : ℕ) (hj : j ≤ 4) (C : ℝ)
    (hC : ∀ l : ℕ, l ≤ j → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ j (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (j.factorial : ℝ) * C * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ j := by
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hT : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} := isOpen_lt continuous_const continuous_fst
  have hmaps := clf_chart_mapsTo R τ hR
  have hxT : Axi.chart R τ y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hmaps hyS
  have hCb : ∀ i : ℕ, i ≤ j →
      ‖iteratedFDerivWithin ℝ i b {m : ℝ × (ℝ × ℝ) | 0 < m.1} (Axi.chart R τ y)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hT hxT]
    exact hC i hi
  have hDb : ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖ ≤
        (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ i := by
    intro i h1 hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i Axi.isOpen_compl_axis hyS]
    exact hKb τ y hy i h1 (le_trans hi hj)
  exact norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (N := ∞) hb (clf_chart_contDiffOn R τ hR)
    (hjLe j) hT.uniqueDiffOn Axi.isOpen_compl_axis.uniqueDiffOn hmaps hyS hCb hDb

/-- Order-4 analogue of `chartLiftJets` (`ChartLift.lean:123`). -/
theorem chartLiftJets4 (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid),
      ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
      ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y → ∀ k : ℕ, k ≤ 4 →
        ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖ ≤
          K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
            ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
  obtain ⟨K, hK0, hKb⟩ := chartJetBound4 R hR
  have hLF : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ m (liftFactor R) y‖ ≤ C * Axi.ϱ y ^ (-(1 + (m : ℝ))) :=
    fun m => liftFactorJet R hR m
  choose Cf hCf0 hCf using hLF
  set A : ℝ := ∑ i ∈ Finset.range 5, Cf i with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => hCf0 i)
  refine ⟨(1 + 48 * A) * (1 + K) ^ 4, mul_pos (by linarith) (pow_pos (by linarith) 4), ?_⟩
  intro b hb τ y hy k hk
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (clf_chart_contDiffOn R τ hR) (clf_chart_mapsTo R τ hR)
  set Sb : ℝ := ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ with hSbdef
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hCbk : ∀ l : ℕ, l ≤ k → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ Sb := fun l hl =>
    Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have hGj : ∀ j : ℕ, j ≤ k → ‖iteratedFDerivWithin ℝ j (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (j.factorial : ℝ) * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ j := fun j hj =>
    clf_comp_jet4 R hR K hKb b hb τ y hy j (by omega) Sb (fun l hl => hCbk l (le_trans hl hj))
  have hFi : ∀ i ∈ Finset.range (k + 1),
      ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ ≤ Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ))) := by
    intro i _
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := liftFactor R) i Axi.isOpen_compl_axis hyS]
    exact hCf i y hyax
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (1 + K) ^ 4 * (1 + |y 2| / Axi.ϱ y) ^ k *
      (Axi.ϱ y ^ (1 + k))⁻¹ * Sb := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ (Axi.ϱ y ^ (1 + k))⁻¹ := inv_nonneg.2 (pow_nonneg hp.le _)
    positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
        ≤ (48 * Cf i) * M := by
    intro i hi
    have hik : i ≤ k := by have := Finset.mem_range.1 hi; omega
    have h1 := hFi i hi
    have h2 := hGj (k - i) (by omega)
    have hc0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
    have hcf := hCf0 i
    have hcj : (k.choose i : ℝ) * ((k - i).factorial : ℝ) ≤ 48 := by
      exact_mod_cast clf_choose_fact4 k i hk hik
    have hj4 : k - i ≤ 4 := by omega
    have hjk : k - i ≤ k := by omega
    have hrp : 0 ≤ Axi.ϱ y ^ (-(1 + (i : ℝ))) := Real.rpow_nonneg hp.le _
    have hs0 : 0 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
    have hstep1 : (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
        (k.choose i : ℝ) * (Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ)))) *
          ((k - i).factorial * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ (k - i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _)
        (mul_nonneg hc0 (mul_nonneg hcf hrp))
    have hid : (k.choose i : ℝ) * (Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ)))) *
          ((k - i).factorial * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ (k - i)) =
        ((k.choose i : ℝ) * ((k - i).factorial : ℝ)) * Cf i * Sb *
          (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) * ((Axi.ϱ y ^ (1 + i))⁻¹ * (Axi.ϱ y ^ (k - i))⁻¹) := by
      rw [clf_rpow _ hp.le i, div_pow]
      ring
    have hinv : (Axi.ϱ y ^ (1 + i))⁻¹ * (Axi.ϱ y ^ (k - i))⁻¹ = (Axi.ϱ y ^ (1 + k))⁻¹ :=
      clf_inv_mul _ i (k - i) k (by omega)
    have hKs : (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) ≤ (1 + K) ^ 4 * (1 + |y 2| / Axi.ϱ y) ^ k := by
      rw [mul_pow]
      have hKj : K ^ (k - i) ≤ (1 + K) ^ 4 :=
        le_trans (pow_le_pow_left₀ hK0.le (by linarith : K ≤ 1 + K) (k - i))
          (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + K) hj4)
      have hsj : (1 + |y 2| / Axi.ϱ y) ^ (k - i) ≤ (1 + |y 2| / Axi.ϱ y) ^ k :=
        pow_le_pow_right₀ hs1 hjk
      exact mul_le_mul hKj hsj (pow_nonneg hs0 _) (by positivity)
    have hW0 : 0 ≤ Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹ := by
      have : 0 ≤ (Axi.ϱ y ^ (1 + k))⁻¹ := inv_nonneg.2 (pow_nonneg hp.le _)
      exact mul_nonneg (mul_nonneg hcf hSb0) this
    have hKs0 : 0 ≤ (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) :=
      pow_nonneg (mul_nonneg hK0.le hs0) _
    calc (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
        ≤ _ := hstep1
      _ = ((k.choose i : ℝ) * ((k - i).factorial : ℝ)) * (Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹) *
            (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) := by
          rw [hid, ← hinv]
          ring
      _ ≤ (48 * (Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹)) * ((1 + K) ^ 4 * (1 + |y 2| / Axi.ϱ y) ^ k) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcj hW0) hKs hKs0 (by positivity)
      _ = (48 * Cf i) * M := by rw [hM]; ring
  have hsum : ∑ i ∈ Finset.range (k + 1), Cf i ≤ A :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun i _ _ => hCf0 i)
  have hfin : (1 + 48 * A) * (1 + K) ^ 4 * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
      (1 + |y 2| / Axi.ϱ y) ^ k * Sb = (1 + 48 * A) * M := by
    rw [clf_rpow _ hp.le k, hM]
    ring
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ :=
        clf_nv_leib R hR τ b hgS y hyS k
    _ ≤ ∑ i ∈ Finset.range (k + 1), (48 * Cf i) * M := Finset.sum_le_sum hterm
    _ = (48 * ∑ i ∈ Finset.range (k + 1), Cf i) * M := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (48 * A) * M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hM0
    _ ≤ (1 + 48 * A) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
    _ = (1 + 48 * A) * (1 + K) ^ 4 * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          (1 + |y 2| / Axi.ϱ y) ^ k * Sb := hfin.symm

/-- **Order-4 far-field homogeneity of the inlet column** (source 2542-2549, 1206-1222). -/
theorem inletEFarHom4 : InletEFarHom4 := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hmode z g _hdat i N
  have hν0 : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq]
    exact (one_le_inv₀ (pow_pos hν0 2)).2 (by nlinarith)
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.2
    have hneg : -d / p.ν < 0 := div_neg_of_neg_of_pos (by linarith [hreg.dm_pos, hreg.dm_le]) hν0
    exact hneg.le
  have hR1 : 1 ≤ p.R := (one_le_inv₀ p.ε_pos).2 hε1
  have hRpos : 0 < p.R := lt_of_lt_of_le one_pos hR1
  obtain ⟨Cb, κ, hκ, hsm, hbd⟩ := inletJetAll lam q hq p hmode hc1 hR1 i 4
  obtain ⟨K, hK0, hKb⟩ := chartLiftJets4 p.R hRpos
  obtain ⟨A, hA⟩ := efar_exp_poly hκ (4 + N)
  have hsmb : ContDiffOn ℝ ∞ (p.inletProfile i) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hsm.contDiffOn
  have hCb0 : 0 ≤ Cb := by
    by_contra hneg
    have hneg' : Cb < 0 := not_le.mp hneg
    have h := hbd 0 (Nat.zero_le _) ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
    have hE : 0 < Real.exp (-(κ * |((1 : ℝ), ((0 : ℝ), (0 : ℝ))).2.2|)) := Real.exp_pos _
    have h0 := norm_nonneg (iteratedFDeriv ℝ 0 (p.inletProfile i) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
    linarith [mul_neg_of_neg_of_pos hneg' hE]
  have hA0 : 0 ≤ A := by
    have h := hA 0 le_rfl
    norm_num at h
    linarith
  refine ⟨5 * K * Cb * A, p.R, hRpos, ?_⟩
  intro τ y hy k hk
  have hp : 0 < Axi.ϱ y := lt_trans hRpos hy
  have hyax : y ∉ Axi.axis := by
    intro h
    rw [Axi.mem_axis_iff] at h
    linarith
  have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
  have hRy : p.R ≤ Axi.ϱ y := le_of_lt hy
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have h1t0 : 0 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hpos1 : 0 < 1 + |y 2| / Axi.ϱ y := by linarith
  have hgS : ContDiffOn ℝ ∞ (fun z => (p.inletProfile i) (Axi.chart p.R τ z)) Axi.axisᶜ :=
    hsmb.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
  have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (p.inletProfile i) τ) Axi.axisᶜ := by
    have hEq : Axi.Nv p.R (p.inletProfile i) τ =
        fun z => liftFactor p.R z ((p.inletProfile i) (Axi.chart p.R τ z)) :=
      funext fun z => Nv_eq_liftFactor p.R (p.inletProfile i) τ z
    rw [hEq]
    exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
  have hη : |y 2| / Axi.ϱ y ≤ |(Axi.chart p.R τ y).2.2| := by
    show |y 2| / Axi.ϱ y ≤ |Axi.trans p.R y|
    rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hp]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) hR1) hp.le
  have hbdk : ∀ l : ℕ, l ≤ 4 →
      ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖ ≤
        Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) := by
    intro l hl
    refine (hbd l hl (Axi.chart p.R τ y)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hη hκ.le))) hCb0
  have hS : ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖
      ≤ 5 * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
    have hk5 : ((k : ℝ) + 1) ≤ 5 := by
      have : (k : ℝ) ≤ 4 := by exact_mod_cast hk
      linarith
    calc ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖
        ≤ ∑ l ∈ Finset.range (k + 1), Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) :=
          Finset.sum_le_sum (fun l hl => hbdk l (by have := Finset.mem_range.1 hl; omega))
      _ = ((k : ℝ) + 1) * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 5 * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) :=
          mul_le_mul_of_nonneg_right hk5 (mul_nonneg hCb0 (Real.exp_pos _).le)
  have hD : ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ =
      ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ := by
    show ‖iteratedFDeriv ℝ k
      (fun x : UnforcedLeray.Space => efarRealCLI (Axi.Nv p.R (p.inletProfile i) τ x)) y‖ = _
    exact efar_realC_norm _ hNvS hyS k
  have hchart := hKb (p.inletProfile i) hsmb τ y hRy k hk
  have hkey : (1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) ≤
      A * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ)) := by
    rw [Real.rpow_neg h1t0, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos1 N)]
    calc (1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))
          * (1 + |y 2| / Axi.ϱ y) ^ N
        = Real.exp (-(κ * (|y 2| / Axi.ϱ y))) * (1 + |y 2| / Axi.ϱ y) ^ (k + N) := by ring
      _ ≤ Real.exp (-(κ * (|y 2| / Axi.ϱ y))) * (1 + |y 2| / Axi.ϱ y) ^ (4 + N) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega))
            (Real.exp_pos _).le
      _ ≤ A := hA _ ht0
  calc ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖
      = ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ := hD
    _ ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
          (5 * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))))) :=
        hchart.trans (mul_le_mul_of_nonneg_left hS
          (mul_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg hp.le _)) (pow_nonneg h1t0 _)))
    _ = (5 * K * Cb) * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          ((1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
        ring
    _ ≤ (5 * K * Cb) * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          (A * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0.le) hCb0)
            (Real.rpow_nonneg hp.le _))
    _ = 5 * K * Cb * A * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
