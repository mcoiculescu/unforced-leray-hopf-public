import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq.IteratedInletDerivY.Near
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.EFar4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.ProdHom2.RawFar3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Drift
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainFluctAgeJetFixed

/-!
# Far-field all-order bound for `inletSrc` (`PartII-b:S2/1/3`)

Source of record: `the November 2 reference manuscript`,
lines 2542-2549 (drift cancellation `L₀E = -νΔE` on the far set and `ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`),
2563-2569 (slice bridge), 1206-1222 (homogeneous raw field).

Proves:
1. `inletEFarHomAll`: all-order far-field homogeneity `-1` of `p.Efun i`, with `ν₀ = 1`.
2. `rawFarJetsAll`: all-order far-field homogeneity `-1` of `p.raw`, with `ν₀` independent of order.
3. `inletFarAll`: with a single `ν₀ > 0` independent of `m`, for every `m : ℕ` and `β : Fin m → Fin 3`,
   `∃ C R0 > 0, ∀ τ ∈ Ioc 0 p.period, ∀ y, R0 < ϱ y → ‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤ C * ϱ^{-3} (1 + |y₃|/ϱ)^{-2}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.B0412
open UnforcedLeray.Short.PartIIIb.Concrete

namespace UnforcedLeray.Short.IIb.IterInletSub

/-! ### 1. All-order far-field homogeneity of `p.Efun i` -/

private lemma chartJetBoundAll (R : ℝ) (hR : 0 < R) (L : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y →
      ∀ m : ℕ, 1 ≤ m → m ≤ L →
        ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
  have key : ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y →
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
    have hyax : y ∉ Axi.axis := RawIterEnvSub.notMem_axis_of_le hR hy
    have hU : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
    have hmem : (Axi.axisᶜ : Set Space) ∈ nhds y := hU.mem_nhds hyax
    have hAgeS : ContDiffOn ℝ ∞ (fun z : Space => R ^ 2 / Axi.ϱ z ^ 2) Axi.axisᶜ :=
      contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2) (fun z hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
    have hLogS : ContDiffOn ℝ ∞ (fun z : Space => Real.log (Axi.age R z)) Axi.axisᶜ :=
      ContDiffOn.log hAgeS (fun z hz => (Axi.age_pos hR.ne' hz).ne')
    have hPhaseS : ContDiffOn ℝ ∞
        (fun z : Space => R * τ / 2 - (R / 2) * Real.log (Axi.age R z)) Axi.axisᶜ :=
      contDiffOn_const.sub (contDiffOn_const.mul hLogS)
    have hTransS : ContDiffOn ℝ ∞ (fun z : Space => R * z 2 / Axi.ϱ z) Axi.axisᶜ :=
      ((show ContDiff ℝ ∞ (fun z : Space => R * z 2) by fun_prop).contDiffOn).div
        Axi.contDiffOn_ϱ (fun z hz => Axi.ϱ_ne_zero hz)
    have hAgeA : ContDiffAt ℝ ∞ (Axi.age R) y := hAgeS.contDiffAt hmem
    have hPhaseA : ContDiffAt ℝ ∞ (Axi.phase R τ) y := hPhaseS.contDiffAt hmem
    have hTransA : ContDiffAt ℝ ∞ (Axi.trans R) y := hTransS.contDiffAt hmem
    have hm' : (m : WithTop ℕ∞) ≤ ∞ := by simp
    have hA := chartJetL1.contDiff.comp_contDiffAt y hAgeA
    have hB := chartJetL2.contDiff.comp_contDiffAt y hPhaseA
    have hC := chartJetL3.contDiff.comp_contDiffAt y hTransA
    have hAB := hA.add hB
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
        (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDA ?_
      calc ‖chartJetL1‖ * (Ca * Axi.ϱ y ^ (-(2 + (m : ℝ))))
          ≤ ‖chartJetL1‖ * (Ca * ((R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hage hCa0) (norm_nonneg _)
        _ ≤ (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
            have : Axi.ϱ y ^ (-(m : ℝ)) ≤ Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y) :=
              le_mul_of_one_le_right hq0 hs1
            have h0 : 0 ≤ ‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) := hL1
            calc ‖chartJetL1‖ * (Ca * ((R ^ 2)⁻¹ * Axi.ϱ y ^ (-(m : ℝ))))
                = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
              _ ≤ (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) *
                    (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
                  mul_le_mul_of_nonneg_left this h0
    have eB : ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ ≤
        (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by
      refine le_trans hDB ?_
      have : Axi.ϱ y ^ (-(m : ℝ)) ≤ Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y) :=
        le_mul_of_one_le_right hq0 hs1
      calc ‖chartJetL2‖ * (Cp * Axi.ϱ y ^ (-(m : ℝ)))
          = (‖chartJetL2‖ * Cp) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
        _ ≤ (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            mul_le_mul_of_nonneg_left this hL2
    have eC : ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ ≤
        (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
      le_trans hDC (le_of_eq (by ring))
    have hAB' : ContDiffAt ℝ ∞ (chartJetL1 ∘ Axi.age R + chartJetL2 ∘ Axi.phase R τ) y := hAB
    have hdec : Axi.chart R τ =
        (chartJetL1 ∘ Axi.age R + chartJetL2 ∘ Axi.phase R τ) + chartJetL3 ∘ Axi.trans R :=
      chartJet_decomp R τ
    rw [hdec, iteratedFDeriv_add_apply (hAB'.of_le hm') (hC.of_le hm'),
      iteratedFDeriv_add_apply (hA.of_le hm') (hB.of_le hm')]
    calc ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
            iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y +
          iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖
        ≤ ‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y +
            iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖ +
          ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ := norm_add_le _ _
      _ ≤ (‖iteratedFDeriv ℝ m (chartJetL1 ∘ Axi.age R) y‖ +
            ‖iteratedFDeriv ℝ m (chartJetL2 ∘ Axi.phase R τ) y‖) +
          ‖iteratedFDeriv ℝ m (chartJetL3 ∘ Axi.trans R) y‖ := add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹)) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) +
          (‖chartJetL2‖ * Cp) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y))) +
          (‖chartJetL3‖ * Ct) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
            add_le_add (add_le_add eA eB) eC
      _ = (‖chartJetL1‖ * (Ca * (R ^ 2)⁻¹) + ‖chartJetL2‖ * Cp + ‖chartJetL3‖ * Ct) *
            (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := by ring
  have key' : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y → 1 ≤ m →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤
        C * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := fun m => by
    by_cases hm : 1 ≤ m
    · obtain ⟨C, hC0, hC⟩ := key m hm
      exact ⟨C, hC0, fun τ y hy _ => hC τ y hy⟩
    · exact ⟨0, le_rfl, fun _ _ _ h => absurd h hm⟩
  choose C hC0 hC using key'
  refine ⟨1 + ∑ i ∈ Finset.range (L + 1), C i,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun i _ => hC0 i)), fun τ y hy m hm1 hmL => ?_⟩
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
  have hCm : C m ≤ 1 + ∑ i ∈ Finset.range (L + 1), C i := by
    have : C m ≤ ∑ i ∈ Finset.range (L + 1), C i :=
      Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.2 (by omega))
    linarith
  have hK1 : 1 ≤ 1 + ∑ i ∈ Finset.range (L + 1), C i := by
    linarith [Finset.sum_nonneg (s := Finset.range (L + 1)) (fun i _ => hC0 i)]
  have hpow : 1 ≤ (1 + ∑ i ∈ Finset.range (L + 1), C i) * (1 + |y 2| / Axi.ϱ y) :=
    one_le_mul_of_one_le_of_one_le hK1 hs1
  calc ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖
      ≤ C m * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) := hC m τ y hy hm1
    _ ≤ (1 + ∑ i ∈ Finset.range (L + 1), C i) * (Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)) :=
        mul_le_mul_of_nonneg_right hCm (mul_nonneg (Real.rpow_nonneg hp.le _) (by linarith))
    _ = ((1 + ∑ i ∈ Finset.range (L + 1), C i) * (1 + |y 2| / Axi.ϱ y)) * Axi.ϱ y ^ (-(m : ℝ)) := by ring
    _ ≤ ((1 + ∑ i ∈ Finset.range (L + 1), C i) * (1 + |y 2| / Axi.ϱ y)) ^ m *
          (Axi.ϱ y ^ m)⁻¹ := by
        rw [Real.rpow_neg hp.le, Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_right (le_self_pow₀ hpow (by omega)) (inv_nonneg.2 (pow_nonneg hp.le _))
    _ = ((1 + ∑ i ∈ Finset.range (L + 1), C i) * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m := by
        rw [div_pow, ← div_eq_mul_inv]

private lemma chartLiftJetsAll (R : ℝ) (hR : 0 < R) (L : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid),
      ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
      ∀ (τ : ℝ) (y : Space), R ≤ Axi.ϱ y → ∀ k : ℕ, k ≤ L →
        ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖ ≤
          K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
            ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
  obtain ⟨K, hK0, hKb⟩ := chartJetBoundAll R hR L
  choose Cf hCf0 hCf using fun m => liftFactorJet R hR m
  set A : ℝ := ∑ i ∈ Finset.range (L + 1), Cf i
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => hCf0 i)
  let Bfac : ℝ := (2 ^ L * L.factorial : ℕ)
  refine ⟨(1 + Bfac * A) * (1 + K) ^ L,
    mul_pos (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (Nat.cast_nonneg _) hA0)) (pow_pos (by linarith) L), ?_⟩
  intro b hb τ y hy k hk
  have hyax : y ∉ Axi.axis := RawIterEnvSub.notMem_axis_of_le hR hy
  have hyS : y ∈ (Axi.axisᶜ : Set Space) := hyax
  have hp : 0 < Axi.ϱ y := lt_of_lt_of_le hR hy
  have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith [div_nonneg (abs_nonneg (y 2)) hp.le]
  have hgS : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (clf_chart_contDiffOn R τ hR) (clf_chart_mapsTo R τ hR)
  set Sb : ℝ := ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg (fun l _ => norm_nonneg _)
  have hCbk : ∀ l : ℕ, l ≤ k → ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ ≤ Sb := fun l hl =>
    Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j b (Axi.chart R τ y)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hGj : ∀ j : ℕ, j ≤ k → ‖iteratedFDerivWithin ℝ j (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (j.factorial : ℝ) * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ j := by
    intro j hj
    have hT : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} := isOpen_lt continuous_const continuous_fst
    have hxT : Axi.chart R τ y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := Axi.age_pos hR.ne' hyax
    have hCb : ∀ l : ℕ, l ≤ j → ‖iteratedFDerivWithin ℝ l b {m | 0 < m.1} (Axi.chart R τ y)‖ ≤ Sb := by
      intro l hl
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) l hT hxT]
      exact hCbk l (le_trans hl hj)
    have hDb : ∀ i : ℕ, 1 ≤ i → i ≤ j →
        ‖iteratedFDerivWithin ℝ i (Axi.chart R τ) Axi.axisᶜ y‖ ≤
          (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ i := by
      intro i h1 hi
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i Axi.isOpen_compl_axis hyS]
      exact hKb τ y hy i h1 (by omega)
    exact norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (N := ∞) hb (clf_chart_contDiffOn R τ hR)
      (by simp) hT.uniqueDiffOn Axi.isOpen_compl_axis.uniqueDiffOn (clf_chart_mapsTo R τ hR) hyS hCb hDb
  have hFi : ∀ i ∈ Finset.range (k + 1),
      ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ ≤ Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ))) := by
    intro i _
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := liftFactor R) i Axi.isOpen_compl_axis hyS]
    exact hCf i y hyax
  set M : ℝ := (1 + K) ^ L * (1 + |y 2| / Axi.ϱ y) ^ k * (Axi.ϱ y ^ (1 + k))⁻¹ * Sb
  have hM0 : 0 ≤ M := by
    have : 0 ≤ (Axi.ϱ y ^ (1 + k))⁻¹ := inv_nonneg.2 (pow_nonneg hp.le _)
    positivity
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ ≤
      (Bfac * Cf i) * M := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hcj : (k.choose i : ℝ) * ((k - i).factorial : ℝ) ≤ Bfac := by
      dsimp [Bfac]
      exact_mod_cast Nat.mul_le_mul
        ((Nat.choose_le_two_pow k i).trans (Nat.pow_le_pow_right (by norm_num) hk))
        (Nat.factorial_le (by omega))
    have hstep1 := mul_le_mul
      (mul_le_mul_of_nonneg_left (hFi i hi) (Nat.cast_nonneg (k.choose i)))
      (hGj (k - i) (by omega)) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg (k.choose i)) (mul_nonneg (hCf0 i) (Real.rpow_nonneg hp.le _)))
    have hid : (k.choose i : ℝ) * (Cf i * Axi.ϱ y ^ (-(1 + (i : ℝ)))) *
          ((k - i).factorial * Sb * (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ (k - i)) =
        ((k.choose i : ℝ) * ((k - i).factorial : ℝ)) * Cf i * Sb *
          (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) * ((Axi.ϱ y ^ (1 + i))⁻¹ * (Axi.ϱ y ^ (k - i))⁻¹) := by
      rw [clf_rpow _ hp.le i, div_pow]; ring
    have hinv : (Axi.ϱ y ^ (1 + i))⁻¹ * (Axi.ϱ y ^ (k - i))⁻¹ = (Axi.ϱ y ^ (1 + k))⁻¹ :=
      clf_inv_mul _ i (k - i) k (by omega)
    have hKs : (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) ≤ (1 + K) ^ L * (1 + |y 2| / Axi.ϱ y) ^ k := by
      rw [mul_pow]
      exact mul_le_mul
        (le_trans (pow_le_pow_left₀ hK0.le (by linarith) _)
          (pow_le_pow_right₀ (by linarith) (by omega)))
        (pow_le_pow_right₀ hs1 (by omega)) (by positivity) (by positivity)
    have hW0 : 0 ≤ Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹ :=
      mul_nonneg (mul_nonneg (hCf0 i) hSb0) (inv_nonneg.2 (pow_nonneg hp.le _))
    calc (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
        ≤ _ := hstep1
      _ = ((k.choose i : ℝ) * ((k - i).factorial : ℝ)) * (Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹) *
            (K * (1 + |y 2| / Axi.ϱ y)) ^ (k - i) := by rw [hid, ← hinv]; ring
      _ ≤ (Bfac * (Cf i * Sb * (Axi.ϱ y ^ (1 + k))⁻¹)) * ((1 + K) ^ L * (1 + |y 2| / Axi.ϱ y) ^ k) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcj hW0) hKs (by positivity) (by positivity)
      _ = (Bfac * Cf i) * M := by dsimp [M]; ring
  have hsum : ∑ i ∈ Finset.range (k + 1), Cf i ≤ A :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) (fun i _ _ => hCf0 i)
  have hfin : (1 + Bfac * A) * (1 + K) ^ L * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
      (1 + |y 2| / Axi.ϱ y) ^ k * Sb = (1 + Bfac * A) * M := by
    rw [clf_rpow _ hp.le k]; dsimp [M]; ring
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (liftFactor R) Axi.axisᶜ y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖ :=
        clf_nv_leib R hR τ b hgS y hyS k
    _ ≤ ∑ i ∈ Finset.range (k + 1), (Bfac * Cf i) * M := Finset.sum_le_sum hterm
    _ = (Bfac * ∑ i ∈ Finset.range (k + 1), Cf i) * M := by rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (Bfac * A) * M := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity)) hM0
    _ ≤ (1 + Bfac * A) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
    _ = (1 + Bfac * A) * (1 + K) ^ L * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          (1 + |y 2| / Axi.ϱ y) ^ k * Sb := hfin.symm

/-- All-order far-field homogeneity `-1` of `p.Efun i`, with `ν₀ = 1`. -/
theorem inletEFarHomAll (lam : ℂ) (q : Planar.Profile) (hq : Planar.IsGrowingEigenpair lam q)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.mode = q →
      ∀ (i : Fin 2) (L N : ℕ), ∃ C R0 : ℝ, 0 < R0 ∧
        ∀ (τ : ℝ) (y : Space), R0 < Axi.ϱ y → ∀ k : ℕ, k ≤ L →
          ‖iteratedFDeriv ℝ k (fun x : Space => p.Efun i (τ, x)) y‖ ≤
            C * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) := by
  intro p d hreg _hν hmode i L N
  have hν0 : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq]
    exact (one_le_inv₀ (pow_pos hν0 2)).2 (by nlinarith)
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.2
    exact (div_neg_of_neg_of_pos (by linarith [hreg.dm_pos, hreg.dm_le]) hν0).le
  have hR1 : 1 ≤ p.R := (one_le_inv₀ p.ε_pos).2 hε1
  have hRpos : 0 < p.R := lt_of_lt_of_le one_pos hR1
  obtain ⟨Cb, κ, hκ, hsm, hbd⟩ := inletJetAll lam q hq p hmode hc1 hR1 i L
  obtain ⟨K, hK0, hKb⟩ := chartLiftJetsAll p.R hRpos L
  obtain ⟨A, hA⟩ := efar_exp_poly hκ (L + N)
  have hsmb : ContDiffOn ℝ ∞ (p.inletProfile i) {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hsm.contDiffOn
  have hCb0 : 0 ≤ Cb := by
    by_contra hneg
    have h := hbd 0 (Nat.zero_le _) ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
    have hE : 0 < Real.exp (-(κ * |((1 : ℝ), ((0 : ℝ), (0 : ℝ))).2.2|)) := Real.exp_pos _
    have h0 := norm_nonneg (iteratedFDeriv ℝ 0 (p.inletProfile i) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
    linarith [mul_neg_of_neg_of_pos (not_le.1 hneg) hE]
  have hA0 : 0 ≤ A := by
    have h := hA 0 le_rfl; norm_num at h; linarith
  refine ⟨((L : ℝ) + 1) * K * Cb * A, p.R, hRpos, ?_⟩
  intro τ y hy k hk
  have hp : 0 < Axi.ϱ y := lt_trans hRpos hy
  have hyax : y ∉ Axi.axis := RawIterEnvSub.notMem_axis_of_le hRpos hy.le
  have hpos1 : 0 < 1 + |y 2| / Axi.ϱ y := by positivity
  have hη : |y 2| / Axi.ϱ y ≤ |(Axi.chart p.R τ y).2.2| := by
    show |y 2| / Axi.ϱ y ≤ |Axi.trans p.R y|
    rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hp]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) hR1) hp.le
  have hbdk : ∀ l : ℕ, l ≤ L →
      ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖ ≤
        Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) := fun l hl =>
    (hbd l hl (Axi.chart p.R τ y)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hη hκ.le))) hCb0)
  have hS : ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖ ≤
      ((L : ℝ) + 1) * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
    have hkL : (k : ℝ) + 1 ≤ (L : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
    calc ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (p.inletProfile i) (Axi.chart p.R τ y)‖
        ≤ ∑ _l ∈ Finset.range (k + 1), Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) :=
          Finset.sum_le_sum (fun l hl => hbdk l (by have := Finset.mem_range.1 hl; omega))
      _ = ((k : ℝ) + 1) * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ ((L : ℝ) + 1) * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) :=
          mul_le_mul_of_nonneg_right hkL (by positivity)
  have hNv : ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ ≤
      ((L : ℝ) + 1) * K * Cb * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
        ((1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by
    have h0 := hKb (p.inletProfile i) hsmb τ y hy.le k hk
    have hpre : 0 ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k :=
      mul_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg hp.le _)) (pow_nonneg hpos1.le _)
    calc ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖
        ≤ _ := h0
      _ ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
            (((L : ℝ) + 1) * (Cb * Real.exp (-(κ * (|y 2| / Axi.ϱ y))))) :=
          mul_le_mul_of_nonneg_left hS hpre
      _ = ((L : ℝ) + 1) * K * Cb * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
            ((1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := by ring
  have hpow : (1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) ≤
      A * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ)) := by
    have hs1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hp.le)
    have hkN : (1 + |y 2| / Axi.ϱ y) ^ (k + N) * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) ≤
        (1 + |y 2| / Axi.ϱ y) ^ (L + N) * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs1 (by omega)) (Real.exp_pos _).le
    have hAN : (1 + |y 2| / Axi.ϱ y) ^ (k + N) * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) ≤ A :=
      hkN.trans (by rw [mul_comm]; exact hA (|y 2| / Axi.ϱ y) (div_nonneg (abs_nonneg _) hp.le))
    have hsplit : (1 + |y 2| / Axi.ϱ y) ^ (k + N) =
        (1 + |y 2| / Axi.ϱ y) ^ k * (1 + |y 2| / Axi.ϱ y) ^ N := pow_add _ _ _
    have hposN : 0 < (1 + |y 2| / Axi.ϱ y) ^ N := pow_pos hpos1 N
    have hinv : ((1 + |y 2| / Axi.ϱ y) ^ N)⁻¹ = (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg hpos1.le, Real.rpow_natCast]
    rw [← hinv, le_mul_inv_iff₀ hposN]
    calc ((1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) *
          (1 + |y 2| / Axi.ϱ y) ^ N
        = ((1 + |y 2| / Axi.ϱ y) ^ k * (1 + |y 2| / Axi.ϱ y) ^ N) *
            Real.exp (-(κ * (|y 2| / Axi.ϱ y))) := by ring
      _ = (1 + |y 2| / Axi.ϱ y) ^ (k + N) * Real.exp (-(κ * (|y 2| / Axi.ϱ y))) := by rw [hsplit]
      _ ≤ A := hAN
  have hrealC : (fun x : Space => p.Efun i (τ, x)) =
      (fun x : Space => realCCLM (Axi.Nv p.R (p.inletProfile i) τ x)) := rfl
  have hrc : ‖iteratedFDeriv ℝ k (fun x : Space => p.Efun i (τ, x)) y‖ ≤
      ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ := by
    rw [hrealC]
    have hgS : ContDiffOn ℝ ∞ (fun z => (p.inletProfile i) (Axi.chart p.R τ z)) Axi.axisᶜ :=
      hsmb.comp (clf_chart_contDiffOn p.R τ hRpos) (clf_chart_mapsTo p.R τ hRpos)
    have hNvS : ContDiffOn ℝ ∞ (Axi.Nv p.R (p.inletProfile i) τ) Axi.axisᶜ := by
      have hEq : Axi.Nv p.R (p.inletProfile i) τ =
          fun z => liftFactor p.R z ((p.inletProfile i) (Axi.chart p.R τ z)) :=
        funext fun z => Nv_eq_liftFactor p.R (p.inletProfile i) τ z
      rw [hEq]
      exact (clf_lift_contDiffOn p.R hRpos).clm_apply hgS
    have hNvAt : ContDiffAt ℝ ∞ (Axi.Nv p.R (p.inletProfile i) τ) y :=
      hNvS.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hyax)
    have hle := ContinuousLinearMap.norm_iteratedFDeriv_comp_left realCCLM hNvAt
      (by simp : (k : WithTop ℕ∞) ≤ ∞) (x := y)
    exact hle.trans (mul_le_of_le_one_left (norm_nonneg _) norm_realCCLM_le_one)
  calc ‖iteratedFDeriv ℝ k (fun x : Space => p.Efun i (τ, x)) y‖
      ≤ ‖iteratedFDeriv ℝ k (Axi.Nv p.R (p.inletProfile i) τ) y‖ := hrc
    _ ≤ ((L : ℝ) + 1) * K * Cb * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          ((1 + |y 2| / Axi.ϱ y) ^ k * Real.exp (-(κ * (|y 2| / Axi.ϱ y)))) := hNv
    _ ≤ ((L : ℝ) + 1) * K * Cb * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          (A * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hK0.le) hCb0)
            (Real.rpow_nonneg hp.le _))
    _ = ((L : ℝ) + 1) * K * Cb * A *
          (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ))) := by ring

/-! ### 2. All-order far-field homogeneity of `p.raw` -/

private lemma meanStream_jetsAll_of (h1 : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ L : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, l ≤ L → ∀ y : ℝ × UnforcedLeray.Cyl.Plane,
          0 < y.1 → y.1 ≤ 1 →
            ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
              UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ C * (1 + |y.2.2|) := by
  obtain ⟨ν₀, hν₀, HJ⟩ := meanJetsFixed_of h1 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν c hν hν₀' hc tr hbuc L => ?_⟩
  have hcp : c = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg hν.le, Real.rpow_two]
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsm2 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc0 tr hbuc
  let M : ℕ → ℝ := fun l => if hl : 1 ≤ l then Classical.choose (HJ ν c hν hν₀' hcp tr hbuc l hl) else 0
  have hM : ∀ (l : ℕ) (hl : 1 ≤ l) (y : ℝ × ℝ), 0 < y.1 →
      ‖iteratedFDeriv ℝ l (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2) y‖ ≤ M l := by
    intro l hl y hy
    dsimp [M]
    simp only [hl, ↓reduceDIte]
    exact Classical.choose_spec (HJ ν c hν hν₀' hcp tr hbuc l hl) y hy
  let B : ℝ := ∑ l ∈ Finset.range (L + 2), max (M l) 0
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => le_max_right _ _
  let gCLM : (ℝ × UnforcedLeray.Cyl.Plane) →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Cyl.Plane |>.prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ |>.comp (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Cyl.Plane))
  have hbpos : ∀ l : ℕ, 1 ≤ l → l ≤ L + 1 → ∀ y : ℝ × UnforcedLeray.Cyl.Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l
        (fun x : ℝ × UnforcedLeray.Cyl.Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ B := by
    intro l hl1 hlL y hy
    have hMl : M l ≤ B :=
      (le_max_left (M l) 0).trans (Finset.single_le_sum (fun _ _ => le_max_right _ _)
        (Finset.mem_range.2 (by omega)))
    have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hy_mem : gCLM y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hy, mem_univ _⟩
    have hcomp_within := gCLM.iteratedFDerivWithin_comp_right hsm2 hU.uniqueDiffOn
      (hU.preimage gCLM.continuous).uniqueDiffOn hy_mem (i := l) (by simp)
    have hcomp_eq : iteratedFDeriv ℝ l
        (fun x : ℝ × UnforcedLeray.Cyl.Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y =
        (iteratedFDeriv ℝ l (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
          (gCLM y)).compContinuousLinearMap (fun _ => gCLM) := by
      rw [← iteratedFDerivWithin_of_isOpen l (hU.preimage gCLM.continuous) hy_mem,
        ← iteratedFDerivWithin_of_isOpen l hU hy_mem]
      exact hcomp_within
    have hnorm_g : ‖gCLM‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
      rw [one_mul, Prod.norm_def]
      exact max_le (norm_fst_le v) ((norm_snd_le v.2).trans (norm_snd_le v))
    calc ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
            UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖
        ≤ ‖iteratedFDeriv ℝ l (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
            (gCLM y)‖ * ∏ _i : Fin l, ‖gCLM‖ := by
          rw [hcomp_eq]; exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ B * 1 := mul_le_mul ((hM l hl1 (y.1, y.2.2) hy).trans hMl)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hnorm_g))
          (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hB0
      _ = B := mul_one B
  have h0 := zeroFromGrad (UnforcedLeray.Short.PartI.meanStream tr) B hsm2
    (hbpos 1 le_rfl (by omega)) 1 one_pos
  refine ⟨|UnforcedLeray.Short.PartI.meanStream tr 1 0| + B, by positivity, fun l hl y hy0 hy1 => ?_⟩
  rcases eq_or_ne l 0 with rfl | hl0
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have h0y := h0 y hy0 hy1
    nlinarith [abs_nonneg (UnforcedLeray.Short.PartI.meanStream tr 1 0), abs_nonneg y.2.2]
  · exact (hbpos l (Nat.pos_of_ne_zero hl0) (by omega) y hy0).trans
      (by nlinarith [abs_nonneg (UnforcedLeray.Short.PartI.meanStream tr 1 0), abs_nonneg y.2.2])

private lemma fluct_jetsAll_of (hF : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ L : ℕ, ∃ (C : ℝ), 0 ≤ C ∧ ∀ l : ℕ, l ≤ L →
          ∀ y : ℝ × UnforcedLeray.Cyl.Plane, 0 < y.1 →
            ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
              tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ C := by
  obtain ⟨ν₀, hν₀, HF⟩ := hF 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν c hν hν₀' hc tr hbuc L => ?_⟩
  have hcp : UnforcedLeray.Short.PartI.trainPeriod 2 ν = c := by
    rw [hc, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg hν.le, Real.rpow_two]
  subst hcp
  have hc0 : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by rw [hc]; positivity
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc0 tr hbuc
  have hsm2 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν _ hν hc0 tr hbuc
  let gCLM : (ℝ × UnforcedLeray.Cyl.Plane) →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Cyl.Plane |>.prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ |>.comp (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Cyl.Plane))
  have hsm : ContDiffOn ℝ ∞
      (fun x : ℝ × UnforcedLeray.Cyl.Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ) :=
    hsm2.comp gCLM.contDiff.contDiffOn (fun x hx => ⟨hx.1, mem_univ _⟩)
  set F : ℝ → UnforcedLeray.Cyl.Plane → ℝ :=
    fun r w => tr.ψ r w -
      UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (tr.ψ r) w.2
  have hFeq :
      (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
        tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) =
        (fun x : ℝ × UnforcedLeray.Cyl.Plane => F x.1 x.2) := rfl
  have hfl : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) := by
    rw [← hFeq]; exact hψ.sub hsm
  have hage : ∀ ℓ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 0 < s → ∀ z : UnforcedLeray.Cyl.Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ j F s z‖ ≤ B := by
    intro ℓ j
    obtain ⟨C, κ, hκ, hC⟩ := HF ν hν hν₀' tr hbuc ℓ j
    refine ⟨|C|, abs_nonneg C, fun s hs z => ?_⟩
    have he0 : 0 ≤ Real.exp (-(κ * s)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(κ * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκ.le hs.le))
    calc ‖UnforcedLeray.Short.PartI.ageJet ℓ j F s z‖
        ≤ C * Real.exp (-(κ * s)) := hC s hs z
      _ ≤ |C| * Real.exp (-(κ * s)) := mul_le_mul_of_nonneg_right (le_abs_self C) he0
      _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) he1
  choose B hB0 hB using hage
  have hJ : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
      ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => G x.1 x.2) (Ioi 0 ×ˢ univ) →
      ∀ y : ℝ × UnforcedLeray.Cyl.Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ i (fun x : ℝ × UnforcedLeray.Cyl.Plane => G x.1 x.2) y‖ ≤
          K * ∑ ℓ ∈ Finset.range (i + 1),
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ :=
    UnforcedLeray.Short.PartI.jointFromAgeJets
  choose K hK0 hK using hJ
  refine ⟨∑ l ∈ Finset.range (L + 1), K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ),
    Finset.sum_nonneg (fun l _ => mul_nonneg (hK0 l) (Finset.sum_nonneg (fun ℓ _ => hB0 ℓ (l - ℓ)))),
    fun l hl y hy => ?_⟩
  have hlL : l ∈ Finset.range (L + 1) := Finset.mem_range.2 (by omega)
  rw [hFeq]
  calc ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane => F x.1 x.2) y‖
      ≤ K l * ∑ ℓ ∈ Finset.range (l + 1),
          ‖UnforcedLeray.Short.PartI.ageJet ℓ (l - ℓ) F y.1 y.2‖ := hK l F hfl y hy
    _ ≤ K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ℓ _ => hB ℓ (l - ℓ) y.1 hy y.2)) (hK0 l)
    _ ≤ ∑ l ∈ Finset.range (L + 1), K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ) :=
        Finset.single_le_sum
          (f := fun l => K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ))
          (fun l' _ => mul_nonneg (hK0 l') (Finset.sum_nonneg (fun ℓ _ => hB0 ℓ (l' - ℓ)))) hlL

private lemma stream_jetsAll_of (h1 : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed)
    (hF : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ L : ℕ, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ l : ℕ, l ≤ L →
          ∀ y : ℝ × UnforcedLeray.Cyl.Plane, 0 < y.1 → y.1 ≤ 1 →
            ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
              tr.ψ x.1 x.2) y‖ ≤ C * (1 + |y.2.2|) ^ M := by
  obtain ⟨ν1, hν1, Hm⟩ := meanStream_jetsAll_of h1
  obtain ⟨ν2, hν2, Hf⟩ := fluct_jetsAll_of hF
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun ν c hν hν' hc tr hbuc L => ?_⟩
  obtain ⟨Cm, hCm0, hm⟩ := Hm ν c hν (hν'.trans (min_le_left _ _)) hc tr hbuc L
  obtain ⟨Cf, hCf0, hf⟩ := Hf ν c hν (hν'.trans (min_le_right _ _)) hc tr hbuc L
  refine ⟨Cm + Cf, 1, add_nonneg hCm0 hCf0, fun l hl y hy0 hy1 => ?_⟩
  have hsm : ContDiffAt ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
      UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y := by
    have hc0 : 0 < c := by rw [hc]; positivity
    have hsm2 := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc0 tr hbuc
    let gCLM : (ℝ × UnforcedLeray.Cyl.Plane) →L[ℝ] (ℝ × ℝ) :=
      ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Cyl.Plane |>.prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ |>.comp (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Cyl.Plane))
    exact ((hsm2.comp gCLM.contDiff.contDiffOn (fun x (hx : x ∈ Ioi 0 ×ˢ univ) => ⟨hx.1, mem_univ _⟩)).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hy0, mem_univ _⟩)).of_le (by exact_mod_cast le_top)
  have hfl : ContDiffAt ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
      tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y := by
    have hc0 : 0 < c := by rw [hc]; positivity
    have hψ := UnforcedLeray.Short.PartI.trainStreamSmooth ν c hν hc0 tr hbuc
    have hsm2 := UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc0 tr hbuc
    let gCLM : (ℝ × UnforcedLeray.Cyl.Plane) →L[ℝ] (ℝ × ℝ) :=
      ContinuousLinearMap.fst ℝ ℝ UnforcedLeray.Cyl.Plane |>.prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ |>.comp (ContinuousLinearMap.snd ℝ ℝ UnforcedLeray.Cyl.Plane))
    have hsm' := hsm2.comp gCLM.contDiff.contDiffOn (fun x (hx : x ∈ Ioi 0 ×ˢ univ) => ⟨hx.1, mem_univ _⟩)
    exact ((hψ.sub hsm').contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hy0, mem_univ _⟩)).of_le
      (by exact_mod_cast le_top)
  have hsplit : (fun x : ℝ × UnforcedLeray.Cyl.Plane => tr.ψ x.1 x.2) =
      (fun x : ℝ × UnforcedLeray.Cyl.Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) +
      (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
        tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) := by
    ext x; simp
  rw [hsplit, iteratedFDeriv_add_apply hsm hfl, pow_one]
  have h1y : 1 ≤ 1 + |y.2.2| := by linarith [abs_nonneg y.2.2]
  calc ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
          UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y +
        iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
          tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖
      ≤ ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
            UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ +
          ‖iteratedFDeriv ℝ l (fun x : ℝ × UnforcedLeray.Cyl.Plane =>
            tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ := norm_add_le _ _
    _ ≤ Cm * (1 + |y.2.2|) + Cf := add_le_add (hm l hl y hy0 hy1) (hf l hl y hy0)
    _ ≤ Cm * (1 + |y.2.2|) + Cf * (1 + |y.2.2|) :=
        add_le_add le_rfl (le_mul_of_one_le_right hCf0 h1y)
    _ = (Cm + Cf) * (1 + |y.2.2|) := by ring

/-- All-order far-field homogeneity of `p.raw`:
for every order `L : ℕ`, with a single `ν₀ > 0` independent of `L`? Wait: we only need `ν₀`
independent of `L`! Here `ν₀` comes from `stream_jetsAll_of` (independent of `L`). -/
private lemma age_le_one_of_radius_gt {R : ℝ} (hR : 0 < R)
    {y : UnforcedLeray.Space} (hy : R < Axi.ϱ y) :
    R ≤ Axi.ϱ y ∧ Axi.age R y ≤ 1 := by
  have hρ : 0 < Axi.ϱ y := hR.trans hy
  refine ⟨hy.le, ?_⟩
  unfold Axi.age
  rw [div_le_one (pow_pos hρ 2)]
  exact pow_le_pow_left₀ hR.le hy.le 2

/-- All-order far-field homogeneity of `p.raw`, with `ν₀` independent of `L`. -/
private theorem rawFarJetsAll (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ L : ℕ, ∃ (CR R0r : ℝ) (M : ℕ), 0 < R0r ∧ 0 ≤ CR ∧
        ContDiffOn ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)
          {x : ℝ × Space | R0r < Axi.ϱ x.2} ∧
        ∀ (τ : ℝ) (y : Space), R0r < Axi.ϱ y → ∀ k : ℕ, k ≤ L →
          ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤
            CR * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ M) := by
  obtain ⟨ν1, hν1, HS⟩ := stream_jetsAll_of UnforcedLeray.Short.PartI.trainJetsBoundedFixed
    UnforcedLeray.Short.PartI.trainFluctAgeJetFixed
  obtain ⟨ν2, hν2, Hsm⟩ := rawJointSmooth dm dp hdm
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun p d hreg hν L => ?_⟩
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_eq : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hbuc : UnforcedLeray.Short.PartI.IsBUCTrain p.train := hreg.train_buc
  have hsm := Hsm p d hreg (hν.trans (min_le_right _ _))
  obtain ⟨Cs, Ms, hCs0, hs⟩ := HS p.ν p.c hν_pos (hν.trans (min_le_left _ _)) hc_eq p.train hbuc (L + 1)
  have hRpos : 0 < p.R := p.R_pos
  obtain ⟨K, hK0, hKb⟩ := chartLiftJetsAll p.R hRpos L
  set b : ℝ × (ℝ × ℝ) → Axi.Merid :=
    UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ
  have hRing := UnforcedLeray.Short.PartIIIb.Concrete.ringProfileMeridJet p.R
    (fun y => p.train.ψ y.1 y.2) hreg.train_stream_smooth
  have hUopen : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    isOpen_lt continuous_const continuous_fst
  have hRawEq : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      b y = UnforcedLeray.Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2) y := by
    intro y hy
    have hεR : p.R⁻¹ = p.ε := inv_inv p.ε
    dsimp [b]
    rw [← hεR]
    exact UnforcedLeray.Short.IIb.rawStreamProfile p.ν p.c p.R p.train p.R_pos
      hreg.train_stream_smooth y hy
  have hb_sm : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    (hRing.1.congr (fun y hy => hRawEq y hy.1)).mono (fun y hy => ⟨hy, mem_univ _⟩)
  let Cfn : ℕ → ℝ := fun l => Classical.choose (hRing.2 l)
  have hCfn : ∀ l : ℕ, ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2)) y‖ ≤
        Cfn l * (1 + |y.1| + |y.2.2|) *
          ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) y‖ :=
    fun l => Classical.choose_spec (hRing.2 l)
  set CM : ℝ := ∑ l ∈ Finset.range (L + 1), max (Cfn l) 0
  have hCM0 : 0 ≤ CM := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hCfn_le : ∀ l : ℕ, l ≤ L → Cfn l ≤ CM := by
    intro l hl
    exact (le_max_left (Cfn l) 0).trans
      (Finset.single_le_sum (fun i _ => le_max_right (Cfn i) 0)
        (Finset.mem_range.2 (by omega)))
  set Cprof : ℝ := CM * 2 * ((L : ℝ) + 2) * Cs
  have hCprof0 : 0 ≤ Cprof := by positivity
  have hpb : ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ 1 → ∀ l : ℕ, l ≤ L →
      ‖iteratedFDeriv ℝ l b m‖ ≤ Cprof * (1 + |m.2.2|) ^ (Ms + 1) := by
    intro m hm0 hm1 l hl
    have hev : b =ᶠ[𝓝 m] UnforcedLeray.Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2) :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hm0) (fun z hz => hRawEq z hz)
    rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds]
    have h1 : ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2)) m‖ ≤
        Cfn l * (1 + |m.1| + |m.2.2|) *
          ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ :=
      hCfn l m hm0
    have hm1' : |m.1| ≤ 1 := by rw [abs_of_pos hm0]; exact hm1
    have h1m : 1 + |m.1| + |m.2.2| ≤ 2 * (1 + |m.2.2|) := by
      have : 0 ≤ |m.2.2| := abs_nonneg _
      linarith
    have hsum_j : ∑ j ∈ Finset.range (l + 2),
        ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ ≤
        ((L : ℝ) + 2) * (Cs * (1 + |m.2.2|) ^ Ms) := by
      have hle : ∀ j ∈ Finset.range (l + 2),
          ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ ≤ Cs * (1 + |m.2.2|) ^ Ms := by
        intro j hj
        have hj' : j ≤ L + 1 := by have := Finset.mem_range.1 hj; omega
        exact hs j hj' m hm0 hm1
      calc ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖
          ≤ ∑ _j ∈ Finset.range (l + 2), (Cs * (1 + |m.2.2|) ^ Ms) :=
            Finset.sum_le_sum hle
        _ = ((l + 2 : ℕ) : ℝ) * (Cs * (1 + |m.2.2|) ^ Ms) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ((L : ℝ) + 2) * (Cs * (1 + |m.2.2|) ^ Ms) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (by omega : l + 2 ≤ L + 2)
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range (l + 2),
        ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    calc ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2)) m‖
        ≤ Cfn l * (1 + |m.1| + |m.2.2|) *
            ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ := h1
      _ ≤ CM * (2 * (1 + |m.2.2|)) * (((L : ℝ) + 2) * (Cs * (1 + |m.2.2|) ^ Ms)) := by
          apply mul_le_mul
          · exact mul_le_mul (hCfn_le l hl) h1m (by positivity) hCM0
          · exact hsum_j
          · exact hsum0
          · positivity
      _ = Cprof * (1 + |m.2.2|) ^ (Ms + 1) := by
          rw [pow_succ']
          dsimp [Cprof]
          ring
  set R0r : ℝ := max p.R 1
  have hR0r_pos : 0 < R0r := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRaw_sm : ContDiffOn ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)
      {x : ℝ × Space | R0r < Axi.ϱ x.2} :=
    hsm.contDiffOn.mono (subset_univ _)
  set Mp : ℕ := Ms + 1
  set CR : ℝ := K * ((L : ℝ) + 1) * Cprof * p.R ^ Mp
  refine ⟨CR, R0r, Mp + L, hR0r_pos, by positivity, hRaw_sm, fun τ y hy k hk => ?_⟩
  have hRy_lt : p.R < Axi.ϱ y := lt_of_le_of_lt (le_max_left _ _) hy
  obtain ⟨hRy, hage⟩ := age_le_one_of_radius_gt hRpos hRy_lt
  have hρ : 0 < Axi.ϱ y := lt_of_lt_of_le hRpos hRy
  have hyax : y ∉ Axi.axis := by
    intro hax
    rw [Axi.mem_axis_iff] at hax
    linarith
  have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R b τ :=
    Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
      (fun z hz => UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis p τ z hz)
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have hchart := hKb b hb_sm τ y hRy k hk
  set t : ℝ := |y 2| / Axi.ϱ y
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) hρ.le
  have hs1 : 1 ≤ 1 + t := by linarith
  have hR1 : 1 ≤ p.R := by
    have hε1 : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.2
      exact (div_neg_of_neg_of_pos (by linarith [hreg.dm_pos, hreg.dm_le]) hν_pos).le
    exact (one_le_inv₀ p.ε_pos).2 hε1
  have hη : |(Axi.chart p.R τ y).2.2| = p.R * t := by
    show |Axi.trans p.R y| = p.R * (|y 2| / Axi.ϱ y)
    rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hρ, mul_div_assoc]
  have h1η : 1 + |(Axi.chart p.R τ y).2.2| ≤ p.R * (1 + t) := by
    rw [hη]
    nlinarith only [hR1]
  have hpowM : (1 + |(Axi.chart p.R τ y).2.2|) ^ Mp ≤ p.R ^ Mp * (1 + t) ^ Mp := by
    calc (1 + |(Axi.chart p.R τ y).2.2|) ^ Mp
        ≤ (p.R * (1 + t)) ^ Mp := pow_le_pow_left₀ (by positivity) h1η Mp
      _ = p.R ^ Mp * (1 + t) ^ Mp := mul_pow _ _ _
  have hm0 : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hRpos.ne' hyax
  have hbl : ∀ l : ℕ, l ≤ L →
      ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ ≤ Cprof * (p.R ^ Mp * (1 + t) ^ Mp) := by
    intro l hl
    calc ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖
        ≤ Cprof * (1 + |(Axi.chart p.R τ y).2.2|) ^ Mp := hpb _ hm0 hage l hl
      _ ≤ Cprof * (p.R ^ Mp * (1 + t) ^ Mp) :=
          mul_le_mul_of_nonneg_left hpowM hCprof0
  have hsum : ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ ≤
      ((L : ℝ) + 1) * (Cprof * (p.R ^ Mp * (1 + t) ^ Mp)) := by
    have hkL : ((k : ℝ) + 1) ≤ (L : ℝ) + 1 := by exact_mod_cast (by omega : k + 1 ≤ L + 1)
    calc ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖
        ≤ ∑ _l ∈ Finset.range (k + 1), Cprof * (p.R ^ Mp * (1 + t) ^ Mp) :=
          Finset.sum_le_sum (fun l hl => hbl l (by have := Finset.mem_range.1 hl; omega))
      _ = ((k : ℝ) + 1) * (Cprof * (p.R ^ Mp * (1 + t) ^ Mp)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((L : ℝ) + 1) * (Cprof * (p.R ^ Mp * (1 + t) ^ Mp)) :=
          mul_le_mul_of_nonneg_right hkL (by positivity)
  have hpowk : (1 + t) ^ k * (1 + t) ^ Mp ≤ (1 + t) ^ (Mp + L) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hs1 (by omega)
  have hpre0 : 0 ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ k :=
    mul_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg hρ.le _)) (pow_nonneg (by positivity) _)
  have hpre1 : 0 ≤ CR * Axi.ϱ y ^ (-(1 + (k : ℝ))) := by
    have : 0 ≤ Axi.ϱ y ^ (-(1 + (k : ℝ))) := Real.rpow_nonneg hρ.le _
    positivity
  calc ‖iteratedFDeriv ℝ k (Axi.Nv p.R b τ) y‖
      ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ k *
          ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ := hchart
    _ ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ k *
          (((L : ℝ) + 1) * (Cprof * (p.R ^ Mp * (1 + t) ^ Mp))) :=
        mul_le_mul_of_nonneg_left hsum hpre0
    _ = CR * Axi.ϱ y ^ (-(1 + (k : ℝ))) * ((1 + t) ^ k * (1 + t) ^ Mp) := by
        dsimp [CR]; ring
    _ ≤ CR * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ (Mp + L) :=
        mul_le_mul_of_nonneg_left hpowk hpre1
    _ = CR * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ (Mp + L)) := by ring

/-! ### 3. Far-field drift-cancelled `Sfar` bound and `inletFarAll` -/

/-- Drift-cancelled far-field operator `Sfar e r ν = -ν Δe + (r·∇)e + (e·∇)r`. -/
def Sfar (e : Space → CVec3) (r : Space → Space) (ν : ℝ) : Space → CVec3 :=
  fun x =>
    (-ν) • (∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k))
    + (∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k))
    + (∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k)))

private lemma inletSrc_eq_Sfar_of_drift {p : Params} {i : Fin 2} {U : Set (ℝ × Space)}
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hdrift : ∀ x ∈ U, dτ (p.Efun i) x - (1 / 2 : ℝ) • radialT (p.Efun i) x -
      (1 / 2 : ℝ) • p.Efun i x = 0)
    (τ : ℝ) (x : Space) (hx : (τ, x) ∈ U) :
    inletSrc p i (τ, x) = Sfar (fun w => p.Efun i (τ, w)) (p.raw τ) p.ν x := by
  have hs := inletSrc_slice p i hE τ x
  have hd := hdrift (τ, x) hx
  have hrad : radialT (p.Efun i) (τ, x) =
      ∑ k : Fin 3, x k • fderiv ℝ (fun w => p.Efun i (τ, w)) x (Jets.ek k) := by
    unfold radialT
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [dy_slice (p.Efun i) (hE.differentiable (by simp)) k τ x]
  rw [hrad] at hd
  rw [hs]
  dsimp [Jets.Sfun, Sfar]
  have hzero : dτ (p.Efun i) (τ, x) -
      (1 / 2 : ℝ) • ∑ k : Fin 3, x k • fderiv ℝ (fun w => p.Efun i (τ, w)) x (Jets.ek k) -
      p.ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (Jets.ek k)) x (Jets.ek k) -
      (1 / 2 : ℝ) • p.Efun i (τ, x) =
      (-p.ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (Jets.ek k)) x (Jets.ek k) := by
    rw [neg_smul]
    calc dτ (p.Efun i) (τ, x) -
          (1 / 2 : ℝ) • ∑ k : Fin 3, x k • fderiv ℝ (fun w => p.Efun i (τ, w)) x (Jets.ek k) -
          p.ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (Jets.ek k)) x (Jets.ek k) -
          (1 / 2 : ℝ) • p.Efun i (τ, x)
        = (dτ (p.Efun i) (τ, x) -
            (1 / 2 : ℝ) • ∑ k : Fin 3, x k • fderiv ℝ (fun w => p.Efun i (τ, w)) x (Jets.ek k) -
            (1 / 2 : ℝ) • p.Efun i (τ, x)) -
            p.ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (Jets.ek k)) x (Jets.ek k) := by abel
      _ = 0 - p.ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (Jets.ek k)) x (Jets.ek k) := by
          rw [hd]
      _ = -(p.ν • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun w => p.Efun i (τ, w)) z (Jets.ek k)) x (Jets.ek k)) :=
          zero_sub _
  rw [hzero]

private lemma rpow_neg_one_add_le_neg_three {ρ : ℝ} (hρ : 1 ≤ ρ) (m : ℕ) :
    ρ ^ (-(1 + ((m + 2 : ℕ) : ℝ))) ≤ ρ ^ (-3 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hρ
  push_cast
  linarith

private lemma rpow_neg_split_le_neg_three {ρ : ℝ} (hρ : 1 ≤ ρ) (a b : ℕ) :
    ρ ^ (-(1 + (a : ℝ))) * ρ ^ (-(1 + ((b + 1 : ℕ) : ℝ))) ≤ ρ ^ (-3 : ℝ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  rw [← Real.rpow_add hρ0]
  apply Real.rpow_le_rpow_of_exponent_le hρ
  push_cast
  linarith

private lemma rpow_mul_neg_two_le {t : ℝ} (ht : 1 ≤ t) (M : ℕ) :
    t ^ M * t ^ (-((M + 2 : ℕ) : ℝ)) = t ^ (-2 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  rw [← Real.rpow_natCast t M, ← Real.rpow_add ht0]
  congr 1
  push_cast
  ring

private def projRFar (k : Fin 3) : Space →L[ℝ] ℝ where
  toFun v := v k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (PiLp.continuous_apply 2 (fun _ => ℝ) k).comp continuous_id

private lemma norm_projRFar_le_one (k : Fin 3) : ‖projRFar k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    rw [one_mul]; exact PiLp.norm_apply_le v k)

private def projCFar (k : Fin 3) : CVec3 →L[ℝ] ℂ where
  toFun v := v k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (PiLp.continuous_apply 2 (fun _ => ℂ) k).comp continuous_id

private lemma norm_projCFar_le_one (k : Fin 3) : ‖projCFar k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    rw [one_mul]; exact PiLp.norm_apply_le v k)

private lemma norm_iteratedFDeriv_fderiv_apply_le_at {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {m : ℕ} {y : E}
    (hf : ContDiffAt ℝ (m + 1) f y) {v : E} (hv : ‖v‖ ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun x => fderiv ℝ f x v) y‖ ≤ ‖iteratedFDeriv ℝ (m + 1) f y‖ := by
  have h1 : (fun x => fderiv ℝ f x v) = fun x => (ContinuousLinearMap.apply ℝ F v) (fderiv ℝ f x) := rfl
  rw [h1]
  have hf1 : ContDiffAt ℝ m (fderiv ℝ f) y := hf.fderiv_right le_rfl
  have hle := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ F v)
    hf1 le_rfl (x := y)
  have happ : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun L => by
      simpa [mul_comm] using L.le_opNorm v)
  have hfd : ‖iteratedFDeriv ℝ m (fderiv ℝ f) y‖ = ‖iteratedFDeriv ℝ (m + 1) f y‖ := by
    rw [norm_iteratedFDeriv_fderiv]
  calc ‖iteratedFDeriv ℝ m (fun x => (ContinuousLinearMap.apply ℝ F v) (fderiv ℝ f x)) y‖
      ≤ ‖ContinuousLinearMap.apply ℝ F v‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ f) y‖ := hle
    _ = ‖ContinuousLinearMap.apply ℝ F v‖ * ‖iteratedFDeriv ℝ (m + 1) f y‖ := by rw [hfd]
    _ ≤ 1 * ‖iteratedFDeriv ℝ (m + 1) f y‖ :=
        mul_le_mul_of_nonneg_right (happ.trans hv) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (m + 1) f y‖ := one_mul _

private lemma norm_iteratedFDeriv_Sfar_le {e : Space → CVec3} {r : Space → Space}
    {ν Ce Cr : ℝ} (hν0 : 0 ≤ ν) (hCe : 0 ≤ Ce) (hCr : 0 ≤ Cr)
    {M m : ℕ} {y : Space} (hρ1 : 1 ≤ Axi.ϱ y)
    (he_sm : ContDiff ℝ ∞ e)
    (hr_sm : ContDiff ℝ ∞ r)
    (he : ∀ k ≤ m + 2, ‖iteratedFDeriv ℝ k e y‖ ≤
      Ce * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-((M + 2 : ℕ) : ℝ))))
    (hr : ∀ k ≤ m + 1, ‖iteratedFDeriv ℝ k r y‖ ≤
      Cr * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ M)) :
    ‖iteratedFDeriv ℝ m (Sfar e r ν) y‖ ≤
      (3 * ν * Ce + 3 * (2 ^ m : ℝ) * Ce * Cr + 3 * (2 ^ m : ℝ) * Ce * Cr) *
        Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by
  set ρ : ℝ := Axi.ϱ y
  set t : ℝ := 1 + |y 2| / ρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ1
  have ht1 : 1 ≤ t := by
    have : 0 ≤ |y 2| / ρ := div_nonneg (abs_nonneg _) hρ0.le
    linarith
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht1
  have htM_le : t ^ (-((M + 2 : ℕ) : ℝ)) ≤ t ^ (-2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le ht1
    push_cast
    linarith
  have he_sm' : ContDiff ℝ ∞ (fun x =>
      (-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) := by
    refine ContDiff.const_smul (c := -ν) ?_
    refine ContDiff.sum (fun k _ => ?_)
    exact ((he_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right (m := ∞)
      (by simp) |>.clm_apply contDiff_const
  have he_sm_fderiv : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => fderiv ℝ e z (Jets.ek k)) := fun k =>
    (he_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hr_sm_comp : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => ((r z k : ℝ) : ℂ)) := fun k =>
    (Complex.ofRealCLM.comp (projRFar k)).contDiff.comp hr_sm
  have hterm2_sm : ContDiff ℝ ∞ (fun x =>
      ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) := by
    refine ContDiff.sum (fun k _ => ?_)
    exact (cvecSmulBilin.contDiff.comp (hr_sm_comp k)).clm_apply (he_sm_fderiv k)
  have he_sm_comp : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => e z k) := fun k =>
    (projCFar k).contDiff.comp he_sm
  have hr_sm_fderiv : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => realC (fderiv ℝ r z (Jets.ek k))) := fun k =>
    realCCLM.contDiff.comp ((hr_sm.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hterm3_sm : ContDiff ℝ ∞ (fun x =>
      ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k))) := by
    refine ContDiff.sum (fun k _ => ?_)
    exact (cvecSmulBilin.contDiff.comp (he_sm_comp k)).clm_apply (hr_sm_fderiv k)
  have hf12 : ContDiffAt ℝ m (fun x =>
      ((-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) +
      (∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k))) y :=
    (he_sm'.add hterm2_sm).contDiffAt.of_le (by simp)
  rw [show Sfar e r ν =
      (fun x =>
        ((-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) +
        (∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k))) +
      (fun x => ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k))) from rfl]
  rw [iteratedFDeriv_add_apply hf12 (hterm3_sm.contDiffAt.of_le (by simp))]
  change ‖iteratedFDeriv ℝ m ((fun x => (-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) + (fun x => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k))) y + _‖ ≤ _
  rw [iteratedFDeriv_add_apply (he_sm'.contDiffAt.of_le (by simp)) (hterm2_sm.contDiffAt.of_le (by simp))]
  have hB1 : ‖cvecSmulBilin‖ ≤ 1 := by
    dsimp [cvecSmulBilin]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z =>
      ContinuousLinearMap.opNorm_le_bound _ (by rw [one_mul]; exact norm_nonneg z) (fun v => by
        simp [LinearMap.mk₂_apply, norm_smul]))
  -- Term 1 bound
  have hb1 : ‖iteratedFDeriv ℝ m (fun x =>
      (-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖ ≤
      3 * ν * Ce * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
    change ‖iteratedFDeriv ℝ m ((-ν) • fun x => ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ((ContDiff.sum (fun k _ =>
      ((he_sm_fderiv k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)).contDiffAt.of_le
        (by simp : (m : ℕ∞ω) ≤ ∞))]
    rw [norm_smul, norm_neg, Real.norm_of_nonneg hν0]
    rw [iteratedFDeriv_fun_sum_apply (fun k _ =>
      (((he_sm_fderiv k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).contDiffAt.of_le
        (by simp : (m : ℕ∞ω) ≤ ∞))]
    have hsum_le : ‖∑ k : Fin 3, iteratedFDeriv ℝ m
        (fun x => fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖ ≤
        3 * (Ce * (ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ))) := by
      calc ‖∑ k : Fin 3, iteratedFDeriv ℝ m
              (fun x => fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖
          ≤ ∑ k : Fin 3, ‖iteratedFDeriv ℝ m
              (fun x => fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k : Fin 3, (Ce * (ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ))) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            have h1 := norm_iteratedFDeriv_fderiv_apply_le_at (m := m) (y := y)
              (f := fun z => fderiv ℝ e z (Jets.ek k))
              ((he_sm_fderiv k).contDiffAt.of_le (by simp)) (norm_ek_le_one k)
            have h2 := norm_iteratedFDeriv_fderiv_apply_le_at (m := m + 1) (y := y)
              (f := e) (he_sm.contDiffAt.of_le (by simp)) (norm_ek_le_one k)
            have h3 := he (m + 2) le_rfl
            have h4 : Ce * (ρ ^ (-(1 + ((m + 2 : ℕ) : ℝ))) * t ^ (-((M + 2 : ℕ) : ℝ))) ≤
                Ce * (ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hCe
              exact mul_le_mul (rpow_neg_one_add_le_neg_three hρ1 m) htM_le
                (Real.rpow_nonneg ht_pos.le _) (Real.rpow_nonneg hρ0.le _)
            exact h1.trans (h2.trans (h3.trans h4))
        _ = 3 * (Ce * (ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ))) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; norm_num
    calc ν * ‖∑ k : Fin 3, iteratedFDeriv ℝ m
          (fun x => fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖
        ≤ ν * (3 * (Ce * (ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)))) := mul_le_mul_of_nonneg_left hsum_le hν0
      _ = 3 * ν * Ce * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by ring
  -- Term 2 bound
  have hb2 : ‖iteratedFDeriv ℝ m (fun x =>
      ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y‖ ≤
      3 * (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
    rw [iteratedFDeriv_fun_sum_apply (f := fun k x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k))
      (fun k _ => ((cvecSmulBilin.contDiff.comp (hr_sm_comp k)).clm_apply (he_sm_fderiv k)).contDiffAt.of_le (by simp))]
    calc ‖∑ k : Fin 3, iteratedFDeriv ℝ m
          (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y‖
        ≤ ∑ k : Fin 3, ‖iteratedFDeriv ℝ m
            (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin 3, ((2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have hbil := cvecSmulBilin.norm_iteratedFDeriv_le_of_bilinear
            (hr_sm_comp k) (he_sm_fderiv k) y (by simp : (m : WithTop ℕ∞) ≤ ∞)
          have hsum_le : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j (fun x => ((r x k : ℝ) : ℂ)) y‖ *
              ‖iteratedFDeriv ℝ (m - j) (fun x => fderiv ℝ e x (Jets.ek k)) y‖ ≤
              ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
            have hL1 : ‖iteratedFDeriv ℝ j (fun x => ((r x k : ℝ) : ℂ)) y‖ ≤
                Cr * (ρ ^ (-(1 + (j : ℝ))) * t ^ M) := by
              have hc : (fun x => ((r x k : ℝ) : ℂ)) =
                  (Complex.ofRealCLM.comp (projRFar k)) ∘ r := rfl
              rw [hc]
              have hop : ‖Complex.ofRealCLM.comp (projRFar k)‖ ≤ 1 := by
                refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
                have h1 : ‖Complex.ofRealCLM‖ ≤ 1 := Complex.ofRealCLM.opNorm_le_bound zero_le_one (fun x => by simp)
                exact (mul_le_mul h1 (norm_projRFar_le_one k) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
              have hcl := (Complex.ofRealCLM.comp (projRFar k)).norm_iteratedFDeriv_comp_left
                (hr_sm.contDiffAt) (by simp : (j : ℕ∞ω) ≤ ∞) (x := y)
              have hcl' : ‖iteratedFDeriv ℝ j ((Complex.ofRealCLM.comp (projRFar k)) ∘ r) y‖ ≤
                  ‖iteratedFDeriv ℝ j r y‖ :=
                hcl.trans ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (one_mul _))
              exact hcl'.trans (hr j (by omega))
            have hL2 : ‖iteratedFDeriv ℝ (m - j) (fun x => fderiv ℝ e x (Jets.ek k)) y‖ ≤
                Ce * (ρ ^ (-(1 + ((m - j + 1 : ℕ) : ℝ))) * t ^ (-((M + 2 : ℕ) : ℝ))) := by
              have hfd := norm_iteratedFDeriv_fderiv_apply_le_at (m := m - j) (y := y)
                (f := e) (he_sm.contDiffAt.of_le (by simp)) (norm_ek_le_one k)
              exact hfd.trans (he (m - j + 1) (by omega))
            have hprod : ‖iteratedFDeriv ℝ j (fun x => ((r x k : ℝ) : ℂ)) y‖ *
                ‖iteratedFDeriv ℝ (m - j) (fun x => fderiv ℝ e x (Jets.ek k)) y‖ ≤
                Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
              calc ‖iteratedFDeriv ℝ j (fun x => ((r x k : ℝ) : ℂ)) y‖ *
                    ‖iteratedFDeriv ℝ (m - j) (fun x => fderiv ℝ e x (Jets.ek k)) y‖
                  ≤ (Cr * (ρ ^ (-(1 + (j : ℝ))) * t ^ M)) *
                    (Ce * (ρ ^ (-(1 + ((m - j + 1 : ℕ) : ℝ))) * t ^ (-((M + 2 : ℕ) : ℝ)))) :=
                      mul_le_mul hL1 hL2 (norm_nonneg _) (by positivity)
                _ = Ce * Cr * (ρ ^ (-(1 + (j : ℝ))) * ρ ^ (-(1 + ((m - j + 1 : ℕ) : ℝ)))) *
                    (t ^ M * t ^ (-((M + 2 : ℕ) : ℝ))) := by ring
                _ ≤ Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
                    rw [rpow_mul_neg_two_le ht1 M]
                    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht_pos.le _)
                    apply mul_le_mul_of_nonneg_left (rpow_neg_split_le_neg_three hρ1 j (m - j))
                    exact mul_nonneg hCe hCr
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
          have hbin : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) =
              (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
            rw [← Finset.sum_mul]
            have h2m : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) = (2 ^ m : ℝ) := by
              exact_mod_cast Nat.sum_range_choose m
            rw [h2m]; ring
          calc ‖iteratedFDeriv ℝ m (fun x => ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y‖
              ≤ ‖cvecSmulBilin‖ * _ := hbil
            _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hB1 (Finset.sum_nonneg (fun _ _ => by positivity))
            _ = _ := one_mul _
            _ ≤ _ := hsum_le
            _ = _ := hbin
      _ = 3 * (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  -- Term 3 bound
  have hb3 : ‖iteratedFDeriv ℝ m (fun x =>
      ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖ ≤
      3 * (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
    rw [iteratedFDeriv_fun_sum_apply (f := fun k x => e x k • realC (fderiv ℝ r x (Jets.ek k)))
      (fun k _ => ((cvecSmulBilin.contDiff.comp (he_sm_comp k)).clm_apply (hr_sm_fderiv k)).contDiffAt.of_le (by simp))]
    calc ‖∑ k : Fin 3, iteratedFDeriv ℝ m
          (fun x => e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖
        ≤ ∑ k : Fin 3, ‖iteratedFDeriv ℝ m
            (fun x => e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin 3, ((2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have hbil := cvecSmulBilin.norm_iteratedFDeriv_le_of_bilinear
            (he_sm_comp k) (hr_sm_fderiv k) y (by simp : (m : WithTop ℕ∞) ≤ ∞)
          have hsum_le : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j (fun x => e x k) y‖ *
              ‖iteratedFDeriv ℝ (m - j) (fun x => realC (fderiv ℝ r x (Jets.ek k))) y‖ ≤
              ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
            have hL1 : ‖iteratedFDeriv ℝ j (fun x => e x k) y‖ ≤
                Ce * (ρ ^ (-(1 + (j : ℝ))) * t ^ (-((M + 2 : ℕ) : ℝ))) := by
              have hc : (fun x => e x k) = (projCFar k) ∘ e := rfl
              rw [hc]
              have hcl := (projCFar k).norm_iteratedFDeriv_comp_left
                (he_sm.contDiffAt) (by simp : (j : ℕ∞ω) ≤ ∞) (x := y)
              have hcl' : ‖iteratedFDeriv ℝ j ((projCFar k) ∘ e) y‖ ≤ ‖iteratedFDeriv ℝ j e y‖ :=
                hcl.trans ((mul_le_mul_of_nonneg_right (norm_projCFar_le_one k) (norm_nonneg _)).trans_eq (one_mul _))
              exact hcl'.trans (he j (by omega))
            have hL2 : ‖iteratedFDeriv ℝ (m - j) (fun x => realC (fderiv ℝ r x (Jets.ek k))) y‖ ≤
                Cr * (ρ ^ (-(1 + ((m - j + 1 : ℕ) : ℝ))) * t ^ M) := by
              have hc : (fun x => realC (fderiv ℝ r x (Jets.ek k))) =
                  realCCLM ∘ (fun x => fderiv ℝ r x (Jets.ek k)) := rfl
              rw [hc]
              have hcl := realCCLM.norm_iteratedFDeriv_comp_left
                (((hr_sm.fderiv_right (m := ∞) (by simp)).clm_apply
                  (contDiff_const (c := Jets.ek k))).contDiffAt)
                (by simp : ((m - j : ℕ) : ℕ∞ω) ≤ ∞) (x := y)
              have hcl' : ‖iteratedFDeriv ℝ (m - j) (realCCLM ∘ fun x => fderiv ℝ r x (Jets.ek k)) y‖ ≤
                  ‖iteratedFDeriv ℝ (m - j) (fun x => fderiv ℝ r x (Jets.ek k)) y‖ :=
                hcl.trans ((mul_le_mul_of_nonneg_right norm_realCCLM_le_one (norm_nonneg _)).trans_eq (one_mul _))
              have hfd := norm_iteratedFDeriv_fderiv_apply_le_at (m := m - j) (y := y)
                (f := r) (hr_sm.contDiffAt.of_le (by simp)) (norm_ek_le_one k)
              exact hcl'.trans (hfd.trans (hr (m - j + 1) (by omega)))
            have hprod : ‖iteratedFDeriv ℝ j (fun x => e x k) y‖ *
                ‖iteratedFDeriv ℝ (m - j) (fun x => realC (fderiv ℝ r x (Jets.ek k))) y‖ ≤
                Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
              calc ‖iteratedFDeriv ℝ j (fun x => e x k) y‖ *
                    ‖iteratedFDeriv ℝ (m - j) (fun x => realC (fderiv ℝ r x (Jets.ek k))) y‖
                  ≤ (Ce * (ρ ^ (-(1 + (j : ℝ))) * t ^ (-((M + 2 : ℕ) : ℝ)))) *
                    (Cr * (ρ ^ (-(1 + ((m - j + 1 : ℕ) : ℝ))) * t ^ M)) :=
                      mul_le_mul hL1 hL2 (norm_nonneg _) (by positivity)
                _ = Ce * Cr * (ρ ^ (-(1 + (j : ℝ))) * ρ ^ (-(1 + ((m - j + 1 : ℕ) : ℝ)))) *
                    (t ^ M * t ^ (-((M + 2 : ℕ) : ℝ))) := by ring
                _ ≤ Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
                    rw [rpow_mul_neg_two_le ht1 M]
                    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht_pos.le _)
                    apply mul_le_mul_of_nonneg_left (rpow_neg_split_le_neg_three hρ1 j (m - j))
                    exact mul_nonneg hCe hCr
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
          have hbin : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) =
              (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
            rw [← Finset.sum_mul]
            have h2m : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) = (2 ^ m : ℝ) := by
              exact_mod_cast Nat.sum_range_choose m
            rw [h2m]; ring
          calc ‖iteratedFDeriv ℝ m (fun x => e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖
              ≤ ‖cvecSmulBilin‖ * _ := hbil
            _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hB1 (Finset.sum_nonneg (fun _ _ => by positivity))
            _ = _ := one_mul _
            _ ≤ _ := hsum_le
            _ = _ := hbin
      _ = 3 * (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  calc ‖iteratedFDeriv ℝ m (fun x =>
          (-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y +
        iteratedFDeriv ℝ m (fun x =>
          ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y +
        iteratedFDeriv ℝ m (fun x =>
          ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖
      ≤ ‖iteratedFDeriv ℝ m (fun x =>
          (-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y +
        iteratedFDeriv ℝ m (fun x =>
          ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y‖ +
        ‖iteratedFDeriv ℝ m (fun x =>
          ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖ := norm_add_le _ _
    _ ≤ (‖iteratedFDeriv ℝ m (fun x =>
          (-ν) • ∑ k : Fin 3, fderiv ℝ (fun z => fderiv ℝ e z (Jets.ek k)) x (Jets.ek k)) y‖ +
        ‖iteratedFDeriv ℝ m (fun x =>
          ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • fderiv ℝ e x (Jets.ek k)) y‖) +
        ‖iteratedFDeriv ℝ m (fun x =>
          ∑ k : Fin 3, e x k • realC (fderiv ℝ r x (Jets.ek k))) y‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (3 * ν * Ce * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) +
        3 * (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ)) +
        3 * (2 ^ m : ℝ) * Ce * Cr * ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) :=
        add_le_add (add_le_add hb1 hb2) hb3
    _ = (3 * ν * Ce + 3 * (2 ^ m : ℝ) * Ce * Cr + 3 * (2 ^ m : ℝ) * Ce * Cr) *
        ρ ^ (-3 : ℝ) * t ^ (-2 : ℝ) := by ring

private lemma inletDriftFar_direct (lam : ℂ) (q : Planar.Profile) (hq : Planar.IsGrowingEigenpair lam q)
    (dm dp : ℝ) (_hdm : 0 < dm) :
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.mode = q →
      ∀ i : Fin 2, ∃ R0 : ℝ, 0 < R0 ∧ ∀ (τ : ℝ) (y : Space), R0 < Axi.ϱ y →
        dτ (p.Efun i) (τ, y) - (1 / 2 : ℝ) • radialT (p.Efun i) (τ, y) -
          (1 / 2 : ℝ) • p.Efun i (τ, y) = 0 := by
  intro p d hreg hν hm i
  have hp : 0 < p.R := p.R_pos
  have hH : 0 < p.H := p.H_pos
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  obtain ⟨C, κ, N, -, -, hper⟩ := UnforcedLeray.Short.IIb.frozenStreamBounds lam q hq 0
  have hfro : ContDiff ℝ ∞ (p.frozenStream i) :=
    UnforcedLeray.Short.IIb.inletCD_frozenStream (hper p.c hc1).1 hm i
  have hI := inlet_contDiff_joint lam q hq hreg hν hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  have hEd : ∀ x, DifferentiableAt ℝ (p.Efun i) x := fun x => hE.differentiable (by simp) x
  refine ⟨2 * p.R / Real.sqrt p.H, div_pos (by linarith) (Real.sqrt_pos.2 hH), fun τ y hR0 => ?_⟩
  have hR0pos : 0 < 2 * p.R / Real.sqrt p.H := div_pos (by linarith) (Real.sqrt_pos.2 hH)
  have hy : 0 < Axi.ϱ y := lt_trans hR0pos hR0
  have hsq : (2 * p.R / Real.sqrt p.H) ^ 2 * p.H = 4 * p.R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hH.le]
    field_simp
    norm_num
  have hA : Axi.age p.R y < p.H / 4 := by
    unfold Axi.age
    rw [div_lt_iff₀ (pow_pos hy 2)]
    have hlt : (2 * p.R / Real.sqrt p.H) ^ 2 < Axi.ϱ y ^ 2 :=
      pow_lt_pow_left₀ hR0 hR0pos.le two_ne_zero
    nlinarith
  have hev : ∀ᶠ l in 𝓝 (1 : ℝ), 0 < l ∧ Axi.age p.R (l • y) < p.H / 4 := by
    have h1 : ∀ᶠ l in 𝓝 (1 : ℝ), Axi.age p.R y / l ^ 2 < p.H / 4 := by
      have hc : ContinuousAt (fun l : ℝ => Axi.age p.R y / l ^ 2) 1 :=
        continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
      exact hc.eventually_lt continuousAt_const (by simpa using hA)
    have h2 : ∀ᶠ l in 𝓝 (1 : ℝ), 0 < l := Ioi_mem_nhds zero_lt_one
    filter_upwards [h1, h2] with l hl1 hl2
    exact ⟨hl2, by rw [age_smul' hl2 hy]; exact hl1⟩
  have hstep : ∀ s t : ℝ, s < p.H / 4 → t < p.H / 4 → ∀ ξ η : ℝ,
      p.inletProfile i (s, (ξ, η)) = p.inletProfile i (t, (ξ, η)) :=
    fun s t hs ht ξ η => inletProfile_indep hfro hs ht ξ η
  have hfg : (fun l : ℝ => p.Efun i (τ + 2 * Real.log l, y)) =ᶠ[𝓝 (1 : ℝ)]
      (fun l : ℝ => l • p.Efun i (τ, l • y)) := by
    filter_upwards [hev] with l hl
    exact Efun_scale p i τ hl.1 hy hA hl.2 hstep
  have hlog : HasDerivAt (fun l : ℝ => τ + 2 * Real.log l) (2 * (1 : ℝ)⁻¹) 1 :=
    ((Real.hasDerivAt_log one_ne_zero).const_mul 2).const_add τ
  have hpair : HasDerivAt (fun l : ℝ => (τ + 2 * Real.log l, y))
      ((2 * (1 : ℝ)⁻¹, (0 : Space))) 1 :=
    hlog.prodMk (hasDerivAt_const (1 : ℝ) y)
  have hpt : τ + 2 * Real.log 1 = τ := by simp
  have hEd' : HasFDerivAt (p.Efun i) (fderiv ℝ (p.Efun i) (τ, y))
      (τ + 2 * Real.log 1, y) := by
    rw [hpt]
    exact (hEd (τ, y)).hasFDerivAt
  have hf := hEd'.comp_hasDerivAt (1 : ℝ) hpair
  have hdτ : fderiv ℝ (p.Efun i) (τ, y) (2 * (1 : ℝ)⁻¹, (0 : Space)) =
      (2 : ℝ) • dτ (p.Efun i) (τ, y) := by
    rw [show ((2 : ℝ) * (1 : ℝ)⁻¹, (0 : Space)) =
      (2 : ℝ) • ((1 : ℝ), (0 : Space)) by simp, map_smul]
    rfl
  rw [hdτ] at hf
  have hkd : DifferentiableAt ℝ (fun x : Space => p.Efun i (τ, x)) y := by
    have h1 : DifferentiableAt ℝ (fun x : Space => ((τ, x) : ℝ × Space)) y :=
      (differentiableAt_const τ).prodMk differentiableAt_id
    exact (hEd (τ, y)).comp y h1
  have hline : HasDerivAt (fun l : ℝ => l • y) ((1 : ℝ) • y) 1 :=
    (hasDerivAt_id' (x := (1 : ℝ))).smul_const y
  have hkf : HasFDerivAt (fun x : Space => p.Efun i (τ, x))
      (fderiv ℝ (fun x : Space => p.Efun i (τ, x)) y) ((1 : ℝ) • y) := by
    rw [one_smul]
    exact hkd.hasFDerivAt
  have hgk := hkf.comp_hasDerivAt (1 : ℝ) hline
  have hgD := (hasDerivAt_id' (x := (1 : ℝ))).smul hgk
  have heq := hf.unique (hgD.congr_of_eventuallyEq hfg)
  simp only [one_smul, Function.comp_apply] at heq
  have hkF : HasFDerivAt (fun x : Space => p.Efun i (τ, x))
      ((fderiv ℝ (p.Efun i) (τ, y)).comp
        ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y :=
    (hEd (τ, y)).hasFDerivAt.comp y ((hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y))
  have hk_eq : fderiv ℝ (fun x : Space => p.Efun i (τ, x)) y y =
      fderiv ℝ (p.Efun i) (τ, y) (0, y) := by
    rw [hkF.fderiv]
    simp
  have hy_sum : y = ∑ j : Fin 3, y j • UnforcedLeray.coordinateVector j := by
    ext k
    fin_cases k <;> simp [UnforcedLeray.coordinateVector, Fin.sum_univ_three]
  have hy_eq : ((0 : ℝ), y) = ∑ j : Fin 3, y j • ((0 : ℝ), UnforcedLeray.coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      exact hy_sum
  have hrad : radialT (p.Efun i) (τ, y) = fderiv ℝ (p.Efun i) (τ, y) (0, y) := by
    rw [hy_eq, map_sum]
    simp only [map_smul, radialT, UnforcedLeray.PhaseSpace.dy]
  rw [hk_eq, ← hrad] at heq
  have hdiv : dτ (p.Efun i) (τ, y) = (1 / 2 : ℝ) • ((2 : ℝ) • dτ (p.Efun i) (τ, y)) := by
    rw [smul_smul]; norm_num
  rw [hdiv, heq]
  module

private lemma inletFarAll_calc
    (ν : ℝ) (hν0 : 0 ≤ ν)
    (e s : ℝ × Space → CVec3) (r : ℝ → Space → Space)
    (hE : ContDiff ℝ ∞ e) (hSrc : ContDiff ℝ ∞ s)
    (hRaw_all : ContDiff ℝ ∞ (fun x : ℝ × Space => r x.1 x.2))
    (m : ℕ) (β : Fin m → Fin 3)
    (R0d R0r R0e : ℝ) (M : ℕ) (CR Ce : ℝ) (hCR0 : 0 ≤ CR) (hCe0 : 0 ≤ Ce)
    (hEqSfar : ∀ τ : ℝ, ∀ y : Space, R0d < Axi.ϱ y →
      s (τ, y) = Sfar (fun w => e (τ, w)) (r τ) ν y)
    (hraw : ∀ (τ : ℝ) (y : Space), R0r < Axi.ϱ y → ∀ k ≤ m + 1,
      ‖iteratedFDeriv ℝ k (r τ) y‖ ≤
        CR * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ M))
    (he : ∀ (τ : ℝ) (y : Space), R0e < Axi.ϱ y → ∀ k ≤ m + 2,
      ‖iteratedFDeriv ℝ k (fun w : Space => e (τ, w)) y‖ ≤
        Ce * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-((M + 2 : ℕ) : ℝ))))
    (τ : ℝ) (y : Space) (hy_d : R0d < Axi.ϱ y) (hy_r : R0r < Axi.ϱ y)
    (hy_e : R0e < Axi.ϱ y) (hy_1 : 1 ≤ Axi.ϱ y) :
    ‖iterDyRev β s (τ, y)‖ ≤
      (3 * ν * Ce + 3 * (2 ^ m : ℝ) * Ce * CR + 3 * (2 ^ m : ℝ) * Ce * CR) *
        Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by
  have hU_open : IsOpen {x : ℝ × Space | R0d < Axi.ϱ x.2} :=
    isOpen_lt continuous_const (Axi.continuous_ϱ.comp continuous_snd)
  have hU_space_open : IsOpen {w : Space | R0d < Axi.ϱ w} :=
    isOpen_lt continuous_const Axi.continuous_ϱ
  have hev : (fun w : Space => s (τ, w)) =ᶠ[𝓝 y]
      Sfar (fun w => e (τ, w)) (r τ) ν :=
    Filter.eventuallyEq_of_mem (hU_space_open.mem_nhds hy_d) (fun w hw => hEqSfar τ w hw)
  have hdy : ‖iterDyRev β s (τ, y)‖ ≤
      ‖iteratedFDeriv ℝ m (Sfar (fun w => e (τ, w)) (r τ) ν) y‖ := by
    have hslice := RawIterEnvSub.norm_iterDyRev_le_slice (a := τ) hU_open hSrc.contDiffOn β hy_d
    rwa [(hev.iteratedFDeriv ℝ m).eq_of_nhds] at hslice
  have hE_slice : ContDiff ℝ ∞ (fun w : Space => e (τ, w)) :=
    hE.comp (contDiff_const.prodMk contDiff_id)
  have hRaw_slice : ContDiff ℝ ∞ (r τ) :=
    hRaw_all.comp (contDiff_const.prodMk contDiff_id)
  have hSfar := norm_iteratedFDeriv_Sfar_le hν0 hCe0 hCR0 (M := M) (m := m) hy_1
    hE_slice hRaw_slice
    (fun k hk => he τ y hy_e k hk) (fun k hk => hraw τ y hy_r k hk)
  exact hdy.trans hSfar

theorem inletFarAll (lam : ℂ) (q : Planar.Profile) (hq : Planar.IsGrowingEigenpair lam q)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.mode = q →
      ∀ (i : Fin 2) (m : ℕ) (β : Fin m → Fin 3),
        ∃ C R0 : ℝ, 0 < R0 ∧ ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space,
          R0 < Axi.ϱ y →
            ‖iterDyRev β (inletSrc p i) (τ, y)‖ ≤
              C * Axi.ϱ y ^ (-3 : ℝ) * (1 + |y 2| / Axi.ϱ y) ^ (-2 : ℝ) := by
  obtain ⟨ν_r, hν_r, Hraw⟩ := rawFarJetsAll dm dp hdm
  obtain ⟨ν_s, hν_s, Hsm⟩ := rawJointSmooth dm dp hdm
  have HE := inletEFarHomAll lam q hq dm dp hdm
  refine ⟨min (min ν_r ν_s) 1, lt_min (lt_min hν_r hν_s) one_pos, fun p d hreg hν hmode i m β => ?_⟩
  have hνr : p.ν ≤ ν_r := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνs : p.ν ≤ ν_s := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  obtain ⟨R0d, hR0d_pos, hdrift_pt⟩ := inletDriftFar_direct lam q hq dm dp hdm p d hreg hν1 hmode i
  have hdrift : ∀ x ∈ {z : ℝ × Space | R0d < Axi.ϱ z.2},
      dτ (p.Efun i) x - (1 / 2 : ℝ) • radialT (p.Efun i) x -
        (1 / 2 : ℝ) • p.Efun i x = 0 := fun x hx => hdrift_pt x.1 x.2 hx
  obtain ⟨CR, R0r, M, hR0r_pos, hCR0, _, hraw⟩ := Hraw p d hreg hνr (m + 1)
  obtain ⟨Ce, R0e, hR0e_pos, he⟩ := HE p d hreg hν1 hmode i (m + 2) (M + 2)
  have hE_sm : ContDiff ℝ ∞ (p.Efun i) :=
    contDiff_realC_meas.comp (inlet_contDiff_joint lam q hq hreg hν1 hmode i)
  have hRaw_all : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) := Hsm p d hreg hνs
  have hSrc : ContDiff ℝ ∞ (inletSrc p i) := inletSrc_contDiff hE_sm hRaw_all
  set R0 : ℝ := max (max R0d R0r) (max R0e 1)
  have hR0_pos : 0 < R0 := lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _))
  have hCe0 : 0 ≤ max Ce 0 := le_max_right _ _
  refine ⟨3 * p.ν * max Ce 0 + 3 * (2 ^ m : ℝ) * max Ce 0 * CR +
      3 * (2 ^ m : ℝ) * max Ce 0 * CR, R0, hR0_pos, fun τ _hτ y hy => ?_⟩
  have hy_d : R0d < Axi.ϱ y := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hy
  have hy_r : R0r < Axi.ϱ y := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hy
  have hy_e : R0e < Axi.ϱ y := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hy
  have hy_1 : 1 ≤ Axi.ϱ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy.le
  exact inletFarAll_calc p.ν p.ν_pos.le (p.Efun i) (inletSrc p i) p.raw hE_sm hSrc hRaw_all
    m β R0d R0r R0e M CR (max Ce 0) hCR0 hCe0
    (fun τ' y' hy' => inletSrc_eq_Sfar_of_drift hE_sm hdrift τ' y' hy')
    hraw (fun τ' y' hy' k hk => (he τ' y' hy' k hk).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (mul_nonneg (Real.rpow_nonneg (Axi.ϱ_nonneg _) _)
          (Real.rpow_nonneg (add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (Axi.ϱ_nonneg _))) _))))
    τ y hy_d hy_r hy_e hy_1

end UnforcedLeray.Short.IIb.IterInletSub
