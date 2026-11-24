import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `NearMaskedFreeBoundC` from the three masked pieces (source 4022-4031, bins 3974-3977)

Proves `nearMaskedFreeBoundC_of` (target `NearMaskedFreeBoundC`, `NearInst/Targets.lean`) from
`MaskedLowerPiece` (output below `sm = ε^b`), `MaskedBinPiece` (the bins `[l_j, l_{j+1})`),
`MaskedUpperPiece` (output above `S = ε^{-b}`) and `OutBandPartition` (the output partition).

At a level `p` with `ε = e^{-d/ν}`, `sm = ε^b < S = ε^{-b}`, `N = binCount sm S δ`:
* `g⁻¹ S_N g = gainRestrS (ageBelow sm) S_N + Σ_{j<N} gainRestrS (ageBand l_j l_{j+1}) S_N
  + gainRestrS (ageAbove S) S_N` (`OutBandPartition`, pushed through `g⁻¹ · g`);
* `log (S/sm) = 2bd/ν ≤ 2b|d₊|/ν`, so `N ≤ K₂ ν⁻¹` with `K₂ = 8b|d₊|/δ + 2`;
* the constants are merged with `ν⁻¹ ≥ 1` (`ν ≤ 1`) and `e^{η_δ/ν} ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- Three-term triangle inequality. -/
theorem norm_three_add {E : Type*} [NormedAddCommGroup E] (A B C : E) :
    ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
  linarith [norm_add_le (A + B) C, norm_add_le A B]

/-- A finite sum of `≤ M` norms: `‖∑ f j‖ ≤ #s · M`. -/
theorem norm_sum_bound {E : Type*} [NormedAddCommGroup E] (s : Finset ℕ) (f : ℕ → E) (M : ℝ)
    (hM : ∀ j ∈ s, ‖f j‖ ≤ M) : ‖∑ j ∈ s, f j‖ ≤ (s.card : ℝ) * M := by
  refine (norm_sum_le s f).trans ?_
  have h := Finset.sum_le_card_nsmul s (fun j => ‖f j‖) M hM
  simpa [nsmul_eq_mul] using h

/-- **`near:masked-free-bound`** (source 4022-4031): the masked free bound from the lower, bin and
upper pieces and the output partition. -/
theorem nearMaskedFreeBoundC_of (hL : MaskedLowerPiece) (hB : MaskedBinPiece)
    (hU : MaskedUpperPiece) (hP : OutBandPartition) : NearMaskedFreeBoundC := by
  intro P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C1, k1, ν1, hν1, hL'⟩ := hL P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C2, k2, ν2, hν2, hB'⟩ := hB P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C3, k3, ν3, hν3, hU'⟩ := hU P hPl Kset hK hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  have hγ : 0 < P.eigenvalue.re := hPl.eigenpair.re_pos
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = 8 * b * |dp| / δ + 2 := ⟨_, rfl⟩
  have hK2nn : 0 ≤ K2 := by
    rw [hK2]
    have h0 : 0 ≤ 8 * b * |dp| / δ :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb.le) (abs_nonneg _)) hδ.le
    linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max k1 (max k2 k3) + 1 := ⟨_, rfl⟩
  have hk1 : k1 ≤ k := by rw [hk]; exact (le_max_left _ _).trans (Nat.le_succ _)
  have hk2 : k2 + 1 ≤ k := by
    rw [hk]; exact Nat.add_le_add_right ((le_max_left k2 k3).trans (le_max_right k1 _)) 1
  have hk3 : k3 ≤ k := by
    rw [hk]; exact (le_max_right k2 k3).trans ((le_max_right k1 _).trans (Nat.le_succ _))
  refine ⟨|C1| + K2 * |C2| + |C3|, k, min ν1 (min ν2 (min ν3 1)),
    lt_min hν1 (lt_min hν2 (lt_min hν3 one_pos)), ?_⟩
  intro p d hBG hpν ρb hρ hρ1 μ hμ SN hact
  have hν := p.ν_pos
  have hεpos := p.ε_pos
  have hd : 0 < d := lt_of_lt_of_le hBG.dm_pos hBG.dm_le
  have hεlt : p.ε < 1 := by
    rw [hBG.eps_eq, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) hν
  have hlog : Real.log p.ε = -d / p.ν := by rw [hBG.eps_eq, Real.log_exp]
  have hη : 0 ≤ etaDelta P.eigenvalue.re δ := by
    unfold etaDelta
    apply mul_nonneg hγ.le
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.2 (by linarith)) (Real.cosh_pos _).le
  have ht0 : 0 ≤ p.ν⁻¹ := inv_nonneg.2 hν.le
  have hνp1 : p.ν ≤ ν1 := hpν.trans (min_le_left _ _)
  have hνp2 : p.ν ≤ ν2 := hpν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνp3 : p.ν ≤ ν3 :=
    hpν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνp4 : p.ν ≤ 1 :=
    hpν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hi : 1 ≤ p.ν⁻¹ := by
    rw [le_inv_comm₀ one_pos hν, inv_one]; exact hνp4
  have he1 : 1 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
    Real.one_le_exp (div_nonneg hη hν.le)
  have hX0 : 0 ≤ p.ν⁻¹ ^ k := pow_nonneg ht0 k
  have hXe : p.ν⁻¹ ^ k ≤ p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
    le_mul_of_one_le_right hX0 he1
  -- the masked pieces at this level
  have hLres : ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBelow (p.ε ^ b)) SN‖
      ≤ C1 * p.ν⁻¹ ^ k1 :=
    hL' p d hBG hνp1 ρb hρ hρ1 μ hμ SN hact
  have hCres : ‖gainRestrS P.eigenvalue.re p.ν_pos (ageAbove (p.ε ^ (-b))) SN‖
      ≤ C3 * p.ν⁻¹ ^ k3 :=
    hU' p d hBG hνp3 ρb hρ hρ1 μ hμ SN hact
  have hsmpos : 0 < p.ε ^ b := Real.rpow_pos_of_pos hεpos b
  have hSpos : 0 < p.ε ^ (-b) := Real.rpow_pos_of_pos hεpos (-b)
  have hbb : -b < b := by linarith
  have hSm : p.ε ^ b < p.ε ^ (-b) := Real.rpow_lt_rpow_of_exponent_gt hεpos hεlt hbb
  -- the bin count
  have hlogS : Real.log (p.ε ^ (-b) / p.ε ^ b) = 2 * b * d / p.ν := by
    rw [Real.log_div hSpos.ne' hsmpos.ne', Real.log_rpow hεpos, Real.log_rpow hεpos, hlog]
    ring
  have hcnt := binCount_lt hsmpos hSm.le hδ
  rw [hlogS] at hcnt
  have hbd : 8 * b * d ≤ 8 * b * |dp| :=
    mul_le_mul_of_nonneg_left (hBG.le_dp.trans (le_abs_self dp)) (by linarith)
  have h3 : 8 * b * d / δ ≤ 8 * b * |dp| / δ := div_le_div_of_nonneg_right hbd hδ.le
  have key : 4 * (2 * b * d / p.ν) / δ + 2 ≤ K2 * p.ν⁻¹ := by
    have e1 : 4 * (2 * b * d / p.ν) / δ = (8 * b * d / δ) * p.ν⁻¹ := by ring
    have e2 : K2 * p.ν⁻¹ = (8 * b * |dp| / δ) * p.ν⁻¹ + 2 * p.ν⁻¹ := by rw [hK2]; ring
    rw [e1, e2]
    have h4 := mul_le_mul_of_nonneg_right h3 ht0
    linarith
  have hNbd : (binCount (p.ε ^ b) (p.ε ^ (-b)) δ : ℝ) ≤ K2 * p.ν⁻¹ := hcnt.le.trans key
  have hN0 : binCount (p.ε ^ b) (p.ε ^ (-b)) δ ≠ 0 := (binCount_pos _ _ _).ne'
  -- the outer decomposition of `g⁻¹ S_N g`
  have hsplit : gainConjS P.eigenvalue.re p.ν_pos SN =
      gainRestrS P.eigenvalue.re p.ν_pos (ageBelow (p.ε ^ b)) SN
        + (∑ j ∈ Finset.range (binCount (p.ε ^ b) (p.ε ^ (-b)) δ),
            gainRestrS P.eigenvalue.re p.ν_pos
              (ageBand (binEdge (p.ε ^ b) (p.ε ^ (-b)) (binCount (p.ε ^ b) (p.ε ^ (-b)) δ) j)
                (binEdge (p.ε ^ b) (p.ε ^ (-b)) (binCount (p.ε ^ b) (p.ε ^ (-b)) δ) (j + 1))) SN)
        + gainRestrS P.eigenvalue.re p.ν_pos (ageAbove (p.ε ^ (-b))) SN := by
    ext F
    have hO := hP p.c (p.ε ^ b) (p.ε ^ (-b)) δ hsmpos hSm hδ
      (SN (gainEquiv p.c mZ ρb P.eigenvalue.re p.ν_pos F))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, gainRestrS,
      gainConjS_apply, ContinuousLinearMap.comp_apply]
    conv_lhs => rw [← hO]
    rw [map_add, map_add, map_sum]
  -- each bin
  have hbin : ∀ j ∈ Finset.range (binCount (p.ε ^ b) (p.ε ^ (-b)) δ),
      ‖gainRestrS P.eigenvalue.re p.ν_pos
          (ageBand (binEdge (p.ε ^ b) (p.ε ^ (-b)) (binCount (p.ε ^ b) (p.ε ^ (-b)) δ) j)
            (binEdge (p.ε ^ b) (p.ε ^ (-b)) (binCount (p.ε ^ b) (p.ε ^ (-b)) δ) (j + 1))) SN‖
        ≤ |C2| * p.ν⁻¹ ^ k2 * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := by
    intro j hj
    have hjN : j + 1 ≤ binCount (p.ε ^ b) (p.ε ^ (-b)) δ := Finset.mem_range.1 hj
    have hl : 0 < binEdge (p.ε ^ b) (p.ε ^ (-b)) (binCount (p.ε ^ b) (p.ε ^ (-b)) δ) j :=
      lt_of_lt_of_le hsmpos (binEdge_ge hsmpos hSm.le _ j)
    have h1 := hB' p d hBG hνp2 ρb hρ hρ1 μ hμ SN hact _ _ hl
      (binEdge_lt_succ hsmpos hSm hN0 j) (binEdge_succ_le hsmpos hSm.le hδ j)
      (binEdge_le_last hsmpos hSm.le hjN)
    exact h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (pow_nonneg ht0 _)) (Real.exp_pos _).le)
  have hS := norm_sum_bound _ _ _ hbin
  rw [Finset.card_range] at hS
  -- assembly
  have hYY : p.ν⁻¹ * p.ν⁻¹ ^ k2 ≤ p.ν⁻¹ ^ k := by
    rw [← pow_succ']; exact pow_le_pow_right₀ hi hk2
  have hM0 : 0 ≤ |C2| * p.ν⁻¹ ^ k2 * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg ht0 _)) (Real.exp_pos _).le
  have hcoef0 : 0 ≤ K2 * |C2| * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
    mul_nonneg (mul_nonneg hK2nn (abs_nonneg _)) (Real.exp_pos _).le
  have hA' : ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBelow (p.ε ^ b)) SN‖
      ≤ |C1| * (p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) :=
    calc _ ≤ C1 * p.ν⁻¹ ^ k1 := hLres
      _ ≤ |C1| * p.ν⁻¹ ^ k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) (pow_nonneg ht0 _)
      _ ≤ |C1| * p.ν⁻¹ ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hi hk1) (abs_nonneg _)
      _ ≤ |C1| * (p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) :=
          mul_le_mul_of_nonneg_left hXe (abs_nonneg _)
  have hC' : ‖gainRestrS P.eigenvalue.re p.ν_pos (ageAbove (p.ε ^ (-b))) SN‖
      ≤ |C3| * (p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) :=
    calc _ ≤ C3 * p.ν⁻¹ ^ k3 := hCres
      _ ≤ |C3| * p.ν⁻¹ ^ k3 := mul_le_mul_of_nonneg_right (le_abs_self C3) (pow_nonneg ht0 _)
      _ ≤ |C3| * p.ν⁻¹ ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hi hk3) (abs_nonneg _)
      _ ≤ |C3| * (p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) :=
          mul_le_mul_of_nonneg_left hXe (abs_nonneg _)
  rw [hsplit]
  refine (norm_three_add _ _ _).trans ?_
  have hSb := hS.trans (show (binCount (p.ε ^ b) (p.ε ^ (-b)) δ : ℝ) *
      (|C2| * p.ν⁻¹ ^ k2 * Real.exp (etaDelta P.eigenvalue.re δ / p.ν))
      ≤ K2 * |C2| * (p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) from
    calc (binCount (p.ε ^ b) (p.ε ^ (-b)) δ : ℝ)
          * (|C2| * p.ν⁻¹ ^ k2 * Real.exp (etaDelta P.eigenvalue.re δ / p.ν))
        ≤ (K2 * p.ν⁻¹) * (|C2| * p.ν⁻¹ ^ k2 * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) :=
          mul_le_mul_of_nonneg_right hNbd hM0
      _ = (K2 * |C2| * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) * (p.ν⁻¹ * p.ν⁻¹ ^ k2) := by
          ring
      _ ≤ (K2 * |C2| * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) * p.ν⁻¹ ^ k :=
          mul_le_mul_of_nonneg_left hYY hcoef0
      _ = K2 * |C2| * (p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)) := by ring)
  exact (add_le_add (add_le_add hA' hSb) hC').trans (le_of_eq (by ring))

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
