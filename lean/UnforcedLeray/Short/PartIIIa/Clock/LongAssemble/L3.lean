import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Part III-a long assembly, L3: the moving-coordinate `xNorm` at the initial age

Proves `UnforcedLeray.Short.IIIa.xNorm_JscaleInv_ae_eq` (task PartIII-a:T21/long/3).

Proof. Put `a = clockA ν t` and `d = cellLen c a = c/√a`.
* If `a > 0`, then `√a > 0`, `y ∈ cell d ↔ √a • y ∈ cell c`, and `w t = f` a.e. on `cell c`
  (`IsLinearisedFlow.initial`). The set where `JscaleInv a (w t) ≠ JscaleInv a f` inside `cell d`
  is contained in the `(√a • ·)`-preimage of the null set `{w t ≠ f} ∩ cell c`, which is null by
  `Measure.addHaar_preimage_smul`. Hence `JscaleInv a (w t) = JscaleInv a f` a.e. on `cell d`,
  and so a.e. for `cellMeasure d m ≪ volume.restrict (cell d)`.
* If `a ≤ 0`, then `√a = 0`, `d = 0`, `cell 0 = ∅`, so both `xNorm`s are `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem xNorm_JscaleInv_ae_eq {ν c m t : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} (h : IsLinearisedFlow ν c m tr t f w u) : xNorm (cellLen c (clockA ν t)) m (JscaleInv (clockA ν t) (w t)) = xNorm (cellLen c (clockA ν t)) m (JscaleInv (clockA ν t) f) := by
  set a := clockA ν t with ha_def
  by_cases ha : 0 < a
  · have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have hrne : Real.sqrt a ≠ 0 := hr.ne'
    have e : Real.sqrt a * (c / Real.sqrt a / 2) = c / 2 := by field_simp
    -- membership transport: `y ∈ cell (c/√a)` iff `√a • y ∈ cell c`
    have hmem : ∀ y : ℝ × ℝ, y ∈ UnforcedLeray.B0579.cell (cellLen c a) ↔
        Real.sqrt a • y ∈ UnforcedLeray.B0579.cell c := by
      intro y
      unfold UnforcedLeray.B0579.cell cellLen
      rw [Set.mem_prod, Set.mem_prod, Set.mem_Ico, Set.mem_Ico]
      simp only [Set.mem_univ, and_true, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · linarith [mul_le_mul_of_nonneg_left h1 hr.le]
        · linarith [mul_lt_mul_of_pos_left h2 hr]
      · rintro ⟨h1, h2⟩
        constructor
        · by_contra hc
          push_neg at hc
          linarith [mul_lt_mul_of_pos_left hc hr]
        · by_contra hc
          push_neg at hc
          linarith [mul_le_mul_of_nonneg_left hc hr.le]
    have hae_c : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)), w t x = f x := h.initial
    rw [ae_iff, Measure.restrict_apply' (UnforcedLeray.B0579.measurableSet_cell c)] at hae_c
    have key : ∀ (g : ℝ × ℝ → ℂ) (y : ℝ × ℝ), JscaleInv a g y = ((a ^ 2 : ℝ) : ℂ) * g (Real.sqrt a • y) :=
      fun g y => rfl
    have hae_d : ∀ᵐ y ∂(volume.restrict (UnforcedLeray.B0579.cell (cellLen c a))),
        JscaleInv a (w t) y = JscaleInv a f y := by
      rw [ae_iff, Measure.restrict_apply' (UnforcedLeray.B0579.measurableSet_cell _)]
      refine measure_mono_null (t := (fun y : ℝ × ℝ => Real.sqrt a • y) ⁻¹'
          ({x : ℝ × ℝ | ¬ w t x = f x} ∩ UnforcedLeray.B0579.cell c)) ?_ ?_
      · intro y hy
        refine ⟨?_, (hmem y).1 hy.2⟩
        intro heq
        apply hy.1
        rw [key, key, heq]
      · rw [Measure.addHaar_preimage_smul volume hrne, hae_c, mul_zero]
    have hae_meas : ∀ᵐ y ∂(UnforcedLeray.B0579.cellMeasure (cellLen c a) m),
        JscaleInv a (w t) y = JscaleInv a f y :=
      (UnforcedLeray.B0579.cellMeasure_ac (cellLen c a) m).ae_le hae_d
    unfold xNorm
    exact eLpNorm_congr_ae hae_meas
  · have hs : Real.sqrt a = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 ha)
    have hd : cellLen c a = 0 := by unfold cellLen; rw [hs, div_zero]
    have hcell : UnforcedLeray.B0579.cell 0 = ∅ := by
      unfold UnforcedLeray.B0579.cell
      simp
    have hμ : UnforcedLeray.B0579.cellMeasure 0 m = 0 := by
      unfold UnforcedLeray.B0579.cellMeasure
      rw [hcell, Measure.restrict_empty]
      simp
    unfold xNorm
    rw [hd, hμ]
    simp

end UnforcedLeray.Short.IIIa
