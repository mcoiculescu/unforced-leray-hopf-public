import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelBlockDiagonal.Pins

/-!
# `PartIII-a:T21/c3/2/1/1/org/2`: block diagonality of the relative evolution (`RelBlockDiagonal`)

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2945
and 2974-2977.

The periodized extension `F̄(z,t) = I_z F(z,t) R_t + S(z,t)(I - Π_t)` has disjoint entrance and
exit supports (SP 2943), the localized interaction `A_rel` reads and writes only the cell, and
`U_rel` is the Duhamel evolution of `(F_rel, A_rel)`.  Hence:

* on data supported in the entrance cell `d(t₁)`: the Duhamel identity
  `U(B,0)W = F(B,0)W + ∫₀^B F(B,r) A(r) U(r,0)W dr` exhibits `U(B,0)W` as a sum of data supported
  in the exit cell `d(t₂)` (`freeBlock_cell_to_cell`, `dampedInt_cellSupported`, closedness of
  the cell-supported subspace under Bochner integrals);
* on data vanishing on the entrance cell: `A_rel` kills the free orbit, so `U(B,0)W = F(B,0)W`
  (`duhamel_eq_free_of_kill`), the exterior dilation, which vanishes on the exit cell
  (`freeBlock_exterior_vanish`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub OrgSplit RelExteriorSub
  RelBlockDiagonalSub

theorem relBlockDiagonal (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) : UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelBlockDiagonal κ := by
  intro _hκ P _hP m hm _K B M_free K_A hB _hM _hKA
  refine ⟨1, le_rfl, fun b _hb => ⟨1, one_pos, ?_⟩⟩
  intro ν hν _hF tr htr t₁ t₂ ht₁ h12 _hbt hBeq α' F_rel A_rel U_rel hT
  obtain ⟨hFrel, hFb, hArel, hAb, hU, -⟩ := hT
  have hν0 : 0 < ν := hν.1
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  have hage_nonneg : ∀ τ, 0 ≤ τ → τ ≤ B → 0 ≤ ageAt ν t₁ τ := fun τ h0 h1 =>
    ageAt_nonneg hν0 ht₁ ht₂ h0 (by rw [hBeq]; exact h1)
  have hageB : ageAt ν t₁ B = t₂ := by
    have := ageAt_movingZ_sub (t₁ := t₁) hν0 ht₂
    rwa [hBeq] at this
  have hage0 : ageAt ν t₁ 0 = t₁ := ageAt_zero hν0 ht₁
  have hB0 : 0 ≤ ageAt ν t₁ B := hage_nonneg B hB.le le_rfl
  -- the Duhamel evolution is stated for the families clamped to the block `[0, B]`
  have hclamp : ∀ r, 0 ≤ r → r ≤ B → clampB B r = r := fun r h0 h1 => by
    unfold clampB
    rw [min_eq_left h1, max_eq_right h0]
  refine ⟨fun W hW => ?_, fun W hW => ?_⟩
  · -- data supported in the entrance cell: every Duhamel term lies in the exit cell
    have hd : U_rel B 0 W = clampF B F_rel B 0 W +
        ∫ r in (0 : ℝ)..B, clampF B F_rel B r (clampA B A_rel r (U_rel r 0 W)) :=
      hU.duhamel () 0 B hB.le (by linarith) W
    have hint : IntervalIntegrable
        (fun r => clampF B F_rel B r (clampA B A_rel r (U_rel r 0 W))) volume 0 B :=
      hU.integrable () 0 B hB.le (by linarith) W
    rw [hd]
    refine isCellSupportedW_add ?_ (isCellSupportedW_intervalIntegral hint fun r hr => ?_)
    · simp only [clampF, hclamp B hB.le le_rfl, hclamp 0 le_rfl hB.le]
      rw [← hageB]
      exact freeBlock_cell_to_cell hFrel hν0 hm htr le_rfl hB.le le_rfl
        (hage_nonneg 0 le_rfl hB.le) hB0 W (by rw [hage0]; exact hW)
    · rw [uIcc_of_le hB.le] at hr
      simp only [clampF, clampA, hclamp B hB.le le_rfl, hclamp r hr.1 hr.2]
      rw [← hageB]
      exact freeBlock_cell_to_cell hFrel hν0 hm htr hr.1 hr.2 le_rfl
        (hage_nonneg r hr.1 hr.2) hB0 _ (dampedInt_cellSupported hArel hr (U_rel r 0 W))
  · -- data vanishing on the entrance cell: `U_rel B 0 W = F_rel B 0 W`, the exterior dilation
    have hFc : ∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖clampF B F_rel τ σ‖ ≤ M_free :=
      fun σ τ h1 _ => hFb _ _ (clampB_mono B h1)
        (by have := clampB_le B τ hB.le; have := clampB_nonneg B σ; linarith)
    have hAc : ∀ τ, ‖clampA B A_rel τ‖ ≤ K_A := fun τ => hAb _
    have hkillc : ∀ r, 0 ≤ r → r ≤ B → clampA B A_rel r (clampF B F_rel r 0 W) = 0 := by
      intro r hr0 hrB
      simp only [clampA, clampF, hclamp r hr0 hrB, hclamp 0 le_rfl hB.le]
      have hd := cellLen_pos hν0 (hage_nonneg r hr0 hrB)
      exact dampedInt_apply_eq_zero hArel ⟨hr0, hrB⟩ hd _
        (freeBlock_exterior_vanish hFrel hν0 ht₁ hr0 hrB hd W hW)
    have hUF : U_rel B 0 W = F_rel B 0 W := by
      rw [duhamel_eq_free_of_kill hU hFc hAc W hkillc B hB.le le_rfl]
      simp only [clampF, hclamp B hB.le le_rfl, hclamp 0 le_rfl hB.le]
    rw [hUF]
    have h := freeBlock_exterior_vanish hFrel hν0 ht₁ hB.le le_rfl (cellLen_pos hν0 hB0) W hW
    rw [hageB] at h
    exact h

end UnforcedLeray.Short.IIIa
