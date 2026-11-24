import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.Exterior
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.SeedOne
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator.RelExteriorBlockBound.Constants

/-!
# `PartIII-a:T21/c3/2/1/1/org/4`: the exterior block bound (`RelExteriorBlockBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2945 and
2979-2980.

For `W` vanishing on the entrance cell `d(t₁)`:
* the free orbit `F_rel τ 0 W` vanishes on the cell `d(r)` (pin of `IsPeriodizedRelFreeBlockEvol` with
  `f = 0`, `ω₀ = 0`), so the localized interaction `A_rel τ` kills it (`dampedInt_apply_eq_zero`)
  and, by Gronwall for the block-clamped families, `U_rel B 0 W = F_rel B 0 W`
  (`duhamel_eq_free_of_kill`);
* `F_rel B 0 W = (clockN)⁻¹ • S(t₂,t₁) W` with `‖S‖ ≤ e^{3B/(2b)}` (`norm_extDilW_cellLen_le_exp`);
* `(clockN)⁻¹ e^{3B/(2b)} ≤ C₀ e^{-hB} + δ` for `b ≥ (|Re κ| + 3/2) B / log (1 + δ)`
  (`exterior_constant`, using `h ≤ Re λ` and `C₀ ≥ 1` from `one_le_of_seedCtx`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open CompactDuhamelGapSub BlockPropagatorSub BlockPropagatorInteriorSub OrgSplit RelExteriorSub

theorem relExteriorBlockBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) : UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelExteriorBlockBound κ := by
  intro _hκ P _hP m hm _K C₀ h B M_free K_A δ_gap _hC₀ hh hhl hB _hM _hKA hδ hSeed
  have hm1 : 1 < m := by linarith
  have hC₀1 : 1 ≤ C₀ := one_le_of_seedCtx hm1 hSeed
  refine ⟨max 1 ((|P.kappa.re| + 3 / 2) * B / Real.log (1 + δ_gap)), le_max_left _ _,
    fun b hb => ?_⟩
  have hb0 : 0 < b := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hb)
  have hbB : (|P.kappa.re| + 3 / 2) * B / Real.log (1 + δ_gap) ≤ b :=
    (le_max_right _ _).trans hb
  refine ⟨1, one_pos, ?_⟩
  intro ν hν _hF tr _htr t₁ t₂ ht₁ h12 hbt hBeq α' _hα' F_rel A_rel U_rel hT W hW
  obtain ⟨hFrel, hFb, hArel, hAb, hU, -⟩ := hT
  have hν0 : 0 < ν := hν.1
  have ht₂ : 0 ≤ t₂ := ht₁.trans h12
  -- ages along the block
  have hage_nonneg : ∀ τ, 0 ≤ τ → τ ≤ B → 0 ≤ ageAt ν t₁ τ := fun τ h0 h1 =>
    ageAt_nonneg hν0 ht₁ ht₂ h0 (by rw [hBeq]; exact h1)
  have hageB : ageAt ν t₁ B = t₂ := by
    have := ageAt_movingZ_sub (t₁ := t₁) hν0 ht₂
    rwa [hBeq] at this
  -- the localized interaction kills the free orbit
  have hkill : ∀ r, 0 ≤ r → r ≤ B → A_rel r (F_rel r 0 W) = 0 := by
    intro r hr0 hrB
    have hd := cellLen_pos hν0 (hage_nonneg r hr0 hrB)
    exact dampedInt_apply_eq_zero hArel ⟨hr0, hrB⟩ hd _
      (freeBlock_exterior_vanish hFrel hν0 ht₁ hr0 hrB hd W hW)
  -- the Duhamel evolution is stated for the families clamped to the block `[0, B]`
  have hclamp : ∀ r, 0 ≤ r → r ≤ B → clampB B r = r := fun r h0 h1 => by
    unfold clampB
    rw [min_eq_left h1, max_eq_right h0]
  have hFc : ∀ σ τ : ℝ, σ ≤ τ → τ ≤ σ + B → ‖clampF B F_rel τ σ‖ ≤ M_free := fun σ τ h1 _ =>
    hFb _ _ (clampB_mono B h1)
      (by have := clampB_le B τ hB.le; have := clampB_nonneg B σ; linarith)
  have hAc : ∀ τ, ‖clampA B A_rel τ‖ ≤ K_A := fun τ => hAb _
  have hkillc : ∀ r, 0 ≤ r → r ≤ B → clampA B A_rel r (clampF B F_rel r 0 W) = 0 := by
    intro r hr0 hrB
    simp only [clampA, clampF, hclamp r hr0 hrB, hclamp 0 le_rfl hB.le]
    exact hkill r hr0 hrB
  have hUF : U_rel B 0 W = F_rel B 0 W := by
    rw [duhamel_eq_free_of_kill hU hFc hAc W hkillc B hB.le le_rfl]
    simp only [clampF, hclamp B hB.le le_rfl, hclamp 0 le_rfl hB.le]
  -- the exterior dilation
  have hd₁ := cellLen_pos hν0 ht₁
  have hd₂ := cellLen_pos hν0 ht₂
  have hFeq := freeBlock_exterior_eq_smul hFrel hν0 ht₁ hB.le hageB hm1 hd₁ hd₂ W hW
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν0 _
  have hS : ‖extDilW hm1 hd₁ hd₂‖ ≤ Real.exp ((3 / (2 * b)) * (movingZ ν t₂ - movingZ ν t₁)) :=
    norm_extDilW_cellLen_le_exp hm1 hc hν0 ht₁ h12 hb0 hbt
  rw [hBeq] at hS
  obtain ⟨hNpos, hconst⟩ := exterior_constant (P := P) hν0 ht₁ h12 hb0 hbt hB hBeq hh hhl hC₀1
    hδ hbB
  have hEW : ‖extDilW hm1 hd₁ hd₂ W‖ ≤ Real.exp (3 / (2 * b) * B) * ‖W‖ :=
    ((extDilW hm1 hd₁ hd₂).le_opNorm W).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  rw [hUF, hFeq, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hNpos.le]
  calc (clockN P ν t₁ t₂)⁻¹ * ‖extDilW hm1 hd₁ hd₂ W‖
      ≤ (clockN P ν t₁ t₂)⁻¹ * (Real.exp (3 / (2 * b) * B) * ‖W‖) :=
        mul_le_mul_of_nonneg_left hEW (inv_nonneg.2 hNpos.le)
    _ = ((clockN P ν t₁ t₂)⁻¹ * Real.exp (3 / (2 * b) * B)) * ‖W‖ := by ring
    _ ≤ (C₀ * Real.exp (-h * B) + δ_gap) * ‖W‖ :=
        mul_le_mul_of_nonneg_right hconst (norm_nonneg _)

end UnforcedLeray.Short.IIIa
