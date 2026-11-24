import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `opNorm_le_of_box`: a bound on box tensors gives the operator bound (source 3905-3912)

Proves `opNorm_le_of_box`: if `X : Z → H` satisfies the bound `‖X F‖ ≤ B ‖f‖_{L²}` on every `F` whose
component sum is a box tensor `f`, then `‖X‖ ≤ B`.

Route.
* `ob_zsumL_norm_le`: `‖zsumL F‖_{H_T} ≤ ‖F‖_Z` for `ρ_b ≤ 1` (`W ≥ 1` gives the `Z₁` inclusion norm
  `≤ 1`, and `ρ_b^{1/2} ≤ 1` the `ρ_b^{-1/2}H_T` inclusion norm; the `Z` norm is the `ℓ¹` sum).
* For box-type `G`, `‖X G‖ ≤ B ‖zsumL G‖ ≤ B ‖G‖` (`zsumL_ae` identifies the `L²` norms).
* For general `F`, the density `hD` gives `F'` of box type with `‖F - F'‖` arbitrarily small, and
  `‖X F‖ ≤ ‖X F'‖ + ‖X‖ ‖F - F'‖`; letting the error go to zero gives `‖X F‖ ≤ B ‖F‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The first inclusion `Z₁ → H_T` has norm `≤ 1` (`W ≥ 1`, source 2696-2700). -/
theorem ob_norm_inclZ1_le {c mZ : ℝ} (hmZ : 0 ≤ mZ) : ‖inclZ1 c mZ hmZ‖ ≤ 1 := by
  refine (Lp.norm_LpToLpOfMeasureLeSMul_le ENNReal.one_ne_top
    (ageμ_le_z1Measure (c := c) hmZ)).trans ?_
  simp

/-- The second inclusion `ρ_b^{-1/2}H_T → H_T` has norm `≤ 1` for `ρ_b ≤ 1` (norm `√ρ_b`). -/
theorem ob_norm_inclRho_le {c ρb : ℝ} (hρ : 0 < ρb) (hρ1 : ρb ≤ 1) : ‖inclRho c ρb hρ‖ ≤ 1 := by
  refine (Lp.norm_LpToLpOfMeasureLeSMul_le ENNReal.ofReal_ne_top
    (ageμ_le_htRho (c := c) hρ)).trans (Real.rpow_le_one ENNReal.toReal_nonneg ?_ ENNReal.toReal_nonneg)
  rw [ENNReal.toReal_ofReal hρ.le]
  exact hρ1

/-- `‖zsumL F‖_{H_T} ≤ ‖F‖_Z` for `ρ_b ≤ 1`. -/
theorem ob_zsumL_norm_le {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (hρ1 : ρb ≤ 1)
    (F : Zsp c mZ ρb) : ‖zsumL c mZ ρb hmZ hρ F‖ ≤ ‖F‖ := by
  have hsplit : zsumL c mZ ρb hmZ hρ F =
      inclZ1 c mZ hmZ (zEquiv c mZ ρb F).1 + inclRho c ρb hρ (zEquiv c mZ ρb F).2 := rfl
  have hF : ‖F‖ = ‖(zEquiv c mZ ρb F).1‖ + ‖(zEquiv c mZ ρb F).2‖ := by
    have h := WithLp.prod_norm_eq_add (p := (1 : ℝ≥0∞)) (by norm_num) F
    simp only [ENNReal.toReal_one, Real.rpow_one, div_one] at h
    exact h
  have hA : ‖inclZ1 c mZ hmZ (zEquiv c mZ ρb F).1‖ ≤ ‖(zEquiv c mZ ρb F).1‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (ob_norm_inclZ1_le (c := c) hmZ))
  have hB : ‖inclRho c ρb hρ (zEquiv c mZ ρb F).2‖ ≤ ‖(zEquiv c mZ ρb F).2‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (ob_norm_inclRho_le hρ hρ1))
  calc ‖zsumL c mZ ρb hmZ hρ F‖
      = ‖inclZ1 c mZ hmZ (zEquiv c mZ ρb F).1 + inclRho c ρb hρ (zEquiv c mZ ρb F).2‖ := by
        rw [hsplit]
    _ ≤ ‖inclZ1 c mZ hmZ (zEquiv c mZ ρb F).1‖ + ‖inclRho c ρb hρ (zEquiv c mZ ρb F).2‖ :=
        norm_add_le _ _
    _ ≤ ‖(zEquiv c mZ ρb F).1‖ + ‖(zEquiv c mZ ρb F).2‖ := add_le_add hA hB
    _ = ‖F‖ := hF.symm

/-- **`opNorm_le_of_box`** (source 3905-3912): a bound on box tensors gives the operator bound. -/
theorem opNorm_le_of_box (hD : BoxDenseZ) {c mZ ρb : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (hρ1 : ρb ≤ 1) (X : Zsp c mZ ρb →L[ℝ] Hsp c) {B : ℝ} (hB : 0 ≤ B)
    (hX : ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f →
      zsum F =ᵐ[ageμ c (-1 / 2)] f →
        eLpNorm (X F : Chart → Merid) 2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal B * eLpNorm f 2 (ageμ c (-1 / 2))) : ‖X‖ ≤ B := by
  -- the bound on box-type inputs
  have hbox : ∀ G : Zsp c mZ ρb, (∃ f : Chart → Ten3, IsBoxTensor f ∧
      zsum G =ᵐ[ageμ c (-1 / 2)] f) → ‖X G‖ ≤ B * ‖G‖ := by
    rintro G ⟨f, hf, hGf⟩
    have hfz : eLpNorm f 2 (ageμ c (-1 / 2)) =
        eLpNorm (zsumL c mZ ρb hmZ hρ G : Chart → Ten3) 2 (ageμ c (-1 / 2)) :=
      (eLpNorm_congr_ae ((zsumL_ae c mZ ρb hmZ hρ G).trans hGf)).symm
    have hA := hX G f hf hGf
    have hfin : eLpNorm f 2 (ageμ c (-1 / 2)) ≠ ⊤ := by
      rw [hfz]
      exact Lp.eLpNorm_ne_top _
    have hXn : ‖X G‖ = (eLpNorm (X G : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal :=
      Lp.norm_def (X G)
    have hZn : ‖zsumL c mZ ρb hmZ hρ G‖ =
        (eLpNorm (zsumL c mZ ρb hmZ hρ G : Chart → Ten3) 2 (ageμ c (-1 / 2))).toReal :=
      Lp.norm_def _
    have hmono : (eLpNorm (X G : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal ≤
        (ENNReal.ofReal B * eLpNorm f 2 (ageμ c (-1 / 2))).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hA
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hmono
    rw [hXn]
    calc (eLpNorm (X G : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal
        ≤ B * (eLpNorm f 2 (ageμ c (-1 / 2))).toReal := hmono
      _ = B * ‖zsumL c mZ ρb hmZ hρ G‖ := by rw [hZn, hfz]
      _ ≤ B * ‖G‖ := mul_le_mul_of_nonneg_left (ob_zsumL_norm_le hmZ hρ hρ1 G) hB
  refine ContinuousLinearMap.opNorm_le_bound X hB (fun F => ?_)
  by_contra hcon
  push_neg at hcon
  have hXnn : 0 ≤ ‖X‖ := norm_nonneg X
  set ε : ℝ := (‖X F‖ - B * ‖F‖) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  set K : ℝ := B + ‖X‖ + 1 with hK_def
  have hK : 0 < K := by rw [hK_def]; linarith
  obtain ⟨F', ⟨f, hf, hF'f⟩, hd⟩ := hD c mZ ρb hc hmZ hρ F (ε / K) (div_pos hε hK)
  have hbF := hbox F' ⟨f, hf, hF'f⟩
  have h1 : X F = X F' + X (F - F') := by
    rw [← map_add]
    congr 1
    abel
  have h2 : ‖X (F - F')‖ ≤ ‖X‖ * ‖F - F'‖ := ContinuousLinearMap.le_opNorm X _
  have h3 : ‖F'‖ ≤ ‖F‖ + ‖F - F'‖ := by
    have := norm_sub_norm_le F' F
    rw [norm_sub_rev F' F] at this
    linarith
  have h4 : ‖X F‖ ≤ ‖X F'‖ + ‖X (F - F')‖ := by
    rw [h1]
    exact norm_add_le _ _
  set d : ℝ := ‖F - F'‖ with hd_def
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdK : d * K < ε := by
    have := hd
    rw [lt_div_iff₀ hK] at this
    exact this
  have h5 : B * ‖F'‖ ≤ B * ‖F‖ + B * d := by
    have := mul_le_mul_of_nonneg_left h3 hB
    rwa [mul_add] at this
  have hK_expand : d * K = B * d + ‖X‖ * d + d := by
    rw [hK_def]
    ring
  linarith [h1, h2, h4, hbF, h5, hK_expand, hdK, hd0, hε_def, hcon]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
