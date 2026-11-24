import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedSupport
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ForbiddenBlockBound

/-!
# `farBlockZero_of`: complete blocks see no far part (source 3905-3912, 3978-3979)

Route: `opNorm_le_of_box` with `B = 0`, applied to `X = outRestr (ageAbove l) ∘ Sf ∘
inRestr (ageBelow (e^δ l))`.  For box-type `F`, the input restriction is the box tensor
`f' = 1_{t<e^δ l} f`, and the far pin gives `Sf G = farOut f'` a.e.  For outputs `s ≥ l` the far
kernel vanishes: the mask in `sepWfar` keeps only chart points with `t > e^δ s ≥ e^δ l`, where
`f'` is zero, so the lifted tensor is zero and `sepW` of the zero tensor is zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The separated Weyl-type integral of the zero tensor vanishes. -/
theorem fbz_sepW_zero (ν : ℝ) (μ : ℂ) (y : Space) (τ : ℝ) :
    UnforcedLeray.Short.IIIa.sepW ν μ
      (fun (_ : ℝ) (_ : Space) => (0 : Matrix (Fin 3) (Fin 3) ℝ)) y τ = 0 := by
  funext i
  simp [UnforcedLeray.Short.IIIa.sepW]

/-- The meridional projection of the zero vector is zero. -/
theorem fbz_merRe_zero : merRe (0 : Fin 3 → ℂ) = 0 := by
  ext i
  fin_cases i <;> simp [merRe]

/-- The far kernel vanishes at outputs `s ≥ l` for tensors vanishing at `t ≥ e^δ l`. -/
theorem fbz_farOut_zero {R c ν μ δ S l : ℝ} (hδ : 0 < δ) (f : Chart → Ten3)
    (hf : ∀ p : Chart, Real.exp δ * l ≤ p.1 → f p = 0) (x : Chart) (hx : l ≤ x.1) :
    farOut R c ν μ δ S f x = 0 := by
  have hfun : (fun τ' z => if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
      then cartLift R c f τ' z else 0) =
      fun (_ : ℝ) (_ : Space) => (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
    funext τ' z
    split_ifs with hc
    · have hle : Real.exp δ * l ≤ (chartOf R c z τ').1 := by
        rw [chartOf_fst_eq]
        exact le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx (Real.exp_pos δ).le) hc)
      have h0 : f (chartOf R c z τ') = 0 := hf _ hle
      simp [cartLift, h0, nsSym_zero_eq]
    · rfl
  unfold farOut
  by_cases hS : x.1 < S
  · rw [if_pos hS]
    have hsep : sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x) = 0 := by
      unfold sepWfar
      rw [hfun]
      exact fbz_sepW_zero _ _ _ _
    rw [hsep, neg_zero, fbz_merRe_zero, smul_zero]
  · rw [if_neg hS]

/-- **`farBlockZero_of`** (source 3905-3912, 3978-3979): complete blocks see no far part. -/
theorem farBlockZero_of (hD : BoxDenseZ) : FarBlockZero := by
  intro c mZ ρb R ν μ δ S l hc hmZ hρ hρ1 hδ hl Sf hSf
  set A : Set Chart := ageBelow (Real.exp δ * l) with hAdef
  have hAm : MeasurableSet A := measurableSet_ageBelow _
  set X : Zsp c mZ ρb →L[ℝ] Hsp c :=
    outRestr c (ageAbove l) ∘L Sf ∘L inRestr c mZ ρb A with hXdef
  have hX : ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f →
      zsum F =ᵐ[ageμ c (-1 / 2)] f →
        eLpNorm (X F : Chart → Merid) 2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal 0 * eLpNorm f 2 (ageμ c (-1 / 2)) := by
    intro F f hf hFf
    have hg : IsBoxTensor (A.indicator f) := IsBoxTensor.indicator hf hAm
    have hGg : zsum (inRestr c mZ ρb A F) =ᵐ[ageμ c (-1 / 2)] A.indicator f := by
      filter_upwards [fb_zsum_inRestr_ae hmZ hρ A hAm F, hFf] with x h1 h2
      rw [h1]
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx, h2]
      · simp [Set.indicator_of_notMem hx]
    have hSF := (isFarMask_iff R ν μ δ S Sf).1 hSf _ _ hg hGg
    have hf' : ∀ p : Chart, Real.exp δ * l ≤ p.1 → (A.indicator f) p = 0 := by
      intro p hp
      exact Set.indicator_of_notMem (show p ∉ A from fun h => (not_lt.2 hp) h) f
    have hzero : (X F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (0 : Chart → Merid) := by
      have h1 := restrLp_ae (μ := ageμ c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2))
        (measurableSet_ageAbove l) (Sf (inRestr c mZ ρb A F))
      have hXF : X F = restrLp (ageμ c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (ageAbove l)
          (Sf (inRestr c mZ ρb A F)) := rfl
      filter_upwards [h1, hSF] with x hx1 hx2
      rw [hXF]
      refine Eq.trans hx1 ?_
      by_cases hx : x ∈ ageAbove l
      · change (ageAbove l).indicator (fun _ => (1 : ℝ)) x •
          ((Sf (inRestr c mZ ρb A F)) : Chart → Merid) x = _
        simp only [Set.indicator_of_mem hx, one_smul]
        rw [hx2, fbz_farOut_zero hδ (A.indicator f) hf' x hx]
        rfl
      · change (ageAbove l).indicator (fun _ => (1 : ℝ)) x •
          ((Sf (inRestr c mZ ρb A F)) : Chart → Merid) x = _
        rw [Set.indicator_of_notMem hx, zero_smul]
        rfl
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    exact zero_le
  have hX0 : ‖X‖ ≤ 0 := opNorm_le_of_box hD hc hmZ hρ hρ1 X le_rfl hX
  exact norm_le_zero_iff.1 hX0

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
