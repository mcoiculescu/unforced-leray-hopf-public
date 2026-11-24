import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.OpBoundOfBox

/-!
# `forbiddenBlockBound_of`: the forbidden separated subblock (source 4011-4014)

From the kernel estimate `ForbiddenKernelBound` and the box density `BoxDenseZ`, the operator
`1_{s<s₋} S_far 1_{t<e^δ s₋}` has norm `≤ P_ν ε √s₋`.  The operator bound is `opNorm_le_of_box`;
on box inputs the input restriction keeps the box property, the far pin turns `Sf` into `farOut`,
and the output restriction is the indicator of `ForbiddenKernelBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The component sum commutes with the input restriction, a.e. on the chart. -/
theorem fb_zsum_inRestr_ae {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (A : Set Chart)
    (hA : MeasurableSet A) (F : Zsp c mZ ρb) :
    zsum (inRestr c mZ ρb A F) =ᵐ[ageμ c (-1 / 2)] fun p => A.indicator (zsum F) p := by
  have h1 := restrLp_ae (μ := z1Measure c mZ) (E := Ten3) hA (zEquiv c mZ ρb F).1
  have h2 := restrLp_ae (μ := htRhoMeasure c ρb) (E := Ten3) hA (zEquiv c mZ ρb F).2
  have a1 : ageμ c (-1 / 2) ≪ z1Measure c mZ :=
    Measure.absolutelyContinuous_of_le_smul (ageμ_le_z1Measure (c := c) hmZ)
  have a2 : ageμ c (-1 / 2) ≪ htRhoMeasure c ρb :=
    Measure.absolutelyContinuous_of_le_smul (ageμ_le_htRho (c := c) hρ)
  filter_upwards [a1.ae_le h1, a2.ae_le h2] with p hp1 hp2
  have e1 : (zEquiv c mZ ρb (inRestr c mZ ρb A F)).1 =
      restrLp (z1Measure c mZ) Ten3 A (zEquiv c mZ ρb F).1 :=
    congrArg Prod.fst (zEquiv_inRestr c mZ ρb A F)
  have e2 : (zEquiv c mZ ρb (inRestr c mZ ρb A F)).2 =
      restrLp (htRhoMeasure c ρb) Ten3 A (zEquiv c mZ ρb F).2 :=
    congrArg Prod.snd (zEquiv_inRestr c mZ ρb A F)
  have hz1 : zsum (inRestr c mZ ρb A F) p =
      ((zEquiv c mZ ρb (inRestr c mZ ρb A F)).1 : Chart → Ten3) p +
        ((zEquiv c mZ ρb (inRestr c mZ ρb A F)).2 : Chart → Ten3) p := rfl
  have hz2 : zsum F p = ((zEquiv c mZ ρb F).1 : Chart → Ten3) p +
      ((zEquiv c mZ ρb F).2 : Chart → Ten3) p := rfl
  rw [hz1, e1, e2, hp1, hp2]
  by_cases hpA : p ∈ A
  · simp [ind, hpA, Set.indicator_of_mem, hz2]
  · simp [ind, hpA, Set.indicator_of_notMem, hz2]

/-- **`forbiddenBlockBound_of`** (source 4011-4014): the forbidden separated subblock estimate
from the kernel estimate and the box density. -/
theorem forbiddenBlockBound_of (hK : ForbiddenKernelBound) (hD : BoxDenseZ) : ForbiddenBlockBound := by
  intro Kset hKc hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C, k, ν₀, hν₀, hK'⟩ := hK Kset hKc hKsub dm dp hdm b δ hb hb1 hδ
  refine ⟨|C|, k, ν₀, hν₀, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ Sf hSf sm hsm hsmS
  set A : Set Chart := ageBelow (Real.exp δ * sm) with hAdef
  have hAm : MeasurableSet A := measurableSet_ageBelow _
  set X : Zsp p.c mZ ρb →L[ℝ] Hsp p.c :=
    outRestr p.c (ageBelow sm) ∘L Sf ∘L inRestr p.c mZ ρb A with hXdef
  have hB : 0 ≤ |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm) :=
    mul_nonneg (mul_nonneg (abs_nonneg C) (pow_nonneg (inv_nonneg.2 p.ν_pos.le) k))
      (mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _))
  have hX : ∀ (F : Zsp p.c mZ ρb) (f : Chart → Ten3), IsBoxTensor f →
      zsum F =ᵐ[ageμ p.c (-1 / 2)] f →
        eLpNorm (X F : Chart → Merid) 2 (ageμ p.c (-3 / 2)) ≤
          ENNReal.ofReal (|C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) *
            eLpNorm f 2 (ageμ p.c (-1 / 2)) := by
    intro F f hf hFf
    have hg : IsBoxTensor (A.indicator f) := IsBoxTensor.indicator hf hAm
    have hGg : zsum (inRestr p.c mZ ρb A F) =ᵐ[ageμ p.c (-1 / 2)] A.indicator f := by
      filter_upwards [fb_zsum_inRestr_ae hmZ hρ A hAm F, hFf] with x h1 h2
      rw [h1]
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx, h2]
      · simp [Set.indicator_of_notMem hx]
    have hSF := (isFarMask_iff p.R p.ν μ δ (p.ε ^ (-b)) Sf).1 hSf _ _ hg hGg
    have hOut : (X F : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)]
        (ageBelow sm).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) (A.indicator f)) := by
      have h1 := restrLp_ae (μ := ageμ p.c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2))
        (measurableSet_ageBelow sm) (Sf (inRestr p.c mZ ρb A F))
      have hXF : X F = restrLp (ageμ p.c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (ageBelow sm)
          (Sf (inRestr p.c mZ ρb A F)) := rfl
      filter_upwards [h1, hSF] with x hx1 hx2
      rw [hXF]
      refine Eq.trans hx1 ?_
      by_cases hx : x ∈ ageBelow sm
      · simp [Set.indicator_of_mem hx, ind, hx2]
      · simp [Set.indicator_of_notMem hx, ind]
    have hsupp : ∀ x, A.indicator f x ≠ 0 → x.1 < Real.exp δ * sm := by
      intro x hx
      by_contra h
      have hxA : x ∉ A := fun h' => h h'
      exact hx (Set.indicator_of_notMem hxA f)
    have hfin := hK' p d hreg hν μ hμ sm hsm hsmS (A.indicator f) hg hsupp
    have hle : eLpNorm (A.indicator f) 2 (ageμ p.c (-1 / 2)) ≤ eLpNorm f 2 (ageμ p.c (-1 / 2)) :=
      eLpNorm_indicator_le f
    calc eLpNorm (X F : Chart → Merid) 2 (ageμ p.c (-3 / 2))
        = eLpNorm ((ageBelow sm).indicator
            (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) (A.indicator f))) 2 (ageμ p.c (-3 / 2)) :=
          eLpNorm_congr_ae hOut
      _ ≤ ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) *
            eLpNorm (A.indicator f) 2 (ageμ p.c (-1 / 2)) := hfin
      _ ≤ ENNReal.ofReal (|C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) *
            eLpNorm f 2 (ageμ p.c (-1 / 2)) := by
          have h0 : 0 ≤ p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm) :=
            mul_nonneg (pow_nonneg (inv_nonneg.2 p.ν_pos.le) k)
              (mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _))
          have hCC : C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm) ≤
              |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm) := by
            calc C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)
                = C * (p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) := by ring
              _ ≤ |C| * (p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) :=
                  mul_le_mul_of_nonneg_right (le_abs_self C) h0
              _ = |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm) := by ring
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCC) hle
  have hc : 0 < p.c := p.c_pos
  exact opNorm_le_of_box hD hc hmZ hρ hρ1 X hB hX

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
