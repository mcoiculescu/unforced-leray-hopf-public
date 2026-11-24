import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ForbiddenBlockBound

/-!
# `maskedStripBound_of`: the partial strip `1_{l≤s<r} S_N 1_{t≥e^δ l}` (source 3996-4005)

Route: `opNorm_le_of_box` with `B = |C| ν⁻ᵏ ε√r`, applied to
`X = outRestr (ageBand l r) ∘ (Seps - Sf) ∘ inRestr (ageAbove (e^δ l))`.  For box-type `F`, the
input restriction is a box tensor `f' = 1_{t ≥ e^δ l} f`; the real stress realization `hK` and the
far pin give `Seps G = fullOut f'` and `Sf G = farOut f'` a.e. (`G = 1_{t≥e^δ l} F`), so the output
is `1_{ageBand}(fullOut f' - farOut f')`, which the strip kernel estimate `hS` bounds by
`C ν⁻ᵏ ε√r ‖f'‖ ≤ C ν⁻ᵏ ε√r ‖f‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **`maskedStripBound_of`** (source 3996-4005): the partial strip from the strip kernel estimate,
the real stress realization `hK` and the box density `hD`. -/
theorem maskedStripBound_of (hK : StressKernelRealization) (hS : StripKernelBound) (hD : BoxDenseZ) :
    MaskedStripBound := by
  intro Kset hKc hKsub mZ hmZ dm dp hdm b δ hb hb1 hδ
  obtain ⟨C, k, ν₀, hν₀, hS'⟩ := hS Kset hKc hKsub dm dp hdm b δ hb hb1 hδ
  refine ⟨|C|, k, ν₀, hν₀, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ Seps Sf hpair l r hl hlr hrl hrS
  have hμ0 : 0 < μ := (hKsub hμ).1
  have hμ4 : -(1 / 4 : ℝ) < μ := by linarith
  obtain ⟨⟨Seps', hstress, htrans⟩, hfar⟩ := hpair
  set X : Zsp p.c mZ ρb →L[ℝ] Hsp p.c :=
    outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) with hXdef
  have hB : 0 ≤ |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) :=
    mul_nonneg (mul_nonneg (abs_nonneg C) (pow_nonneg (inv_nonneg.2 p.ν_pos.le) k))
      (mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _))
  have hX : ∀ (F : Zsp p.c mZ ρb) (f : Chart → Ten3), IsBoxTensor f →
      zsum F =ᵐ[ageμ p.c (-1 / 2)] f →
        eLpNorm (X F : Chart → Merid) 2 (ageμ p.c (-3 / 2)) ≤
          ENNReal.ofReal (|C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
            eLpNorm f 2 (ageμ p.c (-1 / 2)) := by
    intro F f hf hFf
    have hAm : MeasurableSet (ageAbove (Real.exp δ * l)) :=
      measurableSet_le measurable_const measurable_fst
    have hfA : IsBoxTensor ((ageAbove (Real.exp δ * l)).indicator f) :=
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.IsBoxTensor.indicator hf hAm
    have hGz : zsum (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F) =ᵐ[ageμ p.c (-1 / 2)]
        (ageAbove (Real.exp δ * l)).indicator f := by
      filter_upwards [fb_zsum_inRestr_ae hmZ hρ (ageAbove (Real.exp δ * l)) hAm F, hFf] with x h1 h2
      rw [h1]
      by_cases hx : x ∈ ageAbove (Real.exp δ * l)
      · simp [Set.indicator_of_mem hx, h2]
      · simp [Set.indicator_of_notMem hx]
    have hSeps := hK p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl μ hμ4 mZ ρb Seps' Seps
      hstress htrans _ _ hfA hGz
    have hSf := (isFarMask_iff p.R p.ν μ δ (p.ε ^ (-b)) Sf).1 hfar _ _ hfA hGz
    have hU : ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F) : Chart → Merid)
        =ᵐ[ageμ p.c (-3 / 2)]
        (fullOut p.R p.c p.ν μ ((ageAbove (Real.exp δ * l)).indicator f) -
          farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) ((ageAbove (Real.exp δ * l)).indicator f) :
            Chart → Merid) := by
      have h0 := Lp.coeFn_sub (Seps (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F))
        (Sf (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F))
      filter_upwards [h0, hSeps, hSf] with x h1 h2 h3
      rw [ContinuousLinearMap.sub_apply, h1, Pi.sub_apply, h2, h3]
      rfl
    have hO : (X F : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)]
        (ageBand l r).indicator (fullOut p.R p.c p.ν μ ((ageAbove (Real.exp δ * l)).indicator f) -
          farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) ((ageAbove (Real.exp δ * l)).indicator f)) := by
      have h1 := restrLp_ae (μ := ageμ p.c (-3 / 2)) (E := EuclideanSpace ℝ (Fin 2))
        (measurableSet_ageBand l r)
        ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F))
      have hXF : X F = restrLp (ageμ p.c (-3 / 2)) (EuclideanSpace ℝ (Fin 2)) (ageBand l r)
          ((Seps - Sf) (inRestr p.c mZ ρb (ageAbove (Real.exp δ * l)) F)) := rfl
      filter_upwards [h1, hU] with x hx1 hx2
      rw [hXF]
      refine Eq.trans hx1 ?_
      by_cases hx : x ∈ ageBand l r
      · change (ageBand l r).indicator (fun _ => (1 : ℝ)) x • ((Seps - Sf) (inRestr p.c mZ ρb
            (ageAbove (Real.exp δ * l)) F) : Chart → Merid) x = _
        simp only [Set.indicator_of_mem hx, one_smul]
        exact hx2
      · simp [Set.indicator_of_notMem hx, ind]
    have hsupp : ∀ x, (ageAbove (Real.exp δ * l)).indicator f x ≠ 0 → Real.exp δ * l ≤ x.1 := by
      intro x hx
      by_contra h
      have hxA : x ∉ ageAbove (Real.exp δ * l) := fun h' => h h'
      exact hx (Set.indicator_of_notMem hxA f)
    have hfin := hS' p d hreg hν μ hμ l r hl hlr hrl hrS
      ((ageAbove (Real.exp δ * l)).indicator f) hfA hsupp
    have hle : eLpNorm ((ageAbove (Real.exp δ * l)).indicator f) 2 (ageμ p.c (-1 / 2)) ≤
        eLpNorm f 2 (ageμ p.c (-1 / 2)) :=
      eLpNorm_indicator_le f
    calc eLpNorm (X F : Chart → Merid) 2 (ageμ p.c (-3 / 2))
        = eLpNorm ((ageBand l r).indicator
            (fullOut p.R p.c p.ν μ ((ageAbove (Real.exp δ * l)).indicator f) -
              farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) ((ageAbove (Real.exp δ * l)).indicator f)))
            2 (ageμ p.c (-3 / 2)) := eLpNorm_congr_ae hO
      _ ≤ ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
            eLpNorm ((ageAbove (Real.exp δ * l)).indicator f) 2 (ageμ p.c (-1 / 2)) := hfin
      _ ≤ ENNReal.ofReal (|C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
            eLpNorm f 2 (ageμ p.c (-1 / 2)) := by
          have h0 : 0 ≤ p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) :=
            mul_nonneg (pow_nonneg (inv_nonneg.2 p.ν_pos.le) k)
              (mul_nonneg p.ε_pos.le (Real.sqrt_nonneg _))
          have hCC : C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) ≤
              |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) := by
            calc C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)
                = C * (p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) := by ring
              _ ≤ |C| * (p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) :=
                  mul_le_mul_of_nonneg_right (le_abs_self C) h0
              _ = |C| * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r) := by ring
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCC) hle
  exact opNorm_le_of_box hD p.c_pos hmZ hρ hρ1 X hB hX

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
