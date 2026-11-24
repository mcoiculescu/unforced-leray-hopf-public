import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The affine force is `L²` on every age band (source 3426-3440, 4594-4596, 4988)

Source of record: `the November 2 reference manuscript` (73 pages).

`VorticityToVelocity` needs the force in `L²` on every band `[s₁,s₂] × cell`, `s₁ > 0` (the force of
the causal problem lies in the class `𝒯`, 3426-3440; local integrability is not enough, see
`Sub/PartIII-b_C_flatset_col_6/VtvFluxRefute.lean`).  For `f_A` this is local integrability
(`FlatForceLocal`, which gives measurability) together with the Gaussian decay in `η`
(`FlatForceDecay`, 4988): `|f_A| ≤ C/(1 + η²)` and `(1 + η²)⁻¹ ∈ L¹(ℝ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `(1 + η²)⁻¹` is integrable on an age band times the cell. -/
theorem integrableOn_band_inv_one_add_sq (c s₁ s₂ : ℝ) :
    IntegrableOn (fun p : ℝ × (ℝ × ℝ) => (1 + p.2.2 ^ 2)⁻¹) (Icc s₁ s₂ ×ˢ B0579.cell c) := by
  have h1 : Integrable (fun y : ℝ × ℝ => (1 : ℝ) * (1 + y.2 ^ 2)⁻¹)
      ((volume.restrict (Ico (-(c / 2)) (c / 2))).prod volume) :=
    (integrable_const (1 : ℝ)).mul_prod integrable_inv_one_add_sq
  have h2 : Integrable (fun p : ℝ × (ℝ × ℝ) => (1 : ℝ) * ((1 : ℝ) * (1 + p.2.2 ^ 2)⁻¹))
      ((volume.restrict (Icc s₁ s₂)).prod
        ((volume.restrict (Ico (-(c / 2)) (c / 2))).prod volume)) :=
    (integrable_const (1 : ℝ)).mul_prod h1
  have e1 : (volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume : Measure ℝ) =
      (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) := by
    rw [B0579.cell, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have e2 : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Icc s₁ s₂ ×ˢ B0579.cell c) =
      (volume.restrict (Icc s₁ s₂)).prod
        ((volume.restrict (Ico (-(c / 2)) (c / 2))).prod volume) := by
    rw [e1, Measure.prod_restrict, ← Measure.volume_eq_prod]
  unfold IntegrableOn
  rw [e2]
  simpa only [one_mul] using h2

/-- A function on an age band times the cell which is integrable on every bounded part
`{|η| ≤ R}` and bounded by `C/(1 + η²)` is `L²` on the band. -/
theorem memLp_band_of_local_of_decay {c s₁ s₂ C : ℝ} {F : ℝ × (ℝ × ℝ) → ℂ}
    (hloc : ∀ R : ℝ, IntegrableOn F (Icc s₁ s₂ ×ˢ (B0579.cell c ∩ {x | |x.2| ≤ R})))
    (hdec : ∀ s ∈ Icc s₁ s₂, ∀ x ∈ B0579.cell c, ‖F (s, x)‖ ≤ C / (1 + x.2 ^ 2)) :
    MemLp F 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) := by
  have hU : Icc s₁ s₂ ×ˢ B0579.cell c =
      ⋃ n : ℕ, Icc s₁ s₂ ×ˢ (B0579.cell c ∩ {x | |x.2| ≤ n}) := by
    ext p
    simp only [mem_prod, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_ge |p.2.2|
      exact ⟨n, h1, h2, hn⟩
    · rintro ⟨n, h1, h2, -⟩
      exact ⟨h1, h2⟩
  have hmeas : AEStronglyMeasurable F (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) := by
    rw [hU]
    exact aestronglyMeasurable_iUnion_iff.2 fun n => (hloc n).aestronglyMeasurable
  have hS : MeasurableSet (Icc s₁ s₂ ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (B0579.measurableSet_cell c)
  set g : ℝ × (ℝ × ℝ) → ℝ := fun p => C / (1 + p.2.2 ^ 2) with hgdef
  have hgc : Continuous g :=
    continuous_const.div (by fun_prop) fun p => by positivity
  have hg : MemLp g 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell c)) := by
    refine (memLp_two_iff_integrable_sq hgc.aestronglyMeasurable).2 ?_
    refine Integrable.mono' (Integrable.const_mul (integrableOn_band_inv_one_add_sq c s₁ s₂)
      (C ^ 2)) (hgc.pow 2).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have h0 : (0 : ℝ) < 1 + p.2.2 ^ 2 := by positivity
    have h1 : (1 : ℝ) ≤ 1 + p.2.2 ^ 2 := by nlinarith [sq_nonneg p.2.2]
    have hinv : (1 + p.2.2 ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have hinv0 : 0 ≤ (1 + p.2.2 ^ 2)⁻¹ := inv_nonneg.2 h0.le
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [hgdef, div_eq_mul_inv, mul_pow, sq ((1 + p.2.2 ^ 2)⁻¹)]
    calc C ^ 2 * ((1 + p.2.2 ^ 2)⁻¹ * (1 + p.2.2 ^ 2)⁻¹)
        ≤ C ^ 2 * ((1 + p.2.2 ^ 2)⁻¹ * 1) := by
          gcongr
      _ = C ^ 2 * (1 + p.2.2 ^ 2)⁻¹ := by ring
  refine hg.of_le hmeas ((ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_))
  calc ‖F p‖ = ‖F (p.1, p.2)‖ := rfl
    _ ≤ C / (1 + p.2.2 ^ 2) := hdec p.1 hp.1 p.2 hp.2
    _ ≤ ‖g p‖ := Real.le_norm_self _

/-- **`f_A` is `L²` on every age band** (source 3426-3440, 4594-4596, 4988), from
`FlatForceLocal` and `FlatForceDecay`: the force hypothesis of `VorticityToVelocity`. -/
theorem forceC_memLp_band (hLoc : FlatForceLocal) (hDec : FlatForceDecay) {ν μ as : ℝ}
    {χ : ℝ → ℝ} {A : ℝ → Mat3} (hν : 0 < ν) (hχ : IsSourceCutoffC χ) (hA : IsAffElem as A) :
    ∀ s₁ s₂ : ℝ, 0 < s₁ → ∀ i,
      MemLp (fun p => forceC ν μ χ A p i) 2 (volume.restrict (Icc s₁ s₂ ×ˢ B0579.cell (cOf ν))) := by
  intro s₁ s₂ hs₁ i
  obtain ⟨C, hC⟩ := hDec ν μ as χ A hν hχ hA s₁ s₂ hs₁
  exact memLp_band_of_local_of_decay (fun R => hLoc ν μ as χ A hν hχ hA s₁ s₂ R hs₁ i)
    (fun s hs x hx => hC s hs x hx i)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
