import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3`, leaf `PbHmeanTimeIntegral` (Fubini for the horizontal average)

Source of record: `the November 2 reference manuscript`, line 447.
Target: `PbHmeanTimeIntegral` (`Sub/T02_2_3.lean`, line 220): for `F` continuous on `[0,T] × ℝ²` and
`a, b ∈ [0,T]`, `hmean c (z ↦ ∫_a^b F σ z dσ) η = ∫_a^b hmean c (F σ) η dσ`.

Proof.  Unfold `hmean` and pull the factor `c⁻¹` out of both sides (`intervalIntegral.integral_smul`).
The remaining identity is the interchange of the `q`-integral over `Ioc (-c/2) (c/2)` with the
`σ`-integral over `uIoc a b`, which is `MeasureTheory.integral_integral_swap` applied to the
integrable function `(q, σ) ↦ F σ (q, η)`.  Integrability holds because that function is continuous
on the compact rectangle `Icc (-c/2) (c/2) ×ˢ uIcc a b ⊆ Icc (-c/2) (c/2) ×ˢ Icc 0 T`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The function `(q, σ) ↦ F σ (q, η)` is integrable on `Ioc (-c/2) (c/2) × uIoc a b` for the product
of the restricted Lebesgue measures.  It is continuous on the compact rectangle
`Icc (-c/2) (c/2) ×ˢ uIcc a b`, whose second factor lies in `Icc 0 T`. -/
theorem pbHI_integrable (c T : ℝ) (F : ℝ → Plane → ℝ) (a b η : ℝ)
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T)
    (hcont : ContinuousOn (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) :
    Integrable (fun p : ℝ × ℝ => F p.2 (p.1, η))
      ((volume.restrict (Ioc (-c / 2) (c / 2))).prod (volume.restrict (uIoc a b))) := by
  rw [Measure.prod_restrict]
  have hmap : Continuous (fun p : ℝ × ℝ => (p.2, (p.1, η))) := by fun_prop
  have hK : ContinuousOn (fun p : ℝ × ℝ => F p.2 (p.1, η))
      (Icc (-c / 2) (c / 2) ×ˢ uIcc a b) := by
    refine hcont.comp hmap.continuousOn ?_
    intro p hp
    have hp2 : p.2 ∈ uIcc a b := (mem_prod.mp hp).2
    exact mk_mem_prod (uIcc_subset_Icc ha hb hp2) (mem_univ _)
  have hcpt : IsCompact (Icc (-c / 2) (c / 2) ×ˢ uIcc a b) :=
    isCompact_Icc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => F p.2 (p.1, η))
      (Icc (-c / 2) (c / 2) ×ˢ uIcc a b) (volume.prod volume) :=
    hK.integrableOn_compact hcpt
  exact hint.mono_set (prod_mono Ioc_subset_Icc_self uIoc_subset_uIcc)

/-- Fubini on the rectangle, stated with the set integral over `uIoc a b`. -/
theorem pbHI_swap (c T : ℝ) (F : ℝ → Plane → ℝ) (a b η : ℝ)
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T)
    (hcont : ContinuousOn (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) :
    ∫ q in Ioc (-c / 2) (c / 2), ∫ σ in uIoc a b, F σ (q, η) =
      ∫ σ in uIoc a b, ∫ q in Ioc (-c / 2) (c / 2), F σ (q, η) :=
  integral_integral_swap (f := fun q σ => F σ (q, η)) (pbHI_integrable c T F a b η ha hb hcont)

/-- The same interchange with the interval integral `∫ σ in a..b` (sign factor shared by both sides). -/
theorem pbHI_swap_interval (c T : ℝ) (F : ℝ → Plane → ℝ) (a b η : ℝ)
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T)
    (hcont : ContinuousOn (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) :
    ∫ q in Ioc (-c / 2) (c / 2), ∫ σ in a..b, F σ (q, η) =
      ∫ σ in a..b, ∫ q in Ioc (-c / 2) (c / 2), F σ (q, η) := by
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, MeasureTheory.integral_smul]
  rw [pbHI_swap c T F a b η ha hb hcont]

/-- **`PbHmeanTimeIntegral`** (Fubini for the horizontal average; source line 447): the normalized
horizontal average commutes with a time integral over `[a,b] ⊆ [0,T]`. -/
theorem pbHmeanTimeIntegral : PbHmeanTimeIntegral := by
  intro c T F a b hc ha hb hcont η
  simp only [hmean]
  rw [intervalIntegral.integral_smul, pbHI_swap_interval c T F a b η ha hb hcont]

end UnforcedLeray.Short.PartI
