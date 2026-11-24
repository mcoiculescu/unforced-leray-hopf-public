import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T04/5/1/3/2`: cross term of the cutoff energy identity

Target: `apEnergyCrossEstimate : APEnergyCrossEstimate` (`Short/PartI/Sub/PartI_T04_5_1_3.lean`).
Source of record: `the November 2 reference manuscript`, lines 278-286.

Route. `|χ_R'| ≤ C₀/R` (`EtaCutoffFacts`, since `√χ_R ≤ 1`), `|∂_η v| ≤ |Dv|`, and the pointwise
bound `|χ' ⟨v, ∂_η v⟩| ≤ (C₀/R)/2 · (|v|² + |Dv|²)`.  Integrating over the cell and using
`jet_l2` at `j = 0, 1` gives the bound `(C₀/R)/2 · (K₀ + K₁) ≤ C/√R` (since `1/R ≤ 1/√R`).
No Cauchy-Schwarz is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **Leaf 2 (cross term)**: `|∫ χ_R' ⟨v, ∂_η v⟩| ≤ C/√R`. -/
theorem apEnergyCrossEstimate : APEnergyCrossEstimate := by
  intro ν c T v p hν hc hcls
  have hF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hF
  obtain ⟨C0, hC0, hcut⟩ := hF
  obtain ⟨K0, hK0⟩ := hcls.jet_l2 0
  obtain ⟨K1, hK1⟩ := hcls.jet_l2 1
  have hS : 0 ≤ |K0| + |K1| := by positivity
  refine ⟨C0 * (|K0| + |K1|) / 2, div_nonneg (mul_nonneg hC0 hS) (by norm_num), ?_⟩
  intro R hR s hs
  have hR0 : 0 < R := by linarith
  obtain ⟨-, hbd, -, -, hd⟩ := hcut R hR
  -- `|χ_R'| ≤ C₀ / R` everywhere
  have hdbd : ∀ η : ℝ, |deriv (etaCutoff R) η| ≤ C0 / R := by
    intro η
    have h1 := hd η
    have hs1 : Real.sqrt (etaCutoff R η) ≤ 1 :=
      (Real.sqrt_le_sqrt (hbd η).2).trans_eq Real.sqrt_one
    have hk : 0 ≤ C0 / R := div_nonneg hC0 hR0.le
    calc |deriv (etaCutoff R) η| ≤ C0 / R * Real.sqrt (etaCutoff R η) := h1
      _ ≤ C0 / R * 1 := mul_le_mul_of_nonneg_left hs1 hk
      _ = C0 / R := mul_one _
  -- `1 ≤ √R ≤ R` and `1/R ≤ 1/√R`
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hs1 : 1 ≤ Real.sqrt R := by
    have := Real.sqrt_le_sqrt hR
    rwa [Real.sqrt_one] at this
  have hsqle : Real.sqrt R ≤ R := by
    nlinarith [Real.sq_sqrt hR0.le, Real.sqrt_nonneg R,
      mul_nonneg (sub_nonneg.2 hs1) (Real.sqrt_nonneg R)]
  have h1R : 1 / R ≤ 1 / Real.sqrt R := one_div_le_one_div_of_le hsR hsqle
  -- the slice `v(s)` is smooth, hence differentiable
  have hdiff : Differentiable ℝ (v s) :=
    (hcls.classical.contDiff_slice (Ioo_subset_Icc_self hs)).differentiable (by simp)
  obtain ⟨hI0, hV0⟩ := hK0 s (Ioo_subset_Icc_self hs)
  obtain ⟨hI1, hV1⟩ := hK1 s (Ioo_subset_Icc_self hs)
  have hV0' : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 ≤ K0 := hV0
  have hV1' : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2 ≤ K1 := hV1
  -- pointwise majorant
  have hpoint : ∀ z : Plane,
      ‖deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)‖ ≤
        C0 / R / 2 * (‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) := by
    intro z
    have hpe : ‖Cyl.partialEta (v s) z‖ ≤ ‖iteratedFDeriv ℝ 1 (v s) z‖ := by
      rw [norm_iteratedFDeriv_one, Cyl.partialEta_eq_fderiv hdiff z]
      have h01 : ‖fderiv ℝ (v s) z (0, 1)‖ ≤ ‖fderiv ℝ (v s) z‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
        (fderiv ℝ (v s) z).le_opNorm _
      have h1' : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp
      calc ‖fderiv ℝ (v s) z (0, 1)‖ ≤ ‖fderiv ℝ (v s) z‖ * ‖((0 : ℝ), (1 : ℝ))‖ := h01
        _ ≤ ‖fderiv ℝ (v s) z‖ * 1 := mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
        _ = ‖fderiv ℝ (v s) z‖ := mul_one _
    have hu : ‖v s z‖ = ‖iteratedFDeriv ℝ 0 (v s) z‖ := by rw [norm_iteratedFDeriv_zero]
    have hnorm : ‖deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)‖ =
        |deriv (etaCutoff R) z.2| * |inner ℝ (v s z) (Cyl.partialEta (v s) z)| := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hinner : |inner ℝ (v s z) (Cyl.partialEta (v s) z)| ≤
        ‖v s z‖ * ‖Cyl.partialEta (v s) z‖ := abs_real_inner_le_norm _ _
    have hxy : |deriv (etaCutoff R) z.2| * |inner ℝ (v s z) (Cyl.partialEta (v s) z)| ≤
        C0 / R * (‖v s z‖ * ‖Cyl.partialEta (v s) z‖) :=
      mul_le_mul (hdbd z.2) hinner (abs_nonneg _) (div_nonneg hC0 hR0.le)
    have hm2 : ‖iteratedFDeriv ℝ 0 (v s) z‖ * ‖iteratedFDeriv ℝ 1 (v s) z‖ ≤
        (‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖iteratedFDeriv ℝ 0 (v s) z‖ - ‖iteratedFDeriv ℝ 1 (v s) z‖)]
    have hm1 : ‖iteratedFDeriv ℝ 0 (v s) z‖ * ‖Cyl.partialEta (v s) z‖ ≤
        ‖iteratedFDeriv ℝ 0 (v s) z‖ * ‖iteratedFDeriv ℝ 1 (v s) z‖ :=
      mul_le_mul_of_nonneg_left hpe (norm_nonneg _)
    have hm3 : C0 / R * (‖iteratedFDeriv ℝ 0 (v s) z‖ * ‖Cyl.partialEta (v s) z‖) ≤
        C0 / R * ((‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left (hm1.trans hm2) (div_nonneg hC0 hR0.le)
    rw [hnorm]
    calc |deriv (etaCutoff R) z.2| * |inner ℝ (v s z) (Cyl.partialEta (v s) z)|
        ≤ C0 / R * (‖v s z‖ * ‖Cyl.partialEta (v s) z‖) := hxy
      _ = C0 / R * (‖iteratedFDeriv ℝ 0 (v s) z‖ * ‖Cyl.partialEta (v s) z‖) := by rw [hu]
      _ ≤ C0 / R * ((‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) / 2) :=
          hm3
      _ = C0 / R / 2 * (‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) := by
          ring
  -- integrate the majorant
  have hg : IntegrableOn (fun z : Plane => C0 / R / 2 *
      (‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2)) (Cyl.cell c) :=
    (hI0.add hI1).const_mul _
  have hint : ∫ z in Cyl.cell c,
      ‖deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)‖ ≤
        ∫ z in Cyl.cell c, C0 / R / 2 *
          (‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hg
      (Filter.Eventually.of_forall hpoint)
  have hsplit : ∫ z in Cyl.cell c, C0 / R / 2 *
      (‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2 + ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) =
      C0 / R / 2 * ((∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2) +
        ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) := by
    rw [integral_const_mul, integral_add hI0 hI1]
  have hfin : C0 / R / 2 * ((∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2) +
        ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) ≤
      C0 / R / 2 * (|K0| + |K1|) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self K0, le_abs_self K1])
      (div_nonneg (div_nonneg hC0 hR0.le) (by norm_num))
  have hfin2 : C0 / R / 2 * (|K0| + |K1|) ≤ C0 * (|K0| + |K1|) / 2 / Real.sqrt R := by
    have e1 : C0 / R / 2 * (|K0| + |K1|) = (C0 * (|K0| + |K1|) / 2) * (1 / R) := by ring
    have e2 : C0 * (|K0| + |K1|) / 2 / Real.sqrt R =
        (C0 * (|K0| + |K1|) / 2) * (1 / Real.sqrt R) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1R (div_nonneg (mul_nonneg hC0 hS) (by norm_num))
  calc |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)|
      = ‖∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ z in Cyl.cell c, ‖deriv (etaCutoff R) z.2 * inner ℝ (v s z) (Cyl.partialEta (v s) z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ _ := hint
    _ = C0 / R / 2 * ((∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (v s) z‖ ^ 2) +
        ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2) := hsplit
    _ ≤ C0 / R / 2 * (|K0| + |K1|) := hfin
    _ ≤ C0 * (|K0| + |K1|) / 2 / Real.sqrt R := hfin2

end UnforcedLeray.Short.PartI
