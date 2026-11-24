import UnforcedLeray.Short.PartIIIa.Sub.T20_3
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.WeightedHolder

/-!
# Part III-a, task `PartIII-a:T20/3/3`: `X_m ⊂ L¹(cell)` (`L1Integrable`)

Source of record: `the November 2 reference manuscript`, lines 3237-3239.
Target: `L1Integrable` in `Sub/T20_3.lean` (`m > 1`).

Proof. Apply `weightedHolder` with `g = 1`. Its hypothesis is `∫_cell jb^{-m} < ∞`. For
`m > 1`, `∫_{ℝ²} jb^{-m} < ∞` because `1 + ‖x‖² ≤ jb x` (sup norm on `ℝ × ℝ`) and Mathlib's
`integrable_rpow_neg_one_add_norm_sq` applies with `finrank ℝ (ℝ × ℝ) = 2 < 2m`. Restricting to
the cell is `cellVol c ≤ volume`. The conclusion `|ω| ∈ L¹(cell)` gives `ω ∈ L¹(cell)` by
`Integrable.mono'`, using `AEStronglyMeasurable` of `ω` for `cellMeasure`, which is
absolutely continuous with respect to `cellVol c`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

namespace L1IntegrableProof

/-- For the sup norm on `ℝ × ℝ`, `1 + ‖x‖² ≤ jb x = 1 + x₁² + x₂²`. -/
lemma one_add_norm_sq_le_jb (x : ℝ × ℝ) : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by
  have h1 : ‖x.1‖ ^ 2 = x.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖x.2‖ ^ 2 = x.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have hn : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h, h2]
      nlinarith [sq_nonneg x.1]
    · rw [max_eq_left h, h1]
      nlinarith [sq_nonneg x.2]
  unfold B0579.jb
  linarith

/-- `∫_{ℝ²} jb^{-m} < ∞` for `m > 1`. -/
lemma integrable_jb_rpow_neg (m : ℝ) (hm : 1 < m) :
    Integrable (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) volume := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by
    simp
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume)
    (r := 2 * m) (by rw [hd]; linarith)
  have hexp : -(2 * m) / 2 = -m := by ring
  rw [hexp] at h
  refine Integrable.mono' h ?_ ?_
  · exact (B0579.continuous_jb_rpow (-m)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    show ‖B0579.jb x ^ (-m)‖ ≤ (1 + ‖x‖ ^ 2) ^ (-m)
    have hpos : 0 < 1 + ‖x‖ ^ 2 := by positivity
    have hle : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := one_add_norm_sq_le_jb x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le (-m))]
    exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)

/-- `jb^{-m}` is integrable on the cell `cellVol c` for `m > 1`. -/
lemma integrable_jb_rpow_cell (c m : ℝ) (hm : 1 < m) :
    Integrable (fun x : ℝ × ℝ => B0579.jb x ^ (-m)) (B0581.cellVol c) :=
  (integrable_jb_rpow_neg m hm).mono_measure Measure.restrict_le_self

end L1IntegrableProof

/-- **`X_m ⊂ L¹(cell)`** (task `PartIII-a:T20/3/3`; SP 3237-3239; `m > 1`). For every `c > 0`
and `ω ∈ X_{m,c}`, the function `ω` is integrable on the cell. Proof: `weightedHolder` with
`g = 1` (its hypothesis is `L1Integrable`-type integrability of `jb^{-m}` on the cell), then
`ω` is dominated by `|ω|`, which is integrable. -/
theorem l1Integrable : UnforcedLeray.Short.IIIa.CTE.T20_3.L1Integrable := by
  intro m hm c _hc ω
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hgint : Integrable
      (fun x : B0579.Plane => (fun _ : B0579.Plane => (1 : ℝ)) x ^ 2 * B0579.jb x ^ (-m))
      (B0581.cellVol c) := by
    refine (L1IntegrableProof.integrable_jb_rpow_cell c m hm).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hW := weightedHolder c m ω (fun _ => 1) hm0 (fun _ => zero_le_one) measurable_const hgint
  refine Integrable.mono' hW.1 ?_ ?_
  · exact (Lp.aestronglyMeasurable ω).mono_ac (B0579.ac_cellMeasure c m)
  · exact Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs]

end UnforcedLeray.Short.IIIa.CTE.T20_3
