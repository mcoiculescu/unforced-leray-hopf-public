import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14

/-!
# Decomposition of `farMajL2` (`PartIII-b:C/near/masked/14/2`; source 3996-4011, 2683)

Source: `the November 2 reference manuscript`.

`farMajOut` is the `λ`-integral (weight `λ^{2μ+2}`, `λ ∈ (0,1)`) of the slices `farSliceOut λ`.
Minkowski in `λ` reduces `FarMajL2` to a slice bound `‖farSliceOut λ f‖ ≤ C λ^{-3/2} ‖f‖`
(Young/Hardy in the Cartesian similarity variable, normalized-phase shift, chart-to-Cartesian
lifts, 2683) and the integrability of `λ^{2μ+1/2}` on `(0,1)`, which is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The `λ`-slice of the majorant (the inner `z`-integral of `farMaj`, source 3996-4011). -/
def farSlice (R c δ : ℝ) (f : Chart → Ten3) (l : ℝ) (x : Chart) : ℝ≥0∞ :=
  ∫⁻ z : Space,
      (if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
        ENNReal.ofReal (‖chartY R x - l • z‖ ^ (-4 : ℝ) *
          UnforcedLeray.Short.IIIa.tensorNorm
            (cartLift R c f (chartTau R x + 2 * Real.log l) z)) else 0)

/-- The output-side slice `1_{s<S} s^{-1/2} farSlice`. -/
def farSliceOut (R c δ S : ℝ) (f : Chart → Ten3) (l : ℝ) (x : Chart) : ℝ≥0∞ :=
  if x.1 < S then ENNReal.ofReal (Real.sqrt x.1)⁻¹ * farSlice R c δ f l x else 0

/-- `farMajOut` is the weighted `λ`-integral of the slices (proved below). -/
theorem farMajOut_eq (R c μ δ S : ℝ) (f : Chart → Ten3) (x : Chart) :
    farMajOut R c μ δ S f x =
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) * farSliceOut R c δ S f l x := by
  unfold farMajOut farSliceOut farMaj farSlice
  by_cases h : x.1 < S
  · simp only [h, ite_true]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun l => ?_
    ring
  · simp [h]

/-- **Minkowski's integral inequality in `L²`** for nonnegative jointly measurable functions
(general fact; `λ ↦ g λ ·` into `L²(μ)`). -/
def MinkowskiL2 : Prop :=
  ∀ (μ : Measure Chart) (ν : Measure ℝ) [SFinite μ] [SFinite ν] (g : ℝ → Chart → ℝ≥0∞),
    Measurable (Function.uncurry g) →
      (∫⁻ x, (∫⁻ l, g l x ∂ν) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) ≤
        ∫⁻ l, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) ∂ν

/-- **Joint measurability of the slices** in `(λ, x)` for box tensors (the integrand is jointly
measurable in `(λ, x, z)`: `cartLift` of a measurable chart tensor composed with the measurable
`chartOf`, the floor, `chartY`, `chartTau`, `log`). -/
def FarSliceMeasurable : Prop :=
  ∀ (R c δ S : ℝ) (f : Chart → Ten3), IsBoxTensor f →
    Measurable (fun p : ℝ × Chart => farSliceOut R c δ S f p.1 p.2)

/-- **Slice `L²` bound** (source 3996-4011, 2683): for `λ ∈ (0,1)`,
`‖farSliceOut λ f‖_{L²(ageμ c (-3/2))} ≤ C λ^{-3/2} ‖f‖_{L²(ageμ c (-1/2))}` on box tensors, `C`
independent of `λ`, `f`. Proof ingredients: the pointwise majorant `|y-λz|^{-4}` on the far
region `|y-λz| ≥ (1-e^{-δ/2})|y'|` (`|y'| = R/√s`; `|λz'| < e^{-δ/2}|y'|` there), a Hardy/Schur
(or dyadic Young) bound for this homogeneous degree `-3` kernel with the weight `s^{-1/2} ∝ |y'|`
(constant `d` is output dependent, so plain Young with fixed `d` does not apply), the
substitution `w = λ z` (factor `λ^{-3/2}`), the invariance of the periodic phase under the
shift `2 log λ`, and the chart-to-Cartesian conversion of `ageμ` norms (`cartLift` multiplies both
by `√π R`, 2683). -/
def FarSliceL2 : Prop :=
  ∀ (R c δ S : ℝ), 0 < R → 0 < c → 0 < δ → 0 < S →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Chart → Ten3, IsBoxTensor f → ∀ l ∈ Ioo (0 : ℝ) 1,
      ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
        ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) *
          ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))

/-- For `μ > -1/4` the exponent `2μ + 1/2` is positive, so the moment is `≤ 1`. -/
theorem farMoment_le (μ : ℝ) (hμ : -(1 / 4) < μ) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ))
      ≤ 1 := by
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ))
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, 1 := by
        refine setLIntegral_mono measurable_const fun l hl => ?_
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _), ← Real.rpow_add hl.1]
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.rpow_le_one hl.1.le hl.2.le
        linarith
    _ = 1 := by simp

theorem farMajL2_of (h2 : MinkowskiL2) (h3 : FarSliceMeasurable) (h4 : FarSliceL2) :
    FarMajL2 := by
  intro R c δ S μ hR hc hδ hS hμ
  obtain ⟨C, hC, hsl⟩ := h4 R c δ S hR hc hδ hS
  refine ⟨C, hC, fun f hf => ?_⟩
  set m : Measure Chart := ageμ c (-3 / 2) with hm
  set F : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) with hF
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ; infer_instance
  haveI : SFinite m := by rw [hm]; unfold ageμ; infer_instance
  have hw : ∀ l : ℝ, ∀ x, ENNReal.ofReal (l ^ (2 * μ + 2)) * farSliceOut R c δ S f l x
      = ENNReal.ofReal (l ^ (2 * μ + 2)) * farSliceOut R c δ S f l x := fun _ _ => rfl
  let g : ℝ → Chart → ℝ≥0∞ := fun l x =>
    ENNReal.ofReal (l ^ (2 * μ + 2)) * farSliceOut R c δ S f l x
  have hg : Measurable (Function.uncurry g) := by
    have h1 : Measurable fun p : ℝ × Chart => ENNReal.ofReal (p.1 ^ (2 * μ + 2)) :=
      (measurable_ofReal_rpow (2 * μ + 2)).comp measurable_fst
    exact h1.mul (h3 R c δ S f hf)
  have hM := h2 m (volume.restrict (Ioo (0 : ℝ) 1)) g hg
  have hp : (0 : ℝ) < 2 := by norm_num
  have hcalc : (∫⁻ x, (farMajOut R c μ δ S f x) ^ (2 : ℝ) ∂m) ^ ((1 : ℝ) / 2) ≤
      ENNReal.ofReal C * F ^ ((1 : ℝ) / 2) := by
    calc (∫⁻ x, (farMajOut R c μ δ S f x) ^ (2 : ℝ) ∂m) ^ ((1 : ℝ) / 2)
        = (∫⁻ x, (∫⁻ l in Ioo (0 : ℝ) 1, g l x) ^ (2 : ℝ) ∂m) ^ ((1 : ℝ) / 2) := by
          simp only [farMajOut_eq]; rfl
      _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, (∫⁻ x, (g l x) ^ (2 : ℝ) ∂m) ^ ((1 : ℝ) / 2) := hM
      _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) * (ENNReal.ofReal C * F ^ ((1 : ℝ) / 2)) := by
          refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
          have hw0 : (0 : ℝ) ≤ l ^ (2 * μ + 2) := Real.rpow_nonneg hl.1.le _
          have e : ∫⁻ x, (g l x) ^ (2 : ℝ) ∂m =
              ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
                ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂m := by
            simp only [g, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
            exact lintegral_const_mul' _ _
              (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
          rw [e]
          have hb := hsl f hf l hl
          calc (ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
                ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂m) ^ ((1 : ℝ) / 2)
              ≤ (ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
                  (ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) *
                    F)) ^ ((1 : ℝ) / 2) := by
                gcongr
            _ = _ := by
                have : ENNReal.ofReal (l ^ (2 * μ + 2)) ^ (2 : ℝ) *
                    (ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) * F)
                    = (ENNReal.ofReal (l ^ (2 * μ + 2)) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) *
                        ENNReal.ofReal C) ^ (2 : ℝ) * F := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
                  ring
                rw [this, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
                norm_num
                ring
      _ = (∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
            ENNReal.ofReal (l ^ (-3 / 2 : ℝ))) * (ENNReal.ofReal C * F ^ ((1 : ℝ) / 2)) := by
          exact lintegral_mul_const _ (by
            have h1 : Measurable fun l : ℝ => ENNReal.ofReal (l ^ (2 * μ + 2)) :=
              measurable_ofReal_rpow _
            have h2 : Measurable fun l : ℝ => ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) :=
              measurable_ofReal_rpow _
            exact h1.mul h2)
      _ ≤ 1 * (ENNReal.ofReal C * F ^ ((1 : ℝ) / 2)) := by
          gcongr
          exact farMoment_le μ hμ
      _ = _ := one_mul _
  have h5 := ENNReal.rpow_le_rpow hcalc hp.le
  have e : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [← ENNReal.rpow_mul, e, ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ← ENNReal.rpow_mul F, e, ENNReal.rpow_one] at h5
  exact h5

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
