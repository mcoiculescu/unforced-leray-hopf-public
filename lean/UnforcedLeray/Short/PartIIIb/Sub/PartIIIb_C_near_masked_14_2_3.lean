import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2.SliceMeas

/-!
# Decomposition of `farSliceL2` (`PartIII-b:C/near/masked/14/2/3`; source 3996-4011, 3604-3610, 2683)

Source: `the November 2 reference manuscript`.

`FarSliceL2` splits into three independent steps around the Cartesian slice operator
`cartSliceOut` (the `λ`-slice written in the Cartesian similarity variable `y ∈ ℝ³`, with the
tensor norm `g = |cartLift f (τ + 2 log λ)|` as input):

* `FarOutChange` (chart-to-Cartesian on the output side, with the phase sweep): the
  `L²(ageμ c (-3/2))` norm of the slice is `K₁ ∫_{τ ∈ one period} ‖cartSliceOut g_{τ+2 log λ}‖²_{L²(ℝ³)}`.
  (`y = (R/√s, 0, η/√s)`, `dy = π R² s^{-5/2} ds dη`-type Jacobian, `q ↦ τ = 2q/R + log s` with the
  period `2c/R`, axisymmetry for the azimuth.)
* `CartSchur` (the Hardy/Schur estimate, steps (b)-(d) of the task): for the homogeneous degree
  `-3` kernel `|y'| |y - λ z|^{-4} 1{e^δ |z'|² < |y'|²}`, `‖·‖_{L²(ℝ³)} ≤ C λ^{-3/2} ‖g‖_{L²(ℝ³)}`.
* `CartInput` (chart-to-Cartesian on the input side, with the phase shift (e)): for every shift `a`,
  `∫_{τ ∈ one period} ‖cartLift f (τ + a)‖²_{L²(ℝ³)} ≤ K₂ ‖f‖²_{L²(ageμ c (-1/2))}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The slice operator in the Cartesian similarity variable `y`: with the age `s = R²/|y'|²`,
`1_{s<S} s^{-1/2} ∫_z 1_{e^δ s < R²/|z'|²} |y - λ z|^{-4} g(z) dz` (source 3996-4011). -/
def cartSliceOut (R δ S l : ℝ) (g : Space → ℝ) (y : Space) : ℝ≥0∞ :=
  if R ^ 2 / (y 0 ^ 2 + y 1 ^ 2) < S then
    ENNReal.ofReal (Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)))⁻¹ *
      ∫⁻ z : Space,
        (if Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
          ENNReal.ofReal (‖y - l • z‖ ^ (-4 : ℝ) * g z) else 0)
  else 0

/-- The squared `L²(ℝ³)` norm of `cartSliceOut`. -/
def cartOut (R δ S l : ℝ) (g : Space → ℝ) : ℝ≥0∞ :=
  ∫⁻ y : Space, (cartSliceOut R δ S l g y) ^ (2 : ℝ)

/-- The tensor norm of the Cartesian lift at phase `τ`. -/
def liftNorm (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space) : ℝ :=
  UnforcedLeray.Short.IIIa.tensorNorm (cartLift R c f τ z)

/-- **Output chart-to-Cartesian conversion** (source 2683, 3604-3610, 3996-4011), including the
phase sweep (the periodic phase `τ = 2q/R + log s` runs over one period `2c/R` as `q` runs over the
cell, for each fixed `y = (R/√s,0,η/√s)`; the lifted norm is `2c/R`-periodic and axisymmetric, so the
azimuth integral is a constant). `K₁` depends on `R, c` only. -/
def FarOutChange : Prop :=
  ∀ (R c δ S : ℝ), 0 < R → 0 < c → 0 < δ → 0 < S →
    ∃ K₁ : ℝ≥0∞, K₁ ≠ ⊤ ∧ ∀ f : Chart → Ten3, IsBoxTensor f → ∀ l ∈ Ioo (0 : ℝ) 1,
      ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2)) ≤
        K₁ * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R),
          cartOut R δ S l (liftNorm R c f (τ + 2 * Real.log l))

/-- **Hardy/Schur bound** (source 3996-4011): the homogeneous degree `-3` kernel
`|y'| |y - λ z|^{-4} 1{e^δ |z'|² < |y'|²}` (`|y - λz| ≥ (1-e^{-δ/2})|y'|` there since `λ < 1`) is
bounded on `L²(ℝ³)` by `C λ^{-3/2}` (Schur test with a power weight; scaling `w = λ z` gives
`λ^{-3/2}`). -/
def CartSchur : Prop :=
  ∀ (R δ S : ℝ), 0 < R → 0 < δ → 0 < S →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l ∈ Ioo (0 : ℝ) 1, ∀ g : Space → ℝ, Measurable g → (∀ z, 0 ≤ g z) →
      cartOut R δ S l g ≤
        ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) *
          ∫⁻ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ)

/-- **Input chart-to-Cartesian conversion** (source 2683, 3604-3610) with the phase shift: the
lift `cartLift f τ` is `2c/R`-periodic in `τ`, and `∫_{one period} ∫_z |cartLift f (τ + a)|² dz dτ`
is, for every shift `a`, a constant multiple of `∫ |f|² d ageμ c (-1/2)` (`dz = π R² s^{-5/2} ds dη`,
`|sT|² = s² |T|²`, `dτ = (2/R) dq`; `tensorNorm (nsSym T) ≤ |T|`). -/
def CartInput : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c →
    ∃ K₂ : ℝ≥0∞, K₂ ≠ ⊤ ∧ ∀ f : Chart → Ten3, IsBoxTensor f → ∀ a : ℝ,
      ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ∫⁻ z : Space, ENNReal.ofReal (liftNorm R c f (τ + a) z) ^ (2 : ℝ)
        ≤ K₂ * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2))

lemma measurable_liftNorm (R c : ℝ) (f : Chart → Ten3) (hf : Measurable f) (τ : ℝ) :
    Measurable (liftNorm R c f τ) := by
  unfold liftNorm UnforcedLeray.Short.IIIa.tensorNorm
  apply Measurable.sqrt
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (((UnforcedLeray.Short.PartIIIb.Concrete.T8_1.measurable_cartLift_entry R c f hf i j).comp
    (measurable_const.prodMk measurable_id)).pow_const 2)

lemma liftNorm_nonneg (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space) : 0 ≤ liftNorm R c f τ z := by
  unfold liftNorm UnforcedLeray.Short.IIIa.tensorNorm
  exact Real.sqrt_nonneg _

/-- Composition: `FarSliceL2` follows from the three steps. -/
theorem farSliceL2_of (h1 : FarOutChange) (h2 : CartSchur) (h3 : CartInput) : FarSliceL2 := by
  intro R c δ S hR hc hδ hS
  obtain ⟨K₁, hK₁, hout⟩ := h1 R c δ S hR hc hδ hS
  obtain ⟨C, hC, hsch⟩ := h2 R δ S hR hδ hS
  obtain ⟨K₂, hK₂, hin⟩ := h3 R c hR hc
  have hp : (0 : ℝ) < 2 := by norm_num
  refine ⟨C * Real.sqrt ((K₁ * K₂).toReal), mul_nonneg hC (Real.sqrt_nonneg _), fun f hf l hl => ?_⟩
  set F : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) with hF
  have hKK : K₁ * K₂ ≠ ⊤ := ENNReal.mul_ne_top hK₁ hK₂
  have hc' : ENNReal.ofReal (C * Real.sqrt ((K₁ * K₂).toReal)) ^ (2 : ℝ) =
      ENNReal.ofReal C ^ (2 : ℝ) * (K₁ * K₂) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow
      (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKK]
  calc ∫⁻ x, (farSliceOut R c δ S f l x) ^ (2 : ℝ) ∂(ageμ c (-3 / 2))
      ≤ K₁ * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R),
          cartOut R δ S l (liftNorm R c f (τ + 2 * Real.log l)) := hout f hf l hl
    _ ≤ K₁ * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R),
          (ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ)) *
            ∫⁻ z : Space, ENNReal.ofReal (liftNorm R c f (τ + 2 * Real.log l) z) ^ (2 : ℝ) := by
        gcongr with τ
        exact hsch l hl _ (measurable_liftNorm R c f hf.measurable _)
          (liftNorm_nonneg R c f _)
    _ = K₁ * ((ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ)) *
          ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R),
            ∫⁻ z : Space, ENNReal.ofReal (liftNorm R c f (τ + 2 * Real.log l) z) ^ (2 : ℝ)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top))]
    _ ≤ K₁ * ((ENNReal.ofReal C ^ (2 : ℝ) * ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ)) *
          (K₂ * F)) := by
        gcongr
        exact hin f hf (2 * Real.log l)
    _ = ENNReal.ofReal (C * Real.sqrt ((K₁ * K₂).toReal)) ^ (2 : ℝ) *
          ENNReal.ofReal (l ^ (-3 / 2 : ℝ)) ^ (2 : ℝ) * F := by
        rw [hc']; ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
