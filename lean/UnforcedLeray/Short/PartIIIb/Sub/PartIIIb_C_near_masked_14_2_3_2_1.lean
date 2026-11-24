import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2.SchurOne.Schur

/-!
# `SchurOne` from the two Schur kernel bounds (`PartIII-b:C/near/masked/14/2/3/2/1`; source 3996-4011)

Source: `the November 2 reference manuscript`.

Kernel `K y z = (ρ(y)/R) |y-z|^{-4} 1{e^δ R²/ρ(y)² < R²/|z'|²}`, `ρ(y) = √(y₀²+y₁²)`, weight
`w = ρ^{-1}` (`1` on the axis).  The abstract weighted Schur test (`SchurOneHelp.schur_test`) plus the
two weighted kernel integrals `SchurKerA`, `SchurKerB` (source 3996-4011: on the support
`|z'| < e^{-δ/2} ρ(y)` one has `|y-z| ≥ (1-e^{-δ/2}) ρ(y)`; `z'`-plane integral of `ρ(z)^{-1}` over
the disc, `z₂`-integral of `(a²+t²)^{-2}`) give `SchurOne`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The planar radius `ρ(y) = √(y₀²+y₁²)`. -/
def rhoP (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

/-- The Schur kernel of `SchurOne` (source 3996-4011). -/
def schurK (R δ : ℝ) (y z : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (rhoP y / R) *
    (if Real.exp δ * (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
      ENNReal.ofReal (‖y - z‖ ^ (-4 : ℝ)) else 0)

/-- The Schur weight `ρ^{-1}` (and `1` on the axis, where the kernel vanishes). -/
def schurW (y : Space) : ℝ≥0∞ :=
  if y 0 ^ 2 + y 1 ^ 2 = 0 then 1 else ENNReal.ofReal (rhoP y)⁻¹

/-- The axis `{y₀ = y₁ = 0}` is Lebesgue-null in `ℝ³`. -/
def AxisNull14 : Prop :=
  MeasureTheory.volume {y : Space | y 0 ^ 2 + y 1 ^ 2 = 0} = 0

/-- Row bound (source 3996-4011): `∫ K(y,z) w(z) dz ≤ A w(y)`, with `A < ∞` depending on `R, δ`
(`|y-z| ≥ (1-e^{-δ/2})ρ(y)` on the support; `∫_{|z'|<θρ(y)} ρ(z')^{-1} dz' = 2π θ ρ(y)`;
`∫_ℝ (a²+t²)^{-2} dt = (π/2) a^{-3}`). -/
def SchurKerA : Prop :=
  ∀ R δ : ℝ, 0 < R → 0 < δ → ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ y : Space,
    ∫⁻ z : Space, schurK R δ y z * schurW z ≤ A * schurW y

/-- Column bound (source 3996-4011): `∫ K(y,z) w(y) dy ≤ B w(z)`, with `B < ∞` depending on `R, δ`
(on the support `ρ(y) > e^{δ/2}|z'|`, `|y-z| ≥ (1-θ)ρ(y)`; exterior planar integral
`∫_{ρ>r} ρ^{-3} = 2π/r`). -/
def SchurKerB : Prop :=
  ∀ R δ : ℝ, 0 < R → 0 < δ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ z : Space,
    ∫⁻ y : Space, schurK R δ y z * schurW y ≤ B * schurW z

lemma rhoP_nonneg (y : Space) : 0 ≤ rhoP y := Real.sqrt_nonneg _

lemma coord_meas (i : Fin 3) : Measurable (fun y : Space => y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable

lemma schurK_measurable (R δ : ℝ) : Measurable (fun p : Space × Space => schurK R δ p.1 p.2) := by
  unfold schurK rhoP
  have h1 : Measurable (fun p : Space × Space => p.1 0) :=
    (coord_meas 0).comp measurable_fst
  have h2 : Measurable (fun p : Space × Space => p.1 1) :=
    (coord_meas 1).comp measurable_fst
  have h3 : Measurable (fun p : Space × Space => p.2 0) :=
    (coord_meas 0).comp measurable_snd
  have h4 : Measurable (fun p : Space × Space => p.2 1) :=
    (coord_meas 1).comp measurable_snd
  refine Measurable.mul ?_ ?_
  · refine ENNReal.measurable_ofReal.comp ?_
    exact (Real.continuous_sqrt.measurable.comp ((h1.pow_const 2).add (h2.pow_const 2))).div_const _
  · refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt
        (measurable_const.mul (measurable_const.div ((h1.pow_const 2).add (h2.pow_const 2))))
        (measurable_const.div ((h3.pow_const 2).add (h4.pow_const 2)))
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _

lemma schurW_measurable : Measurable schurW := by
  unfold schurW rhoP
  have h1 : Measurable (fun y : Space => y 0) := coord_meas 0
  have h2 : Measurable (fun y : Space => y 1) := coord_meas 1
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun ((h1.pow_const 2).add (h2.pow_const 2)) measurable_const
  · exact ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.measurable.comp ((h1.pow_const 2).add (h2.pow_const 2))).inv

lemma schurW_ne_zero (y : Space) : schurW y ≠ 0 := by
  unfold schurW
  split_ifs with h
  · exact one_ne_zero
  · have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have : 0 < rhoP y := Real.sqrt_pos.2 hp
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 this)).ne'

lemma schurW_ne_top (y : Space) : schurW y ≠ ⊤ := by
  unfold schurW
  split_ifs with h
  · exact ENNReal.one_ne_top
  · have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have : 0 < rhoP y := Real.sqrt_pos.2 hp
    exact ENNReal.ofReal_ne_top

/-- Pointwise bridge: off the axis, the slice is bounded by the kernel integral. -/
lemma cartSliceOut_le_kernel (R δ S : ℝ) (hR : 0 < R) (g : Space → ℝ) (hg0 : ∀ z, 0 ≤ g z)
    (y : Space) (hy : y 0 ^ 2 + y 1 ^ 2 ≠ 0) :
    cartSliceOut R δ S 1 g y ≤ ∫⁻ z : Space, schurK R δ y z * ENNReal.ofReal (g z) := by
  have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
  have hrho : 0 < rhoP y := Real.sqrt_pos.2 hp
  have hsq : Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)) = R / rhoP y := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hR.le]; rfl
  have hc : ENNReal.ofReal (Real.sqrt (R ^ 2 / (y 0 ^ 2 + y 1 ^ 2)))⁻¹ =
      ENNReal.ofReal (rhoP y / R) := by
    rw [hsq, inv_div]
  unfold cartSliceOut
  split_ifs with hS
  · rw [hc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    unfold schurK
    rw [mul_assoc]
    refine mul_le_mul_right ?_ _
    split_ifs with hz
    · rw [one_smul, ← ENNReal.ofReal_mul (by positivity)]
    · simp
  · exact bot_le

/-- `SchurOne` from the two kernel bounds and the null axis. -/
theorem schurOne_of (hax : AxisNull14) (hA : SchurKerA) (hB : SchurKerB) : SchurOne := by
  intro R δ S hR hδ hS
  obtain ⟨A, hAt, hA'⟩ := hA R δ hR hδ
  obtain ⟨B, hBt, hB'⟩ := hB R δ hR hδ
  refine ⟨Real.sqrt ((A * B).toReal), Real.sqrt_nonneg _, fun g hgm hg0 => ?_⟩
  have hAB : ENNReal.ofReal (Real.sqrt ((A * B).toReal)) ^ (2 : ℝ) = A * B := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal (ENNReal.mul_ne_top hAt hBt)
  rw [hAB]
  have hgm' : Measurable (fun z => ENNReal.ofReal (g z)) := ENNReal.measurable_ofReal.comp hgm
  have key := SchurOneHelp.schur_test (volume : Measure Space) (schurK R δ) schurW A B
    (schurK_measurable R δ) schurW_measurable schurW_ne_zero schurW_ne_top hA' hB'
    (fun z => ENNReal.ofReal (g z)) hgm'
  have e2 : ∀ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ) = ENNReal.ofReal (g z) ^ 2 := by
    intro z; exact ENNReal.rpow_two _
  calc cartOut R δ S 1 g
      = ∫⁻ y : Space, (cartSliceOut R δ S 1 g y) ^ (2 : ℝ) := rfl
    _ ≤ ∫⁻ y : Space, (∫⁻ z : Space, schurK R δ y z * ENNReal.ofReal (g z)) ^ 2 := by
        refine lintegral_mono_ae ?_
        have : ∀ᵐ y : Space, y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
          rw [ae_iff]
          have h := hax
          unfold AxisNull14 at h
          convert h using 2
          ext y; simp
        filter_upwards [this] with y hy
        rw [ENNReal.rpow_two]
        exact pow_le_pow_left₀ zero_le (cartSliceOut_le_kernel R δ S hR g hg0 y hy) 2
    _ ≤ A * B * ∫⁻ z, ENNReal.ofReal (g z) ^ 2 := key
    _ = A * B * ∫⁻ z : Space, ENNReal.ofReal (g z) ^ (2 : ℝ) := by
        simp only [ENNReal.rpow_two]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
