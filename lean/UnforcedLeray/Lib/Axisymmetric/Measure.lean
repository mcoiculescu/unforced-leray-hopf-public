import UnforcedLeray.Lib.Axisymmetric.Cylindrical
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# AX02: cylindrical integration on `ℝ³`


§5 Layer 3, target AX02 (`Axi/Measure.lean`), bypass BP10 (§4). Blueprint units served:
B0197 (`eq:st18-t00198`, tex 2994–3003), B0550 (tex 8724–8732), B0782 (tex 11237–11243).

`lintegral_cylindrical` is the full change of variables
`∫ f dy = ∫_{r>0} ∫_{−π<θ<π} ∫_z r f(r cos θ, r sin θ, z) dz dθ dr` for nonnegative measurable
`f`, built from `PiLp.volume_preserving_toLp`, `volume_preserving_piFinSuccAbove`,
`volume_preserving_finTwoArrow` and Mathlib's planar `lintegral_comp_polarCoord_symm`. The
argument follows the radial case `lintegral_space_axisymmetric` of the unit draft

formalization `NonUniqueEuler/lean/NonUniqueEuler/P/Infra/Polar/Radial.lean`), extended to
non-radial integrands. `lintegral_axisymm` integrates the angle out, and `volume_axis` says
that the axis is a null set (so the Lean junk values of the frame on the axis never matter).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.Axi

/-- Cylindrical coordinates `((r, θ), z) ↦ (r cos θ, r sin θ, z)`. -/
def cylMap (p : (ℝ × ℝ) × ℝ) : Space :=
  !₂[p.1.1 * Real.cos p.1.2, p.1.1 * Real.sin p.1.2, p.2]

theorem continuous_cylMap : Continuous cylMap := by
  unfold cylMap
  fun_prop

theorem measurable_cylMap : Measurable cylMap := continuous_cylMap.measurable

theorem measurable_toLp_three : Measurable (@WithLp.toLp 2 (Fin 3 → ℝ)) :=
  (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable

theorem measurable_ϱ : Measurable ϱ := continuous_ϱ.measurable

theorem measurable_coord (i : Fin 3) : Measurable fun y : Space => y i :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable

theorem measurable_mer : Measurable mer :=
  measurable_ϱ.prodMk (measurable_coord 2)

/-- Restriction to `s ×ˢ univ` of a product measure, as an iterated integral. -/
theorem setLIntegral_prod_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] (s : Set α)
    {H : α × β → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p in s ×ˢ (univ : Set β), H p ∂(μ.prod ν) = ∫⁻ a in s, ∫⁻ b, H (a, b) ∂ν ∂μ := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hH.aemeasurable]

/-- The coordinates of `Space` as `ℝ × (ℝ × ℝ)`: `y ↦ (y₃, (y₁, y₂))`, inverse direction. -/
theorem toLp_piFinSuccAbove_symm (z : ℝ) (q : ℝ × ℝ) :
    WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).symm
      (z, (MeasurableEquiv.finTwoArrow).symm q)) = !₂[q.1, q.2, z] := by
  ext i
  fin_cases i <;> rfl

/-- **AX02 `lintegral_cylindrical`** (BP10). For nonnegative measurable `f` on `ℝ³`,
`∫ f dy = ∫_{(r,θ) ∈ (0,∞) × (−π,π)} ∫_z r f(r cos θ, r sin θ, z)`. -/
theorem lintegral_cylindrical (f : Space → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y =
      ∫⁻ p in (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal p.1.1 * f (cylMap p) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2) with he_def
  have hF : Measurable fun v : Fin 3 → ℝ => f (WithLp.toLp 2 v) := hf.comp measurable_toLp_three
  -- Step 1: `Space ≃ (Fin 3 → ℝ)`
  have h1 : ∫⁻ y, f y = ∫⁻ v : Fin 3 → ℝ, f (WithLp.toLp 2 v) :=
    ((PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp hf).symm
  -- Step 2: `(Fin 3 → ℝ) ≃ ℝ × (Fin 2 → ℝ)`, splitting off the last coordinate
  have he : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))
  have h2 : ∫⁻ v : Fin 3 → ℝ, f (WithLp.toLp 2 v) =
      ∫⁻ u : ℝ × (Fin 2 → ℝ), f (WithLp.toLp 2 (e.symm u)) :=
    (he.lintegral_comp hF).symm
  have hF2 : Measurable fun u : ℝ × (Fin 2 → ℝ) => f (WithLp.toLp 2 (e.symm u)) :=
    hF.comp e.symm.measurable
  -- Step 3: Tonelli in `(z, w)`, then `(Fin 2 → ℝ) ≃ ℝ × ℝ` and planar polar coordinates
  have h3 : ∀ z : ℝ, ∫⁻ w : Fin 2 → ℝ, f (WithLp.toLp 2 (e.symm (z, w))) =
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal q.1 * f (cylMap (q, z)) := by
    intro z
    have hK : Measurable fun w : Fin 2 → ℝ => f (WithLp.toLp 2 (e.symm (z, w))) :=
      hF2.comp measurable_prodMk_left
    have hA := (MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)).lintegral_comp hK
    rw [← hA]
    have hB : ∀ q : ℝ × ℝ, f (WithLp.toLp 2 (e.symm (z, (MeasurableEquiv.finTwoArrow).symm q))) =
        f !₂[q.1, q.2, z] := fun q => by rw [toLp_piFinSuccAbove_symm]
    rw [lintegral_congr hB, ← lintegral_comp_polarCoord_symm]
    rfl
  rw [h1, h2, Measure.volume_eq_prod, lintegral_prod _ hF2.aemeasurable, lintegral_congr h3]
  -- Step 4: swap `z` with `(r, θ)` and recombine
  have hH : Measurable fun p : (ℝ × ℝ) × ℝ => ENNReal.ofReal p.1.1 * f (cylMap p) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (hf.comp measurable_cylMap)
  rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ, setLIntegral_prod_univ _ hH]
  refine lintegral_lintegral_swap ?_
  exact (hH.comp measurable_swap).aemeasurable

theorem ϱ_cylMap {p : (ℝ × ℝ) × ℝ} (hp : 0 < p.1.1) : ϱ (cylMap p) = p.1.1 := by
  have h : (cylMap p) 0 ^ 2 + (cylMap p) 1 ^ 2 = p.1.1 ^ 2 := by
    simp only [cylMap]
    show (p.1.1 * Real.cos p.1.2) ^ 2 + (p.1.1 * Real.sin p.1.2) ^ 2 = p.1.1 ^ 2
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [ϱ, h, Real.sqrt_sq hp.le]

theorem cylMap_two (p : (ℝ × ℝ) × ℝ) : (cylMap p) 2 = p.2 := rfl

/-- **AX02 `lintegral_axisymm`.** For nonnegative measurable `g` on the meridian plane,
`∫ g(ϱ(y), y₃) dy = 2π ∫_{ρ>0} ∫_z ρ g(ρ, z)`. -/
theorem lintegral_axisymm (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (ϱ y, y 2) =
      ENNReal.ofReal (2 * π) * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 * g p := by
  have hgm : Measurable fun y : Space => g (ϱ y, y 2) := hg.comp measurable_mer
  rw [lintegral_cylindrical _ hgm]
  have hS : MeasurableSet ((Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ×ˢ (univ : Set ℝ)) :=
    (measurableSet_Ioi.prod measurableSet_Ioo).prod MeasurableSet.univ
  rw [setLIntegral_congr_fun hS (g := fun p : (ℝ × ℝ) × ℝ => ENNReal.ofReal p.1.1 * g (p.1.1, p.2))
    (fun p hp => by
      simp only [ϱ_cylMap hp.1.1, cylMap_two])]
  have hH : Measurable fun p : (ℝ × ℝ) × ℝ => ENNReal.ofReal p.1.1 * g (p.1.1, p.2) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst)).mul
      (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hH' : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * g p :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul hg
  rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ, setLIntegral_prod_univ _ hH, Measure.volume_eq_prod ℝ ℝ,
    setLIntegral_prod_univ _ hH', ← Measure.prod_restrict]
  have hK : Measurable fun q : ℝ × ℝ => ∫⁻ z, ENNReal.ofReal q.1 * g (q.1, z) :=
    (hH.comp (by fun_prop : Measurable fun x : (ℝ × ℝ) × ℝ => ((x.1.1, x.1.2), x.2))
      ).lintegral_prod_right'
  rw [lintegral_prod _ hK.aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => ?_
  rw [mul_comm]
  congr 1
  congr 1
  ring

/-- **AX02 `volume_axis`.** The axis is a Lebesgue null set. -/
theorem volume_axis : volume axis = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 = 0} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have h := lintegral_axisymm ({p : ℝ × ℝ | p.1 = 0}.indicator 1)
    (measurable_one.indicator hm)
  have hrhs : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal p.1 * {p : ℝ × ℝ | p.1 = 0}.indicator 1 p = 0 := by
    rw [setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
      (g := fun _ => 0) (fun p hp => by
        have hp1 : p.1 ≠ 0 := ne_of_gt hp.1
        have : p ∉ {p : ℝ × ℝ | p.1 = 0} := hp1
        simp [Set.indicator_of_notMem this])]
    simp
  rw [hrhs, mul_zero] at h
  have hl : ∫⁻ y, {p : ℝ × ℝ | p.1 = 0}.indicator (1 : ℝ × ℝ → ℝ≥0∞) (ϱ y, y 2) =
      volume axis := by
    rw [← lintegral_indicator_one isClosed_axis.measurableSet]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ axis
    · have h0 : ϱ y = 0 := (mem_axis_iff y).1 hy
      simp [Set.indicator, hy, h0]
    · have h0 : ϱ y ≠ 0 := ϱ_ne_zero hy
      simp [Set.indicator, hy, h0]
  rw [← hl, h]

theorem ae_not_mem_axis : ∀ᵐ y : Space, y ∉ axis :=
  measure_eq_zero_iff_ae_notMem.1 volume_axis

end UnforcedLeray.Axi
