import UnforcedLeray.Statement
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# B0220 helper: the outer chart, the profile cell and cylindrical integration

Blueprint unit B0220 (label `eq:st18-t00113`), `paper/main.tex` lines 3279–3314.

In outer Cartesian coordinates `x = (r cos φ, r sin φ, z)` the manuscript puts
`a = 1/r`, `s = r⁻²`, `q = ε⁻¹ log r + τ/(2ε)` and `η = z/(εr)` (tex lines 3283–3288).
This file defines these coordinates on `Space = EuclideanSpace ℝ (Fin 3)` (the library's
physical space, `UnforcedLeray.Statement`), the profile cell `s > 0, q ∈ (0,c], η ∈ ℝ`,
and proves the cylindrical integration formula
`∫ G(r, z) dx = 2π ∫_{r>0} ∫ r G(r,z) dz dr` for nonnegative measurable `G`.

The polar step adapts `lintegral_comp_norm` of the reference formalization
`NonUniqueEuler/lean/NonUniqueEuler/P/Infra/Polar/Radial.lean` (there on `ℂ`, here on
`ℝ × ℝ`).

On the axis `r = 0` the Lean values of `a, s, q, η` are junk (`0⁻¹ = 0`, `log 0 = 0`); the
axis is a null set (`volume_axis`), so no statement below depends on them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.B0220

/-- Profile variables `(s, q, η)`, in the manuscript's order `b(s,q,η)` (tex line 3292). -/
abbrev Profile := ℝ × ℝ × ℝ

/-- The cylindrical radius `r = √(x₁² + x₂²)` of `x = (r cos φ, r sin φ, z)`. -/
def radius (x : Space) : ℝ := √(x 0 ^ 2 + x 1 ^ 2)

/-- `a = 1/r` (tex line 3284). -/
def liftA (x : Space) : ℝ := (radius x)⁻¹

/-- The age `s = r⁻²` (tex line 3284). -/
def ageS (x : Space) : ℝ := (radius x ^ 2)⁻¹

/-- `q = ε⁻¹ log r + τ/(2ε)` (tex line 3285). -/
def cellQ (ε : ℝ) (x : Space) (τ : ℝ) : ℝ := ε⁻¹ * Real.log (radius x) + τ / (2 * ε)

/-- `η = z/(εr)` (tex line 3286). -/
def etaCoord (ε : ℝ) (x : Space) : ℝ := x 2 / (ε * radius x)

/-- The outer chart `(x, τ) ↦ (s, q, η)`. -/
def chart (ε : ℝ) (y : Space × ℝ) : Profile := (ageS y.1, cellQ ε y.1 y.2, etaCoord ε y.1)

/-- Reduction of `q` into the cell `(0, c]`: `q - c (⌈q/c⌉ - 1)`. -/
def reduceIoc (c q : ℝ) : ℝ := q - c * ((⌈q / c⌉ : ℝ) - 1)

/-- The chart followed by reduction of `q` into the cell `(0, c]`. -/
def cellChart (ε c : ℝ) (y : Space × ℝ) : Profile :=
  (ageS y.1, reduceIoc c (cellQ ε y.1 y.2), etaCoord ε y.1)

/-- The profile cell: `s > 0`, one `q`-cell `(0, c]`, `η ∈ ℝ`. -/
def cell (c : ℝ) : Set Profile := Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)

/-- One `τ` period `(0, 2εc]` and the full physical space. -/
def physDomain (ε c : ℝ) : Set (Space × ℝ) := univ ×ˢ Ioc 0 (2 * ε * c)

/-- Lebesgue measure `dx dτ` on one `τ` period. -/
def physMeasure (ε c : ℝ) : Measure (Space × ℝ) := volume.restrict (physDomain ε c)

/-- Unweighted Lebesgue measure `ds dq dη` on the cell. -/
def cellMeasure (c : ℝ) : Measure Profile := volume.restrict (cell c)

/-- The weight `s^{-3/2}` of `H` (tex line 3307). -/
def weightH (p : Profile) : ℝ≥0∞ := ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ)))

/-- The weight `s^{1/2}` of `H_g` (tex line 3308). -/
def weightHg (p : Profile) : ℝ≥0∞ := ENNReal.ofReal (p.1 ^ (1 / 2 : ℝ))

/-- `s^{-3/2} ds dq dη` on the cell. -/
def measureH (c : ℝ) : Measure Profile := (cellMeasure c).withDensity weightH

/-- `s^{1/2} ds dq dη` on the cell. -/
def measureHg (c : ℝ) : Measure Profile := (cellMeasure c).withDensity weightHg

/-- `c`-periodicity of a profile in `q`. -/
def QPeriodic {E : Type*} (c : ℝ) (b : Profile → E) : Prop :=
  ∀ p : Profile, b (p.1, p.2.1 + c, p.2.2) = b p

/-- The `c`-periodic extension of the cell values of a profile. -/
def periodize {E : Type*} (c : ℝ) (b : Profile → E) (p : Profile) : E :=
  b (p.1, reduceIoc c p.2.1, p.2.2)

/-! ### Measurability -/

theorem continuous_radius : Continuous radius := by
  unfold radius
  fun_prop

theorem measurable_radius : Measurable radius := continuous_radius.measurable

theorem measurable_liftA : Measurable liftA := measurable_radius.inv

theorem measurable_ageS : Measurable ageS := (measurable_radius.pow_const 2).inv

theorem measurable_height : Measurable fun x : Space => x 2 :=
  ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)

theorem measurable_etaCoord (ε : ℝ) : Measurable (etaCoord ε) :=
  measurable_height.div (measurable_radius.const_mul ε)

theorem measurable_reduceIoc (c : ℝ) : Measurable (reduceIoc c) := by
  unfold reduceIoc
  have h : Measurable fun q : ℝ => ((⌈q / c⌉ : ℤ) : ℝ) :=
    measurable_from_top.comp (Int.measurable_ceil.comp (measurable_id.div_const c))
  exact measurable_id.sub (h.sub_const 1 |>.const_mul c)

theorem measurable_cellQ (ε : ℝ) : Measurable fun y : Space × ℝ => cellQ ε y.1 y.2 := by
  unfold cellQ
  exact ((Real.measurable_log.comp (measurable_radius.comp measurable_fst)).const_mul _).add
    (measurable_snd.div_const _)

theorem measurable_chart (ε : ℝ) : Measurable (chart ε) :=
  (measurable_ageS.comp measurable_fst).prodMk
    ((measurable_cellQ ε).prodMk ((measurable_etaCoord ε).comp measurable_fst))

theorem measurable_cellChart (ε c : ℝ) : Measurable (cellChart ε c) :=
  (measurable_ageS.comp measurable_fst).prodMk
    (((measurable_reduceIoc c).comp (measurable_cellQ ε)).prodMk
      ((measurable_etaCoord ε).comp measurable_fst))

theorem measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)

theorem measurable_weightH : Measurable weightH :=
  ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)

theorem measurable_weightHg : Measurable weightHg :=
  ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)

/-! ### Cylindrical integration -/

/-- Plane polar coordinates for a radial nonnegative function (adapted from
`NonUniqueEuler/P/Infra/Polar/Radial.lean`, `lintegral_comp_norm`). -/
theorem lintegral_plane_radial (K : ℝ → ℝ≥0∞) (hK : Measurable K) :
    ∫⁻ p : ℝ × ℝ, K (√(p.1 ^ 2 + p.2 ^ 2)) =
      2 * ENNReal.ofReal π * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * K r := by
  rw [← lintegral_comp_polarCoord_symm]
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hmeas : MeasurableSet (polarCoord.target) := by
    rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun hmeas (g := fun p : ℝ × ℝ => ENNReal.ofReal p.1 * K p.1)
    (fun p hp => by
      rw [htarget] at hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      simp only [smul_eq_mul, polarCoord_symm_apply]
      congr 2
      rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq hp1.le])]
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal z.1 * K z.1)
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hK.comp measurable_fst)).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have h2 : ENNReal.ofReal (π - -π) = 2 * ENNReal.ofReal π := by
    rw [sub_neg_eq_add, ← two_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2, mul_comm]

/-- Cylindrical integration of an axisymmetric nonnegative function on `ℝ³`:
`∫ G(r, z) dx = 2π ∫_{r>0} ∫ r G(r, z) dz dr`. -/
theorem lintegral_space_axisymmetric (G : ℝ → ℝ → ℝ≥0∞)
    (hG : Measurable (Function.uncurry G)) :
    ∫⁻ x : Space, G (radius x) (x 2) =
      2 * ENNReal.ofReal π * ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z, ENNReal.ofReal r * G r z := by
  set g : (Fin 3 → ℝ) → ℝ≥0∞ := fun v => G (√(v 0 ^ 2 + v 1 ^ 2)) (v 2) with hg_def
  have hgm : Measurable fun v : Fin 3 → ℝ => (√(v 0 ^ 2 + v 1 ^ 2), v 2) :=
    (by fun_prop : Continuous fun v : Fin 3 → ℝ => (√(v 0 ^ 2 + v 1 ^ 2), v 2)).measurable
  have hg : Measurable g := hG.comp hgm
  have h1 : ∫⁻ x : Space, G (radius x) (x 2) = ∫⁻ v, g v :=
    (PiLp.volume_preserving_ofLp (Fin 3)).lintegral_comp hg
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have he : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))
  have h2 : ∫⁻ v, g v = ∫⁻ u : ℝ × (Fin 2 → ℝ), g (e.symm u) :=
    (he.lintegral_comp hg).symm
  have h3 : ∀ u : ℝ × (Fin 2 → ℝ), g (e.symm u) = G (√(u.2 0 ^ 2 + u.2 1 ^ 2)) u.1 := by
    rintro ⟨t, w⟩
    rfl
  have hm4 : Measurable fun u : ℝ × (Fin 2 → ℝ) => G (√(u.2 0 ^ 2 + u.2 1 ^ 2)) u.1 :=
    hG.comp ((by fun_prop : Continuous fun u : ℝ × (Fin 2 → ℝ) =>
      (√(u.2 0 ^ 2 + u.2 1 ^ 2), u.1)).measurable)
  have h4 : ∀ t : ℝ, ∫⁻ w : Fin 2 → ℝ, G (√(w 0 ^ 2 + w 1 ^ 2)) t =
      2 * ENNReal.ofReal π * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * G r t := by
    intro t
    have hK : Measurable fun r => G r t := hG.comp (measurable_id.prodMk measurable_const)
    rw [← lintegral_plane_radial (fun r => G r t) hK]
    exact (volume_preserving_finTwoArrow ℝ).lintegral_comp
      (f := fun p : ℝ × ℝ => G (√(p.1 ^ 2 + p.2 ^ 2)) t)
      (hK.comp ((by fun_prop : Continuous fun p : ℝ × ℝ => √(p.1 ^ 2 + p.2 ^ 2)).measurable))
  rw [h1, h2, lintegral_congr h3, Measure.volume_eq_prod,
    lintegral_prod _ hm4.aemeasurable, lintegral_congr h4, lintegral_const_mul' _ _
      (by simp [ENNReal.mul_eq_top]), lintegral_lintegral_swap]
  exact ((ENNReal.measurable_ofReal.comp measurable_snd).mul
    (hG.comp (measurable_snd.prodMk measurable_fst))).aemeasurable

/-- The axis `r = 0`. -/
def axis : Set Space := {x | radius x = 0}

theorem volume_axis : volume axis = 0 := by
  have hm : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
  have h := lintegral_space_axisymmetric (fun r _ => ({0} : Set ℝ).indicator 1 r)
    ((measurable_one.indicator hm).comp measurable_fst)
  have hrhs : ∫⁻ r in Ioi (0 : ℝ), ∫⁻ z : ℝ,
      ENNReal.ofReal r * ({0} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) r = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) (fun r hr => by
      have : r ∉ ({0} : Set ℝ) := by simpa using (ne_of_gt hr)
      simp [Set.indicator_of_notMem this])]
    simp
  rw [hrhs, mul_zero] at h
  have : ∫⁻ x : Space, ({0} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) (radius x) = volume axis := by
    show _ = volume (radius ⁻¹' {0})
    rw [← lintegral_indicator_one (measurable_radius hm)]
    refine lintegral_congr fun x => ?_
    simp only [Set.indicator, Set.mem_preimage]
    rfl
  rw [← this, h]

end UnforcedLeray.B0220
