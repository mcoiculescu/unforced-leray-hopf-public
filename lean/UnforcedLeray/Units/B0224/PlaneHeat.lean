import UnforcedLeray.Units.B0220
import UnforcedLeray.Lib.HeatR3.ConvOp
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# B0224 helper: the heat semigroup of the cylinder on one period strip

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379, and its
infrastructure item "heat semigroup on the periodic strip `(ℝ/cℤ) × ℝ`" (INF05 T15).


is a `c`-periodic function of `(q, η) ∈ ℝ × ℝ`, and the cylinder heat `e^{θΔ_{q,η}}` is the
planar heat (INF04 T3, `Heat.heatConv`, decision D17) applied to the periodic function:

  `e^{θΔ}u(x) = ∫_{ℝ²} G_θ(y) u(x - y) dy`,  `G_θ(y) = (4πθ)^{-1} e^{-|y|²/(4θ)}`  (`θ > 0`).

At `θ ≤ 0` we set `e^{θΔ} = id` (`planeHeat`), the convention of `Heat.heatLp`; the semigroup
`T_0(t)` of B0224 uses heat time `νs(1 - e^{-t})`, which is `0` at `t = 0`.

The norms are taken over the period strip `(0, c] × ℝ` of the manuscript (`strip`; B0220 uses
the cell `q ∈ (0, c]`, tex line 3305).

Main results:
* `lintegral_strip_comp_sub`, `integral_strip_comp_add`: translation invariance of strip
  integrals of periodic functions;
* `enorm_integral_gauss_sq_le`: Jensen's inequality `|∫G_θ g|² ≤ ∫G_θ|g|²`;
* `lintegral_strip_gauss`: `∫_strip ∫ G_θ(y) φ(x - y) dy dx = ∫_strip φ` for periodic `φ ≥ 0`
  (the heat preserves the strip mass);
* `integral_strip_inner_planeHeat`: the heat is symmetric on `L²(strip)` for periodic fields.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-! ### The embedding `ℝ² → (q, η)` and the period strip -/

/-- The translations `y ↦ (y₀, y₁)` of the `(q, η)` plane. -/
def planeι : Euc 2 →+ ℝ × ℝ where
  toFun y := (y 0, y 1)
  map_zero' := by simp
  map_add' x y := by simp

theorem planeι_apply (y : Euc 2) : planeι y = (y 0, y 1) := rfl

theorem continuous_planeι : Continuous planeι := by
  change Continuous fun y : Euc 2 => (y 0, y 1)
  exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).prodMk
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)

theorem measurable_planeι : Measurable planeι := continuous_planeι.measurable

/-- One period strip `(0, c] × ℝ` of the `(q, η)` plane (the `(q, η)` part of `B0220.cell`). -/
def strip (c : ℝ) : Set (ℝ × ℝ) := Ioc 0 c ×ˢ (univ : Set ℝ)

theorem measurableSet_strip (c : ℝ) : MeasurableSet (strip c) :=
  measurableSet_Ioc.prod MeasurableSet.univ

theorem restrict_strip (c : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (strip c) =
      volume.restrict (Ico 0 (0 + c) ×ˢ (univ : Set ℝ)) := by
  rw [strip, Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict, zero_add,
    Measure.restrict_congr_set (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm]

section Periodic

variable {c : ℝ}

theorem isPeriodic_comp_sub {F : Type*} {u : ℝ × ℝ → F} (hu : Cyl.IsPeriodic c u)
    (v : ℝ × ℝ) : Cyl.IsPeriodic c (fun z => u (z - v)) := by
  intro z
  have : (z.1 + c, z.2) - v = ((z - v).1 + c, (z - v).2) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub]; ring
  simp only [this]
  exact hu _

theorem lintegral_strip_eq_cell (hc : 0 < c) {φ : ℝ × ℝ → ℝ≥0∞} (hφ : Cyl.IsPeriodic c φ) :
    ∫⁻ z in strip c, φ z = ∫⁻ z in Cyl.cell c, φ z := by
  rw [restrict_strip]
  exact Cyl.lintegral_strip_eq_cell hc hφ 0

theorem integral_strip_eq_cell {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hc : 0 < c) {φ : ℝ × ℝ → F} (hφ : Cyl.IsPeriodic c φ) :
    ∫ z in strip c, φ z = ∫ z in Cyl.cell c, φ z := by
  rw [restrict_strip]
  exact Cyl.integral_strip_eq_cell hc hφ 0

/-- Translation invariance of strip integrals of periodic functions. -/
theorem lintegral_strip_comp_sub (hc : 0 < c) {φ : ℝ × ℝ → ℝ≥0∞} (hφ : Cyl.IsPeriodic c φ)
    (v : ℝ × ℝ) : ∫⁻ z in strip c, φ (z - v) = ∫⁻ z in strip c, φ z := by
  rw [lintegral_strip_eq_cell hc (isPeriodic_comp_sub hφ v), lintegral_strip_eq_cell hc hφ]
  simpa [sub_eq_add_neg] using Cyl.lintegral_cell_comp_add hc hφ (-v)

/-- Translation invariance of strip integrals of periodic functions, Bochner version. -/
theorem integral_strip_comp_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hc : 0 < c) {φ : ℝ × ℝ → F} (hφ : Cyl.IsPeriodic c φ) (v : ℝ × ℝ) :
    ∫ z in strip c, φ (z + v) = ∫ z in strip c, φ z := by
  have hφv : Cyl.IsPeriodic c (fun z => φ (z + v)) := by
    simpa [sub_eq_add_neg] using isPeriodic_comp_sub hφ (-v)
  rw [integral_strip_eq_cell hc hφv, integral_strip_eq_cell hc hφ]
  exact Cyl.integral_cell_comp_add hc hφ v

end Periodic

/-! ### The Gaussian as a probability density -/

theorem lintegral_ofReal_gauss {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) = 1 := by
  simpa only [Heat.enorm_gaussKernel hθ] using Heat.lintegral_enorm_gaussKernel (d := 2) hθ

theorem measurable_ofReal_gauss (θ : ℝ) :
    Measurable fun y : Euc 2 => ENNReal.ofReal (gaussKernel 2 θ y) :=
  ENNReal.measurable_ofReal.comp (Gaussian.continuous_gaussKernel θ).measurable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Jensen's inequality** for the Gaussian average: `|∫ G_θ g|² ≤ ∫ G_θ |g|²`. -/
theorem enorm_integral_gauss_sq_le {θ : ℝ} (hθ : 0 < θ) {g : Euc 2 → E}
    (hg : AEStronglyMeasurable g) :
    ‖∫ y, gaussKernel 2 θ y • g y‖ₑ ^ 2 ≤
      ∫⁻ y, ENNReal.ofReal (gaussKernel 2 θ y) * ‖g y‖ₑ ^ 2 := by
  set G : Euc 2 → ℝ := gaussKernel 2 θ with hG
  have hG0 : ∀ y, 0 ≤ G y := fun y => Gaussian.gaussKernel_nonneg hθ y
  have h1 : ‖∫ y, G y • g y‖ₑ ≤ ∫⁻ y, ENNReal.ofReal (G y) * ‖g y‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (hG0 y)]
  set a : Euc 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (√(G y)) * ‖g y‖ₑ with ha
  set b : Euc 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (√(G y)) with hb
  have hbm : Measurable b :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_sqrt.comp (Gaussian.continuous_gaussKernel θ)).measurable
  have ham : AEMeasurable a := hbm.aemeasurable.mul hg.enorm
  have hsq : ∀ y, ENNReal.ofReal (√(G y)) * ENNReal.ofReal (√(G y)) = ENNReal.ofReal (G y) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hG0 y)]
  have hab : ∀ y, (a * b) y = ENNReal.ofReal (G y) * ‖g y‖ₑ := by
    intro y
    simp only [Pi.mul_apply, ha, hb]
    rw [mul_comm (ENNReal.ofReal _) ‖g y‖ₑ, mul_assoc, hsq, mul_comm]
  have ha2 : ∀ y, a y ^ (2 : ℝ) = ENNReal.ofReal (G y) * ‖g y‖ₑ ^ 2 := by
    intro y
    simp only [ha, ENNReal.rpow_two, sq]
    rw [mul_mul_mul_comm, hsq]
  have hb2 : ∀ y, b y ^ (2 : ℝ) = ENNReal.ofReal (G y) := by
    intro y
    simp only [hb, ENNReal.rpow_two, sq, hsq]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Euc 2))
    Real.HolderConjugate.two_two ham hbm.aemeasurable
  simp only [hab, ha2, hb2] at hH
  rw [hG, lintegral_ofReal_gauss hθ, ENNReal.one_rpow, mul_one] at hH
  calc ‖∫ y, G y • g y‖ₑ ^ 2 ≤ (∫⁻ y, ENNReal.ofReal (G y) * ‖g y‖ₑ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ y, ENNReal.ofReal (G y) * ‖g y‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ∫⁻ y, ENNReal.ofReal (G y) * ‖g y‖ₑ ^ 2 := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num

/-! ### The heat on the plane -/

/-- The cylinder heat `e^{θΔ_{q,η}}` acting on a (periodic) function `u` of `(q, η)`:
the planar Gaussian average `Heat.heatConv planeι θ u` for `θ > 0` (tex line 3373), and the
identity for `θ ≤ 0`. -/
def planeHeat (θ : ℝ) (u : ℝ × ℝ → E) : ℝ × ℝ → E :=
  if 0 < θ then Heat.heatConv planeι θ u else u

theorem planeHeat_of_pos {θ : ℝ} (hθ : 0 < θ) (u : ℝ × ℝ → E) (x : ℝ × ℝ) :
    planeHeat θ u x = ∫ y : Euc 2, gaussKernel 2 θ y • u (x - planeι y) := by
  simp only [planeHeat, hθ, ↓reduceIte, Heat.heatConv]

theorem planeHeat_of_nonpos {θ : ℝ} (hθ : θ ≤ 0) (u : ℝ × ℝ → E) : planeHeat θ u = u := by
  simp only [planeHeat, not_lt.2 hθ, ↓reduceIte]

theorem planeHeat_smul (θ r : ℝ) (u : ℝ × ℝ → E) :
    planeHeat θ (fun x => r • u x) = fun x => r • planeHeat θ u x := by
  funext x
  by_cases hθ : 0 < θ
  · simp only [planeHeat_of_pos hθ, smul_comm _ r, integral_smul]
  · simp only [planeHeat_of_nonpos (not_lt.1 hθ)]

/-- The heat preserves the strip mass of periodic nonnegative functions:
`∫_strip ∫ G_θ(y) φ(x - y) dy dx = ∫_strip φ`. -/
theorem lintegral_strip_gauss {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {φ : ℝ × ℝ → ℝ≥0∞}
    (hφm : Measurable φ) (hφ : Cyl.IsPeriodic c φ) :
    ∫⁻ x in strip c, ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - planeι y) =
      ∫⁻ x in strip c, φ x := by
  have hm : Measurable fun q : (ℝ × ℝ) × Euc 2 =>
      ENNReal.ofReal (gaussKernel 2 θ q.2) * φ (q.1 - planeι q.2) :=
    ((measurable_ofReal_gauss θ).comp measurable_snd).mul
      (hφm.comp (measurable_fst.sub (measurable_planeι.comp measurable_snd)))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ y : Euc 2, ∫⁻ x in strip c, ENNReal.ofReal (gaussKernel 2 θ y) * φ (x - planeι y)
      = ∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y) * ∫⁻ x in strip c, φ x := by
        refine lintegral_congr fun y => ?_
        have hmy : Measurable fun x : ℝ × ℝ => φ (x - planeι y) :=
          hφm.comp (measurable_id.sub_const _)
        rw [lintegral_const_mul _ hmy, lintegral_strip_comp_sub hc hφ]
    _ = (∫⁻ y : Euc 2, ENNReal.ofReal (gaussKernel 2 θ y)) * ∫⁻ x in strip c, φ x :=
        lintegral_mul_const _ (measurable_ofReal_gauss θ)
    _ = ∫⁻ x in strip c, φ x := by rw [lintegral_ofReal_gauss hθ, one_mul]

/-- `x ≤ 1 + x²` in `[0, ∞]`. -/
theorem le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

/-- If `∫ G_θ |g|² < ∞`, the Gaussian average of `g` converges absolutely. -/
theorem integrable_gauss_smul {θ : ℝ} (hθ : 0 < θ) {g : Euc 2 → E}
    (hg : AEStronglyMeasurable g)
    (hfin : ∫⁻ y, ENNReal.ofReal (gaussKernel 2 θ y) * ‖g y‖ₑ ^ 2 < ∞) :
    Integrable fun y => gaussKernel 2 θ y • g y := by
  refine ⟨((Gaussian.continuous_gaussKernel θ).aestronglyMeasurable).smul hg, ?_⟩
  have hle : ∫⁻ y, ‖gaussKernel 2 θ y • g y‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (gaussKernel 2 θ y) * (1 + ‖g y‖ₑ ^ 2) := by
    refine lintegral_mono fun y => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (Gaussian.gaussKernel_nonneg hθ y)]
    gcongr
    exact le_one_add_sq _
  refine lt_of_le_of_lt hle ?_
  simp_rw [mul_add, mul_one]
  rw [lintegral_add_left (measurable_ofReal_gauss θ), lintegral_ofReal_gauss hθ]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hfin⟩

end UnforcedLeray.B0224
