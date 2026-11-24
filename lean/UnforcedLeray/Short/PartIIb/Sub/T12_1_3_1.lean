import UnforcedLeray.Short.PartIIb.Sub.T12_1_3
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Part II-b, task `PartII-b:T12/1/3/1` (`CylMollApprox`): decomposition into leaves

Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
The mollifications `E_n = ρ_n * D` with `ρ_n = mollBump n` (radii `1/(n+2)`, `2/(n+2)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `n`-th mollifier: a smooth normalized bump of inner radius `1/(n+2)` and outer radius
`2/(n+2)` on `ℝ × ℝ`. -/
def mollBump (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := 1 / ((n : ℝ) + 2)
  rOut := 2 / ((n : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [div_lt_div_iff_of_pos_right this]; norm_num

/-- The mollification `ρ * D` (convolution in `z`, componentwise in `CMerid`). -/
def cylMoll (ρ : ContDiffBump (0 : ℝ × ℝ)) (D : ℝ × ℝ → CMerid) : ℝ × ℝ → CMerid :=
  fun z => ∫ y, ρ.normed volume y • D (z - y)

/-- **Leaf `T12/1/3/1/a`** (SP 1923-1926): a `c`-periodic `L^r(avgμ c)` field is locally integrable
on the plane for `volume` (a bounded box meets finitely many cells; `lintegral_cell_periodize`,
`integral_eq_tsum_cell` in `Lib/CylinderB/Periodize.lean`; Hölder on each cell). -/
def CylLocInt : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → LocallyIntegrable D volume

/-- **Leaf `T12/1/3/1/b`**: `ρ * D` is `c`-periodic and each component is `C^∞`
(`HasCompactSupport.contDiff_convolution_right`, `D` locally integrable; periodicity by
translation invariance of the convolution). -/
def CylMollSmoothPeriodic : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → ∀ ρ : ContDiffBump (0 : ℝ × ℝ),
    (∀ z : ℝ × ℝ, cylMoll ρ D (z.1 + c, z.2) = cylMoll ρ D z) ∧
      ∀ i : Fin 2, ContDiff ℝ ∞ (fun z => cylMoll ρ D z i)

/-- **Leaf `T12/1/3/1/c`**: `ρ * D` is bounded (Hölder on the ball `closedBall 0 ρ.rOut`, which
meets at most `⌈2ρ.rOut / c⌉ + 1` cells; uniform in `z` by periodicity). -/
def CylMollBounded : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → ∀ ρ : ContDiffBump (0 : ℝ × ℝ),
    ∃ M : ℝ, ∀ z (i : Fin 2), ‖cylMoll ρ D z i‖ ≤ M

/-- **Leaf `T12/1/3/1/d`**: `ρ * D ∈ L^r(avgμ c)` (Minkowski/Young on the cell;
`Cyl.eLpNorm_planarConv_periodic_le` after replacing `D` by a strongly measurable a.e.-equal
periodic representative). -/
def CylMollMemLp : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → ∀ ρ : ContDiffBump (0 : ℝ × ℝ),
    MemLp (cylMoll ρ D) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `T12/1/3/1/e`**: the weak divergence-free identity passes to `ρ * D`
(`φ * ρ̌` is a `CylTest`; Fubini on the cell and `integral_cell_mul_comp_sub`). -/
def CylMollWeakDiv : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → CylWeakDiv c D →
    ∀ ρ : ContDiffBump (0 : ℝ × ℝ), CylWeakDiv c (cylMoll ρ D)

/-- **Leaf `T12/1/3/1/f`**: orthogonality to solenoidal tests passes to `ρ * D`
(`Ψ * ρ̌` is a `CylSolTest`). -/
def CylMollWeakSol : Prop :=
  ∀ c r : ℝ, 0 < c → 1 < r → ∀ D : ℝ × ℝ → CMerid, CylLp c r D → CylWeakSol c D →
    ∀ ρ : ContDiffBump (0 : ℝ × ℝ), CylWeakSol c (cylMoll ρ D)

theorem cylMollApprox_of (h1 : CylLocInt) (h2 : CylMollSmoothPeriodic) (h3 : CylMollBounded)
    (h4 : CylMollMemLp) (h5 : CylMollWeakDiv) (h6 : CylMollWeakSol) : CylMollApprox := by
  intro c r hc hr D hD hdiv hsol
  refine ⟨fun n => cylMoll (mollBump n) D, fun n => ?_, fun n => h5 c r hc hr D hD hdiv _,
    fun n => h6 c r hc hr D hD hsol _, ?_⟩
  · have hmem := h4 c r hc hr D hD (mollBump n)
    obtain ⟨hper, hsm⟩ := h2 c r hc hr D hD (mollBump n)
    refine ⟨⟨hper, hmem⟩, hsm, h3 c r hc hr D hD (mollBump n), fun i => ?_⟩
    have hm : MemLp (fun z => (cylMoll (mollBump n) D z) i) (ENNReal.ofReal r)
        (UnforcedLeray.Cyl.avgμ c) := by
      refine hmem.of_le_mul (c := 1) ?_ (Eventually.of_forall fun z => ?_)
      · exact (hsm i).continuous.aestronglyMeasurable
      · simpa using PiLp.norm_apply_le (cylMoll (mollBump n) D z) i
    exact hm
  · have hli := h1 c r hc hr D hD
    have hv : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        Tendsto (fun n => cylMoll (mollBump n) D z) atTop (𝓝 (D z)) := by
      have := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (φ := mollBump) (l := atTop) (K := 2) (μ := (volume : Measure (ℝ × ℝ)))
        (g := D) ?_ ?_ hli
      · filter_upwards [this] with z hz
        simpa [cylMoll, convolution_def] using hz
      · show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
        exact Tendsto.div_atTop tendsto_const_nhds
          (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      · refine Eventually.of_forall fun n => ?_
        show 2 / ((n : ℝ) + 2) ≤ 2 * (1 / ((n : ℝ) + 2))
        rw [mul_one_div]
    have hac : UnforcedLeray.Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)) := by
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _
    exact hac.ae_le hv

end UnforcedLeray.Short.IIb
