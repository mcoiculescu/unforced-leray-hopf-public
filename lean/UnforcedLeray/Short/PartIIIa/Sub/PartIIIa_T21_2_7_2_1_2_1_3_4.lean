import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3

/-!
# `PartIII-a:T21/2/7/2/1/2/1/3/4`: `SupBddByXNorm` from a local Sobolev bound and a box comparison

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3061 (the
weighted `H^j_{-m}` energies control sup norms of the smooth version on bounded sets).

The bound splits into
* `LocalSobolevBox`: an unweighted local Sobolev inequality on a box
  (`‖G x‖ ≤ C Σ_{|w| ≤ 2} ‖∂^w G‖_{L²(box)}`, cutoff, `G = ∫∫ ∂₁∂₂(ζ G)` over a quadrant,
  Cauchy-Schwarz);
* `BoxXNorm`: the unweighted `L²` norm of a `c`-periodic function on a box is bounded by the
  `X_{-m,c}` norm (finitely many period translates of the cell meet the box, and the density
  `jb^{-m}` is bounded below on bounded sets).
`PdCxPeriodic` supplies periodicity of all `∂^w g`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf (local Sobolev on a box)**: for every `M` there is `C ≥ 0` such that every smooth `G`
satisfies `|G x| ≤ C Σ_{|w| ≤ 2} ‖∂^w G‖_{L²(closedBall 0 (M+1))}` for `‖x‖ ≤ M` (sup norm, so the
ball is a square).  Proof: cutoff `ζ ∈ C_c^∞`, `ζ = 1` on `closedBall 0 M`, supported in
`closedBall 0 (M+1)`; `(ζ G)(x) = ∫∫_{quadrant} ∂₁∂₂(ζ G)` by the fundamental theorem of calculus
twice; Leibniz gives `∂₁∂₂(ζ G) = Σ (∂^{w'} ζ)(∂^{w} G)` with `|w|, |w'| ≤ 2`; Cauchy-Schwarz on
the (finite measure) box. -/
def LocalSobolevBox : Prop :=
  ∀ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ ∞ G → ∀ x : ℝ × ℝ, ‖x‖ ≤ M →
    ENNReal.ofReal ‖G x‖ ≤ ENNReal.ofReal C *
      (wordsLe2.map fun w =>
        eLpNorm (adjSpatial w G) 2 (volume.restrict (Metric.closedBall (0 : ℝ × ℝ) (M + 1)))).sum

/-- **Leaf (periodic functions: box norm against the weighted cell norm)**: the plane `L²` norm of
a `c`-periodic function on a box is at most `K ‖f‖_{X_{-m,c}}`. -/
def BoxXNorm : Prop :=
  ∀ c m M : ℝ, 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ × ℝ → ℂ,
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) →
      eLpNorm f 2 (volume.restrict (Metric.closedBall (0 : ℝ × ℝ) M)) ≤
        ENNReal.ofReal K * xNorm c (-m) f

theorem supBddByXNorm_of (hL : LocalSobolevBox) (hB : BoxXNorm) (hP : PdCxPeriodic) :
    SupBddByXNorm := by
  intro c m R hc
  obtain ⟨C, hC0, hC⟩ := hL R
  obtain ⟨K, hK0, hK⟩ := hB c m (R + 1) hc
  refine ⟨C * K, mul_nonneg hC0 hK0, fun g hg hper x hx => ?_⟩
  have hpw : ∀ w : List (Fin 2), ∀ y : ℝ × ℝ,
      adjSpatial w g (y.1 + c, y.2) = adjSpatial w g y := by
    intro w
    induction w with
    | nil => exact hper
    | cons k w ih => exact hP c k _ (contDiff_adjSpatial hg w) ih
  have h1 := hC g hg x hx
  have h2 : (wordsLe2.map fun w =>
        eLpNorm (adjSpatial w g) 2 (volume.restrict (Metric.closedBall (0 : ℝ × ℝ) (R + 1)))).sum ≤
      (wordsLe2.map fun w => ENNReal.ofReal K * xNorm c (-m) (adjSpatial w g)).sum :=
    List.sum_le_sum fun w _ => hK _ (hpw w)
  have h3 : (wordsLe2.map fun w => ENNReal.ofReal K * xNorm c (-m) (adjSpatial w g)).sum =
      ENNReal.ofReal K * (wordsLe2.map fun w => xNorm c (-m) (adjSpatial w g)).sum := by
    simp only [wordsLe2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  calc ENNReal.ofReal ‖g x‖ ≤ _ := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal K *
          (wordsLe2.map fun w => xNorm c (-m) (adjSpatial w g)).sum) := by
        rw [← h3]; gcongr
    _ = _ := by rw [← mul_assoc, ENNReal.ofReal_mul hC0]

end UnforcedLeray.Short.IIIa
