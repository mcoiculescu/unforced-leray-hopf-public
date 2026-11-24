import UnforcedLeray.Lib.LerayLp.Leray
import Mathlib.MeasureTheory.Function.Holder

/-!
# Symmetry of the `L^p` Leray projection under the `L^p`–`L^{p'}` pairing (INF01 T14)

Blueprint: INF01 target T14 (`integral_inner_lerayLp_symm`) of

step of §4.8 behind "`𝔓 = id` on solenoidal fields" (T15). Manuscript: `P_σ` is an orthogonal
(self-adjoint) projection at `q = 2` (unit B0414, `paper/main.tex` lines 7340–7342) and the
operators at different exponents agree on intersections (unit B0430, lines 3720–3732).

For Hölder conjugate `1 < p, q < ∞`, `F ∈ L^p(R³;R³)` and `G ∈ L^q(R³;R³)`:
`∫ ⟨𝔓F, G⟩ = ∫ ⟨F, 𝔓G⟩`. Proof: on `L² ∩ L^p` and `L² ∩ L^q` both projections are the
self-adjoint `L²` projection (`lerayLp_ae_eq_projection`); both sides are continuous in `F`
and in `G` (Mathlib's Hölder pairing `ContinuousLinearMap.lpPairing`), and `L² ∩ L^r` is dense
in `L^r` for `r < ∞` (`dense_memLp_two_vec`).

* `innerPairing p q`: `(u, v) ↦ ∫ ⟨u, v⟩` as a continuous bilinear map `L^p × L^q → ℝ`;
* `dense_memLp_two_vec`: `L² ∩ L^p` is dense in `L^p(R³;R³)`;
* `integral_inner_lerayLp_of_memLp_two`: the identity for `G ∈ L² ∩ L^q`;
* `integral_inner_lerayLp_symm` (**T14**): the identity for all `F ∈ L^p`, `G ∈ L^q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

section Pairing

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- `(u, v) ↦ ∫ ⟨u(x), v(x)⟩ dx`, a continuous bilinear pairing `L^p × L^q → ℝ`. -/
def innerPairing :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space q (volume : Measure Space) →L[ℝ] ℝ :=
  (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing volume p q

variable {p q}

theorem innerPairing_apply (u : Lp Space p (volume : Measure Space))
    (v : Lp Space q (volume : Measure Space)) :
    innerPairing p q u v = ∫ x, inner ℝ (u x) (v x) := by
  rw [innerPairing, ContinuousLinearMap.lpPairing_eq_integral]
  rfl

end Pairing

/-- For Hölder conjugate exponents with `p < ∞`, `1 < q`. -/
theorem one_lt_of_holderConjugate {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) :
    1 < q :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 (lt_top_iff_ne_top.2 hp)

/-- For Hölder conjugate exponents with `1 < p`, `q < ∞`. -/
theorem ne_top_of_holderConjugate {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q] (hp1 : 1 < p) :
    q ≠ ⊤ :=
  (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp1.ne'

/-- `L² ∩ L^p` is dense in `L^p(R³;R³)` for `p < ∞`. -/
theorem dense_memLp_two_vec (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {u : Lp Space p (volume : Measure Space) | MemLp u 2 volume} := by
  refine Metric.dense_iff.2 fun u r hr => ?_
  obtain ⟨g, hgs, hgu, hgc, hgp⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
  refine ⟨hgp.toLp g, ?_, (hgc.memLp_of_hasCompactSupport hgs).ae_eq hgp.coeFn_toLp.symm⟩
  rw [Metric.mem_ball, dist_comm, Lp.dist_def]
  have h1 : (u : SpatialField) - ⇑(hgp.toLp g) =ᵐ[volume] (u : SpatialField) - g := by
    filter_upwards [hgp.coeFn_toLp] with x hx
    simp [hx]
  rw [eLpNorm_congr_ae h1]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgu
  rw [ENNReal.toReal_ofReal (half_pos hr).le] at h2
  linarith

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- **INF01 T14 (duality, first half).** For `F ∈ L^p` and `G ∈ L² ∩ L^q`,
`∫ ⟨𝔓F, G⟩ = ∫ ⟨F, 𝔓G⟩`. -/
theorem integral_inner_lerayLp_of_memLp_two (hp1 : 1 < p) (hp : p ≠ ⊤) (hq1 : 1 < q)
    (hq : q ≠ ⊤) (F : Lp Space p (volume : Measure Space))
    (G : Lp Space q (volume : Measure Space)) (hG : MemLp G 2 volume) :
    ∫ x, inner ℝ (lerayLp p hp1 hp F x) (G x) = ∫ x, inner ℝ (F x) (lerayLp q hq1 hq G x) := by
  rw [← innerPairing_apply, ← innerPairing_apply]
  have hc1 : Continuous fun F : Lp Space p (volume : Measure Space) =>
      innerPairing p q (lerayLp p hp1 hp F) G :=
    Continuous.clm_apply (f := fun F => innerPairing p q (lerayLp p hp1 hp F)) (g := fun _ => G)
      ((innerPairing p q).continuous.comp (lerayLp p hp1 hp).continuous) continuous_const
  have hc2 : Continuous fun F : Lp Space p (volume : Measure Space) =>
      innerPairing p q F (lerayLp q hq1 hq G) :=
    Continuous.clm_apply (f := fun F => innerPairing p q F) (g := fun _ => lerayLp q hq1 hq G)
      (innerPairing p q).continuous continuous_const
  have hsub : {u : Lp Space p (volume : Measure Space) | MemLp u 2 volume} ⊆
      {F | innerPairing p q (lerayLp p hp1 hp F) G = innerPairing p q F (lerayLp q hq1 hq G)} := by
    intro u (hu : MemLp u 2 volume)
    change innerPairing p q (lerayLp p hp1 hp u) G = innerPairing p q u (lerayLp q hq1 hq G)
    rw [innerPairing_apply, innerPairing_apply]
    have h1 := lerayLp_ae_eq_projection hp1 hp u hu
    have h2 := lerayLp_ae_eq_projection hq1 hq G hG
    calc ∫ x, inner ℝ (lerayLp p hp1 hp u x) (G x)
        = ∫ x, inner ℝ (Leray.projection (hu.toLp u) x) ((hG.toLp G) x) := by
          refine integral_congr_ae ?_
          filter_upwards [h1, hG.coeFn_toLp] with x h1 h2
          rw [h1, h2]
      _ = inner ℝ (Leray.projection (hu.toLp u)) (hG.toLp G) := (L2.inner_def _ _).symm
      _ = inner ℝ (hu.toLp u) (Leray.projection (hG.toLp G)) :=
          Leray.projection_selfadjoint _ _
      _ = ∫ x, inner ℝ ((hu.toLp u) x) (Leray.projection (hG.toLp G) x) := L2.inner_def _ _
      _ = ∫ x, inner ℝ (u x) (lerayLp q hq1 hq G x) := by
          refine integral_congr_ae ?_
          filter_upwards [h2, hu.coeFn_toLp] with x h1 h2
          rw [h1, h2]
  have h := (isClosed_eq hc1 hc2).closure_subset_iff.2 hsub
  rw [(dense_memLp_two_vec p hp).closure_eq] at h
  exact h (mem_univ F)

/-- **INF01 T14.** The `L^p` Leray projection is symmetric under the `L^p`–`L^q` pairing:
`∫ ⟨𝔓F, G⟩ = ∫ ⟨F, 𝔓G⟩` for `F ∈ L^p(R³;R³)`, `G ∈ L^q(R³;R³)`, `1/p + 1/q = 1`,
`1 < p, q < ∞`. -/
theorem integral_inner_lerayLp_symm (hp1 : 1 < p) (hp : p ≠ ⊤) (hq1 : 1 < q) (hq : q ≠ ⊤)
    (F : Lp Space p (volume : Measure Space)) (G : Lp Space q (volume : Measure Space)) :
    ∫ x, inner ℝ (lerayLp p hp1 hp F x) (G x) = ∫ x, inner ℝ (F x) (lerayLp q hq1 hq G x) := by
  rw [← innerPairing_apply, ← innerPairing_apply]
  have hc1 : Continuous fun G : Lp Space q (volume : Measure Space) =>
      innerPairing p q (lerayLp p hp1 hp F) G :=
    (innerPairing p q (lerayLp p hp1 hp F)).continuous
  have hc2 : Continuous fun G : Lp Space q (volume : Measure Space) =>
      innerPairing p q F (lerayLp q hq1 hq G) :=
    ((innerPairing p q F).comp (lerayLp q hq1 hq)).continuous
  have hsub : {u : Lp Space q (volume : Measure Space) | MemLp u 2 volume} ⊆
      {G | innerPairing p q (lerayLp p hp1 hp F) G = innerPairing p q F (lerayLp q hq1 hq G)} := by
    intro G (hG : MemLp G 2 volume)
    change innerPairing p q (lerayLp p hp1 hp F) G = innerPairing p q F (lerayLp q hq1 hq G)
    rw [innerPairing_apply, innerPairing_apply]
    exact integral_inner_lerayLp_of_memLp_two hp1 hp hq1 hq F G hG
  have h := (isClosed_eq hc1 hc2).closure_subset_iff.2 hsub
  rw [(dense_memLp_two_vec q hq).closure_eq] at h
  exact h (mem_univ G)

end UnforcedLeray.RieszLp
