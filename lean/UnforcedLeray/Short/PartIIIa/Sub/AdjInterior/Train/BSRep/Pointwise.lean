import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Proved
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Cutoff
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwise

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: the pointwise kernel identities for decaying fields

Source: `the November 2 reference manuscript` (SP) lines 2081-2084, 3121
(`K_d = ∇^⊥G_d`, `ΔG_d = Σ_n δ_{(nd, 0)}`). Statement `BsrKerPointwiseDecay` in `BSRep/Defs.lean`.

`bsrKerPointwiseDecay_of : BsrWeightInt → BsrKerPointwiseDecay`: the proved test identities
`kerDivPointwise_of kerNearFar`, `kerCurlPointwise_of kerNearFar` for the cutoff tests of
`bsrCutoffApprox`, and dominated convergence (dominator from `bsrWeightIntShift_of`).

`tjTrainBSRep_of_two`: `TjTrainBSRep m` from the train leaves and `BsrWeightInt`, `BsrKcHasFDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

theorem bsrKerPointwiseDecay_of (hWI : BsrWeightInt) : BsrKerPointwiseDecay := by
  intro d β A hd hβ φ hφ hper hA hA' y
  obtain ⟨ψ, K, hK0, hψ, hev, hbd⟩ := bsrCutoffApprox d φ hφ hper
  have hW := bsrWeightIntShift_of hWI d β hd hβ y
  rw [← cell_eq_Cyl'] at hW
  have hdiv := kerDivPointwise_of kerNearFar d hd
  have hcurl := kerCurlPointwise_of kerNearFar d hd
  -- the weighted bounds as upper bounds
  have hwpos : ∀ x : ℝ × ℝ, 0 < (1 + x.2 ^ 2) ^ (β / 2) := fun x =>
    Real.rpow_pos_of_pos (by positivity) _
  have hwb : ∀ x : ℝ × ℝ, |φ x| ≤ A * (1 + x.2 ^ 2) ^ (-(β / 2)) := by
    intro x
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (hwpos x), mul_comm]
    exact hA x
  have hwb' : ∀ x : ℝ × ℝ, ‖fderiv ℝ φ x‖ ≤ A * (1 + x.2 ^ 2) ^ (-(β / 2)) := by
    intro x
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (hwpos x), mul_comm]
    exact hA' x
  have hpdb : ∀ (n : ℕ) (j : Fin 2) (x : ℝ × ℝ),
      |B0579.pd j (ψ n) x| ≤ (1 + K) * A * (1 + x.2 ^ 2) ^ (-(β / 2)) := by
    intro n j x
    calc |B0579.pd j (ψ n) x| ≤ ‖fderiv ℝ φ x‖ + K * |φ x| := hbd n j x
      _ ≤ A * (1 + x.2 ^ 2) ^ (-(β / 2)) + K * (A * (1 + x.2 ^ 2) ^ (-(β / 2))) :=
          add_le_add (hwb' x) (mul_le_mul_of_nonneg_left (hwb x) hK0)
      _ = (1 + K) * A * (1 + x.2 ^ 2) ^ (-(β / 2)) := by ring
  have hkb : ∀ (x : ℝ × ℝ) (j : Fin 2),
      |kerD d (x - y) j| ≤ ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖ := by
    intro x j
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le _ j
  have hkm : ∀ j : Fin 2, Measurable (fun x : ℝ × ℝ => kerD d (x - y) j) := fun j =>
    ((PiLp.continuous_apply 2 _ j).measurable).comp
      ((UnforcedLeray.Cyl.measurable_bsKernel d).comp (measurable_id.sub measurable_const))
  have hpdc : ∀ (n : ℕ) (j : Fin 2), Continuous (B0579.pd j (ψ n)) := fun n j =>
    ((hψ n).pd j).continuous
  -- the dominator
  have hbint : Integrable (fun x : ℝ × ℝ => 2 * ((1 + K) * A) *
      ((1 + x.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖))
      (volume.restrict (B0579.cell d)) := hW.const_mul _
  have hdom : ∀ (n : ℕ) (x : ℝ × ℝ) (a b : Fin 2), ‖kerD d (x - y) a * B0579.pd b (ψ n) x‖ ≤
      (1 + K) * A * ((1 + x.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖) := by
    intro n x a b
    rw [Real.norm_eq_abs, abs_mul]
    calc |kerD d (x - y) a| * |B0579.pd b (ψ n) x|
        ≤ ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖ * ((1 + K) * A * (1 + x.2 ^ 2) ^ (-(β / 2))) :=
          mul_le_mul (hkb x a) (hpdb n b x) (abs_nonneg _) (norm_nonneg _)
      _ = (1 + K) * A * ((1 + x.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖) := by
          ring
  -- dominated convergence for both integrands
  have hlim : ∀ (a b a' b' : Fin 2) (s : ℝ),
      Tendsto (fun n : ℕ => ∫ x in B0579.cell d,
          (kerD d (x - y) a * B0579.pd b (ψ n) x + s * (kerD d (x - y) a' * B0579.pd b' (ψ n) x)))
        atTop (𝓝 (∫ x in B0579.cell d,
          (kerD d (x - y) a * B0579.pd b φ x + s * (kerD d (x - y) a' * B0579.pd b' φ x)))) := by
    intro a b a' b' s
    refine tendsto_integral_of_dominated_convergence
      (fun x : ℝ × ℝ => (1 + |s|) * (2 * ((1 + K) * A) *
        ((1 + x.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖)))
      (fun n => ?_) (hbint.const_mul _) (fun n => ?_) ?_
    · exact (((hkm a).mul (hpdc n b).measurable).add
        (measurable_const.mul ((hkm a').mul (hpdc n b').measurable))).aestronglyMeasurable
    · refine Eventually.of_forall (fun x => ?_)
      have h1 := hdom n x a b
      have h2 := hdom n x a' b'
      have hB : 0 ≤ (1 + K) * A * ((1 + x.2 ^ 2) ^ (-(β / 2)) *
          ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖) := (norm_nonneg _).trans h1
      calc ‖kerD d (x - y) a * B0579.pd b (ψ n) x +
            s * (kerD d (x - y) a' * B0579.pd b' (ψ n) x)‖
          ≤ ‖kerD d (x - y) a * B0579.pd b (ψ n) x‖ +
            |s| * ‖kerD d (x - y) a' * B0579.pd b' (ψ n) x‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            rw [norm_mul s, Real.norm_eq_abs s]
        _ ≤ (1 + K) * A * ((1 + x.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖) +
            |s| * ((1 + K) * A * ((1 + x.2 ^ 2) ^ (-(β / 2)) *
              ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖)) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
        _ ≤ (1 + |s|) * (2 * ((1 + K) * A) *
            ((1 + x.2 ^ 2) ^ (-(β / 2)) * ‖UnforcedLeray.Cyl.bsKernel d (x - y)‖)) := by
            nlinarith [abs_nonneg s]
    · refine Eventually.of_forall (fun x => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      rw [hn.2 b, hn.2 b']
  refine ⟨?_, ?_⟩
  · have h := hlim 0 0 1 1 1
    simp only [one_mul] at h
    have h0 : ∀ n : ℕ, (∫ x in B0579.cell d,
        (kerD d (x - y) 0 * B0579.pd 0 (ψ n) x + kerD d (x - y) 1 * B0579.pd 1 (ψ n) x)) = 0 :=
      fun n => hdiv (ψ n) (hψ n) y
    simp only [h0] at h
    exact tendsto_nhds_unique tendsto_const_nhds h |>.symm
  · have h := hlim 0 1 1 0 (-1)
    simp only [neg_one_mul, ← sub_eq_add_neg] at h
    have h0 : ∀ n : ℕ, (∫ x in B0579.cell d,
        (kerD d (x - y) 0 * B0579.pd 1 (ψ n) x - kerD d (x - y) 1 * B0579.pd 0 (ψ n) x)) =
          ψ n y := fun n => hcurl (ψ n) (hψ n) y
    simp only [h0] at h
    have hy : Tendsto (fun n : ℕ => ψ n y) atTop (𝓝 (φ y)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev y] with n hn
      exact hn.1.symm
    exact tendsto_nhds_unique h hy

/-- **`TjTrainBSRep m` from the train leaves and the two kernel leaves** `BsrWeightInt`,
`BsrKcHasFDeriv`. -/
theorem tjTrainBSRep_of_two (m : ℝ) (hm : 8 < m) (hV : TjTrainVort) (hDec : TjVortDecay m)
    (hG : TjLadGrad m) (hKb : TjKcBound) (hWI : BsrWeightInt) (hD : BsrKcHasFDeriv) :
    TjTrainBSRep m :=
  tjTrainBSRep_of_rest m hm hV hDec hG hKb hWI hD (bsrKerPointwiseDecay_of hWI)

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.bsrKerPointwiseDecay_of
#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep_of_two
