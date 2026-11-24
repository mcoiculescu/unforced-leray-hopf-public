import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP

/-!
# `PartIII-a:T21/c2/2/5/3`, leaf 1: integrability of the transport integrands (`FmrTransGenInt`)

Source: `the November 2 reference manuscript`, lines 2950-2954.  Weight-generic
copy of `PartII-b` `TransportIBP.integrable_Gf`, `integrable_Hf`: the weight `jb^m` is replaced by an
admissible weight `w` (`TransWt`), using `|w| + |∂₀w| + |∂₁w| ≤ K jb^m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem fmrTransGenInt : FmrTransGenInt := by
  intro ν c tr σ hσ hc hν hM m w hw g hg
  obtain ⟨M, hM⟩ := hM
  have hM0 : 0 ≤ M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hM 0)
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  obtain ⟨K0, hK0, hK0le⟩ : ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ x : B0579.Plane,
      |w x| + |B0579.pd 0 w x| + |B0579.pd 1 w x| ≤ K0 * B0579.jb x ^ m := by
    obtain ⟨K, hK⟩ := hw.bound
    refine ⟨max K 0, le_max_right _ _, fun x => (hK x).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (B0579.jb_pos x).le m)
  have hwK : ∀ x : B0579.Plane, |w x| ≤ K0 * B0579.jb x ^ m := fun x => by
    have := hK0le x
    linarith [abs_nonneg (B0579.pd 0 w x), abs_nonneg (B0579.pd 1 w x)]
  have hp0K : ∀ x : B0579.Plane, |B0579.pd 0 w x| ≤ K0 * B0579.jb x ^ m := fun x => by
    have := hK0le x
    linarith [abs_nonneg (w x), abs_nonneg (B0579.pd 1 w x)]
  have hp1K : ∀ x : B0579.Plane, |B0579.pd 1 w x| ≤ K0 * B0579.jb x ^ m := fun x => by
    have := hK0le x
    linarith [abs_nonneg (w x), abs_nonneg (B0579.pd 0 w x)]
  have hv : ContDiff ℝ 1 (tr.v σ) :=
    TransportIBP.contDiff_one_of_top (TransportIBP.contDiff_slice tr hσ)
  have hv0 : Continuous fun x : B0579.Plane => tr.v σ x 0 :=
    ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hv1 : Continuous fun x : B0579.Plane => tr.v σ x 1 :=
    ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
  have hg1 : ContDiff ℝ 1 g := hg.smooth.of_le (by norm_num)
  have hw1 : ContDiff ℝ 1 w := hw.smooth
  have hwc : Continuous w := hw1.continuous
  have hc1 : Continuous fun x : B0579.Plane =>
      g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) * w x :=
    (hg1.continuous.mul ((hv0.mul (TransportIBP.continuous_pd hg1 0)).add
      (hv1.mul (TransportIBP.continuous_pd hg1 1)))).mul hwc
  have hc2 : Continuous fun x : B0579.Plane =>
      g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 w x + tr.v σ x 1 * B0579.pd 1 w x) :=
    (hg1.continuous.pow 2).mul ((hv0.mul (TransportIBP.continuous_pd hw1 0)).add
      (hv1.mul (TransportIBP.continuous_pd hw1 1)))
  obtain ⟨C, hC0, hC⟩ := TransportIBP.g2rho_bound hg m
  have hQint : IntegrableOn (fun x : B0579.Plane => (2 * M * K0 * (C * C)) * B0579.jb x ^ (-4 : ℝ))
      (UnforcedLeray.Cyl.cell c) :=
    (TransportIBP.integrable_jb_neg4.const_mul _).integrableOn
  have bnd1 : ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      ‖g x * (tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x) * w x‖ ≤
        (2 * M * K0 * (C * C)) * B0579.jb x ^ (-4 : ℝ) := by
    intro x hx
    obtain ⟨a0, a1, -⟩ := hC x hx
    have hv0' : |tr.v σ x 0| ≤ M := by linarith [abs_nonneg (tr.v σ x 1), hM x]
    have hv1' : |tr.v σ x 1| ≤ M := by linarith [abs_nonneg (tr.v σ x 0), hM x]
    have hsum : |tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x|
        ≤ M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x| := by
      calc |tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x|
          ≤ |tr.v σ x 0 * B0579.pd 0 g x| + |tr.v σ x 1 * B0579.pd 1 g x| := abs_add_le _ _
        _ = |tr.v σ x 0| * |B0579.pd 0 g x| + |tr.v σ x 1| * |B0579.pd 1 g x| := by
            rw [abs_mul, abs_mul]
        _ ≤ M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x| :=
            add_le_add (mul_le_mul_of_nonneg_right hv0' (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hv1' (abs_nonneg _))
    have hB : 0 ≤ |g x| * (M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x|) :=
      mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg hM0 (abs_nonneg _))
        (mul_nonneg hM0 (abs_nonneg _)))
    have hJ : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le m
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |g x| * |tr.v σ x 0 * B0579.pd 0 g x + tr.v σ x 1 * B0579.pd 1 g x| * |w x|
        ≤ |g x| * (M * |B0579.pd 0 g x| + M * |B0579.pd 1 g x|) * (K0 * B0579.jb x ^ m) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)) (hwK x) (abs_nonneg _) hB
      _ = M * K0 * (|g x| * |B0579.pd 0 g x| * B0579.jb x ^ m)
          + M * K0 * (|g x| * |B0579.pd 1 g x| * B0579.jb x ^ m) := by ring
      _ ≤ M * K0 * (C * C * B0579.jb x ^ (-4 : ℝ)) + M * K0 * (C * C * B0579.jb x ^ (-4 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left a0 (mul_nonneg hM0 hK0))
            (mul_le_mul_of_nonneg_left a1 (mul_nonneg hM0 hK0))
      _ = (2 * M * K0 * (C * C)) * B0579.jb x ^ (-4 : ℝ) := by ring
  have bnd2 : ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      ‖g x ^ 2 * (tr.v σ x 0 * B0579.pd 0 w x + tr.v σ x 1 * B0579.pd 1 w x)‖ ≤
        (2 * M * K0 * (C * C)) * B0579.jb x ^ (-4 : ℝ) := by
    intro x hx
    obtain ⟨-, -, a2⟩ := hC x hx
    have hv0' : |tr.v σ x 0| ≤ M := by linarith [abs_nonneg (tr.v σ x 1), hM x]
    have hv1' : |tr.v σ x 1| ≤ M := by linarith [abs_nonneg (tr.v σ x 0), hM x]
    have hsum : |tr.v σ x 0 * B0579.pd 0 w x + tr.v σ x 1 * B0579.pd 1 w x|
        ≤ M * |B0579.pd 0 w x| + M * |B0579.pd 1 w x| := by
      calc |tr.v σ x 0 * B0579.pd 0 w x + tr.v σ x 1 * B0579.pd 1 w x|
          ≤ |tr.v σ x 0 * B0579.pd 0 w x| + |tr.v σ x 1 * B0579.pd 1 w x| := abs_add_le _ _
        _ = |tr.v σ x 0| * |B0579.pd 0 w x| + |tr.v σ x 1| * |B0579.pd 1 w x| := by
            rw [abs_mul, abs_mul]
        _ ≤ M * |B0579.pd 0 w x| + M * |B0579.pd 1 w x| :=
            add_le_add (mul_le_mul_of_nonneg_right hv0' (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hv1' (abs_nonneg _))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc g x ^ 2 * |tr.v σ x 0 * B0579.pd 0 w x + tr.v σ x 1 * B0579.pd 1 w x|
        ≤ g x ^ 2 * (M * |B0579.pd 0 w x| + M * |B0579.pd 1 w x|) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ ≤ g x ^ 2 * (M * (K0 * B0579.jb x ^ m) + M * (K0 * B0579.jb x ^ m)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hp0K x) hM0)
              (mul_le_mul_of_nonneg_left (hp1K x) hM0)) (sq_nonneg _)
      _ = (2 * M * K0) * (g x ^ 2 * B0579.jb x ^ m) := by ring
      _ ≤ (2 * M * K0) * (C * C * B0579.jb x ^ (-4 : ℝ)) :=
          mul_le_mul_of_nonneg_left a2 (mul_nonneg (mul_nonneg (by norm_num) hM0) hK0)
      _ = (2 * M * K0 * (C * C)) * B0579.jb x ^ (-4 : ℝ) := by ring
  rw [hcell]
  exact ⟨TransportIBP.integrableOn_cell_of_bound hQint hc1 bnd1,
    TransportIBP.integrableOn_cell_of_bound hQint hc2 bnd2⟩

end UnforcedLeray.Short.IIIa
