import UnforcedLeray.Short.PartIIb.Sub.T22_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap.Lattice

/-!


`CylTrainBound` (Sub/T22_2.lean): for `Σ > 0`, `ν > 0`, `c > 0`, `δ ≥ 0` and a train with
`TrainClose tr Σ δ`, the velocity is bounded on `[0, Σ/ν] × ℝ²`.

Route: `TrainClose` at order `0` gives `|v - V_c| ≤ δ` componentwise (on the cell, `jb ≥ 1`; on the
plane by `c`-periodicity, `TrainClose.norm_sub_le`), and the periodized
heat vortex `V_c` is bounded for every `c > 0`: its components are lattice sums of `u_k(1 + νσ)`,
`1 ≤ 1 + νσ ≤ 1 + Σ`, dominated by a Gaussian in the first variable (`abs_u1_le`, `abs_u2_le`).
Unlike `TrainGap.lean` (which needs `c ≥ 1`), the lattice sum is bounded for every `c > 0` with a
Gaussian rate `β c²/4` (the constant may depend on `c`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Points `y = t - j c` with `|t| ≤ c/2` and `j ≠ 0` satisfy `(j c/2)² ≤ y²`. -/
theorem sq_lower_aux {c t y : ℝ} (hc : 0 < c) (ht : |t| ≤ c / 2) (j : ℤ) (hj : j ≠ 0)
    (hy : y = t - (j : ℝ) * c) : ((j : ℝ) * c / 2) ^ 2 ≤ y ^ 2 := by
  have ht' := abs_le.mp ht
  rcases lt_or_gt_of_ne hj with h | h
  · have hj1 : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    have hm : 0 ≤ (-(j : ℝ) - 1) * c := mul_nonneg (by linarith) hc.le
    have hA : 0 ≤ y + (j : ℝ) * c / 2 := by subst hy; nlinarith
    have hB : 0 ≤ y - (j : ℝ) * c / 2 := by subst hy; nlinarith
    nlinarith [mul_nonneg hA hB]
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hm : 0 ≤ ((j : ℝ) - 1) * c := mul_nonneg (by linarith) hc.le
    have hA : y + (j : ℝ) * c / 2 ≤ 0 := by subst hy; nlinarith
    have hB : y - (j : ℝ) * c / 2 ≤ 0 := by subst hy; nlinarith
    nlinarith [mul_nonneg (neg_nonneg.mpr hA) (neg_nonneg.mpr hB)]

/-- **Uniform lattice bound for every `c > 0`.** The Gaussian lattice sum is dominated by the
lattice sum of rate `β c²/4`, uniformly in the base point. -/
theorem lat_gen {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    ∑' n : ℤ, Real.exp (-(β * (x - n * c) ^ 2)) ≤
      ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)) := by
  obtain ⟨k, hk⟩ := TrainGap.exists_round hc x
  have hγ : 0 < β * c ^ 2 / 4 := by positivity
  have hsum_f : Summable (fun n : ℤ => Real.exp (-(β * (x - n * c) ^ 2))) :=
    UnforcedLeray.B0146.summable_exp_shift hβ hc.ne' x
  have hg : Summable (fun m : ℤ => Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2))) :=
    TrainGap.summable_gauss_int hγ
  have hg' : Summable (fun n : ℤ => Real.exp (-((β * c ^ 2 / 4) * ((n - k : ℤ) : ℝ) ^ 2))) :=
    (Equiv.subRight k).summable_iff.mpr hg
  have hpt : ∀ n : ℤ, Real.exp (-(β * (x - n * c) ^ 2)) ≤
      Real.exp (-((β * c ^ 2 / 4) * ((n - k : ℤ) : ℝ) ^ 2)) := by
    intro n
    apply Real.exp_le_exp.mpr
    by_cases hj : n - k = 0
    · have hj0 : ((n - k : ℤ) : ℝ) = 0 := by simp [hj]
      rw [hj0]
      nlinarith [sq_nonneg (x - n * c), hβ]
    · have key := sq_lower_aux hc hk (n - k) hj (y := x - n * c) (by push_cast; ring)
      have := mul_le_mul_of_nonneg_left key hβ.le
      nlinarith [this]
  calc ∑' n : ℤ, Real.exp (-(β * (x - n * c) ^ 2))
      ≤ ∑' n : ℤ, Real.exp (-((β * c ^ 2 / 4) * ((n - k : ℤ) : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum hpt hsum_f hg'
    _ = ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)) :=
        (Equiv.subRight k).tsum_eq (fun m : ℤ => Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)))

/-- The components of the periodized heat vortex as lattice sums of `u_k` (any `c > 0`). -/
theorem vc_fst_lat {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) (x : B0579.Plane) :
    UnforcedLeray.Train.Vc ν c s x 0 =
      ∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * s) (x.1 - n * c, x.2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs
  rw [UnforcedLeray.Train.Vc_eq, UnforcedLeray.B0146.periodicVelocity_eq hc0 ha,
    UnforcedLeray.Train.toVec_zero]
  rfl

theorem vc_snd_lat {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) (x : B0579.Plane) :
    UnforcedLeray.Train.Vc ν c s x 1 =
      ∑' n : ℤ, UnforcedLeray.B0146.u2 (1 + ν * s) (x.1 - n * c, x.2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs
  rw [UnforcedLeray.Train.Vc_eq, UnforcedLeray.B0146.periodicVelocity_eq hc0 ha,
    UnforcedLeray.Train.toVec_one]
  rfl

/-- **Uniform bound on the periodized heat vortex**, for every `c > 0` and every age
`σ ∈ [0, ∞)` with `1 + νσ ≤ K`. The constant depends on `K`, `c` only. -/
theorem vc_sup_aux {K ν c : ℝ} (hK : 0 < K) (hν : 0 < ν) (hc : 0 < c) :
    ∃ C : ℝ, ∀ σ : ℝ, 0 ≤ σ → 1 + ν * σ ≤ K → ∀ x : B0579.Plane,
      |UnforcedLeray.Train.Vc ν c σ x 0| ≤ C ∧ |UnforcedLeray.Train.Vc ν c σ x 1| ≤ C := by
  set β : ℝ := 1 / (8 * K) with hβdef
  have hβ : 0 < β := div_pos one_pos (by linarith)
  refine ⟨(2 * K + 1) * ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)), ?_⟩
  intro σ hσ hK' x
  have ha1 : 1 ≤ 1 + ν * σ := by nlinarith
  have hc0 : c ≠ 0 := hc.ne'
  have hL : 0 ≤ ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)) :=
    tsum_nonneg (fun m => (Real.exp_pos _).le)
  have hK2 : 0 ≤ 2 * K + 1 := by linarith
  constructor
  · rw [vc_fst_lat hν hc hσ x]
    have hg : Summable (fun n : ℤ => (2 * K + 1) * Real.exp (-(β * (x.1 - n * c) ^ 2))) :=
      (UnforcedLeray.B0146.summable_exp_shift hβ hc0 x.1).mul_left _
    calc |∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2)|
        ≤ ∑' n : ℤ, (2 * K + 1) * Real.exp (-(β * (x.1 - n * c) ^ 2)) :=
          TrainGap.abs_tsum_le' hg (fun n => TrainGap.abs_u1_le ha1 hK' (x.1 - n * c, x.2))
      _ = (2 * K + 1) * ∑' n : ℤ, Real.exp (-(β * (x.1 - n * c) ^ 2)) := tsum_mul_left
      _ ≤ (2 * K + 1) * ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (lat_gen hβ hc x.1) hK2
  · rw [vc_snd_lat hν hc hσ x]
    have hg : Summable (fun n : ℤ => (2 * K + 1) * Real.exp (-(β * (x.1 - n * c) ^ 2))) :=
      (UnforcedLeray.B0146.summable_exp_shift hβ hc0 x.1).mul_left _
    calc |∑' n : ℤ, UnforcedLeray.B0146.u2 (1 + ν * σ) (x.1 - n * c, x.2)|
        ≤ ∑' n : ℤ, (2 * K + 1) * Real.exp (-(β * (x.1 - n * c) ^ 2)) :=
          TrainGap.abs_tsum_le' hg (fun n => TrainGap.abs_u2_le ha1 hK' (x.1 - n * c, x.2))
      _ = (2 * K + 1) * ∑' n : ℤ, Real.exp (-(β * (x.1 - n * c) ^ 2)) := tsum_mul_left
      _ ≤ (2 * K + 1) * ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (lat_gen hβ hc x.1) hK2

/-- **`PartII-b:T22/2/5`: the train velocity is bounded** (needed N4). -/
theorem cylTrainBound : UnforcedLeray.Short.IIb.CylTrainBound := by
  unfold CylTrainBound
  intro Sg ν c δ hSg hν hc hδ tr htr
  obtain ⟨C, hC⟩ := vc_sup_aux (K := 1 + Sg) (ν := ν) (c := c) (by linarith) hν hc
  refine ⟨2 * (C + δ), ?_⟩
  intro s hs0 hsS x
  have hνs : ν * s ≤ Sg := by
    have h1 : ν * (Sg / ν) = Sg := by field_simp
    have h2 : ν * s ≤ ν * (Sg / ν) := mul_le_mul_of_nonneg_left hsS hν.le
    linarith
  have hK' : 1 + ν * s ≤ 1 + Sg := by linarith
  -- `TrainClose` holds on the cell; `c`-periodicity extends it to the plane
  -- (`TrainClose.norm_sub_le`, `Sub/TrainCloseCell.lean`)
  have hclose : ∀ y : B0579.Plane, ‖tr.v s y - UnforcedLeray.Train.Vc ν c s y‖ ≤ δ :=
    fun y => htr.norm_sub_le hc hs0 hsS y
  have hcomp : ∀ (y : B0579.Plane) (k : Fin 2),
      |tr.v s y k - UnforcedLeray.Train.Vc ν c s y k| ≤ δ := by
    intro y k
    have h1 := PiLp.norm_apply_le (tr.v s y - UnforcedLeray.Train.Vc ν c s y) k
    rw [PiLp.sub_apply, Real.norm_eq_abs] at h1
    exact h1.trans (hclose y)
  have A0 : |tr.v s x 0| ≤ C + δ := by
    have h := abs_sub_abs_le_abs_sub (tr.v s x 0) (UnforcedLeray.Train.Vc ν c s x 0)
    linarith [h, (hC s hs0 hK' x).1, hcomp x 0]
  have A1 : |tr.v s x 1| ≤ C + δ := by
    have h := abs_sub_abs_le_abs_sub (tr.v s x 1) (UnforcedLeray.Train.Vc ν c s x 1)
    linarith [h, (hC s hs0 hK' x).2, hcomp x 1]
  linarith [A0, A1]

end UnforcedLeray.Short.IIb
