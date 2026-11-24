import UnforcedLeray.Short.PartIIb.Sub.T22
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap.Lattice

/-!
# Part II-b, task `PartII-b:T22` leaf 6: the train gap on the cell (`CylTrainGap`)

Source of record: `the November 2 reference manuscript`, lines 2085-2093 (the
train comparison: "image velocities, the seam region ... contribute at most `C(δ_c + e^{-b c²})`")
and line 2108.

The statement `CylTrainGap` (`Sub/T22.lean`) is proved for `Σ > 0` with `C = 2 + 2 C₀ E L`,
`b = 1/(32(1 + Σ))`, where `C₀ = 2K + 1`, `K = 1 + Σ`, `E = e^{b}`, `L = ∑_m e^{-b m²}`.

Route:
* `TrainClose` at order `0` gives `‖v - V_c‖ ≤ δ` on the cell, hence on the plane by `c`-periodicity
  (`TrainClose.norm_sub_le`, `Sub/TrainCloseCell.lean`), and each component is within `δ`.
* `V_c(x)_k = ∑_n u_k(x - n c e₁)` (the periodized isolated vortex, `Train.Vc_eq`,
  `B0146.periodicVelocity_eq`), and `u_k(a, ·)` is the `k`-th component of `isoVelocity`.
* The `n = 0` term of that sum is the central vortex `isoVelocity ν σ x`; the remaining terms are
  bounded by `TrainGap.tail_exp_le` on the cell (`|x_1| ≤ c/2`, `|n c| ≥ |n| c/2`).
* The uniform sup bound on `V_c` (used for the `δ + 1` part) is `TrainGap.lattice_uniform`.

Helpers: `TrainGap/Gauss.lean`, `TrainGap/Iso.lean`, `TrainGap/Lattice.lean` in the folder
`Tasks/CylEnergy/TrainGap/`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The first component of the periodized heat vortex is the lattice sum of `u1`. -/
theorem trainGap_vc_fst {ν c s : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (hs : 0 ≤ s)
    (x : B0579.Plane) :
    UnforcedLeray.Train.Vc ν c s x 0 =
      ∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * s) (x.1 - n * c, x.2) := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs
  rw [UnforcedLeray.Train.Vc_eq, UnforcedLeray.B0146.periodicVelocity_eq hc0 ha,
    UnforcedLeray.Train.toVec_zero]
  rfl

/-- The second component of the periodized heat vortex is the lattice sum of `u2`. -/
theorem trainGap_vc_snd {ν c s : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (hs : 0 ≤ s)
    (x : B0579.Plane) :
    UnforcedLeray.Train.Vc ν c s x 1 =
      ∑' n : ℤ, UnforcedLeray.B0146.u2 (1 + ν * s) (x.1 - n * c, x.2) := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs
  rw [UnforcedLeray.Train.Vc_eq, UnforcedLeray.B0146.periodicVelocity_eq hc0 ha,
    UnforcedLeray.Train.toVec_one]
  rfl

/-- The first component of the isolated velocity is `u1` at width `1 + νs`. -/
theorem trainGap_iso_fst (ν s : ℝ) (x : B0579.Plane) :
    (UnforcedLeray.B0146.isoVelocity ν s x).1 = UnforcedLeray.B0146.u1 (1 + ν * s) x := by
  rw [UnforcedLeray.B0146.isoVelocity_apply]
  rfl

/-- The second component of the isolated velocity is `u2` at width `1 + νs`. -/
theorem trainGap_iso_snd (ν s : ℝ) (x : B0579.Plane) :
    (UnforcedLeray.B0146.isoVelocity ν s x).2 = UnforcedLeray.B0146.u2 (1 + ν * s) x := by
  rw [UnforcedLeray.B0146.isoVelocity_apply]
  rfl

/-- Absolute value of a Gaussian-dominated lattice sum, uniformly in the base point. -/
theorem trainGap_abs_tsum {β c C₀ : ℝ} (hβ : 0 < β) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀) (x : ℝ)
    {f : ℤ → ℝ} (hf : ∀ n : ℤ, |f n| ≤ C₀ * Real.exp (-(β * (x - n * c) ^ 2))) :
    |∑' n, f n| ≤ C₀ * ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have hs : Summable (fun n : ℤ => C₀ * Real.exp (-(β * (x - n * c) ^ 2))) :=
    (UnforcedLeray.B0146.summable_exp_shift hβ hc0 x).mul_left C₀
  calc |∑' n, f n| ≤ ∑' n : ℤ, C₀ * Real.exp (-(β * (x - n * c) ^ 2)) :=
        TrainGap.abs_tsum_le' hs hf
    _ = C₀ * ∑' n : ℤ, Real.exp (-(β * (x - n * c) ^ 2)) := tsum_mul_left
    _ ≤ C₀ * ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (TrainGap.lattice_uniform hβ hc x) hC₀

/-- The series over the cell with its `n = 0` term removed, for a Gaussian-dominated summand. -/
theorem trainGap_cell_tail {β c C₀ : ℝ} (hβ : 0 < β) (hc : 1 ≤ c) (hC₀ : 0 ≤ C₀)
    {x : B0579.Plane} (hx : |x.1| ≤ c / 2) {f : ℤ → ℝ} (y : ℝ) (hy : f 0 = y)
    (hf : ∀ n : ℤ, |f n| ≤ C₀ * Real.exp (-(β * (x.1 - n * c) ^ 2))) :
    |∑' n, f n - y| ≤
      C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2))) *
        ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have hγ : 0 < β / 4 := by
    have : (0 : ℝ) < 1 := one_pos
    linarith
  have hsum : Summable f := TrainGap.summable_of_gauss_bound hβ hc0 hf
  have hH : Summable (fun m : ℤ =>
      (C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)))) *
        Real.exp (-((β / 4) * (m : ℝ) ^ 2))) :=
    (TrainGap.summable_gauss_int hγ).mul_left _
  have hb : ∀ n : ℤ, n ≠ 0 → |f n| ≤
      (C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)))) *
        Real.exp (-((β / 4) * (n : ℝ) ^ 2)) := by
    intro n hn
    have h1 := hf n
    have h2 := TrainGap.tail_exp_le hβ hc hx hn
    have h3 : C₀ * Real.exp (-(β * (x.1 - n * c) ^ 2)) ≤
        C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)) *
          Real.exp (-((β / 4) * (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left h2 hC₀
    calc |f n| ≤ C₀ * Real.exp (-(β * (x.1 - n * c) ^ 2)) := h1
      _ ≤ C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)) *
          Real.exp (-((β / 4) * (n : ℝ) ^ 2))) := h3
      _ = (C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)))) *
          Real.exp (-((β / 4) * (n : ℝ) ^ 2)) := by ring
  have hH0 : ∀ n : ℤ, 0 ≤ (C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)))) *
      Real.exp (-((β / 4) * (n : ℝ) ^ 2)) := fun n =>
    mul_nonneg (mul_nonneg hC₀ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
      (Real.exp_pos _).le
  have hmain := TrainGap.tsum_ite_zero_bound hsum hH hH0 hb
  rw [← hy]
  calc |∑' n, f n - f 0| ≤ ∑' m : ℤ,
        (C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)))) *
          Real.exp (-((β / 4) * (m : ℝ) ^ 2)) := hmain
    _ = (C₀ * (Real.exp (β / 4) * Real.exp (-((β / 4) * c ^ 2)))) *
          ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) := tsum_mul_left

/-- **Leaf 6: the train gap on the cell** (SP 2085-2093, line 2108). For `Σ > 0` there are
`C, b > 0` such that for `ν > 0`, `c ≥ 1`, `δ ≥ 0`, a train with `TrainClose tr Σ δ` and every
age `σ ∈ [0, Σ/ν]`: the velocity is bounded by `C(δ + 1)` on the plane, and on the cell it differs
from the central Gaussian vortex `isoVelocity ν σ` by at most `C(δ + e^{-b c²})`. -/
theorem cylTrainGap : CylTrainGap := by
  unfold CylTrainGap
  intro Sg hSg
  set K : ℝ := 1 + Sg with hKdef
  have hK : 0 < K := by rw [hKdef]; linarith
  set β : ℝ := 1 / (8 * K) with hβdef
  have hβ : 0 < β := div_pos one_pos (by linarith)
  set C₀ : ℝ := 2 * K + 1 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  set L : ℝ := ∑' m : ℤ, Real.exp (-((β / 4) * (m : ℝ) ^ 2)) with hLdef
  have hL0 : 0 ≤ L := tsum_nonneg (fun m => (Real.exp_pos _).le)
  set E : ℝ := Real.exp (β / 4) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  set C : ℝ := 2 + 2 * (C₀ * E * L) with hCdef
  have hPos : 0 ≤ C₀ * E * L := mul_nonneg (mul_nonneg hC₀.le (by linarith)) hL0
  have hC2 : 2 ≤ C := by rw [hCdef]; linarith
  have hCpos : 0 < C := by linarith
  have hbpos : 0 < β / 4 := by linarith
  refine ⟨C, β / 4, hCpos, hbpos, ?_⟩
  intro ν c δ hν hc hδ tr htr σ hσ
  obtain ⟨hσ0, hσS⟩ := hσ
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hc).ne'
  have hνσ : ν * σ ≤ Sg := by
    have h1 : ν * (Sg / ν) = Sg := by field_simp
    have h2 : ν * σ ≤ ν * (Sg / ν) := mul_le_mul_of_nonneg_left hσS hν.le
    linarith
  have hνσ0 : 0 ≤ ν * σ := mul_nonneg hν.le hσ0
  have ha1 : 1 ≤ 1 + ν * σ := by linarith
  have haK : 1 + ν * σ ≤ K := by rw [hKdef]; linarith
  -- pointwise closeness at order zero: `TrainClose` on the cell, extended to the plane by
  -- `c`-periodicity (`Sub/TrainCloseCell.lean`)
  have hclose : ∀ x : B0579.Plane, ‖tr.v σ x - UnforcedLeray.Train.Vc ν c σ x‖ ≤ δ :=
    fun x => htr.norm_sub_le (lt_of_lt_of_le one_pos hc) hσ0 hσS x
  have hcomp : ∀ x : B0579.Plane, ∀ k : Fin 2,
      |tr.v σ x k - UnforcedLeray.Train.Vc ν c σ x k| ≤ δ := by
    intro x k
    have h1 := PiLp.norm_apply_le (tr.v σ x - UnforcedLeray.Train.Vc ν c σ x) k
    rw [PiLp.sub_apply, Real.norm_eq_abs] at h1
    exact h1.trans (hclose x)
  -- uniform bound on the periodized vortex (for the `δ + 1` part)
  have hunif : ∀ x : B0579.Plane,
      |UnforcedLeray.Train.Vc ν c σ x 0| ≤ C₀ * L ∧ |UnforcedLeray.Train.Vc ν c σ x 1| ≤ C₀ * L := by
    intro x
    constructor
    · rw [trainGap_vc_fst hν hc hσ0 x]
      exact trainGap_abs_tsum (f := fun n : ℤ => UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2))
        hβ hc hC₀.le x.1 (fun n => TrainGap.abs_u1_le ha1 haK (x.1 - n * c, x.2))
    · rw [trainGap_vc_snd hν hc hσ0 x]
      exact trainGap_abs_tsum (f := fun n : ℤ => UnforcedLeray.B0146.u2 (1 + ν * σ) (x.1 - n * c, x.2))
        hβ hc hC₀.le x.1 (fun n => TrainGap.abs_u2_le ha1 haK (x.1 - n * c, x.2))
  have hEL : C₀ * L ≤ C₀ * E * L := by
    have h := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hC₀.le hL0)
    nlinarith [h]
  -- part (i): the `δ + 1` bound on the whole plane
  have hpart1 : ∀ x : B0579.Plane,
      |tr.v σ x 0| + |tr.v σ x 1| ≤ C * (δ + 1) := by
    intro x
    have h0 := hcomp x 0
    have h1 := hcomp x 1
    obtain ⟨u0, u1'⟩ := hunif x
    obtain ⟨h0a, h0b⟩ := abs_le.mp h0
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨u0a, u0b⟩ := abs_le.mp u0
    obtain ⟨u1a, u1b⟩ := abs_le.mp u1'
    have t0 : |tr.v σ x 0| ≤ δ + C₀ * L := abs_le.mpr ⟨by linarith, by linarith⟩
    have t1 : |tr.v σ x 1| ≤ δ + C₀ * L := abs_le.mpr ⟨by linarith, by linarith⟩
    have hδC : 0 ≤ (C - 2) * δ := mul_nonneg (by linarith) hδ
    rw [hCdef] at hδC ⊢
    nlinarith [mul_nonneg hPos hδ]
  refine ⟨hpart1, ?_⟩
  -- part (ii): the cell estimate
  intro x hx
  have hx' : x.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.mp hx).1
  obtain ⟨hl, hr⟩ := Set.mem_Ico.mp hx'
  have hx1 : |x.1| ≤ c / 2 := abs_le.mpr ⟨hl, hr.le⟩
  have key0 : |(∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2)) -
      UnforcedLeray.B0146.u1 (1 + ν * σ) x| ≤ C₀ * (E * Real.exp (-((β / 4) * c ^ 2))) * L := by
    have h := trainGap_cell_tail
      (f := fun n : ℤ => UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2))
      hβ hc hC₀.le hx1 (UnforcedLeray.B0146.u1 (1 + ν * σ) x) (by simp)
      (fun n => TrainGap.abs_u1_le ha1 haK (x.1 - n * c, x.2))
    rw [← hEdef, ← hLdef] at h
    exact h
  have key1 : |(∑' n : ℤ, UnforcedLeray.B0146.u2 (1 + ν * σ) (x.1 - n * c, x.2)) -
      UnforcedLeray.B0146.u2 (1 + ν * σ) x| ≤ C₀ * (E * Real.exp (-((β / 4) * c ^ 2))) * L := by
    have h := trainGap_cell_tail
      (f := fun n : ℤ => UnforcedLeray.B0146.u2 (1 + ν * σ) (x.1 - n * c, x.2))
      hβ hc hC₀.le hx1 (UnforcedLeray.B0146.u2 (1 + ν * σ) x) (by simp)
      (fun n => TrainGap.abs_u2_le ha1 haK (x.1 - n * c, x.2))
    rw [← hEdef, ← hLdef] at h
    exact h
  have hd0 : |tr.v σ x 0 - UnforcedLeray.B0146.u1 (1 + ν * σ) x| ≤
      δ + C₀ * (E * Real.exp (-((β / 4) * c ^ 2))) * L := by
    have h1 := hcomp x 0
    rw [trainGap_vc_fst hν hc hσ0 x] at h1
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp key0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hd1 : |tr.v σ x 1 - UnforcedLeray.B0146.u2 (1 + ν * σ) x| ≤
      δ + C₀ * (E * Real.exp (-((β / 4) * c ^ 2))) * L := by
    have h1 := hcomp x 1
    rw [trainGap_vc_snd hν hc hσ0 x] at h1
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp key1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [trainGap_iso_fst ν σ x, trainGap_iso_snd ν σ x, neg_mul, hCdef]
  have he0 : 0 ≤ Real.exp (-((β / 4) * c ^ 2)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg hPos hδ, mul_nonneg hPos he0, hd0, hd1]

end UnforcedLeray.Short.IIb
