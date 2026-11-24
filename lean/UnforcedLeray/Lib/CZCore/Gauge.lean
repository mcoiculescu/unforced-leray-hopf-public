import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.Lattice

/-!
# Anisotropic gauge and dyadic boxes with integer weights (INF01 T8, with INF02 T0)


target T8 (anisotropic geometry, integer weights), together with the gauge facts of INF02 T0
(`scoping/INF02-FabesRiviere.md` §5), as decision D4 of `scoping/README.md` §3 prescribes.
Manuscript use: the Calderón–Zygmund bounds of the Leray projection (blueprint unit B0414,
`paper/main.tex` lines 7336–7344, citing Grafakos Cor. 5.2.8) and the parabolic estimate
eq:free-stress-11 (unit B0423, lines 7447–7477), whose kernel is homogeneous for the
parabolic weights `a = (2,1,…,1)`.

Weights are `a : Fin N → ℕ+`; the elliptic case is `a = 1`, the parabolic one `a = (2,1,…,1)`.

## Gauge (INF02 T0)

* `anisoNorm a x = max_i |x_i|^{1/a_i}` (a finite supremum in `ℝ≥0`; `0` when `N = 0`).
* `anisoNorm_add_le` (subadditivity, from the concavity of `t ↦ t^{1/a}`), `anisoNorm_neg`,
  `anisoNorm_sub_comm`, `anisoNorm_pos`, `continuous_anisoNorm`.
* `anisoNorm_dil`: `ρ(δ_λ x) = λ ρ(x)` for `δ_λ x = (λ^{a_i} x_i)`.
* `volume_anisoClosedBall`, `volume_anisoBall`: `|{ρ ≤ r}| = |{ρ < r}| = 2^N r^{|a|}` with
  `|a| = homDim a = Σ a_i`; translated forms `volume_anisoClosedBall_sub`.
* `lintegral_anisoNorm_rpow_neg_le`: the tail integral
  `∫_{ρ > R} ρ^{-b} ≤ 2^N 2^{|a|} (1 - 2^{|a|-b})^{-1} R^{|a|-b}` for `b > |a|`.

## Dyadic boxes (INF01 T8)

* `dyLen k = 2^{-k}`; the generation-`k` box with index `m ∈ ℤ^N` is
  `dyadicBox a k m = Π_i [m_i ℓ_i, (m_i+1) ℓ_i)`, `ℓ_i = dyLen k ^ a_i`.
* `mem_dyadicBox_iff`: `x ∈ dyadicBox a k m ↔ dyIdx a k x = m`, so boxes of one generation
  partition the space.
* `dyIdx_eq_of_le`, `dyadicBox_subset_of_le`: boxes nest (integer weights).
* `volume_dyadicBox`: `|Q| = dyLen k ^ |a|`; `volume_dyadicBox_pred`: the parent has volume
  `2^{|a|} |Q|`.
* `anisoNorm_sub_dyCenter_le`: the closed box lies in `{ρ(· - c_Q) ≤ dyLen k}`;
  `volume_dyStar`: the expanded set `{ρ(· - c_Q) ≤ 2 dyLen k}` has volume `2^{N+|a|} |Q|`.
* `dist_le_of_dyIdx_eq`: two points of one box of generation `k ≥ 0` are within `dyLen k`.
* `finite_dyIdx_image`: a bounded set meets finitely many boxes of a given generation.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {N : ℕ}

/-- The homogeneous dimension `|a| = Σ_i a_i`. -/
def homDim (a : Fin N → ℕ+) : ℕ := ∑ i, (a i : ℕ)

/-- The anisotropic gauge in `ℝ≥0`: `max_i ‖x_i‖^{1/a_i}`. -/
def anisoNNorm (a : Fin N → ℕ+) (x : Fin N → ℝ) : ℝ≥0 :=
  Finset.univ.sup fun i => ‖x i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹)

/-- **T8 (INF01 §5) / T0 (INF02 §5).** The anisotropic gauge `ρ_a(x) = max_i |x_i|^{1/a_i}`. -/
def anisoNorm (a : Fin N → ℕ+) (x : Fin N → ℝ) : ℝ := anisoNNorm a x

section Gauge

variable (a : Fin N → ℕ+)

theorem anisoNorm_nonneg (x : Fin N → ℝ) : 0 ≤ anisoNorm a x := NNReal.coe_nonneg _

theorem inv_weight_pos (i : Fin N) : 0 < (((a i : ℕ) : ℝ))⁻¹ := by
  have : (0 : ℝ) < ((a i : ℕ) : ℝ) := by exact_mod_cast (a i).pos
  positivity

theorem inv_weight_le_one (i : Fin N) : (((a i : ℕ) : ℝ))⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast (a i).pos)

theorem one_le_homDim [NeZero N] : 1 ≤ homDim a := by
  unfold homDim
  calc 1 ≤ (a 0 : ℕ) := (a 0).pos
    _ ≤ ∑ i, (a i : ℕ) :=
        Finset.single_le_sum (f := fun i => (a i : ℕ)) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ _)

theorem abs_rpow_le_anisoNorm (x : Fin N → ℝ) (i : Fin N) :
    |x i| ^ (((a i : ℕ) : ℝ)⁻¹) ≤ anisoNorm a x := by
  have h : ‖x i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹) ≤ anisoNNorm a x :=
    Finset.le_sup (f := fun i => ‖x i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹)) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 h
  simpa [anisoNorm, NNReal.coe_rpow] using h2

theorem anisoNorm_le_iff {x : Fin N → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    anisoNorm a x ≤ r ↔ ∀ i, |x i| ^ (((a i : ℕ) : ℝ)⁻¹) ≤ r := by
  constructor
  · intro h i; exact (abs_rpow_le_anisoNorm a x i).trans h
  · intro h
    have : anisoNNorm a x ≤ r.toNNReal := by
      refine Finset.sup_le fun i _ => ?_
      rw [Real.le_toNNReal_iff_coe_le hr]
      simpa [NNReal.coe_rpow] using h i
    exact (Real.le_toNNReal_iff_coe_le hr).1 this

theorem anisoNorm_lt_iff {x : Fin N → ℝ} {r : ℝ} (hr : 0 < r) :
    anisoNorm a x < r ↔ ∀ i, |x i| ^ (((a i : ℕ) : ℝ)⁻¹) < r := by
  constructor
  · intro h i; exact (abs_rpow_le_anisoNorm a x i).trans_lt h
  · intro h
    have : anisoNNorm a x < r.toNNReal := by
      refine (Finset.sup_lt_iff (show (⊥ : ℝ≥0) < r.toNNReal from
        Real.toNNReal_pos.2 hr)).2 fun i _ => ?_
      rw [Real.lt_toNNReal_iff_coe_lt]
      simpa [NNReal.coe_rpow] using h i
    exact Real.lt_toNNReal_iff_coe_lt.1 this

/-- `|t|^{1/a} ≤ r ↔ |t| ≤ r^a`. -/
theorem abs_rpow_inv_le_iff {t r : ℝ} (hr : 0 ≤ r) (n : ℕ+) :
    |t| ^ (((n : ℕ) : ℝ)⁻¹) ≤ r ↔ |t| ≤ r ^ (n : ℕ) := by
  rw [Real.rpow_inv_le_iff_of_pos (abs_nonneg t) hr (by exact_mod_cast n.pos),
    Real.rpow_natCast]

theorem abs_rpow_inv_lt_iff {t r : ℝ} (hr : 0 ≤ r) (n : ℕ+) :
    |t| ^ (((n : ℕ) : ℝ)⁻¹) < r ↔ |t| < r ^ (n : ℕ) := by
  rw [Real.rpow_inv_lt_iff_of_pos (abs_nonneg t) hr (by exact_mod_cast n.pos),
    Real.rpow_natCast]

theorem anisoNorm_le_iff_abs {x : Fin N → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    anisoNorm a x ≤ r ↔ ∀ i, |x i| ≤ r ^ (a i : ℕ) := by
  rw [anisoNorm_le_iff a hr]
  exact forall_congr' fun i => abs_rpow_inv_le_iff hr (a i)

theorem anisoNorm_lt_iff_abs {x : Fin N → ℝ} {r : ℝ} (hr : 0 < r) :
    anisoNorm a x < r ↔ ∀ i, |x i| < r ^ (a i : ℕ) := by
  rw [anisoNorm_lt_iff a hr]
  exact forall_congr' fun i => abs_rpow_inv_lt_iff hr.le (a i)

theorem abs_le_anisoNorm_pow (x : Fin N → ℝ) (i : Fin N) : |x i| ≤ anisoNorm a x ^ (a i : ℕ) :=
  (anisoNorm_le_iff_abs a (anisoNorm_nonneg a x)).1 le_rfl i

/-- **Subadditivity** of the gauge (concavity of `t ↦ t^{1/a}`, `a ≥ 1`). -/
theorem anisoNorm_add_le (x y : Fin N → ℝ) :
    anisoNorm a (x + y) ≤ anisoNorm a x + anisoNorm a y := by
  have h : anisoNNorm a (x + y) ≤ anisoNNorm a x + anisoNNorm a y := by
    refine Finset.sup_le fun i _ => ?_
    have hx : ‖x i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹) ≤ anisoNNorm a x :=
      Finset.le_sup (f := fun i => ‖x i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹)) (Finset.mem_univ i)
    have hy : ‖y i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹) ≤ anisoNNorm a y :=
      Finset.le_sup (f := fun i => ‖y i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹)) (Finset.mem_univ i)
    calc ‖(x + y) i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹)
        ≤ (‖x i‖₊ + ‖y i‖₊) ^ (((a i : ℕ) : ℝ)⁻¹) :=
          NNReal.rpow_le_rpow (nnnorm_add_le _ _) (inv_weight_pos a i).le
      _ ≤ ‖x i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹) + ‖y i‖₊ ^ (((a i : ℕ) : ℝ)⁻¹) :=
          NNReal.rpow_add_le_add_rpow _ _ (inv_weight_pos a i).le (inv_weight_le_one a i)
      _ ≤ anisoNNorm a x + anisoNNorm a y := add_le_add hx hy
  exact_mod_cast h

theorem anisoNorm_neg (x : Fin N → ℝ) : anisoNorm a (-x) = anisoNorm a x := by
  simp [anisoNorm, anisoNNorm]

theorem anisoNorm_sub_comm (x y : Fin N → ℝ) : anisoNorm a (x - y) = anisoNorm a (y - x) := by
  rw [← anisoNorm_neg, neg_sub]

theorem anisoNorm_zero : anisoNorm a 0 = 0 := by
  have h := (anisoNorm_le_iff_abs a (le_refl (0 : ℝ)) (x := 0)).2 fun i => by
    simp [zero_pow (a i).ne_zero]
  exact le_antisymm h (anisoNorm_nonneg a 0)

theorem anisoNorm_pos {x : Fin N → ℝ} (hx : x ≠ 0) : 0 < anisoNorm a x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact (Real.rpow_pos_of_pos (abs_pos.2 hi) _).trans_le (abs_rpow_le_anisoNorm a x i)

/-- Reverse triangle inequality. -/
theorem anisoNorm_sub_le_sub (x y : Fin N → ℝ) :
    anisoNorm a x - anisoNorm a y ≤ anisoNorm a (x - y) := by
  have := anisoNorm_add_le a (x - y) y
  rw [sub_add_cancel] at this
  linarith

theorem continuous_anisoNorm : Continuous (anisoNorm a) := by
  refine NNReal.continuous_coe.comp ?_
  unfold anisoNNorm
  refine Continuous.finset_sup_apply fun i _ => ?_
  exact (NNReal.continuous_rpow_const (inv_weight_pos a i).le).comp
    (continuous_nnnorm.comp (continuous_apply i))

theorem measurable_anisoNorm : Measurable (anisoNorm a) := (continuous_anisoNorm a).measurable

/-- The anisotropic dilation `δ_λ x = (λ^{a_i} x_i)_i`. -/
def anisoDil (l : ℝ) (x : Fin N → ℝ) : Fin N → ℝ := fun i => l ^ (a i : ℕ) * x i

/-- **Dilation** (INF02 T0): `ρ(δ_λ x) = λ ρ(x)` for `λ ≥ 0`. -/
theorem anisoNorm_dil {l : ℝ} (hl : 0 ≤ l) (x : Fin N → ℝ) :
    anisoNorm a (anisoDil a l x) = l * anisoNorm a x := by
  set L : ℝ≥0 := l.toNNReal
  have hL : ‖l‖₊ = L := by ext; simp [abs_of_nonneg hl, L, Real.coe_toNNReal _ hl]
  have h : anisoNNorm a (anisoDil a l x) = L * anisoNNorm a x := by
    unfold anisoNNorm
    rw [NNReal.mul_finset_sup]
    refine Finset.sup_congr rfl fun i _ => ?_
    simp only [anisoDil, nnnorm_mul, nnnorm_pow, hL]
    rw [NNReal.mul_rpow, NNReal.pow_rpow_inv_natCast _ (a i).ne_zero]
  simp [anisoNorm, h, L, Real.coe_toNNReal _ hl]

/-- The closed anisotropic ball is a coordinate box. -/
theorem anisoClosedBall_eq {r : ℝ} (hr : 0 ≤ r) :
    {x : Fin N → ℝ | anisoNorm a x ≤ r} =
      Icc (fun i => -r ^ (a i : ℕ)) (fun i => r ^ (a i : ℕ)) := by
  ext x
  simp only [mem_ofPred_eq, anisoNorm_le_iff_abs a hr, mem_Icc, Pi.le_def, abs_le]
  constructor
  · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · intro h i; exact ⟨h.1 i, h.2 i⟩

/-- The open anisotropic ball is a coordinate box. -/
theorem anisoBall_eq {r : ℝ} (hr : 0 < r) :
    {x : Fin N → ℝ | anisoNorm a x < r} =
      univ.pi fun i => Ioo (-r ^ (a i : ℕ)) (r ^ (a i : ℕ)) := by
  ext x
  simp only [mem_ofPred_eq, anisoNorm_lt_iff_abs a hr, mem_univ_pi, mem_Ioo, abs_lt]

private theorem prod_two_mul_pow (r : ℝ) :
    ∏ i, (r ^ (a i : ℕ) - -r ^ (a i : ℕ)) = 2 ^ N * r ^ homDim a := by
  have : ∀ i, r ^ (a i : ℕ) - -r ^ (a i : ℕ) = 2 * r ^ (a i : ℕ) := fun i => by ring
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum, homDim]

/-- **Volume of the closed gauge ball** (INF02 T0): `|{ρ ≤ r}| = 2^N r^{|a|}`. -/
theorem volume_anisoClosedBall {r : ℝ} (hr : 0 ≤ r) :
    volume {x : Fin N → ℝ | anisoNorm a x ≤ r} = ENNReal.ofReal (2 ^ N * r ^ homDim a) := by
  rw [anisoClosedBall_eq a hr, Real.volume_Icc_pi, ← ENNReal.ofReal_prod_of_nonneg, prod_two_mul_pow]
  intro i _
  have : 0 ≤ r ^ (a i : ℕ) := pow_nonneg hr _
  linarith

/-- **Volume of the open gauge ball** (INF02 T0): `|{ρ < r}| = 2^N r^{|a|}`. -/
theorem volume_anisoBall {r : ℝ} (hr : 0 < r) :
    volume {x : Fin N → ℝ | anisoNorm a x < r} = ENNReal.ofReal (2 ^ N * r ^ homDim a) := by
  rw [anisoBall_eq a hr, Real.volume_pi_Ioo, ← ENNReal.ofReal_prod_of_nonneg, prod_two_mul_pow]
  intro i _
  have : 0 ≤ r ^ (a i : ℕ) := pow_nonneg hr.le _
  linarith

theorem measurableSet_anisoClosedBall_sub (c : Fin N → ℝ) (r : ℝ) :
    MeasurableSet {x : Fin N → ℝ | anisoNorm a (x - c) ≤ r} :=
  measurableSet_le ((measurable_anisoNorm a).comp (measurable_id.sub_const c)) measurable_const

theorem measurableSet_anisoFar_sub (c : Fin N → ℝ) (r : ℝ) :
    MeasurableSet {x : Fin N → ℝ | r < anisoNorm a (x - c)} :=
  measurableSet_lt measurable_const ((measurable_anisoNorm a).comp (measurable_id.sub_const c))

/-- Translated closed gauge ball. -/
theorem volume_anisoClosedBall_sub (c : Fin N → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume {x : Fin N → ℝ | anisoNorm a (x - c) ≤ r} = ENNReal.ofReal (2 ^ N * r ^ homDim a) := by
  have : {x : Fin N → ℝ | anisoNorm a (x - c) ≤ r} =
      (fun x => x + -c) ⁻¹' {x | anisoNorm a x ≤ r} := by
    ext x; simp [sub_eq_add_neg]
  rw [this, measure_preimage_add_right, volume_anisoClosedBall a hr]

/-- `(2^j R)^{-b} (2^{j+1} R)^{|a|} = 2^{|a|} R^{|a|-b} (2^{|a|-b})^j`. -/
private theorem shell_algebra {R : ℝ} (hR : 0 < R) (b : ℝ) (d : ℕ) (j : ℕ) :
    ((2 : ℝ) ^ j * R) ^ (-b) * ((2 : ℝ) ^ (j + 1) * R) ^ d =
      2 ^ d * R ^ ((d : ℝ) - b) * ((2 : ℝ) ^ ((d : ℝ) - b)) ^ j := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have e1 : ((2 : ℝ) ^ j * R) ^ (-b) = (2 : ℝ) ^ ((j : ℝ) * -b) * R ^ (-b) := by
    rw [Real.mul_rpow (by positivity) hR.le, ← Real.rpow_natCast, ← Real.rpow_mul h2.le]
  have e2 : ((2 : ℝ) ^ (j + 1) * R) ^ d = (2 : ℝ) ^ (((j : ℝ) + 1) * d) * R ^ (d : ℝ) := by
    rw [mul_pow, ← pow_mul, ← Real.rpow_natCast R, ← Real.rpow_natCast (2 : ℝ) ((j + 1) * d)]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have e3 : ((2 : ℝ) ^ ((d : ℝ) - b)) ^ j = (2 : ℝ) ^ (((d : ℝ) - b) * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le]
  have e4 : (2 : ℝ) ^ d = (2 : ℝ) ^ (d : ℝ) := (Real.rpow_natCast 2 d).symm
  have e5 : R ^ ((d : ℝ) - b) = R ^ (-b) * R ^ (d : ℝ) := by
    rw [← Real.rpow_add hR]; ring_nf
  rw [e1, e2, e3, e4, e5]
  calc (2 : ℝ) ^ ((j : ℝ) * -b) * R ^ (-b) * ((2 : ℝ) ^ (((j : ℝ) + 1) * d) * R ^ (d : ℝ))
      = ((2 : ℝ) ^ ((j : ℝ) * -b) * (2 : ℝ) ^ (((j : ℝ) + 1) * d)) * (R ^ (-b) * R ^ (d : ℝ)) := by
        ring
    _ = (2 : ℝ) ^ ((j : ℝ) * -b + ((j : ℝ) + 1) * d) * (R ^ (-b) * R ^ (d : ℝ)) := by
        rw [Real.rpow_add h2]
    _ = (2 : ℝ) ^ ((d : ℝ) + ((d : ℝ) - b) * j) * (R ^ (-b) * R ^ (d : ℝ)) := by
        rw [show (j : ℝ) * -b + ((j : ℝ) + 1) * d = (d : ℝ) + ((d : ℝ) - b) * j by ring]
    _ = _ := by rw [Real.rpow_add h2]; ring

/-- **Tail integral** (INF02 T0): for `b > |a|` and `R > 0`,
`∫_{ρ > R} ρ^{-b} ≤ 2^N 2^{|a|} (1 - 2^{|a|-b})^{-1} R^{|a|-b}` (dyadic shells). -/
theorem lintegral_anisoNorm_rpow_neg_le {b R : ℝ} (hb : (homDim a : ℝ) < b) (hR : 0 < R) :
    ∫⁻ x in {x : Fin N → ℝ | R < anisoNorm a x}, ENNReal.ofReal (anisoNorm a x ^ (-b)) ≤
      ENNReal.ofReal (2 ^ N * 2 ^ homDim a * R ^ ((homDim a : ℝ) - b) /
        (1 - 2 ^ ((homDim a : ℝ) - b))) := by
  set d := homDim a
  set q : ℝ := (2 : ℝ) ^ ((d : ℝ) - b) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set S : ℕ → Set (Fin N → ℝ) := fun j =>
    {x | (2 : ℝ) ^ j * R < anisoNorm a x ∧ anisoNorm a x ≤ (2 : ℝ) ^ (j + 1) * R}
  have hcover : {x : Fin N → ℝ | R < anisoNorm a x} ⊆ ⋃ j, S j := by
    intro x hx
    simp only [mem_ofPred_eq] at hx
    have hex : ∃ n : ℕ, anisoNorm a x ≤ (2 : ℝ) ^ (n + 1) * R := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (anisoNorm a x / R) (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hR] at hn
      have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
      nlinarith
    classical
    refine mem_iUnion.2 ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simpa using hx
    · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      push Not at hmin
      rwa [Nat.sub_add_cancel (show 1 ≤ Nat.find hex from hpos)] at hmin
  have hshell : ∀ j : ℕ, ∫⁻ x in S j, ENNReal.ofReal (anisoNorm a x ^ (-b)) ≤
      ENNReal.ofReal (2 ^ N * 2 ^ d * R ^ ((d : ℝ) - b) * q ^ j) := by
    intro j
    have hpos : 0 < (2 : ℝ) ^ j * R := by positivity
    calc ∫⁻ x in S j, ENNReal.ofReal (anisoNorm a x ^ (-b))
        ≤ ∫⁻ _ in S j, ENNReal.ofReal (((2 : ℝ) ^ j * R) ^ (-b)) := by
          refine setLIntegral_mono' ?_ fun x hx => ?_
          · exact (measurableSet_lt measurable_const (measurable_anisoNorm a)).inter
              (measurableSet_le (measurable_anisoNorm a) measurable_const)
          · exact ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow_of_nonpos hpos hx.1.le (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]))
      _ = ENNReal.ofReal (((2 : ℝ) ^ j * R) ^ (-b)) * volume (S j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ j * R) ^ (-b)) *
            ENNReal.ofReal (2 ^ N * ((2 : ℝ) ^ (j + 1) * R) ^ d) := by
          gcongr
          rw [← volume_anisoClosedBall a (by positivity)]
          exact measure_mono fun x hx => hx.2
      _ = ENNReal.ofReal (2 ^ N * 2 ^ d * R ^ ((d : ℝ) - b) * q ^ j) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have := shell_algebra hR b d j
          rw [hq]
          linear_combination (2 ^ N : ℝ) * this
  calc ∫⁻ x in {x : Fin N → ℝ | R < anisoNorm a x}, ENNReal.ofReal (anisoNorm a x ^ (-b))
      ≤ ∫⁻ x in ⋃ j, S j, ENNReal.ofReal (anisoNorm a x ^ (-b)) := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ x in S j, ENNReal.ofReal (anisoNorm a x ^ (-b)) := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (2 ^ N * 2 ^ d * R ^ ((d : ℝ) - b)) * ENNReal.ofReal q ^ j := by
        refine ENNReal.tsum_le_tsum fun j => (hshell j).trans_eq ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq0]
    _ = ENNReal.ofReal (2 ^ N * 2 ^ d * R ^ ((d : ℝ) - b)) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (2 ^ N * 2 ^ d * R ^ ((d : ℝ) - b) / (1 - q)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0,
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity),
          div_eq_mul_inv]

end Gauge

end UnforcedLeray.CZ
