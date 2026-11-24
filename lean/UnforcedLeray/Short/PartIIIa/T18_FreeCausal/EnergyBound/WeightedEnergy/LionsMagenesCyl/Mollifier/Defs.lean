import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1` (`Mollifier`): the periodic mollifier on the cylinder

Source of record: `the November 2 reference manuscript`, lines 3427-3440 (the
energy class on the cylinder `C_c = (ℝ/cℤ) × ℝ`, `∇b ∈ L²_loc((0,∞); L²)`) and 3541-3552 (the
energy identity, whose proof mollifies `b(s)` on the cylinder). This file fixes the concrete
mollifier family used for `HasLMMollifier` (`Sub/T18_3_1_3.lean`).

* `lmPer1 c t ∈ [-c/2, c/2)` is `t` reduced modulo `c` (for `c > 0`), and `lmPer c (q, η) =
  (lmPer1 c q, η)` reduces a point of the plane to the cell `B0579.cell c = [-c/2, c/2) × ℝ`.
* `lmRho c k` is the normalized smooth bump of `Mathlib` (`ContDiffBump.normed`) on `ℝ × ℝ`
  (sup norm), centred at `0`, with radii `δ/(k+2) < δ/(k+1)`, `δ = c/4` for `c > 0`: even,
  nonnegative, smooth, of unit mass, supported in the ball of radius `δ/(k+1) → 0`.
* `lmK c k z = lmRho c k (lmPer c z)` is the periodized kernel. Since the support of `lmRho c k`
  lies in `|z₁| < c/4 < c/2`, at most one translate `lmRho c k (z₁ + n c, z₂)` is nonzero, so
  `lmK c k z = ∑ₙ lmRho c k (z₁ + n c, z₂)`: this is the periodization `K_k` of the task spec.
* `lmJs c k g x = ∫_cell K_k(x - y) g(y) dy` (scalar) and `lmJ c k f x i = lmJs c k f_i x`.
* `lmExt c g = g ∘ lmPer c` is the `c`-periodic extension of the restriction of `g` to the cell.

Proved here: the elementary facts on `lmPer1`, the support, sign, bound and measurability of the
kernel, and the clauses `periodic`, `smul` of `IsLMMollifier` for `lmJ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

/-! ### Reduction to the cell -/

/-- `t` reduced modulo `c` into `[-c/2, c/2)` (for `c > 0`). -/
def lmPer1 (c t : ℝ) : ℝ := c * Int.fract ((t + c / 2) / c) - c / 2

/-- Reduction of a point of the plane to the cell `[-c/2, c/2) × ℝ`. -/
def lmPer (c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (lmPer1 c z.1, z.2)

theorem lmPer1_add {c : ℝ} (hc : c ≠ 0) (t : ℝ) : lmPer1 c (t + c) = lmPer1 c t := by
  unfold lmPer1
  rw [show t + c + c / 2 = (t + c / 2) + c by ring, add_div, div_self hc, Int.fract_add_one]

theorem lmPer1_sub {c : ℝ} (hc : c ≠ 0) (t : ℝ) : lmPer1 c (t - c) = lmPer1 c t := by
  have h := lmPer1_add hc (t - c)
  rw [sub_add_cancel] at h
  exact h.symm

theorem lmPer1_mem {c : ℝ} (hc : 0 < c) (t : ℝ) : lmPer1 c t ∈ Ico (-(c / 2)) (c / 2) := by
  have h0 := Int.fract_nonneg ((t + c / 2) / c)
  have h1 := Int.fract_lt_one ((t + c / 2) / c)
  unfold lmPer1
  constructor <;> nlinarith

/-- `lmPer1 c t = t - n c` whenever `t - n c` lies in `[-c/2, c/2)`. -/
theorem lmPer1_eq_sub_int {c : ℝ} (hc : 0 < c) {t : ℝ} (n : ℤ)
    (h : t - n * c ∈ Ico (-(c / 2)) (c / 2)) : lmPer1 c t = t - n * c := by
  have hc0 : c ≠ 0 := hc.ne'
  have hfr : Int.fract ((t + c / 2) / c) = (t - n * c + c / 2) / c := by
    rw [Int.fract_eq_iff]
    refine ⟨div_nonneg (by linarith [h.1]) hc.le, (div_lt_one hc).2 (by linarith [h.2]), n, ?_⟩
    rw [← sub_div, show t + c / 2 - (t - n * c + c / 2) = n * c by ring,
      mul_div_cancel_right₀ _ hc0]
  unfold lmPer1
  rw [hfr, mul_div_cancel₀ _ hc0]
  ring

theorem lmPer1_of_mem {c : ℝ} (hc : 0 < c) {t : ℝ} (h : t ∈ Ico (-(c / 2)) (c / 2)) :
    lmPer1 c t = t := by
  have := lmPer1_eq_sub_int hc (t := t) 0 (by simpa using h)
  simpa using this

/-- `lmPer1 c t - t` is an integer multiple of `c`. -/
theorem lmPer1_sub_self {c : ℝ} (hc : c ≠ 0) (t : ℝ) : ∃ n : ℤ, lmPer1 c t = t - n * c := by
  refine ⟨⌊(t + c / 2) / c⌋, ?_⟩
  unfold lmPer1
  rw [← Int.self_sub_floor, mul_sub, mul_div_cancel₀ _ hc]
  ring

theorem measurable_lmPer1 (c : ℝ) : Measurable (lmPer1 c) := by
  unfold lmPer1
  exact (measurable_const.mul (measurable_fract.comp
    ((measurable_id.add_const _).div_const _))).sub_const _

theorem measurable_lmPer (c : ℝ) : Measurable (lmPer c) :=
  ((measurable_lmPer1 c).comp measurable_fst).prodMk measurable_snd

theorem lmPer_add (c : ℝ) (hc : c ≠ 0) (z : ℝ × ℝ) : lmPer c (z.1 + c, z.2) = lmPer c z := by
  simp [lmPer, lmPer1_add hc]

theorem lmPer_of_mem {c : ℝ} (hc : 0 < c) {z : ℝ × ℝ} (hz : z ∈ B0579.cell c) :
    lmPer c z = z := by
  have h1 : z.1 ∈ Ico (-(c / 2)) (c / 2) := hz.1
  simp [lmPer, lmPer1_of_mem hc h1]

/-! ### The bump and the periodized kernel -/

/-- The scale `δ = c/4` (for `c > 0`; `1` otherwise, a junk value making the bump well defined). -/
def lmDelta (c : ℝ) : ℝ := if 0 < c then c / 4 else 1

theorem lmDelta_pos (c : ℝ) : 0 < lmDelta c := by
  unfold lmDelta
  split_ifs with h
  · positivity
  · exact one_pos

theorem lmDelta_eq {c : ℝ} (hc : 0 < c) : lmDelta c = c / 4 := by
  simp [lmDelta, hc]

/-- The bump with radii `δ/(k+2) < δ/(k+1)` centred at `0`. -/
def lmBump (c : ℝ) (k : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := lmDelta c / (k + 2)
  rOut := lmDelta c / (k + 1)
  rIn_pos := div_pos (lmDelta_pos c) (by positivity)
  rIn_lt_rOut := by
    have h := lmDelta_pos c
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem lmBump_rOut (c : ℝ) (k : ℕ) : (lmBump c k).rOut = lmDelta c / (k + 1) := rfl

theorem lmBump_rIn (c : ℝ) (k : ℕ) : (lmBump c k).rIn = lmDelta c / (k + 2) := rfl

/-- The mollifier `ρ_k` on the plane: even, nonnegative, smooth, unit mass, support in the
(sup-norm) ball of radius `δ/(k+1)`. -/
def lmRho (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ := (lmBump c k).normed volume

/-- The periodized kernel `K_k(z) = ρ_k(z reduced to the cell) = ∑ₙ ρ_k(z₁ + n c, z₂)`. -/
def lmK (c : ℝ) (k : ℕ) (z : ℝ × ℝ) : ℝ := lmRho c k (lmPer c z)

/-- The periodic extension `g ∘ lmPer c` of the restriction of `g` to the cell. -/
def lmExt (c : ℝ) (g : ℝ × ℝ → ℂ) (y : ℝ × ℝ) : ℂ := g (lmPer c y)

/-- The scalar mollifier `J_k g(x) = ∫_cell K_k(x - y) g(y) dy`. -/
def lmJs (c : ℝ) (k : ℕ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  ∫ y in B0579.cell c, (lmK c k (x - y) : ℂ) * g y

/-- The mollifier family on vector fields, componentwise. -/
def lmJ (c : ℝ) (k : ℕ) (f : LMSpField) : LMSpField := fun x i => lmJs c k (fun y => f y i) x

theorem lmJ_apply (c : ℝ) (k : ℕ) (f : LMSpField) (x : ℝ × ℝ) (i : Fin 2) :
    lmJ c k f x i = lmJs c k (fun y => f y i) x := rfl

/-! ### Elementary facts on `ρ_k` and `K_k` -/

theorem lmRho_nonneg (c : ℝ) (k : ℕ) (z : ℝ × ℝ) : 0 ≤ lmRho c k z :=
  (lmBump c k).nonneg_normed z

theorem lmRho_neg (c : ℝ) (k : ℕ) (z : ℝ × ℝ) : lmRho c k (-z) = lmRho c k z :=
  (lmBump c k).normed_neg z

theorem lmRho_contDiff (c : ℝ) (k : ℕ) : ContDiff ℝ ∞ (lmRho c k) :=
  (lmBump c k).contDiff_normed

theorem lmRho_continuous (c : ℝ) (k : ℕ) : Continuous (lmRho c k) :=
  (lmBump c k).continuous_normed

theorem lmRho_hasCompactSupport (c : ℝ) (k : ℕ) : HasCompactSupport (lmRho c k) :=
  (lmBump c k).hasCompactSupport_normed

theorem lmRho_integral (c : ℝ) (k : ℕ) : ∫ z, lmRho c k z = 1 :=
  (lmBump c k).integral_normed

/-- Support: `ρ_k z ≠ 0` forces `‖z‖ < δ/(k+1)`. -/
theorem lmRho_ne_zero {c : ℝ} {k : ℕ} {z : ℝ × ℝ} (h : lmRho c k z ≠ 0) :
    ‖z‖ < lmDelta c / (k + 1) := by
  have hs : z ∈ Function.support (lmRho c k) := h
  unfold lmRho at hs
  rw [(lmBump c k).support_normed_eq, Metric.mem_ball, dist_zero_right] at hs
  exact hs

/-- `ρ_k z = 0` when `|z₁| ≥ c/4` or `|z₂| ≥ c/4` (`c > 0`). -/
theorem lmRho_eq_zero {c : ℝ} (hc : 0 < c) (k : ℕ) {z : ℝ × ℝ}
    (hz : c / 4 ≤ |z.1| ∨ c / 4 ≤ |z.2|) : lmRho c k z = 0 := by
  by_contra h
  have h1 := lmRho_ne_zero h
  rw [lmDelta_eq hc] at h1
  have h2 : c / 4 / (k + 1) ≤ c / 4 := div_le_self (by linarith) (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  have h3 : |z.1| ≤ ‖z‖ := by
    rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_left _ _
  have h4 : |z.2| ≤ ‖z‖ := by
    rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_right _ _
  rcases hz with hz | hz <;> linarith

theorem lmRho_bdd (c : ℝ) (k : ℕ) : ∃ M : ℝ, ∀ z : ℝ × ℝ, |lmRho c k z| ≤ M := by
  obtain ⟨M, hM⟩ := (lmRho_hasCompactSupport c k).exists_bound_of_continuous
    (lmRho_continuous c k)
  exact ⟨M, fun z => by simpa [Real.norm_eq_abs] using hM z⟩

theorem lmK_nonneg (c : ℝ) (k : ℕ) (z : ℝ × ℝ) : 0 ≤ lmK c k z := lmRho_nonneg c k _

theorem lmK_periodic {c : ℝ} (hc : c ≠ 0) (k : ℕ) (z : ℝ × ℝ) :
    lmK c k (z.1 + c, z.2) = lmK c k z := by
  simp only [lmK, lmPer_add c hc z]

theorem lmK_bdd (c : ℝ) (k : ℕ) : ∃ M : ℝ, ∀ z : ℝ × ℝ, |lmK c k z| ≤ M := by
  obtain ⟨M, hM⟩ := lmRho_bdd c k
  exact ⟨M, fun z => hM _⟩

theorem measurable_lmK (c : ℝ) (k : ℕ) : Measurable (lmK c k) :=
  (lmRho_continuous c k).measurable.comp (measurable_lmPer c)

/-- Band: `K_k z = 0` when `|z₂| ≥ c/4` (`c > 0`). -/
theorem lmK_eq_zero_of_snd {c : ℝ} (hc : 0 < c) (k : ℕ) {z : ℝ × ℝ} (hz : c / 4 ≤ |z.2|) :
    lmK c k z = 0 :=
  lmRho_eq_zero hc k (Or.inr hz)

/-- On `|z₁| < c/2` the kernel is the bump itself. -/
theorem lmK_eq_lmRho {c : ℝ} (hc : 0 < c) (k : ℕ) {z : ℝ × ℝ}
    (hz : z.1 ∈ Ico (-(c / 2)) (c / 2)) : lmK c k z = lmRho c k z := by
  simp [lmK, lmPer, lmPer1_of_mem hc hz]

/-! ### The clauses `periodic` and `smul` -/

theorem lmJs_periodic {c : ℝ} (hc : c ≠ 0) (k : ℕ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    lmJs c k g (x.1 + c, x.2) = lmJs c k g x := by
  unfold lmJs
  congr 1
  funext y
  have h : ((x.1 + c, x.2) : ℝ × ℝ) - y = ((x - y).1 + c, (x - y).2) := by
    ext <;> simp <;> ring
  rw [h, lmK_periodic hc]

theorem lmJs_smul (c : ℝ) (k : ℕ) (a : ℂ) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    lmJs c k (fun y => a * g y) x = a * lmJs c k g x := by
  unfold lmJs
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem lmJ_periodic {c : ℝ} (hc : c ≠ 0) (k : ℕ) (f : LMSpField) (x : ℝ × ℝ) (i : Fin 2) :
    lmJ c k f (x.1 + c, x.2) i = lmJ c k f x i :=
  lmJs_periodic hc k _ x

theorem lmJ_smul (c : ℝ) (k : ℕ) (a : ℂ) (f : LMSpField) :
    lmJ c k (fun x i => a * f x i) = fun x i => a * lmJ c k f x i := by
  funext x i
  exact lmJs_smul c k a (fun y => f y i) x

end UnforcedLeray.Short.IIIa
