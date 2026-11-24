import UnforcedLeray.Units.B0113
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# B0146, helper: lattice sums of Gaussian-dominated functions

Infrastructure for blueprint unit **B0146** (`eq:st18-t00144`, `paper/main.tex` lines
2196–2216), item `INF27` of the blueprint ("termwise differentiation of lattice sums").

For a function `g : ℝ² → ℝ` with Gaussian decay in the first coordinate,
`|g w| ≤ K e^{-β w₁²}`, the lattice sum `∑ₙ g(q - n c, η)` over `n ∈ ℤ` converges absolutely
for every `c ≠ 0`, and its Cartesian partial derivatives (and its derivative in a width
parameter) are the lattice sums of the derivatives. The decay hypotheses are discharged by a
small closure calculus (`PG`: polynomial growth, `GF`: Gaussian decay), uniform for widths in a
compact interval `[A₁, A₂] ⊂ (0, ∞)`.

The two summability lemmas `quadratic_decay_cocompact` and `summable_quadratic` are copied
(they are private there) from the draft

-/

set_option autoImplicit false

noncomputable section

open Filter Asymptotics Real
open scoped Topology

namespace UnforcedLeray.B0146

open UnforcedLeray.GaussianVortex

/-! ### Gaussian lattice summability -/

/-- Copied from `PeriodizedGaussian.lean` (`quadratic_decay_cocompact`). -/
lemma quadratic_decay_cocompact {a : ℝ} (ha : a < 0) (b s : ℝ) :
    (fun x : ℝ => Real.exp (a * x ^ 2 + b * x)) =o[cocompact ℝ]
      (fun x : ℝ => |x| ^ s) := by
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · refine ((rexp_neg_quadratic_isLittleO_rpow_atTop ha (-b) s).comp_tendsto
      Filter.tendsto_neg_atBot_atTop).congr' (Eventually.of_forall fun x => by simp) ?_
    refine (eventually_lt_atBot 0).mp (Eventually.of_forall fun x hx => ?_)
    simp only [Function.comp_apply, abs_of_neg hx]
  · refine (rexp_neg_quadratic_isLittleO_rpow_atTop ha b s).congr' EventuallyEq.rfl ?_
    refine (eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_)
    simp_rw [abs_of_pos hx]

/-- Copied from `PeriodizedGaussian.lean` (`summable_quadratic`). -/
lemma summable_quadratic {a : ℝ} (ha : a < 0) (b : ℝ) :
    Summable (fun n : ℤ => Real.exp (a * (n : ℝ) ^ 2 + b * n)) := by
  have hO := (quadratic_decay_cocompact ha b (-2)).isBigO
  have h := hO.comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2)) h

/-- `∑ₙ e^{-β (x - n c)²}` converges for `β > 0`, `c ≠ 0`. -/
lemma summable_exp_shift {β c : ℝ} (hβ : 0 < β) (hc : c ≠ 0) (x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(β * (x - n * c) ^ 2))) := by
  have ha : -(β * c ^ 2) < 0 := by
    have := sq_pos_of_ne_zero hc
    have := mul_pos hβ this
    linarith
  have h := (summable_quadratic ha (2 * β * x * c)).mul_left (Real.exp (-(β * x ^ 2)))
  refine h.congr fun n => ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- Moving the base point by less than one costs a fixed factor and half the exponent. -/
lemma exp_shift_local {β x y d : ℝ} (hβ : 0 < β) (hxy : |y - x| < 1) :
    Real.exp (-(β * (y - d) ^ 2)) ≤ Real.exp β * Real.exp (-(β / 2 * (x - d) ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (y - x) ^ 2 ≤ 1 := by
    have := abs_lt.mp hxy
    nlinarith
  have h2 : (x - d) ^ 2 ≤ 2 * (y - d) ^ 2 + 2 := by
    nlinarith [sq_nonneg ((y - d) - (x - y))]
  nlinarith [mul_le_mul_of_nonneg_left h2 hβ.le]

/-! ### Lattice translates and lattice sums -/

/-- The lattice translate `(q, η) ↦ (q - n c, η)`. -/
def shift (c : ℝ) (n : ℤ) (z : Plane) : Plane := (z.1 - n * c, z.2)

/-- The lattice sum `∑ₙ g(q - n c, η)`. -/
def latticeSum (c : ℝ) (g : Plane → ℝ) (z : Plane) : ℝ := ∑' n : ℤ, g (shift c n z)

/-- Gaussian decay in the first coordinate. -/
def XDecay (g : Plane → ℝ) : Prop :=
  ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ ∀ w : Plane, |g w| ≤ K * Real.exp (-(β * w.1 ^ 2))

theorem XDecay.summable_norm {g : Plane → ℝ} (hg : XDecay g) {c : ℝ} (hc : c ≠ 0)
    (z : Plane) : Summable (fun n : ℤ => ‖g (shift c n z)‖) := by
  obtain ⟨K, β, -, hβ, hb⟩ := hg
  refine Summable.of_norm_bounded ((summable_exp_shift hβ hc z.1).mul_left K) fun n => ?_
  rw [norm_norm, Real.norm_eq_abs]
  exact hb _

theorem XDecay.summable {g : Plane → ℝ} (hg : XDecay g) {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    Summable (fun n : ℤ => g (shift c n z)) :=
  (hg.summable_norm hc z).of_norm

theorem XDecay.hasSum {g : Plane → ℝ} (hg : XDecay g) {c : ℝ} (hc : c ≠ 0) (z : Plane) :
    HasSum (fun n : ℤ => g (shift c n z)) (latticeSum c g z) :=
  (hg.summable hc z).hasSum

/-- Termwise `x`-derivative of a lattice sum. -/
theorem hasDerivAt_latticeSum_x {g g' : Plane → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hd : ∀ w : Plane, HasDerivAt (fun t => g (t, w.2)) (g' w) w.1)
    (hg : XDecay g) (hg' : XDecay g') (z : Plane) :
    HasDerivAt (fun t => latticeSum c g (t, z.2)) (latticeSum c g' z) z.1 := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hg'
  have hu : Summable (fun n : ℤ =>
      K * Real.exp β * Real.exp (-(β / 2 * (z.1 - n * c) ^ 2))) :=
    (summable_exp_shift (half_pos hβ) hc z.1).mul_left _
  have hmem : z.1 ∈ Set.Ioo (z.1 - 1) (z.1 + 1) := ⟨by linarith, by linarith⟩
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℤ) (t : ℝ) => g (shift c n (t, z.2)))
    (g' := fun (n : ℤ) (t : ℝ) => g' (shift c n (t, z.2)))
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hd (y - n * c, z.2)).comp_sub_const y (n * c))
    (fun n y hy => ?_) hmem (hg.summable hc (z.1, z.2)) hmem
  · exact h
  · have hy' : |y - z.1| < 1 := abs_sub_lt_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
    rw [Real.norm_eq_abs]
    calc |g' (shift c n (y, z.2))| ≤ K * Real.exp (-(β * (y - n * c) ^ 2)) := hb _
      _ ≤ K * (Real.exp β * Real.exp (-(β / 2 * (z.1 - n * c) ^ 2))) :=
          mul_le_mul_of_nonneg_left (exp_shift_local hβ hy') hK
      _ = K * Real.exp β * Real.exp (-(β / 2 * (z.1 - n * c) ^ 2)) := by ring

/-- Termwise `y`-derivative of a lattice sum. -/
theorem hasDerivAt_latticeSum_y {g g' : Plane → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hd : ∀ w : Plane, HasDerivAt (fun t => g (w.1, t)) (g' w) w.2)
    (hg : XDecay g) (hg' : XDecay g') (z : Plane) :
    HasDerivAt (fun t => latticeSum c g (z.1, t)) (latticeSum c g' z) z.2 := by
  obtain ⟨K, β, -, hβ, hb⟩ := hg'
  have hu : Summable (fun n : ℤ => K * Real.exp (-(β * (z.1 - n * c) ^ 2))) :=
    (summable_exp_shift hβ hc z.1).mul_left _
  have h := hasDerivAt_tsum
    (g := fun (n : ℤ) (t : ℝ) => g (shift c n (z.1, t)))
    (g' := fun (n : ℤ) (t : ℝ) => g' (shift c n (z.1, t)))
    hu (fun n y => hd (z.1 - n * c, y))
    (fun n y => by rw [Real.norm_eq_abs]; exact hb _) (hg.summable hc (z.1, z.2)) z.2
  exact h

theorem partialX_latticeSum {g g' : Plane → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hd : ∀ w : Plane, HasDerivAt (fun t => g (t, w.2)) (g' w) w.1)
    (hg : XDecay g) (hg' : XDecay g') :
    partialX (latticeSum c g) = latticeSum c g' :=
  funext fun z => (hasDerivAt_latticeSum_x hc hd hg hg' z).deriv

theorem partialY_latticeSum {g g' : Plane → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hd : ∀ w : Plane, HasDerivAt (fun t => g (w.1, t)) (g' w) w.2)
    (hg : XDecay g) (hg' : XDecay g') :
    partialY (latticeSum c g) = latticeSum c g' :=
  funext fun z => (hasDerivAt_latticeSum_y hc hd hg hg' z).deriv

/-- Termwise derivative of a lattice sum in a width parameter `b` near `a₀ > 0`. -/
theorem hasDerivAt_latticeSum_width {G G' : ℝ → Plane → ℝ} {c a₀ : ℝ} (hc : c ≠ 0)
    (ha₀ : 0 < a₀)
    (hd : ∀ b : ℝ, 0 < b → ∀ w : Plane, HasDerivAt (fun b' => G b' w) (G' b w) b)
    (hG : XDecay (G a₀))
    (hG' : ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧
      ∀ b ∈ Set.Icc (a₀ / 2) (2 * a₀), ∀ w : Plane, |G' b w| ≤ K * Real.exp (-(β * w.1 ^ 2)))
    (z : Plane) :
    HasDerivAt (fun b => latticeSum c (G b) z) (latticeSum c (G' a₀) z) a₀ := by
  obtain ⟨K, β, -, hβ, hb⟩ := hG'
  have hu : Summable (fun n : ℤ => K * Real.exp (-(β * (z.1 - n * c) ^ 2))) :=
    (summable_exp_shift hβ hc z.1).mul_left _
  have hmem : a₀ ∈ Set.Ioo (a₀ / 2) (2 * a₀) := ⟨by linarith, by linarith⟩
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℤ) (b : ℝ) => G b (shift c n z))
    (g' := fun (n : ℤ) (b : ℝ) => G' b (shift c n z))
    hu isOpen_Ioo isPreconnected_Ioo
    (fun n b hb' => hd b (by linarith [hb'.1]) _)
    (fun n b hb' => by
      rw [Real.norm_eq_abs]
      exact hb b ⟨hb'.1.le, hb'.2.le⟩ _) hmem (hG.summable hc z) hmem
  exact h

/-! ### Polynomial growth and Gaussian decay, uniformly in the width -/

theorem radiusSq_nonneg (w : Plane) : 0 ≤ radiusSq w := by
  unfold radiusSq
  positivity

theorem fst_sq_le_radiusSq (w : Plane) : w.1 ^ 2 ≤ radiusSq w := by
  unfold radiusSq
  nlinarith [sq_nonneg w.2]

theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]

theorem one_add_radiusSq_le {ε : ℝ} (hε : 0 < ε) (w : Plane) :
    1 + radiusSq w ≤ (1 + ε⁻¹) * Real.exp (ε * radiusSq w) := by
  have hR := radiusSq_nonneg w
  have h1 := Real.add_one_le_exp (ε * radiusSq w)
  have h2 : 1 + radiusSq w ≤ (1 + ε⁻¹) * (ε * radiusSq w + 1) := by
    have : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
    nlinarith [mul_nonneg hε.le hR, inv_pos.mpr hε]
  calc 1 + radiusSq w ≤ (1 + ε⁻¹) * (ε * radiusSq w + 1) := h2
    _ ≤ (1 + ε⁻¹) * Real.exp (ε * radiusSq w) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Polynomial growth, uniformly for widths `a ∈ [A₁, A₂]`. -/
def PG (A₁ A₂ : ℝ) (p : ℝ → Plane → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ a ∈ Set.Icc A₁ A₂, ∀ w : Plane,
    |p a w| ≤ M * Real.exp (ε * radiusSq w)

/-- Gaussian decay in the radius, uniformly for widths `a ∈ [A₁, A₂]`. -/
def GF (A₁ A₂ : ℝ) (f : ℝ → Plane → ℝ) : Prop :=
  ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ ∀ a ∈ Set.Icc A₁ A₂, ∀ w : Plane,
    |f a w| ≤ K * Real.exp (-(β * radiusSq w))

section Closure

variable {A₁ A₂ : ℝ}

theorem PG.const (k : ℝ) : PG A₁ A₂ (fun _ _ => k) := by
  intro ε hε
  refine ⟨|k|, fun a _ w => ?_⟩
  exact le_mul_of_one_le_right (abs_nonneg k)
    (Real.one_le_exp (mul_nonneg hε.le (radiusSq_nonneg w)))

theorem PG.inv (hA : 0 < A₁) : PG A₁ A₂ (fun a _ => a⁻¹) := by
  intro ε hε
  refine ⟨A₁⁻¹, fun a ha w => ?_⟩
  have hapos : 0 < a := lt_of_lt_of_le hA ha.1
  rw [abs_of_pos (inv_pos.mpr hapos)]
  calc a⁻¹ ≤ A₁⁻¹ := inv_anti₀ hA ha.1
    _ ≤ A₁⁻¹ * Real.exp (ε * radiusSq w) :=
        le_mul_of_one_le_right (inv_pos.mpr hA).le
          (Real.one_le_exp (mul_nonneg hε.le (radiusSq_nonneg w)))

theorem PG.fst : PG A₁ A₂ (fun _ w => w.1) := by
  intro ε hε
  refine ⟨1 + ε⁻¹, fun a _ w => ?_⟩
  have h1 := abs_le_one_add_sq w.1
  have h2 := fst_sq_le_radiusSq w
  linarith [one_add_radiusSq_le hε w]

theorem PG.snd : PG A₁ A₂ (fun _ w => w.2) := by
  intro ε hε
  refine ⟨1 + ε⁻¹, fun a _ w => ?_⟩
  have h1 := abs_le_one_add_sq w.2
  have h2 : w.2 ^ 2 ≤ radiusSq w := by unfold radiusSq; nlinarith [sq_nonneg w.1]
  linarith [one_add_radiusSq_le hε w]

theorem PG.rsq : PG A₁ A₂ (fun _ w => radiusSq w) := by
  intro ε hε
  refine ⟨1 + ε⁻¹, fun a _ w => ?_⟩
  rw [abs_of_nonneg (radiusSq_nonneg w)]
  linarith [one_add_radiusSq_le hε w]

theorem PG.add {p q : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) (hq : PG A₁ A₂ q) :
    PG A₁ A₂ (fun a w => p a w + q a w) := by
  intro ε hε
  obtain ⟨M₁, h₁⟩ := hp ε hε
  obtain ⟨M₂, h₂⟩ := hq ε hε
  refine ⟨M₁ + M₂, fun a ha w => ?_⟩
  have := h₁ a ha w
  have := h₂ a ha w
  calc |p a w + q a w| ≤ |p a w| + |q a w| := abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem PG.neg {p : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) : PG A₁ A₂ (fun a w => -p a w) := by
  intro ε hε
  obtain ⟨M, h⟩ := hp ε hε
  exact ⟨M, fun a ha w => by rw [abs_neg]; exact h a ha w⟩

theorem PG.sub {p q : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) (hq : PG A₁ A₂ q) :
    PG A₁ A₂ (fun a w => p a w - q a w) := by
  have := hp.add hq.neg
  simpa only [← sub_eq_add_neg] using this

theorem PG.mul {p q : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) (hq : PG A₁ A₂ q) :
    PG A₁ A₂ (fun a w => p a w * q a w) := by
  intro ε hε
  obtain ⟨M₁, h₁⟩ := hp (ε / 2) (half_pos hε)
  obtain ⟨M₂, h₂⟩ := hq (ε / 2) (half_pos hε)
  refine ⟨M₁ * M₂, fun a ha w => ?_⟩
  have e1 := h₁ a ha w
  have e2 := h₂ a ha w
  have hexp : Real.exp (ε / 2 * radiusSq w) * Real.exp (ε / 2 * radiusSq w) =
      Real.exp (ε * radiusSq w) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [abs_mul]
  calc |p a w| * |q a w|
      ≤ (M₁ * Real.exp (ε / 2 * radiusSq w)) * (M₂ * Real.exp (ε / 2 * radiusSq w)) :=
        mul_le_mul e1 e2 (abs_nonneg _) (le_trans (abs_nonneg _) e1)
    _ = M₁ * M₂ * Real.exp (ε * radiusSq w) := by rw [← hexp]; ring

theorem PG.div_const {p : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) (k : ℝ) :
    PG A₁ A₂ (fun a w => p a w / k) := by
  have := hp.mul (PG.const k⁻¹)
  simpa only [← div_eq_mul_inv] using this

theorem PG.pow {p : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) (k : ℕ) :
    PG A₁ A₂ (fun a w => p a w ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using PG.const (A₁ := A₁) (A₂ := A₂) 1
  | succ k ih =>
    have := ih.mul hp
    simpa only [← pow_succ] using this

theorem PG.gw (hA : 0 < A₁) : PG A₁ A₂ (fun a w => B0113.gw a w) := by
  intro ε hε
  refine ⟨1, fun a ha w => ?_⟩
  have hapos : 0 < a := lt_of_lt_of_le hA ha.1
  have h1 : B0113.gw a w ≤ 1 := by
    unfold B0113.gw
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg (inv_pos.mpr hapos).le (radiusSq_nonneg w)
    linarith
  show |B0113.gw a w| ≤ _
  rw [abs_of_pos (by unfold B0113.gw; exact Real.exp_pos _), one_mul]
  exact h1.trans (Real.one_le_exp (mul_nonneg hε.le (radiusSq_nonneg w)))

theorem GF.gw (hA : 0 < A₁) : GF A₁ A₂ (fun a w => B0113.gw a w) := by
  refine ⟨1, (4 * (|A₂| + 1))⁻¹, zero_le_one, by positivity, fun a ha w => ?_⟩
  have hapos : 0 < a := lt_of_lt_of_le hA ha.1
  have hle : a ≤ |A₂| + 1 := le_trans ha.2 (by linarith [le_abs_self A₂])
  have h1 : (4 * (|A₂| + 1))⁻¹ ≤ (4 * a)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h2 : (4 * a)⁻¹ = a⁻¹ / 4 := by field_simp
  have h3 : (4 * (|A₂| + 1))⁻¹ * radiusSq w ≤ a⁻¹ * radiusSq w / 4 := by
    have := mul_le_mul_of_nonneg_right h1 (radiusSq_nonneg w)
    rw [h2] at this
    linarith
  show |B0113.gw a w| ≤ _
  rw [B0113.gw, abs_of_pos (Real.exp_pos _), one_mul]
  apply Real.exp_le_exp.mpr
  linarith

theorem GF.mul_left {p f : ℝ → Plane → ℝ} (hp : PG A₁ A₂ p) (hf : GF A₁ A₂ f) :
    GF A₁ A₂ (fun a w => p a w * f a w) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hf
  obtain ⟨M, hM⟩ := hp (β / 2) (half_pos hβ)
  refine ⟨|M| * K, β / 2, by positivity, half_pos hβ, fun a ha w => ?_⟩
  rw [abs_mul]
  have e1 := hM a ha w
  have e2 := hb a ha w
  have hexp : Real.exp (β / 2 * radiusSq w) * Real.exp (-(β * radiusSq w)) =
      Real.exp (-(β / 2 * radiusSq w)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |p a w| * |f a w|
      ≤ (|M| * Real.exp (β / 2 * radiusSq w)) * (K * Real.exp (-(β * radiusSq w))) :=
        mul_le_mul (e1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le))
          e2 (abs_nonneg _) (by positivity)
    _ = |M| * K * Real.exp (-(β / 2 * radiusSq w)) := by rw [← hexp]; ring

theorem GF.add {f g : ℝ → Plane → ℝ} (hf : GF A₁ A₂ f) (hg : GF A₁ A₂ g) :
    GF A₁ A₂ (fun a w => f a w + g a w) := by
  obtain ⟨K₁, β₁, hK₁, hβ₁, h₁⟩ := hf
  obtain ⟨K₂, β₂, hK₂, hβ₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, min β₁ β₂, by positivity, lt_min hβ₁ hβ₂, fun a ha w => ?_⟩
  have hR := radiusSq_nonneg w
  have m₁ : Real.exp (-(β₁ * radiusSq w)) ≤ Real.exp (-(min β₁ β₂ * radiusSq w)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left β₁ β₂])
  have m₂ : Real.exp (-(β₂ * radiusSq w)) ≤ Real.exp (-(min β₁ β₂ * radiusSq w)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right β₁ β₂])
  have e1 := h₁ a ha w
  have e2 := h₂ a ha w
  calc |f a w + g a w| ≤ |f a w| + |g a w| := abs_add_le _ _
    _ ≤ K₁ * Real.exp (-(β₁ * radiusSq w)) + K₂ * Real.exp (-(β₂ * radiusSq w)) := by linarith
    _ ≤ K₁ * Real.exp (-(min β₁ β₂ * radiusSq w)) + K₂ * Real.exp (-(min β₁ β₂ * radiusSq w)) :=
        add_le_add (mul_le_mul_of_nonneg_left m₁ hK₁) (mul_le_mul_of_nonneg_left m₂ hK₂)
    _ = (K₁ + K₂) * Real.exp (-(min β₁ β₂ * radiusSq w)) := by ring

theorem GF.neg {f : ℝ → Plane → ℝ} (hf : GF A₁ A₂ f) : GF A₁ A₂ (fun a w => -f a w) := by
  obtain ⟨K, β, hK, hβ, h⟩ := hf
  exact ⟨K, β, hK, hβ, fun a ha w => by rw [abs_neg]; exact h a ha w⟩

theorem GF.sub {f g : ℝ → Plane → ℝ} (hf : GF A₁ A₂ f) (hg : GF A₁ A₂ g) :
    GF A₁ A₂ (fun a w => f a w - g a w) := by
  have := hf.add hg.neg
  simpa only [← sub_eq_add_neg] using this

/-- Uniform Gaussian decay in the first coordinate. -/
theorem GF.unif {f : ℝ → Plane → ℝ} (hf : GF A₁ A₂ f) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ ∀ a ∈ Set.Icc A₁ A₂, ∀ w : Plane,
      |f a w| ≤ K * Real.exp (-(β * w.1 ^ 2)) := by
  obtain ⟨K, β, hK, hβ, h⟩ := hf
  refine ⟨K, β, hK, hβ, fun a ha w => (h a ha w).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    nlinarith [fst_sq_le_radiusSq w])) hK

theorem GF.xdecay {f : ℝ → Plane → ℝ} (hf : GF A₁ A₂ f) {a : ℝ} (ha : a ∈ Set.Icc A₁ A₂) :
    XDecay (f a) := by
  obtain ⟨K, β, hK, hβ, h⟩ := hf.unif
  exact ⟨K, β, hK, hβ, h a ha⟩

end Closure

/-- Closure tactic for the decay predicates `PG` and `GF`. -/
macro "decay_tac" : tactic => `(tactic| repeat' (first
  | exact PG.const _
  | exact PG.fst
  | exact PG.snd
  | exact PG.rsq
  | (apply PG.inv; assumption)
  | (apply PG.gw; assumption)
  | (apply GF.gw; assumption)
  | apply PG.pow
  | apply PG.neg
  | apply PG.mul
  | apply PG.add
  | apply PG.sub
  | apply PG.div_const
  | apply GF.neg
  | apply GF.add
  | apply GF.sub
  | apply GF.mul_left))

example {a : ℝ} (ha : 0 < a) :
    GF a a (fun b w => -(b⁻¹ ^ 3 * w.1 * w.2 / 2) * B0113.gw b w *
      (b⁻¹ ^ 2 * (3 / 2 - b⁻¹ * radiusSq w / 4) * B0113.gw b w)) := by
  decay_tac

end UnforcedLeray.B0146
