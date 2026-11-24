import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy
import UnforcedLeray.Short.PartIIb.Tasks.CylExistence

/-!
# Small-period (`0 < c ≤ 1`) cylinder energy bound for `PartII-b:T24`

In `FreeCylEnergy` (`Sub/T22.lean`), the energy estimate is proved for `c ≥ 1`.
For `0 < c ≤ 1`, the periodized heat vortex `V_c = Train.Vc ν c σ` on the centered cell
`B0579.cell c` (`|q| ≤ c/2`) satisfies:
* `c * |V_c(x)_0| ≤ C₁(Σ)` (the `O(1/c)` Gaussian lattice sum is multiplied by `c`, matching the
  factor `|∂_q(jb^m)| = 2m|q| jb^{m-1} ≤ m c jb^m` on the cell `|q| ≤ c/2`),
* `|V_c(x)_1| ≤ C₂(Σ)` on `|q| ≤ c/2` (because `u_2` is odd in `q`, so paired images `±n` cancel
  to order `O(|q|) = O(c)`, which cancels the `O(1/c)` lattice sum).

Hence `(v · ∇(jb^m)) ≤ m C(Σ) (δ + 1) jb^m` on `B0579.cell c` for all `0 < c ≤ 1`, and for
`0 < c ≤ 1` the constant `1` is bounded by `e^b e^{-b c²}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-! ## Elementary exponential and geometric-series bounds for `0 < c ≤ 1` -/

/-- `u * exp(-u) ≤ 1` for all `u : ℝ`. -/
private lemma mul_exp_neg_le_one (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h2 : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc u * Real.exp (-u)
      ≤ Real.exp u * Real.exp (-u) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := h2

private lemma exp_neg_sub_le_of_le {r s M : ℝ} (hr : M ≤ r) (hrs : r ≤ s) :
    |Real.exp (-r) - Real.exp (-s)| ≤ |r - s| * Real.exp (-M) := by
  have h1 : Real.exp (-s) ≤ Real.exp (-r) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-r) ≤ Real.exp (-M) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-s) = Real.exp (-r) * Real.exp (-(s - r)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : 1 - Real.exp (-(s - r)) ≤ s - r := by
    linarith [Real.add_one_le_exp (-(s - r))]
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  calc Real.exp (-r) - Real.exp (-s)
      = (1 - Real.exp (-(s - r))) * Real.exp (-r) := by rw [h3]; ring
    _ ≤ (s - r) * Real.exp (-M) :=
        mul_le_mul h4 h2 (Real.exp_pos _).le (by linarith)
    _ = -(r - s) * Real.exp (-M) := by ring

/-- Mean-value bound for `exp(-r) - exp(-s)` when `r, s ≥ M`. -/
private lemma abs_exp_neg_sub_le {r s M : ℝ} (hr : M ≤ r) (hs : M ≤ s) :
    |Real.exp (-r) - Real.exp (-s)| ≤ |r - s| * Real.exp (-M) := by
  rcases le_total r s with h | h
  · exact exp_neg_sub_le_of_le hr h
  · rw [abs_sub_comm (Real.exp (-r)), abs_sub_comm r s]
    exact exp_neg_sub_le_of_le hs h

/-- For `γ > 0` and `0 < c ≤ 1`, the half-lattice Gaussian sum is `O(1/c)`. -/
theorem c_mul_tsum_nat_gauss_le {γ c : ℝ} (hγ : 0 < γ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Summable (fun k : ℕ => Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))) ∧
      c * ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) ≤ Real.exp γ * (1 + γ) / γ := by
  set r : ℝ := Real.exp (-(γ * c))
  have hγc : 0 < γ * c := mul_pos hγ hc0
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hgeom : Summable (fun k : ℕ => Real.exp γ * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp γ)
  have hpt : ∀ k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) ≤ Real.exp γ * r ^ k := by
    intro k
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hu : c * (k : ℝ) - 1 ≤ c ^ 2 * (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (c * (k : ℝ) - 1), mul_nonneg hc0.le hk0]
    have hmul : -(γ * c ^ 2 * (k : ℝ) ^ 2) ≤ γ + (k : ℝ) * (-(γ * c)) := by
      nlinarith [mul_le_mul_of_nonneg_left hu hγ.le]
    calc Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))
        ≤ Real.exp (γ + (k : ℝ) * (-(γ * c))) := Real.exp_le_exp.2 hmul
      _ = Real.exp γ * r ^ k := by
          rw [Real.exp_add, Real.exp_nat_mul]
  have hsum : Summable (fun k : ℕ => Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hpt hgeom
  refine ⟨hsum, ?_⟩
  have htsum : ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) ≤ Real.exp γ * (1 - r)⁻¹ := by
    calc ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))
        ≤ ∑' k : ℕ, Real.exp γ * r ^ k := Summable.tsum_le_tsum hpt hsum hgeom
      _ = Real.exp γ * ∑' k : ℕ, r ^ k := tsum_mul_left
      _ = Real.exp γ * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr0 hr1]
  have h1mr : γ * c / (1 + γ * c) ≤ 1 - r := by
    have hpos : 0 < 1 + γ * c := by linarith
    have hexp : 1 + γ * c ≤ Real.exp (γ * c) := by
      linarith [Real.add_one_le_exp (γ * c)]
    have hrinv : r ≤ (1 + γ * c)⁻¹ := by
      have : r = (Real.exp (γ * c))⁻¹ := by rw [← Real.exp_neg]
      rw [this]
      exact inv_anti₀ hpos hexp
    have hident : 1 - (1 + γ * c)⁻¹ = γ * c / (1 + γ * c) := by
      field_simp
      ring
    linarith
  have hdiv_pos : 0 < γ * c / (1 + γ * c) := div_pos hγc (by linarith)
  have hinv_le : (1 - r)⁻¹ ≤ (1 + γ * c) / (γ * c) := by
    have := inv_anti₀ hdiv_pos h1mr
    rwa [inv_div] at this
  have hc_inv : c * (1 - r)⁻¹ ≤ (1 + γ) / γ := by
    have h1 : c * (1 - r)⁻¹ ≤ c * ((1 + γ * c) / (γ * c)) :=
      mul_le_mul_of_nonneg_left hinv_le hc0.le
    have h2 : c * ((1 + γ * c) / (γ * c)) = (1 + γ * c) / γ := by
      have hc_ne : c ≠ 0 := hc0.ne'
      have hγ_ne : γ ≠ 0 := hγ.ne'
      field_simp
    have h3 : (1 + γ * c) / γ ≤ (1 + γ) / γ := by
      apply div_le_div_of_nonneg_right _ hγ.le
      nlinarith
    linarith
  calc c * ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))
      ≤ c * (Real.exp γ * (1 - r)⁻¹) := mul_le_mul_of_nonneg_left htsum hc0.le
    _ = Real.exp γ * (c * (1 - r)⁻¹) := by ring
    _ ≤ Real.exp γ * ((1 + γ) / γ) := mul_le_mul_of_nonneg_left hc_inv (Real.exp_pos _).le
    _ = Real.exp γ * (1 + γ) / γ := by ring

/-- Full-lattice Gaussian sum bound for `0 < c ≤ 1`. -/
theorem c_mul_tsum_int_gauss_le {γ c : ℝ} (hγ : 0 < γ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    c * ∑' n : ℤ, Real.exp (-((γ * c ^ 2) * (n : ℝ) ^ 2)) ≤
      2 * (Real.exp γ * (1 + γ) / γ) := by
  have hγc2 : 0 < γ * c ^ 2 := by positivity
  let g : ℤ → ℝ := fun n => Real.exp (-((γ * c ^ 2) * (n : ℝ) ^ 2))
  have hg : Summable g := TrainGap.summable_gauss_int hγc2
  have hrel := tsum_nat_add_neg hg
  have h0 : 0 ≤ g 0 := (Real.exp_pos _).le
  have heq : (fun k : ℕ => g k + g (-k)) =
      fun k : ℕ => 2 * Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) := by
    funext k
    dsimp [g]
    push_cast
    have : (-(k : ℝ)) ^ 2 = (k : ℝ) ^ 2 := neg_sq (k : ℝ)
    rw [this]
    ring
  rw [heq, tsum_mul_left] at hrel
  have hle : ∑' n : ℤ, g n ≤
      2 * ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) := by linarith
  have hnat := (c_mul_tsum_nat_gauss_le hγ hc0 hc1).2
  calc c * ∑' n : ℤ, g n
      ≤ c * (2 * ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hle hc0.le
    _ = 2 * (c * ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))) := by ring
    _ ≤ 2 * (Real.exp γ * (1 + γ) / γ) :=
        mul_le_mul_of_nonneg_left hnat (by norm_num)

/-! ## Paired-image bound for `u2` on the cell (`|q| ≤ c/2`, `0 < c ≤ 1`) -/

/-- Paired-image cancellation for `u2` at lattice index `k : ℕ`. -/
private theorem u2_pair_bound {a K c : ℝ} (ha1 : 1 ≤ a) (haK : a ≤ K)
    (hc0 : 0 < c) {x : B0579.Plane} (hx : |x.1| ≤ c / 2) (k : ℕ) :
    |UnforcedLeray.B0146.u2 a (x.1 - (k : ℤ) * c, x.2) +
      UnforcedLeray.B0146.u2 a (x.1 - (-(k : ℤ) : ℤ) * c, x.2)| ≤
      17 * c * Real.exp (-((1 / (32 * K)) * c ^ 2 * (k : ℝ) ^ 2)) := by
  have ha0 : 0 < a := by linarith
  have hK0 : 0 < K := lt_of_lt_of_le ha0 haK
  have hainv2 : a⁻¹ ^ 2 ≤ 1 := by
    have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
    have h0 : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
    nlinarith
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp only [Nat.cast_zero, Int.cast_zero, neg_zero, zero_mul, sub_zero, sq, mul_zero,
      Real.exp_zero, mul_one]
    have hg1 : UnforcedLeray.B0113.gw a x ≤ 1 := by
      calc UnforcedLeray.B0113.gw a x
          ≤ Real.exp (-((x.1 ^ 2 + x.2 ^ 2) / (4 * K))) := TrainGap.gw_le ha1 haK x
        _ ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    have hg0 : 0 < UnforcedLeray.B0113.gw a x := Real.exp_pos _
    have hu2 : |UnforcedLeray.B0146.u2 a x| ≤ c / 2 := by
      unfold UnforcedLeray.B0146.u2
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a⁻¹ ^ 2), abs_of_pos hg0]
      calc a⁻¹ ^ 2 * |x.1| * UnforcedLeray.B0113.gw a x
          ≤ 1 * (c / 2) * 1 :=
            mul_le_mul (mul_le_mul hainv2 hx (abs_nonneg _) zero_le_one) hg1 hg0.le (by linarith)
        _ = c / 2 := by ring
    have h2 : |UnforcedLeray.B0146.u2 a x + UnforcedLeray.B0146.u2 a x| ≤ c := by
      linarith [abs_add_le (UnforcedLeray.B0146.u2 a x) (UnforcedLeray.B0146.u2 a x)]
    linarith
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    set q : ℝ := x.1
    set y : ℝ := (k : ℝ) * c
    have hy_ge_c : c ≤ y := by nlinarith
    have hy0 : 0 ≤ y := by linarith
    have hq_le_y : |q| ≤ y / 2 := by linarith
    have hq_bounds := abs_le.1 hq_le_y
    have hqm : y / 2 ≤ y - q := by linarith
    have hqp : y / 2 ≤ y + q := by linarith
    have hsq_m : y ^ 2 / 4 ≤ (q - y) ^ 2 := by
      have : (y / 2) ^ 2 ≤ (y - q) ^ 2 := by nlinarith
      nlinarith
    have hsq_p : y ^ 2 / 4 ≤ (q + y) ^ 2 := by
      have : (y / 2) ^ 2 ≤ (y + q) ^ 2 := by nlinarith
      nlinarith
    set α : ℝ := (4 * a)⁻¹
    have hα_pos : 0 < α := by positivity
    have hα_lower : 1 / (4 * K) ≤ α := by
      dsimp [α]
      rw [one_div]
      exact inv_anti₀ (by positivity) (by linarith)
    set A : ℝ := a⁻¹ ^ 2 * Real.exp (-(x.2 ^ 2 / (4 * a)))
    have hA0 : 0 ≤ A := by positivity
    have hA1 : A ≤ 1 := by
      have hexp : Real.exp (-(x.2 ^ 2 / (4 * a))) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
      calc A ≤ 1 * 1 := mul_le_mul hainv2 hexp (Real.exp_pos _).le zero_le_one
        _ = 1 := mul_one 1
    have hgw_eq : ∀ z : ℝ, UnforcedLeray.B0113.gw a (z, x.2) =
        Real.exp (-(x.2 ^ 2 / (4 * a))) * Real.exp (-(α * z ^ 2)) := by
      intro z
      unfold UnforcedLeray.B0113.gw UnforcedLeray.GaussianVortex.radiusSq
      rw [← Real.exp_add]
      congr 1
      dsimp [α]
      ring
    have hu2_eq : ∀ z : ℝ, UnforcedLeray.B0146.u2 a (z, x.2) =
        A * z * Real.exp (-(α * z ^ 2)) := by
      intro z
      unfold UnforcedLeray.B0146.u2
      rw [hgw_eq z]
      dsimp [A]
      ring
    have hshift_pos : x.1 - (k : ℤ) * c = q - y := by push_cast; rfl
    have hshift_neg : x.1 - (-(k : ℤ) : ℤ) * c = q + y := by push_cast; ring
    rw [hshift_pos, hshift_neg, hu2_eq (q - y), hu2_eq (q + y)]
    have hsplit : A * (q - y) * Real.exp (-(α * (q - y) ^ 2)) +
        A * (q + y) * Real.exp (-(α * (q + y) ^ 2)) =
        A * (q * (Real.exp (-(α * (q - y) ^ 2)) + Real.exp (-(α * (q + y) ^ 2))) +
          y * (Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2)))) := by ring
    rw [hsplit, abs_mul, abs_of_nonneg hA0]
    have hM_m : α * y ^ 2 / 4 ≤ α * (q - y) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq_m hα_pos.le
      linarith
    have hM_p : α * y ^ 2 / 4 ≤ α * (q + y) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq_p hα_pos.le
      linarith
    have hexp_m : Real.exp (-(α * (q - y) ^ 2)) ≤ Real.exp (-(α * y ^ 2 / 8)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hα_pos.le (sq_nonneg y)])
    have hexp_p : Real.exp (-(α * (q + y) ^ 2)) ≤ Real.exp (-(α * y ^ 2 / 8)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hα_pos.le (sq_nonneg y)])
    have hterm1 : |q * (Real.exp (-(α * (q - y) ^ 2)) + Real.exp (-(α * (q + y) ^ 2)))| ≤
        c * Real.exp (-(α * y ^ 2 / 8)) := by
      rw [abs_mul, abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
      calc |q| * (Real.exp (-(α * (q - y) ^ 2)) + Real.exp (-(α * (q + y) ^ 2)))
          ≤ (c / 2) * (Real.exp (-(α * y ^ 2 / 8)) + Real.exp (-(α * y ^ 2 / 8))) :=
            mul_le_mul hx (add_le_add hexp_m hexp_p) (by positivity) (by linarith)
        _ = c * Real.exp (-(α * y ^ 2 / 8)) := by ring
    have hdiff := abs_exp_neg_sub_le hM_p hM_m
    have hrs_eq : |α * (q + y) ^ 2 - α * (q - y) ^ 2| ≤ 2 * α * c * y := by
      have h1 : α * (q + y) ^ 2 - α * (q - y) ^ 2 = 4 * α * y * q := by ring
      rw [h1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * α * y)]
      nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 4 * α * y)]
    have hterm2 : |y * (Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2)))| ≤
        16 * c * Real.exp (-(α * y ^ 2 / 8)) := by
      rw [abs_mul, abs_of_nonneg hy0]
      have h1 : y * |Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2))| ≤
          2 * α * c * y ^ 2 * Real.exp (-(α * y ^ 2 / 4)) := by
        calc y * |Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2))|
            ≤ y * (|α * (q + y) ^ 2 - α * (q - y) ^ 2| * Real.exp (-(α * y ^ 2 / 4))) :=
              mul_le_mul_of_nonneg_left hdiff hy0
          _ ≤ y * ((2 * α * c * y) * Real.exp (-(α * y ^ 2 / 4))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hrs_eq (Real.exp_pos _).le) hy0
          _ = 2 * α * c * y ^ 2 * Real.exp (-(α * y ^ 2 / 4)) := by ring
      have h2 : Real.exp (-(α * y ^ 2 / 4)) =
          Real.exp (-(α * y ^ 2 / 8)) * Real.exp (-(α * y ^ 2 / 8)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 := mul_exp_neg_le_one (α * y ^ 2 / 8)
      calc y * |Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2))|
          ≤ 2 * α * c * y ^ 2 * Real.exp (-(α * y ^ 2 / 4)) := h1
        _ = 16 * c * ((α * y ^ 2 / 8) * Real.exp (-(α * y ^ 2 / 8))) *
              Real.exp (-(α * y ^ 2 / 8)) := by rw [h2]; ring
        _ ≤ 16 * c * 1 * Real.exp (-(α * y ^ 2 / 8)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 16 * c * Real.exp (-(α * y ^ 2 / 8)) := by ring
    have hrate : Real.exp (-(α * y ^ 2 / 8)) ≤
        Real.exp (-((1 / (32 * K)) * c ^ 2 * (k : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.2
      have hy2 : y ^ 2 = c ^ 2 * (k : ℝ) ^ 2 := by dsimp [y]; ring
      rw [hy2]
      have h4 : 1 / (32 * K) ≤ α / 8 := by
        rw [show (1 : ℝ) / (32 * K) = (1 / (4 * K)) / 8 by ring]
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ c ^ 2 * (k : ℝ) ^ 2)
      linarith
    have hcomb : |q * (Real.exp (-(α * (q - y) ^ 2)) + Real.exp (-(α * (q + y) ^ 2))) +
        y * (Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2)))| ≤
        17 * c * Real.exp (-(α * y ^ 2 / 8)) := by
      have := abs_add_le (q * (Real.exp (-(α * (q - y) ^ 2)) + Real.exp (-(α * (q + y) ^ 2))))
        (y * (Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2))))
      linarith
    calc A * |q * (Real.exp (-(α * (q - y) ^ 2)) + Real.exp (-(α * (q + y) ^ 2))) +
          y * (Real.exp (-(α * (q + y) ^ 2)) - Real.exp (-(α * (q - y) ^ 2)))|
        ≤ 1 * (17 * c * Real.exp (-(α * y ^ 2 / 8))) :=
          mul_le_mul hA1 hcomb (abs_nonneg _) zero_le_one
      _ ≤ 17 * c * Real.exp (-((1 / (32 * K)) * c ^ 2 * (k : ℝ) ^ 2)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hrate (by positivity)

/-- Uniform bound on `c * |Vc_0| + |Vc_1|` on the cell `B0579.cell c` for `0 < c ≤ 1`. -/
theorem vc_cell_small_c {Sg : ℝ} (hSg : 0 < Sg) :
    ∃ C_v : ℝ, 0 < C_v ∧
      ∀ (ν c : ℝ), 0 < ν → 0 < c → c ≤ 1 →
      ∀ σ ∈ Icc (0 : ℝ) (Sg / ν), ∀ x ∈ B0579.cell c,
        c * |UnforcedLeray.Train.Vc ν c σ x 0| + |UnforcedLeray.Train.Vc ν c σ x 1| ≤ C_v := by
  set K : ℝ := 1 + Sg
  have hK : 0 < K := by dsimp [K]; linarith
  set β : ℝ := 1 / (8 * K)
  have hβ : 0 < β := div_pos one_pos (by linarith)
  set γ : ℝ := β / 4
  have hγ : 0 < γ := by dsimp [γ]; linarith
  set B : ℝ := Real.exp γ * (1 + γ) / γ
  have hB : 0 < B := div_pos (mul_pos (Real.exp_pos _) (by linarith)) hγ
  refine ⟨(2 * K + 1) * (2 * B) + (17 * B + (2 * K + 1)), by positivity, ?_⟩
  intro ν c hν hc0 hc1 σ hσ x hx
  have hνσ : ν * σ ≤ Sg := by
    have h1 : ν * (Sg / ν) = Sg := by field_simp
    have h2 : ν * σ ≤ ν * (Sg / ν) := mul_le_mul_of_nonneg_left hσ.2 hν.le
    linarith
  have ha1 : 1 ≤ 1 + ν * σ := by nlinarith [hσ.1, hν]
  have haK : 1 + ν * σ ≤ K := by dsimp [K]; linarith
  -- Bound on c * |Vc_0|
  have hVc0 : c * |UnforcedLeray.Train.Vc ν c σ x 0| ≤ (2 * K + 1) * (2 * B) := by
    rw [vc_fst_lat hν hc0 hσ.1 x]
    have hg : Summable (fun n : ℤ => (2 * K + 1) * Real.exp (-(β * (x.1 - n * c) ^ 2))) :=
      (UnforcedLeray.B0146.summable_exp_shift hβ hc0.ne' x.1).mul_left _
    have h1 : |∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2)| ≤
        (2 * K + 1) * ∑' m : ℤ, Real.exp (-((γ * c ^ 2) * (m : ℝ) ^ 2)) := by
      calc |∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2)|
          ≤ ∑' n : ℤ, (2 * K + 1) * Real.exp (-(β * (x.1 - n * c) ^ 2)) :=
            TrainGap.abs_tsum_le' hg (fun n => TrainGap.abs_u1_le ha1 haK (x.1 - n * c, x.2))
        _ = (2 * K + 1) * ∑' n : ℤ, Real.exp (-(β * (x.1 - n * c) ^ 2)) := tsum_mul_left
        _ ≤ (2 * K + 1) * ∑' m : ℤ, Real.exp (-((β * c ^ 2 / 4) * (m : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (lat_gen hβ hc0 x.1) (by linarith)
        _ = (2 * K + 1) * ∑' m : ℤ, Real.exp (-((γ * c ^ 2) * (m : ℝ) ^ 2)) := by
            dsimp [γ]; ring_nf
    calc c * |∑' n : ℤ, UnforcedLeray.B0146.u1 (1 + ν * σ) (x.1 - n * c, x.2)|
        ≤ c * ((2 * K + 1) * ∑' m : ℤ, Real.exp (-((γ * c ^ 2) * (m : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 hc0.le
      _ = (2 * K + 1) * (c * ∑' m : ℤ, Real.exp (-((γ * c ^ 2) * (m : ℝ) ^ 2))) := by ring
      _ ≤ (2 * K + 1) * (2 * B) :=
          mul_le_mul_of_nonneg_left (c_mul_tsum_int_gauss_le hγ hc0 hc1) (by linarith)
  -- Bound on |Vc_1| on the cell
  have hx' : x.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.mp hx).1
  have hx1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx'.1, hx'.2.le⟩
  have hVc1 : |UnforcedLeray.Train.Vc ν c σ x 1| ≤ 17 * B + (2 * K + 1) := by
    rw [vc_snd_lat hν hc0 hσ.1 x]
    let f : ℤ → ℝ := fun n => UnforcedLeray.B0146.u2 (1 + ν * σ) (x.1 - n * c, x.2)
    have hf : Summable f :=
      TrainGap.summable_of_gauss_bound hβ hc0.ne'
        (fun n => TrainGap.abs_u2_le ha1 haK (x.1 - n * c, x.2))
    have hrel := tsum_nat_add_neg hf
    have htsum_eq : ∑' n : ℤ, f n = (∑' k : ℕ, (f k + f (-k))) - f 0 := by linarith
    have hf0 : |f 0| ≤ 2 * K + 1 := by
      have h := TrainGap.abs_u2_le ha1 haK (x.1 - (0 : ℤ) * c, x.2)
      have hexp1 : Real.exp (-((1 / (8 * K)) * (x.1 - (0 : ℤ) * c) ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (x.1 - (0 : ℤ) * c)])
      calc |f 0| ≤ (2 * K + 1) * Real.exp (-((1 / (8 * K)) * (x.1 - (0 : ℤ) * c) ^ 2)) := h
        _ ≤ (2 * K + 1) * 1 := mul_le_mul_of_nonneg_left hexp1 (by linarith)
        _ = 2 * K + 1 := mul_one _
    obtain ⟨hsum_nat, hnat_le⟩ := c_mul_tsum_nat_gauss_le hγ hc0 hc1
    have hγ_eq : 1 / (32 * K) = γ := by dsimp [γ, β]; ring
    have hpair : ∀ k : ℕ, ‖f k + f (-k)‖ ≤
        (17 * c) * Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) := by
      intro k
      rw [Real.norm_eq_abs, ← hγ_eq]
      exact u2_pair_bound ha1 haK hc0 hx1 k
    have hsum_maj : Summable (fun k : ℕ => (17 * c) * Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))) :=
      hsum_nat.mul_left (17 * c)
    have hsum_pair : Summable (fun k : ℕ => ‖f k + f (-k)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpair hsum_maj
    have hpair_tsum : |∑' k : ℕ, (f k + f (-k))| ≤ 17 * B := by
      calc |∑' k : ℕ, (f k + f (-k))|
          = ‖∑' k : ℕ, (f k + f (-k))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' k : ℕ, ‖f k + f (-k)‖ := norm_tsum_le_tsum_norm hsum_pair
        _ ≤ ∑' k : ℕ, (17 * c) * Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2)) :=
            Summable.tsum_le_tsum hpair hsum_pair hsum_maj
        _ = 17 * (c * ∑' k : ℕ, Real.exp (-(γ * c ^ 2 * (k : ℝ) ^ 2))) := by
            rw [tsum_mul_left]; ring
        _ ≤ 17 * B := mul_le_mul_of_nonneg_left hnat_le (by norm_num)
    change |∑' n : ℤ, f n| ≤ 17 * B + (2 * K + 1)
    rw [htsum_eq]
    linarith [abs_sub (∑' k : ℕ, (f k + f (-k))) (f 0)]
  linarith

/-! ## Cell weight derivative and dissipation for `0 < c ≤ 1` -/

/-- On `B0579.cell c`, `|∂_0 (jb^m) x| ≤ m * c * jb x ^ m`. -/
private theorem pd_zero_jb_cell_le {c m : ℝ} (hc0 : 0 < c) (hm : 0 ≤ m)
    {x : B0579.Plane} (hx : x ∈ B0579.cell c) :
    |B0579.pd 0 (fun y => B0579.jb y ^ m) x| ≤ m * c * B0579.jb x ^ m := by
  have hx' : x.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.mp hx).1
  have hx1 : |x.1| ≤ c / 2 := abs_le.2 ⟨hx'.1, hx'.2.le⟩
  have h2x1 : |2 * x.1| ≤ c := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hj : 0 < B0579.jb x := B0579.jb_pos x
  have hj1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hJ : 0 ≤ B0579.jb x ^ (m - 1) := Real.rpow_nonneg hj.le _
  have hpow : B0579.jb x ^ m = B0579.jb x ^ (m - 1) * B0579.jb x := by
    rw [← Real.rpow_add_one hj.ne']
    ring_nf
  have hJ_le : B0579.jb x ^ (m - 1) ≤ B0579.jb x ^ m := by
    rw [hpow]
    exact le_mul_of_one_le_right hJ hj1
  rw [B0579.pd_zero_jb_rpow,
    show 2 * x.1 * m * B0579.jb x ^ (m - 1) = (2 * x.1) * (m * B0579.jb x ^ (m - 1)) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hm hJ)]
  calc |2 * x.1| * (m * B0579.jb x ^ (m - 1))
      ≤ c * (m * B0579.jb x ^ m) :=
        mul_le_mul h2x1 (mul_le_mul_of_nonneg_left hJ_le hm) (mul_nonneg hm hJ) hc0.le
    _ = m * c * B0579.jb x ^ m := by ring

/-- Smooth-datum `X_{m,c}` energy bound for `0 < p.c ≤ 1` under `IsBUCTrain` and `TrainClose`. -/
theorem small_c_energy_bound {m Sg : ℝ} (hm : 8 < m) (hSg : 0 < Sg) :
    ∃ (Cm_s C_s : ℝ), 0 < Cm_s ∧ 0 < C_s ∧
      ∀ (p : Params), p.c ≤ 1 → UnforcedLeray.Short.PartI.IsBUCTrain p.train →
      ∀ δ : ℝ, 0 ≤ δ → TrainClose p.train Sg δ →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / p.ν →
      ∀ f : B0579.Plane → ℝ, B0579.IsCylTest p.c f →
      ∀ ω : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω →
        eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≤
          ENNReal.ofReal (Real.exp ((Cm_s * p.ν + C_s * δ + C_s) * (t - s))) *
            eLpNorm f 2 (B0579.cellMeasure p.c m) := by
  have hm0 : 0 < m := by linarith
  obtain ⟨Cd, hCd⟩ := cylDiffusionBound m hm0
  obtain ⟨Cv, hCv_pos, hCv⟩ := vc_cell_small_c hSg
  set Cm_s : ℝ := |Cd| + 1
  set C_s : ℝ := m * (Cv + 2)
  have hCm_pos : 0 < Cm_s := by positivity
  have hCs_pos : 0 < C_s := mul_pos hm0 (by linarith)
  refine ⟨Cm_s, C_s, hCm_pos, hCs_pos, ?_⟩
  intro p hc1 hbu δ hδ hclose s t hs hst htT f hf ω hω
  have hν : 0 < p.ν := p.ν_pos
  have hc0 : 0 < p.c := p.c_pos
  have hsT : s ≤ Sg / p.ν := hst.trans htT
  obtain ⟨ω', hreg, hω's⟩ := cylRegularExists_of_buc hν hc0 hbu hs hsT hf
  have hae := cylWeakEqClassical m hm Sg hSg p.ν p.c δ hν hc0 hδ p.train hclose s hs f hf
    ω' hreg hω's ω hω
  have hEeq : ∀ σ ∈ Icc s (Sg / p.ν), cylEnergy p.c m (ω σ) = cylEnergy p.c m (ω' σ) :=
    fun σ hσ => (t22_energy_congr (hae σ hσ)).symm
  obtain ⟨M, hM⟩ := cylTrainBound Sg p.ν p.c δ hSg hν hc0 hδ p.train hclose
  have hMbdd : ∀ σ ∈ Icc s (Sg / p.ν), ∀ x : B0579.Plane,
      |p.train.v σ x 0| + |p.train.v σ x 1| ≤ M :=
    fun σ hσ x => hM σ (hs.trans hσ.1) hσ.2 x
  obtain ⟨hcont, hderiv⟩ := regularEnergyDeriv p.c p.ν m s (Sg / p.ν) p.train.v ω' hc0 hreg
    ⟨M, hMbdd⟩
  set K : ℝ := Cm_s * p.ν + C_s * δ + C_s
  have hdiss : ∀ τ ∈ Ico s (Sg / p.ν),
      2 * ∫ x in B0579.cell p.c, ω' τ x * (p.ν * lapP (ω' τ) x -
          (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
            (B0579.density m x : ℝ)
        ≤ 2 * K * cylEnergy p.c m (ω' τ) := by
    intro τ hτ
    have hτI : τ ∈ Icc s (Sg / p.ν) := ⟨hτ.1, hτ.2.le⟩
    have hτ0 : τ ∈ Icc (0 : ℝ) (Sg / p.ν) := ⟨hs.trans hτ.1, hτ.2.le⟩
    have hsd := hreg.slice τ hτI
    obtain ⟨hE, hI1, hD⟩ := hCd p.c hc0 (ω' τ) hsd
    obtain ⟨hT1, hT2, hT⟩ := cylTransportIBP p.ν p.c p.train τ hτ0.1 hc0
      ⟨M, hMbdd τ hτI⟩ m (ω' τ) hsd
    have hsplit : (∫ x in B0579.cell p.c, ω' τ x * (p.ν * lapP (ω' τ) x -
          (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
            (B0579.density m x : ℝ))
        = p.ν * (∫ x in B0579.cell p.c, ω' τ x * lapP (ω' τ) x * (B0579.density m x : ℝ))
          - (∫ x in B0579.cell p.c, ω' τ x * (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x +
              p.train.v τ x 1 * B0579.pd 1 (ω' τ) x) * (B0579.density m x : ℝ)) := by
      have h1 : (fun x => ω' τ x * (p.ν * lapP (ω' τ) x -
          (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
            (B0579.density m x : ℝ))
          = fun x => p.ν * (ω' τ x * lapP (ω' τ) x * (B0579.density m x : ℝ)) -
            ω' τ x * (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x +
              p.train.v τ x 1 * B0579.pd 1 (ω' τ) x) * (B0579.density m x : ℝ) := by
        funext x; ring
      rw [h1, integral_sub (hI1.const_mul p.ν) hT1, integral_const_mul]
    have hJ : (∫ x in B0579.cell p.c, ω' τ x ^ 2 *
        (p.train.v τ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
          p.train.v τ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x))
        ≤ (C_s * δ + C_s) * cylEnergy p.c m (ω' τ) := by
      have hint : IntegrableOn
          (fun x => (C_s * δ + C_s) * (ω' τ x ^ 2 * (B0579.density m x : ℝ)))
          (B0579.cell p.c) := hE.const_mul (C_s * δ + C_s)
      have hle : (∫ x in B0579.cell p.c, ω' τ x ^ 2 *
          (p.train.v τ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
            p.train.v τ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x))
          ≤ ∫ x in B0579.cell p.c,
              (C_s * δ + C_s) * (ω' τ x ^ 2 * (B0579.density m x : ℝ)) := by
        refine setIntegral_mono_on hT2 hint (B0579.measurableSet_cell p.c) fun x hx => ?_
        have hpd0 := pd_zero_jb_cell_le hc0 hm0.le hx
        have hpd1 := (t22_pd_jb_le hm0.le x).2
        have hd : (B0579.density m x : ℝ) = B0579.jb x ^ m := B0579.coe_density m x
        have hW : 0 ≤ B0579.jb x ^ m := Real.rpow_nonneg (B0579.jb_pos x).le _
        have hcl := hclose.norm_sub_le hc0 hτ0.1 hτ0.2 x
        have hc0_diff : |p.train.v τ x 0 - UnforcedLeray.Train.Vc p.ν p.c τ x 0| ≤ δ := by
          have h1 := PiLp.norm_apply_le (p.train.v τ x - UnforcedLeray.Train.Vc p.ν p.c τ x) 0
          rw [PiLp.sub_apply, Real.norm_eq_abs] at h1
          exact h1.trans hcl
        have hc1_diff : |p.train.v τ x 1 - UnforcedLeray.Train.Vc p.ν p.c τ x 1| ≤ δ := by
          have h1 := PiLp.norm_apply_le (p.train.v τ x - UnforcedLeray.Train.Vc p.ν p.c τ x) 1
          rw [PiLp.sub_apply, Real.norm_eq_abs] at h1
          exact h1.trans hcl
        have hv0 : |p.train.v τ x 0| ≤ δ + |UnforcedLeray.Train.Vc p.ν p.c τ x 0| := by
          linarith [abs_sub_abs_le_abs_sub (p.train.v τ x 0)
            (UnforcedLeray.Train.Vc p.ν p.c τ x 0)]
        have hv1 : |p.train.v τ x 1| ≤ δ + |UnforcedLeray.Train.Vc p.ν p.c τ x 1| := by
          linarith [abs_sub_abs_le_abs_sub (p.train.v τ x 1)
            (UnforcedLeray.Train.Vc p.ν p.c τ x 1)]
        have hvc := hCv p.ν p.c hν hc0 hc1 τ hτ0 x hx
        have hcv_tot : p.c * |p.train.v τ x 0| + |p.train.v τ x 1| ≤ 2 * δ + Cv := by
          have hp0 : p.c * |p.train.v τ x 0| ≤
              p.c * δ + p.c * |UnforcedLeray.Train.Vc p.ν p.c τ x 0| := by
            nlinarith [mul_le_mul_of_nonneg_left hv0 hc0.le]
          have hpδ : p.c * δ ≤ δ := by nlinarith
          linarith
        have ht0 : p.train.v τ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x ≤
            |p.train.v τ x 0| * (m * p.c * B0579.jb x ^ m) :=
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hpd0 (abs_nonneg _))
        have ht1 : p.train.v τ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x ≤
            |p.train.v τ x 1| * (m * B0579.jb x ^ m) :=
          (le_abs_self _).trans (by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hpd1 (abs_nonneg _))
        have hsum_v : p.train.v τ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
            p.train.v τ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x ≤
            (C_s * δ + C_s) * B0579.jb x ^ m := by
          have hmW : 0 ≤ m * B0579.jb x ^ m := mul_nonneg hm0.le hW
          have h1 : (p.c * |p.train.v τ x 0| + |p.train.v τ x 1|) * (m * B0579.jb x ^ m) ≤
              (2 * δ + Cv) * (m * B0579.jb x ^ m) :=
            mul_le_mul_of_nonneg_right hcv_tot hmW
          have h2 : (2 * δ + Cv) * m ≤ C_s * δ + C_s := by
            dsimp [C_s]
            nlinarith [mul_nonneg hm0.le (mul_nonneg hCv_pos.le hδ)]
          have h3 : (2 * δ + Cv) * (m * B0579.jb x ^ m) ≤ (C_s * δ + C_s) * B0579.jb x ^ m := by
            calc (2 * δ + Cv) * (m * B0579.jb x ^ m)
                = ((2 * δ + Cv) * m) * B0579.jb x ^ m := by ring
              _ ≤ (C_s * δ + C_s) * B0579.jb x ^ m := mul_le_mul_of_nonneg_right h2 hW
          linarith
        rw [hd]
        calc ω' τ x ^ 2 * (p.train.v τ x 0 * B0579.pd 0 (fun y => B0579.jb y ^ m) x +
              p.train.v τ x 1 * B0579.pd 1 (fun y => B0579.jb y ^ m) x)
            ≤ ω' τ x ^ 2 * ((C_s * δ + C_s) * B0579.jb x ^ m) :=
              mul_le_mul_of_nonneg_left hsum_v (sq_nonneg _)
          _ = (C_s * δ + C_s) * (ω' τ x ^ 2 * B0579.jb x ^ m) := by ring
      refine hle.trans (le_of_eq ?_)
      rw [integral_const_mul]
      rfl
    have hνD : p.ν * (2 * ∫ x in B0579.cell p.c, ω' τ x * lapP (ω' τ) x *
        (B0579.density m x : ℝ)) ≤ p.ν * (Cd * cylEnergy p.c m (ω' τ)) :=
      mul_le_mul_of_nonneg_left hD hν.le
    have hEnn := t22_energy_nonneg p.c m (ω' τ)
    have hK_le : (Cd * p.ν + C_s * δ + C_s) * cylEnergy p.c m (ω' τ) ≤
        2 * K * cylEnergy p.c m (ω' τ) := by
      apply mul_le_mul_of_nonneg_right _ hEnn
      dsimp [K, Cm_s]
      nlinarith [le_abs_self Cd, abs_nonneg Cd, hν, mul_nonneg hCs_pos.le hδ, hCs_pos]
    rw [hsplit]
    linarith [hνD, hJ, hT, hK_le]
  have hrate' : CylEnergyRate p.c m K (Ico s t) ω' :=
    ⟨fun τ => 2 * ∫ x in B0579.cell p.c, ω' τ x * (p.ν * lapP (ω' τ) x -
        (p.train.v τ x 0 * B0579.pd 0 (ω' τ) x + p.train.v τ x 1 * B0579.pd 1 (ω' τ) x)) *
          (B0579.density m x : ℝ),
      fun τ hτ => ⟨hderiv τ ⟨hτ.1, lt_of_lt_of_le hτ.2 htT⟩,
        hdiss τ ⟨hτ.1, lt_of_lt_of_le hτ.2 htT⟩⟩⟩
  have hgr := cyl_gronwall_of_rate (hcont.mono (Icc_subset_Icc le_rfl htT)) hrate' hst
  have htI : t ∈ Icc s (Sg / p.ν) := ⟨hst, htT⟩
  have hsI : s ∈ Icc s (Sg / p.ν) := ⟨le_rfl, hsT⟩
  have hωt : MemLp (ω t) 2 (B0579.cellMeasure p.c m) := hω.memX t hst
  have hfm : MemLp f 2 (B0579.cellMeasure p.c m) := hf.memLp m
  have hEs : cylEnergy p.c m (ω s) = cylEnergy p.c m f := t22_energy_congr hω.initial
  have hsq : (eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)).toReal ^ 2 ≤
      Real.exp (2 * K * (t - s)) * (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal ^ 2 := by
    rw [t22_energy_eq_sq_eLpNorm hωt, t22_energy_eq_sq_eLpNorm hfm, hEeq t htI, ← hEs, hEeq s hsI]
    exact hgr
  have hexp2 : Real.exp (2 * K * (t - s)) = Real.exp (K * (t - s)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hreal : (eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)).toReal ≤
      Real.exp (K * (t - s)) * (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal := by
    have hnn : 0 ≤ Real.exp (K * (t - s)) * (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal :=
      mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
    refine (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg hnn two_ne_zero).1 ?_
    rw [mul_pow, ← hexp2]
    exact hsq
  calc eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)
      = ENNReal.ofReal (eLpNorm (ω t) 2 (B0579.cellMeasure p.c m)).toReal :=
        (ENNReal.ofReal_toReal hωt.eLpNorm_lt_top.ne).symm
    _ ≤ ENNReal.ofReal (Real.exp (K * (t - s)) *
          (eLpNorm f 2 (B0579.cellMeasure p.c m)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (K * (t - s))) * eLpNorm f 2 (B0579.cellMeasure p.c m) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hfm.eLpNorm_lt_top.ne]

end UnforcedLeray.Short.IIb

end
