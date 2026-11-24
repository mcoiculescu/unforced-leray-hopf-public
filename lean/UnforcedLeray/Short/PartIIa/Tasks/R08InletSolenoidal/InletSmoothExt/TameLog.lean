import UnforcedLeray.Short.PartIIa.Sub.R08_2

/-!
# Part II-a, task `PartII-a:R08/2/7`: the logarithmic coordinate is tame (`TameLog`)

Source of record: `the November 2 reference manuscript`. The coordinate
`q = R log(r/R)` is defined at line 1185 and used in the lift at line 1209; the derivative-cost
sentence ("each derivative costs `C/r`", "including smoothness at nonzero axis points") is at
lines 1327-1334.

Target `TameLog` (`Sub/R08_2.lean`): for all `δ M R` with `0 < R`, the function
`y ↦ R * log (ϱ y / R)` is `FlatOn (flatRegion δ M) 0`: it is `C^∞` off the axis and every
iterated derivative is bounded by `C / ϱ^N` on `flatRegion δ M`.

Proof. On the open set `axisᶜ` we have `R log(ϱ/R) = g_R(s)` where `s(y) = y₀² + y₁² = ϱ²` and
`g_R(u) = (R/2) log u - R log R`. Apply Faà di Bruno (`norm_iteratedFDerivWithin_comp_le`) with
inner function `s` (set `axisᶜ`) and outer function `g_R` (set `Ioi 0`):
* outer: the derivatives of `log` are explicit, `iteratedDeriv (k+1) g_R u = (R/2) P_k u^{-(k+1)}`
  with a constant `P_k`; hence for `0 < u ≤ 1` and `i ≤ n`, `‖D^i g_R(u)‖ ≤ A u^{-(n+1)}`;
* inner: `‖D^i s(y)‖` for `1 ≤ i ≤ n` is bounded on the closed ball of radius `B` (compactness of
  the ball and continuity of `D^i s`), which contains `flatRegion δ M` when `B = 1 + |M|`.

This gives `‖D^n F(y)‖ ≤ C ϱ(y)^{-(2n+2)}` for `y` off the axis with `ϱ y < 1`, `‖y‖ ≤ B`.

Helper prefix: `tlg*`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Outer profile `g_R(u) = (R/2) log u - R log R`; off the axis `R log(ϱ/R) = g_R(ϱ²)`. -/
def tlgG (R : ℝ) (u : ℝ) : ℝ := R / 2 * Real.log u - R * Real.log R

/-- Inner quadratic `s(y) = y₀² + y₁²`, which equals `ϱ(y)²`. -/
def tlgS (y : Space) : ℝ := y 0 ^ 2 + y 1 ^ 2

/-- Coefficient of the outer bound: `Σ_{k ≤ n} (|(R/2) ∏_{i<k}(-1-i)| + |R log R|)`. -/
def tlgA (R : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (|R / 2 * (∏ i ∈ Finset.range k, (((-1 : ℤ) : ℝ) - i))| + |R * Real.log R|)

theorem tlgS_contDiff (k : WithTop ℕ∞) : ContDiff ℝ k tlgS := by
  unfold tlgS
  fun_prop

theorem tlgS_eq (y : Space) : tlgS y = Axi.ϱ y ^ 2 := (Axi.ϱ_sq y).symm

theorem tlgS_pos {y : Space} (hy : y ∉ Axi.axis) : 0 < tlgS y := by
  rw [tlgS_eq]
  exact pow_pos (Axi.ϱ_pos hy) 2

theorem tlgS_le_one {y : Space} (hy : Axi.ϱ y < 1) : tlgS y ≤ 1 := by
  rw [tlgS_eq]
  nlinarith [Axi.ϱ_nonneg y]

theorem tlgG_contDiffOn (R : ℝ) : ContDiffOn ℝ ∞ (tlgG R) (Ioi 0) := by
  unfold tlgG
  have hlog : ContDiffOn ℝ ∞ (fun u : ℝ => Real.log u) (Ioi 0) :=
    contDiffOn_id.log (fun u hu => (Set.mem_Ioi.mp hu).ne')
  exact (contDiffOn_const.mul hlog).sub contDiffOn_const

theorem tlgS_contDiffOn : ContDiffOn ℝ ∞ tlgS Axi.axisᶜ :=
  (tlgS_contDiff ∞).contDiffOn

theorem tlgS_mapsTo : MapsTo tlgS Axi.axisᶜ (Ioi 0) :=
  fun _ hy => Set.mem_Ioi.mpr (tlgS_pos hy)

/-! ### Derivatives of the outer profile -/

theorem tlg_deriv_G (R : ℝ) : deriv (tlgG R) = fun v : ℝ => R / 2 * v⁻¹ := by
  unfold tlgG
  rw [deriv_sub_const_fun, deriv_const_mul_field', Real.deriv_log']

theorem tlg_iter_const_mul (c : ℝ) (k : ℕ) :
    ∀ f : ℝ → ℝ, deriv^[k] (fun u => c * f u) = fun u => c * deriv^[k] f u := by
  induction k with
  | zero =>
    intro f
    rfl
  | succ k ih =>
    intro f
    simp only [Function.iterate_succ_apply]
    rw [deriv_const_mul_field', ih]

theorem tlg_iteratedDeriv_G (R : ℝ) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (tlgG R) u =
      R / 2 * ((∏ i ∈ Finset.range k, (((-1 : ℤ) : ℝ) - i)) * u ^ ((-1 : ℤ) - k)) := by
  have hd : deriv (tlgG R) = fun v : ℝ => R / 2 * v ^ (-1 : ℤ) := by
    rw [tlg_deriv_G]
    funext v
    rw [zpow_neg_one]
  have hiter := tlg_iter_const_mul (R / 2) k (fun w : ℝ => w ^ (-1 : ℤ))
  rw [iteratedDeriv_succ', iteratedDeriv_eq_iterate, hd, hiter]
  dsimp only
  rw [iter_deriv_zpow]

theorem tlg_norm_iteratedDeriv_G (R : ℝ) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖iteratedDeriv (k + 1) (tlgG R) u‖ =
      |R / 2 * (∏ i ∈ Finset.range k, (((-1 : ℤ) : ℝ) - i))| * (u ^ (k + 1))⁻¹ := by
  have hz : u ^ ((-1 : ℤ) - k) = (u ^ (k + 1))⁻¹ := by
    rw [show ((-1 : ℤ) - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast]
  rw [tlg_iteratedDeriv_G, Real.norm_eq_abs, hz, ← mul_assoc, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hu _))]

/-! ### The coefficient `tlgA` -/

theorem tlgA_nonneg (R : ℝ) (n : ℕ) : 0 ≤ tlgA R n :=
  Finset.sum_nonneg fun k _ => by positivity

theorem tlgA_ge_term (R : ℝ) {n k : ℕ} (hk : k ≤ n) :
    |R / 2 * (∏ i ∈ Finset.range k, (((-1 : ℤ) : ℝ) - i))| ≤ tlgA R n := by
  unfold tlgA
  have hsingle := Finset.single_le_sum
    (f := fun j : ℕ => |R / 2 * (∏ i ∈ Finset.range j, (((-1 : ℤ) : ℝ) - i))| +
      |R * Real.log R|)
    (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) hsingle

theorem tlgA_zero_le (R : ℝ) (n : ℕ) : |R / 2| + |R * Real.log R| ≤ tlgA R n := by
  unfold tlgA
  have hsingle := Finset.single_le_sum
    (f := fun j : ℕ => |R / 2 * (∏ i ∈ Finset.range j, (((-1 : ℤ) : ℝ) - i))| +
      |R * Real.log R|)
    (fun j _ => by positivity) (Finset.mem_range.2 (Nat.succ_pos n))
  have e : |R / 2| + |R * Real.log R| =
      (fun j : ℕ => |R / 2 * (∏ i ∈ Finset.range j, (((-1 : ℤ) : ℝ) - i))| +
        |R * Real.log R|) 0 := by
    simp
  rw [e]
  exact hsingle

/-! ### Outer bound -/

theorem tlg_outer (R : ℝ) (n : ℕ) :
    ∃ A : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ i : ℕ, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (tlgG R) (Ioi 0) u‖ ≤ A * (u ^ (n + 1))⁻¹ := by
  refine ⟨tlgA R n, fun u hu0 hu1 i hi => ?_⟩
  have hpow : ∀ j : ℕ, j ≤ n + 1 → (u ^ j)⁻¹ ≤ (u ^ (n + 1))⁻¹ := fun j hj =>
    inv_anti₀ (pow_pos hu0 _) (pow_le_pow_of_le_one hu0.le hu1 hj)
  have hX1 : 1 ≤ (u ^ (n + 1))⁻¹ := by
    have h := hpow 0 (Nat.zero_le _)
    simpa using h
  have hXpos : 0 ≤ (u ^ (n + 1))⁻¹ := by positivity
  have hA0 : 0 ≤ tlgA R n := tlgA_nonneg R n
  cases i with
  | zero =>
    rw [norm_iteratedFDerivWithin_zero]
    have hneg : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
    have hlog : |Real.log u| ≤ (u ^ (n + 1))⁻¹ := by
      have h1 : Real.log u⁻¹ ≤ u⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hu0)
      rw [Real.log_inv] at h1
      have h2 : u⁻¹ ≤ (u ^ (n + 1))⁻¹ := by simpa using hpow 1 (by omega)
      rw [abs_of_nonpos hneg]
      linarith
    have hT := tlgA_zero_le R n
    have h3 : |R * Real.log R| ≤ |R * Real.log R| * (u ^ (n + 1))⁻¹ :=
      le_mul_of_one_le_right (abs_nonneg _) hX1
    have h4 : |R / 2| * |Real.log u| ≤ |R / 2| * (u ^ (n + 1))⁻¹ :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    unfold tlgG
    calc ‖R / 2 * Real.log u - R * Real.log R‖
        = |R / 2 * Real.log u - R * Real.log R| := Real.norm_eq_abs _
      _ ≤ |R / 2 * Real.log u| + |R * Real.log R| := abs_sub _ _
      _ = |R / 2| * |Real.log u| + |R * Real.log R| := by rw [abs_mul]
      _ ≤ |R / 2| * (u ^ (n + 1))⁻¹ + |R * Real.log R| * (u ^ (n + 1))⁻¹ :=
          add_le_add h4 h3
      _ = (|R / 2| + |R * Real.log R|) * (u ^ (n + 1))⁻¹ := by ring
      _ ≤ tlgA R n * (u ^ (n + 1))⁻¹ := mul_le_mul_of_nonneg_right hT hXpos
  | succ k =>
    have hk : k ≤ n := by omega
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (k + 1) isOpen_Ioi (Set.mem_Ioi.mpr hu0),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, tlg_norm_iteratedDeriv_G R k hu0]
    exact mul_le_mul (tlgA_ge_term R hk) (hpow (k + 1) (by omega)) (by positivity) hA0

/-! ### Norm localisation: `flatRegion` lies in a ball -/

theorem tlg_norm_le {y : Space} {M : ℝ} (hϱ : Axi.ϱ y < 1) (hyM : |y 2| ≤ M) :
    ‖y‖ ≤ 1 + |M| := by
  have h1 : ‖y‖ ^ 2 = Axi.ϱ y ^ 2 + y 2 ^ 2 := Axi.norm_sq_eq_ϱ_sq_add y
  have hϱ0 := Axi.ϱ_nonneg y
  have hϱ2 : Axi.ϱ y ^ 2 ≤ 1 := by nlinarith
  have hy2 : y 2 ^ 2 ≤ M ^ 2 := by
    have h := sq_abs (y 2)
    nlinarith [abs_nonneg (y 2)]
  have hM : M ^ 2 ≤ |M| ^ 2 := by rw [sq_abs]
  have hsq : ‖y‖ ^ 2 ≤ (1 + |M|) ^ 2 := by nlinarith [abs_nonneg M]
  nlinarith [norm_nonneg y, abs_nonneg M]

/-! ### Faà di Bruno on `axisᶜ` -/

theorem tlg_main (R B : ℝ) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, ∀ y : Space, y ∉ Axi.axis → Axi.ϱ y < 1 → ‖y‖ ≤ B →
      ‖iteratedFDeriv ℝ n (fun z : Space => R * Real.log (Axi.ϱ z / R)) y‖ ≤
        C * (Axi.ϱ y ^ (2 * n + 2))⁻¹ := by
  obtain ⟨A, hA⟩ := tlg_outer R n
  have hcont : Continuous
      (fun x : Space => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j tlgS x‖) := by
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((tlgS_contDiff (j : WithTop ℕ∞)).continuous_iteratedFDeriv').norm
  obtain ⟨K0, hK0⟩ :=
    (isCompact_closedBall (0 : Space) B).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨(Nat.factorial n : ℝ) * A * (1 + |K0|) ^ n, fun y hy hϱ hyB => ?_⟩
  have hu0 : 0 < tlgS y := tlgS_pos hy
  have hu1 : tlgS y ≤ 1 := tlgS_le_one hϱ
  -- inner derivatives, pointwise on the ball
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i tlgS Axi.axisᶜ y‖ ≤ (1 + |K0|) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i Axi.isOpen_compl_axis hy]
    have hsum : ‖iteratedFDeriv ℝ i tlgS y‖ ≤
        ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j tlgS y‖ :=
      Finset.single_le_sum (f := fun j : ℕ => ‖iteratedFDeriv ℝ j tlgS y‖)
        (fun j _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hin))
    have hK : ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j tlgS y‖ ≤ K0 := by
      have h : ‖∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j tlgS y‖‖ ≤ K0 :=
        hK0 y (mem_closedBall_zero_iff.2 hyB)
      rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
    have hK0' : K0 ≤ |K0| := le_abs_self K0
    have hbase : ‖iteratedFDeriv ℝ i tlgS y‖ ≤ 1 + |K0| := by
      linarith [abs_nonneg K0]
    exact le_trans hbase (le_self_pow₀ (by linarith [abs_nonneg K0]) (by omega))
  have hC : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (tlgG R) (Ioi 0) (tlgS y)‖ ≤ A * (tlgS y ^ (n + 1))⁻¹ :=
    fun i hi => hA (tlgS y) hu0 hu1 i hi
  have hFB := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := tlgG R) (f := tlgS) (n := n)
    (s := Axi.axisᶜ) (t := Ioi 0) (x := y) (N := ∞)
    (tlgG_contDiffOn R) tlgS_contDiffOn (by exact_mod_cast le_top)
    isOpen_Ioi.uniqueDiffOn Axi.isOpen_compl_axis.uniqueDiffOn tlgS_mapsTo hy hC hD
  have hEq : Set.EqOn (fun z : Space => R * Real.log (Axi.ϱ z / R)) (tlgG R ∘ tlgS)
      Axi.axisᶜ := by
    intro z hz
    have hz0 : Axi.ϱ z ≠ 0 := Axi.ϱ_ne_zero hz
    simp only [Function.comp_apply, tlgG, tlgS_eq]
    rw [Real.log_pow, Real.log_div hz0 hR.ne']
    push_cast
    ring
  have hXY : (tlgS y ^ (n + 1))⁻¹ = (Axi.ϱ y ^ (2 * n + 2))⁻¹ := by
    rw [tlgS_eq, ← pow_mul, show 2 * (n + 1) = 2 * n + 2 by ring]
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n Axi.isOpen_compl_axis hy,
    iteratedFDerivWithin_congr hEq hy n]
  refine le_trans hFB (le_of_eq ?_)
  rw [hXY]
  ring

/-! ### The theorem -/

theorem tameLog : UnforcedLeray.Short.PartIIa.TameLog := by
  intro δ M R hR
  unfold FlatOn
  refine ⟨?_, fun n => ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun y : Space => Axi.ϱ y / R) Axi.axisᶜ :=
      Axi.contDiffOn_ϱ.div_const R
    have h2 : ContDiffOn ℝ ∞ (fun y : Space => Real.log (Axi.ϱ y / R)) Axi.axisᶜ :=
      h1.log (fun y hy => div_ne_zero (Axi.ϱ_ne_zero hy) hR.ne')
    exact contDiffOn_const.mul h2
  · obtain ⟨C, hC⟩ := tlg_main R (1 + |M|) hR n
    refine ⟨C, 2 * n + 2, fun y hy => ?_⟩
    obtain ⟨hyax, hϱ1, _, hyM⟩ := hy
    have hnorm : ‖y‖ ≤ 1 + |M| := tlg_norm_le hϱ1 hyM
    have h := hC y hyax hϱ1 hnorm
    rw [neg_zero, zero_div, Real.exp_zero, mul_one, div_eq_mul_inv]
    exact h

end UnforcedLeray.Short.PartIIa
