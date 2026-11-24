import UnforcedLeray.Short.PartI.Sub.PartI_T21

/-!
# `PartI:T21/2` (`Sub/PartI_T21_2.lean`): decomposition of `TrainWeightedJetBounds`

Source of record: `the November 2 reference manuscript`, lines 513-526
(old 508-515), in the proof of Lemma `sct:heat`.

This module develops the polynomial-weight absorption machinery and leaf propositions for
`PartI:T21/2` (`TrainWeightedJetBounds`):
1. **Exponential-polynomial absorption inequalities** (`PartI_T21.pow_mul_exp_neg_le`,
   `PartI_T21.one_add_pow_two_mul_exp_sq_le`, `PartI_T21.one_add_pow_two_mul_exp_lin_le`):
   using `Real.pow_div_factorial_le_exp`, any polynomial transverse weight `(1 + d²)^m` is
   absorbed into either a Gaussian tail `exp(-b d² / (C₀ + ν s))` (at polynomial cost in
   `1 + s`) or a cylinder exponential tail `exp(-b l / c)` (at polynomial cost in `c`).
2. **Unconditional global weighted `L^∞` and `L²` bounds for vorticity `ω = ∇ × v`**
   (`PartI_T21.wSupNorm_vorticity_of_gaussianTail`):
   proves the `ω` clause of `TrainWeightedJetBounds` unconditionally on all of `ℝ²` from
   `TrainVorticityGaussianTail` (`PartI:T20`).
3. **Unconditional exterior-strip weighted jet bounds for `(ψ, v, p)`**
   (`PartI_T21.exterior_weighted_jet_of_transverseTail`):
   proves that on the exterior region `|z.2| ≥ C'/ν + 2`, the weighted jet norms
   `√(jap m z) ‖ageJet ℓ j F s z‖` for `F ∈ {tr.ψ, tr.v, tr.p}` are bounded by
   `polyPS C_ext (N + 4m) ν c s` unconditionally from `TrainStreamVelocityPressureTransverseTail`
   (`PartI:T21/1`).
4. **Reduction of `TrainWeightedJetBounds` to the two leaf obligations**:
   * `TrainInteriorStripJetBounds` (`PartI:T21/2/1`, source lines 499-526): unweighted
     `polyPS` bounds for `ageJet ℓ j` of `(tr.ψ, tr.v, tr.p)` on any interior strip
     `|z.2| ≤ C'/ν + 2`;
   * `TrainFluctJetWSupNormLe` (`PartI:T21/2/2`, source lines 499-526): `wSupNorm m`
     stability of the horizontal fluctuation operators `ψ ↦ ψ - hmean c ψ` and `v ↦ hfluct c v`
     under `ageJet ℓ j`;
   and conditional assembly `trainWeightedJetBounds_of_interior_and_fluct` (composed by
   `PartI:T21/2` in `Short/PartI/Sub/PartI_T21/WeightedJetBounds.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap)

/-! ### 1. Leaf obligations for `PartI:T21/2` (source lines 499-526) -/

/-- **Leaf 2a (`TrainInteriorStripJetBounds`, `PartI:T21/2/1`, source lines 499-526)**:
unweighted polynomial-in-`(c, ν⁻¹, 1 + s)` bounds for `ageJet ℓ j` of `(tr.ψ, tr.v, tr.p)` on any
interior strip `|z.2| ≤ C' / ν + 2` (obtained by combining the boundary values at
`|z.2| = C' / ν + 2` from `hTail` at `l = 0` with the interior pre/post-overlap regularity from
`TrainComparison` + `Vc_bounds`, `TrainOverlap`, and `TrainVorticityGaussianTail`). -/
def TrainInteriorStripJetBounds : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∀ C' : ℝ, 0 < C' →
    ∃ C_int : ℝ, ∃ N_int : ℕ, ∃ ν₀ : ℝ, 0 < C_int ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, |z.2| ≤ C' / ν + 2 →
            let c := trainPeriod ρ ν
            let K := polyPS C_int N_int ν c s
            ‖ageJet ℓ j tr.ψ s z‖ ≤ K ∧
            ‖ageJet ℓ j tr.v s z‖ ≤ K ∧
            ‖ageJet ℓ j tr.p s z‖ ≤ K

/-- **Leaf 2b (`TrainFluctJetWSupNormLe`, `PartI:T21/2/2`, source lines 499-526)**:
the horizontal-fluctuation operators `ψ ↦ ψ - hmean c ψ` and `v ↦ hfluct c v` commute with
`ageJet ℓ j` and have `wSupNorm m` bounded by `4 * wSupNorm m` of the full field (since `hmean c`
averages in `z.1` at fixed `z.2`, preserving the transverse weight `jap m z = (1 + z.2²)^m`). -/
def TrainFluctJetWSupNormLe : Prop :=
  ∀ {ν c : ℝ}, 0 < ν → 0 < c → ∀ (tr : B0140.TrainSol ν c), IsBUCTrain tr →
    ∀ (m ℓ j : ℕ) {s B : ℝ}, 0 < s → 0 ≤ B →
      (wSupNorm m (ageJet ℓ j tr.ψ s) ≤ ENNReal.ofReal B →
        wSupNorm m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤
          ENNReal.ofReal (4 * B)) ∧
      (wSupNorm m (ageJet ℓ j tr.v s) ≤ ENNReal.ofReal B →
        wSupNorm m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤
          ENNReal.ofReal (4 * B))

namespace PartI_T21

abbrev TrainInteriorStripJetBounds : Prop :=
  UnforcedLeray.Short.PartI.TrainInteriorStripJetBounds

abbrev TrainFluctJetWSupNormLe : Prop :=
  UnforcedLeray.Short.PartI.TrainFluctJetWSupNormLe

/-! ### 2. Exponential-polynomial absorption lemmas -/

/-- For `x ≥ 0` and `m : ℕ`, `x^m * exp(-x) ≤ m!`. -/
theorem pow_mul_exp_neg_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m * Real.exp (-x) ≤ (m.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp x hx m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  rw [div_le_iff₀ hf] at h
  calc x ^ m * Real.exp (-x)
      ≤ (Real.exp x * (m.factorial : ℝ)) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = (m.factorial : ℝ) * (Real.exp x * Real.exp (-x)) := by ring
    _ = (m.factorial : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Since `1 ≤ jap m z`, `√(jap m z) ≤ jap m z`. -/
theorem sqrt_jap_le_jap (m : ℕ) (z : Plane) :
    Real.sqrt (jap m z) ≤ jap m z := by
  have h1 : 1 ≤ jap m z := by
    unfold jap
    exact one_le_pow₀ (by nlinarith [sq_nonneg z.2])
  exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩

/-- If `|z.2| ≤ R + d` with `R, d ≥ 0`, then `1 + z.2² ≤ 2 (1 + R²) (1 + d²)`. -/
theorem one_add_sq_le_of_abs_le_add {R d : ℝ} (_hR : 0 ≤ R) (_hd : 0 ≤ d) (z : Plane)
    (hz : |z.2| ≤ R + d) :
    1 + z.2 ^ 2 ≤ 2 * (1 + R ^ 2) * (1 + d ^ 2) := by
  have hsq : z.2 ^ 2 ≤ (R + d) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg z.2) hz 2
  have hRd : (R + d) ^ 2 ≤ 2 * R ^ 2 + 2 * d ^ 2 := by
    nlinarith [sq_nonneg (R - d)]
  nlinarith [sq_nonneg R, sq_nonneg d, mul_nonneg (sq_nonneg R) (sq_nonneg d)]

/-- If `|z.2| ≤ R + d` with `R, d ≥ 0`, then
`jap m z ≤ (2 * (1 + R²))^m * (1 + d²)^m`. -/
theorem jap_le_of_abs_le_add {R d : ℝ} (hR : 0 ≤ R) (hd : 0 ≤ d) (m : ℕ) (z : Plane)
    (hz : |z.2| ≤ R + d) :
    jap m z ≤ (2 * (1 + R ^ 2)) ^ m * (1 + d ^ 2) ^ m := by
  unfold jap
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_sq_le_of_abs_le_add hR hd z hz) m

/-- For `d ≥ 0` and `m : ℕ`, `(1 + d²)^m ≤ 2^m * (1 + d^(2m))`. -/
theorem one_add_sq_pow_le (m : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    (1 + d ^ 2) ^ m ≤ 2 ^ m * (1 + d ^ (2 * m)) := by
  by_cases hd1 : d ≤ 1
  · have hd2 : d ^ 2 ≤ 1 := by nlinarith
    have hle : 1 + d ^ 2 ≤ 2 := by linarith
    calc (1 + d ^ 2) ^ m
        ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) hle m
      _ ≤ 2 ^ m * (1 + d ^ (2 * m)) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hd (2 * m)])
  · have hd1' : 1 < d := not_le.mp hd1
    have hd2 : 1 ≤ d ^ 2 := by nlinarith
    have hle : 1 + d ^ 2 ≤ 2 * d ^ 2 := by linarith
    calc (1 + d ^ 2) ^ m
        ≤ (2 * d ^ 2) ^ m := pow_le_pow_left₀ (by positivity) hle m
      _ = 2 ^ m * d ^ (2 * m) := by rw [mul_pow, ← pow_mul]
      _ ≤ 2 ^ m * (1 + d ^ (2 * m)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Absorbing `(1 + d^(2m))` into a Gaussian factor `exp(-(b * d² / A))` for `b, A > 0`:
`(1 + d^(2m)) * exp(-(b * d² / A)) ≤ 1 + m! * (A / b)^m`. -/
theorem one_add_pow_two_mul_exp_sq_le (m : ℕ) {b A d : ℝ}
    (hb : 0 < b) (hA : 0 < A) :
    (1 + d ^ (2 * m)) * Real.exp (-(b * d ^ 2 / A)) ≤
      1 + (m.factorial : ℝ) * (A / b) ^ m := by
  set x : ℝ := b * d ^ 2 / A
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hexp_le_one : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hd_pow : d ^ (2 * m) = (A / b) ^ m * x ^ m := by
    have hd2 : d ^ 2 = (A / b) * x := by
      dsimp [x]
      field_simp
    rw [pow_mul, hd2, mul_pow]
  have hterm : d ^ (2 * m) * Real.exp (-x) ≤ (m.factorial : ℝ) * (A / b) ^ m := by
    rw [hd_pow, mul_assoc]
    calc (A / b) ^ m * (x ^ m * Real.exp (-x))
        ≤ (A / b) ^ m * (m.factorial : ℝ) :=
          mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le m hx) (by positivity)
      _ = (m.factorial : ℝ) * (A / b) ^ m := mul_comm _ _
  calc (1 + d ^ (2 * m)) * Real.exp (-x)
      = Real.exp (-x) + d ^ (2 * m) * Real.exp (-x) := by ring
    _ ≤ 1 + (m.factorial : ℝ) * (A / b) ^ m := add_le_add hexp_le_one hterm

/-- Absorbing `(1 + l^(2m))` into a linear exponential factor `exp(-(b * l / c))` for
`b, c > 0` and `l ≥ 0`:
`(1 + l^(2m)) * exp(-(b * l / c)) ≤ 1 + (2m)! * (c / b)^(2m)`. -/
theorem one_add_pow_two_mul_exp_lin_le (m : ℕ) {b c l : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hl : 0 ≤ l) :
    (1 + l ^ (2 * m)) * Real.exp (-(b * l / c)) ≤
      1 + ((2 * m).factorial : ℝ) * (c / b) ^ (2 * m) := by
  set y : ℝ := b * l / c
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hexp_le_one : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hl_pow : l ^ (2 * m) = (c / b) ^ (2 * m) * y ^ (2 * m) := by
    have hly : l = (c / b) * y := by
      dsimp [y]
      field_simp
    conv_lhs => rw [hly]
    rw [mul_pow]
  have hterm : l ^ (2 * m) * Real.exp (-y) ≤ ((2 * m).factorial : ℝ) * (c / b) ^ (2 * m) := by
    rw [hl_pow, mul_assoc]
    calc (c / b) ^ (2 * m) * (y ^ (2 * m) * Real.exp (-y))
        ≤ (c / b) ^ (2 * m) * ((2 * m).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le (2 * m) hy) (by positivity)
      _ = ((2 * m).factorial : ℝ) * (c / b) ^ (2 * m) := mul_comm _ _
  calc (1 + l ^ (2 * m)) * Real.exp (-y)
      = Real.exp (-y) + l ^ (2 * m) * Real.exp (-y) := by ring
    _ ≤ 1 + ((2 * m).factorial : ℝ) * (c / b) ^ (2 * m) := add_le_add hexp_le_one hterm

/-! ### 3. Polynomial base comparisons for `X = (1 + c + ν⁻¹) * (1 + s)` -/

/-- For `C' > 0`, `ν > 0`, `c ≥ 0`, `s ≥ 0`, we have
`2 * (1 + (C' / ν + 2)²) ≤ 2 * (1 + (C' + 2)²) * ((1 + c + ν⁻¹) * (1 + s))²`. -/
theorem two_mul_one_add_R_sq_le {C' ν c s : ℝ} (hC' : 0 < C') (hν : 0 < ν)
    (hc : 0 ≤ c) (hs : 0 ≤ s) :
    2 * (1 + (C' / ν + 2) ^ 2) ≤
      2 * (1 + (C' + 2) ^ 2) * ((1 + c + ν⁻¹) * (1 + s)) ^ 2 := by
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1s : 1 ≤ 1 + s := by linarith
  have h1X : 1 ≤ X := by
    dsimp [X]
    nlinarith [mul_nonneg hc hs, mul_nonneg hν_inv hs]
  have hνX : ν⁻¹ ≤ X := by
    dsimp [X]
    nlinarith [mul_nonneg hc hs, mul_nonneg hν_inv hs]
  have hR_le : C' / ν + 2 ≤ (C' + 2) * X := by
    rw [div_eq_mul_inv]
    nlinarith
  have hR_sq : (C' / ν + 2) ^ 2 ≤ (C' + 2) ^ 2 * X ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hR_le 2
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ h1X
  nlinarith

/-- For `b, C₀, ν₀ > 0`, `0 < ν ≤ ν₀`, `c ≥ 0`, `s ≥ 0`,
`1 + m! * ((C₀ + ν * s) / b)^m ≤ (1 + m! * ((C₀ + ν₀) / b)^m) * ((1 + c + ν⁻¹) * (1 + s))^m`. -/
theorem gauss_absorb_factor_le (m : ℕ) {b C₀ ν₀ ν c s : ℝ}
    (hb : 0 < b) (hC₀ : 0 < C₀) (hν₀ : 0 < ν₀) (hν : 0 < ν) (hν_le : ν ≤ ν₀)
    (hc : 0 ≤ c) (hs : 0 ≤ s) :
    1 + (m.factorial : ℝ) * ((C₀ + ν * s) / b) ^ m ≤
      (1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m) * ((1 + c + ν⁻¹) * (1 + s)) ^ m := by
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have h1s_le : 1 + s ≤ X := by
    dsimp [X]
    nlinarith [mul_nonneg hc hs, mul_nonneg hν_inv hs]
  have h1X : 1 ≤ X ^ m := by
    have : 1 ≤ X := by linarith
    exact one_le_pow₀ this
  have hnum : (C₀ + ν * s) / b ≤ ((C₀ + ν₀) / b) * X := by
    have h1 : C₀ + ν * s ≤ (C₀ + ν₀) * (1 + s) := by nlinarith
    have h2 : (C₀ + ν₀) * (1 + s) ≤ (C₀ + ν₀) * X :=
      mul_le_mul_of_nonneg_left h1s_le (by positivity)
    calc (C₀ + ν * s) / b
        ≤ ((C₀ + ν₀) * X) / b := div_le_div_of_nonneg_right (h1.trans h2) hb.le
      _ = ((C₀ + ν₀) / b) * X := by ring
  have hpow : ((C₀ + ν * s) / b) ^ m ≤ ((C₀ + ν₀) / b) ^ m * X ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hnum m
  have hfac : 0 ≤ (m.factorial : ℝ) := by positivity
  calc 1 + (m.factorial : ℝ) * ((C₀ + ν * s) / b) ^ m
      ≤ X ^ m + (m.factorial : ℝ) * (((C₀ + ν₀) / b) ^ m * X ^ m) :=
        add_le_add h1X (mul_le_mul_of_nonneg_left hpow hfac)
    _ = (1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m) * X ^ m := by ring

/-- For `b > 0`, `ν > 0`, `c ≥ 0`, `s ≥ 0`,
`1 + (2m)! * (c / b)^(2m) ≤ (1 + (2m)! * (1 / b)^(2m)) * ((1 + c + ν⁻¹) * (1 + s))^(2m)`. -/
theorem lin_absorb_factor_le (m : ℕ) {b ν c s : ℝ}
    (hb : 0 < b) (hν : 0 < ν) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    1 + ((2 * m).factorial : ℝ) * (c / b) ^ (2 * m) ≤
      (1 + ((2 * m).factorial : ℝ) * (1 / b) ^ (2 * m)) *
        ((1 + c + ν⁻¹) * (1 + s)) ^ (2 * m) := by
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hc_le : c ≤ X := by
    dsimp [X]
    nlinarith [mul_nonneg hc hs, mul_nonneg hν_inv hs]
  have h1X : 1 ≤ X ^ (2 * m) := by
    have : 1 ≤ X := by
      dsimp [X]
      nlinarith [mul_nonneg hc hs, mul_nonneg hν_inv hs]
    exact one_le_pow₀ this
  have hcb : c / b ≤ (1 / b) * X := by
    calc c / b ≤ X / b := div_le_div_of_nonneg_right hc_le hb.le
      _ = (1 / b) * X := by ring
  have hpow : (c / b) ^ (2 * m) ≤ (1 / b) ^ (2 * m) * X ^ (2 * m) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hcb (2 * m)
  have hfac : 0 ≤ ((2 * m).factorial : ℝ) := by positivity
  calc 1 + ((2 * m).factorial : ℝ) * (c / b) ^ (2 * m)
      ≤ X ^ (2 * m) + ((2 * m).factorial : ℝ) * ((1 / b) ^ (2 * m) * X ^ (2 * m)) :=
        add_le_add h1X (mul_le_mul_of_nonneg_left hpow hfac)
    _ = (1 + ((2 * m).factorial : ℝ) * (1 / b) ^ (2 * m)) * X ^ (2 * m) := by ring

/-! ### 4. Unconditional global `wSupNorm` bound for vorticity `ω = ∇ × v` -/

/-- Pointwise weighted vorticity bound on all of `ℝ²` from a Gaussian transverse tail:
for any `z : Plane`, `√(jap m z) * exp(-b d² / (C₀ + ν s))` (where `d = max (|z.2| - C'/ν) 0`)
is bounded by `K_m * ((1 + c + ν⁻¹) * (1 + s))^(3m)`. -/
theorem sqrt_jap_mul_gaussianTail_le (m : ℕ) {b C₀ C' ν₀ ν c s : ℝ}
    (hb : 0 < b) (hC₀ : 0 < C₀) (hC' : 0 < C') (hν₀ : 0 < ν₀)
    (hν : 0 < ν) (hν_le : ν ≤ ν₀) (hc : 0 ≤ c) (hs : 0 ≤ s) (z : Plane) :
    let d := max (|z.2| - C' / ν) 0
    let K_m := (4 * (1 + (C' + 2) ^ 2)) ^ m *
      (1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m)
    Real.sqrt (jap m z) * Real.exp (-(b * d ^ 2 / (C₀ + ν * s))) ≤
      K_m * ((1 + c + ν⁻¹) * (1 + s)) ^ (3 * m) := by
  intro d K_m
  set R : ℝ := C' / ν + 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hd : 0 ≤ d := le_max_right _ _
  have hz : |z.2| ≤ R + d := by
    have h1 : |z.2| - C' / ν ≤ d := le_max_left _ _
    dsimp [R]
    linarith
  have hjap1 : Real.sqrt (jap m z) ≤ (2 * (1 + R ^ 2)) ^ m * (1 + d ^ 2) ^ m :=
    (sqrt_jap_le_jap m z).trans (jap_le_of_abs_le_add hR hd m z hz)
  have hjap2 : (1 + d ^ 2) ^ m ≤ 2 ^ m * (1 + d ^ (2 * m)) := one_add_sq_pow_le m hd
  have hA : 0 < C₀ + ν * s := by positivity
  have habs := one_add_pow_two_mul_exp_sq_le m hb hA (d := d)
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have hR_pow : (2 * (1 + R ^ 2)) ^ m * 2 ^ m ≤
      (4 * (1 + (C' + 2) ^ 2)) ^ m * X ^ (2 * m) := by
    have hR_le := two_mul_one_add_R_sq_le hC' hν hc hs
    calc (2 * (1 + R ^ 2)) ^ m * 2 ^ m
        ≤ (2 * (1 + (C' + 2) ^ 2) * X ^ 2) ^ m * 2 ^ m := by gcongr
      _ = (2 * (1 + (C' + 2) ^ 2)) ^ m * (X ^ 2) ^ m * 2 ^ m := by rw [mul_pow]
      _ = (2 * (1 + (C' + 2) ^ 2) * 2) ^ m * X ^ (2 * m) := by
          rw [← pow_mul, mul_comm _ (X ^ (2 * m)), mul_assoc, ← mul_pow, mul_comm (X ^ (2 * m))]
      _ = (4 * (1 + (C' + 2) ^ 2)) ^ m * X ^ (2 * m) := by ring
  have hg_le := gauss_absorb_factor_le m hb hC₀ hν₀ hν hν_le hc hs
  calc Real.sqrt (jap m z) * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))
      ≤ ((2 * (1 + R ^ 2)) ^ m * (2 ^ m * (1 + d ^ (2 * m)))) *
          Real.exp (-(b * d ^ 2 / (C₀ + ν * s))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact hjap1.trans (mul_le_mul_of_nonneg_left hjap2 (by positivity))
    _ = ((2 * (1 + R ^ 2)) ^ m * 2 ^ m) *
          ((1 + d ^ (2 * m)) * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))) := by ring
    _ ≤ ((4 * (1 + (C' + 2) ^ 2)) ^ m * X ^ (2 * m)) *
          ((1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m) * X ^ m) :=
        mul_le_mul hR_pow (habs.trans hg_le) (by positivity) (by positivity)
    _ = K_m * X ^ (3 * m) := by
        dsimp [K_m]
        rw [show 3 * m = 2 * m + m by omega, pow_add]
        ring

/-- **Unconditional `wSupNorm` bound for vorticity `ω = ∇ × v`** on all of `ℝ²` from
`TrainVorticityGaussianTail` (`PartI:T20`). -/
theorem wSupNorm_vorticity_of_gaussianTail (hVort : TrainVorticityGaussianTail) :
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          let c := trainPeriod ρ ν
          wSupNorm m (ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s) ≤
            ENNReal.ofReal (polyPS C N ν c s) := by
  intro ρ hρ m ℓ j
  obtain ⟨b, C₀, C', hb, hC₀, hC', C₁, N₁, ν₁, hC₁, hν₁, hV⟩ := hVort ρ hρ ℓ j
  let K_m : ℝ := (4 * (1 + (C' + 2) ^ 2)) ^ m *
    (1 + (m.factorial : ℝ) * ((C₀ + ν₁) / b) ^ m)
  have hKm : 0 < K_m := by dsimp [K_m]; positivity
  refine ⟨C₁ * K_m, N₁ + 3 * m, ν₁, mul_pos hC₁ hKm, hν₁, ?_⟩
  intro ν hν hν_le tr htr s hs
  let c := trainPeriod ρ ν
  have hc : 0 ≤ c := Real.rpow_nonneg hν.le _
  unfold wSupNorm
  refine iSup_le fun z => ?_
  have hω := hV ν hν hν_le tr htr s hs z
  have hjap := sqrt_jap_mul_gaussianTail_le m hb hC₀ hC' hν₁ hν hν_le hc hs.le z
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  set d := max (|z.2| - C' / ν) 0
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have h1s : 1 ≤ 1 + s := by linarith
  have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hpoly : polyP C₁ N₁ ν c ≤ C₁ * X ^ N₁ := by
    unfold polyP
    apply mul_le_mul_of_nonneg_left _ hC₁.le
    apply pow_le_pow_left₀ (by positivity)
    dsimp [X]
    nlinarith [mul_nonneg hc hs.le, mul_nonneg hν_inv hs.le]
  calc Real.sqrt (jap m z) * ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖
      ≤ Real.sqrt (jap m z) * (polyP C₁ N₁ ν c * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))) :=
        mul_le_mul_of_nonneg_left hω (Real.sqrt_nonneg _)
    _ = polyP C₁ N₁ ν c * (Real.sqrt (jap m z) * Real.exp (-(b * d ^ 2 / (C₀ + ν * s)))) := by
        ring
    _ ≤ (C₁ * X ^ N₁) * (K_m * X ^ (3 * m)) :=
        mul_le_mul hpoly hjap (by positivity) (by positivity)
    _ = polyPS (C₁ * K_m) (N₁ + 3 * m) ν c s := by
        unfold polyPS
        rw [pow_add]
        ring

/-! ### 5. Unconditional exterior-strip weighted bounds for `(ψ, v, p)` from `hTail` -/

/-- Pointwise exterior absorption: for `z : Plane` with `C' / ν + 2 ≤ |z.2|` and `l = |z.2| - (C' / ν + 2)`,
`√(jap m z) * (exp(-(b * l / c)) + exp(-(b * l² / (C₀ + ν * s))))` is bounded by
`K_ext * ((1 + c + ν⁻¹) * (1 + s))^(4m)`. -/
theorem sqrt_jap_mul_transverseTail_le (m : ℕ) {b C₀ C' ν₀ ν c s : ℝ}
    (hb : 0 < b) (hC₀ : 0 < C₀) (hC' : 0 < C') (hν₀ : 0 < ν₀)
    (hν : 0 < ν) (hν_le : ν ≤ ν₀) (hc : 0 < c) (hs : 0 ≤ s)
    (z : Plane) (hz : C' / ν + 2 ≤ |z.2|) :
    let l := |z.2| - (C' / ν + 2)
    let K_ext := (4 * (1 + (C' + 2) ^ 2)) ^ m *
      ((1 + ((2 * m).factorial : ℝ) * (1 / b) ^ (2 * m)) +
        (1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m))
    Real.sqrt (jap m z) *
        (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s)))) ≤
      K_ext * ((1 + c + ν⁻¹) * (1 + s)) ^ (4 * m) := by
  intro l K_ext
  set R : ℝ := C' / ν + 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hl : 0 ≤ l := by dsimp [l, R]; linarith
  have hz_eq : |z.2| ≤ R + l := by dsimp [l, R]; linarith
  have hjap1 : Real.sqrt (jap m z) ≤ (2 * (1 + R ^ 2)) ^ m * (1 + l ^ 2) ^ m :=
    (sqrt_jap_le_jap m z).trans (jap_le_of_abs_le_add hR hl m z hz_eq)
  have hjap2 : (1 + l ^ 2) ^ m ≤ 2 ^ m * (1 + l ^ (2 * m)) := one_add_sq_pow_le m hl
  have hA : 0 < C₀ + ν * s := by positivity
  have habs_lin :=
    (one_add_pow_two_mul_exp_lin_le m hb hc hl).trans
      (lin_absorb_factor_le m hb hν hc.le hs)
  have habs_sq :=
    (one_add_pow_two_mul_exp_sq_le m hb hA (d := l)).trans
      (gauss_absorb_factor_le m hb hC₀ hν₀ hν hν_le hc.le hs)
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have h1X : 1 ≤ X := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    dsimp [X]
    nlinarith [mul_nonneg hc.le hs, mul_nonneg this hs]
  have hXm_le : X ^ m ≤ X ^ (2 * m) := pow_le_pow_right₀ h1X (by omega)
  have habs_sq' : (1 + l ^ (2 * m)) * Real.exp (-(b * l ^ 2 / (C₀ + ν * s))) ≤
      (1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m) * X ^ (2 * m) :=
    habs_sq.trans (mul_le_mul_of_nonneg_left hXm_le (by positivity))
  have hR_pow : (2 * (1 + R ^ 2)) ^ m * 2 ^ m ≤
      (4 * (1 + (C' + 2) ^ 2)) ^ m * X ^ (2 * m) := by
    have hR_le := two_mul_one_add_R_sq_le hC' hν hc.le hs
    calc (2 * (1 + R ^ 2)) ^ m * 2 ^ m
        ≤ (2 * (1 + (C' + 2) ^ 2) * X ^ 2) ^ m * 2 ^ m := by gcongr
      _ = (2 * (1 + (C' + 2) ^ 2)) ^ m * (X ^ 2) ^ m * 2 ^ m := by rw [mul_pow]
      _ = (2 * (1 + (C' + 2) ^ 2) * 2) ^ m * X ^ (2 * m) := by
          rw [← pow_mul, mul_comm _ (X ^ (2 * m)), mul_assoc, ← mul_pow, mul_comm (X ^ (2 * m))]
      _ = (4 * (1 + (C' + 2) ^ 2)) ^ m * X ^ (2 * m) := by ring
  calc Real.sqrt (jap m z) *
        (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))
      ≤ ((2 * (1 + R ^ 2)) ^ m * 2 ^ m) *
          ((1 + l ^ (2 * m)) * Real.exp (-(b * l / c)) +
            (1 + l ^ (2 * m)) * Real.exp (-(b * l ^ 2 / (C₀ + ν * s)))) := by
        have hjap : Real.sqrt (jap m z) ≤
            ((2 * (1 + R ^ 2)) ^ m * 2 ^ m) * (1 + l ^ (2 * m)) := by
          calc Real.sqrt (jap m z)
              ≤ (2 * (1 + R ^ 2)) ^ m * (2 ^ m * (1 + l ^ (2 * m))) :=
                hjap1.trans (mul_le_mul_of_nonneg_left hjap2 (by positivity))
            _ = ((2 * (1 + R ^ 2)) ^ m * 2 ^ m) * (1 + l ^ (2 * m)) := by ring
        calc Real.sqrt (jap m z) *
              (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))
            ≤ (((2 * (1 + R ^ 2)) ^ m * 2 ^ m) * (1 + l ^ (2 * m))) *
                (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s)))) :=
              mul_le_mul_of_nonneg_right hjap (by positivity)
          _ = ((2 * (1 + R ^ 2)) ^ m * 2 ^ m) *
                ((1 + l ^ (2 * m)) * Real.exp (-(b * l / c)) +
                  (1 + l ^ (2 * m)) * Real.exp (-(b * l ^ 2 / (C₀ + ν * s)))) := by ring
    _ ≤ ((4 * (1 + (C' + 2) ^ 2)) ^ m * X ^ (2 * m)) *
          ((1 + ((2 * m).factorial : ℝ) * (1 / b) ^ (2 * m)) * X ^ (2 * m) +
            (1 + (m.factorial : ℝ) * ((C₀ + ν₀) / b) ^ m) * X ^ (2 * m)) :=
        mul_le_mul hR_pow (add_le_add habs_lin habs_sq') (by positivity) (by positivity)
    _ = K_ext * X ^ (4 * m) := by
        dsimp [K_ext]
        rw [show 4 * m = 2 * m + 2 * m by omega, pow_add]
        ring

/-- **Unconditional exterior-strip weighted jet bounds for `(ψ, v, p)`** from
`TrainStreamVelocityPressureTransverseTail` (`PartI:T21/1`):
on `|z.2| ≥ C' / ν + 2`, the `m`-weighted jet norms `√(jap m z) * ‖ageJet ℓ j F s z‖`
for `F ∈ {tr.ψ, tr.v, tr.p}` are bounded by `polyPS C_ext (N + 4m) ν c s`. -/
theorem exterior_weighted_jet_of_transverseTail
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (m ℓ j : ℕ) :
    ∃ C' C_ext : ℝ, ∃ N_ext : ℕ, ∃ ν₀ : ℝ, 0 < C' ∧ 0 < C_ext ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          ∀ z : Plane, C' / ν + 2 ≤ |z.2| →
            let c := trainPeriod ρ ν
            let K := polyPS C_ext N_ext ν c s
            Real.sqrt (jap m z) * ‖ageJet ℓ j tr.ψ s z‖ ≤ K ∧
            Real.sqrt (jap m z) * ‖ageJet ℓ j tr.v s z‖ ≤ K ∧
            Real.sqrt (jap m z) * ‖ageJet ℓ j tr.p s z‖ ≤ K := by
  obtain ⟨b, C₀, C', hb, hC₀, hC', C₁, N₁, ν₁, hC₁, hν₁, hT⟩ := hTail ρ hρ ℓ j
  let K_ext : ℝ := (4 * (1 + (C' + 2) ^ 2)) ^ m *
    ((1 + ((2 * m).factorial : ℝ) * (1 / b) ^ (2 * m)) +
      (1 + (m.factorial : ℝ) * ((C₀ + ν₁) / b) ^ m))
  have hK_ext : 0 < K_ext := by dsimp [K_ext]; positivity
  refine ⟨C', C₁ * K_ext, N₁ + 4 * m, ν₁, hC', mul_pos hC₁ hK_ext, hν₁, ?_⟩
  intro ν hν hν_le tr htr s hs z hz
  let c := trainPeriod ρ ν
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  set l : ℝ := |z.2| - (C' / ν + 2)
  have hl : 0 ≤ l := by dsimp [l]; linarith
  have hz_l : C' / ν + 2 + l ≤ |z.2| := by dsimp [l]; linarith
  obtain ⟨hψ, hv, hp⟩ := hT s hs.le ν hν hν_le tr htr l hl s hs le_rfl z hz_l
  have hjap := sqrt_jap_mul_transverseTail_le m hb hC₀ hC' hν₁ hν hν_le hc hs.le z hz
  have hpoly_nn : 0 ≤ polyPS C₁ N₁ ν c s := by
    unfold polyPS
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  have hprod : polyPS C₁ N₁ ν c s *
      (Real.sqrt (jap m z) *
        (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) ≤
      polyPS (C₁ * K_ext) (N₁ + 4 * m) ν c s := by
    calc polyPS C₁ N₁ ν c s *
          (Real.sqrt (jap m z) *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s)))))
        ≤ polyPS C₁ N₁ ν c s * (K_ext * ((1 + c + ν⁻¹) * (1 + s)) ^ (4 * m)) :=
          mul_le_mul_of_nonneg_left hjap hpoly_nn
      _ = polyPS (C₁ * K_ext) (N₁ + 4 * m) ν c s := by
          unfold polyPS
          rw [pow_add]
          ring
  refine ⟨?_, ?_, ?_⟩
  · calc Real.sqrt (jap m z) * ‖ageJet ℓ j tr.ψ s z‖
        ≤ Real.sqrt (jap m z) * (polyPS C₁ N₁ ν c s *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) :=
          mul_le_mul_of_nonneg_left hψ (Real.sqrt_nonneg _)
      _ = polyPS C₁ N₁ ν c s * (Real.sqrt (jap m z) *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) := by ring
      _ ≤ polyPS (C₁ * K_ext) (N₁ + 4 * m) ν c s := hprod
  · calc Real.sqrt (jap m z) * ‖ageJet ℓ j tr.v s z‖
        ≤ Real.sqrt (jap m z) * (polyPS C₁ N₁ ν c s *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) :=
          mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg _)
      _ = polyPS C₁ N₁ ν c s * (Real.sqrt (jap m z) *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) := by ring
      _ ≤ polyPS (C₁ * K_ext) (N₁ + 4 * m) ν c s := hprod
  · calc Real.sqrt (jap m z) * ‖ageJet ℓ j tr.p s z‖
        ≤ Real.sqrt (jap m z) * (polyPS C₁ N₁ ν c s *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) :=
          mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
      _ = polyPS C₁ N₁ ν c s * (Real.sqrt (jap m z) *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * s))))) := by ring
      _ ≤ polyPS (C₁ * K_ext) (N₁ + 4 * m) ν c s := hprod

/-! ### 6. Interior-strip weight bound and gluing with exterior bounds -/

/-- On the interior strip `|z.2| ≤ C' / ν + 2`, `√(jap m z)` is bounded by
`(2 * (1 + (C' + 2)²))^m * ((1 + c + ν⁻¹) * (1 + s))^(2m)`. -/
theorem sqrt_jap_le_on_interior_strip (m : ℕ) {C' ν c s : ℝ}
    (hC' : 0 < C') (hν : 0 < ν) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (z : Plane) (hz : |z.2| ≤ C' / ν + 2) :
    Real.sqrt (jap m z) ≤
      (2 * (1 + (C' + 2) ^ 2)) ^ m * ((1 + c + ν⁻¹) * (1 + s)) ^ (2 * m) := by
  set R : ℝ := C' / ν + 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hz0 : |z.2| ≤ R + 0 := by dsimp [R]; linarith
  have hjap := (sqrt_jap_le_jap m z).trans (jap_le_of_abs_le_add hR le_rfl m z hz0)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow,
    mul_one] at hjap
  have hR_le := two_mul_one_add_R_sq_le hC' hν hc hs
  calc Real.sqrt (jap m z)
      ≤ (2 * (1 + R ^ 2)) ^ m := hjap
    _ ≤ (2 * (1 + (C' + 2) ^ 2) * ((1 + c + ν⁻¹) * (1 + s)) ^ 2) ^ m :=
        pow_le_pow_left₀ (by positivity) hR_le m
    _ = (2 * (1 + (C' + 2) ^ 2)) ^ m * ((1 + c + ν⁻¹) * (1 + s)) ^ (2 * m) := by
        rw [mul_pow, ← pow_mul]

/-- Global `wSupNorm m` bounds on all of `ℝ²` for `ageJet ℓ j` of `(tr.ψ, tr.v, tr.p)` obtained
by gluing `exterior_weighted_jet_of_transverseTail` on `|z.2| ≥ C'/ν + 2` with
`TrainInteriorStripJetBounds` on `|z.2| ≤ C'/ν + 2`. -/
theorem wSupNorm_stream_vel_pressure_of_interior_and_tail
    (hTail : TrainStreamVelocityPressureTransverseTail)
    (hInt : TrainInteriorStripJetBounds)
    (ρ : ℝ) (hρ : 1 / 2 < ρ) (m ℓ j : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          let c := trainPeriod ρ ν
          let K := ENNReal.ofReal (polyPS C N ν c s)
          wSupNorm m (ageJet ℓ j tr.ψ s) ≤ K ∧
          wSupNorm m (ageJet ℓ j tr.v s) ≤ K ∧
          wSupNorm m (ageJet ℓ j tr.p s) ≤ K := by
  obtain ⟨C', C_ext, N_ext, ν_ext, hC', hC_ext, hν_ext, hExt⟩ :=
    exterior_weighted_jet_of_transverseTail hTail ρ hρ m ℓ j
  obtain ⟨C_int, N_int, ν_int, hC_int, hν_int, hIn⟩ := hInt ρ hρ ℓ j C' hC'
  let K_int : ℝ := (2 * (1 + (C' + 2) ^ 2)) ^ m
  have hK_int : 0 < K_int := by dsimp [K_int]; positivity
  let C_out : ℝ := max C_ext (C_int * K_int)
  let N_out : ℕ := max N_ext (N_int + 2 * m)
  refine ⟨C_out, N_out, min ν_ext ν_int, lt_max_of_lt_left hC_ext, lt_min hν_ext hν_int, ?_⟩
  intro ν hν hν_le tr htr s hs
  have hν_e : ν ≤ ν_ext := hν_le.trans (min_le_left _ _)
  have hν_i : ν ≤ ν_int := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc : 0 ≤ c := Real.rpow_nonneg hν.le _
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have h1X : 1 ≤ X := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    dsimp [X]
    nlinarith [mul_nonneg hc hs.le, mul_nonneg this hs.le]
  have hpoly_ext : polyPS C_ext N_ext ν c s ≤ polyPS C_out N_out ν c s := by
    unfold polyPS
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
      (by positivity) (le_trans hC_ext.le (le_max_left _ _))
  have hpoly_int : K_int * X ^ (2 * m) * polyPS C_int N_int ν c s ≤ polyPS C_out N_out ν c s := by
    calc K_int * X ^ (2 * m) * polyPS C_int N_int ν c s
        = (C_int * K_int) * X ^ (N_int + 2 * m) := by
          unfold polyPS
          rw [pow_add]
          ring
      _ ≤ C_out * X ^ N_out :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
            (by positivity) (le_trans hC_ext.le (le_max_left _ _))
      _ = polyPS C_out N_out ν c s := rfl
  have hpt : ∀ z : Plane,
      Real.sqrt (jap m z) * ‖ageJet ℓ j tr.ψ s z‖ ≤ polyPS C_out N_out ν c s ∧
      Real.sqrt (jap m z) * ‖ageJet ℓ j tr.v s z‖ ≤ polyPS C_out N_out ν c s ∧
      Real.sqrt (jap m z) * ‖ageJet ℓ j tr.p s z‖ ≤ polyPS C_out N_out ν c s := by
    intro z
    rcases le_total (C' / ν + 2) |z.2| with hz_ext | hz_int
    · obtain ⟨hψ, hv, hp⟩ := hExt ν hν hν_e tr htr s hs z hz_ext
      exact ⟨hψ.trans hpoly_ext, hv.trans hpoly_ext, hp.trans hpoly_ext⟩
    · obtain ⟨hψ, hv, hp⟩ := hIn ν hν hν_i tr htr s hs z hz_int
      have hjap := sqrt_jap_le_on_interior_strip m hC' hν hc hs.le z hz_int
      have hpoly_in_nn : 0 ≤ polyPS C_int N_int ν c s := by
        unfold polyPS
        have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
        positivity
      refine ⟨?_, ?_, ?_⟩
      · exact (mul_le_mul hjap hψ (norm_nonneg _) (by positivity)).trans hpoly_int
      · exact (mul_le_mul hjap hv (norm_nonneg _) (by positivity)).trans hpoly_int
      · exact (mul_le_mul hjap hp (norm_nonneg _) (by positivity)).trans hpoly_int
  refine ⟨iSup_le fun z => ?_, iSup_le fun z => ?_, iSup_le fun z => ?_⟩
  · rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hpt z).1
  · rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hpt z).2.1
  · rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hpt z).2.2

end PartI_T21

/-! ### 7. Conditional assembly of `TrainWeightedJetBounds` (`PartI:T21/2`) -/

/-- **Conditional assembly of `TrainWeightedJetBounds` (`PartI:T21/2`)** from
`TrainVorticityGaussianTail`, `TrainStreamVelocityPressureTransverseTail`,
`TrainInteriorStripJetBounds`, and `TrainFluctJetWSupNormLe`. Composed by `PartI:T21/2` in
`Short/PartI/Sub/PartI_T21/WeightedJetBounds.lean`. -/
theorem trainWeightedJetBounds_of_interior_and_fluct
    (hInt : TrainInteriorStripJetBounds)
    (hFluct : TrainFluctJetWSupNormLe)
    (_hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail) :
    TrainWeightedJetBounds := by
  apply PartI_T21.trainWeightedJetBounds_of_wSupNorm
  intro ρ hρ m ℓ j
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hSVP⟩ :=
    PartI_T21.wSupNorm_stream_vel_pressure_of_interior_and_tail hTail hInt ρ hρ m ℓ j
  obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hω⟩ :=
    PartI_T21.wSupNorm_vorticity_of_gaussianTail hVort ρ hρ m ℓ j
  let C_out : ℝ := max (4 * C₁) C₂
  let N_out : ℕ := max N₁ N₂
  refine ⟨C_out, N_out, min ν₁ ν₂, lt_max_of_lt_left (by linarith), lt_min hν₁ hν₂, ?_⟩
  intro ν hν hν_le tr htr s hs
  have hν₁_le : ν ≤ ν₁ := hν_le.trans (min_le_left _ _)
  have hν₂_le : ν ≤ ν₂ := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨hψ, hv, hp⟩ := hSVP ν hν hν₁_le tr htr s hs
  have hω_s := hω ν hν hν₂_le tr htr s hs
  have hB₁_nn : 0 ≤ polyPS C₁ N₁ ν c s := by
    unfold polyPS
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  obtain ⟨hψ_fluct_imp, hv_fluct_imp⟩ := hFluct hν hc_pos tr htr m ℓ j hs hB₁_nn
  have hψ_fluct := hψ_fluct_imp hψ
  have hv_fluct := hv_fluct_imp hv
  set X : ℝ := (1 + c + ν⁻¹) * (1 + s)
  have h1X : 1 ≤ X := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    dsimp [X]
    nlinarith [mul_nonneg hc_pos.le hs.le, mul_nonneg this hs.le]
  have hpoly₁ : polyPS C₁ N₁ ν c s ≤ polyPS C_out N_out ν c s := by
    unfold polyPS
    have hC₁_le : C₁ ≤ C_out := le_trans (by linarith) (le_max_left (4 * C₁) C₂)
    exact mul_le_mul hC₁_le (pow_le_pow_right₀ h1X (le_max_left _ _))
      (by positivity) (le_trans hC₁.le hC₁_le)
  have hpoly₁_four : 4 * polyPS C₁ N₁ ν c s ≤ polyPS C_out N_out ν c s := by
    unfold polyPS
    calc 4 * (C₁ * X ^ N₁)
        = (4 * C₁) * X ^ N₁ := by ring
      _ ≤ C_out * X ^ N_out :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1X (le_max_left _ _))
            (by positivity) (le_trans (by positivity) (le_max_left _ _))
  have hpoly₂ : polyPS C₂ N₂ ν c s ≤ polyPS C_out N_out ν c s := by
    unfold polyPS
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1X (le_max_right _ _))
      (by positivity) (le_trans hC₂.le (le_max_right _ _))
  exact ⟨hψ_fluct.trans (ENNReal.ofReal_le_ofReal hpoly₁_four),
    hv_fluct.trans (ENNReal.ofReal_le_ofReal hpoly₁_four),
    hv.trans (ENNReal.ofReal_le_ofReal hpoly₁),
    hω_s.trans (ENNReal.ofReal_le_ofReal hpoly₂),
    hp.trans (ENNReal.ofReal_le_ofReal hpoly₁)⟩

namespace PartI_T21

theorem trainWeightedJetBounds_of_interior_and_fluct
    (hInt : TrainInteriorStripJetBounds)
    (hFluct : TrainFluctJetWSupNormLe)
    (hOv : TrainOverlap)
    (hVort : TrainVorticityGaussianTail)
    (hTail : TrainStreamVelocityPressureTransverseTail) :
    TrainWeightedJetBounds :=
  UnforcedLeray.Short.PartI.trainWeightedJetBounds_of_interior_and_fluct hInt hFluct hOv hVort hTail

end PartI_T21

end UnforcedLeray.Short.PartI
