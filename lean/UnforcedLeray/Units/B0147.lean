import UnforcedLeray.Units.B0147.Scaling

/-!
# B0147 — Pointwise, energy and cross-stress bounds for the periodized heat vortex
(`eq:st18-t00145`)

Blueprint unit **B0147**, label `eq:st18-t00145`, `paper/main.tex` lines 2217–2234
(§`sec:st18-3421`, "Gaussian comparison up to the overlap age"); infrastructure `INF27`,
`INF29`; dependency **B0146** (`Units/B0146.lean`, the periodization).

**Statement (tex lines 2217–2234).** For `1 ≤ a ≤ c²` and every fixed `j`,
`‖D^jV_c‖_∞ ≤ C_j a^{-(3+j)/2}`, `‖V_c‖₂ ≤ C a^{-1}`, `‖D^jQ_c‖₂ ≤ C_j a^{-(5+j)/2} e^{-b_jc²/a}`,
with constants independent of `ν` and of `c`; "the same calculation permits any fixed
transverse weight in units of `√a`".

**Conventions.**
* `a = heatWidth ν s = 1 + νs`; `V_c = B0146.periodicVelocity ν c s` and
  `Q_c^{kl} = B0146.crossStress ν c s · k l` (unit B0146, reused, not redefined); `vcomp v k`
  is the `k`-th Cartesian component (`k = 0`: `q`, `k = 1`: `η`).
* `D^j` is every iterated classical partial derivative of order `j`: unit B0151's
  `derivWord w` along a word `w : List Bool` of length `j` (`true` = `∂_q`, `false` = `∂_η`),
  applied to each component. The derivatives are proved to be genuine
  (`classical_derivatives`): each `derivWord w` has an actual one-variable derivative in `q` and
  in `η`, equal to the next word's value, so no junk value of `deriv` enters.
* `‖·‖_∞` is the pointwise bound at every `z`; `‖·‖₂` is unit B0151's cell norm
  `eLpNorm · 2 (cellMeasure c)` on `(0, c] × ℝ` (tex lines 2109–2110), in `ℝ≥0∞`, together with
  `MemLp`, so no junk value of the Lebesgue integral enters.
* The transverse weight in units of `√a` is `(1 + η²/a)^m`, `m : ℕ`; `m = 0` is the unweighted
  statement (`eq_st18_t00145`).
* Hypotheses: `0 < c`, `1 ≤ a`, `a ≤ c²`. The manuscript's standing `c ≥ 2`, `ν > 0` are not
  needed; constants depend only on `j` (the word) and `m`, never on `ν`, `s`, `c`.

**Proof (tex lines 2228–2234).** Rescale `y = x/√a` (`Units/B0147/Scaling.lean`): the period
becomes `L = c/√a ≥ 1`, `V_c = a^{-3/2} ∑ₙ U(y - nLe₁)`, `Q_c = a^{-3} ∑_{i≠j} U_i ⊗ U_j`, and a
derivative word of length `j` produces `a^{-j/2}`. Derivatives of the unit-width profile are
polynomials times `e^{-|y|²/4}` and are absorbed into a smaller Gaussian (`GP.bound`). Gaussian
lattice sums are bounded uniformly for `L ≥ 1`, and on one cell only the two nearest
Gaussians survive (`Units/B0147/Lattice.lean`). For `Q_c` the product of the `i`-th and
`j`-th Gaussians, `i ≠ j`, carries `e^{-βL²/4} = e^{-βc²/(4a)}` (`bil_abs_le`). The cell `L²`
norms then follow from `∫e^{-bt²} = √(π/b)` (`Units/B0147/CellNorm.lean`).

**Main declarations.** `unit_B0147` (the whole unit as stated: constants `C_{j,m}`, `b_{j,m}`
depending only on the order `j` and the weight exponent `m`, plus well-posedness: convergence
of the series and genuine derivatives); `sup_bound_order`, `cross_bound_order` (order-uniform
constants); `sup_bound`, `l2_bound`, `cross_bound` (per derivative word);
`classical_derivatives`; `periodized_heat_vortex_bounds` (per word, with weights);
`eq_st18_t00145` (the unweighted display, `V_c` as a vector field in `L²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.B0147

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0146 (latticeSum shift uc vcomp periodicVelocity crossStress HasPartialX
  HasPartialY)
open UnforcedLeray.B0151 (derivWord cellMeasure)
open UnforcedLeray.B0113 (heatWidth)

section Components

variable {ν c s : ℝ}

theorem derivWord_velocity (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (k : Fin 2) (w : List Bool)
    {g : Plane → ℝ} (hw : ∀ L : ℝ, L ≠ 0 → derivWord w (latticeSum L (U k)) = latticeSum L g) :
    derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) = fun x =>
      lam (heatWidth ν s) ^ 3 * lam (heatWidth ν s) ^ w.length *
        latticeSum (lam (heatWidth ν s) * c) g
          (lam (heatWidth ν s) * x.1, lam (heatWidth ν s) * x.2) := by
  rw [velocity_scale hc ha k, derivWord_scale, hw _ (mul_ne_zero (lam_pos ha).ne' hc)]

theorem derivWord_cross (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (k l : Fin 2) (w : List Bool)
    {H : ℝ → Plane → ℝ} (hw : ∀ L : ℝ, L ≠ 0 → derivWord w (bil L (U k) (U l)) = H L) :
    derivWord w (fun x => crossStress ν c s x k l) = fun x =>
      lam (heatWidth ν s) ^ 6 * lam (heatWidth ν s) ^ w.length *
        H (lam (heatWidth ν s) * c) (lam (heatWidth ν s) * x.1, lam (heatWidth ν s) * x.2) := by
  rw [crossStress_scale ha k l, derivWord_scale, hw _ (mul_ne_zero (lam_pos ha).ne' hc)]

/-- Every derivative word of `V_c^k` and of `Q_c^{kl}` is a genuine iterated partial derivative:
it has an actual derivative in `q` and in `η`, equal to the classical partials. -/
theorem classical_derivatives (hc : c ≠ 0) (ha : 0 < heatWidth ν s) (w : List Bool)
    (z : Plane) :
    (∀ k : Fin 2,
      HasPartialX (derivWord w (fun x => vcomp (periodicVelocity ν c s x) k)) z ∧
      HasPartialY (derivWord w (fun x => vcomp (periodicVelocity ν c s x) k)) z) ∧
    (∀ k l : Fin 2,
      HasPartialX (derivWord w (fun x => crossStress ν c s x k l)) z ∧
      HasPartialY (derivWord w (fun x => crossStress ν c s x k l)) z) := by
  have hLne : lam (heatWidth ν s) * c ≠ 0 := mul_ne_zero (lam_pos ha).ne' hc
  refine ⟨fun k => ?_, fun k l => ?_⟩
  · obtain ⟨g, hg, hw⟩ := (GP_U k).derivWord_lattice w
    rw [derivWord_velocity hc ha k w hw]
    have h := hg.lattice_hasPartial hLne (lam (heatWidth ν s) * z.1, lam (heatWidth ν s) * z.2)
    exact ⟨hasPartialX_scale _ _ _ z h.1, hasPartialY_scale _ _ _ z h.2⟩
  · obtain ⟨H, hH, hw⟩ := (BS.pair (GP_U k) (GP_U l)).deriv_word w
    rw [derivWord_cross hc ha k l w hw]
    have h := hH.hasPartial hLne (lam (heatWidth ν s) * z.1, lam (heatWidth ν s) * z.2)
    exact ⟨hasPartialX_scale _ _ _ z h.1, hasPartialY_scale _ _ _ z h.2⟩

end Components

/-! ### The three estimates of tex line 2220, one component at a time -/

theorem sup_bound_k (w : List Bool) (m : ℕ) (k : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ z : Plane, (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
          C * heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2) := by
  obtain ⟨g, hg, hw⟩ := (GP_U k).derivWord_lattice w
  obtain ⟨K, β, hK, hβ, hb⟩ := (hg.weight m).bound
  have hθ := theta_nonneg (β / 8)
  refine ⟨K * (2 + theta (β / 8)), by positivity, fun ν c s hc ha1 hac z => ?_⟩
  have ha : 0 < heatWidth ν s := by linarith
  have hl := lam_pos ha
  have hL := one_le_lam_mul ha hc hac
  rw [derivWord_velocity hc.ne' ha k w hw, weight_eq ha]
  set l := lam (heatWidth ν s)
  have hS : |(1 + (l * z.2) ^ 2) ^ m * latticeSum (l * c) g (l * z.1, l * z.2)| ≤
      K * (2 + theta (β / 8)) := by
    have := latticeSum_sup hK hβ hL hb (l * z.1, l * z.2)
    rwa [← latticeSum_weight] at this
  have hpow : l ^ 3 * l ^ w.length = heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2) := by
    rw [← pow_add, lam_pow_eq_rpow ha, Nat.cast_add, Nat.cast_ofNat]
  have hw0 : 0 ≤ (1 + (l * z.2) ^ 2) ^ m := by positivity
  calc (1 + (l * z.2) ^ 2) ^ m * |l ^ 3 * l ^ w.length * latticeSum (l * c) g (l * z.1, l * z.2)|
      = (l ^ 3 * l ^ w.length) *
          |(1 + (l * z.2) ^ 2) ^ m * latticeSum (l * c) g (l * z.1, l * z.2)| := by
        rw [abs_mul, abs_mul (_ ^ m), abs_of_nonneg hw0, abs_of_nonneg (by positivity)]
        ring
    _ ≤ (l ^ 3 * l ^ w.length) * (K * (2 + theta (β / 8))) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = K * (2 + theta (β / 8)) * heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2) := by
        rw [hpow]; ring

theorem l2_bound_k (m : ℕ) (k : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * (heatWidth ν s)⁻¹) := by
  have hg := (GP_U k).weight m
  obtain ⟨K, β, hK, hβ, hb⟩ := hg.bound
  obtain ⟨M, hM, hcell⟩ := eLpNorm_lattice_cell hK hβ
  refine ⟨M, hM, fun ν c s hc ha1 hac => ?_⟩
  have ha : 0 < heatWidth ν s := by linarith
  have hl := lam_pos ha
  have hL := one_le_lam_mul ha hc hac
  have hLne : lam (heatWidth ν s) * c ≠ 0 := by positivity
  have hF : (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
      vcomp (periodicVelocity ν c s z) k) = fun z => lam (heatWidth ν s) ^ 3 *
        latticeSum (lam (heatWidth ν s) * c) (fun x => (1 + x.2 ^ 2) ^ m * U k x)
          (lam (heatWidth ν s) * z.1, lam (heatWidth ν s) * z.2) := by
    funext z
    rw [weight_eq ha, congrFun (velocity_scale hc.ne' ha k) z, ← latticeSum_weight]
    ring
  rw [hF]
  set l := lam (heatWidth ν s)
  have hcont : Continuous (fun z : Plane => l ^ 3 *
      latticeSum (l * c) (fun x => (1 + x.2 ^ 2) ^ m * U k x) (l * z.1, l * z.2)) :=
    continuous_const.mul ((hg.latticeSum_continuous hLne).comp
      (f := fun z : Plane => (l * z.1, l * z.2)) (by fun_prop))
  have hpt : ∀ z : Plane, z.1 ∈ Ioc 0 c → |l ^ 3 *
      latticeSum (l * c) (fun x => (1 + x.2 ^ 2) ^ m * U k x) (l * z.1, l * z.2)| ≤
      l ^ 3 * (K * Real.exp (-(β * (l * z.2) ^ 2)) *
        (Real.exp (-(β * (l * z.1) ^ 2)) + Real.exp (-(β * (l * z.1 - l * c) ^ 2)) +
          Real.exp (-(β * (l * c) ^ 2 / 2)) * theta (β / 8))) := by
    intro z hz
    rw [abs_mul, abs_of_pos (pow_pos hl 3)]
    exact mul_le_mul_of_nonneg_left (latticeSum_cell hK hβ hL hb (l * z.1, l * z.2)
      (by have := hz.1; positivity) (mul_le_mul_of_nonneg_left hz.2 hl.le)) (by positivity)
  have hbound := hcell l c _ hl hc hL hpt
  have he : ENNReal.ofReal (l ^ 2 * M) = ENNReal.ofReal (M * (heatWidth ν s)⁻¹) := by
    rw [lam_sq ha, mul_comm]
  rw [he] at hbound
  exact ⟨⟨hcont.aestronglyMeasurable, hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩

theorem cross_bound_kl (w : List Bool) (m : ℕ) (k l : Fin 2) :
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s →
      heatWidth ν s ≤ c ^ 2 →
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
            Real.exp (-(b * c ^ 2 / heatWidth ν s))) := by
  obtain ⟨H₁, hH₁, hw⟩ := (BS.pair (GP_U k) (GP_U l)).deriv_word w
  have hH₂ := hH₁.weight m
  obtain ⟨C, γ, hC, hγ, hb⟩ := hH₂.bound
  obtain ⟨M, hM, hcell⟩ := eLpNorm_bs_cell hC hγ
  refine ⟨M, γ / 2, hM, by positivity, fun ν c s hc ha1 hac => ?_⟩
  have ha : 0 < heatWidth ν s := by linarith
  have hl := lam_pos ha
  have hL := one_le_lam_mul ha hc hac
  have hLne : lam (heatWidth ν s) * c ≠ 0 := by positivity
  have hF : (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
      derivWord w (fun x => crossStress ν c s x k l) z) = fun z =>
        lam (heatWidth ν s) ^ (6 + w.length) *
          ((1 + (lam (heatWidth ν s) * z.2) ^ 2) ^ m *
            H₁ (lam (heatWidth ν s) * c) (lam (heatWidth ν s) * z.1,
              lam (heatWidth ν s) * z.2)) := by
    funext z
    rw [weight_eq ha, derivWord_cross hc.ne' ha k l w hw, pow_add]
    ring
  rw [hF]
  set l' := lam (heatWidth ν s)
  have hcont : Continuous (fun z : Plane => l' ^ (6 + w.length) *
      ((1 + (l' * z.2) ^ 2) ^ m * H₁ (l' * c) (l' * z.1, l' * z.2))) :=
    continuous_const.mul ((hH₂.continuous hLne).comp
      (f := fun z : Plane => (l' * z.1, l' * z.2)) (by fun_prop))
  have hpt : ∀ z : Plane, z.1 ∈ Ioc 0 c → |l' ^ (6 + w.length) *
      ((1 + (l' * z.2) ^ 2) ^ m * H₁ (l' * c) (l' * z.1, l' * z.2))| ≤
      l' ^ (6 + w.length) * (C * Real.exp (-(γ * (l' * c) ^ 2)) *
        Real.exp (-(γ * (l' * z.2) ^ 2))) := by
    intro z _
    rw [abs_mul, abs_of_pos (pow_pos hl _)]
    exact mul_le_mul_of_nonneg_left (hb (l' * c) hL (l' * z.1, l' * z.2)) (by positivity)
  have hbound := hcell l' c (6 + w.length) _ hl hc hL hpt
  have he : l' ^ (6 + w.length) * l'⁻¹ * M * Real.exp (-(γ / 2 * (l' * c) ^ 2)) =
      M * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
        Real.exp (-(γ / 2 * c ^ 2 / heatWidth ν s)) := by
    have h1 : l' ^ (6 + w.length) * l'⁻¹ = l' ^ (5 + w.length) := by
      rw [show 6 + w.length = (5 + w.length) + 1 by ring, pow_succ]
      field_simp
    have h2 : l' ^ (5 + w.length) = heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) := by
      rw [lam_pow_eq_rpow ha, Nat.cast_add, Nat.cast_ofNat]
    rw [h1, h2, lam_mul_sq ha, mul_div_assoc]
    ring
  rw [he] at hbound
  exact ⟨⟨hcont.aestronglyMeasurable, hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩

/-! ### Uniform constants over the components -/

theorem rpow_nonneg_width {a e : ℝ} (ha : 1 ≤ a) : 0 ≤ a ^ e :=
  Real.rpow_nonneg (by linarith) e

/-- **Pointwise bounds** (tex line 2220, first estimate, with weight):
`(1 + η²/a)^m |D^j V_c| ≤ C_{j,m} a^{-(3+j)/2}` for `0 < c`, `1 ≤ a ≤ c²`. -/
theorem sup_bound (w : List Bool) (m : ℕ) :
    ∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ (k : Fin 2) (z : Plane), (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
          C * heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2) := by
  obtain ⟨C₀, h₀, b₀⟩ := sup_bound_k w m 0
  obtain ⟨C₁, h₁, b₁⟩ := sup_bound_k w m 1
  refine ⟨C₀ + C₁, fun ν c s hc ha1 hac k z => ?_⟩
  have hp := rpow_nonneg_width (e := -(3 + (w.length : ℝ)) / 2) ha1
  fin_cases k
  · exact (b₀ ν c s hc ha1 hac z).trans (mul_le_mul_of_nonneg_right (by linarith) hp)
  · exact (b₁ ν c s hc ha1 hac z).trans (mul_le_mul_of_nonneg_right (by linarith) hp)

/-- **Energy bound over one cell** (tex line 2221, second estimate, with weight):
`‖(1 + η²/a)^m V_c‖_{L²(cell)} ≤ C_m a^{-1}` for `0 < c`, `1 ≤ a ≤ c²`. -/
theorem l2_bound (m : ℕ) :
    ∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ k : Fin 2,
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * (heatWidth ν s)⁻¹) := by
  obtain ⟨C₀, h₀, b₀⟩ := l2_bound_k m 0
  obtain ⟨C₁, h₁, b₁⟩ := l2_bound_k m 1
  refine ⟨C₀ + C₁, fun ν c s hc ha1 hac k => ?_⟩
  have hp : 0 ≤ (heatWidth ν s)⁻¹ := inv_nonneg.mpr (by linarith)
  fin_cases k
  · obtain ⟨hm, he⟩ := b₀ ν c s hc ha1 hac
    exact ⟨hm, he.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) hp))⟩
  · obtain ⟨hm, he⟩ := b₁ ν c s hc ha1 hac
    exact ⟨hm, he.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) hp))⟩

theorem cross_mono {C C' b b' X Y : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ C') (hb : b' ≤ b) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) : C * X * Real.exp (-(b * Y)) ≤ C' * X * Real.exp (-(b' * Y)) :=
  mul_le_mul (mul_le_mul_of_nonneg_right hC hX) (Real.exp_le_exp.mpr (by nlinarith))
    (Real.exp_pos _).le (mul_nonneg (hC0.trans hC) hX)

/-- **Cross-stress bound over one cell** (tex line 2221, third estimate, with weight):
`‖(1 + η²/a)^m D^j Q_c‖_{L²(cell)} ≤ C_{j,m} a^{-(5+j)/2} e^{-b_{j,m} c²/a}` for `0 < c`,
`1 ≤ a ≤ c²`, with `b_{j,m} > 0`. -/
theorem cross_bound (w : List Bool) (m : ℕ) :
    ∃ C b : ℝ, 0 < b ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ k l : Fin 2,
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
            Real.exp (-(b * c ^ 2 / heatWidth ν s))) := by
  obtain ⟨C₀₀, b₀₀, hC₀₀, hb₀₀, h₀₀⟩ := cross_bound_kl w m 0 0
  obtain ⟨C₀₁, b₀₁, hC₀₁, hb₀₁, h₀₁⟩ := cross_bound_kl w m 0 1
  obtain ⟨C₁₀, b₁₀, hC₁₀, hb₁₀, h₁₀⟩ := cross_bound_kl w m 1 0
  obtain ⟨C₁₁, b₁₁, hC₁₁, hb₁₁, h₁₁⟩ := cross_bound_kl w m 1 1
  refine ⟨C₀₀ + C₀₁ + C₁₀ + C₁₁, min (min b₀₀ b₀₁) (min b₁₀ b₁₁),
    lt_min (lt_min hb₀₀ hb₀₁) (lt_min hb₁₀ hb₁₁), fun ν c s hc ha1 hac k l => ?_⟩
  have hX := rpow_nonneg_width (e := -(5 + (w.length : ℝ)) / 2) ha1
  have hY : 0 ≤ c ^ 2 / heatWidth ν s := div_nonneg (sq_nonneg c) (by linarith)
  have mono : ∀ C' b' : ℝ, 0 ≤ C' → C' ≤ C₀₀ + C₀₁ + C₁₀ + C₁₁ →
      min (min b₀₀ b₀₁) (min b₁₀ b₁₁) ≤ b' →
      ENNReal.ofReal (C' * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
        Real.exp (-(b' * c ^ 2 / heatWidth ν s))) ≤
      ENNReal.ofReal ((C₀₀ + C₀₁ + C₁₀ + C₁₁) * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
        Real.exp (-(min (min b₀₀ b₀₁) (min b₁₀ b₁₁) * c ^ 2 / heatWidth ν s))) := by
    intro C' b' h0 hC hb
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_assoc, mul_div_assoc]
    exact cross_mono h0 hC hb hX hY
  fin_cases k <;> fin_cases l
  · obtain ⟨hm, he⟩ := h₀₀ ν c s hc ha1 hac
    exact ⟨hm, he.trans (mono _ _ hC₀₀ (by linarith)
      ((min_le_left _ _).trans (min_le_left _ _)))⟩
  · obtain ⟨hm, he⟩ := h₀₁ ν c s hc ha1 hac
    exact ⟨hm, he.trans (mono _ _ hC₀₁ (by linarith)
      ((min_le_left _ _).trans (min_le_right _ _)))⟩
  · obtain ⟨hm, he⟩ := h₁₀ ν c s hc ha1 hac
    exact ⟨hm, he.trans (mono _ _ hC₁₀ (by linarith)
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  · obtain ⟨hm, he⟩ := h₁₁ ν c s hc ha1 hac
    exact ⟨hm, he.trans (mono _ _ hC₁₁ (by linarith)
      ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- The cell energy bound for the vector field `V_c` itself (the norm of `ℝ × ℝ` is the max
norm, equivalent to the Euclidean one up to `√2`). -/
theorem l2_bound_vector :
    ∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      MemLp (periodicVelocity ν c s) 2 (cellMeasure c) ∧
      eLpNorm (periodicVelocity ν c s) 2 (cellMeasure c) ≤
        ENNReal.ofReal (C * (heatWidth ν s)⁻¹) := by
  obtain ⟨C, hC⟩ := l2_bound 0
  refine ⟨2 * max C 0, fun ν c s hc ha1 hac => ?_⟩
  have h0 := hC ν c s hc ha1 hac 0
  have h1 := hC ν c s hc ha1 hac 1
  simp only [pow_zero, one_mul] at h0 h1
  obtain ⟨m0, e0⟩ := h0
  obtain ⟨m1, e1⟩ := h1
  have hinv : 0 ≤ (heatWidth ν s)⁻¹ := inv_nonneg.mpr (by linarith)
  have hp : 0 ≤ max C 0 * (heatWidth ν s)⁻¹ := mul_nonneg (le_max_right _ _) hinv
  have hle : ENNReal.ofReal (C * (heatWidth ν s)⁻¹) ≤
      ENNReal.ofReal (max C 0 * (heatWidth ν s)⁻¹) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hinv)
  have hmeas : AEStronglyMeasurable (periodicVelocity ν c s) (cellMeasure c) :=
    m0.1.prodMk m1.1
  have hnorm : eLpNorm (periodicVelocity ν c s) 2 (cellMeasure c) ≤
      ENNReal.ofReal (2 * max C 0 * (heatWidth ν s)⁻¹) := by
    calc eLpNorm (periodicVelocity ν c s) 2 (cellMeasure c)
        ≤ eLpNorm (fun z => ‖vcomp (periodicVelocity ν c s z) 0‖ +
            ‖vcomp (periodicVelocity ν c s z) 1‖) 2 (cellMeasure c) := by
          apply eLpNorm_mono_ae_real
          refine Eventually.of_forall fun z => ?_
          rw [Prod.norm_def]
          exact max_le (le_add_of_nonneg_right (norm_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))
      _ ≤ eLpNorm (fun z => ‖vcomp (periodicVelocity ν c s z) 0‖) 2 (cellMeasure c) +
          eLpNorm (fun z => ‖vcomp (periodicVelocity ν c s z) 1‖) 2 (cellMeasure c) :=
          eLpNorm_add_le m0.1.norm m1.1.norm one_le_two
      _ = eLpNorm (fun z => vcomp (periodicVelocity ν c s z) 0) 2 (cellMeasure c) +
          eLpNorm (fun z => vcomp (periodicVelocity ν c s z) 1) 2 (cellMeasure c) := by
          rw [eLpNorm_norm, eLpNorm_norm]
      _ ≤ ENNReal.ofReal (max C 0 * (heatWidth ν s)⁻¹) +
          ENNReal.ofReal (max C 0 * (heatWidth ν s)⁻¹) :=
          add_le_add (e0.trans hle) (e1.trans hle)
      _ = ENNReal.ofReal (2 * max C 0 * (heatWidth ν s)⁻¹) := by
          rw [← ENNReal.ofReal_add hp hp]
          congr 1
          ring
  exact ⟨⟨hmeas, hnorm.trans_lt ENNReal.ofReal_lt_top⟩, hnorm⟩

/-! ### The unit -/

/-- **Unit B0147** (`eq:st18-t00145`, tex lines 2217–2234), with every fixed transverse weight
`(1 + η²/a)^m` (tex line 2234). For every derivative word `w` (order `j = w.length`) and every
`m`, with constants depending only on `w` and `m`, for all `ν, s, c` with `0 < c`,
`1 ≤ a = 1 + νs ≤ c²`:
1. `(1 + η²/a)^m |D_w V_c^k| ≤ C a^{-(3+j)/2}` pointwise;
2. `‖(1 + η²/a)^m V_c^k‖_{L²(cell)} ≤ C a^{-1}` (and the field is in `L²` of the cell);
3. `‖(1 + η²/a)^m D_w Q_c^{kl}‖_{L²(cell)} ≤ C a^{-(5+j)/2} e^{-bc²/a}`, `b > 0`;
4. all the derivative words of `V_c` and `Q_c` are genuine iterated partial derivatives. -/
theorem periodized_heat_vortex_bounds :
    (∀ (w : List Bool) (m : ℕ), ∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s →
      heatWidth ν s ≤ c ^ 2 → ∀ (k : Fin 2) (z : Plane), (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
          C * heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2)) ∧
    (∀ m : ℕ, ∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ k : Fin 2,
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * (heatWidth ν s)⁻¹)) ∧
    (∀ (w : List Bool) (m : ℕ), ∃ C b : ℝ, 0 < b ∧ ∀ ν c s : ℝ, 0 < c →
      1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 → ∀ k l : Fin 2,
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
            Real.exp (-(b * c ^ 2 / heatWidth ν s)))) ∧
    (∀ ν c s : ℝ, c ≠ 0 → 0 < heatWidth ν s → ∀ (w : List Bool) (z : Plane),
      (∀ k : Fin 2,
        HasPartialX (derivWord w (fun x => vcomp (periodicVelocity ν c s x) k)) z ∧
        HasPartialY (derivWord w (fun x => vcomp (periodicVelocity ν c s x) k)) z) ∧
      (∀ k l : Fin 2,
        HasPartialX (derivWord w (fun x => crossStress ν c s x k l)) z ∧
        HasPartialY (derivWord w (fun x => crossStress ν c s x k l)) z)) :=
  ⟨sup_bound, l2_bound, cross_bound,
    fun _ _ _ hc ha w z => classical_derivatives hc ha w z⟩

/-- **The display `eq:st18-t00145`** (tex lines 2217–2222): for `1 ≤ a ≤ c²` and every fixed
`j`, `‖D^jV_c‖_∞ ≤ C_j a^{-(3+j)/2}`, `‖V_c‖₂ ≤ C a^{-1}` (over one cell, for the vector field),
`‖D^jQ_c‖₂ ≤ C_j a^{-(5+j)/2} e^{-b_jc²/a}`, constants independent of `ν` and `c`. -/
theorem eq_st18_t00145 :
    (∀ w : List Bool, ∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s →
      heatWidth ν s ≤ c ^ 2 → ∀ (k : Fin 2) (z : Plane),
        |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
          C * heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2)) ∧
    (∃ C : ℝ, ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      MemLp (periodicVelocity ν c s) 2 (cellMeasure c) ∧
      eLpNorm (periodicVelocity ν c s) 2 (cellMeasure c) ≤
        ENNReal.ofReal (C * (heatWidth ν s)⁻¹)) ∧
    (∀ w : List Bool, ∃ C b : ℝ, 0 < b ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s →
      heatWidth ν s ≤ c ^ 2 → ∀ k l : Fin 2,
      MemLp (derivWord w (fun x => crossStress ν c s x k l)) 2 (cellMeasure c) ∧
      eLpNorm (derivWord w (fun x => crossStress ν c s x k l)) 2 (cellMeasure c) ≤
        ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
          Real.exp (-(b * c ^ 2 / heatWidth ν s)))) := by
  refine ⟨fun w => ?_, l2_bound_vector, fun w => ?_⟩
  · obtain ⟨C, hC⟩ := sup_bound w 0
    refine ⟨C, fun ν c s hc ha1 hac k z => ?_⟩
    have := hC ν c s hc ha1 hac k z
    simpa only [pow_zero, one_mul] using this
  · obtain ⟨C, b, hb, hC⟩ := cross_bound w 0
    refine ⟨C, b, hb, fun ν c s hc ha1 hac k l => ?_⟩
    have := hC ν c s hc ha1 hac k l
    simp only [pow_zero, one_mul] at this
    exact this

/-! ### Constants depending only on the order `j`

The manuscript's constants are `C_j`, `b_j` (tex line 2219: "for every fixed `j`"), one for all
derivatives of order `j`. There are `2^j` words of length `j`, so the per-word constants above
are made uniform over a finite set. -/

/-- All derivative words of length `j`. -/
def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | j + 1 => (words j).image (List.cons true) ∪ (words j).image (List.cons false)

theorem mem_words : ∀ w : List Bool, w ∈ words w.length
  | [] => by simp [words]
  | true :: w => by
      simp only [List.length_cons, words]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_words w))
  | false :: w => by
      simp only [List.length_cons, words]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_words w))

/-- Per-index constants `(C_i, b_i)`, monotone in `C` (upwards) and `b` (downwards), are made
uniform over a finite set of indices. -/
theorem finset_uniform {ι : Type*} [DecidableEq ι] (S : Finset ι) (P : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i C b C' b', 0 ≤ C → P i C b → C ≤ C' → 0 < b' → b' ≤ b → P i C' b')
    (h : ∀ i, ∃ C b, 0 ≤ C ∧ 0 < b ∧ P i C b) :
    ∃ C b, 0 ≤ C ∧ 0 < b ∧ ∀ i ∈ S, P i C b := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 1, le_rfl, one_pos, by simp⟩
  | insert i S _ ih =>
    obtain ⟨C₁, b₁, hC₁, hb₁, h₁⟩ := h i
    obtain ⟨C₂, b₂, hC₂, hb₂, h₂⟩ := ih
    refine ⟨max C₁ C₂, min b₁ b₂, le_max_of_le_left hC₁, lt_min hb₁ hb₂, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hmono _ _ _ _ _ hC₁ h₁ (le_max_left _ _) (lt_min hb₁ hb₂) (min_le_left _ _)
    · exact hmono _ _ _ _ _ hC₂ (h₂ x hx) (le_max_right _ _) (lt_min hb₁ hb₂)
        (min_le_right _ _)

/-- Constants uniform over all words of a fixed length `j`. -/
theorem uniform_words (P : List Bool → ℝ → ℝ → Prop)
    (hmono : ∀ w C b C' b', 0 ≤ C → P w C b → C ≤ C' → 0 < b' → b' ≤ b → P w C' b')
    (h : ∀ w, ∃ C b, 0 ≤ C ∧ 0 < b ∧ P w C b) (j : ℕ) :
    ∃ C b, 0 ≤ C ∧ 0 < b ∧ ∀ w : List Bool, w.length = j → P w C b := by
  obtain ⟨C, b, hC, hb, hS⟩ := finset_uniform (words j) P hmono h
  exact ⟨C, b, hC, hb, fun w hw => hS w (hw ▸ mem_words w)⟩

/-- **Pointwise bounds with `C_{j,m}`** (tex line 2220): one constant for every derivative of
order `j` of every component of `V_c`, with the transverse weight `(1 + η²/a)^m`. -/
theorem sup_bound_order (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ w : List Bool, w.length = j → ∀ (k : Fin 2) (z : Plane),
        (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
          |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
            C * heatWidth ν s ^ (-(3 + (j : ℝ)) / 2) := by
  obtain ⟨C, _, hC, _, hS⟩ := uniform_words
    (fun w C _ => ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ (k : Fin 2) (z : Plane), (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
          C * heatWidth ν s ^ (-(3 + (w.length : ℝ)) / 2))
    (fun w C b C' b' _ hP hCC _ _ ν c s hc ha1 hac k z =>
      (hP ν c s hc ha1 hac k z).trans
        (mul_le_mul_of_nonneg_right hCC (rpow_nonneg_width ha1)))
    (fun w => by
      obtain ⟨C, hC⟩ := sup_bound w m
      exact ⟨max C 0, 1, le_max_right _ _, one_pos, fun ν c s hc ha1 hac k z =>
        (hC ν c s hc ha1 hac k z).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_nonneg_width ha1))⟩) j
  refine ⟨C, hC, fun ν c s hc ha1 hac w hw k z => ?_⟩
  subst hw
  exact hS w rfl ν c s hc ha1 hac k z

/-- **Cross-stress bounds with `C_{j,m}`, `b_{j,m}`** (tex line 2221): one pair of constants for
every derivative of order `j` of every entry of `Q_c`, with the transverse weight
`(1 + η²/a)^m`. -/
theorem cross_bound_order (j m : ℕ) :
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s →
      heatWidth ν s ≤ c ^ 2 → ∀ w : List Bool, w.length = j → ∀ k l : Fin 2,
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (j : ℝ)) / 2) *
            Real.exp (-(b * c ^ 2 / heatWidth ν s))) := by
  obtain ⟨C, b, hC, hb, hS⟩ := uniform_words
    (fun w C b => ∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
      ∀ k l : Fin 2,
      MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ∧
      eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
        derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ≤
          ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (w.length : ℝ)) / 2) *
            Real.exp (-(b * c ^ 2 / heatWidth ν s))))
    (fun w C b C' b' hC0 hP hCC _ hbb ν c s hc ha1 hac k l => by
      obtain ⟨hm, he⟩ := hP ν c s hc ha1 hac k l
      refine ⟨hm, he.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      have hX := rpow_nonneg_width (e := -(5 + (w.length : ℝ)) / 2) ha1
      have hY : 0 ≤ c ^ 2 / heatWidth ν s := div_nonneg (sq_nonneg c) (by linarith)
      rw [mul_div_assoc, mul_div_assoc]
      exact cross_mono hC0 hCC hbb hX hY)
    (fun w => by
      obtain ⟨C, b, hb, hC⟩ := cross_bound w m
      refine ⟨max C 0, b, le_max_right _ _, hb, fun ν c s hc ha1 hac k l => ?_⟩
      obtain ⟨hm, he⟩ := hC ν c s hc ha1 hac k l
      refine ⟨hm, he.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      have hX := rpow_nonneg_width (e := -(5 + (w.length : ℝ)) / 2) ha1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
        (Real.exp_pos _).le) j
  refine ⟨C, b, hC, hb, fun ν c s hc ha1 hac w hw k l => ?_⟩
  subst hw
  exact hS w rfl ν c s hc ha1 hac k l

/-- **Unit B0147, as stated** (`eq:st18-t00145`, tex lines 2217–2234). For every derivative
order `j` and every transverse weight exponent `m` (the weight `(1 + η²/a)^m` is in units of
`√a`, tex line 2234; `m = 0` is the unweighted display), there are constants `C_{j,m} ≥ 0`,
`b_{j,m} > 0`, independent of `ν`, `s`, `c` and of the derivative of order `j`, such that for all
`ν, s` and `c > 0` with `1 ≤ a = 1 + νs ≤ c²`:
1. `(1 + η²/a)^m |D^jV_c^k| ≤ C a^{-(3+j)/2}` at every point;
2. `‖(1 + η²/a)^m V_c^k‖_{L²(one cell)} ≤ C a^{-1}`, the field being in `L²` of the cell;
3. `‖(1 + η²/a)^m D^jQ_c^{kl}‖_{L²(one cell)} ≤ C a^{-(5+j)/2} e^{-bc²/a}`, the field being in
   `L²` of the cell.
Well-posedness (no junk value enters): 4. the image series defining `V_c` and the off-diagonal
series defining `Q_c` converge (unit B0146), and 5. every iterated derivative is a genuine
partial derivative. -/
theorem unit_B0147 (j m : ℕ) :
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧
      (∀ ν c s : ℝ, 0 < c → 1 ≤ heatWidth ν s → heatWidth ν s ≤ c ^ 2 →
        (∀ w : List Bool, w.length = j → ∀ (k : Fin 2) (z : Plane),
          (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
            |derivWord w (fun x => vcomp (periodicVelocity ν c s x) k) z| ≤
              C * heatWidth ν s ^ (-(3 + (j : ℝ)) / 2)) ∧
        (∀ k : Fin 2,
          MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
            vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ∧
          eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
            vcomp (periodicVelocity ν c s z) k) 2 (cellMeasure c) ≤
              ENNReal.ofReal (C * (heatWidth ν s)⁻¹)) ∧
        (∀ w : List Bool, w.length = j → ∀ k l : Fin 2,
          MemLp (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
            derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ∧
          eLpNorm (fun z : Plane => (1 + z.2 ^ 2 / heatWidth ν s) ^ m *
            derivWord w (fun x => crossStress ν c s x k l) z) 2 (cellMeasure c) ≤
              ENNReal.ofReal (C * heatWidth ν s ^ (-(5 + (j : ℝ)) / 2) *
                Real.exp (-(b * c ^ 2 / heatWidth ν s))))) ∧
      (∀ ν c s : ℝ, c ≠ 0 → 0 < heatWidth ν s → ∀ z : Plane,
        Summable (fun n : ℤ => B0146.imageVelocity ν c n s z) ∧
        ∀ k l : Fin 2, Summable (fun p : ({p : ℤ × ℤ | p.1 ≠ p.2} : Set (ℤ × ℤ)) =>
          vcomp (B0146.imageVelocity ν c p.1.1 s z) k *
            vcomp (B0146.imageVelocity ν c p.1.2 s z) l)) ∧
      (∀ ν c s : ℝ, c ≠ 0 → 0 < heatWidth ν s → ∀ (w : List Bool) (z : Plane),
        (∀ k : Fin 2,
          HasPartialX (derivWord w (fun x => vcomp (periodicVelocity ν c s x) k)) z ∧
          HasPartialY (derivWord w (fun x => vcomp (periodicVelocity ν c s x) k)) z) ∧
        (∀ k l : Fin 2,
          HasPartialX (derivWord w (fun x => crossStress ν c s x k l)) z ∧
          HasPartialY (derivWord w (fun x => crossStress ν c s x k l)) z)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := sup_bound_order j m
  obtain ⟨C₂, h₂⟩ := l2_bound m
  obtain ⟨C₃, b, hC₃, hb, h₃⟩ := cross_bound_order j m
  refine ⟨C₁ + max C₂ 0 + C₃, b, by positivity, hb, fun ν c s hc ha1 hac => ⟨?_, ?_, ?_⟩,
    fun ν c s hc ha z => ⟨(B0146.hasSum_periodicVelocity hc ha z).summable,
      fun k l => B0146.summable_crossStress hc ha z k l⟩,
    fun ν c s hc ha w z => classical_derivatives hc ha w z⟩
  · intro w hw k z
    exact (h₁ ν c s hc ha1 hac w hw k z).trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_right C₂ 0]) (rpow_nonneg_width ha1))
  · intro k
    obtain ⟨hm, he⟩ := h₂ ν c s hc ha1 hac k
    refine ⟨hm, he.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (inv_nonneg.mpr (by linarith))))⟩
    linarith [le_max_left C₂ 0]
  · intro w hw k l
    obtain ⟨hm, he⟩ := h₃ ν c s hc ha1 hac w hw k l
    refine ⟨hm, he.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith [le_max_right C₂ 0]) (rpow_nonneg_width ha1)) (Real.exp_pos _).le

end UnforcedLeray.B0147
