import UnforcedLeray.Short.PartIIb.Sub.G4_2_2
import UnforcedLeray.Lib.PlanarSectors.AngularTwo

/-!
# Part II-b, task `PartII-b:G4/2/2/4` (`radialAngularDecay`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route.  On `|x|² > 1/2` write `g(|x|) e^{2iϑ} = y² β(|y|²)` with `y = x₁ + i x₂` and
`β(t) = g(√t)/t` (using `e^{2iϑ} = y²/|y|²`).  A global smooth extension `β` of `t ↦ g(√t)/t` with
Gaussian bounds `|β^{(m)}(t)| ≤ C e^{-κ t}` for `t ≥ 1` (leaf `RadOneDDecay`) turns the problem into the
existing Cartesian bound `Planar.norm_iteratedFDeriv_angularTwo_le`
(`Lib/PlanarSectors/AngularTwo.lean`: `‖D^k(y² β(|y|²))‖ ≤ C (1+|y|)^N ∑_{m≤k} |β^{(m)}(|y|²)|`);
the polynomial factor is absorbed into the Gaussian (`κ ↦ κ/2`), and the identification `ℝ × ℝ ≃L ℂ`
costs a factor `‖e‖^j`.

Proved here: `radialAngularDecay_of : RadOneDDecay → RadialAngularDecay`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- **Leaf `PartII-b:G4/2/2/4/1`** (SP 2349-2352; the 1D Gaussian derivative bounds of
`t ↦ g(√t)/t`): for `g` smooth on `(0,∞)` with Gaussian-bounded derivatives on `[1,∞)`, there is a
globally smooth `β` equal to `g(√t)/t` for `t > 1/2` whose derivatives of order `≤ k` are bounded by
`C e^{-κ t}` on `[1, ∞)`, with `C, κ` depending only on `k`. -/
def RadOneDDecay : Prop :=
  ∀ g : ℝ → ℂ, ContDiffOn ℝ ∞ g (Ioi 0) →
    (∀ j : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv j g r‖ ≤ C * Real.exp (-(κ * r ^ 2))) →
    ∃ β : ℝ → ℂ, ContDiff ℝ ∞ β ∧ (∀ t : ℝ, 1 / 2 < t → β t = g (Real.sqrt t) / (t : ℂ)) ∧
      ∀ k : ℕ, ∃ (C κ : ℝ), 0 < κ ∧ ∀ m : ℕ, m ≤ k → ∀ t : ℝ, 1 ≤ t →
        ‖iteratedDeriv m β t‖ ≤ C * Real.exp (-(κ * t))

theorem radPoly_le_exp (N : ℕ) {κ : ℝ} (hκ : 0 < κ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ / 2 * r ^ 2) := by
  have h1 : 1 + r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have h2 : (1 + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) h1 N
  refine h2.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h2κ : 0 < 2 * κ := by linarith
  rw [← sub_nonneg]
  have : (N : ℝ) ^ 2 / (2 * κ) + κ / 2 * r ^ 2 - N * r = (κ * r - N) ^ 2 / (2 * κ) := by
    field_simp
    ring
  rw [this]
  positivity

theorem radialAngularDecay_of (h : RadOneDDecay) : RadialAngularDecay := by
  intro g hg hdec j
  obtain ⟨β, hβ, hβeq, hbd⟩ := h g hg hdec
  obtain ⟨C, κ, hκ, hb⟩ := hbd j
  obtain ⟨C0, N, hCN⟩ := Planar.norm_iteratedFDeriv_angularTwo_le j
  set e : (ℝ × ℝ) →L[ℝ] ℂ := ((Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ) : (ℝ × ℝ) →L[ℝ] ℂ) with he
  have hex : ∀ y : ℝ × ℝ, e y = (y.1 : ℂ) + (y.2 : ℂ) * Complex.I := fun y =>
    Complex.equivRealProdCLM_symm_apply y
  have hnorm2 : ∀ y : ℝ × ℝ, ‖e y‖ ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    intro y
    rw [hex, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  set F : ℂ → ℂ := fun y => y ^ 2 * β (‖y‖ ^ 2) with hF
  have hFc : ContDiff ℝ j F := by
    have := Planar.contDiff_angularTwo (n := (j : WithTop ℕ∞)) (β := β)
      (hβ.of_le (by exact_mod_cast le_top))
    exact this
  -- local identification
  have hopen : IsOpen {y : ℝ × ℝ | 1 / 2 < y.1 ^ 2 + y.2 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have key : ∀ x : ℝ × ℝ, 1 < x.1 ^ 2 + x.2 ^ 2 →
      ‖iteratedFDeriv ℝ j (fun y : ℝ × ℝ =>
          g (Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) * angularTwo y) x‖ ≤
        ‖iteratedFDeriv ℝ j F (e x)‖ * ‖e‖ ^ j := by
    intro x hx
    have hev : (fun y : ℝ × ℝ => g (Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) * angularTwo y)
        =ᶠ[𝓝 x] (F ∘ e) := by
      filter_upwards [hopen.mem_nhds (show (1 / 2 : ℝ) < x.1 ^ 2 + x.2 ^ 2 by linarith)] with y hy
      have hy' : (1 / 2 : ℝ) < y.1 ^ 2 + y.2 ^ 2 := hy
      simp only [Function.comp_apply, hF]
      rw [hnorm2, hβeq _ hy', hex]
      unfold angularTwo
      push_cast
      ring
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right e hFc x (le_refl _)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp
  refine ⟨‖e‖ ^ j * (|C0| * Real.exp ((N : ℝ) ^ 2 / (2 * κ)) * ((j + 1) * |C|)), κ / 2, by positivity,
    fun x hx => ?_⟩
  have h1 := key x hx
  have hβj : ContDiff ℝ j β := hβ.of_le (by exact_mod_cast le_top)
  have h2 := hCN β hβj (e x)
  have ht1 : (1 : ℝ) ≤ x.1 ^ 2 + x.2 ^ 2 := hx.le
  have hr2 := hnorm2 x
  set t : ℝ := x.1 ^ 2 + x.2 ^ 2 with ht
  set r : ℝ := ‖e x‖ with hr
  set S : ℝ := ∑ m ∈ Finset.range (j + 1), ‖iteratedDeriv m β (‖e x‖ ^ 2)‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => norm_nonneg _
  have hsum : S ≤ ((j : ℝ) + 1) * (|C| * Real.exp (-(κ * t))) := by
    calc S ≤ ∑ m ∈ Finset.range (j + 1), |C| * Real.exp (-(κ * t)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [hr2]
          exact (hb m (by have := Finset.mem_range.1 hm; omega) t ht1).trans
            (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      _ = ((j : ℝ) + 1) * (|C| * Real.exp (-(κ * t))) := by
          rw [Finset.sum_const, Finset.card_range]
          simp
  have hpoly := radPoly_le_exp N hκ (norm_nonneg (e x))
  rw [← hr, hr2] at hpoly
  have hr0 : 0 ≤ (1 + r) ^ N := by positivity
  have he0 : 0 ≤ ‖e‖ ^ j := by positivity
  have hexp : Real.exp (κ / 2 * t) * Real.exp (-(κ * t)) = Real.exp (-(κ / 2 * t)) := by
    rw [← Real.exp_add]
    ring_nf
  calc _ ≤ ‖iteratedFDeriv ℝ j F (e x)‖ * ‖e‖ ^ j := h1
    _ ≤ (C0 * (1 + r) ^ N * S) * ‖e‖ ^ j := by gcongr
    _ ≤ (|C0| * (1 + r) ^ N * S) * ‖e‖ ^ j := by
        gcongr
        exact le_abs_self C0
    _ ≤ (|C0| * (Real.exp ((N : ℝ) ^ 2 / (2 * κ)) * Real.exp (κ / 2 * t)) *
          (((j : ℝ) + 1) * (|C| * Real.exp (-(κ * t))))) * ‖e‖ ^ j := by
        gcongr
    _ = (‖e‖ ^ j * (|C0| * Real.exp ((N : ℝ) ^ 2 / (2 * κ)) * (((j : ℝ) + 1) * |C|))) *
          (Real.exp (κ / 2 * t) * Real.exp (-(κ * t))) := by ring
    _ = _ := by rw [hexp]

end UnforcedLeray.Short.IIb
