import UnforcedLeray.Lib.ParabolicB.LqOp

/-!
# Time dilation and the viscosity scaling of eq:free-stress-11 (INF02 T8)


target T8 ("ν-scaling"). Manuscript: the lemma eq:free-stress-11 (`paper/main.tex` lines
7447–7477, blueprint unit B0423), proof lines 7469–7470 ("the dilation `x = √ν z` makes the
constant independent of viscosity"). Here the dilation is in time instead, `(t, x) ↦ (ν t, x)`,
which carries `∂_t - νΔ` to `ν (∂_s - Δ)`; the effect on the constant is the same.

* `tsc d c : PS d →L[ℝ] PS d`, `(t, x) ↦ (c t, x)`; for `c ≠ 0` a homeomorphism with
  `map (tsc d c) volume = |c⁻¹| • volume` (`map_tsc`).
* `integral_comp_tsc`, `eLpNorm_comp_tsc`, `memLp_comp_tsc`; tests are preserved
  (`IsSTTest.comp_tsc`), and `∂_x`, `∂_x²`, `Δ_x` commute with `tsc`, while
  `∂_t (f ∘ tsc c) = c (∂_t f) ∘ tsc c` (`tD_comp_tsc`).
* `heatEq_tsc`: if `(∂_t - νΔ)u = F` against tests, then
  `(∂_s - Δ)(u ∘ tsc ν⁻¹) = ν⁻¹ F ∘ tsc ν⁻¹` against tests.
* `weakSD2_of_tsc`: weak second derivatives transfer back along `tsc ν`.
* `eLpNorm_smul_comp_tsc_le`: the `L^q` bound at `ν = 1` becomes `‖ν D²u‖_q ≤ C ‖F‖_q`, with the
  same `C`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

section Dilation

/-- Time dilation `(t, x) ↦ (c t, x)`. -/
def tsc (d : ℕ) (c : ℝ) : PS d →L[ℝ] PS d :=
  ContinuousLinearMap.prodMap (c • ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ (Euc d))

@[simp] theorem tsc_apply (c : ℝ) (X : PS d) : tsc d c X = (c * X.1, X.2) := rfl

theorem tsc_tsc (a b : ℝ) (X : PS d) : tsc d a (tsc d b X) = tsc d (a * b) X := by
  simp [mul_assoc]

theorem tsc_inv_tsc {c : ℝ} (hc : c ≠ 0) (X : PS d) : tsc d c⁻¹ (tsc d c X) = X := by
  rw [tsc_tsc, inv_mul_cancel₀ hc]; simp

theorem tsc_tsc_inv {c : ℝ} (hc : c ≠ 0) (X : PS d) : tsc d c (tsc d c⁻¹ X) = X := by
  rw [tsc_tsc, mul_inv_cancel₀ hc]; simp

/-- `tsc d c` as a homeomorphism, `c ≠ 0`. -/
def tscHomeomorph {c : ℝ} (hc : c ≠ 0) : PS d ≃ₜ PS d where
  toFun := tsc d c
  invFun := tsc d c⁻¹
  left_inv := tsc_inv_tsc hc
  right_inv := tsc_tsc_inv hc
  continuous_toFun := (tsc d c).continuous
  continuous_invFun := (tsc d c⁻¹).continuous

theorem measurableEmbedding_tsc {c : ℝ} (hc : c ≠ 0) : MeasurableEmbedding (tsc d c) :=
  (tscHomeomorph (d := d) hc).measurableEmbedding

theorem det_tsc (c : ℝ) :
    LinearMap.det ((tsc d c : PS d →L[ℝ] PS d) : PS d →ₗ[ℝ] PS d) = c := by
  rw [tsc, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap]
  have h1 : ((c • ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = c • LinearMap.id := rfl
  have h2 : ((ContinuousLinearMap.id ℝ (Euc d) : Euc d →L[ℝ] Euc d) : Euc d →ₗ[ℝ] Euc d) =
      LinearMap.id := rfl
  rw [h1, h2, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id, Module.finrank_self]
  ring

/-- **The Jacobian of the time dilation.** -/
theorem map_tsc {c : ℝ} (hc : c ≠ 0) :
    Measure.map (tsc d c) volume = ENNReal.ofReal |c⁻¹| • (volume : Measure (PS d)) := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (PS d))
    (f := ((tsc d c : PS d →L[ℝ] PS d) : PS d →ₗ[ℝ] PS d)) (by rw [det_tsc]; exact hc)
  rw [det_tsc] at h
  exact h

theorem integral_comp_tsc {c : ℝ} (hc : c ≠ 0) (g : PS d → ℝ) :
    ∫ X, g (tsc d c X) = |c⁻¹| * ∫ X, g X := by
  rw [← (measurableEmbedding_tsc hc).integral_map, map_tsc hc, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

/-- Substitution `Y = (ν t, x)`: `∫ g = ν ∫ g ∘ tsc ν`. -/
theorem integral_eq_mul_integral_comp_tsc {ν : ℝ} (hν : 0 < ν) (g : PS d → ℝ) :
    ∫ Y, g Y = ν * ∫ X, g (tsc d ν X) := by
  rw [integral_comp_tsc hν.ne', abs_of_pos (inv_pos.2 hν), ← mul_assoc, mul_inv_cancel₀ hν.ne',
    one_mul]

theorem eLpNorm_comp_tsc {c : ℝ} (hc : c ≠ 0) (g : PS d → ℝ) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    eLpNorm (g ∘ tsc d c) p volume =
      ENNReal.ofReal |c⁻¹| ^ (1 / p).toReal * eLpNorm g p volume := by
  rw [← (measurableEmbedding_tsc hc).eLpNorm_map_measure, map_tsc hc,
    eLpNorm_smul_measure_of_ne_top hp, smul_eq_mul]

theorem memLp_comp_tsc {c : ℝ} (hc : c ≠ 0) {g : PS d → ℝ} {p : ℝ≥0∞}
    (hg : MemLp g p volume) : MemLp (g ∘ tsc d c) p volume := by
  rw [← (measurableEmbedding_tsc hc).memLp_map_measure_iff, map_tsc hc]
  exact hg.smul_measure ENNReal.ofReal_ne_top

theorem IsSTTest.comp_tsc {c : ℝ} (hc : c ≠ 0) {φ : PS d → ℝ} (hφ : IsSTTest φ) :
    IsSTTest (φ ∘ tsc d c) :=
  ⟨hφ.1.comp (tsc d c).contDiff, hφ.2.comp_homeomorph (tscHomeomorph hc)⟩

end Dilation

section Derivatives

theorem dirD_comp_tsc {f : PS d → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (v : PS d) :
    dirD v (f ∘ tsc d c) = fun X => dirD (tsc d c v) f (tsc d c X) := by
  funext X
  simp only [dirD]
  rw [((hf (tsc d c X)).hasFDerivAt.comp X (tsc d c).hasFDerivAt).fderiv]
  rfl

theorem tsc_sdir (c : ℝ) (i : Fin d) : tsc d c (sdir i) = sdir i := by
  simp [sdir]

theorem tsc_tdir (c : ℝ) : tsc d c (tdir : PS d) = c • (tdir : PS d) := by
  ext <;> simp [tdir]

theorem sD_comp_tsc {f : PS d → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (i : Fin d) :
    sD i (f ∘ tsc d c) = sD i f ∘ tsc d c := by
  funext X
  have h := congrFun (dirD_comp_tsc hf c (sdir i)) X
  simp only [tsc_sdir] at h
  exact h

theorem tD_comp_tsc {f : PS d → ℝ} (hf : Differentiable ℝ f) (c : ℝ) :
    tD (f ∘ tsc d c) = fun X => c * tD f (tsc d c X) := by
  funext X
  have h := congrFun (dirD_comp_tsc hf c tdir) X
  simp only [tsc_tdir] at h
  rw [show tD (f ∘ tsc d c) X = dirD tdir (f ∘ tsc d c) X from rfl, h]
  simp only [dirD, map_smul, smul_eq_mul]

theorem sD2_comp_tsc {f : PS d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (i j : Fin d) :
    sD2 i j (f ∘ tsc d c) = sD2 i j f ∘ tsc d c := by
  show sD i (sD j (f ∘ tsc d c)) = _
  rw [sD_comp_tsc (hf.differentiable (by simp)),
    sD_comp_tsc ((contDiff_dirD hf _).differentiable (by simp))]

theorem sLap_comp_tsc {f : PS d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    sLap (f ∘ tsc d c) = sLap f ∘ tsc d c := by
  funext X
  simp only [sLap, Function.comp_apply]
  congr 1; funext k
  rw [sD2_comp_tsc hf]
  rfl

end Derivatives

section Transfer

variable {ν : ℝ} {u F : PS d → ℝ}

/-- **Scaling of the equation.** If `(∂_t - νΔ)u = F` against tests, then the time-dilated
pair `ũ = u ∘ tsc ν⁻¹`, `F̃ = ν⁻¹ F ∘ tsc ν⁻¹` solves `(∂_s - Δ)ũ = F̃` against tests. -/
theorem heatEq_tsc (hν : 0 < ν)
    (heq : ∀ φ : PS d → ℝ, IsSTTest φ →
      ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X) :
    ∀ ψ : PS d → ℝ, IsSTTest ψ →
      ∫ Y, (u ∘ tsc d ν⁻¹) Y * (-tD ψ Y - 1 * sLap ψ Y) =
        ∫ Y, (fun Y => ν⁻¹ * F (tsc d ν⁻¹ Y)) Y * ψ Y := by
  intro ψ hψ
  have hφ : IsSTTest (ψ ∘ tsc d ν) := hψ.comp_tsc hν.ne'
  have h := heq _ hφ
  rw [tD_comp_tsc hψ.differentiable, sLap_comp_tsc hψ.1] at h
  conv_lhs => rw [integral_eq_mul_integral_comp_tsc hν]
  conv_rhs => rw [integral_eq_mul_integral_comp_tsc hν]
  simp only [Function.comp_apply, tsc_inv_tsc hν.ne']
  have e1 : ν * ∫ X, u X * (-tD ψ (tsc d ν X) - 1 * sLap ψ (tsc d ν X)) =
      ∫ X, u X * (-(ν * tD ψ (tsc d ν X)) - ν * sLap ψ (tsc d ν X)) := by
    rw [← integral_const_mul]
    congr 1; funext X; ring
  have e2 : ν * ∫ X, ν⁻¹ * F X * ψ (tsc d ν X) = ∫ X, F X * ψ (tsc d ν X) := by
    rw [← integral_const_mul]
    congr 1; funext X
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul]
  rw [e1, e2]
  exact h

/-- **Weak second derivatives transfer back** along the time dilation. -/
theorem weakSD2_of_tsc (hν : 0 < ν) {D : PS d → ℝ} {i j : Fin d}
    (hD : ∀ ψ : PS d → ℝ, IsSTTest ψ →
      ∫ Y, (u ∘ tsc d ν⁻¹) Y * sD2 i j ψ Y = ∫ Y, D Y * ψ Y)
    {φ : PS d → ℝ} (hφ : IsSTTest φ) :
    ∫ X, u X * sD2 i j φ X = ∫ X, (D ∘ tsc d ν) X * φ X := by
  have hψ : IsSTTest (φ ∘ tsc d ν⁻¹) := hφ.comp_tsc (inv_ne_zero hν.ne')
  have h := hD _ hψ
  rw [sD2_comp_tsc hφ.1] at h
  conv_lhs at h => rw [integral_eq_mul_integral_comp_tsc hν]
  conv_rhs at h => rw [integral_eq_mul_integral_comp_tsc hν]
  simp only [Function.comp_apply, tsc_inv_tsc hν.ne'] at h
  exact mul_left_cancel₀ hν.ne' h

/-- **The constant does not depend on `ν`.** If `‖D‖_q ≤ C ‖ν⁻¹ F ∘ tsc ν⁻¹‖_q`, then
`‖ν D ∘ tsc ν‖_q ≤ C ‖F‖_q`. -/
theorem eLpNorm_smul_comp_tsc_le (hν : 0 < ν) {D : PS d → ℝ} {p : ℝ≥0∞} (hp : p ≠ ⊤)
    {C : ℝ≥0∞}
    (hD : eLpNorm D p volume ≤ C * eLpNorm (fun Y => ν⁻¹ * F (tsc d ν⁻¹ Y)) p volume) :
    eLpNorm (fun X => ν * (D ∘ tsc d ν) X) p volume ≤ C * eLpNorm F p volume := by
  set r : ℝ := (1 / p).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have n1 : eLpNorm (fun X => ν * (D ∘ tsc d ν) X) p volume =
      ENNReal.ofReal ν * (ENNReal.ofReal ν⁻¹ ^ r * eLpNorm D p volume) := by
    have : (fun X => ν * (D ∘ tsc d ν) X) = ν • (D ∘ tsc d ν) := rfl
    rw [this, eLpNorm_const_smul, eLpNorm_comp_tsc hν.ne' D hp, abs_of_pos hνi,
      Real.enorm_eq_ofReal hν.le]
  have n2 : eLpNorm (fun Y => ν⁻¹ * F (tsc d ν⁻¹ Y)) p volume =
      ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν ^ r * eLpNorm F p volume) := by
    have : (fun Y => ν⁻¹ * F (tsc d ν⁻¹ Y)) = ν⁻¹ • (F ∘ tsc d ν⁻¹) := rfl
    rw [this, eLpNorm_const_smul, eLpNorm_comp_tsc (inv_ne_zero hν.ne') F hp, inv_inv,
      abs_of_pos hν, Real.enorm_eq_ofReal hνi.le]
  have p1 : ENNReal.ofReal ν * ENNReal.ofReal ν⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hν.le, mul_inv_cancel₀ hν.ne', ENNReal.ofReal_one]
  have p2 : ENNReal.ofReal ν⁻¹ ^ r * ENNReal.ofReal ν ^ r = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hr0, ← ENNReal.ofReal_mul hνi.le,
      inv_mul_cancel₀ hν.ne', ENNReal.ofReal_one, ENNReal.one_rpow]
  rw [n1]
  calc ENNReal.ofReal ν * (ENNReal.ofReal ν⁻¹ ^ r * eLpNorm D p volume)
      ≤ ENNReal.ofReal ν * (ENNReal.ofReal ν⁻¹ ^ r *
          (C * eLpNorm (fun Y => ν⁻¹ * F (tsc d ν⁻¹ Y)) p volume)) := by gcongr
    _ = (ENNReal.ofReal ν * ENNReal.ofReal ν⁻¹) *
          (ENNReal.ofReal ν⁻¹ ^ r * ENNReal.ofReal ν ^ r) * (C * eLpNorm F p volume) := by
        rw [n2]; ring
    _ = C * eLpNorm F p volume := by rw [p1, p2, one_mul, one_mul]

end Transfer

end UnforcedLeray.Parabolic
