import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9

/-!
# `PartIII-b:C/inst/9/3`: `FAcCellBound` from three Gaussian leaves

Source `the November 2 reference manuscript`
5063-5079 (Gaussian cell norm of `f_A`), 4963-4979 (the fields `V_j`).

Plan: `‖merOf f_AB‖² ≤ K1 |B|² Σ_j G_a(x_j)` pointwise (term bound + lattice weight sum +
Cauchy-Schwarz over `j` with weights `e^{-|x_j|²/(8a)}`), the cell integral of the lattice sum
unfolds to `c⁻¹ ∫_{ℝ²} G_a`, and `∫ G_a ≤ K2` uniformly for `a ∈ [1, 2.1]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th summand of `fAB` (source 5063-5079): `(B_mer x_j)·∇V_j + B V_j`. -/
def fAcTerm (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ) : Vec3 :=
  emb (fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))) + mv B (emb (Vj ν s j x))

/-- Gaussian majorant `G_a(y) = (1+|y|²)^4 e^{-3|y|²/(8a)}`. -/
def fAcG (a : ℝ) (y : ℝ × ℝ) : ℝ := (1 + sq2 y) ^ 4 * Real.exp (-(3 / 8) * sq2 y / a)

/-- Leaf 1a (source 5063-5079; derivative of `V_j = a⁻² e^{-|x_j|²/(4a)} J x_j` explicit; note the
derivative contributes a factor `|x_j|`, absorbed by the Gaussian): pointwise term bound. -/
def FAcTermPointwise : Prop :=
  ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖merOf (fAcTerm ν s B j x)‖ ≤
      C0 * frob B * (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))

/-- Leaf 1b (source 5063-5079): uniform lattice sum of Gaussian weights, `c ≥ 1`, `a ∈ [1, 2.1]`. -/
def FAcLatticeWeight : Prop :=
  ∃ C1 : ℝ, ∀ c t a : ℝ, 1 ≤ c → 1 ≤ a → a ≤ 21 / 10 →
    (∑' j : ℤ, Real.exp (-((t - j * c) ^ 2) / (8 * a))) ≤ C1

/-- Leaf 1 (= 1a + 1b + Cauchy-Schwarz over `j` with weights `e^{-|x_j|²/(8a)}`, source 5063-5079):
pointwise square bound by the lattice sum of `G_a`. -/
def FAcSumPointwise : Prop :=
  ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ (ν s : ℝ) (B : Mat3) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s →
    s ≤ (11 / 10) / ν →
    ‖merOf (fAB ν s B x)‖ ^ 2 ≤ K1 * frob B ^ 2 * ∑' j : ℤ, fAcG (ageA ν s) (xj ν j x)

/-- Leaf 2 (source 5063-5079, unfolding the lattice sum over the centred cell; `avgμ c = c⁻¹ dq dη`). -/
def FAcCellUnfold : Prop :=
  ∀ (c : ℝ) (f : ℝ × ℝ → ℝ), 0 < c → Measurable f → (∀ y, 0 ≤ f y) →
    ∫⁻ x, ENNReal.ofReal (∑' j : ℤ, f (x.1 - j * c, x.2)) ∂(UnforcedLeray.Cyl.avgμ c)
      ≤ ENNReal.ofReal c⁻¹ * ∫⁻ y, ENNReal.ofReal (f y) ∂volume

/-- Leaf 3 (source 5063-5079): uniform Gaussian integral for `a ∈ [1, 2.1]`. -/
def FAcGaussInt : Prop :=
  ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ a : ℝ, 1 ≤ a → a ≤ 21 / 10 →
    ∫⁻ y, ENNReal.ofReal (fAcG a y) ∂(volume : Measure (ℝ × ℝ)) ≤ ENNReal.ofReal K2

theorem fAcCellBound_of (h1 : FAcSumPointwise) (h2 : FAcCellUnfold) (h3 : FAcGaussInt) :
    FAcCellBound := by
  obtain ⟨K1, hK1, hP⟩ := h1
  obtain ⟨K2, hK2, hG⟩ := h3
  refine ⟨Real.sqrt (K1 * K2), Real.sqrt_nonneg _, ?_⟩
  intro ν s hν hν1 hs hsT B
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  have hc0 : 0 < cOf ν := by linarith
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by
    unfold ageA
    have : ν * s ≤ 11 / 10 := by
      rw [le_div_iff₀ hν] at hsT; linarith
    linarith
  have hfB : (0 : ℝ) ≤ K1 * frob B ^ 2 := by positivity
  have hnn : ∀ y, 0 ≤ fAcG (ageA ν s) y := by
    intro y
    unfold fAcG sq2
    positivity
  have hmeas : Measurable (fAcG (ageA ν s)) := by
    unfold fAcG sq2
    fun_prop
  calc ∫⁻ x, ENNReal.ofReal (‖merOf (fAB ν s B x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal (K1 * frob B ^ 2) *
          ENNReal.ofReal (∑' j : ℤ, fAcG (ageA ν s) (xj ν j x))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hfB]
        exact ENNReal.ofReal_le_ofReal (hP ν s B x hν hν1 hs hsT)
    _ = ENNReal.ofReal (K1 * frob B ^ 2) *
          ∫⁻ x, ENNReal.ofReal (∑' j : ℤ, fAcG (ageA ν s) (xj ν j x))
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K1 * frob B ^ 2) *
          (ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal K2) := by
        gcongr
        calc _ ≤ ENNReal.ofReal (cOf ν)⁻¹ *
              ∫⁻ y, ENNReal.ofReal (fAcG (ageA ν s) y) ∂volume :=
            h2 (cOf ν) (fAcG (ageA ν s)) hc0 hmeas hnn
          _ ≤ _ := by gcongr; exact hG _ ha1 ha2
    _ ≤ ENNReal.ofReal (K1 * frob B ^ 2) * (ENNReal.ofReal 1 * ENNReal.ofReal K2) := by
        gcongr
        exact inv_le_one_of_one_le₀ hc1
    _ = ENNReal.ofReal (Real.sqrt (K1 * K2) ^ 2 * frob B ^ 2) := by
        rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul hfB,
          Real.sq_sqrt (mul_nonneg hK1 hK2)]
        congr 1; ring

end UnforcedLeray.Short.PartIIIb.Concrete
