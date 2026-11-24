import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Defs

/-!
# Part III-a, `PartIII-a:T21/2/2/3/6`: the derivative bound of the adjoint interaction, decomposed

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058 (the
adjoint localized interaction maps `X_{-m,d}` to `H^1_{-m,d}` uniformly), 3044-3047 (`p_d` is
equivalent to `⟨y⟩^{2m}`), 2875-2896 (periodic kernel `K_d`).

`AdjointLocalizedBound m` provides, for every `Φ ∈ X_{-m,d}`, a weak interaction `χ'` with weak
gradient `g'` and `h1Norm ≤ C ‖Φ‖`. A classical `C¹` periodic interaction `χ` of a continuous `Φ`
(same characterisation against all tests) has `∂_jχ = g'_j` a.e. (`AdjChiUnique`: kernel velocities
exist, du Bois-Reymond on the cylinder, a `C¹` periodic function has its classical derivative as
weak derivative, weak derivatives are unique); then the weights `p_d⁻¹` and `⟨y⟩^{-m}` compare
(`AdjChiWeights`, `AdjPhiMemLp`). `adjChiDerivBound_of` assembles `AdjChiDerivBound m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- **Sub 1** (SP 2875-2896, 3052-3058; the core uniqueness step). Let `Φ ∈ X_{-m,d}` and let `χ`
be a `C¹` `d`-periodic and `χ'` another field, both adjoint interactions of `Φ` for the same
`E` (same characterisation against every cylinder test with every kernel velocity), `χ'` with weak
gradient `g'` in the finite `H^1_{-m,d}` norm. Then `∂_jχ = g'_j` almost everywhere on the cell.
Proof: (a) every test has a kernel velocity (periodic Biot-Savart, mean-shear far field);
(b) `∫(χ - χ')ψ = 0` for all tests `ψ`, with `χ'ψ` integrable (`χ'` is a.e. measurable
and locally integrable, from the weak-derivative integrability and `xNorm < ∞`), so `χ = χ'`
a.e. on the cell by du Bois-Reymond; (c) `HasWeakCellDerivC d j χ (pdCx j χ)` by classical
integration by parts on the cell (`C¹` and `d`-periodic), and weak derivatives are unique. -/
def AdjChiUnique (m : ℝ) : Prop :=
  ∀ (d : ℝ) (E : ℝ × ℝ → ℝ) (Φ χ χ' : ℝ × ℝ → ℂ) (g' : Fin 2 → ℝ × ℝ → ℂ), 0 < d →
    MemLp Φ 2 (B0579.cellMeasure d (-m)) → ContDiff ℝ 1 χ →
    (∀ y : ℝ × ℝ, χ (y.1 + d, y.2) = χ y) →
    IsAdjInteraction d E Φ χ → IsAdjInteraction d E Φ χ' →
    (∀ j, HasWeakCellDerivC d j χ' (g' j)) → h1Norm d m χ' g' ≠ ⊤ →
    ∀ j : Fin 2, pdCx j χ =ᵐ[volume.restrict (B0579.cell d)] g' j

/-- **Sub 2** (SP 3044-3047, weight equivalence `jb^{-m} ≤ p_d⁻¹ ≤ (π²/4)^m jb^{-m}` on the cell;
ENNReal-to-real conversion): if `∂_kχ = g'_k` a.e. and
`‖⟨y⟩^{-m}g'‖_{L²} ≤ ‖h1Norm‖ ≤ C √E_0` then `Σ_k ∫ p_d⁻¹|∂_kχ|² ≤ (π²/4)^m C² E_0`, the integrands
being integrable. -/
def AdjChiWeights (m : ℝ) : Prop :=
  0 ≤ m → ∀ (d C E0 : ℝ) (χ χ' : ℝ × ℝ → ℂ) (g' : Fin 2 → ℝ × ℝ → ℂ), 0 < d → 0 ≤ C → 0 ≤ E0 →
    (∀ j, pdCx j χ =ᵐ[volume.restrict (B0579.cell d)] g' j) →
    h1Norm d m χ' g' ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt E0) →
    (∀ k : Fin 2, IntegrableOn (fun y => periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2)
      (B0579.cell d)) ∧
    ∑ k : Fin 2, ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx k χ y‖ ^ 2 ≤
      (Real.pi ^ 2 / 4) ^ m * C ^ 2 * E0

/-- **Sub 3** (SP 3044-3047): a continuous `Φ` with `∫ p_d⁻¹|Φ|² < ∞` lies in
`L²(cell, jb^{-m})` with `‖Φ‖_{X_{-m,d}} ≤ √E_0` (since `jb^{-m} ≤ p_d⁻¹` on the cell, valid for `0 ≤ m` only; for `m < 0` the
comparison holds only up to the constant `(π²/4)^{|m|}`). -/
def AdjPhiMemLp (m : ℝ) : Prop :=
  0 ≤ m → ∀ (d : ℝ) (Φ : ℝ × ℝ → ℂ), 0 < d → Continuous Φ →
    IntegrableOn (fun y => periodicWeight (-m) d y * ‖Φ y‖ ^ 2) (B0579.cell d) →
    MemLp Φ 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) Φ ≤ ENNReal.ofReal (Real.sqrt (adjE0 d m Φ))

theorem adjChiDerivBound_of (m : ℝ) (hL : AdjointLocalizedBound m) (h1 : AdjChiUnique m)
    (h2 : AdjChiWeights m) (h3 : AdjPhiMemLp m) : AdjChiDerivBound m := by
  intro hm
  obtain ⟨b₀, hb₀⟩ := hL
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨C, ν₀, hν₀, h⟩ := hb₀ b hb
  refine ⟨(Real.pi ^ 2 / 4) ^ m * (max C 0) ^ 2, ν₀, by positivity, hν₀, ?_⟩
  intro ν hν tr htr r hr hθ Φ χ hΦc hΦi hχ1 hχp hχc
  have hν0 : 0 < ν := hν.1
  have ha : 0 < clockA ν r := by
    unfold clockA
    have : 0 ≤ ν * r := mul_nonneg hν0.le hr
    linarith
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
    unfold cellLen
    exact div_pos (Real.rpow_pos_of_pos hν0 _) (Real.sqrt_pos.mpr ha)
  obtain ⟨hmem, hxn⟩ := h3 hm _ Φ hd hΦc hΦi
  obtain ⟨χ', g', hw, hn, hch⟩ := h ν hν tr htr r hr hθ Φ hmem
  have hne : h1Norm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m χ' g' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hn
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxn)
  have hχ'c : IsAdjInteraction (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (movingTrainE tr r) Φ χ' :=
    fun ψ uψ hψ hu => hch ψ uψ hψ hu
  have hae := h1 _ (movingTrainE tr r) Φ χ χ' g' hd hmem hχ1 hχp hχc hχ'c hw hne
  have hE0 : 0 ≤ adjE0 (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m Φ := adjE0_nonneg _ _ _
  have hCe : ENNReal.ofReal C = ENNReal.ofReal (max C 0) := by
    rcases le_total C 0 with h0 | h0
    · rw [ENNReal.ofReal_of_nonpos h0, max_eq_right h0, ENNReal.ofReal_zero]
    · rw [max_eq_left h0]
  have := h2 hm _ (max C 0) _ χ χ' g' hd (le_max_right _ _) hE0 hae
    (by rw [← hCe]; exact hn.trans (mul_le_mul_right hxn _))
  refine ⟨this.1, this.2.trans ?_⟩
  exact le_of_eq (by ring)

end UnforcedLeray.Short.IIIa.AdjE1
