import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint

/-!
# Part III-a, `PartIII-a:T21/2/1`: the adjoint localized interaction, decomposed

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3058
(the adjoint localized interaction maps `X_{-m,d}` to `H^1_{-m,d}` uniformly) with the kernel
comparison 2875-2896.

`AdjointLocalizedBound m` splits into
* `LocalizedSourceBounds` (SP 3053-3054, weighted Cauchy-Schwarz from `RescaledTrainBounds`): the
  localized source `F_j = Φ ∂_jE_mov` has `L¹(C_d)` and `L²(C_d)` norms `≤ C ‖Φ‖_{X_{-m,d}}`;
* `KernelAdjointBound` (SP 2875-2896, 3055-3057): the periodic-kernel adjoint `χ = K_d^T F` of an
  `L¹ ∩ L²` vector field `F` (duality `∫χψ = ∫ F·K_dψ` for every test `ψ`, any circulation) exists
  with `‖χ‖_{H^1_{-m,d}} ≤ C(‖F‖_{L¹} + ‖F‖_{L²})`, uniformly in the cell length `d ≥ 1`
  (near part `O(1/|x-y|)`, far part bounded including the horizontal mean, order-zero
  multiplier for `∇χ`).
`adjointLocalizedBound_of` assembles them (the cell length is `d ≥ 1` in the regime
`θ ≥ b ≥ 1`, `ν ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The localized source `F_j = Φ ∂_jE_mov` (SP 3052-3054). -/
def locSource {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (Φ : ℝ × ℝ → ℂ)
    (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)

/-- **Localized source bounds** (SP 3053-3054): from `RescaledTrainBounds m` and weighted
Cauchy-Schwarz, `F_j = Φ ∂_jE_mov` is in `L¹ ∩ L²(C_d)` with both norms `≤ C ‖Φ‖_{X_{-m,d}}`,
uniformly, for BUC trains (`PartI.IsBUCTrain`, SP 270-288; `RescaledTrainBounds m` holds only for
them). -/
def LocalizedSourceBounds (m : ℝ) : Prop :=
  ∃ b₀ : ℝ, ∀ b : ℝ, b₀ ≤ b → ∃ (C ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
      b ≤ clockTheta ν r → ∀ Φ : ℝ × ℝ → ℂ,
        MemLp Φ 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) →
        ∀ j : Fin 2,
          IntegrableOn (locSource tr r Φ j)
            (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))) ∧
          MemLp (locSource tr r Φ j) 2
            (volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) ∧
          eLpNorm (locSource tr r Φ j) 1
              (volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) ≤
            ENNReal.ofReal C * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ ∧
          eLpNorm (locSource tr r Φ j) 2
              (volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) ≤
            ENNReal.ofReal C * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ

/-- **The periodic-kernel adjoint** (SP 2875-2896, 3055-3057): for `m > 1`, uniformly in the cell
length `d ≥ 1`, every `L¹ ∩ L²` field `F` on `C_d` has a kernel adjoint `χ = K_d^T F` with
`∫χψ = ∫ F·K_dψ` for every real test `ψ` (any circulation, `K_dψ` the kernel velocity) and
`‖χ‖_{H^1_{-m,d}} ≤ C (‖F‖_{L¹} + ‖F‖_{L²})`. -/
def KernelAdjointBound (m : ℝ) : Prop :=
  1 < m → ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d → ∀ F : Fin 2 → ℝ × ℝ → ℂ,
    (∀ j, IntegrableOn (F j) (B0579.cell d) ∧ MemLp (F j) 2 (volume.restrict (B0579.cell d))) →
    ∃ (χ : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC d j χ (gχ j)) ∧
      h1Norm d m χ gχ ≤ ENNReal.ofReal C * ∑ j,
        (eLpNorm (F j) 1 (volume.restrict (B0579.cell d)) +
          eLpNorm (F j) 2 (volume.restrict (B0579.cell d))) ∧
      ∀ ψ uψ, B0579.IsCylTest d ψ → IsKernelBiotSavart d ψ uψ →
        ∫ y in B0579.cell d, χ y * (ψ y : ℂ) =
          ∫ y in B0579.cell d, ∑ j, F j y * ((uψ y j : ℝ) : ℂ)

/-- In the regime `ν ≤ 1`, `1 ≤ b ≤ θ(r)`, the cell length is at least `1`
(`d = ν⁻²/√a ≥ ν^{-3/2}√b`). -/
theorem cellLen_ge_one {ν b r : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hb : 1 ≤ b) (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
  have ha : 0 < clockA ν r := by unfold clockA; positivity
  have hνa : ν * clockA ν r ≤ 1 := by
    have h1 : 1 ≤ clockTheta ν r := hb.trans hθ
    unfold clockTheta at h1
    exact (one_le_inv₀ (by positivity)).mp h1
  have hc : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by rw [Real.rpow_neg hν.le, Real.rpow_two]
  have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν.le hν1
  have hprod : clockA ν r * ν ^ 4 ≤ 1 := by
    have : clockA ν r * ν ^ 4 = (ν * clockA ν r) * ν ^ 3 := by ring
    rw [this]
    exact mul_le_one₀ hνa (by positivity) hν3
  have hle : clockA ν r ≤ ((ν ^ 2)⁻¹) ^ 2 := by
    have : ((ν ^ 2)⁻¹) ^ 2 = 1 / ν ^ 4 := by field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact hprod
  have hs : Real.sqrt (clockA ν r) ≤ (ν ^ 2)⁻¹ := by
    calc Real.sqrt (clockA ν r) ≤ Real.sqrt (((ν ^ 2)⁻¹) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (ν ^ 2)⁻¹ := Real.sqrt_sq (by positivity)
  unfold cellLen
  rw [hc, one_le_div (Real.sqrt_pos.mpr ha)]
  exact hs

/-- **Assembly** of `AdjointLocalizedBound` (SP 3052-3058). -/
theorem adjointLocalizedBound_of (m : ℝ) (hm : 1 < m) (hK : KernelAdjointBound m)
    (hS : LocalizedSourceBounds m) : AdjointLocalizedBound m := by
  obtain ⟨CK, hCK0, hCK⟩ := hK hm
  obtain ⟨b₀, hS⟩ := hS
  refine ⟨max b₀ 1, fun b hb => ?_⟩
  obtain ⟨CS, ν₀, hCS0, hν₀, hS'⟩ := hS b (le_trans (le_max_left _ _) hb)
  refine ⟨CK * (4 * CS), min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro ν hν tr htr r hr hθ Φ hΦ
  have hνS : ν ∈ Ioc 0 ν₀ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hd := cellLen_ge_one hν.1 (hν.2.trans (min_le_right _ _))
    (le_trans (le_max_right _ _) hb) hr hθ
  have hF := hS' ν hνS tr htr r hr hθ Φ hΦ
  obtain ⟨χ, gχ, hder, hh1, hdual⟩ := hCK _ hd (locSource tr r Φ)
    (fun j => ⟨(hF j).1, (hF j).2.1⟩)
  refine ⟨χ, gχ, hder, ?_, ?_⟩
  · refine hh1.trans ?_
    have hsum : ∑ j : Fin 2, (eLpNorm (locSource tr r Φ j) 1
          (volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) +
        eLpNorm (locSource tr r Φ j) 2
          (volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))))) ≤
        4 * (ENNReal.ofReal CS *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ) := by
      rw [Fin.sum_univ_two]
      have h0 := hF 0
      have h1 := hF 1
      calc _ ≤ (ENNReal.ofReal CS * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ +
            ENNReal.ofReal CS * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ) +
          (ENNReal.ofReal CS * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ +
            ENNReal.ofReal CS * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ) :=
            add_le_add (add_le_add h0.2.2.1 h0.2.2.2) (add_le_add h1.2.2.1 h1.2.2.2)
        _ = _ := by ring
    calc ENNReal.ofReal CK * _ ≤ ENNReal.ofReal CK *
          (4 * (ENNReal.ofReal CS *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ)) := by gcongr
      _ = ENNReal.ofReal (CK * (4 * CS)) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) Φ := by
        rw [ENNReal.ofReal_mul hCK0, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring
  · intro ψ uψ hψ hu
    rw [hdual ψ uψ hψ hu]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [locSource, Fin.sum_univ_two]
    push_cast
    ring

end UnforcedLeray.Short.IIIa
