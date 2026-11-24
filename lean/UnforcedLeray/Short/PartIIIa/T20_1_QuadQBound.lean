import UnforcedLeray.Short.PartIIIa.Sub.T20

/-!
# Part III-a, task `PartIII-a:T20/1`: the moment bound `QuadQBound`

Source of record: `the November 2 reference manuscript`, lines 3230-3236
("The moment bound is weighted Cauchy-Schwarz"). Target: `CTE.QuadQBound` (`Sub/T20.lean`).

Proof. Let `ρ x = jb x ^ m` and `μ = cellMeasure d m`, so that `dμ = ρ dx` on the cell.
* `|∫_cell η² f dx| ≤ ∫_cell η² |f| dx` (`enorm_integral_le_lintegral_enorm`).
* `∫_cell g dx = ∫ ρ⁻¹ g dμ` (`lintegral_cell_eq`), so the integral is `∫ (ρ⁻¹ η²) |f| dμ`.
* Cauchy-Schwarz in `L²(μ)` (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) bounds it by
  `(∫ (ρ⁻¹ η²)² dμ)^{1/2} · ‖f‖_{L²(μ)}`.
* `∫ (ρ⁻¹ η²)² dμ = ∫_cell ρ⁻¹ η⁴ dx ≤ ∫_{ℝ²} (1 + ‖x‖²)^{2-m} dx`, using `η⁴ ≤ (1 + ‖x‖²)²`
  and `1 + ‖x‖² ≤ jb x`; this is finite for `m > 3` (Mathlib `integrable_rpow_neg_one_add_norm_sq`).

The constant is `C = (2/π) (K.toReal)^{1/2}` with `K` the plane integral; it does not depend on `d`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa.CTE

namespace QuadQBoundProof

/-- The cell density `jb x ^ m` as an extended nonnegative real. -/
lemma density_eq (m : ℝ) (x : ℝ × ℝ) :
    ((B0579.density m x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := rfl

lemma ofReal_density_pos (m : ℝ) (x : ℝ × ℝ) : 0 < ENNReal.ofReal (B0579.jb x ^ m) :=
  ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (B0579.jb_pos x) m)

/-- Change of measure from the cell Lebesgue measure to `cellMeasure c m`. -/
lemma lintegral_cell_eq (c m : ℝ) (h : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x in B0579.cell c, h x =
      ∫⁻ x, (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * h x ∂(B0579.cellMeasure c m) := by
  rw [B0579.cellMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (B0579.measurable_density m).coe_nnreal_ennreal (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [density_eq, ← mul_assoc, ENNReal.mul_inv_cancel (ofReal_density_pos m x).ne'
    ENNReal.ofReal_ne_top, one_mul]

/-- The `cellMeasure c m` integral as a cell Lebesgue integral with density `jb^m`. -/
lemma lintegral_cellMeasure_eq (c m : ℝ) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(B0579.cellMeasure c m) =
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.jb x ^ m) * g x := by
  rw [B0579.cellMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (B0579.measurable_density m).coe_nnreal_ennreal (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  rfl

/-- `L²` norm as the square root of the lintegral of the squared enorm (no integrability). -/
lemma eLpNorm_two_eq (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2', htr]
  simp only [ENNReal.rpow_two]

/-- Pointwise: `(1 + ‖x‖²)^{2-m} ≥ (jb x ^ m)⁻¹ (x₂²)²` for `m > 3`. -/
lemma inv_mul_sq_le (m : ℝ) (hm : 3 < m) (x : ℝ × ℝ) :
    (B0579.jb x ^ m)⁻¹ * (x.2 ^ 2) ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ (2 - m) := by
  have hq0 : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hn : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
    rw [Prod.norm_def]
    rcases max_choice ‖x.1‖ ‖x.2‖ with h | h <;> rw [h, Real.norm_eq_abs, sq_abs] <;>
      nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hqjb : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by
    unfold B0579.jb
    linarith
  have hs : ‖x.2‖ ^ 2 = x.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have hsn : x.2 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← hs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le x) 2
  have hx2 : (x.2 ^ 2) ^ 2 ≤ (1 + ‖x‖ ^ 2) ^ 2 := by
    have h0 : 0 ≤ x.2 ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg (show 0 ≤ (1 + ‖x‖ ^ 2) - x.2 ^ 2 by linarith)
      (show 0 ≤ (1 + ‖x‖ ^ 2) + x.2 ^ 2 by positivity)]
  have hqm : 0 < (1 + ‖x‖ ^ 2) ^ m := by positivity
  have hqA : (1 + ‖x‖ ^ 2) ^ m ≤ B0579.jb x ^ m :=
    Real.rpow_le_rpow hq0.le hqjb (by linarith)
  calc (B0579.jb x ^ m)⁻¹ * (x.2 ^ 2) ^ 2
      ≤ ((1 + ‖x‖ ^ 2) ^ m)⁻¹ * (1 + ‖x‖ ^ 2) ^ 2 :=
        mul_le_mul (inv_anti₀ hqm hqA) hx2 (by positivity) (by positivity)
    _ = (1 + ‖x‖ ^ 2) ^ (2 - m) := by
        rw [Real.rpow_sub hq0, Real.rpow_two]
        ring

/-- Pointwise weight bound: `ρ · (ρ⁻¹ · |x₂²|)² ≤ (1 + ‖x‖²)^{2-m}` with `ρ = jb^m`. -/
lemma density_mul_sq_le (m : ℝ) (hm : 3 < m) (x : ℝ × ℝ) :
    ENNReal.ofReal (B0579.jb x ^ m) *
        ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) ^ 2 ≤
      ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m)) := by
  have hA : 0 < B0579.jb x ^ m := Real.rpow_pos_of_pos (B0579.jb_pos x) m
  have ha : ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (x.2 ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hreal : B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹ * x.2 ^ 2) ^ 2 ≤
      (1 + ‖x‖ ^ 2) ^ (2 - m) := by
    have e : B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹ * x.2 ^ 2) ^ 2 =
        (B0579.jb x ^ m)⁻¹ * (x.2 ^ 2) ^ 2 := by
      calc B0579.jb x ^ m * ((B0579.jb x ^ m)⁻¹ * x.2 ^ 2) ^ 2
          = (B0579.jb x ^ m * (B0579.jb x ^ m)⁻¹) * ((B0579.jb x ^ m)⁻¹ * (x.2 ^ 2) ^ 2) := by
            ring
        _ = (B0579.jb x ^ m)⁻¹ * (x.2 ^ 2) ^ 2 := by
            rw [mul_inv_cancel₀ hA.ne', one_mul]
    rw [e]
    exact inv_mul_sq_le m hm x
  have hnn : 0 ≤ (B0579.jb x ^ m)⁻¹ * x.2 ^ 2 := by positivity
  rw [ha, ← ENNReal.ofReal_inv_of_pos hA, ← ENNReal.ofReal_mul (inv_nonneg.2 hA.le),
    ← ENNReal.ofReal_pow hnn, ← ENNReal.ofReal_mul hA.le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The plane integral of the moment weight, finite for `m > 3`. -/
lemma integrable_moment (m : ℝ) (hm : 3 < m) :
    Integrable (fun x : ℝ × ℝ => (1 + ‖x‖ ^ 2) ^ (2 - m)) := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by
    simp
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume)
    (r := 2 * (m - 2)) (by rw [hd]; linarith)
  have hfun : (fun x : ℝ × ℝ => (1 + ‖x‖ ^ 2) ^ (2 - m)) =
      fun x : ℝ × ℝ => (1 + ‖x‖ ^ 2) ^ (-(2 * (m - 2)) / 2) := by
    funext x
    congr 1
    ring
  rw [hfun]
  exact h

/-- The main estimate for a fixed `d`, with the constant `ofReal (2/π) * K^{1/2}`. -/
lemma key (m : ℝ) (hm : 3 < m) (d : ℝ) (f : ℝ × ℝ → ℂ)
    (hf : MemLp f 2 (B0579.cellMeasure d m)) :
    ENNReal.ofReal ‖quadQ d f‖ ≤
      ENNReal.ofReal (2 / Real.pi) * (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) *
        xNorm d m f := by
  -- Step 1: the integral is bounded by the lintegral of the enorm
  have step1 : ENNReal.ofReal ‖quadQ d f‖ ≤
      ENNReal.ofReal (2 / Real.pi) * ∫⁻ x in B0579.cell d, ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖f x‖ₑ := by
    have hc : ‖((2 / Real.pi : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (2 / Real.pi) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc ENNReal.ofReal ‖quadQ d f‖ = ‖quadQ d f‖ₑ := ofReal_norm _
      _ = ‖((2 / Real.pi : ℝ) : ℂ)‖ₑ *
            ‖∫ x in B0579.cell d, ((x.2 ^ 2 : ℝ) : ℂ) * f x‖ₑ := by
          rw [quadQ, enorm_mul, enorm_neg]
      _ = ENNReal.ofReal (2 / Real.pi) * ‖∫ x in B0579.cell d, ((x.2 ^ 2 : ℝ) : ℂ) * f x‖ₑ := by
          rw [hc]
      _ ≤ ENNReal.ofReal (2 / Real.pi) *
            ∫⁻ x in B0579.cell d, ‖((x.2 ^ 2 : ℝ) : ℂ) * f x‖ₑ :=
          mul_le_mul_of_nonneg_left (enorm_integral_le_lintegral_enorm _) zero_le
      _ = ENNReal.ofReal (2 / Real.pi) * ∫⁻ x in B0579.cell d, ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖f x‖ₑ := by
          simp only [enorm_mul]
  -- Step 2: change of measure to `cellMeasure d m`
  have step2 := lintegral_cell_eq d m (fun x => ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖f x‖ₑ)
  -- Step 3: Cauchy-Schwarz in `L²(cellMeasure d m)`
  have hmeasA : Measurable (fun x : ℝ × ℝ => ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) := by
    fun_prop
  have hF : AEMeasurable (fun x : ℝ × ℝ => (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ *
      ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) (B0579.cellMeasure d m) := by
    apply Measurable.aemeasurable
    have hj : Measurable (fun x : ℝ × ℝ => B0579.jb x ^ m) :=
      (B0579.continuous_jb_rpow m).measurable
    exact (hj.ennreal_ofReal.inv).mul hmeasA
  have hG : AEMeasurable (fun x : ℝ × ℝ => ‖f x‖ₑ) (B0579.cellMeasure d m) :=
    hf.aestronglyMeasurable.enorm
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (B0579.cellMeasure d m)
    (p := 2) (q := 2) Real.HolderConjugate.two_two hF hG
  simp only [ENNReal.rpow_two] at hCS
  -- Step 4: the weight integral is bounded by the plane integral
  have hsq : ∫⁻ x, ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) ^ 2
      ∂(B0579.cellMeasure d m) ≤ ∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m)) := by
    rw [lintegral_cellMeasure_eq]
    calc ∫⁻ x in B0579.cell d, ENNReal.ofReal (B0579.jb x ^ m) *
            ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) ^ 2
        ≤ ∫⁻ x in B0579.cell d, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m)) :=
          lintegral_mono fun x => density_mul_sq_le m hm x
      _ ≤ ∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m)) :=
          setLIntegral_le_lintegral _ _
  -- Step 5: assemble
  have hG2 : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) = xNorm d m f := by
    rw [← eLpNorm_two_eq]
    rfl
  have hstep3 : ∫⁻ x, (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * (‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖f x‖ₑ)
      ∂(B0579.cellMeasure d m) ≤
      (∫⁻ x, ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) ^ 2
          ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) := by
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) hCS
    simp only [Pi.mul_apply, mul_assoc]
  have hpow : (∫⁻ x, ((ENNReal.ofReal (B0579.jb x ^ m))⁻¹ * ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ) ^ 2
      ∂(B0579.cellMeasure d m)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hsq (by norm_num)
  calc ENNReal.ofReal ‖quadQ d f‖
      ≤ ENNReal.ofReal (2 / Real.pi) * ∫⁻ x in B0579.cell d,
          ‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖f x‖ₑ := step1
    _ = ENNReal.ofReal (2 / Real.pi) * ∫⁻ x, (ENNReal.ofReal (B0579.jb x ^ m))⁻¹ *
          (‖((x.2 ^ 2 : ℝ) : ℂ)‖ₑ * ‖f x‖ₑ) ∂(B0579.cellMeasure d m) := by
          rw [step2]
    _ ≤ ENNReal.ofReal (2 / Real.pi) * ((∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) *
          xNorm d m f) := by
          refine mul_le_mul_of_nonneg_left (hstep3.trans ?_) zero_le
          rw [← hG2]
          exact mul_le_mul_of_nonneg_right hpow zero_le
    _ = ENNReal.ofReal (2 / Real.pi) * (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) *
          xNorm d m f := by
          rw [mul_assoc]

end QuadQBoundProof

/-- **Moment bound** (SP 3230-3236, "weighted Cauchy-Schwarz"): for `m > 3`, there is a constant
`C` with `|Q_d f| ≤ C ‖f‖_{X_{m,d}}` for every `d` and every `f ∈ L²(cellMeasure d m)`, the
constant being independent of `d`. -/
theorem quadQ_bound : QuadQBound := by
  unfold QuadQBound
  intro m hm
  have hK : (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ≠ ⊤ :=
    (QuadQBoundProof.integrable_moment m hm).lintegral_lt_top.ne
  have hC : ENNReal.ofReal (2 / Real.pi * (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))).toReal ^
      (1 / 2 : ℝ)) = ENNReal.ofReal (2 / Real.pi) *
        (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hK]
  refine ⟨2 / Real.pi * (∫⁻ x : ℝ × ℝ, ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (2 - m))).toReal ^ (1 / 2 : ℝ),
    fun d f hf => ?_⟩
  rw [hC]
  exact QuadQBoundProof.key m hm d f hf

end UnforcedLeray.Short.IIIa.CTE
