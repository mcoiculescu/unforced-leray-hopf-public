import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b.FrameCont

/-!
# Part III-a, task `PartIII-a:T21/c1/b`: uniform frame facts, decomposed (SP 2891-2897)

Source of record: `the November 2 reference manuscript`, lines 2891-2897.

The analytic content of `PerFrameFactsAll` is split into four planar leaves for the kernels of
`PlanarFrameKernels` (Gaussian `e`, `O(|y|^{-2})` dual `lamP`, planar biorthogonality), none of
which needs `IsSeedKernels`:

* `PerGramUnfold`, `PerGramTail`: the Gram matrix is the `k = 0` term (biorthogonality, `δ_ij`)
  plus an `O(d^{-2})` off-diagonal tail;
* `PerEBound`: uniform `X_{m,d}` bound of the periodized growing vectors;
* `PerLam0Bound`: uniform dual bound (with integrability) of the periodized dual rows on
  a.e.-strongly measurable inputs.

Proved here: the assembly `perFrameFactsAll_of` (uniform inverse of the Gram matrix, `Λ E = I`,
transfer of the bounds to `Λ = G⁻¹ Λ⁰`, and the cell-length scaling `cellLen ≥ D`). The third field
of `PerFrameFacts` quantifies over every input `W`; a non-measurable `W` is handled by
`FrameCont.exists_aesm_replacement` (if `Λ_i W` is integrable, `1_{Λ_i ≠ 0} W` is measurable with the
same `Λ_i W` and a smaller norm; otherwise the integral is `0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The `k`-th term of the unfolded Gram entry: `∫_ℝ² λ_i(y) e_j(y₁ + k d, y₂) dy`. -/
def gramTerm (κ : PlanarFrameKernels) (d : ℝ) (i j : Fin 2) (k : ℤ) : ℂ :=
  ∫ y, κ.lamP i y * κ.e j (y.1 + k * d, y.2)

/-- **Leaf 1** (SP 2894-2895; unfolding the periodization over the centred cell `B0579.cell d`):
for `d > 0` the Gram entry is the sum over `k ∈ ℤ` of the planar cross integrals,
`G_ij = Σ_k ∫ λ_i(y) e_j(y₁ + kd, y₂) dy`, and the series is summable. Sketch: `∫_cell P_d λ_i · P_d e_j
= Σ_{n,m} ∫_cell λ_i(x+nd) e_j(x+md)`; both are periodic in `x₁`, the double sum collapses with `k = m - n`
and the cells `cell + n d` tile the plane (`Gaussian.integral_cell_periodize` in
`Lib/Gaussian/PeriodizationCell.lean` is the one-factor model); Fubini/`tsum` interchange is justified
by `e_decay` and `lamP_decay`. -/
def PerGramUnfold (κ : PlanarFrameKernels) : Prop :=
  ∀ d : ℝ, 0 < d → ∀ i j : Fin 2,
    Summable (fun k : ℤ => gramTerm κ d i j k) ∧ perGram κ d i j = ∑' k : ℤ, gramTerm κ d i j k

/-- **Leaf 2** (SP 2894-2895; off-diagonal tail): `Σ_{k ≠ 0} ∫ λ_i(y) e_j(y₁ + kd, y₂) dy = O(d^{-2})`.
Sketch: `|λ_i(y)| ≤ C(1+|y|)^{-2}` and `|e_j(y₁+kd,y₂)| ≤ C e^{-|y+kd e₁|²/8}`, so the `k`-th term is
`≲ (1+|k|d)^{-2}` (split the `y₁` half-plane at `-kd/2`), and `Σ_{k≠0}(|k|d)^{-2} ≤ C/d²`. -/
def PerGramTail (κ : PlanarFrameKernels) : Prop :=
  ∃ C D : ℝ, ∀ d : ℝ, D ≤ d → ∀ i j : Fin 2,
    ‖∑' k : ℤ, (if k = 0 then (0 : ℂ) else gramTerm κ d i j k)‖ ≤ C / d ^ 2

/-- **Leaf 3** (SP 2894-2895; `E` has Gaussian tails, uniformly in the period): for `m > 8` there is
`K` with `‖P_d e_i‖_{X_{m,d}} ≤ K` for all `d ≥ 1`. Sketch: on the cell `|y₁| ≤ d/2` the term `n = 0`
carries the weight `(1+|y|²)^m` against `e^{-|y|²/8}`; for `n ≠ 0`, `|y₁ + n d| ≥ |n|d/2`, so those terms are
`≤ C e^{-n²d²/32} e^{-y₂²/8}`, beating `(1+d²/4+y₂²)^{m}` uniformly (model:
`lintegral_cell_sq_norm_periodize_le_of_gauss`, `summable_gauss_shift`/`tsum_gauss_shift_le`). -/
def PerEBound (κ : PlanarFrameKernels) : Prop :=
  ∀ m : ℝ, 8 < m → ∃ K : ℝ, ∀ d : ℝ, 1 ≤ d → ∀ i : Fin 2,
    xNorm d m (perE κ d i) ≤ ENNReal.ofReal K

/-- **Leaf 4** (SP 2894-2897; dual error / `X_{m,d}`-duality of the unnormalised rows): for `m > 8`
there is `K` such that for all `d ≥ 1` and every a.e.-strongly measurable `W` on the cell with
`‖W‖_{X_{m,d}} < ∞` (an element of `X_{m,d}`), the function `Λ⁰_i W` is integrable on the cell and
`|∫_cell Λ⁰_i W| ≤ K ‖W‖_{X_{m,d}}`. (Measurability is needed: `xNorm` is an `eLpNorm`, finite for some
non-measurable `W` with `Λ⁰_i W` not integrable.) Sketch: `|Λ⁰_i(y)| ≤ C Σ_n (1+|y₁+nd|+|y₂|)^{-2}`
is bounded on the cell uniformly in `d ≥ 1` (`n ≠ 0` terms: `|y₁+nd| ≥ |n|/2`), then Cauchy-Schwarz
against the weight `(1+|x|²)^m`: `∫_cell (1+|x|²)^{-m} ≤ C''` uniformly. -/
def PerLam0Bound (κ : PlanarFrameKernels) : Prop :=
  ∀ m : ℝ, 8 < m → ∃ K : ℝ, ∀ d : ℝ, 1 ≤ d → ∀ (i : Fin 2) (W : ℝ × ℝ → ℂ),
    AEStronglyMeasurable W (volume.restrict (B0579.cell d)) →
    xNorm d m W ≠ ∞ →
      IntegrableOn (fun x => perLam0 κ d i x * W x) (B0579.cell d) ∧
      ENNReal.ofReal ‖∫ x in B0579.cell d, perLam0 κ d i x * W x‖ ≤
        ENNReal.ofReal K * xNorm d m W

/-- Gram near the identity for large `d` (from leaves 1, 2 and biorthogonality). -/
theorem perGramNear_of (κ : PlanarFrameKernels) (h1 : PerGramUnfold κ) (h2 : PerGramTail κ) :
    ∀ δ : ℝ, 0 < δ → ∃ D : ℝ, ∀ d : ℝ, D ≤ d → ∀ i j : Fin 2,
      ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ δ := by
  intro δ hδ
  obtain ⟨C, D₀, hC⟩ := h2
  refine ⟨max (max D₀ 1) (Real.sqrt (|C| / δ) + 1), fun d hd i j => ?_⟩
  have hd1 : D₀ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hd2 : 1 ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  have hd3 : Real.sqrt (|C| / δ) + 1 ≤ d := le_trans (le_max_right _ _) hd
  have hdpos : 0 < d := by linarith
  obtain ⟨hs, he⟩ := h1 d hdpos i j
  have hsplit := hs.tsum_eq_add_tsum_ite 0
  have h0 : gramTerm κ d i j 0 = if i = j then 1 else 0 := by
    simp only [gramTerm, Int.cast_zero, zero_mul, add_zero]
    exact κ.biorth i j
  have hrest : perGram κ d i j - (if i = j then 1 else 0) =
      ∑' k : ℤ, (if k = 0 then (0 : ℂ) else gramTerm κ d i j k) := by
    rw [he, hsplit, h0]
    simp only [add_sub_cancel_left]
  rw [hrest]
  refine (hC d hd1 i j).trans ?_
  have hsq : |C| / δ ≤ d ^ 2 := by
    have h0le : 0 ≤ |C| / δ := by positivity
    have := Real.sq_sqrt h0le
    nlinarith [Real.sqrt_nonneg (|C| / δ)]
  rw [div_le_iff₀ (by positivity)]
  calc C ≤ |C| := le_abs_self C
    _ = |C| / δ * δ := by field_simp
    _ ≤ d ^ 2 * δ := by gcongr
    _ = δ * d ^ 2 := by ring

/-- A `2×2` complex matrix within `1/4` of the identity is invertible with entries of the inverse
bounded by `3`. -/
theorem gram_inv_bound (G : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ i j, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4) :
    IsUnit G.det ∧ ∀ i j, ‖G⁻¹ i j‖ ≤ 3 := by
  have h00 := h 0 0
  have h11 := h 1 1
  have h01 := h 0 1
  have h10 := h 1 0
  simp only [if_true, if_false, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, sub_zero,
    Fin.one_eq_zero_iff, one_ne_zero] at h00 h11 h01 h10
  have ha : 3 / 4 ≤ ‖G 0 0‖ := by
    have := norm_sub_norm_le (1 : ℂ) (G 0 0)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hd : 3 / 4 ≤ ‖G 1 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (G 1 1)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have ha' : ‖G 0 0‖ ≤ 5 / 4 := by
    have := norm_sub_norm_le (G 0 0) 1
    rw [norm_one] at this
    linarith
  have hd' : ‖G 1 1‖ ≤ 5 / 4 := by
    have := norm_sub_norm_le (G 1 1) 1
    rw [norm_one] at this
    linarith
  have hdet : 1 / 2 ≤ ‖G.det‖ := by
    rw [Matrix.det_fin_two]
    have h1 := norm_sub_norm_le (G 0 0 * G 1 1) (G 0 1 * G 1 0)
    rw [norm_mul, norm_mul] at h1
    nlinarith [norm_nonneg (G 0 1), norm_nonneg (G 1 0), mul_le_mul ha hd (by norm_num)
      (norm_nonneg _), mul_le_mul h01 h10 (norm_nonneg _) (by norm_num)]
  have hne : G.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    linarith
  refine ⟨isUnit_iff_ne_zero.2 hne, fun i j => ?_⟩
  have hinv : ‖G.det⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hentry : ∀ x : ℂ, ‖x‖ ≤ 5 / 4 → ‖G.det⁻¹ * x‖ ≤ 3 := fun x hx => by
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg G.det⁻¹]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.smul_apply, smul_eq_mul, Fin.zero_eta,
    Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Fin.isValue,
    Fin.reduceFinMk] <;> apply hentry <;> (try simp only [norm_neg]) <;> linarith

/-- Scaling of the cell length (SP 2891-2897): `b ≥ 1`, `θ(s) ≥ b` and `ν ≤ (D+1)⁻²` give
`d = ν⁻²/√a ≥ D`. -/
theorem cellLen_ge {D ν s b : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hνD : ν ≤ 1 / (D + 1) ^ 2)
    (hb : 1 ≤ b) (hs : 0 ≤ s) (ht : b ≤ clockTheta ν s) :
    D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := by
  have ha : 1 ≤ clockA ν s := by
    unfold clockA; nlinarith [mul_nonneg hν.le hs]
  have hapos : 0 < clockA ν s := by linarith
  have hθ : 1 ≤ (ν * clockA ν s)⁻¹ := by
    have := le_trans hb ht
    simpa [clockTheta] using this
  have hνa : ν * clockA ν s ≤ 1 := by
    have hp : 0 < ν * clockA ν s := mul_pos hν hapos
    rwa [one_le_inv₀ hp] at hθ
  have hrpow : ν ^ (-2 : ℝ) = (ν ^ 2)⁻¹ := by
    rw [Real.rpow_neg hν.le]; norm_cast
  unfold cellLen
  rw [hrpow]
  have hsq : 0 < Real.sqrt (clockA ν s) := Real.sqrt_pos.2 hapos
  rw [le_div_iff₀ hsq]
  have h1 : 0 < (ν ^ 2)⁻¹ := by positivity
  have hlhs : 0 ≤ D * Real.sqrt (clockA ν s) := by positivity
  refine le_of_sq_le_sq ?_ h1.le
  rw [mul_pow, Real.sq_sqrt hapos.le]
  have hD1 : D ^ 2 * ν ^ 3 ≤ 1 := by
    have h3 : ν ^ 3 ≤ ν * (1 / (D + 1) ^ 2) ^ 2 := by
      have : ν ^ 2 ≤ (1 / (D + 1) ^ 2) ^ 2 := pow_le_pow_left₀ hν.le hνD 2
      nlinarith [hν]
    have h4 : D ^ 2 * (1 / (D + 1) ^ 2) ^ 2 ≤ 1 := by
      have hp : 0 < (D + 1) ^ 2 := by positivity
      rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_le_one (by positivity)]
      nlinarith [sq_nonneg D, sq_nonneg (D + 1), mul_nonneg hD hD]
    calc D ^ 2 * ν ^ 3 ≤ D ^ 2 * (ν * (1 / (D + 1) ^ 2) ^ 2) := by gcongr
      _ = ν * (D ^ 2 * (1 / (D + 1) ^ 2) ^ 2) := by ring
      _ ≤ ν * 1 := by gcongr
      _ ≤ 1 := by
        have : ν ≤ 1 := by
          have h5 : 1 / (D + 1) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          linarith
        linarith
  have hrhs : ((ν ^ 2)⁻¹) ^ 2 = (ν ^ 4)⁻¹ := by rw [← inv_pow]; ring
  have hνpos : 0 < ν := hν
  have hA : clockA ν s ≤ ν⁻¹ := by
    rw [le_inv_comm₀ hapos hν, inv_eq_one_div]
    rw [le_div_iff₀ hapos]; linarith
  calc D ^ 2 * clockA ν s ≤ D ^ 2 * ν⁻¹ := by gcongr
    _ = (D ^ 2 * ν ^ 3) * (ν ^ 4)⁻¹ := by field_simp
    _ ≤ 1 * (ν ^ 4)⁻¹ := by gcongr
    _ = ((ν ^ 2)⁻¹) ^ 2 := by rw [hrhs, one_mul]

/-- **Assembly**: `PerFrameFactsAll` from the four planar leaves (SP 2891-2897). -/
theorem perFrameFactsAll_of (κ : PlanarFrameKernels) (h1 : PerGramUnfold κ) (h2 : PerGramTail κ)
    (hE : PerEBound κ) (hL : PerLam0Bound κ) : PerFrameFactsAll κ := by
  intro m hm
  obtain ⟨D₁, hD₁⟩ := perGramNear_of κ h1 h2 (1 / 4) (by norm_num)
  obtain ⟨KE, hKE⟩ := hE m hm
  obtain ⟨KL', hKL'⟩ := hL m hm
  set KL : ℝ := max KL' 0 with hKLdef
  have hKL0 : 0 ≤ KL := le_max_right _ _
  set D : ℝ := max D₁ 1 with hDdef
  have hD1 : 1 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := by linarith
  set K : ℝ := max (max KE (6 * KL)) 1 with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K, 1, fun b hb => ⟨1 / (D + 1) ^ 2, by positivity, fun ν hν => ?_⟩⟩
  have hνpos : 0 < ν := hν.1
  have hνD : ν ≤ 1 / (D + 1) ^ 2 := hν.2
  -- facts valid at every admissible age
  have key : ∀ s : ℝ, 0 ≤ s → b ≤ clockTheta ν s →
      1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν s) ∧
      D₁ ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := fun s hs ht => by
    have hge := cellLen_ge hD0 hνpos hνD hb hs ht
    exact ⟨le_trans (le_max_right _ _) hge, le_trans (le_max_left _ _) hge⟩
  have hKLle : ∀ d : ℝ, ∀ i W, 1 ≤ d → AEStronglyMeasurable W (volume.restrict (B0579.cell d)) →
      xNorm d m W ≠ ∞ →
      ENNReal.ofReal ‖∫ x in B0579.cell d, perLam0 κ d i x * W x‖ ≤
        ENNReal.ofReal KL * xNorm d m W := fun d i W hd hWm hW =>
    (hKL' d hd i W hWm hW).2.trans (by gcongr; exact le_max_left _ _)
  have hgram : ∀ d : ℝ, D₁ ≤ d → IsUnit (perGram κ d).det ∧ ∀ i j, ‖(perGram κ d)⁻¹ i j‖ ≤ 3 :=
    fun d hd => gram_inv_bound _ (hD₁ d hd)
  have hEfin : ∀ d : ℝ, 1 ≤ d → ∀ i, xNorm d m (perE κ d i) ≠ ∞ := fun d hd i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKE d hd i)
  -- the periodized growing vectors are continuous, hence measurable inputs
  have hEm : ∀ d : ℝ, 1 ≤ d → ∀ i,
      AEStronglyMeasurable (perE κ d i) (volume.restrict (B0579.cell d)) := fun d hd i =>
    (FrameCont.perE_continuous κ (by linarith) i).aestronglyMeasurable
  -- unfolding of the normalised rows (measurable inputs)
  have hlin : ∀ d : ℝ, 1 ≤ d → ∀ (i : Fin 2) (W : ℝ × ℝ → ℂ),
      AEStronglyMeasurable W (volume.restrict (B0579.cell d)) → xNorm d m W ≠ ∞ →
      ∫ x in B0579.cell d, perLam κ d i x * W x =
        ∑ j, (perGram κ d)⁻¹ i j * ∫ x in B0579.cell d, perLam0 κ d j x * W x := by
    intro d hd i W hWm hW
    have : (fun x => perLam κ d i x * W x) =
        fun x => ∑ j, (perGram κ d)⁻¹ i j * (perLam0 κ d j x * W x) := by
      funext x
      simp only [perLam, Finset.sum_mul, mul_assoc]
    rw [this, integral_finsetSum]
    · simp only [integral_const_mul]
    · intro j _
      exact ((hKL' d hd j W hWm hW).1).const_mul _
  -- the dual bound of the normalised rows on measurable inputs
  have hmeas : ∀ d : ℝ, 1 ≤ d → D₁ ≤ d → ∀ (i : Fin 2) (W : ℝ × ℝ → ℂ),
      AEStronglyMeasurable W (volume.restrict (B0579.cell d)) → xNorm d m W ≠ ∞ →
      ENNReal.ofReal ‖∫ x in B0579.cell d, perLam κ d i x * W x‖ ≤
        ENNReal.ofReal K * xNorm d m W := by
    intro d hd1 hdD i W hWm hW
    obtain ⟨-, hbd⟩ := hgram d hdD
    rw [hlin d hd1 i W hWm hW]
    set x := (xNorm d m W).toReal with hx
    have hX : xNorm d m W = ENNReal.ofReal x := (ENNReal.ofReal_toReal hW).symm
    have hI : ∀ j, ‖∫ x in B0579.cell d, perLam0 κ d j x * W x‖ ≤ KL * x := by
      intro j
      have := hKLle d j W hd1 hWm hW
      rw [hX, ← ENNReal.ofReal_mul hKL0] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    have hsum : ‖∑ j, (perGram κ d)⁻¹ i j * ∫ x in B0579.cell d, perLam0 κ d j x * W x‖ ≤
        K * x := by
      rw [Fin.sum_univ_two]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
      have hK6 : 6 * KL ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
      have e0 := hbd i 0
      have e1 := hbd i 1
      have i0 := hI 0
      have i1 := hI 1
      nlinarith [norm_nonneg ((perGram κ d)⁻¹ i 0), norm_nonneg ((perGram κ d)⁻¹ i 1),
        norm_nonneg (∫ x in B0579.cell d, perLam0 κ d 0 x * W x),
        norm_nonneg (∫ x in B0579.cell d, perLam0 κ d 1 x * W x),
        mul_nonneg hKL0 hx0, mul_le_mul e0 i0 (norm_nonneg _) (by norm_num),
        mul_le_mul e1 i1 (norm_nonneg _) (by norm_num), mul_le_mul_of_nonneg_right hK6 hx0]
    rw [hX, ← ENNReal.ofReal_mul hKpos.le]
    exact ENNReal.ofReal_le_ofReal hsum
  refine ⟨?_, ?_, ?_⟩
  · intro s hs ht i j
    obtain ⟨hd1, hdD⟩ := key s hs ht
    set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s) with hd
    change ∫ x in B0579.cell d, perLam κ d i x * perE κ d j x = _
    rw [hlin d hd1 i _ (hEm d hd1 j) (hEfin d hd1 j)]
    obtain ⟨hU, -⟩ := hgram d hdD
    have hmul := Matrix.nonsing_inv_mul (perGram κ d) hU
    have := congrFun (congrFun hmul i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  · intro s hs ht i
    obtain ⟨hd1, hdD⟩ := key s hs ht
    exact (hKE _ hd1 i).trans (ENNReal.ofReal_le_ofReal (le_trans (le_max_left _ _)
      (le_max_left _ _)))
  · intro s hs ht i W
    obtain ⟨hd1, hdD⟩ := key s hs ht
    set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s) with hd
    change ENNReal.ofReal ‖∫ x in B0579.cell d, perLam κ d i x * W x‖ ≤ _
    by_cases hW : xNorm d m W = ∞
    · rw [hW, ENNReal.mul_top (by simpa using hKpos)]
      exact le_top
    by_cases hint : IntegrableOn (fun x => perLam κ d i x * W x) (B0579.cell d)
    · -- `W` need not be measurable: `W' = 1_{Λ_i ≠ 0} W` is, with the same `Λ_i W`
      obtain ⟨W', hW'm, hW'le, hW'eq⟩ := FrameCont.exists_aesm_replacement
        (FrameCont.perLam_continuous κ (by linarith) i) hint
      have hle : xNorm d m W' ≤ xNorm d m W := eLpNorm_mono hW'le
      have heq : ∫ x in B0579.cell d, perLam κ d i x * W x =
          ∫ x in B0579.cell d, perLam κ d i x * W' x :=
        integral_congr_ae (Eventually.of_forall fun x => (hW'eq x).symm)
      rw [heq]
      refine (hmeas d hd1 hdD i W' hW'm (ne_top_of_le_ne_top hW hle)).trans ?_
      gcongr
    · rw [integral_undef hint, norm_zero, ENNReal.ofReal_zero]
      exact zero_le

end UnforcedLeray.Short.IIIa
