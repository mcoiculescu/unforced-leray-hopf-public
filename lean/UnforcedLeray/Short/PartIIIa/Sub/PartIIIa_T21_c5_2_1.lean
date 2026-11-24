import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2

/-!
# Part III-a, task `PartIII-a:T21/c5/2/1` decomposition (`Sub/PartIII-a_T21_c5_2_1.lean`, SP 2893, 2905-2912, 2991-2995)

Source of record: `the November 2 reference manuscript` (SP), lines 2893, 2905-2912,
and 2991-2995 (`eq:short-causal-ampl-moving`).

## Mathematical structure and proved reductions

1. **Quantitative Gram-matrix and Gram-inverse `O(d⁻²)` approximation (proved here)**:
   * `perGram_sub_id_bound`: combines `perGramUnfold κ` and `perGramTail κ` (`Clock/FrameFacts.lean`)
     with planar biorthogonality `κ.biorth` to obtain a uniform threshold `D_G ≥ 1` and constant
     `C_G ≥ 0` such that for all `d ≥ D_G`,
     `‖perGram κ d i j - δ_{i,j}‖ ≤ C_G / d ^ 2` and `‖perGram κ d i j - δ_{i,j}‖ ≤ 1 / 4`.
   * `gram_entry_bound` and `gram_inv_sub_id_bound`: for any `2 × 2` matrix `G` within `1 / 4` of
     the identity with `‖G i j - δ_{i,j}‖ ≤ E`, the entries of `G` are bounded by `2`, `G` is
     invertible with `‖G⁻¹ i j‖ ≤ 3`, and the algebraic identity
     `G⁻¹ - I = G⁻¹ (I - G)` yields `‖G⁻¹ i j - δ_{i,j}‖ ≤ 6 * E`.
   * `perGram_inv_sub_id_bound`: specializes `gram_inv_sub_id_bound` to `perGram κ d` to prove
     `‖(perGram κ d)⁻¹ i j - δ_{i,j}‖ ≤ (6 * C_G) / d ^ 2` for all `d ≥ D_G`.

2. **Uniform `X_{-m, d}` membership and bound for the unnormalised dual rows `perLam0` (proved here)**:
   * `memLp_and_xNorm_perLam0`: uses the uniform cell supremum `Lam0B.perLam0_sup` and the weight
     integrability `Lam0B.integrable_jb_neg_two` (`Sub/PartIII-a_T21_c1_b_4.lean`) to prove that for
     every `m > 8` there exists `C_0 ≥ 0` such that for all `d ≥ 1` and `k : Fin 2`,
     `MemLp (perLam0 κ d k) 2 (B0579.cellMeasure d (-m))` and
     `xNorm d (-m) (perLam0 κ d k) ≤ ENNReal.ofReal C_0`.
   * `integrableOn_perLam0_mul_perE`: combines `perLam0Bound κ`, `perEBound κ`, and
     `FrameCont.perE_continuous` to prove that `perLam0 κ d k * perE κ d j` is integrable on
     `B0579.cell d` for all `d ≥ 1`.

3. **Unnormalised heat/dilation decomposition and `O(ν³ / θ(r))` error assembly (proved here)**:
   * Defines `physFrameLam0`, `physLam0DualHeat`, `movLam0DualHeat`, `movLam0DirectHeat`, and the
     moving-time Gram-inverse derivative `movGramInvDeriv`.
   * `movDirectHeat_eq_sum`: integrates the pointwise product-rule decomposition of `movLamDualHeat`
     against `perE κ d(r) j` on `movingCell` to express `movDirectHeat κ ν r i j` as
     `∑ k, (perGram κ d)⁻¹ i k * movLam0DirectHeat κ ν r k j + ∑ k, movGramInvDeriv κ ν r i k * perGram κ d k j`.
   * `norm_directHeatErr_le`: rewrites `directHeatErr κ P ν r i j` as the
     sum of the unnormalised oscillator tail `(G⁻¹)_{i,k} (movLam0DirectHeat_{k,j} - δ_{k,j} κ_k / θ)`,
     the Gram-inverse normalisation error `((G⁻¹)_{i,k} - δ_{i,k}) δ_{k,j} κ_k / θ`, and the
     Gram-inverse derivative term `(∂_z G⁻¹)_{i,k} G_{k,j}`, and bounds the total norm by
     `C_h * ν ^ 3 / clockTheta ν r` via `inv_cellLen_sq_eq_nu_cube_div_theta`.
   * `directHeatError_of` and `movLamDualHeatBound_of`: assemble `DirectHeatError κ`
     (`PartIII-a:T21/c5/2/1`) and `MovLamDualHeatBound κ` (`PartIII-a:T21/c5/3/1`) from the two
     unnormalised analytical leaves `MovLam0HeatDecomp κ` (`PartIII-a:T21/c5/2/1/1`) and
     `PerOscGramApprox κ` (`PartIII-a:T21/c5/2/1/2`) with zero sorry.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-! ## Unnormalised heat/dilation dual rows, direct heat pairing, and Gram-inverse derivative -/

/-- Physical-variable unnormalised dual test function `φ⁰_k(r, x) = a(r)⁻¹ Λ⁰_k(d(r), x / √a(r))`
associated with `perLam0 κ d(r) k` (SP 2898-2905). -/
def physFrameLam0 (κ : PlanarFrameKernels) (ν r : ℝ) (k : Fin 2) : ℝ × ℝ → ℂ :=
  physAdj (clockA ν r) (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k)

/-- Physical-variable time-derivative + viscous Laplacian part on the unnormalised dual row
`physFrameLam0 κ ν · k` (SP 2905-2912). -/
def physLam0DualHeat (κ : PlanarFrameKernels) (ν r : ℝ) (k : Fin 2) (x : ℝ × ℝ) : ℂ :=
  ladDt (fun r' x' => physFrameLam0 κ ν r' k x') r x +
    (ν : ℂ) * ladLapCx (physFrameLam0 κ ν r k) x

/-- Moving-variable heat/dilation + age-derivative part on the unnormalised dual row
`perLam0 κ d(r) k`: `a(r)² * movingPhi ν (physLam0DualHeat κ ν · k) r = (θ(r)⁻¹ D^# + ∂_z)(perLam0 κ d(r) k)`
(SP 2905-2912, 2991-2995). -/
def movLam0DualHeat (κ : PlanarFrameKernels) (ν r : ℝ) (k : Fin 2) (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    movingPhi ν (fun r' => physLam0DualHeat κ ν r' k) r y

/-- Unnormalised heat/dilation + age-derivative pairing on `perE κ d(r) j`:
`∫_{movingCell} movLam0DualHeat κ ν r k y * perE κ d(r) j y dy`, which by integration by parts and
the periodization identity `θ⁻¹ D(P_d e_j) - ∂_z(P_d e_j) = θ⁻¹ P_d(D e_j)` equals
`θ(r)⁻¹ * <perLam0 κ d(r) k, P_{d(r)}(D e_j)>_{cell d(r)}` (SP 2893, 2905-2912, 2991-2995). -/
def movLam0DirectHeat (κ : PlanarFrameKernels) (ν r : ℝ) (k j : Fin 2) : ℂ :=
  ∫ y in movingCell ν (ν ^ (-2 : ℝ)) r,
    movLam0DualHeat κ ν r k y * perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y

/-- Moving-time derivative `(∂_z (G(d(r))⁻¹)_{i, k})(r) = a(r)² * ∂_r ((perGram κ d(r))⁻¹ i k)`
of the Gram-matrix inverse (SP 2905-2912, 2991-2995). -/
def movGramInvDeriv (κ : PlanarFrameKernels) (ν r : ℝ) (i k : Fin 2) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    derivWithin (fun r' => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')))⁻¹ i k)
      (Set.Ici r) r

/-! ## Unnormalised analytical leaves for `DirectHeatError` (`PartIII-a:T21/c5/2/1`) -/

/-- **Analytical Leaf 1 (`PartIII-a:T21/c5/2/1/1`, `MovLam0HeatDecomp`, SP 2905-2912, 2990-2997)**:
By the product rule for `perLam κ d(r) i = ∑ k, (perGram κ d(r))⁻¹ i k * perLam0 κ d(r) k` and the
dual periodization identity `θ⁻¹ D^#(P_d λ_k) + ∂_z(P_d λ_k) = θ⁻¹ P_d(D^# λ_k)`:
1. `movLamDualHeat κ ν r i` decomposes into the Gram-weighted sum of `movLam0DualHeat κ ν r k` plus
   the Gram-inverse derivative sum `∑ k, movGramInvDeriv κ ν r i k * perLam0 κ d(r) k`;
2. `movLam0DualHeat κ ν r k` belongs to `X_{-m, d(r)}` with norm `O(1 / clockTheta ν r)` and is
   integrable against `perE κ d(r) j` on `B0579.cell d(r)`;
3. the Gram-inverse moving-time derivative satisfies
   `‖movGramInvDeriv κ ν r i k‖ ≤ C_0h / (clockTheta ν r * d(r) ^ 2)`.
Composed by task `PartIII-a:T21/c5/2/1` via `directHeatError_of`. -/
def MovLam0HeatDecomp (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ m : ℝ, 8 < m →
  ∃ C_0h D_0h : ℝ, 0 ≤ C_0h ∧ 1 ≤ D_0h ∧
    ∀ ν : ℝ, ν ∈ Ioc 0 1 →
    ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
      let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
      D_0h ≤ d →
      (∀ i : Fin 2, ∀ y : ℝ × ℝ,
        movLamDualHeat κ ν r i y =
          (∑ k : Fin 2, (perGram κ d)⁻¹ i k * movLam0DualHeat κ ν r k y) +
          (∑ k : Fin 2, movGramInvDeriv κ ν r i k * perLam0 κ d k y)) ∧
      (∀ k : Fin 2,
        MemLp (movLam0DualHeat κ ν r k) 2 (B0579.cellMeasure d (-m)) ∧
        xNorm d (-m) (movLam0DualHeat κ ν r k) ≤
          ENNReal.ofReal (C_0h / clockTheta ν r)) ∧
      (∀ k j : Fin 2,
        IntegrableOn (fun y => movLam0DualHeat κ ν r k y * perE κ d j y) (B0579.cell d)) ∧
      (∀ i k : Fin 2,
        ‖movGramInvDeriv κ ν r i k‖ ≤ C_0h / (clockTheta ν r * d ^ 2))

/-- **Analytical Leaf 2 (`PartIII-a:T21/c5/2/1/2`, `PerOscGramApprox`, SP 2893, 2905-2912, 2991-2995)**:
By integration by parts on the moving cell, the periodization identity
`θ⁻¹ D(P_d e_j) - ∂_z(P_d e_j) = θ⁻¹ P_d(D e_j)`, the planar subleading pairing
`⟨λ_k, D e_j⟩ = δ_{k,j} κ_k`, and the off-diagonal periodized tail `O(d⁻²)`, the unnormalised
direct heat pairing `movLam0DirectHeat κ ν r k j` approximates `δ_{k,j} (modeKappa P k / θ(r))`
to order `O(1 / (θ(r) * d(r)²))`.
Composed by task `PartIII-a:T21/c5/2/1` via `directHeatError_of`. -/
def PerOscGramApprox (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∀ (P : PlanarData), IsPlanarReference P →
  ∃ C_osc D_osc : ℝ, 0 ≤ C_osc ∧ 1 ≤ D_osc ∧
    ∀ ν : ℝ, ν ∈ Ioc 0 1 →
    ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
      let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
      D_osc ≤ d →
      ∀ k j : Fin 2,
        ‖movLam0DirectHeat κ ν r k j -
          (if k = j then modeKappa P k / (clockTheta ν r : ℂ) else 0)‖ ≤
          C_osc / (clockTheta ν r * d ^ 2)

namespace DirectHeatSub

open ComplCouplingSub

/-! ## Quantitative Gram-matrix and Gram-inverse `O(d⁻²)` bounds -/

/-- Quantitative `O(d⁻²)` bound on `perGram κ d - I₂` from `perGramUnfold κ` and `perGramTail κ`. -/
theorem perGram_sub_id_bound (κ : PlanarFrameKernels) :
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d → ∀ i j : Fin 2,
        ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ C_G / d ^ 2 ∧
        ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4 := by
  have h1 := perGramUnfold κ
  have h2 := perGramTail κ
  obtain ⟨D₁, hD₁⟩ := perGramNear_of κ h1 h2 (1 / 4) (by norm_num)
  obtain ⟨C, D₀, hC⟩ := h2
  refine ⟨max C 0, max (max D₀ D₁) 1, le_max_right _ _, le_max_right _ _, fun d hd i j => ?_⟩
  have hd0 : D₀ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
  have hd1 : D₁ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
  have hd_ge_one : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hdpos : 0 < d := by linarith
  refine ⟨?_, hD₁ d hd1 i j⟩
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
  refine (hC d hd0 i j).trans ?_
  gcongr
  exact le_max_left _ _

/-- Any `2 × 2` complex matrix within `1 / 4` of the identity has entries bounded by `2`. -/
theorem gram_entry_bound (G : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4) (i j : Fin 2) :
    ‖G i j‖ ≤ 2 := by
  have hij := h i j
  have htri := norm_sub_norm_le (G i j) (if i = j then 1 else 0)
  by_cases heq : i = j
  · subst heq
    simp only [↓reduceIte, norm_one] at hij htri
    linarith
  · simp only [heq, ↓reduceIte, sub_zero] at hij
    linarith

/-- Algebraic identity `(G⁻¹)_{i,j} - δ_{i,j} = ∑ k, (G⁻¹)_{i,k} * (δ_{k,j} - G_{k,j})` for an
invertible `2 × 2` matrix `G`. -/
theorem gram_inv_sub_id_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (hU : IsUnit G.det) (i j : Fin 2) :
    G⁻¹ i j - (if i = j then 1 else 0) =
      ∑ k : Fin 2, G⁻¹ i k * ((if k = j then 1 else 0) - G k j) := by
  have hmul := Matrix.nonsing_inv_mul G hU
  have hentry := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  simp_rw [mul_sub, Finset.sum_sub_distrib, hentry]
  congr 1
  rw [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

/-- If `G` is within `1 / 4` of the identity and `‖G i j - δ_{i,j}‖ ≤ E`, then
`‖G⁻¹ i j - δ_{i,j}‖ ≤ 6 * E`. -/
theorem gram_inv_sub_id_bound (G : Matrix (Fin 2) (Fin 2) ℂ) {E : ℝ}
    (h14 : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ 1 / 4)
    (hE : ∀ i j : Fin 2, ‖G i j - (if i = j then 1 else 0)‖ ≤ E) (i j : Fin 2) :
    ‖G⁻¹ i j - (if i = j then 1 else 0)‖ ≤ 6 * E := by
  obtain ⟨hU, hinv⟩ := gram_inv_bound G h14
  rw [gram_inv_sub_id_eq G hU i j, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_sub_rev (if (0 : Fin 2) = j then 1 else 0),
    norm_sub_rev (if (1 : Fin 2) = j then 1 else 0)]
  have h0 := hinv i 0
  have h1 := hinv i 1
  have e0 := hE 0 j
  have e1 := hE 1 j
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) e0
  nlinarith [norm_nonneg (G⁻¹ i 0), norm_nonneg (G⁻¹ i 1),
    norm_nonneg (G 0 j - if (0 : Fin 2) = j then 1 else 0),
    norm_nonneg (G 1 j - if (1 : Fin 2) = j then 1 else 0),
    mul_le_mul h0 e0 (norm_nonneg _) (by norm_num),
    mul_le_mul h1 e1 (norm_nonneg _) (by norm_num)]

/-- Uniform `O(d⁻²)` bound on `(perGram κ d)⁻¹ - I₂`, together with entry bounds on `perGram κ d`
and `(perGram κ d)⁻¹`. -/
theorem perGram_inv_sub_id_bound (κ : PlanarFrameKernels) :
    ∃ C_G D_G : ℝ, 0 ≤ C_G ∧ 1 ≤ D_G ∧
      ∀ d : ℝ, D_G ≤ d →
        IsUnit (perGram κ d).det ∧
        (∀ i j : Fin 2, ‖perGram κ d i j‖ ≤ 2) ∧
        (∀ i j : Fin 2, ‖(perGram κ d)⁻¹ i j‖ ≤ 3) ∧
        (∀ i j : Fin 2, ‖(perGram κ d)⁻¹ i j - (if i = j then 1 else 0)‖ ≤ (6 * C_G) / d ^ 2) := by
  obtain ⟨C_G, D_G, hCG, hDG, hG⟩ := perGram_sub_id_bound κ
  refine ⟨C_G, D_G, hCG, hDG, fun d hd => ?_⟩
  have h14 : ∀ i j : Fin 2, ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ 1 / 4 :=
    fun i j => (hG d hd i j).2
  have hE : ∀ i j : Fin 2, ‖perGram κ d i j - (if i = j then 1 else 0)‖ ≤ C_G / d ^ 2 :=
    fun i j => (hG d hd i j).1
  obtain ⟨hU, hinv⟩ := gram_inv_bound (perGram κ d) h14
  refine ⟨hU, gram_entry_bound (perGram κ d) h14, hinv, fun i j => ?_⟩
  have hbd := gram_inv_sub_id_bound (perGram κ d) h14 hE i j
  exact hbd.trans (by ring_nf; rfl)

/-! ## Uniform `X_{-m, d}` membership and bound for `perLam0`, and cell integrability -/

/-- For every `m > 8`, the unnormalised periodized dual rows `perLam0 κ d k` belong to
`MemLp · 2 (B0579.cellMeasure d (-m))` with `xNorm d (-m)` bounded uniformly for all `d ≥ 1`. -/
theorem memLp_and_xNorm_perLam0 (κ : PlanarFrameKernels) {m : ℝ} (hm : 8 < m) :
    ∃ C_0 : ℝ, 0 ≤ C_0 ∧
      ∀ d : ℝ, 1 ≤ d → ∀ k : Fin 2,
        MemLp (perLam0 κ d k) 2 (B0579.cellMeasure d (-m)) ∧
        xNorm d (-m) (perLam0 κ d k) ≤ ENNReal.ofReal C_0 := by
  obtain ⟨B, hB0, hB⟩ := Lam0B.perLam0_sup κ
  set G : ℝ × ℝ → ℝ := fun y => B * B0579.jb y ^ ((-m) / 2) with hG
  have hGmem : MemLp G 2 volume := by
    have hcont : Continuous G :=
      continuous_const.mul (B0579.continuous_jb_rpow _)
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine (Lam0B.integrable_jb_neg_two.const_mul (B ^ 2)).mono'
      (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hj0 : 0 ≤ B0579.jb y := (B0579.jb_pos y).le
    have e1 : (B0579.jb y ^ ((-m) / 2)) ^ 2 = B0579.jb y ^ (-m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0]
      congr 1; push_cast; ring
    have e2 : B0579.jb y ^ (-m) ≤ B0579.jb y ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (Lam0B.jb_ge_one y) (by linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _), hG]
    simp only
    rw [mul_pow, e1]
    exact mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
  set C_0 : ℝ := (eLpNorm G 2 volume).toReal with hC0
  have hGfin : eLpNorm G 2 volume ≠ ⊤ := hGmem.2.ne
  refine ⟨C_0, ENNReal.toReal_nonneg, fun d hd k => ?_⟩
  have hd0 : 0 < d := by linarith
  have hFc : Continuous (perLam0 κ d k) := Lam0B.perLam0_continuous κ hd0 k
  have hle : xNorm d (-m) (perLam0 κ d k) ≤ ENNReal.ofReal C_0 := by
    change eLpNorm (perLam0 κ d k) 2 (B0579.cellMeasure d (-m)) ≤ ENNReal.ofReal C_0
    rw [Lam0B.eLpNorm_cellMeasure_cx]
    have hmono : eLpNorm (fun x => ((B0579.jb x ^ ((-m) / 2) : ℝ) : ℂ) * perLam0 κ d k x) 2
        (volume.restrict (B0579.cell d)) ≤ eLpNorm G 2 (volume.restrict (B0579.cell d)) := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell d)] with y hy
      have h1 := hB d hd k y hy
      have hj0 : 0 ≤ B0579.jb y ^ ((-m) / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
      have hGnn : 0 ≤ G y := mul_nonneg hB0 hj0
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hj0, Real.norm_of_nonneg hGnn]
      dsimp [G]
      linarith [mul_le_mul_of_nonneg_left h1 hj0]
    refine hmono.trans ?_
    refine (eLpNorm_mono_measure G Measure.restrict_le_self).trans ?_
    rw [hC0, ENNReal.ofReal_toReal hGfin]
  refine ⟨⟨hFc.aestronglyMeasurable, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, hle⟩

/-- For `d ≥ 1`, `perLam0 κ d k * perE κ d j` is integrable on `B0579.cell d`. -/
theorem integrableOn_perLam0_mul_perE (κ : PlanarFrameKernels) {d : ℝ} (hd : 1 ≤ d)
    (k j : Fin 2) :
    IntegrableOn (fun y => perLam0 κ d k y * perE κ d j y) (B0579.cell d) := by
  have hm : (8 : ℝ) < 9 := by norm_num
  obtain ⟨KE, hKE⟩ := perEBound κ 9 hm
  obtain ⟨KL, hKL⟩ := perLam0Bound κ 9 hm
  have hEfin : xNorm d 9 (perE κ d j) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hKE d hd j)
  have hEm : AEStronglyMeasurable (perE κ d j) (volume.restrict (B0579.cell d)) :=
    (FrameCont.perE_continuous κ (by linarith) j).aestronglyMeasurable
  exact (hKL d hd k (perE κ d j) hEm hEfin).1

/-! ## Membership and `X_{-m, d}` bound for `movLamDualHeat`, and integral decomposition -/

/-- From the pointwise decomposition of `movLamDualHeat` and the `X_{-m, d}` bounds on
`movLam0DualHeat` and `perLam0`, `movLamDualHeat κ ν r i` belongs to
`MemLp · 2 (B0579.cellMeasure d (-m))` with `xNorm` bounded by `O(1 / clockTheta ν r)`. -/
theorem memLp_and_xNorm_movLamDualHeat (κ : PlanarFrameKernels) {ν r m C_0h C_0 : ℝ} (i : Fin 2)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hθ : 1 ≤ clockTheta ν r) (hC0h : 0 ≤ C_0h) (hC0 : 0 ≤ C_0)
    (hGinv : ∀ k : Fin 2, ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k‖ ≤ 3)
    (hGder : ∀ k : Fin 2,
      ‖movGramInvDeriv κ ν r i k‖ ≤
        C_0h / (clockTheta ν r * (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2))
    (hpt : ∀ y : ℝ × ℝ,
      movLamDualHeat κ ν r i y =
        (∑ k : Fin 2,
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k * movLam0DualHeat κ ν r k y) +
        (∑ k : Fin 2,
          movGramInvDeriv κ ν r i k * perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k y))
    (h0h : ∀ k : Fin 2,
      MemLp (movLam0DualHeat κ ν r k) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m) (movLam0DualHeat κ ν r k) ≤
        ENNReal.ofReal (C_0h / clockTheta ν r))
    (hlam0 : ∀ k : Fin 2,
      MemLp (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)) ∧
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (-m)
        (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k) ≤ ENNReal.ofReal C_0) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    MemLp (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) ∧
    xNorm d (-m) (movLamDualHeat κ ν r i) ≤
      ENNReal.ofReal ((6 * C_0h + 2 * C_0h * C_0) * (1 / clockTheta ν r)) := by
  intro d
  have hfeq : movLamDualHeat κ ν r i =
      (((perGram κ d)⁻¹ i 0 • movLam0DualHeat κ ν r 0) +
        ((perGram κ d)⁻¹ i 1 • movLam0DualHeat κ ν r 1)) +
      ((movGramInvDeriv κ ν r i 0 • perLam0 κ d 0) +
        (movGramInvDeriv κ ν r i 1 • perLam0 κ d 1)) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hpt y, Fin.sum_univ_two, Fin.sum_univ_two]
  have hm00 : MemLp ((perGram κ d)⁻¹ i 0 • movLam0DualHeat κ ν r 0) 2
      (B0579.cellMeasure d (-m)) := (h0h 0).1.const_smul _
  have hm01 : MemLp ((perGram κ d)⁻¹ i 1 • movLam0DualHeat κ ν r 1) 2
      (B0579.cellMeasure d (-m)) := (h0h 1).1.const_smul _
  have hm10 : MemLp (movGramInvDeriv κ ν r i 0 • perLam0 κ d 0) 2
      (B0579.cellMeasure d (-m)) := (hlam0 0).1.const_smul _
  have hm11 : MemLp (movGramInvDeriv κ ν r i 1 • perLam0 κ d 1) 2
      (B0579.cellMeasure d (-m)) := (hlam0 1).1.const_smul _
  have hmem : MemLp (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) := by
    rw [hfeq]
    exact (hm00.add hm01).add (hm10.add hm11)
  refine ⟨hmem, ?_⟩
  change eLpNorm (movLamDualHeat κ ν r i) 2 (B0579.cellMeasure d (-m)) ≤ _
  rw [hfeq]
  have htri1 := eLpNorm_add_le (hm00.add hm01).aestronglyMeasurable
    (hm10.add hm11).aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htri2 := eLpNorm_add_le hm00.aestronglyMeasurable hm01.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htri3 := eLpNorm_add_le hm10.aestronglyMeasurable hm11.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hbd_0 : ∀ k : Fin 2,
      eLpNorm ((perGram κ d)⁻¹ i k • movLam0DualHeat κ ν r k) 2
        (B0579.cellMeasure d (-m)) ≤ ENNReal.ofReal (3 * (C_0h / clockTheta ν r)) := by
    intro k
    rw [eLpNorm_const_smul, ← ofReal_norm]
    refine (mul_le_mul (ENNReal.ofReal_le_ofReal (hGinv k)) (h0h k).2 zero_le
      zero_le).trans ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hθpos : 0 < clockTheta ν r := by linarith
  have hGder_theta : ∀ k : Fin 2, ‖movGramInvDeriv κ ν r i k‖ ≤ C_0h / clockTheta ν r := by
    intro k
    refine (hGder k).trans ?_
    exact div_le_div_of_nonneg_left hC0h hθpos (by nlinarith)
  have hbd_1 : ∀ k : Fin 2,
      eLpNorm (movGramInvDeriv κ ν r i k • perLam0 κ d k) 2
        (B0579.cellMeasure d (-m)) ≤ ENNReal.ofReal ((C_0h / clockTheta ν r) * C_0) := by
    intro k
    rw [eLpNorm_const_smul, ← ofReal_norm]
    refine (mul_le_mul (ENNReal.ofReal_le_ofReal (hGder_theta k)) (hlam0 k).2 zero_le
      zero_le).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  refine (htri1.trans (add_le_add htri2 htri3)).trans ?_
  refine (add_le_add (add_le_add (hbd_0 0) (hbd_0 1)) (add_le_add (hbd_1 0) (hbd_1 1))).trans ?_
  have hpos1 : 0 ≤ 3 * (C_0h / clockTheta ν r) := by positivity
  have hpos2 : 0 ≤ (C_0h / clockTheta ν r) * C_0 := by positivity
  rw [← ENNReal.ofReal_add hpos1 hpos1, ← ENNReal.ofReal_add hpos2 hpos2,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by ring_nf; linarith)

/-- Integral decomposition of `movDirectHeat κ ν r i j` into the Gram-weighted unnormalised heat
pairing plus the Gram-inverse derivative pairing. -/
theorem movDirectHeat_eq_sum (κ : PlanarFrameKernels) {ν r : ℝ} (i j : Fin 2)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hpt : ∀ y : ℝ × ℝ,
      movLamDualHeat κ ν r i y =
        (∑ k : Fin 2,
          (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k * movLam0DualHeat κ ν r k y) +
        (∑ k : Fin 2,
          movGramInvDeriv κ ν r i k * perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k y))
    (hint0 : ∀ k : Fin 2,
      IntegrableOn
        (fun y => movLam0DualHeat κ ν r k y *
          perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y)
        (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))) :
    let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
    movDirectHeat κ ν r i j =
      (∑ k : Fin 2, (perGram κ d)⁻¹ i k * movLam0DirectHeat κ ν r k j) +
      (∑ k : Fin 2, movGramInvDeriv κ ν r i k * perGram κ d k j) := by
  intro d
  unfold movDirectHeat movLam0DirectHeat movingCell
  have hfeq : (fun y => movLamDualHeat κ ν r i y * perE κ d j y) =
      fun y =>
        (∑ k : Fin 2, (perGram κ d)⁻¹ i k * (movLam0DualHeat κ ν r k y * perE κ d j y)) +
        (∑ k : Fin 2, movGramInvDeriv κ ν r i k * (perLam0 κ d k y * perE κ d j y)) := by
    funext y
    rw [hpt y, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring
  have hint_a : IntegrableOn
      (fun y => ∑ k : Fin 2, (perGram κ d)⁻¹ i k * (movLam0DualHeat κ ν r k y * perE κ d j y))
      (B0579.cell d) :=
    integrable_finsetSum _ fun k _ => (hint0 k).const_mul _
  have hint_b : IntegrableOn
      (fun y => ∑ k : Fin 2, movGramInvDeriv κ ν r i k * (perLam0 κ d k y * perE κ d j y))
      (B0579.cell d) :=
    integrable_finsetSum _ fun k _ => (integrableOn_perLam0_mul_perE κ hd k j).const_mul _
  rw [hfeq, integral_add hint_a hint_b, integral_finsetSum, integral_finsetSum]
  · congr 1
    · refine Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    · refine Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  · intro k _
    exact (integrableOn_perLam0_mul_perE κ hd k j).const_mul _
  · intro k _
    exact (hint0 k).const_mul _

/-- Norm of `modeKappa P k` equals `‖P.kappa‖` for both `k ∈ {0, 1}`. -/
theorem norm_modeKappa (P : PlanarData) (k : Fin 2) :
    ‖modeKappa P k‖ = ‖P.kappa‖ := by
  unfold modeKappa
  fin_cases k <;> simp

/-- Norm bound on `directHeatErr κ P ν r i j` from the unnormalised heat pairing approximation, the
Gram-inverse `O(d⁻²)` approximation, and the Gram-inverse derivative bound. -/
theorem norm_directHeatErr_le (κ : PlanarFrameKernels) (P : PlanarData) {ν r C_G C_0h C_osc : ℝ}
    (i j : Fin 2) (hν : ν ∈ Ioc 0 1) (hr : 0 ≤ r) (hθ : 1 ≤ clockTheta ν r)
    (hCG : 0 ≤ C_G) (hC0h : 0 ≤ C_0h) (hCosc : 0 ≤ C_osc)
    (hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hG : ∀ k l : Fin 2, ‖perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k l‖ ≤ 2)
    (hGinv : ∀ k l : Fin 2, ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ k l‖ ≤ 3)
    (hGsub : ∀ k l : Fin 2,
      ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ k l - (if k = l then 1 else 0)‖ ≤
        (6 * C_G) / (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2)
    (hGder : ∀ k : Fin 2,
      ‖movGramInvDeriv κ ν r i k‖ ≤
        C_0h / (clockTheta ν r * (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2))
    (hosc : ∀ k : Fin 2,
      ‖movLam0DirectHeat κ ν r k j -
        (if k = j then modeKappa P k / (clockTheta ν r : ℂ) else 0)‖ ≤
        C_osc / (clockTheta ν r * (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) ^ 2))
    (hsum : movDirectHeat κ ν r i j =
      (∑ k : Fin 2,
        (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i k * movLam0DirectHeat κ ν r k j) +
      (∑ k : Fin 2,
        movGramInvDeriv κ ν r i k * perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) k j)) :
    ‖directHeatErr κ P ν r i j‖ ≤
      (6 * C_osc + 12 * C_G * ‖P.kappa‖ + 4 * C_0h) * ν ^ 3 / clockTheta ν r := by
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
  set D_k : Fin 2 → ℂ := fun k =>
    if k = j then modeKappa P k / (clockTheta ν r : ℂ) else 0
  have hdiag : (if i = j then modeKappa P i / (clockTheta ν r : ℂ) else 0) =
      ∑ k : Fin 2, (if i = k then (1 : ℂ) else 0) * D_k k := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [D_k]
  have herr : directHeatErr κ P ν r i j =
      (∑ k : Fin 2,
        ((perGram κ d)⁻¹ i k * (movLam0DirectHeat κ ν r k j - D_k k) +
          ((perGram κ d)⁻¹ i k - (if i = k then 1 else 0)) * D_k k)) +
      (∑ k : Fin 2, movGramInvDeriv κ ν r i k * perGram κ d k j) := by
    unfold directHeatErr
    rw [hsum, hdiag, add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  have hθpos : 0 < clockTheta ν r := by linarith
  have hdpos : 0 < d := by linarith
  have hDk_bound : ∀ k : Fin 2, ‖D_k k‖ ≤ ‖P.kappa‖ := by
    intro k
    dsimp [D_k]
    split_ifs with hkj
    · rw [norm_div, norm_modeKappa, Complex.norm_real, Real.norm_of_nonneg hθpos.le]
      exact div_le_self (norm_nonneg _) hθ
    · rw [norm_zero]
      exact norm_nonneg _
  have hosc_d2 : ∀ k : Fin 2, ‖movLam0DirectHeat κ ν r k j - D_k k‖ ≤ C_osc / d ^ 2 := by
    intro k
    refine (hosc k).trans ?_
    exact div_le_div_of_nonneg_left hCosc (by positivity) (by nlinarith [sq_pos_of_pos hdpos])
  have hder_d2 : ∀ k : Fin 2, ‖movGramInvDeriv κ ν r i k‖ ≤ C_0h / d ^ 2 := by
    intro k
    refine (hGder k).trans ?_
    exact div_le_div_of_nonneg_left hC0h (by positivity) (by nlinarith [sq_pos_of_pos hdpos])
  have hterm1 : ∀ k : Fin 2,
      ‖(perGram κ d)⁻¹ i k * (movLam0DirectHeat κ ν r k j - D_k k) +
        ((perGram κ d)⁻¹ i k - (if i = k then 1 else 0)) * D_k k‖ ≤
      (3 * C_osc + 6 * C_G * ‖P.kappa‖) / d ^ 2 := by
    intro k
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have a1 := hGinv i k
    have b1 := hosc_d2 k
    have a2 := hGsub i k
    have b2 := hDk_bound k
    have hprod1 : ‖(perGram κ d)⁻¹ i k‖ * ‖movLam0DirectHeat κ ν r k j - D_k k‖ ≤
        3 * (C_osc / d ^ 2) :=
      mul_le_mul a1 b1 (norm_nonneg _) (by norm_num)
    have hprod2 : ‖(perGram κ d)⁻¹ i k - (if i = k then 1 else 0)‖ * ‖D_k k‖ ≤
        ((6 * C_G) / d ^ 2) * ‖P.kappa‖ :=
      mul_le_mul a2 b2 (norm_nonneg _) (by positivity)
    calc ‖(perGram κ d)⁻¹ i k‖ * ‖movLam0DirectHeat κ ν r k j - D_k k‖ +
          ‖(perGram κ d)⁻¹ i k - (if i = k then 1 else 0)‖ * ‖D_k k‖
        ≤ 3 * (C_osc / d ^ 2) + ((6 * C_G) / d ^ 2) * ‖P.kappa‖ := add_le_add hprod1 hprod2
      _ = (3 * C_osc + 6 * C_G * ‖P.kappa‖) / d ^ 2 := by ring
  have hterm2 : ∀ k : Fin 2,
      ‖movGramInvDeriv κ ν r i k * perGram κ d k j‖ ≤ (2 * C_0h) / d ^ 2 := by
    intro k
    rw [norm_mul]
    have a1 := hder_d2 k
    have b1 := hG k j
    calc ‖movGramInvDeriv κ ν r i k‖ * ‖perGram κ d k j‖
        ≤ (C_0h / d ^ 2) * 2 := mul_le_mul a1 b1 (norm_nonneg _) (by positivity)
      _ = (2 * C_0h) / d ^ 2 := by ring
  have hbd : ‖directHeatErr κ P ν r i j‖ ≤
      (6 * C_osc + 12 * C_G * ‖P.kappa‖ + 4 * C_0h) * (1 / d ^ 2) := by
    rw [herr, Fin.sum_univ_two, Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
    have t10 := hterm1 0
    have t11 := hterm1 1
    have t20 := hterm2 0
    have t21 := hterm2 1
    calc _ ≤ (3 * C_osc + 6 * C_G * ‖P.kappa‖) / d ^ 2 +
            (3 * C_osc + 6 * C_G * ‖P.kappa‖) / d ^ 2 +
            ((2 * C_0h) / d ^ 2 + (2 * C_0h) / d ^ 2) :=
          add_le_add (add_le_add t10 t11) (add_le_add t20 t21)
      _ = (6 * C_osc + 12 * C_G * ‖P.kappa‖ + 4 * C_0h) * (1 / d ^ 2) := by ring
  refine hbd.trans ?_
  have hd_eq : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
    inv_cellLen_sq_eq_nu_cube_div_theta hν.1 hr
  rw [hd_eq, mul_div_assoc]

/-! ## Conditional assemblies of `DirectHeatError` and `MovLamDualHeatBound` -/

/-- **Conditional assembly of `MovLamDualHeatBound` (`PartIII-a:T21/c5/3/1`)** from
`MovLam0HeatDecomp κ` with zero sorry. -/
theorem movLamDualHeatBound_of (κ : PlanarFrameKernels)
    (hDecomp : MovLam0HeatDecomp κ) : MovLamDualHeatBound κ := by
  intro hκ m hm
  obtain ⟨C_G, D_G, hCG, hDG, hGram⟩ := perGram_inv_sub_id_bound κ
  obtain ⟨C_0, hC0, hLam0⟩ := memLp_and_xNorm_perLam0 κ hm
  obtain ⟨C_0h, D_0h, hC0h, hD0h, hD⟩ := hDecomp hκ m hm
  set D := max D_G D_0h
  have hD_ge_one : 1 ≤ D := le_trans hDG (le_max_left _ _)
  have hD_nonneg : 0 ≤ D := by linarith
  refine ⟨6 * C_0h + 2 * C_0h * C_0, 1, by positivity, le_rfl, fun b hb => ?_⟩
  refine ⟨1 / (D + 1) ^ 2, by positivity, fun ν hν r hr hbr i => ?_⟩
  have hν1 : ν ∈ Ioc 0 1 := ⟨hν.1, hν.2.trans (by
    rw [div_le_one (by positivity)]
    nlinarith)⟩
  have hθ : 1 ≤ clockTheta ν r := le_trans hb hbr
  have hdD : D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    cellLen_ge hD_nonneg hν.1 hν.2 hb hr hbr
  have hdDG : D_G ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_left _ _) hdD
  have hdD0h : D_0h ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_right _ _) hdD
  have hd1 : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans hD_ge_one hdD
  obtain ⟨-, -, hGinv, -⟩ := hGram _ hdDG
  obtain ⟨hpt, h0h, -, hGder⟩ := hD ν hν1 r hr hθ hdD0h
  exact memLp_and_xNorm_movLamDualHeat κ i hd1 hθ hC0h hC0 (hGinv i) (hGder i) (hpt i) h0h
    (hLam0 _ hd1)

/-- **Conditional assembly of `DirectHeatError` (`PartIII-a:T21/c5/2/1`)** from
`MovLam0HeatDecomp κ` and `PerOscGramApprox κ` with zero sorry. -/
theorem directHeatError_of (κ : PlanarFrameKernels)
    (hDecomp : MovLam0HeatDecomp κ)
    (hOsc : PerOscGramApprox κ) : DirectHeatError κ := by
  intro hκ P hP m hm
  obtain ⟨C_G, D_G, hCG, hDG, hGram⟩ := perGram_inv_sub_id_bound κ
  obtain ⟨C_0, hC0, hLam0⟩ := memLp_and_xNorm_perLam0 κ hm
  obtain ⟨C_0h, D_0h, hC0h, hD0h, hD⟩ := hDecomp hκ m hm
  obtain ⟨C_osc, D_osc, hCosc, hDosc, hO⟩ := hOsc hκ P hP
  set D := max (max D_G D_0h) D_osc
  have hD_ge_one : 1 ≤ D :=
    le_trans hDG (le_trans (le_max_left _ _) (le_max_left _ _))
  have hD_nonneg : 0 ≤ D := by linarith
  set C_h := 6 * C_osc + 12 * C_G * ‖P.kappa‖ + 4 * C_0h
  refine ⟨C_h, 1, by positivity, le_rfl, fun b hb => ?_⟩
  refine ⟨1 / (D + 1) ^ 2, by positivity, fun ν hν r hr hbr i j => ?_⟩
  have hν1 : ν ∈ Ioc 0 1 := ⟨hν.1, hν.2.trans (by
    rw [div_le_one (by positivity)]
    nlinarith)⟩
  have hθ : 1 ≤ clockTheta ν r := le_trans hb hbr
  have hdD : D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    cellLen_ge hD_nonneg hν.1 hν.2 hb hr hbr
  have hdDG : D_G ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdD
  have hdD0h : D_0h ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdD
  have hdDosc : D_osc ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans (le_max_right _ _) hdD
  have hd1 : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    le_trans hD_ge_one hdD
  obtain ⟨-, hG, hGinv, hGsub⟩ := hGram _ hdDG
  obtain ⟨hpt, h0h, hint0, hGder⟩ := hD ν hν1 r hr hθ hdD0h
  have hosc := hO ν hν1 r hr hθ hdDosc
  have hmem := (memLp_and_xNorm_movLamDualHeat κ i hd1 hθ hC0h hC0 (hGinv i) (hGder i)
    (hpt i) h0h (hLam0 _ hd1)).1
  have hsum := movDirectHeat_eq_sum κ i j hd1 (hpt i) (fun k => hint0 k j)
  have hbd := norm_directHeatErr_le κ P i j hν1 hr hθ hCG hC0h hCosc hd1 hG hGinv hGsub
    (hGder i) (fun k => hosc k j) hsum
  exact ⟨hmem, hbd⟩

end DirectHeatSub

/-- **Conditional assembly of `DirectHeatError` (`PartIII-a:T21/c5/2/1`)** from
`MovLam0HeatDecomp κ` (`PartIII-a:T21/c5/2/1/1`) and `PerOscGramApprox κ`
(`PartIII-a:T21/c5/2/1/2`) with zero sorry. -/
theorem directHeatError_of (κ : PlanarFrameKernels)
    (hDecomp : MovLam0HeatDecomp κ)
    (hOsc : PerOscGramApprox κ) : DirectHeatError κ :=
  DirectHeatSub.directHeatError_of κ hDecomp hOsc

end UnforcedLeray.Short.IIIa
