import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.XNormSplit
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.MovingCalc

/-!
# Part III-a, task `PartIII-a:T21/c5/3/1` sub-infrastructure: moving heat/dilation dual bound (`MovLamDualHeatBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2896-2912 and
2990-2997 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Proved infrastructure in this file

1. **`X_{-m, d}` bounds for cell-bounded fields (`eLpNorm_cellMeasure_neg_le_of_cell_bdd`,
   `memLp_and_xNorm_neg_le_of_cell_bdd`)**:
   Any measurable field `F : ℝ × ℝ → ℂ` bounded by `B ≥ 0` on `B0579.cell d` belongs to
   `MemLp F 2 (B0579.cellMeasure d (-m))` for `m > 1` with
   `xNorm d (-m) F ≤ ENNReal.ofReal ((B0592.weightConst m).toReal * B)`.
2. **Periodization continuity, cell sup bound, and `X_{-m, d}` bound for `O(|y|⁻²)` planar
   profiles (`perSum_continuous_of_inv_sq_decay`, `perSum_cell_sup_of_inv_sq_decay`,
   `memLp_and_xNorm_perSum_of_inv_sq_decay`)**:
   Any continuous planar profile `Ψ : ℝ × ℝ → ℂ` with `‖Ψ z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2`
   has continuous `d`-periodization `perSum d Ψ` for `d > 0`, uniform cell sup bound on
   `B0579.cell d` for `d ≥ 1`, and uniform `X_{-m, d}` norm bound for `m > 1`, `d ≥ 1`.
   In particular this applies to `perLam0 κ d j` (`memLp_and_xNorm_perLam0_neg`).
3. **Physical-to-moving periodization, Gram inverse bound, and Laplacian scaling identities
   (`physAdj_perSum_eq_perSum_physAdj`, `physFrameLam0_eq_perSum_physAdj`,
   `physFrameLam_eq_sum_perGram_inv`, `perGram_inv_entry_bound`, `movPlanarLap_physAdj_eq`)**:
   Shows that `physFrameLam0 κ ν r j` is the `c = ν⁻²`-periodization (with `r`-independent
   physical period `c`) of `physAdj (clockA ν r) (κ.lamP j)`, proves the uniform bound
   `‖(perGram κ d)⁻¹ i j‖ ≤ 3` for large `d`, and proves the moving pullback identity for the
   viscous Laplacian of a dilated planar profile via `E0.lapCx_scale`.
4. **Conditional assembly (`movLamDualHeatBound_of`)**:
   Assembles `MovLamDualHeatBound κ` from the two analytical leaves
   `SeedLamPDSharpDecay κ` (`PartIII-a:T21/c5/3/1/1`, the `D^#` periodization identity and `O(|y|⁻²)`
   decay of `D^#(κ.lamP j)`) and `PerGramInvHeatSplit κ` (`PartIII-a:T21/c5/3/1/2`, the product-rule
   split of `perLam = G(d)⁻¹ perLam0` with `‖(G⁻¹)_z‖ = O(θ(r)⁻¹)` for large `d(r)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace ComplCouplingHeat

/-! ## 1. `X_{-m, d}` bounds for cell-bounded fields -/

/-- Any field `F` bounded by `B ≥ 0` on `B0579.cell d` has `X_{-m, d}` norm at most
`(B0592.weightConst m).toReal * B` for `m > 1`. -/
theorem eLpNorm_cellMeasure_neg_le_of_cell_bdd {m d B : ℝ} (hm : 1 < m) (_hB0 : 0 ≤ B)
    {F : ℝ × ℝ → ℂ} (hB : ∀ y ∈ B0579.cell d, ‖F y‖ ≤ B) :
    eLpNorm F 2 (B0579.cellMeasure d (-m)) ≤
      ENNReal.ofReal ((B0592.weightConst m).toReal * B) := by
  have hWfin : B0592.weightConst m ≠ ⊤ := (B0592.weightConst_lt_top hm).ne
  have hmass : B0579.cellMeasure d (-m) Set.univ ≤
      ∫⁻ x, ENNReal.ofReal (B0579.jb x ^ (-m)) := by
    rw [B0579.cellMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_restrict MeasurableSet.univ, Set.univ_inter]
    exact setLIntegral_le_lintegral _ _
  have huniv : B0579.cellMeasure d (-m) Set.univ ^ (2⁻¹ : ℝ) ≤ B0592.weightConst m := by
    unfold B0592.weightConst
    rw [one_div]
    exact ENNReal.rpow_le_rpow hmass (by norm_num)
  have hae_cell : ∀ᵐ y ∂(B0579.cellMeasure d (-m)), y ∈ B0579.cell d :=
    (B0579.cellMeasure_ac d (-m)).ae_le (ae_restrict_mem (B0579.measurableSet_cell d))
  have hae_bdd : ∀ᵐ y ∂(B0579.cellMeasure d (-m)), ‖F y‖ₑ ≤ ENNReal.ofReal B := by
    filter_upwards [hae_cell] with y hy
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB y hy)
  have hbound := eLpNorm_le_of_ae_enorm_bound hae_bdd (p := (2 : ℝ≥0∞))
  simp only [ENNReal.toReal_ofNat, smul_eq_mul] at hbound
  calc eLpNorm F 2 (B0579.cellMeasure d (-m))
      ≤ ENNReal.ofReal B * B0579.cellMeasure d (-m) Set.univ ^ (2⁻¹ : ℝ) := hbound
    _ = B0579.cellMeasure d (-m) Set.univ ^ (2⁻¹ : ℝ) * ENNReal.ofReal B := mul_comm _ _
    _ ≤ B0592.weightConst m * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal ((B0592.weightConst m).toReal * B) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hWfin]

/-- Any a.e. strongly measurable field `F` on `B0579.cell d` bounded by `B ≥ 0` on `B0579.cell d`
belongs to `MemLp F 2 (B0579.cellMeasure d (-m))` for `m > 1` and satisfies
`xNorm d (-m) F ≤ ENNReal.ofReal ((B0592.weightConst m).toReal * B)`. -/
theorem memLp_and_xNorm_neg_le_of_cell_bdd {m d B : ℝ} (hm : 1 < m) (hB0 : 0 ≤ B)
    {F : ℝ × ℝ → ℂ} (hFm : AEStronglyMeasurable F (volume.restrict (B0579.cell d)) )
    (hB : ∀ y ∈ B0579.cell d, ‖F y‖ ≤ B) :
    MemLp F 2 (B0579.cellMeasure d (-m)) ∧
    xNorm d (-m) F ≤ ENNReal.ofReal ((B0592.weightConst m).toReal * B) := by
  have hle := eLpNorm_cellMeasure_neg_le_of_cell_bdd hm hB0 hB
  refine ⟨⟨hFm.mono_ac (B0579.cellMeasure_ac d (-m)), lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩,
    hle⟩

/-- Scaling of `xNorm d (-m)` under multiplication by a complex constant `c : ℂ`. -/
theorem xNorm_const_mul_le {m d K : ℝ} {c : ℂ} {F : ℝ × ℝ → ℂ}
    (_hK0 : 0 ≤ K) (hF : xNorm d (-m) F ≤ ENNReal.ofReal K) :
    xNorm d (-m) (fun y => c * F y) ≤ ENNReal.ofReal (‖c‖ * K) := by
  unfold xNorm at hF ⊢
  have heq : (fun y => c * F y) = c • F := rfl
  rw [heq, eLpNorm_const_smul]
  calc ‖c‖ₑ * eLpNorm F 2 (B0579.cellMeasure d (-m))
      ≤ ENNReal.ofReal ‖c‖ * ENNReal.ofReal K := by
        rw [← ofReal_norm]
        gcongr
    _ = ENNReal.ofReal (‖c‖ * K) := (ENNReal.ofReal_mul (norm_nonneg c)).symm

/-- Triangle inequality in `X_{-m, d}` with explicit `ENNReal.ofReal` bounds. -/
theorem memLp_and_xNorm_add_le {m d K₁ K₂ : ℝ} {F₁ F₂ : ℝ × ℝ → ℂ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hF₁ : MemLp F₁ 2 (B0579.cellMeasure d (-m)))
    (hF₂ : MemLp F₂ 2 (B0579.cellMeasure d (-m)))
    (hb₁ : xNorm d (-m) F₁ ≤ ENNReal.ofReal K₁)
    (hb₂ : xNorm d (-m) F₂ ≤ ENNReal.ofReal K₂) :
    MemLp (fun y => F₁ y + F₂ y) 2 (B0579.cellMeasure d (-m)) ∧
    xNorm d (-m) (fun y => F₁ y + F₂ y) ≤ ENNReal.ofReal (K₁ + K₂) := by
  refine ⟨hF₁.add hF₂, ?_⟩
  unfold xNorm
  calc eLpNorm (fun y => F₁ y + F₂ y) 2 (B0579.cellMeasure d (-m))
      ≤ eLpNorm F₁ 2 (B0579.cellMeasure d (-m)) +
          eLpNorm F₂ 2 (B0579.cellMeasure d (-m)) :=
        eLpNorm_add_le hF₁.1 hF₂.1 (by norm_num)
    _ ≤ ENNReal.ofReal K₁ + ENNReal.ofReal K₂ := add_le_add hb₁ hb₂
    _ = ENNReal.ofReal (K₁ + K₂) := (ENNReal.ofReal_add hK₁ hK₂).symm

/-! ## 2. Periodization bounds for `O(|y|⁻²)` planar profiles -/

lemma perSum_eq_tsum_shiftVec (d : ℝ) (Ψ : ℝ × ℝ → ℂ) :
    perSum d Ψ = fun y => ∑' n : ℤ, Ψ (y - Gaussian.shiftVec (-d) n) := by
  funext y
  unfold perSum
  refine tsum_congr fun n => ?_
  congr 1
  ext <;> simp [Gaussian.shiftVec]

lemma translate_bound_of_inv_sq_decay {Ψ : ℝ × ℝ → ℂ} {C : ℝ}
    (hC : ∀ z : ℝ × ℝ, ‖Ψ z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) (z : ℝ × ℝ) :
    ‖Ψ z‖ ≤ |C| * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  refine (hC z).trans ?_
  rw [Lam0B.rpow_neg_two_eq _ (by positivity)]
  have h1 : (1 + |z.1| + |z.2|)⁻¹ ≤ (1 + |z.1|)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith [abs_nonneg z.2])
  have h2 : ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ ((1 + |z.1|)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  calc C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 ≤ |C| * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + |z.1|)⁻¹) ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)

/-- Continuity of `perSum d Ψ` for any continuous planar kernel `Ψ` with `O(|z|⁻²)` decay. -/
theorem perSum_continuous_of_inv_sq_decay {Ψ : ℝ × ℝ → ℂ} {C d : ℝ} (hd : 0 < d)
    (hΨ : Continuous Ψ) (hC : ∀ z : ℝ × ℝ, ‖Ψ z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    Continuous (perSum d Ψ) := by
  rw [perSum_eq_tsum_shiftVec]
  exact Gaussian.continuous_tsum_translates hΨ (s := 2) (c := -d) (C := |C|)
    (by norm_num) (by linarith) (translate_bound_of_inv_sq_decay hC)

/-- Uniform sup bound on `B0579.cell d` (`d ≥ 1`) for `perSum d Ψ` when `Ψ` has `O(|z|⁻²)` decay. -/
theorem perSum_cell_sup_of_inv_sq_decay {Ψ : ℝ × ℝ → ℂ} {C : ℝ}
    (hC : ∀ z : ℝ × ℝ, ‖Ψ z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d : ℝ, 1 ≤ d → ∀ y ∈ B0579.cell d, ‖perSum d Ψ y‖ ≤ B := by
  have hs : Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    Gaussian.summable_one_add_abs_int_rpow (by norm_num)
  have hsum : HasSum (fun n : ℤ => 4 * |C| * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)))
      (4 * |C| * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) :=
    (hs.hasSum).mul_left (4 * |C|)
  refine ⟨4 * |C| * ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)), by
    have : 0 ≤ ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) :=
      tsum_nonneg fun n => by positivity
    positivity, fun d hd y hy => ?_⟩
  have hy1 : |y.1| ≤ d / 2 := by
    rw [abs_le]
    exact ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  unfold perSum
  refine tsum_of_norm_bounded hsum fun n => ?_
  refine (translate_bound_of_inv_sq_decay hC _).trans ?_
  have hlow : (1 + |(n : ℝ)|) / 2 ≤ 1 + |y.1 + n * d| := by
    by_cases hn : n = 0
    · subst hn; simp; linarith [abs_nonneg y.1]
    · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h3 : |(n : ℝ) * d| ≤ |y.1 + n * d| + |y.1| := by
        have h4 : |(n : ℝ) * d| = |(y.1 + n * d) - y.1| := by congr 1; ring
        rw [h4]
        linarith [abs_sub_le (y.1 + n * d) y.1 0, abs_sub (y.1 + n * d) y.1]
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < d)] at h3
      nlinarith [abs_nonneg (y.1 + n * d)]
  have hpos : 0 < (1 + |(n : ℝ)|) / 2 := by positivity
  have h5 : (1 + |y.1 + n * d|) ^ (-(2 : ℝ)) ≤ ((1 + |(n : ℝ)|) / 2) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
  have h6 : ((1 + |(n : ℝ)|) / 2) ^ (-(2 : ℝ)) = 4 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by positivity), Real.rpow_two]
    field_simp
    norm_num
  calc |C| * (1 + |y.1 + n * d|) ^ (-(2 : ℝ))
      ≤ |C| * (4 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ))) := by
        rw [← h6]; exact mul_le_mul_of_nonneg_left h5 (abs_nonneg C)
    _ = 4 * |C| * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring

/-- Uniform `X_{-m, d}` membership and norm bound for `perSum d Ψ` (`m > 1`, `d ≥ 1`). -/
theorem memLp_and_xNorm_perSum_of_inv_sq_decay {Ψ : ℝ × ℝ → ℂ} {C m : ℝ} (hm : 1 < m)
    (hΨ : Continuous Ψ) (hC : ∀ z : ℝ × ℝ, ‖Ψ z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 1 ≤ d →
      MemLp (perSum d Ψ) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (perSum d Ψ) ≤ ENNReal.ofReal K := by
  obtain ⟨B, hB0, hB⟩ := perSum_cell_sup_of_inv_sq_decay hC
  refine ⟨(B0592.weightConst m).toReal * B, mul_nonneg ENNReal.toReal_nonneg hB0, fun d hd => ?_⟩
  have hcont : Continuous (perSum d Ψ) := perSum_continuous_of_inv_sq_decay (by linarith) hΨ hC
  exact memLp_and_xNorm_neg_le_of_cell_bdd hm hB0 hcont.aestronglyMeasurable (hB d hd)

/-- Uniform `X_{-m, d}` membership and norm bound for `perLam0 κ d j` (`m > 1`, `d ≥ 1`). -/
theorem memLp_and_xNorm_perLam0_neg (κ : PlanarFrameKernels) {m : ℝ} (hm : 1 < m) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ d : ℝ, 1 ≤ d → ∀ j : Fin 2,
      MemLp (perLam0 κ d j) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (perLam0 κ d j) ≤ ENNReal.ofReal K₀ := by
  obtain ⟨B, hB0, hB⟩ := Lam0B.perLam0_sup κ
  refine ⟨(B0592.weightConst m).toReal * B, mul_nonneg ENNReal.toReal_nonneg hB0,
    fun d hd j => ?_⟩
  have hcont : Continuous (perLam0 κ d j) := Lam0B.perLam0_continuous κ (by linarith) j
  exact memLp_and_xNorm_neg_le_of_cell_bdd hm hB0 hcont.aestronglyMeasurable (hB d hd j)

/-! ## 3. Periodization, Gram inverse bound, and scaling identities for `physFrameLam0` -/

/-- Unnormalised physical frame dual row `a(r)⁻¹ * perLam0 κ d(r) j (x / √a(r))` (SP 2896, 2906). -/
def physFrameLam0 (κ : PlanarFrameKernels) (ν r : ℝ) (j : Fin 2) : ℝ × ℝ → ℂ :=
  physAdj (clockA ν r) (perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j)

/-- Rescaling `physAdj a` commutes with periodization: `physAdj a (perSum (c / √a) f)` is the
`c`-periodization `perSum c (physAdj a f)` with `a`-independent physical period `c`. -/
theorem physAdj_perSum_eq_perSum_physAdj {a c : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    physAdj a (perSum (cellLen c a) f) x = perSum c (physAdj a f) x := by
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  unfold physAdj perSum cellLen
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  congr 2
  ext
  · dsimp
    ring
  · rfl

/-- `physFrameLam0 κ ν r j` is the `c = ν⁻²`-periodization of `physAdj (clockA ν r) (κ.lamP j)`
with `r`-independent physical period `c = ν⁻²`. -/
theorem physFrameLam0_eq_perSum_physAdj (κ : PlanarFrameKernels) {ν r : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (j : Fin 2) (x : ℝ × ℝ) :
    physFrameLam0 κ ν r j x =
      perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν r) (κ.lamP j)) x := by
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  exact physAdj_perSum_eq_perSum_physAdj ha (κ.lamP j) x

/-- Pointwise expansion of `physFrameLam` in terms of `(perGram κ d)⁻¹` and `physFrameLam0`. -/
theorem physFrameLam_eq_sum_perGram_inv (κ : PlanarFrameKernels) (ν r : ℝ) (i : Fin 2)
    (x : ℝ × ℝ) :
    physFrameLam κ ν r i x =
      ∑ j : Fin 2,
        (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j * physFrameLam0 κ ν r j x := by
  unfold physFrameLam physFrameLam0 physAdj perLam
  simp only [Fin.sum_univ_two]
  ring

/-- Uniform entrywise bound `‖(perGram κ d)⁻¹ i j‖ ≤ 3` for all sufficiently large `d`. -/
theorem perGram_inv_entry_bound (κ : PlanarFrameKernels) :
    ∃ D₁ : ℝ, 1 ≤ D₁ ∧ ∀ d : ℝ, D₁ ≤ d → ∀ i j : Fin 2, ‖(perGram κ d)⁻¹ i j‖ ≤ 3 := by
  obtain ⟨D₀, hD₀⟩ :=
    perGramNear_of κ (perGramUnfold κ) (perGramTail κ) (1 / 4) (by norm_num)
  refine ⟨max D₀ 1, le_max_right _ _, fun d hd i j => ?_⟩
  exact (gram_inv_bound (perGram κ d) (hD₀ d (le_trans (le_max_left _ _) hd))).2 i j

/-- Moving pullback of the physical Laplacian of a dilated planar profile `physAdj a L`:
`a² * movingPhi ν (ν * Δ(physAdj a L)) = θ(r)⁻¹ * Δ L` (proved via `E0.lapCx_scale`). -/
theorem movPlanarLap_physAdj_eq {L : ℝ × ℝ → ℂ} (hL : ContDiff ℝ ∞ L)
    {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (y : ℝ × ℝ) :
    (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
      movingPhi ν (fun r' x' => (ν : ℂ) * ladLapCx (physAdj (clockA ν r') L) x') r y =
      (clockTheta ν r : ℂ)⁻¹ * E0.lapCx L y := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hsa : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 ha
  have hsa_ne : Real.sqrt (clockA ν r) ≠ 0 := hsa.ne'
  have ha_ne : (clockA ν r : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hν_ne : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hphys : physAdj (clockA ν r) L =
      fun x => ((clockA ν r : ℝ) : ℂ) *
        L ((Real.sqrt (clockA ν r))⁻¹ * x.1, (Real.sqrt (clockA ν r))⁻¹ * x.2) := by
    funext x
    unfold physAdj
    congr 2
    exact Prod.ext (by ring) (by ring)
  have hlap : ladLapCx (physAdj (clockA ν r) L) (Real.sqrt (clockA ν r) * y.1,
      Real.sqrt (clockA ν r) * y.2) =
      ((clockA ν r : ℝ) : ℂ) * (((Real.sqrt (clockA ν r))⁻¹ : ℝ) : ℂ) ^ 2 *
        E0.lapCx L y := by
    change E0.lapCx (physAdj (clockA ν r) L)
        (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) = _
    rw [hphys, E0.lapCx_scale L hL ((clockA ν r : ℝ) : ℂ) (Real.sqrt (clockA ν r))⁻¹]
    rw [inv_mul_cancel_left₀ hsa_ne y.1, inv_mul_cancel_left₀ hsa_ne y.2]
  unfold movingPhi
  dsimp only
  rw [hlap]
  have hsq_a : (clockA ν r) ^ (2 : ℝ) = (clockA ν r) ^ 2 := Real.rpow_two (clockA ν r)
  have hsq_s : (((Real.sqrt (clockA ν r))⁻¹ : ℝ) : ℂ) ^ 2 = (((clockA ν r)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  rw [hsq_a, hsq_s]
  unfold clockTheta
  push_cast
  field_simp [ha_ne, hν_ne]

/-- Moving-variable heat/dilation dual generator on the unnormalised periodized row `perLam0`:
`a(r)² * movingPhi ν (∂_r φ⁰_j + ν Δ φ⁰_j) r` (SP 2896, 2905-2912). -/
def movLam0DualHeat (κ : PlanarFrameKernels) (ν r : ℝ) (j : Fin 2) (y : ℝ × ℝ) : ℂ :=
  (((clockA ν r) ^ (2 : ℝ) : ℝ) : ℂ) *
    movingPhi ν (fun r' x' =>
      ladDt (fun s x'' => physFrameLam0 κ ν s j x'') r' x' +
        (ν : ℂ) * ladLapCx (physFrameLam0 κ ν r' j) x') r y

/-! ## 4. Analytical leaves and assembly of `MovLamDualHeatBound` -/

/-- **Leaf 1a (`SeedLamPDSharpDecay`, `PartIII-a:T21/c5/3/1/1`, SP 2896, 2905-2912)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`), the unnormalised moving heat/dilation generator
`movLam0DualHeat κ ν r j` satisfies the dual periodization identity
`movLam0DualHeat κ ν r j y = θ(r)⁻¹ * perSum d(r) (Ψ j) y` (where `Ψ j = D^# (κ.lamP j)` up to sign
convention), and the planar profiles `Ψ j` are continuous with `O((1 + |z₁| + |z₂|)⁻²)` decay. -/
def SeedLamPDSharpDecay (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ (Ψ : Fin 2 → ℝ × ℝ → ℂ) (C_d : ℝ), 0 ≤ C_d ∧
    (∀ j : Fin 2, Continuous (Ψ j)) ∧
    (∀ (j : Fin 2) (z : ℝ × ℝ), ‖Ψ j z‖ ≤ C_d * ((1 + |z.1| + |z.2|)⁻¹) ^ 2) ∧
    ∀ {ν r : ℝ}, 0 < ν → 0 ≤ r →
      1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) →
      ∀ (j : Fin 2) (y : ℝ × ℝ),
        movLam0DualHeat κ ν r j y =
          (clockTheta ν r : ℂ)⁻¹ *
            perSum (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Ψ j) y

/-- **Leaf 1b (`PerGramInvHeatSplit`, `PartIII-a:T21/c5/3/1/2`, SP 2901-2912, 2990-2997)**:
For a Part I seed kernel `κ` (`IsSeedKernels κ`) and sufficiently large moving cell length `d(r)`,
differentiating `physFrameLam = G(d(r))⁻¹ physFrameLam0` splits `movLamDualHeat κ ν r i` into the
Gram-normalised sum of `movLam0DualHeat κ ν r j` plus the moving-time derivative of `G(d(r))⁻¹`
acting on `perLam0 κ d(r) j`, with `‖(G(d(r))⁻¹)_z i j‖ ≤ C_g / clockTheta ν r`
(since `(G⁻¹)_z = O(θ(r)⁻¹ d(r)⁻²) = O(θ(r)⁻¹)` for `d(r) ≥ 1`). -/
def PerGramInvHeatSplit (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ →
  ∃ C_g D_g : ℝ, 0 ≤ C_g ∧ 1 ≤ D_g ∧
    ∀ {ν r : ℝ}, 0 < ν → 0 ≤ r →
      let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r)
      D_g ≤ d →
      ∀ i : Fin 2, ∃ gDz : Fin 2 → ℂ,
        (∀ j : Fin 2, ‖gDz j‖ ≤ C_g * (1 / clockTheta ν r)) ∧
        ∀ y : ℝ × ℝ,
          movLamDualHeat κ ν r i y =
            ∑ j : Fin 2,
              ((perGram κ d)⁻¹ i j * movLam0DualHeat κ ν r j y +
                gDz j * perLam0 κ d j y)

/-- Conditional proof of `MovLamDualHeatBound κ` (`PartIII-a:T21/c5/3/1`) from
`SeedLamPDSharpDecay κ` and `PerGramInvHeatSplit κ`. -/
theorem movLamDualHeatBound_of (κ : PlanarFrameKernels)
    (hSharp : SeedLamPDSharpDecay κ)
    (hSplit : PerGramInvHeatSplit κ) :
    MovLamDualHeatBound κ := by
  intro hκ m hm
  have hm1 : 1 < m := by linarith
  obtain ⟨Ψ, C_d, -, hΨ_cont, hΨ_decay, hmov0⟩ := hSharp hκ
  obtain ⟨K_Ψ0, hK_Ψ0, hΨ0⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hΨ_cont 0) (hΨ_decay 0)
  obtain ⟨K_Ψ1, hK_Ψ1, hΨ1⟩ :=
    memLp_and_xNorm_perSum_of_inv_sq_decay hm1 (hΨ_cont 1) (hΨ_decay 1)
  set K_Ψ : ℝ := max K_Ψ0 K_Ψ1
  have hK_Ψ : 0 ≤ K_Ψ := le_trans hK_Ψ0 (le_max_left _ _)
  have hΨ_bound : ∀ d : ℝ, 1 ≤ d → ∀ j : Fin 2,
      MemLp (perSum d (Ψ j)) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (perSum d (Ψ j)) ≤ ENNReal.ofReal K_Ψ := by
    intro d hd j
    fin_cases j
    · obtain ⟨hm0, hb0⟩ := hΨ0 d hd
      exact ⟨hm0, hb0.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
    · obtain ⟨hm1', hb1'⟩ := hΨ1 d hd
      exact ⟨hm1', hb1'.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  obtain ⟨K₀, hK₀, hLam0⟩ := memLp_and_xNorm_perLam0_neg κ hm1
  obtain ⟨D_1, hD_1, hGramInv⟩ := perGram_inv_entry_bound κ
  obtain ⟨C_g, D_g, hC_g0, hD_g, hSplit'⟩ := hSplit hκ
  set D : ℝ := max D_1 D_g
  have hD1 : 1 ≤ D := le_trans hD_1 (le_max_left _ _)
  have hD0 : 0 ≤ D := by linarith
  set C_h : ℝ := 2 * (3 * K_Ψ + C_g * K₀)
  have hC_h0 : 0 ≤ C_h := by positivity
  refine ⟨C_h, 1, hC_h0, le_rfl, fun b hb => ?_⟩
  refine ⟨1 / (D + 1) ^ 2, by positivity, fun ν hν r hr hθ i => ?_⟩
  intro d
  have hdD : D ≤ d := cellLen_ge hD0 hν.1 hν.2 hb hr hθ
  have hd1 : 1 ≤ d := le_trans hD1 hdD
  have hd_D1 : D_1 ≤ d := le_trans (le_max_left _ _) hdD
  have hd_Dg : D_g ≤ d := le_trans (le_max_right _ _) hdD
  have hθ1 : 1 ≤ clockTheta ν r := le_trans hb hθ
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ1
  have hinvθ_nonneg : 0 ≤ 1 / clockTheta ν r := by positivity
  have hnorm_invθ : ‖(clockTheta ν r : ℂ)⁻¹‖ = 1 / clockTheta ν r := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hθ_pos.le, one_div]
  obtain ⟨gDz, hgDz_bound, hEq⟩ := hSplit' hν.1 hr hd_Dg i
  have hterm : ∀ j : Fin 2,
      let T := fun y => (perGram κ d)⁻¹ i j * movLam0DualHeat κ ν r j y +
        gDz j * perLam0 κ d j y
      MemLp T 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) T ≤ ENNReal.ofReal ((3 * K_Ψ + C_g * K₀) * (1 / clockTheta ν r)) := by
    intro j
    obtain ⟨hΨm, hΨx⟩ := hΨ_bound d hd1 j
    obtain ⟨hL0m, hL0x⟩ := hLam0 d hd1 j
    have hA_eq : (fun y => (perGram κ d)⁻¹ i j * movLam0DualHeat κ ν r j y) =
        fun y => ((perGram κ d)⁻¹ i j * (clockTheta ν r : ℂ)⁻¹) * perSum d (Ψ j) y := by
      funext y
      rw [hmov0 hν.1 hr hd1 j y, mul_assoc]
    have hAm : MemLp (fun y => (perGram κ d)⁻¹ i j * movLam0DualHeat κ ν r j y) 2
        (B0579.cellMeasure d (-m)) := by
      rw [hA_eq]
      exact hΨm.const_mul _
    have hAx : xNorm d (-m) (fun y => (perGram κ d)⁻¹ i j * movLam0DualHeat κ ν r j y) ≤
        ENNReal.ofReal (3 * K_Ψ * (1 / clockTheta ν r)) := by
      rw [hA_eq]
      refine (xNorm_const_mul_le hK_Ψ hΨx).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [norm_mul, hnorm_invθ]
      have hG_le : ‖(perGram κ d)⁻¹ i j‖ ≤ 3 := hGramInv d hd_D1 i j
      calc ‖(perGram κ d)⁻¹ i j‖ * (1 / clockTheta ν r) * K_Ψ
          ≤ 3 * (1 / clockTheta ν r) * K_Ψ := by gcongr
        _ = 3 * K_Ψ * (1 / clockTheta ν r) := by ring
    have hBm : MemLp (fun y => gDz j * perLam0 κ d j y) 2 (B0579.cellMeasure d (-m)) :=
      hL0m.const_mul _
    have hBx : xNorm d (-m) (fun y => gDz j * perLam0 κ d j y) ≤
        ENNReal.ofReal (C_g * K₀ * (1 / clockTheta ν r)) := by
      refine (xNorm_const_mul_le hK₀ hL0x).trans (ENNReal.ofReal_le_ofReal ?_)
      have hg_le : ‖gDz j‖ ≤ C_g * (1 / clockTheta ν r) := hgDz_bound j
      calc ‖gDz j‖ * K₀ ≤ (C_g * (1 / clockTheta ν r)) * K₀ := by gcongr
        _ = C_g * K₀ * (1 / clockTheta ν r) := by ring
    obtain ⟨hABm, hABx⟩ := memLp_and_xNorm_add_le
      (by positivity) (by positivity) hAm hBm hAx hBx
    refine ⟨hABm, hABx.trans ?_⟩
    rw [show 3 * K_Ψ * (1 / clockTheta ν r) + C_g * K₀ * (1 / clockTheta ν r) =
      (3 * K_Ψ + C_g * K₀) * (1 / clockTheta ν r) by ring]
  obtain ⟨hm0, hx0⟩ := hterm 0
  obtain ⟨hm1', hx1'⟩ := hterm 1
  have hsum_eq : movLamDualHeat κ ν r i = fun y =>
      ((perGram κ d)⁻¹ i 0 * movLam0DualHeat κ ν r 0 y + gDz 0 * perLam0 κ d 0 y) +
      ((perGram κ d)⁻¹ i 1 * movLam0DualHeat κ ν r 1 y + gDz 1 * perLam0 κ d 1 y) := by
    funext y
    rw [hEq y, Fin.sum_univ_two]
  rw [hsum_eq]
  obtain ⟨hm_tot, hx_tot⟩ := memLp_and_xNorm_add_le
    (by positivity) (by positivity) hm0 hm1' hx0 hx1'
  refine ⟨hm_tot, hx_tot.trans ?_⟩
  rw [show (3 * K_Ψ + C_g * K₀) * (1 / clockTheta ν r) +
      (3 * K_Ψ + C_g * K₀) * (1 / clockTheta ν r) =
      C_h * (1 / clockTheta ν r) by unfold C_h; ring]

end ComplCouplingHeat

/-- Top-level alias for `ComplCouplingHeat.SeedLamPDSharpDecay` (`PartIII-a:T21/c5/3/1/1`). -/
abbrev SeedLamPDSharpDecay (κ : PlanarFrameKernels) : Prop :=
  ComplCouplingHeat.SeedLamPDSharpDecay κ

/-- Top-level alias for `ComplCouplingHeat.PerGramInvHeatSplit` (`PartIII-a:T21/c5/3/1/2`). -/
abbrev PerGramInvHeatSplit (κ : PlanarFrameKernels) : Prop :=
  ComplCouplingHeat.PerGramInvHeatSplit κ

/-- Conditional assembly of `MovLamDualHeatBound κ` (`PartIII-a:T21/c5/3/1`) from
`SeedLamPDSharpDecay κ` (`PartIII-a:T21/c5/3/1/1`) and
`PerGramInvHeatSplit κ` (`PartIII-a:T21/c5/3/1/2`). -/
theorem movLamDualHeatBound_of (κ : PlanarFrameKernels)
    (hSharp : SeedLamPDSharpDecay κ)
    (hSplit : PerGramInvHeatSplit κ) :
    MovLamDualHeatBound κ :=
  ComplCouplingHeat.movLamDualHeatBound_of κ hSharp hSplit

end UnforcedLeray.Short.IIIa
