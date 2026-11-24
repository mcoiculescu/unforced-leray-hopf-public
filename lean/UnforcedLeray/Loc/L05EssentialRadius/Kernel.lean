import UnforcedLeray.Loc.L05EssentialRadius.Abstract
import UnforcedLeray.Loc.L05EssentialRadius.HMinusOne

/-!
# L5: compactness of `S₀(t)𝓑_*(r)` from compactness of multiplication by `U_* ∈ C₀`

`paper/main.tex` lines 332–336 (blueprint B0714 (a)–(c)): "Multiplication by `U_* ∈ C_0` is
compact `X → L²`, by Rellich compactness on balls and a small uniform tail. Hence
`𝓑_* : X → H^{-1}` is compact, and `S_0(r)𝓑_* : X → X` is compact for `r > 0`."

* `C0MulCompact`: the multiplication statement (B0714 (a)), in sequential form on `H¹(ℝ³)`;
  it is proved in `Rellich.lean`.
* `norm_S0L_le`: `‖S₀(t)F‖_X ≤ ‖S₀(t/2)‖ e^{-t/8} ‖e^{aΔ}F‖₂` with `a = h(e^{t/2}-1)`: the
  factorization of `S₀(t)` through `L²` (line 335).
* `duhamelKernelNull_of`: B0714 (c) in the sequential form `DuhamelKernelNull` of
  `Abstract.lean`, from `C0MulCompact` and the `H⁻¹` bound `norm_heat_sq_le` of
  `HMinusOne.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace UnforcedLeray.Loc.L05

open UnforcedLeray.Blueprint UnforcedLeray.Infra.WeaklyNullCompact

/-- **B0714 (a)** (line 332, "Rellich compactness on balls and a small uniform tail"):
multiplication by a field `U ∈ C₀(ℝ³;ℝ³)` maps weakly null sequences of `H¹(ℝ³;ℝ³)` to
sequences with `∫ |U|²|fₙ|² → 0`, i.e. it is compact `H¹ → L²`. -/
def C0MulCompact : Prop :=
  ∀ (U : ZeroAtInftyContinuousMap Space Space) (f : ℕ → SobolevGraph.H1),
    (∀ G : SobolevGraph.H1, Tendsto (fun n => ⟪G, f n⟫_ℝ) atTop (𝓝 0)) →
      Tendsto (fun n => ∫ y, ‖U y‖ ^ 2 * ‖((f n).value : SpatialField) y‖ ^ 2) atTop (𝓝 0)

theorem toL2_congr_ae {f g : SpatialField} (h : f =ᵐ[volume] g) : toL2 f = toL2 g := by
  by_cases hf : MemLp f 2 volume
  · have hg : MemLp g 2 volume := hf.ae_eq h
    rw [toL2_of_memLp hf, toL2_of_memLp hg]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp g 2 volume := fun hg => hf (hg.ae_eq h.symm)
    unfold toL2
    simp [hf, hg]

theorem norm_C0_apply_le (U : ZeroAtInftyContinuousMap Space Space) (y : Space) :
    ‖U y‖ ≤ ‖U‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm U.toBCF y

theorem norm_symTensorColumns_le (U f : SpatialField) (j : Fin 3) (y : Space) :
    ‖symTensorColumns U f j y‖ ≤ 2 * (‖U y‖ * ‖f y‖) := by
  unfold symTensorColumns
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have h1 : ‖(f y) j‖ ≤ ‖f y‖ := PiLp.norm_apply_le (f y) j
  have h2 : ‖(U y) j‖ ≤ ‖U y‖ := PiLp.norm_apply_le (U y) j
  nlinarith [norm_nonneg (U y), norm_nonneg (f y), norm_nonneg ((f y) j), norm_nonneg ((U y) j)]

/-- The columns of `U ⊗ f + f ⊗ U` are small in `L²` when `∫|U|²|f|²` is small. -/
theorem norm_toL2_symTensorColumns_sq_le (U : ZeroAtInftyContinuousMap Space Space)
    {f : SpatialField} (hf : MemLp f 2 volume) (j : Fin 3) :
    ‖toL2 (symTensorColumns U f j)‖ ^ 2 ≤ 4 * ∫ y, ‖U y‖ ^ 2 * ‖f y‖ ^ 2 := by
  have hUc : Continuous U := U.continuous
  have hmeas : AEStronglyMeasurable (symTensorColumns U f j) volume := by
    unfold symTensorColumns
    have hfj : AEStronglyMeasurable (fun y => (f y) j) volume :=
      (PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable hf.1
    have hUj : AEStronglyMeasurable (fun y => (U y) j) volume :=
      ((PiLp.continuous_apply 2 _ j).comp hUc).aestronglyMeasurable
    exact (hfj.smul hUc.aestronglyMeasurable).add (hUj.smul hf.1)
  have hdom : MemLp (fun y => 2 * ‖U‖ * ‖f y‖) 2 volume := hf.norm.const_mul _
  have hmem : MemLp (symTensorColumns U f j) 2 volume :=
    hdom.of_le hmeas (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine (norm_symTensorColumns_le U f j y).trans ?_
      have := norm_C0_apply_le U y
      have := norm_nonneg (f y)
      nlinarith)
  have hint : Integrable (fun y => ‖U y‖ ^ 2 * ‖f y‖ ^ 2) volume := by
    have hf2 : Integrable (fun y => ‖f y‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hf.1).mp hf
    refine (hf2.const_mul (‖U‖ ^ 2)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((hUc.norm.pow 2).aestronglyMeasurable).mul (hf.1.norm.pow 2)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_C0_apply_le U y) 2) (sq_nonneg _)
  rw [norm_toL2_sq hmem, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
    (hint.const_mul 4) (Eventually.of_forall fun y => ?_)
  have h := norm_symTensorColumns_le U f j y
  have h0 : 0 ≤ ‖symTensorColumns U f j y‖ := norm_nonneg _
  calc ‖symTensorColumns U f j y‖ ^ 2 ≤ (2 * (‖U y‖ * ‖f y‖)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = 4 * (‖U y‖ ^ 2 * ‖f y‖ ^ 2) := by ring

variable {h : ℝ} {S : FreeEvolution}

/-- Factorization of `S₀(t)` through `L²` (line 335): `‖S₀(t)F‖_X ≤ ‖S₀(t/2)‖ e^{-t/8}
‖e^{aΔ}F‖₂`, `a = h(e^{t/2}-1)`. -/
theorem norm_S0L_le (hh : 0 ≤ h) (hS : IsFreeEvolution h S) {t : ℝ} (ht : 0 < t) (F : L2div) :
    ‖S.S0L t F‖ ≤ ‖S.S0L (t / 2)‖ *
      (Real.exp (-(t / 2) / 4) * ‖Heat.heatOperator (h * (Real.exp (t / 2) - 1)) (Lclass F)‖) := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hsplit := S0L_add hh hS ht2 ht2 F
  rw [add_halves] at hsplit
  rw [hsplit, ← norm_ιX_S0L hS ht2 F]
  exact ContinuousLinearMap.le_opNorm _ _

variable {D : BackgroundData} {c : Coefficients}

/-- **B0714 (c)** (lines 333–336), sequential form: given `C0MulCompact`, every
`S₀(t)𝓑_*(r)`, `0 < t ≤ 1`, maps weakly null sequences of `X` to null sequences. -/
theorem duhamelKernelNull_of (hR : C0MulCompact) (hh : 0 < D.h) (hS : IsFreeEvolution D.h S)
    (hc : IsCoefficients D c) : DuhamelKernelNull c S := by
  intro t r ht _ x hx
  obtain ⟨V, -, -, hV⟩ := hc.Ustar_C0
  obtain ⟨M, hM⟩ := exists_norm_le_of_weaklyNull (𝕜 := ℝ) hx
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the columns tend to zero
  have hH1 : ∀ G : SobolevGraph.H1, Tendsto (fun n => ⟪G, (x n).toH1⟫_ℝ) atTop (𝓝 0) := by
    have hw := ((weakTendsto_zero_iff (𝕜 := ℝ)).mpr hx).map Xincl
    rw [map_zero] at hw
    exact (weakTendsto_zero_iff (𝕜 := ℝ)).mp hw
  have hint := hR (V r) (fun n => (x n).toH1) hH1
  set s : ℕ → ℝ := fun n => ∑ j, ‖toL2 (symTensorColumns (D.Ustar r) (Xval (x n)) j)‖ with hs
  have hcol : ∀ n j, ‖toL2 (symTensorColumns (D.Ustar r) (Xval (x n)) j)‖ ≤
      2 * Real.sqrt (∫ y, ‖V r y‖ ^ 2 * ‖Xval (x n) y‖ ^ 2) := by
    intro n j
    have hcongr : symTensorColumns (D.Ustar r) (Xval (x n)) j =ᵐ[volume]
        symTensorColumns (V r) (Xval (x n)) j := by
      filter_upwards [hV r] with y hy
      simp only [symTensorColumns, hy]
    rw [toL2_congr_ae hcongr]
    have hb := norm_toL2_symTensorColumns_sq_le (V r) (Lp.memLp (Xclass (x n))) j
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4] at hb
    have := Real.abs_le_sqrt hb
    rw [abs_norm, Real.sqrt_mul' _ (integral_nonneg fun y => by positivity),
      Real.sqrt_sq (by norm_num)] at this
    exact this
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => 3 * (2 * Real.sqrt
        (∫ y, ‖V r y‖ ^ 2 * ‖Xval (x n) y‖ ^ 2))) atTop (𝓝 0) := by
      have := ((hint.sqrt).const_mul 2).const_mul 3
      rw [Real.sqrt_zero, mul_zero, mul_zero] at this
      exact this
    refine squeeze_zero (fun n => Finset.sum_nonneg fun j _ => norm_nonneg _)
      (fun n => ?_) hsq
    calc s n ≤ ∑ _j : Fin 3, 2 * Real.sqrt (∫ y, ‖V r y‖ ^ 2 * ‖Xval (x n) y‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => hcol n j
      _ = _ := by simp
  -- the heat bound
  set a : ℝ := D.h * (Real.exp (t / 2) - 1) with ha_def
  have ha : 0 < a := mul_pos hh (sub_pos.mpr (Real.one_lt_exp_iff.mpr (half_pos ht)))
  set K1 : ℝ := ‖S.S0L (t / 2)‖ * Real.exp (-(t / 2) / 4) with hK1
  set K2 : ℝ := Heat.h1SmoothingBound a * (‖c.B r‖ * M) with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hbound : ∀ n, ‖S.S0L t (c.B r (x n))‖ ≤ K1 * Real.sqrt (s n * K2) := by
    intro n
    refine (norm_S0L_le hh.le hS ht _).trans ?_
    rw [hK1, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      (norm_nonneg _)
    have hq := norm_heat_sq_le (hc.B_weak r (x n)) ha
    have hF : ‖Lclass (c.B r (x n))‖ ≤ ‖c.B r‖ * M := by
      rw [← norm_L2div]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _))
    have hq' : ‖Heat.heatOperator a (Lclass (c.B r (x n)))‖ ^ 2 ≤ s n * K2 := by
      refine hq.trans (mul_le_mul_of_nonneg_left ?_
        (Finset.sum_nonneg fun j _ => norm_nonneg _))
      exact mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _)
    have := Real.abs_le_sqrt hq'
    rwa [abs_norm] at this
  have hlim : Tendsto (fun n => K1 * Real.sqrt (s n * K2)) atTop (𝓝 0) := by
    have := ((hs0.mul_const K2).sqrt).const_mul K1
    simpa using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) hbound hlim

end UnforcedLeray.Loc.L05
