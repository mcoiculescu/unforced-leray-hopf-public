import UnforcedLeray.Units.B0121.Spectral

/-!
# B0121 helper: elements of `X_{G,j}` have Gaussian-`L²` weak derivatives up to order `j`

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865), the direction
"graph norm controls the derivatives". For `f ∈ X_{G,j}` and a word `w` of length `k ≤ j`,
the truncations `U_G (∑_{ℓ<M} ⟪e_ℓ, f⟫ e_ℓ)` (finite combinations of Hermite levels, tex
line 1864) have conjugated derivatives `A_w` forming a Cauchy sequence in `L²(ℝ², dy)`
(`cauchySeq_Aw`, by the level computation `sum_norm_sq_Aw_chi`); the limit `gam f k w`
gives the weak derivative `wd f k w = √G (gam f k w)` of the planar function of `f`
(`hasWeakDerivOn_wd`), and `sum_norm_sq_gam` computes the sum of the squared norms over all
words of length `k` ("Summing the orthogonal levels proves the equivalence", tex line 1864).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap InnerProductSpace ComplexConjugate Real ENNReal ContDiff

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094 UnforcedLeray.B0010 UnforcedLeray.PlanarBS.Sob

/-- The Hermite coefficients `⟪e_ℓ, f⟫_{X_G}` of `f`. -/
def coef (f : XG) (ℓ : ℕ) : ℂ := ⟪oscBasis ℓ, f⟫_ℂ

/-- `U_G` of the truncation `∑_{ℓ<M} ⟪e_ℓ, f⟫ e_ℓ` of `f` to its first `M` Hermite levels. -/
def trunc (f : XG) (M : ℕ) : S2 := chi (Finset.range M) (coef f)

theorem isAngularTwo_trunc (f : XG) (M : ℕ) : IsAngularTwo (trunc f M) :=
  isAngularTwo_chi _ _

theorem tendsto_toXG_trunc (f : XG) : Tendsto (fun M => toXG (trunc f M)) atTop (𝓝 f) := by
  have h := (hasSum_components f).tendsto_sum_nat
  refine h.congr fun M => ?_
  rw [trunc, toXG_chi]
  rfl

theorem dirs_succ {k : ℕ} (w : Fin (k + 1) → Fin 2) : dirs w = ev (w 0) :: dirs (Fin.tail w) := by
  simp [dirs, List.ofFn_succ]
  rfl

/-- The classical derivatives of `√G χ`: `∂_w (√G χ) = √G A_w χ`. -/
theorem iterDirDeriv_gS (k : ℕ) (w : Fin k → Fin 2) (χ : S2) :
    iterDirDeriv (dirs w) ⇑(gS χ) = ⇑(gS (Aw k w χ)) := by
  induction k generalizing χ with
  | zero => rfl
  | succ k ih =>
    rw [dirs_succ, iterDirDeriv_cons, ih, Aw_succ, ← dop_gS]
    rfl

theorem hasWeakDerivOn_gS (k : ℕ) (w : Fin k → Fin 2) (χ : S2) :
    HasWeakDerivOn univ (dirs w) ⇑(gS χ) ⇑(gS (Aw k w χ)) := by
  rw [← iterDirDeriv_gS]
  exact hasWeakDerivOn_of_contDiffOn isOpen_univ (n := k) (by simp)
    (((gS χ).smooth k).contDiffOn)

/-- Pairings with a temperate test function pass to the limit in `L²(ℝ², G⁻¹ dy)`. -/
theorem tendsto_integral_mul_of_gauss {F : ℝ × ℝ → ℂ} {Fn : ℕ → ℝ × ℝ → ℂ}
    (hF : MemGaussL2 F) (hFn : ∀ n, MemGaussL2 (Fn n))
    (hd : ∀ n, MemGaussL2 fun z => F z - Fn n z)
    (hlim : Tendsto (fun n => ‖(hd n).toLp (B0093.conjG fun z => F z - Fn n z)‖) atTop (𝓝 0))
    {Φ : ℝ × ℝ → ℂ} (hΦ : Φ.HasTemperateGrowth) :
    Tendsto (fun n => ∫ z, Fn n z * Φ z) atTop (𝓝 (∫ z, F z * Φ z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖(∫ z, Fn n z * Φ z) - ∫ z, F z * Φ z‖ ≤
      ‖(hd n).toLp (B0093.conjG fun z => F z - Fn n z)‖ * ‖J (wS Φ hΦ)‖ := by
    intro n
    rw [← integral_sub (integrable_mul_temperate (hFn n) hΦ) (integrable_mul_temperate hF hΦ),
      ← norm_neg, ← integral_neg]
    have e : (fun z => -(Fn n z * Φ z - F z * Φ z)) = fun z => (F z - Fn n z) * Φ z := by
      funext z
      ring
    rw [e]
    exact norm_integral_mul_temperate_le (hd n) hΦ
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  have := hlim.mul_const ‖J (wS Φ hΦ)‖
  rwa [zero_mul] at this

/-! ## The level sums -/

theorem summable_qpoly_coef {j : ℕ} {f : XG} (hf : f ∈ XGj j) {k : ℕ} (hk : k ≤ j) :
    Summable fun ℓ : ℕ => qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 := by
  have h := ((mem_XGj_iff j f).1 hf).mul_left ((2 + (j : ℝ)) ^ j)
  refine Summable.of_nonneg_of_le (fun ℓ => mul_nonneg (qpoly_nonneg k ℓ) (by positivity))
    (fun ℓ => ?_) h
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (qpoly_le hk ℓ) (by positivity)

theorem trunc_sub (f : XG) {m n : ℕ} (h : m ≤ n) :
    trunc f n - trunc f m = chi (Finset.Ico m n) (coef f) := by
  simp only [trunc, chi]
  rw [Finset.sum_Ico_eq_sub _ h]

theorem norm_J_Aw_chi_le (k : ℕ) (w : Fin k → Fin 2) (s : Finset ℕ) (a : ℕ → ℂ) :
    ‖J (Aw k w (chi s a))‖ ^ 2 ≤ 2 * π * ∑ ℓ ∈ s, qpoly k (2 + ℓ) * ‖a ℓ‖ ^ 2 := by
  rw [← sum_norm_sq_Aw_chi]
  exact Finset.single_le_sum (f := fun w => ‖J (Aw k w (chi s a))‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ w)

/-- The truncations give a Cauchy sequence of conjugated derivatives. -/
theorem cauchySeq_Aw {j : ℕ} {f : XG} (hf : f ∈ XGj j) {k : ℕ} (hk : k ≤ j)
    (w : Fin k → Fin 2) : CauchySeq fun M => J (Aw k w (trunc f M)) := by
  set g : ℕ → ℝ := fun ℓ => qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 with hg
  have hgs : Summable g := summable_qpoly_coef hf hk
  have hg0 : ∀ ℓ, 0 ≤ g ℓ := fun ℓ => mul_nonneg (qpoly_nonneg k ℓ) (by positivity)
  set b : ℕ → ℝ := fun N => Real.sqrt (2 * π * ∑' ℓ, g (ℓ + N)) with hb
  have key : ∀ m n N, N ≤ m → m ≤ n →
      dist (J (Aw k w (trunc f n))) (J (Aw k w (trunc f m))) ≤ b N := by
    intro m n N hNm hmn
    rw [dist_eq_norm, ← map_sub, ← map_sub, trunc_sub f hmn]
    have h1 := norm_J_Aw_chi_le k w (Finset.Ico m n) (coef f)
    have h2 : ∑ ℓ ∈ Finset.Ico m n, g ℓ ≤ ∑' ℓ, g (ℓ + N) := by
      have hIco : Finset.Ico m n ⊆ (Finset.range (n - N)).map (addRightEmbedding N) := by
        intro ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        rw [Finset.mem_map]
        exact ⟨ℓ - N, Finset.mem_range.2 (by omega), by simp; omega⟩
      calc ∑ ℓ ∈ Finset.Ico m n, g ℓ
          ≤ ∑ ℓ ∈ (Finset.range (n - N)).map (addRightEmbedding N), g ℓ :=
            Finset.sum_le_sum_of_subset_of_nonneg hIco fun ℓ _ _ => hg0 ℓ
        _ = ∑ ℓ ∈ Finset.range (n - N), g (ℓ + N) := by
            rw [Finset.sum_map]
            rfl
        _ ≤ ∑' ℓ, g (ℓ + N) :=
            Summable.sum_le_tsum _ (fun ℓ _ => hg0 _) ((summable_nat_add_iff N).2 hgs)
    rw [hb]
    apply Real.le_sqrt_of_sq_le
    calc ‖J (Aw k w (chi (Finset.Ico m n) (coef f)))‖ ^ 2
        ≤ 2 * π * ∑ ℓ ∈ Finset.Ico m n, g ℓ := h1
      _ ≤ 2 * π * ∑' ℓ, g (ℓ + N) := by gcongr
  refine cauchySeq_of_le_tendsto_0 b (fun n m N hn hm => ?_) ?_
  · rcases le_total m n with h | h
    · exact key m n N hm h
    · rw [dist_comm]
      exact key n m N hn h
  · have h1 := tendsto_sum_nat_add g
    have h2 := (h1.const_mul (2 * π)).sqrt
    simpa [hb] using h2

/-- The `L²(ℝ², dy)` limit of the conjugated derivatives `A_w` of the truncations. -/
def gam (f : XG) (k : ℕ) (w : Fin k → Fin 2) : L2v :=
  limUnder atTop fun M => J (Aw k w (trunc f M))

theorem tendsto_gam {j : ℕ} {f : XG} (hf : f ∈ XGj j) {k : ℕ} (hk : k ≤ j)
    (w : Fin k → Fin 2) : Tendsto (fun M => J (Aw k w (trunc f M))) atTop (𝓝 (gam f k w)) :=
  (cauchySeq_Aw hf hk w).tendsto_limUnder

/-- The weak derivative `∂_w f = √G (gam f k w) = U_G⁻¹ (lim A_w U_G f_M)`. -/
def wd (f : XG) (k : ℕ) (w : Fin k → Fin 2) : ℝ × ℝ → ℂ :=
  fun z => sqGc z * (gam f k w : ℝ × ℝ → ℂ) z

theorem conjG_wd (f : XG) (k : ℕ) (w : Fin k → Fin 2) :
    B0093.conjG (wd f k w) = (gam f k w : ℝ × ℝ → ℂ) := by
  funext z
  rw [conjG_apply, wd, sqGc, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sqG_pos z).ne', Complex.ofReal_one, one_mul]

theorem conjG_wd_sub (f : XG) (k : ℕ) (w : Fin k → Fin 2) (ζ : S2) :
    B0093.conjG (fun z => wd f k w z - gS ζ z) = (gam f k w : ℝ × ℝ → ℂ) - ⇑ζ := by
  funext z
  have h1 := congrFun (conjG_wd f k w) z
  have h2 := congrFun (conjG_gS ζ) z
  rw [conjG_apply] at h1 h2 ⊢
  rw [Pi.sub_apply, mul_sub, h1, h2]

theorem memGaussL2_wd (f : XG) (k : ℕ) (w : Fin k → Fin 2) : MemGaussL2 (wd f k w) := by
  rw [MemGaussL2, conjG_wd]
  exact Lp.memLp _

theorem gaussNormSq_wd (f : XG) (k : ℕ) (w : Fin k → Fin 2) :
    gaussNormSq (wd f k w) = ‖gam f k w‖ ^ 2 := by
  rw [← norm_toLp_sq (memGaussL2_wd f k w)]
  congr 2
  rw [MemLp.toLp_congr (memGaussL2_wd f k w) (Lp.memLp (gam f k w))
    (Eventually.of_forall fun z => by rw [conjG_wd]), Lp.toLp_coeFn]

/-- **The weak derivatives of the planar function of `f ∈ X_{G,j}`**:
`wd f k w = ∂_{w 0} ⋯ ∂_{w (k-1)} f` weakly, for every word of length `k ≤ j`. -/
theorem hasWeakDerivOn_wd {j : ℕ} {f : XG} (hf : f ∈ XGj j) {k : ℕ} (hk : k ≤ j)
    (w : Fin k → Fin 2) : HasWeakDerivOn univ (dirs w) (planar f) (wd f k w) := by
  intro φ hφ
  have hΦt := (hφ.iterDirDeriv (dirs w))
  have hΦ : (iterDirDeriv (dirs w) φ).HasTemperateGrowth :=
    hΦt.compact.hasTemperateGrowth hΦt.smooth
  have hφT : φ.HasTemperateGrowth := hφ.compact.hasTemperateGrowth hφ.smooth
  -- left side
  have hd1 : ∀ M, MemGaussL2 fun z => planar f z - gS (trunc f M) z := fun M =>
    (planar_sub_gS f (isAngularTwo_trunc f M)).1
  have hn1 : ∀ M, ‖(hd1 M).toLp (B0093.conjG fun z => planar f z - gS (trunc f M) z)‖ =
      Real.sqrt (2 * π) * ‖f - toXG (trunc f M)‖ := by
    intro M
    obtain ⟨h, hh⟩ := planar_sub_gS f (isAngularTwo_trunc f M)
    rw [← Real.sqrt_sq (norm_nonneg _), hh, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (norm_nonneg _)]
  have L1 := tendsto_integral_mul_of_gauss (memGaussL2_planar f)
    (fun M => memGaussL2_gS (trunc f M)) hd1
    (by
      simp_rw [hn1]
      have h := (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_toXG_trunc f)).const_mul
        (Real.sqrt (2 * π))
      rw [mul_zero] at h
      refine h.congr fun M => ?_
      rw [norm_sub_rev]) hΦ
  -- right side
  have hd2 : ∀ M, MemGaussL2 fun z => wd f k w z - gS (Aw k w (trunc f M)) z := by
    intro M
    rw [MemGaussL2, conjG_wd_sub]
    exact (Lp.memLp _).sub ((Aw k w (trunc f M)).memLp 2 volume)
  have hn2 : ∀ M, ‖(hd2 M).toLp (B0093.conjG fun z => wd f k w z - gS (Aw k w (trunc f M)) z)‖ =
      ‖gam f k w - J (Aw k w (trunc f M))‖ := by
    intro M
    have e := conjG_wd_sub f k w (Aw k w (trunc f M))
    have hm : MemLp ((gam f k w : ℝ × ℝ → ℂ) - ⇑(Aw k w (trunc f M))) 2 volume :=
      (Lp.memLp _).sub ((Aw k w (trunc f M)).memLp 2 volume)
    rw [MemLp.toLp_congr (hd2 M) hm (Eventually.of_forall fun z => by rw [e]),
      MemLp.toLp_sub (Lp.memLp _) ((Aw k w (trunc f M)).memLp 2 volume), Lp.toLp_coeFn]
    rfl
  have L2 := tendsto_integral_mul_of_gauss (memGaussL2_wd f k w)
    (fun M => memGaussL2_gS (Aw k w (trunc f M))) hd2
    (by
      simp_rw [hn2]
      have h := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_gam hf hk w)
      refine h.congr fun M => ?_
      rw [norm_sub_rev]) hφT
  have E : ∀ M, ∫ z, gS (trunc f M) z * iterDirDeriv (dirs w) φ z =
      (-1 : ℂ) ^ (dirs w).length * ∫ z, gS (Aw k w (trunc f M)) z * φ z :=
    fun M => hasWeakDerivOn_gS k w (trunc f M) φ hφ
  have L1' := (L2.const_mul ((-1 : ℂ) ^ (dirs w).length)).congr fun M => (E M).symm
  exact tendsto_nhds_unique L1 L1'

/-- **Summing the levels**: `∑_{|w| = k} ‖∂_w f‖²_{L²(G⁻¹)} = 2π ∑_ℓ qpoly k (2 + ℓ) |⟪e_ℓ, f⟫|²`. -/
theorem sum_norm_sq_gam {j : ℕ} {f : XG} (hf : f ∈ XGj j) {k : ℕ} (hk : k ≤ j) :
    ∑ w : Fin k → Fin 2, ‖gam f k w‖ ^ 2 =
      2 * π * ∑' ℓ : ℕ, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2 := by
  have h1 : Tendsto (fun M => ∑ w : Fin k → Fin 2, ‖J (Aw k w (trunc f M))‖ ^ 2) atTop
      (𝓝 (∑ w : Fin k → Fin 2, ‖gam f k w‖ ^ 2)) :=
    tendsto_finset_sum _ fun w _ => ((tendsto_gam hf hk w).norm).pow 2
  have h2 : Tendsto (fun M => ∑ w : Fin k → Fin 2, ‖J (Aw k w (trunc f M))‖ ^ 2) atTop
      (𝓝 (2 * π * ∑' ℓ : ℕ, qpoly k (2 + ℓ) * ‖coef f ℓ‖ ^ 2)) := by
    have h := ((summable_qpoly_coef hf hk).hasSum.tendsto_sum_nat).const_mul (2 * π)
    refine h.congr fun M => ?_
    rw [trunc, sum_norm_sq_Aw_chi]
  exact tendsto_nhds_unique h1 h2

end UnforcedLeray.B0121
