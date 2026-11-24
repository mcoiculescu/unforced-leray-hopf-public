import UnforcedLeray.Lib.SobolevC.CylTransfer
import UnforcedLeray.Lib.SobolevB.WeightDensity

/-!
# Density of smooth periodic fields in `W^{k,p}(ρ)` on the cylinder (INF11 target S4)


target S4 (`W.cylinder_dense_smooth`); decisions D1 and D3 of `scoping/README.md` §3.
Manuscript uses: B0433 (tex 7550–7576, smooth approximation and mollification on the periodic
cylinder), B0892 (tex 13970–13985, "smooth approximation").

## Proof
For `x ∈ W^{k,p}(ρ)` on the cylinder, let `g_u` be the periodic extensions of its components,
moved to `Eucl 2` (`gfld`); they are `ℝ²` weak derivatives of `g_∅` (`hasWeakDeriv_gfld`,
from `CylExtend` and `CylTransfer`).
* **Cutoff.** With `cutQ R = cut1(·/R)` (`cut1 y = β(y₀)β(y₁)`), the Leibniz fields
  `hfld = ∑_u lcoef (cutQ R) w u · g_u` form an element `yR` of `W^{k,p}(ℝ²)` (weight `1`).
* **Mollification.** `vfun = ρ_j ⋆ (β(y₁/R) g_∅)` is smooth, periodic and vanishes for
  `|y₁| > 2R + 1`; near the cell it agrees with `ρ_j ⋆ (cutQ R · g_∅)`, whose derivatives are
  `ρ_j ⋆ hfld`, the components of `W.mollify yR`.  So `Ufun = vfun ∘ toPlane⁻¹` is an
  `IsCylSmooth` field (`isCylSmooth_Ufun`) with
  `‖∂^α Ufun - ∂^α x‖ ≤ C_R ‖∂^α(W.mollify yR) - ∂^α yR‖ + ‖hfld ∘ toPlane⁻¹ - ∂^α x‖`.
* The first term tends to `0` as `j → ∞` (`W.tendsto_mollify`), the second as `R → ∞`
  (the Leibniz coefficients of `cutQ R` scale like `R^{-(|w|-|u|)}`); a diagonal choice gives
  `W.cylinder_dense_smooth`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

/-! ### Cutoffs on `Eucl 2` -/

section Cut

/-- `β`: `1` on `[-1, 1]`, `0` outside `(-2, 2)`. -/
def bump1 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bump1_eq_one {t : ℝ} (ht : |t| ≤ 1) : bump1 t = 1 :=
  bump1.one_of_mem_closedBall (by rw [mem_closedBall, Real.dist_eq, sub_zero]; exact ht)

theorem bump1_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : bump1 t = 0 :=
  bump1.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)

/-- `cut1 y = β(y 0) β(y 1)`. -/
def cut1 (y : Eucl 2) : ℝ := bump1 (y 0) * bump1 (y 1)

theorem contDiff_cut1 : ContDiff ℝ ∞ cut1 :=
  (bump1.contDiff.comp (EuclideanSpace.proj (0 : Fin 2)).contDiff).mul
    (bump1.contDiff.comp (EuclideanSpace.proj (1 : Fin 2)).contDiff)

theorem cut1_eq_zero {y : Eucl 2} (h : 2 ≤ |y 0| ∨ 2 ≤ |y 1|) : cut1 y = 0 := by
  rcases h with h | h
  · simp [cut1, bump1_eq_zero h]
  · simp [cut1, bump1_eq_zero h]

theorem cut1_eq_one {y : Eucl 2} (h0 : |y 0| ≤ 1) (h1 : |y 1| ≤ 1) : cut1 y = 1 := by
  simp [cut1, bump1_eq_one h0, bump1_eq_one h1]

theorem cut1_nonneg (y : Eucl 2) : 0 ≤ cut1 y := mul_nonneg bump1.nonneg bump1.nonneg

theorem cut1_le_one (y : Eucl 2) : cut1 y ≤ 1 :=
  mul_le_one₀ bump1.le_one bump1.nonneg bump1.le_one

theorem support_cut1_subset : Function.support cut1 ⊆ boxE 2 2 := by
  intro y hy
  rw [mem_boxE]
  by_contra h
  rw [not_and_or, not_le, not_le] at h
  exact hy (cut1_eq_zero (h.imp le_of_lt le_of_lt))

theorem hasCompactSupport_cut1 : HasCompactSupport cut1 :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_boxE 2 2) support_cut1_subset

theorem bddDerivs_cut1 (r : ℕ) : BddDerivs r cut1 :=
  bddDerivs_of_hasCompactSupport contDiff_cut1 hasCompactSupport_cut1

/-- `cutQ R = cut1(·/R)`. -/
def cutQ (R : ℝ) (y : Eucl 2) : ℝ := cut1 (R⁻¹ • y)

/-- `cutE R y = β(y 1 / R)` (independent of `y 0`). -/
def cutE (R : ℝ) (y : Eucl 2) : ℝ := bump1 (R⁻¹ * y 1)

theorem contDiff_cutQ (R : ℝ) : ContDiff ℝ ∞ (cutQ R) :=
  contDiff_cut1.comp (contDiff_const_smul _)

theorem continuous_cutE (R : ℝ) : Continuous (cutE R) :=
  bump1.continuous.comp (continuous_const.mul (EuclideanSpace.proj (1 : Fin 2)).continuous)

theorem cutQ_eq_cutE {R : ℝ} (hR : 0 < R) {y : Eucl 2} (hy : |y 0| ≤ R) :
    cutQ R y = cutE R y := by
  have h0 : |R⁻¹ * y 0| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR), inv_mul_le_iff₀ hR, mul_one]
    exact hy
  simp only [cutQ, cut1, cutE, PiLp.smul_apply, smul_eq_mul]
  rw [bump1_eq_one h0, one_mul]

theorem cutE_eq_zero {R : ℝ} (hR : 0 < R) {y : Eucl 2} (hy : 2 * R ≤ |y 1|) : cutE R y = 0 := by
  apply bump1_eq_zero
  rw [abs_mul, abs_of_pos (inv_pos.mpr hR), le_inv_mul_iff₀ hR]
  linarith

theorem cutQ_eq_zero {R : ℝ} (hR : 0 < R) {y : Eucl 2} (hy : 2 * R ≤ |y 0| ∨ 2 * R ≤ |y 1|) :
    cutQ R y = 0 := by
  apply cut1_eq_zero
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hR),
    le_inv_mul_iff₀ hR]
  rcases hy with h | h
  · left; linarith
  · right; linarith

theorem tsupport_cutQ_subset {R : ℝ} (hR : 0 < R) : tsupport (cutQ R) ⊆ boxE (2 * R) (2 * R) := by
  refine closure_minimal (fun y hy => ?_) (isCompact_boxE _ _).isClosed
  rw [mem_boxE]
  by_contra h
  rw [not_and_or, not_le, not_le] at h
  exact hy (cutQ_eq_zero hR (h.imp le_of_lt le_of_lt))

theorem lcoef_cutQ (R : ℝ) (w u : List (Fin 2)) (y : Eucl 2) :
    lcoef (cutQ R) w u y = (R⁻¹) ^ (w.length - u.length) * lcoef cut1 w u (R⁻¹ • y) :=
  lcoef_dilate contDiff_cut1 _ w u y

theorem lcoef_cutQ_eq_zero {R : ℝ} (hR : 0 < R) (w u : List (Fin 2)) {y : Eucl 2}
    (hy : 2 * R < |y 0| ∨ 2 * R < |y 1|) : lcoef (cutQ R) w u y = 0 := by
  apply lcoef_eq_zero_of_notMem_tsupport
  intro hy'
  have := mem_boxE.mp (tsupport_cutQ_subset hR hy')
  rcases hy with h | h <;> linarith [this.1, this.2]

end Cut

/-! ### The components of a cylinder element and their extensions -/

section Fields

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ} {ρ : Weight (ℝ × ℝ)}

/-- The component of `x` along the word `u` (`0` for `|u| > k`). -/
def cfld (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2)) : ℝ × ℝ → F :=
  if h : u.length ≤ k then ⇑(W.deriv (cylinder c) ρ 𝕜 F k p (Idx.ofList u h) x) else 0

theorem cfld_of_le (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2)) (h : u.length ≤ k) :
    cfld x u = ⇑(W.deriv (cylinder c) ρ 𝕜 F k p (Idx.ofList u h) x) := dif_pos h

theorem length_toList_le (α : Idx 2 k) : (Idx.toList α).length ≤ k := by
  rw [Idx.length_toList]; exact Nat.lt_succ_iff.mp α.1.2

theorem cfld_toList (x : W (cylinder c) ρ 𝕜 F k p) (α : Idx 2 k) :
    cfld x (Idx.toList α) = ⇑(W.deriv (cylinder c) ρ 𝕜 F k p α x) := by
  rw [cfld_of_le x _ (length_toList_le α), Idx.ofList_toList]

theorem cfld_nil (x : W (cylinder c) ρ 𝕜 F k p) :
    cfld x [] = ⇑(W.value (cylinder c) ρ 𝕜 F k p x) := by
  rw [cfld_of_le x [] (Nat.zero_le _), Idx.ofList_nil]
  rfl

theorem stronglyMeasurable_cfld (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2)) :
    StronglyMeasurable (cfld x u) := by
  unfold cfld
  split_ifs
  · exact Lp.stronglyMeasurable _
  · exact stronglyMeasurable_const

theorem memLp_cfld (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2)) :
    MemLp (cfld x u) p (wμ (volume.restrict (cylCell c)) ρ) := by
  unfold cfld
  split_ifs
  · exact Lp.memLp _
  · exact MemLp.zero

theorem integrableOn_cfld (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2)) (M : ℝ) :
    IntegrableOn (cfld x u) (cylCell c ∩ {z | |z.2| ≤ M}) := by
  unfold cfld
  split_ifs with h
  · exact integrableOn_of_hasWeakDeriv_cylinder (W.hasWeakDeriv x (Idx.ofList u h)) M
  · exact integrableOn_zero

theorem eLpNorm_cfld_lt_top (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2))
    (M : ℝ) : eLpNorm (cfld x u) p (volume.restrict (cylCell c ∩ {z | |z.2| ≤ M})) < ⊤ :=
  eLpNorm_cell_inter_lt_top ρ hp (memLp_cfld x u) M

/-- The periodic extension of the component along `u`, on `Eucl 2`. -/
def gfld (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2)) : Eucl 2 → F :=
  perExt hc (cfld x u) ∘ toPlane

theorem gfld_of_mem (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2))
    {z : ℝ × ℝ} (hz : z ∈ cylCell c) : gfld hc x u (toPlane.symm z) = cfld x u z := by
  simp only [gfld, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact perExt_of_mem hc _ hz

theorem locallyIntegrable_gfld (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p)
    (u : List (Fin 2)) : LocallyIntegrable (gfld hc x u) volume :=
  locallyIntegrable_perExt_comp hc hp (stronglyMeasurable_cfld x u) (eLpNorm_cfld_lt_top hp x u)

theorem memLp_boxE_gfld (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p)
    (u : List (Fin 2)) (A M : ℝ) : MemLp (gfld hc x u) p (volume.restrict (boxE A M)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  exact memLp_boxE_perExt hc hp0 hp (stronglyMeasurable_cfld x u) (eLpNorm_cfld_lt_top hp x u) A M

/-- **The extended components are `ℝ²` weak derivatives of the extended field.** -/
theorem hasWeakDeriv_gfld (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (u : List (Fin 2))
    (h : u.length ≤ k) : HasWeakDeriv (wholeSpace 2) (u.map e) (gfld hc x []) (gfld hc x u) := by
  have hw := W.hasWeakDeriv x (Idx.ofList u h)
  rw [← cfld_nil x, ← cfld_of_le x u h] at hw
  have h1 := hasWeakDeriv_perExt hc (stronglyMeasurable_cfld x []) (stronglyMeasurable_cfld x u)
    (integrableOn_cfld x []) (integrableOn_cfld x u) hw
  have h2 := hasWeakDeriv_comp_toPlane h1
  rwa [map_cylinder_word, TestDomain.word_eq_map, Idx.toList_ofList, wholeSpace_dir] at h2

/-- The Leibniz fields of `cutQ R · g_∅`. -/
def hfld (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ) (w : List (Fin 2)) (y : Eucl 2) :
    F :=
  ∑ u ∈ wordSet k, lcoef (cutQ R) w u y • gfld hc x u y

theorem hfld_nil (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ) :
    hfld hc x R [] = fun y => cutQ R y • gfld hc x [] y :=
  funext fun y => sum_lcoef_nil_smul _ k _ y

theorem hasWeakDeriv_hfld (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ)
    (w : List (Fin 2)) (hw : w.length ≤ k) :
    HasWeakDeriv (wholeSpace 2) (w.map e) (hfld hc x R []) (hfld hc x R w) := by
  rw [hfld_nil]
  exact hasWeakDeriv_smul_word (contDiff_cutQ R) (gfld hc x)
    (fun u _ => locallyIntegrable_gfld hc hp x u) (fun u hu => hasWeakDeriv_gfld hc x u hu) w hw

theorem lcoef_cutQ_bounded {R : ℝ} (hR : 0 < R) (w u : List (Fin 2)) :
    ∃ B, ∀ y, ‖lcoef (cutQ R) w u y‖ ≤ B := by
  have hcs : HasCompactSupport (lcoef (cutQ R) w u) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_boxE (2 * R) (2 * R))
      fun y hy => ?_
    rw [mem_boxE]
    by_contra h
    rw [not_and_or, not_le, not_le] at h
    exact hy (lcoef_cutQ_eq_zero hR w u h)
  exact (contDiff_lcoef (contDiff_cutQ R) w u).continuous.bounded_above_of_compact_support hcs

theorem memLp_hfld (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ}
    (hR : 0 < R) (w : List (Fin 2)) : MemLp (hfld hc x R w) p volume := by
  unfold hfld
  refine memLp_finsetSum _ fun u _ => ?_
  set K := boxE (2 * R) (2 * R) with hKdef
  have hK : IsCompact K := isCompact_boxE _ _
  have hvan : ∀ y ∉ K, lcoef (cutQ R) w u y • gfld hc x u y = 0 := by
    intro y hy
    rw [hKdef, mem_boxE, not_and_or, not_le, not_le] at hy
    rw [lcoef_cutQ_eq_zero hR w u hy, zero_smul]
  have hind : (fun y => lcoef (cutQ R) w u y • gfld hc x u y) =
      K.indicator (fun y => lcoef (cutQ R) w u y • gfld hc x u y) := by
    funext y
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, hvan y hy]
  rw [hind, memLp_indicator_iff_restrict hK.measurableSet]
  obtain ⟨B, hB⟩ := lcoef_cutQ_bounded hR w u
  have hφ : MemLp (lcoef (cutQ R) w u) ⊤ (volume.restrict K) :=
    memLp_top_of_bound (contDiff_lcoef (contDiff_cutQ R) w u).continuous.aestronglyMeasurable B
      (Eventually.of_forall hB)
  exact (memLp_boxE_gfld hc hp x u _ _).smul (r := p) hφ

/-- **The cut-off extension as an element of `W^{k,p}(ℝ²)`** (weight `1`). -/
def yR (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ} (hR : 0 < R) :
    W (wholeSpace 2) 1 𝕜 F k p :=
  W.ofFields (fun α => hfld hc x R (Idx.toList α))
    (fun α => by rw [wμ_one]; exact memLp_hfld hc hp x hR _)
    (fun α => by
      have h := hasWeakDeriv_hfld hc hp x R (Idx.toList α) (length_toList_le α)
      rw [TestDomain.word_eq_map, wholeSpace_dir]
      exact h)

theorem deriv_yR (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ}
    (hR : 0 < R) (α : Idx 2 k) :
    ⇑(W.deriv (wholeSpace 2) 1 𝕜 F k p α (yR hc hp x hR)) =ᵐ[volume]
      hfld hc x R (Idx.toList α) := by
  have h := (W.deriv_ofFields (D := wholeSpace 2) (ρ := 1) (𝕜 := 𝕜) (F := F) (k := k) (p := p)
    (fun α => hfld hc x R (Idx.toList α))
    (fun α => by rw [wμ_one]; exact memLp_hfld hc hp x hR _)
    (fun α => by
      have h := hasWeakDeriv_hfld hc hp x R (Idx.toList α) (length_toList_le α)
      rw [TestDomain.word_eq_map, wholeSpace_dir]
      exact h) α)
  rw [yR, h]
  exact (ae_eq_wμ_iff volume 1).mp (MemLp.coeFn_toLp _)

end Fields

/-! ### The smooth periodic approximants -/

section Approx

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ} {ρ : Weight (ℝ × ℝ)}

theorem shrinkBump_rOut_le_one (j : ℕ) : (shrinkBump 2 j).rOut ≤ 1 := by
  show ((j : ℝ) + 1)⁻¹ ≤ 1
  exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])

/-- Mollifications only see the `rOut`-neighbourhood. -/
theorem moll_congr_ball {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (b : ContDiffBump (0 : Eucl 2)) {f g : Eucl 2 → G} {y : Eucl 2}
    (h : ∀ t : Eucl 2, ‖t‖ < b.rOut → f (y - t) = g (y - t)) :
    moll b volume f y = moll b volume g y := by
  rw [moll_apply_swap, moll_apply_swap]
  congr 1
  funext t
  by_cases ht : ‖t‖ < b.rOut
  · rw [h t ht]
  · have h0 : b.normed volume t = 0 := by
      by_contra hne
      have hmem : t ∈ Function.support (b.normed volume) := hne
      rw [b.support_normed_eq, mem_ball, dist_zero_right] at hmem
      exact ht hmem
    rw [h0, zero_smul, zero_smul]

theorem moll_zero' {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (b : ContDiffBump (0 : Eucl 2)) (y : Eucl 2) :
    moll b volume (fun _ => (0 : G)) y = 0 := by
  rw [moll_apply_swap]
  simp

theorem abs_sub_apply_one_gt {y t : Eucl 2} {a : ℝ} (ht : ‖t‖ < 1) (hy : a + 1 < |y 1|) :
    a < |(y - t) 1| := by
  have h1 : |t 1| ≤ ‖t‖ := by
    have := PiLp.norm_apply_le t 1
    rwa [Real.norm_eq_abs] at this
  have h2 := abs_sub_abs_le_abs_sub (y 1) (t 1)
  rw [PiLp.sub_apply]
  linarith

/-- `ρ_j ⋆ (β(y₁/R) g_∅)`. -/
def vfun (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ) (j : ℕ) : Eucl 2 → F :=
  moll (shrinkBump 2 j) volume (fun y => cutE R y • gfld hc x [] y)

/-- The approximant on the cylinder carrier. -/
def Ufun (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ) (j : ℕ) : ℝ × ℝ → F :=
  vfun hc x R j ∘ toPlane.symm

theorem toPlane_symm_c (c : ℝ) : toPlane.symm ((c, 0) : ℝ × ℝ) = c • e 0 := by
  rw [← toPlane_symm_cylDir 0, ← map_smul]
  congr 1
  ext <;> simp [cylDir]

theorem vfun_add (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ) (j : ℕ) (y : Eucl 2) :
    vfun hc x R j (y + c • e 0) = vfun hc x R j y := by
  unfold vfun
  rw [moll_apply_swap, moll_apply_swap]
  congr 1
  funext t
  rw [show y + c • e 0 - t = (y - t) + c • e 0 by abel]
  have h1 : cutE R ((y - t) + c • e 0) = cutE R (y - t) := by
    simp [cutE, e]
  have h2 : gfld hc x [] ((y - t) + c • e 0) = gfld hc x [] (y - t) := by
    simp only [gfld, Function.comp_apply, map_add, map_smul, toPlane_e]
    have hcd : c • cylDir 0 = ((c, 0) : ℝ × ℝ) := by ext <;> simp [cylDir]
    rw [hcd, perExt_add]
  rw [h1, h2]

theorem vfun_eq_zero (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ} (hR : 0 < R) (j : ℕ)
    {y : Eucl 2} (hy : 2 * R + 1 < |y 1|) : vfun hc x R j y = 0 := by
  have : vfun hc x R j y = moll (shrinkBump 2 j) volume (fun _ => (0 : F)) y := by
    refine moll_congr_ball _ fun t ht => ?_
    have h := abs_sub_apply_one_gt (ht.trans_le (shrinkBump_rOut_le_one j)) hy
    rw [cutE_eq_zero hR h.le, zero_smul]
  rw [this, moll_zero']

theorem locallyIntegrable_cutE_gfld (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p)
    (R : ℝ) : LocallyIntegrable (fun y => cutE R y • gfld hc x [] y) volume :=
  (locallyIntegrable_gfld hc hp x []).continuous_smul (continuous_cutE R)

theorem contDiff_vfun (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) (R : ℝ)
    (j : ℕ) : ContDiff ℝ ∞ (vfun hc x R j) :=
  contDiff_moll _ (locallyIntegrable_cutE_gfld hc hp x R)

/-- **The approximants are smooth periodic fields vanishing for `|η|` large.** -/
theorem isCylSmooth_Ufun (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ}
    (hR : 0 < R) (j : ℕ) : IsCylSmooth c (Ufun hc x R j) := by
  refine ⟨(contDiff_vfun hc hp x R j).comp toPlane.symm.contDiff, fun z => ?_,
    ⟨2 * R + 1, fun z hz => ?_⟩⟩
  · simp only [Ufun, Function.comp_apply, map_add, toPlane_symm_c]
    exact vfun_add hc x R j _
  · simp only [Ufun, Function.comp_apply]
    exact vfun_eq_zero hc x hR j (by rw [toPlane_symm_apply_one]; exact hz)

theorem hfld_eq_zero (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ} (hR : 0 < R)
    (w : List (Fin 2)) {y : Eucl 2} (hy : 2 * R < |y 1|) : hfld hc x R w y = 0 := by
  unfold hfld
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [lcoef_cutQ_eq_zero hR w u (Or.inr hy), zero_smul]

theorem moll_hfld_eq_zero (hc : 0 < c) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ} (hR : 0 < R)
    (w : List (Fin 2)) (j : ℕ) {y : Eucl 2} (hy : 2 * R + 1 < |y 1|) :
    moll (shrinkBump 2 j) volume (hfld hc x R w) y = 0 := by
  have : moll (shrinkBump 2 j) volume (hfld hc x R w) y =
      moll (shrinkBump 2 j) volume (fun _ => (0 : F)) y := by
    refine moll_congr_ball _ fun t ht => ?_
    exact hfld_eq_zero hc x hR w (abs_sub_apply_one_gt (ht.trans_le (shrinkBump_rOut_le_one j)) hy)
  rw [this, moll_zero']

/-- **Near the cell the derivatives of the approximant are mollified Leibniz fields.** -/
theorem iterD_Ufun (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ}
    (hR : 0 < R) (j : ℕ) (α : Idx 2 k) {z : ℝ × ℝ} (hz : |z.1| < R - 1) :
    iterD ((cylinder c).word α) (Ufun hc x R j) z =
      moll (shrinkBump 2 j) volume (hfld hc x R (Idx.toList α)) (toPlane.symm z) := by
  have hch := iterD_comp_clm (toPlane.symm : ℝ × ℝ →L[ℝ] Eucl 2) (contDiff_vfun hc hp x R j)
    ((cylinder c).word α)
  simp only [ContinuousLinearEquiv.coe_coe] at hch
  rw [Ufun, hch, Function.comp_apply, map_cylinder_word]
  set O : Set (Eucl 2) := {y | |y 0| < R - 1} with hO
  have hOo : IsOpen O := isOpen_lt (continuous_abs.comp (EuclideanSpace.proj (0 : Fin 2)).continuous)
    continuous_const
  have hTz : toPlane.symm z ∈ O := by
    show |(toPlane.symm z) 0| < R - 1
    rw [toPlane_symm_apply_zero]; exact hz
  have heq : EqOn (vfun hc x R j)
      (moll (shrinkBump 2 j) volume (fun y => cutQ R y • gfld hc x [] y)) O := by
    intro y hy
    refine moll_congr_ball _ fun t ht => ?_
    have ht1 : ‖t‖ < 1 := ht.trans_le (shrinkBump_rOut_le_one j)
    have h0 : |t 0| ≤ ‖t‖ := by
      have := PiLp.norm_apply_le t 0
      rwa [Real.norm_eq_abs] at this
    have hy0 : |y 0| < R - 1 := hy
    have h2 : |(y - t) 0| ≤ R := by
      rw [PiLp.sub_apply]
      have := abs_sub (y 0) (t 0)
      linarith
    rw [cutQ_eq_cutE hR h2]
  rw [iterD_eqOn hOo heq _ hTz]
  have hw := hasWeakDeriv_hfld hc hp x R (Idx.toList α) (length_toList_le α)
  rw [hfld_nil] at hw
  have hloc : LocallyIntegrable (fun y => cutQ R y • gfld hc x [] y) volume :=
    (locallyIntegrable_gfld hc hp x []).continuous_smul (contDiff_cutQ R).continuous
  have h2 := iterDD_cv_of_hasWeakDeriv (μ := volume) (dir := e)
    (hw : HasWeakDeriv (wholeSpaceOf (Eucl 2) volume e) _ _ _)
    ((shrinkBump 2 j).contDiff_normed (μ := volume))
    ((shrinkBump 2 j).hasCompactSupport_normed (μ := volume)) hloc
  rw [TestDomain.word_eq_map, wholeSpace_dir]
  exact congrFun h2 (toPlane.symm z)

end Approx

/-! ### The estimate for one approximant -/

section Estimate

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ} {ρ : Weight (ℝ × ℝ)}

theorem wμ_cylinder_ac (c : ℝ) (ρ : Weight (ℝ × ℝ)) : wμ (cylinder c).μ ρ ≪ volume :=
  (wμ_ac _ ρ).trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem abs_fst_le_of_mem_cylCell {z : ℝ × ℝ} (hz : z ∈ cylCell c) : |z.1| ≤ c / 2 :=
  abs_le.mpr ⟨hz.1.1, hz.1.2.le⟩

/-- **The estimate for one approximant**: with `H = hfld (toList α)`,
`‖∂^α Ufun - ∂^α x‖ ≤ C_R ‖ρ_j ⋆ H - H‖_{L²(ℝ²)} + ‖H ∘ toPlane⁻¹ - ∂^α x‖`. -/
theorem exists_bound_Ufun (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) {R : ℝ}
    (hR0 : 0 < R) (hR : c / 2 + 1 < R) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (j : ℕ) (α : Idx 2 k),
      eLpNorm (fun z => iterD ((cylinder c).word α) (Ufun hc x R j) z - cfld x (Idx.toList α) z)
          p (wμ (cylinder c).μ ρ) ≤
        C * eLpNorm (fun y => moll (shrinkBump 2 j) volume (hfld hc x R (Idx.toList α)) y -
              hfld hc x R (Idx.toList α) y) p volume +
          eLpNorm (fun z => hfld hc x R (Idx.toList α) (toPlane.symm z) - cfld x (Idx.toList α) z)
            p (wμ (cylinder c).μ ρ) := by
  set K : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R + 1)) (2 * R + 1) with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC, hle⟩ := eLpNorm_wμ_le_of_vanish' (F := F) (volume.restrict (cylCell c)) ρ hKc hp
  refine ⟨C, hC, fun j α => ?_⟩
  set w := Idx.toList α with hw
  set H := hfld hc x R w with hHdef
  set M := moll (shrinkBump 2 j) volume H with hMdef
  have hH : MemLp H p volume := memLp_hfld hc hp x hR0 w
  have hMc : Continuous M :=
    (contDiff_moll _ (hH.locallyIntegrable (Fact.out : (1 : ℝ≥0∞) ≤ p))).continuous
  have hac := wμ_cylinder_ac c ρ
  have hHT : AEStronglyMeasurable (fun z => H (toPlane.symm z)) volume :=
    hH.1.comp_measurePreserving measurePreserving_toPlane_symm
  set h1 : ℝ × ℝ → F := fun z => M (toPlane.symm z) - H (toPlane.symm z) with hh1
  set h2 : ℝ × ℝ → F := fun z => H (toPlane.symm z) - cfld x w z with hh2
  have hsplit : (fun z => iterD ((cylinder c).word α) (Ufun hc x R j) z - cfld x w z)
      =ᵐ[wμ (cylinder c).μ ρ] fun z => h1 z + h2 z := by
    refine (ae_eq_wμ_iff _ ρ).mpr ?_
    rw [cylinder_μ]
    filter_upwards [ae_restrict_mem (measurableSet_cylCell c)] with z hz
    have hz1 : |z.1| < R - 1 := by linarith [abs_fst_le_of_mem_cylCell hz]
    rw [iterD_Ufun hc hp x hR0 j α hz1]
    simp only [hh1, hh2, hMdef, hHdef]
    abel
  have hm1 : AEStronglyMeasurable h1 (wμ (cylinder c).μ ρ) :=
    (((hMc.comp toPlane.symm.continuous).aestronglyMeasurable).sub hHT).mono_ac hac
  have hm2 : AEStronglyMeasurable h2 (wμ (cylinder c).μ ρ) :=
    (hHT.mono_ac hac).sub (stronglyMeasurable_cfld x w).aestronglyMeasurable
  have hvan : ∀ᵐ z ∂(volume.restrict (cylCell c)), z ∉ K → h1 z = 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_cylCell c)] with z hz hzK
    have h2' : 2 * R + 1 < |z.2| := by
      by_contra hle'
      push_neg at hle'
      exact hzK ⟨Ico_subset_Icc_self hz.1, abs_le.mp hle'⟩
    have hT1 : 2 * R + 1 < |(toPlane.symm z) 1| := by rwa [toPlane_symm_apply_one]
    simp only [hh1, hMdef, hHdef, moll_hfld_eq_zero hc x hR0 w j hT1,
      hfld_eq_zero hc x hR0 w (by linarith : 2 * R < |(toPlane.symm z) 1|), sub_zero]
  have hcomp : eLpNorm ((fun y => M y - H y) ∘ toPlane.symm) p volume =
      eLpNorm (fun y => M y - H y) p volume :=
    eLpNorm_comp_measurePreserving (hMc.aestronglyMeasurable.sub hH.1)
      measurePreserving_toPlane_symm
  have hh1c : h1 = (fun y => M y - H y) ∘ toPlane.symm := rfl
  calc eLpNorm (fun z => iterD ((cylinder c).word α) (Ufun hc x R j) z - cfld x w z) p
        (wμ (cylinder c).μ ρ)
      = eLpNorm (fun z => h1 z + h2 z) p (wμ (cylinder c).μ ρ) := eLpNorm_congr_ae hsplit
    _ ≤ eLpNorm h1 p (wμ (cylinder c).μ ρ) + eLpNorm h2 p (wμ (cylinder c).μ ρ) :=
        eLpNorm_add_le hm1 hm2 Fact.out
    _ ≤ C * eLpNorm (fun y => M y - H y) p volume + eLpNorm h2 p (wμ (cylinder c).μ ρ) := by
        gcongr
        calc eLpNorm h1 p (wμ (cylinder c).μ ρ)
            ≤ C * eLpNorm h1 p (volume.restrict (cylCell c)) := hle h1 hvan
          _ ≤ C * eLpNorm h1 p volume := by
              gcongr
              exact Measure.restrict_le_self
          _ = C * eLpNorm (fun y => M y - H y) p volume := by rw [hh1c, hcomp]

end Estimate

/-! ### Removing the cutoff -/

section CutConv

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ} {ρ : Weight (ℝ × ℝ)}

/-- The cutoff radii `R_m = m + c + 2`. -/
def Rseq (c : ℝ) (m : ℕ) : ℝ := (m : ℝ) + c + 2

theorem Rseq_pos (hc : 0 < c) (m : ℕ) : 0 < Rseq c m := by
  unfold Rseq; positivity

theorem Rseq_gt (hc : 0 < c) (m : ℕ) : c / 2 + 1 < Rseq c m := by
  unfold Rseq; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith

theorem one_le_Rseq (hc : 0 < c) (m : ℕ) : 1 ≤ Rseq c m := by
  unfold Rseq; have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith

theorem tendsto_inv_Rseq (c : ℝ) : Tendsto (fun m => (Rseq c m)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) + c + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)
  exact tendsto_inv_atTop_zero.comp h1

theorem tendsto_cutQ (hc : 0 < c) (y : Eucl 2) :
    Tendsto (fun m => cutQ (Rseq c m) y) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (max |y 0| |y 1|)
  filter_upwards [eventually_ge_atTop N] with m hm
  symm
  have hR := Rseq_pos hc m
  have hRm : max |y 0| |y 1| ≤ Rseq c m := by
    unfold Rseq
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  apply cut1_eq_one
  · simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hR),
      inv_mul_le_iff₀ hR, mul_one]
    exact (le_max_left _ _).trans hRm
  · simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hR),
      inv_mul_le_iff₀ hR, mul_one]
    exact (le_max_right _ _).trans hRm

/-- One term of the Leibniz expansion of the cutoff tends to its limit in `L^p(ρ)` on the
cell. -/
theorem tendsto_cut_term (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p)
    (α : Idx 2 k) (u : List (Fin 2)) :
    Tendsto (fun m : ℕ => eLpNorm (fun z => lcoef (cutQ (Rseq c m)) (Idx.toList α) u
        (toPlane.symm z) • cfld x u z - (if u = Idx.toList α then cfld x u z else 0)) p
        (wμ (cylinder c).μ ρ)) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hf : MemLp (cfld x u) p (wμ (cylinder c).μ ρ) := memLp_cfld x u
  have hα := length_toList_le α
  by_cases hu : u = Idx.toList α
  · subst hu
    have h := tendsto_eLpNorm_smul_of_tendsto hp0 hp hf
      (c := fun m z => cutQ (Rseq c m) (toPlane.symm z) - 1)
      (fun m => ((((contDiff_cutQ _).continuous.comp toPlane.symm.continuous).sub
        continuous_const)).aestronglyMeasurable)
      (fun m z => by
        rw [abs_le]
        constructor <;>
          linarith [cut1_nonneg ((Rseq c m)⁻¹ • toPlane.symm z),
            cut1_le_one ((Rseq c m)⁻¹ • toPlane.symm z),
            show cutQ (Rseq c m) (toPlane.symm z) = cut1 ((Rseq c m)⁻¹ • toPlane.symm z) from rfl])
      (fun z => by simpa using (tendsto_cutQ hc (toPlane.symm z)).sub_const 1)
    refine h.congr fun m => ?_
    congr 1
    funext z
    rw [lcoef_self, if_pos rfl, sub_smul, one_smul]
  · by_cases hlen : u.length < (Idx.toList α).length
    · obtain ⟨B, hB⟩ := (bddDerivs_lcoef (bddDerivs_cut1 k) (Idx.toList α) hα u).bounded
      have hbound : ∀ m : ℕ, eLpNorm (fun z => lcoef (cutQ (Rseq c m)) (Idx.toList α) u
          (toPlane.symm z) • cfld x u z - (if u = Idx.toList α then cfld x u z else 0)) p
          (wμ (cylinder c).μ ρ) ≤ ENNReal.ofReal ((Rseq c m)⁻¹ * B) *
            eLpNorm (cfld x u) p (wμ (cylinder c).μ ρ) := by
        intro m
        simp only [if_neg hu, sub_zero]
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) p
        have hs0 : 0 ≤ (Rseq c m)⁻¹ := inv_nonneg.mpr (Rseq_pos hc m).le
        have hs1 : (Rseq c m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_Rseq hc m)
        have hpow : ((Rseq c m)⁻¹) ^ ((Idx.toList α).length - u.length) ≤ (Rseq c m)⁻¹ :=
          pow_le_of_le_one hs0 hs1 (by omega)
        rw [norm_smul, Real.norm_eq_abs, lcoef_cutQ, abs_mul, abs_of_nonneg (pow_nonneg hs0 _)]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul hpow (hB _) (abs_nonneg _) hs0
      have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal ((Rseq c m)⁻¹ * B) *
          eLpNorm (cfld x u) p (wμ (cylinder c).μ ρ)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun m : ℕ => (Rseq c m)⁻¹ * B) atTop (𝓝 0) := by
          simpa using (tendsto_inv_Rseq c).mul_const B
        have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hf.2.ne)
        simpa using h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun m => zero_le) hbound
    · have hz : ∀ m : ℕ, lcoef (cutQ (Rseq c m)) (Idx.toList α) u = 0 := by
        intro m
        rcases Nat.lt_or_ge (Idx.toList α).length u.length with h | h
        · exact lcoef_eq_zero _ h
        · rw [lcoef_diag _ (by omega), if_neg hu]
      refine tendsto_const_nhds.congr fun m => ?_
      simp [hz m, hu]

/-- **The cutoff error tends to `0`** as `R → ∞`. -/
theorem tendsto_hfld_sub (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p)
    (α : Idx 2 k) :
    Tendsto (fun m : ℕ => eLpNorm (fun z => hfld hc x (Rseq c m) (Idx.toList α) (toPlane.symm z) -
        cfld x (Idx.toList α) z) p (wμ (cylinder c).μ ρ)) atTop (𝓝 0) := by
  have hα : Idx.toList α ∈ wordSet (n := 2) k := mem_wordSet.mpr (length_toList_le α)
  set term : ℕ → List (Fin 2) → ℝ × ℝ → F := fun m u z =>
    lcoef (cutQ (Rseq c m)) (Idx.toList α) u (toPlane.symm z) • cfld x u z -
      (if u = Idx.toList α then cfld x u z else 0) with hterm
  have hrep : ∀ m : ℕ, (fun z => hfld hc x (Rseq c m) (Idx.toList α) (toPlane.symm z) -
      cfld x (Idx.toList α) z) =ᵐ[wμ (cylinder c).μ ρ] ∑ u ∈ wordSet k, term m u := by
    intro m
    refine (ae_eq_wμ_iff _ ρ).mpr ?_
    rw [cylinder_μ]
    filter_upwards [ae_restrict_mem (measurableSet_cylCell c)] with z hz
    rw [Finset.sum_apply]
    simp only [hterm, hfld]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (wordSet k) (Idx.toList α), if_pos hα]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gfld_of_mem hc x u hz]
  have hmeas : ∀ m : ℕ, ∀ u ∈ wordSet (n := 2) k,
      AEStronglyMeasurable (term m u) (wμ (cylinder c).μ ρ) := by
    intro m u _
    have h2 : AEStronglyMeasurable (fun z => if u = Idx.toList α then cfld x u z else 0)
        (wμ (cylinder c).μ ρ) := by
      by_cases h : u = Idx.toList α
      · simp only [h, if_true]; exact (stronglyMeasurable_cfld x _).aestronglyMeasurable
      · simp only [h, if_false]; exact aestronglyMeasurable_const
    exact ((((contDiff_lcoef (contDiff_cutQ _) _ u).continuous.comp
      toPlane.symm.continuous).aestronglyMeasurable).smul
        (stronglyMeasurable_cfld x u).aestronglyMeasurable).sub h2
  have hle : ∀ m : ℕ, eLpNorm (fun z => hfld hc x (Rseq c m) (Idx.toList α) (toPlane.symm z) -
      cfld x (Idx.toList α) z) p (wμ (cylinder c).μ ρ) ≤
        ∑ u ∈ wordSet k, eLpNorm (term m u) p (wμ (cylinder c).μ ρ) := by
    intro m
    rw [eLpNorm_congr_ae (hrep m)]
    exact eLpNorm_sum_le (hmeas m) Fact.out
  have hsum : Tendsto (fun m : ℕ => ∑ u ∈ wordSet k, eLpNorm (term m u) p (wμ (cylinder c).μ ρ))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (wordSet k) fun u _ => tendsto_cut_term hc hp x α u
    simpa [hterm] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun m => zero_le) hle

end CutConv

/-! ### Density -/

section Main

variable {F : Type*} [NormedAddCommGroup F] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F]
  {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ} {ρ : Weight (ℝ × ℝ)}

/-- **Density of smooth periodic fields on the cylinder** (S4, `W.cylinder_dense_smooth`;
B0433 tex 7550–7576, B0892 tex 13970–13985): for `c > 0`, `1 ≤ p < ∞`, every weight `ρ` and
every `k`, the elements of `W^{k,p}(ρ)` on the cylinder `ℝ/cℤ × ℝ` whose field is (a.e. on the
cell) a smooth `c`-periodic field vanishing for `|η|` large are dense. -/
theorem W.cylinder_dense_smooth (hc : 0 < c) (hp : p ≠ ⊤) :
    Dense {x : W (cylinder c) ρ 𝕜 F k p | ∃ u : ℝ × ℝ → F, IsCylSmooth c u ∧
      (W.value (cylinder c) ρ 𝕜 F k p x : ℝ × ℝ → F) =ᵐ[(cylinder c).μ] u} := by
  intro x
  choose C hC hbound using fun m : ℕ =>
    exists_bound_Ufun (ρ := ρ) hc hp x (Rseq_pos hc m) (Rseq_gt hc m)
  set E : ℕ → ℕ → Idx 2 k → ℝ≥0∞ := fun m j α =>
    eLpNorm (fun y => moll (shrinkBump 2 j) volume (hfld hc x (Rseq c m) (Idx.toList α)) y -
      hfld hc x (Rseq c m) (Idx.toList α) y) p volume with hE
  have hEt : ∀ (m : ℕ) (α : Idx 2 k), Tendsto (fun j => C m * E m j α) atTop (𝓝 0) := by
    intro m α
    have hR := Rseq_pos hc m
    have h1 := W.tendsto_mollify hp (tendsto_shrinkBump_rOut 2) (yR hc hp x hR)
    have h2 := ((W.deriv (wholeSpace 2) 1 𝕜 F k p α).continuous.tendsto _).comp h1
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h2
    have h3 : Tendsto (fun j => E m j α) atTop (𝓝 0) := by
      refine h2.congr fun j => ?_
      simp only [Function.comp_apply, hE]
      have hmoll : moll (shrinkBump 2 j) volume
          ⇑(W.deriv (wholeSpace 2) 1 𝕜 F k p α (yR hc hp x hR)) =
            moll (shrinkBump 2 j) volume (hfld hc x (Rseq c m) (Idx.toList α)) :=
        cv_congr_ae _ (deriv_yR hc hp x hR α)
      refine (eLpNorm_wμ_one _ p).trans (eLpNorm_congr_ae ?_)
      filter_upwards [(ae_eq_wμ_iff volume 1).mp
        (W.memLp_moll_deriv hp (shrinkBump 2 j) (yR hc hp x hR) α).coeFn_toLp,
        deriv_yR hc hp x hR α] with y hy1 hy2
      rw [Pi.sub_apply, W.deriv_mollify, hy2, ← hmoll]
      exact congrArg (· - _) hy1
    simpa using ENNReal.Tendsto.const_mul h3 (Or.inr (hC m))
  have hJ : ∀ m : ℕ, ∃ j, ∀ α : Idx 2 k, C m * E m j α ≤ (m : ℝ≥0∞)⁻¹ := by
    intro m
    have hpos : (0 : ℝ≥0∞) < (m : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top m)
    exact (eventually_all.mpr fun α => ENNReal.tendsto_nhds_zero.mp (hEt m α) _ hpos).exists
  choose J hJ using hJ
  set Y : ℕ → W (cylinder c) ρ 𝕜 F k p := fun m =>
    W.ofCylSmooth 𝕜 k p ρ hc (Ufun hc x (Rseq c m) (J m))
      (isCylSmooth_Ufun hc hp x (Rseq_pos hc m) (J m)) with hY
  have hlim : Tendsto Y atTop (𝓝 x) := by
    refine W.tendsto_of_deriv fun α => ?_
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hle : ∀ m : ℕ, eLpNorm (⇑(W.deriv (cylinder c) ρ 𝕜 F k p α (Y m)) -
        ⇑(W.deriv (cylinder c) ρ 𝕜 F k p α x)) p (wμ (cylinder c).μ ρ) ≤
          (m : ℝ≥0∞)⁻¹ + eLpNorm (fun z => hfld hc x (Rseq c m) (Idx.toList α) (toPlane.symm z) -
            cfld x (Idx.toList α) z) p (wμ (cylinder c).μ ρ) := by
      intro m
      have hae : (⇑(W.deriv (cylinder c) ρ 𝕜 F k p α (Y m)) -
          ⇑(W.deriv (cylinder c) ρ 𝕜 F k p α x)) =ᵐ[wμ (cylinder c).μ ρ]
            fun z => iterD ((cylinder c).word α) (Ufun hc x (Rseq c m) (J m)) z -
              cfld x (Idx.toList α) z := by
        filter_upwards [W.deriv_ofCylSmooth (ρ := ρ) (𝕜 := 𝕜) (k := k) (p := p) hc _
          (isCylSmooth_Ufun hc hp x (Rseq_pos hc m) (J m)) α] with z hz
        rw [Pi.sub_apply, hz, cfld_toList]
      rw [eLpNorm_congr_ae hae]
      refine (hbound m (J m) α).trans ?_
      gcongr
      exact hJ m α
    have hlim' : Tendsto (fun m : ℕ => (m : ℝ≥0∞)⁻¹ + eLpNorm (fun z =>
        hfld hc x (Rseq c m) (Idx.toList α) (toPlane.symm z) - cfld x (Idx.toList α) z) p
          (wμ (cylinder c).μ ρ)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_inv_nat_nhds_zero.add (tendsto_hfld_sub hc hp x α)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim' (fun m => zero_le) hle
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun m =>
    ⟨_, isCylSmooth_Ufun hc hp x (Rseq_pos hc m) (J m),
      (ae_eq_wμ_iff _ ρ).mp (W.value_ofCylSmooth hc _ _)⟩)

/-- Sequential form of `W.cylinder_dense_smooth`. -/
theorem W.exists_seq_cylSmooth (hc : 0 < c) (hp : p ≠ ⊤) (x : W (cylinder c) ρ 𝕜 F k p) :
    ∃ y : ℕ → W (cylinder c) ρ 𝕜 F k p, (∀ j, ∃ u : ℝ × ℝ → F, IsCylSmooth c u ∧
      (W.value (cylinder c) ρ 𝕜 F k p (y j) : ℝ × ℝ → F) =ᵐ[(cylinder c).μ] u) ∧
        Tendsto y atTop (𝓝 x) := by
  have h := (W.cylinder_dense_smooth (𝕜 := 𝕜) (F := F) (k := k) (ρ := ρ) hc hp).closure_eq ▸
    Set.mem_univ x
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp h
  exact ⟨y, hy, hlim⟩

end Main

end UnforcedLeray.Sob
