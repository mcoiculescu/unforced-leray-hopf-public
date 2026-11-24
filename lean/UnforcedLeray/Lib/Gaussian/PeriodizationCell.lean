import UnforcedLeray.Lib.Gaussian.Periodization
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The periodization operator on the cell (INF22 G7, part 2)


target G7, lemmas 4–6. Units B0364 (tex 6788–6801), B0314/B0352/B0638 (tex 6037–6045,
6645–6653, 12572–12582), B0147 (tex 2217–2234), B0894.

The cell is `[0, c) × ℝ` (`cell c`); the centred cell of decision D1 is its translate by `c/2`,
and the cell integral of a `c`-periodic function does not depend on the choice.

Main results:
* `integral_cell_periodize` (lemma 4): `∫_{[0,c)×ℝ} P_c f = ∫_{ℝ²} f` for integrable `f`;
* `integral_cell_weight_periodize` (lemma 5, B0364): the same with a weight `φ(η)` depending only
  on the transverse variable, e.g. the moment functional `Q_c(w) = -(2/π)∫_cell η² w`, so
  `Q_c(P_c f) = Q_∞(f)`;
* `lintegral_cell_sq_norm_periodize_le_of_gauss` (lemma 6, cell `L²` part; B0147): if
  `‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}` and `0 < a ≤ c²`, then
  `∫_cell ‖P_c f‖² ≤ 40π A² a`, uniformly in `c` (stated with the lower integral, which needs no
  measurability of `P_c f`).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Set Real
open scoped ENNReal

/-! ### Cells and their translates -/

/-- The fundamental cell `[0, c) × ℝ`. -/
def cell (c : ℝ) : Set (ℝ × ℝ) := Ico 0 c ×ˢ univ

theorem measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- The translated cell `{w | w + (nc, 0) ∈ cell c}`. -/
def tcell (c : ℝ) (n : ℤ) : Set (ℝ × ℝ) := (fun w => w + shiftVec c n) ⁻¹' cell c

theorem mem_tcell {c : ℝ} {n : ℤ} {w : ℝ × ℝ} : w ∈ tcell c n ↔ w.1 + n * c ∈ Ico 0 c := by
  simp [tcell, cell, shiftVec]

theorem measurableSet_tcell (c : ℝ) (n : ℤ) : MeasurableSet (tcell c n) :=
  (measurableSet_cell c).preimage (measurable_id.add_const _)

theorem pairwise_disjoint_tcell {c : ℝ} (hc : 0 < c) :
    Pairwise (Function.onFun Disjoint (tcell c)) := by
  intro m n hmn
  show Disjoint (tcell c m) (tcell c n)
  rw [Set.disjoint_left]
  intro w hm hn
  rw [mem_tcell] at hm hn
  obtain ⟨k, _, hk⟩ := existsUnique_add_zsmul_mem_Ico hc w.1 0
  have h1 := hk m (by show w.1 + m • c ∈ Ico 0 (0 + c); rwa [zsmul_eq_mul, zero_add])
  have h2 := hk n (by show w.1 + n • c ∈ Ico 0 (0 + c); rwa [zsmul_eq_mul, zero_add])
  exact hmn (h1.trans h2.symm)

theorem iUnion_tcell {c : ℝ} (hc : 0 < c) : ⋃ n, tcell c n = univ := by
  refine eq_univ_of_forall fun w => mem_iUnion.2 ?_
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ico hc w.1 0
  refine ⟨k, mem_tcell.2 ?_⟩
  rwa [zsmul_eq_mul, zero_add] at hk

theorem preimage_sub_tcell (c : ℝ) (n : ℤ) :
    (fun z => z - shiftVec c n) ⁻¹' tcell c n = cell c := by
  ext z; simp [tcell]

section Translate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem setIntegral_cell_translate (f : ℝ × ℝ → E) (c : ℝ) (n : ℤ) :
    ∫ z in cell c, f (z - shiftVec c n) = ∫ w in tcell c n, f w := by
  have h := (measurePreserving_sub_right volume (shiftVec c n)).setIntegral_preimage_emb
    (measurableEmbedding_subRight (shiftVec c n)) f (tcell c n)
  rwa [preimage_sub_tcell] at h

theorem setLIntegral_cell_translate (f : ℝ × ℝ → ℝ≥0∞) (c : ℝ) (n : ℤ) :
    ∫⁻ z in cell c, f (z - shiftVec c n) = ∫⁻ w in tcell c n, f w := by
  have h := (measurePreserving_sub_right volume (shiftVec c n)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_subRight (shiftVec c n)) f (tcell c n)
  rwa [preimage_sub_tcell] at h

/-- `∑_n ∫_cell g(z - (nc,0)) = ∫_{ℝ²} g` for the lower integral. -/
theorem tsum_setLIntegral_cell_translate (g : ℝ × ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    ∑' n : ℤ, ∫⁻ z in cell c, g (z - shiftVec c n) = ∫⁻ w, g w := by
  simp_rw [setLIntegral_cell_translate g c]
  rw [← lintegral_iUnion (measurableSet_tcell c) (pairwise_disjoint_tcell hc), iUnion_tcell hc,
    Measure.restrict_univ]

/-- **G7, lemma 4.** `∫_{[0,c)×ℝ} P_c f = ∫_{ℝ²} f` for integrable `f` and `c > 0`. -/
theorem integral_cell_periodize [CompleteSpace E] {f : ℝ × ℝ → E} (hf : Integrable f) {c : ℝ}
    (hc : 0 < c) : ∫ z in cell c, periodize c f z = ∫ z, f z := by
  simp_rw [periodize_eq]
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (fun z => f (z - shiftVec c n))
      (volume.restrict (cell c)) :=
    fun n => (hf.comp_sub_right (shiftVec c n)).aestronglyMeasurable.restrict
  have hlin : ∑' n : ℤ, ∫⁻ z in cell c, ‖f (z - shiftVec c n)‖ₑ = ∫⁻ w, ‖f w‖ₑ :=
    tsum_setLIntegral_cell_translate (fun w => ‖f w‖ₑ) hc
  rw [integral_tsum hmeas (by rw [hlin]; exact hf.2.ne)]
  simp_rw [setIntegral_cell_translate f c]
  rw [← integral_iUnion (measurableSet_tcell c) (pairwise_disjoint_tcell hc)
    (by rw [iUnion_tcell hc]; exact hf.integrableOn), iUnion_tcell hc, Measure.restrict_univ]

/-- A weight depending only on `η` passes through the periodization. -/
theorem periodize_weight_smul (φ : ℝ → ℝ) (f : ℝ × ℝ → E) (c : ℝ) (z : ℝ × ℝ) :
    periodize c (fun w => φ w.2 • f w) z = φ z.2 • periodize c f z := by
  unfold periodize
  exact tsum_const_smul'' (φ z.2)

/-- **G7, lemma 5 (B0364, tex 6788–6801).** Weighted cell integrals of periodizations:
`∫_cell φ(η) P_c f = ∫_{ℝ²} φ(η) f` whenever `φ(η) f` is integrable. With `φ(η) = -(2/π)η²`
this is `Q_c(P_c f) = Q_∞(f)`. -/
theorem integral_cell_weight_periodize [CompleteSpace E] (φ : ℝ → ℝ) {f : ℝ × ℝ → E}
    (hf : Integrable (fun w : ℝ × ℝ => φ w.2 • f w)) {c : ℝ} (hc : 0 < c) :
    ∫ z in cell c, φ z.2 • periodize c f z = ∫ z, φ z.2 • f z := by
  simp_rw [← periodize_weight_smul φ f c]
  exact integral_cell_periodize hf hc

end Translate

/-! ### The cell `L²` bound under a Gaussian translate bound -/

/-- The planar Gaussian integral `∫_{ℝ²} e^{-(q²+η²)/(4a)} = 4πa`, with integrability. -/
theorem integrable_gauss_plane {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) := by
  have hb : 0 < 1 / (4 * a) := by positivity
  have h := (integrable_exp_neg_mul_sq hb).mul_prod (integrable_exp_neg_mul_sq hb)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [← Real.exp_add]; congr 1; ring

theorem integral_gauss_plane {a : ℝ} (ha : 0 < a) :
    ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a)) = 4 * π * a := by
  have hb : 0 < 1 / (4 * a) := by positivity
  have hfun : (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) =
      fun z => Real.exp (-(1 / (4 * a)) * z.1 ^ 2) * Real.exp (-(1 / (4 * a)) * z.2 ^ 2) := by
    funext z; rw [← Real.exp_add]; congr 1; ring
  have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => Real.exp (-(1 / (4 * a)) * x ^ 2))
    (fun x : ℝ => Real.exp (-(1 / (4 * a)) * x ^ 2))
  rw [integral_gaussian, Real.mul_self_sqrt (by positivity)] at h
  rw [hfun, Measure.volume_eq_prod]
  refine h.trans ?_
  field_simp

section L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **G7, lemma 6 (cell `L²` part; B0147, tex 2217–2234).** If `‖f(q,η)‖ ≤ A e^{-(q²+η²)/(4a)}`
with `0 < a ≤ c²` and `c > 0`, then `∫_{[0,c)×ℝ} ‖P_c f‖² ≤ 40π A² a`, uniformly in `c`. -/
theorem lintegral_cell_sq_norm_periodize_le_of_gauss {f : ℝ × ℝ → E} {A a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hac : a ≤ c ^ 2) (hfm : AEStronglyMeasurable f)
    (hf : ∀ z : ℝ × ℝ, ‖f z‖ ≤ A * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * a))) :
    ∫⁻ z in cell c, ‖periodize c f z‖ₑ ^ 2 ≤ ENNReal.ofReal (40 * π * A ^ 2 * a) := by
  have hA : 0 ≤ A := by
    have h := hf 0
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    norm_num at h
    exact (norm_nonneg _).trans h
  have hsplit : ∀ (z : ℝ × ℝ) (n : ℤ),
      A * Real.exp (-((z.1 - n * c) ^ 2 + z.2 ^ 2) / (4 * a)) =
      A * Real.exp (-z.2 ^ 2 / (4 * a)) * Real.exp (-(z.1 - n * c) ^ 2 / (4 * a)) := by
    intro z n; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hgsum : ∀ z : ℝ × ℝ, Summable fun n : ℤ =>
      A * Real.exp (-((z.1 - n * c) ^ 2 + z.2 ^ 2) / (4 * a)) := by
    intro z; simp_rw [hsplit]; exact (summable_gauss_shift ha hac z.1).mul_left _
  have hnsum : ∀ z : ℝ × ℝ, Summable fun n : ℤ => ‖f (z.1 - n * c, z.2)‖ := fun z =>
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hf _) (hgsum z)
  -- pointwise: ‖P_c f‖ ≤ ∑ ‖f_n‖ ≤ 10 A
  have hpt1 : ∀ z : ℝ × ℝ, ‖periodize c f z‖ ≤ ∑' n : ℤ, ‖f (z.1 - n * c, z.2)‖ :=
    fun z => norm_tsum_le_tsum_norm (hnsum z)
  have hpt2 : ∀ z : ℝ × ℝ, ∑' n : ℤ, ‖f (z.1 - n * c, z.2)‖ ≤ 10 * A := by
    intro z
    refine ((hnsum z).tsum_le_tsum (fun n => hf _) (hgsum z)).trans ?_
    simp_rw [hsplit]
    rw [tsum_mul_left]
    have h10 := tsum_gauss_shift_le ha hac z.1
    have he : Real.exp (-z.2 ^ 2 / (4 * a)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ z.2 ^ 2 / (4 * a) := by positivity
      rw [neg_div]; linarith)
    have h0 : 0 ≤ ∑' n : ℤ, Real.exp (-(z.1 - n * c) ^ 2 / (4 * a)) :=
      tsum_nonneg fun n => (Real.exp_pos _).le
    calc A * Real.exp (-z.2 ^ 2 / (4 * a)) * ∑' n : ℤ, Real.exp (-(z.1 - n * c) ^ 2 / (4 * a))
        ≤ A * 1 * 10 := by gcongr
      _ = 10 * A := by ring
  -- ‖P_c f‖ₑ² ≤ ofReal(10A) * ∑ ‖f_n‖ₑ
  have hpt : ∀ z : ℝ × ℝ, ‖periodize c f z‖ₑ ^ 2 ≤
      ENNReal.ofReal (10 * A) * ∑' n : ℤ, ‖f (z - shiftVec c n)‖ₑ := by
    intro z
    have hS : ∑' n : ℤ, ‖f (z - shiftVec c n)‖ₑ =
        ENNReal.ofReal (∑' n : ℤ, ‖f (z.1 - n * c, z.2)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hnsum z)]
      congr 1; funext n
      rw [sub_shiftVec, ofReal_norm]
    rw [hS, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hpt1 z
    have h2 := hpt2 z
    have h0 : 0 ≤ ‖periodize c f z‖ := norm_nonneg _
    nlinarith
  have hmeas : ∀ n : ℤ, AEMeasurable (fun z => ‖f (z - shiftVec c n)‖ₑ)
      (volume.restrict (cell c)) := fun n =>
    ((hfm.comp_measurePreserving (measurePreserving_sub_right volume (shiftVec c n))).enorm).restrict
  have hint := (integrable_gauss_plane ha).const_mul A
  calc ∫⁻ z in cell c, ‖periodize c f z‖ₑ ^ 2
      ≤ ∫⁻ z in cell c, ENNReal.ofReal (10 * A) * ∑' n : ℤ, ‖f (z - shiftVec c n)‖ₑ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (10 * A) * ∑' n : ℤ, ∫⁻ z in cell c, ‖f (z - shiftVec c n)‖ₑ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeas]
    _ = ENNReal.ofReal (10 * A) * ∫⁻ w, ‖f w‖ₑ := by
        rw [tsum_setLIntegral_cell_translate (fun w => ‖f w‖ₑ) hc]
    _ ≤ ENNReal.ofReal (10 * A) *
          ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (A * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * a))) := by
        gcongr with w
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hf w)
    _ = ENNReal.ofReal (10 * A) * ENNReal.ofReal (A * (4 * π * a)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun z => by positivity)]
        rw [integral_const_mul, integral_gauss_plane ha]
    _ = ENNReal.ofReal (40 * π * A ^ 2 * a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end L2

end UnforcedLeray.Gaussian
