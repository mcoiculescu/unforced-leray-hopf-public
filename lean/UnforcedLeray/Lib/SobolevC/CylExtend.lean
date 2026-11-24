import UnforcedLeray.Lib.SobolevC.CylSmooth
import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Periodic extension of cylinder fields to `ℝ²` (INF11 target S4, cylinder part, step 2)


(S4, `W.cylinder_dense_smooth`; S14 "periodic weak derivative ↔ `ℝ²` weak derivative of the
periodic field"); decision D1 of `scoping/README.md` §3.  Manuscript use: B0433 (tex
7550–7576), B0892 (tex 13970–13985).

## Main declarations
* `perExt hc f`: the `c`-periodic extension of a function on the cell `[-c/2, c/2) × ℝ`;
* `perSum c χ`: the periodization `∑ᶠ m, χ(· + (mc, 0))` of a compactly supported test, a cylinder
  test (`isCylTest_perSum`) whose derivatives are the periodizations of the derivatives
  (`iterDirDeriv_perSum`);
* `lintegral_unfold`, `integral_unfold`: `∫_{ℝ²} h = ∑'_m ∫_{cell} h(· + (mc, 0))`;
* `integral_smul_perExt`: `∫_{ℝ²} χ • perExt f = ∫_{cell} perSum χ • f`;
* `hasWeakDeriv_perExt`: a periodic weak derivative on the cylinder is an `ℝ²` weak derivative of
  the periodic extensions;
* `integrableOn_of_hasWeakDeriv_cylinder`: the fields of a periodic weak derivative are integrable
  on every `cell ∩ {|η| ≤ M}`;
* `lintegral_box_perExt_le`: local `L^r` bounds of periodic extensions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.Sob

variable {c : ℝ}

/-! ### Index sets -/

theorem int_mem_Icc_of_abs_mul_le (hc : 0 < c) {m : ℤ} {B : ℝ} (h : |(m : ℝ) * c| ≤ B) :
    m ∈ Finset.Icc (-⌈B / c⌉) ⌈B / c⌉ := by
  rw [abs_mul, abs_of_pos hc, ← le_div_iff₀ hc] at h
  have h1 : (m : ℝ) ≤ B / c := (le_abs_self _).trans h
  have h2 : -(m : ℝ) ≤ B / c := (neg_le_abs _).trans h
  have h3 : m ≤ ⌈B / c⌉ := by
    have := (h1.trans (Int.le_ceil _))
    exact_mod_cast this
  have h4 : -m ≤ ⌈B / c⌉ := by
    have := (h2.trans (Int.le_ceil _))
    exact_mod_cast this
  rw [Finset.mem_Icc]
  constructor <;> omega

/-! ### Periodic extension -/

section PerExt

variable {F : Type*} [NormedAddCommGroup F]

/-- The `c`-periodic extension of a field given on the cell `[-c/2, c/2) × ℝ`. -/
def perExt (hc : 0 < c) (f : ℝ × ℝ → F) (z : ℝ × ℝ) : F :=
  f (toIcoMod hc (-(c / 2)) z.1, z.2)

theorem perExt_of_mem (hc : 0 < c) (f : ℝ × ℝ → F) {z : ℝ × ℝ} (hz : z ∈ cylCell c) :
    perExt hc f z = f z := by
  have h1 : z.1 ∈ Ico (-(c / 2)) (-(c / 2) + c) := by
    rw [show -(c / 2) + c = c / 2 by ring]; exact hz.1
  simp only [perExt, (toIcoMod_eq_self hc).mpr h1]

theorem perExt_add_int (hc : 0 < c) (f : ℝ × ℝ → F) (m : ℤ) (z : ℝ × ℝ) :
    perExt hc f (z + ((m : ℝ) * c, 0)) = perExt hc f z := by
  simp only [perExt, Prod.fst_add, Prod.snd_add, add_zero]
  rw [← zsmul_eq_mul, toIcoMod_add_zsmul]

theorem perExt_add (hc : 0 < c) (f : ℝ × ℝ → F) (z : ℝ × ℝ) :
    perExt hc f (z + (c, 0)) = perExt hc f z := by
  have := perExt_add_int hc f 1 z
  simpa using this

theorem perExt_add_int_of_mem (hc : 0 < c) (f : ℝ × ℝ → F) (m : ℤ) {z : ℝ × ℝ}
    (hz : z ∈ cylCell c) : perExt hc f (z + ((m : ℝ) * c, 0)) = f z := by
  rw [perExt_add_int, perExt_of_mem hc f hz]

theorem measurable_toIcoMod (hc : 0 < c) (a : ℝ) : Measurable (toIcoMod hc a) := by
  have : toIcoMod hc a = fun b => b - ((⌊(b - a) / c⌋ : ℤ) : ℝ) * c := by
    funext b; rw [toIcoMod, toIcoDiv_eq_floor, zsmul_eq_mul]
  rw [this]
  exact measurable_id.sub (((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (Measurable.floor ((measurable_id.sub_const a).div_const c))).mul_const c)

theorem stronglyMeasurable_perExt (hc : 0 < c) {f : ℝ × ℝ → F} (hf : StronglyMeasurable f) :
    StronglyMeasurable (perExt hc f) :=
  hf.comp_measurable ((measurable_toIcoMod hc _).comp measurable_fst |>.prodMk measurable_snd)

end PerExt

/-! ### Periodization of tests -/

section PerSum

theorem mem_idx_of_ne_zero (hc : 0 < c) {χ : ℝ × ℝ → ℝ} {A : ℝ}
    (hA : ∀ z, χ z ≠ 0 → |z.1| ≤ A) {B : ℝ} {z : ℝ × ℝ} (hz : |z.1| ≤ B) {m : ℤ}
    (hne : χ (z + ((m : ℝ) * c, 0)) ≠ 0) :
    m ∈ Finset.Icc (-⌈(A + B) / c⌉) ⌈(A + B) / c⌉ := by
  have h1 := hA _ hne
  simp only [Prod.fst_add] at h1
  apply int_mem_Icc_of_abs_mul_le hc
  have h2 := abs_le.mp h1
  have h3 := abs_le.mp hz
  rw [abs_le]
  constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]

/-- The periodization `∑ᶠ m, χ(z + (mc, 0))` of a test. -/
def perSum (c : ℝ) (χ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := ∑ᶠ m : ℤ, χ (z + ((m : ℝ) * c, 0))

/-- Locally, `perSum` is a finite sum. -/
theorem perSum_eq_sum (hc : 0 < c) {χ : ℝ × ℝ → ℝ} {A : ℝ} (hA : ∀ z, χ z ≠ 0 → |z.1| ≤ A)
    {B : ℝ} {z : ℝ × ℝ} (hz : |z.1| ≤ B) :
    perSum c χ z = ∑ m ∈ Finset.Icc (-⌈(A + B) / c⌉) ⌈(A + B) / c⌉,
      χ (z + ((m : ℝ) * c, 0)) := by
  apply finsum_eq_sum_of_support_subset
  intro m hm
  exact Finset.mem_coe.mpr (mem_idx_of_ne_zero hc hA hz hm)

theorem contDiff_perSum (hc : 0 < c) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {A : ℝ}
    (hA : ∀ z, χ z ≠ 0 → |z.1| ≤ A) : ContDiff ℝ ∞ (perSum c χ) := by
  refine contDiff_iff_contDiffAt.2 fun z₀ => ?_
  have hopen : IsOpen {z : ℝ × ℝ | |z.1| < |z₀.1| + 1} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hev : perSum c χ =ᶠ[𝓝 z₀] fun z =>
      ∑ m ∈ Finset.Icc (-⌈(A + (|z₀.1| + 1)) / c⌉) ⌈(A + (|z₀.1| + 1)) / c⌉,
        χ (z + ((m : ℝ) * c, 0)) := by
    filter_upwards [hopen.mem_nhds (by simp)] with z hz
    exact perSum_eq_sum hc hA (le_of_lt hz)
  have hs : ContDiff ℝ ∞ (fun z =>
      ∑ m ∈ Finset.Icc (-⌈(A + (|z₀.1| + 1)) / c⌉) ⌈(A + (|z₀.1| + 1)) / c⌉,
        χ (z + ((m : ℝ) * c, 0))) :=
    ContDiff.sum fun m _ => hχ.comp (contDiff_id.add contDiff_const)
  exact hs.contDiffAt.congr_of_eventuallyEq hev

theorem perSum_add (χ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : perSum c χ (z + (c, 0)) = perSum c χ z := by
  have := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun m : ℤ => χ (z + ((m : ℝ) * c, 0)))
  simp only [Equiv.coe_addRight] at this
  unfold perSum
  rw [← this]
  refine finsum_congr fun m => ?_
  congr 1
  ext <;> simp <;> ring

theorem perSum_eq_zero {χ : ℝ × ℝ → ℝ} {M : ℝ} (hM : ∀ z : ℝ × ℝ, M < |z.2| → χ z = 0)
    {z : ℝ × ℝ} (hz : M < |z.2|) : perSum c χ z = 0 := by
  unfold perSum
  exact finsum_eq_zero_of_forall_eq_zero fun m => hM _ (by simpa using hz)

theorem tsupport_iterDirDeriv_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℝ) (vs : List E) : tsupport (iterDirDeriv vs χ) ⊆ tsupport χ := by
  induction vs with
  | nil => exact subset_rfl
  | cons v vs ih => exact (tsupport_fderiv_apply_subset ℝ v).trans ih

theorem fderiv_perSum (hc : 0 < c) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {A : ℝ}
    (hA : ∀ z ∈ tsupport χ, |z.1| ≤ A) (z₀ v : ℝ × ℝ) :
    fderiv ℝ (perSum c χ) z₀ v = perSum c (fun y => fderiv ℝ χ y v) z₀ := by
  have hA' : ∀ z, χ z ≠ 0 → |z.1| ≤ A := fun z hz => hA z (subset_tsupport _ hz)
  have hdA : ∀ z, fderiv ℝ χ z v ≠ 0 → |z.1| ≤ A := fun z hz =>
    hA z (tsupport_fderiv_apply_subset ℝ v (subset_tsupport _ hz))
  have hopen : IsOpen {z : ℝ × ℝ | |z.1| < |z₀.1| + 1} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  set S := Finset.Icc (-⌈(A + (|z₀.1| + 1)) / c⌉) ⌈(A + (|z₀.1| + 1)) / c⌉ with hS
  have hev : perSum c χ =ᶠ[𝓝 z₀] fun z => ∑ m ∈ S, χ (z + ((m : ℝ) * c, 0)) := by
    filter_upwards [hopen.mem_nhds (by simp)] with z hz
    exact perSum_eq_sum hc hA' (le_of_lt hz)
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  rw [hev.fderiv_eq, perSum_eq_sum hc hdA (le_of_lt (lt_add_one |z₀.1|)),
    fderiv_fun_sum (fun (m : ℤ) _ => (show DifferentiableAt ℝ (fun z => χ (z + ((m : ℝ) * c, 0))) z₀
      from (hd _).comp z₀ (differentiableAt_id.add_const _)))]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fderiv_comp_add_right]

theorem iterDirDeriv_perSum (hc : 0 < c) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {A : ℝ}
    (hA : ∀ z ∈ tsupport χ, |z.1| ≤ A) (vs : List (ℝ × ℝ)) :
    iterDirDeriv vs (perSum c χ) = perSum c (iterDirDeriv vs χ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext z
    simp only [iterDirDeriv_cons]
    rw [ih, fderiv_perSum hc (contDiff_iterDirDeriv hχ vs)
      (fun y hy => hA y (tsupport_iterDirDeriv_subset χ vs hy)) z v]

/-- Bounds for a compactly supported function on `ℝ × ℝ`. -/
theorem exists_bound_of_hasCompactSupport {χ : ℝ × ℝ → ℝ} (hχc : HasCompactSupport χ) :
    ∃ R : ℝ, (∀ z ∈ tsupport χ, |z.1| ≤ R) ∧ ∀ z : ℝ × ℝ, R < |z.2| → χ z = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp
    hχc.isCompact.isBounded
  have hn : ∀ z ∈ tsupport χ, |z.1| ≤ R ∧ |z.2| ≤ R := by
    intro z hz
    have := hR hz
    rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
    exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩
  refine ⟨R, fun z hz => (hn z hz).1, fun z hz => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hzs
  linarith [(hn z hzs).2]

/-- **The periodization of a `C_c^∞` test is a cylinder test.** -/
theorem isCylTest_perSum (hc : 0 < c) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : IsCylTest c (perSum c ψ) := by
  obtain ⟨R, hA, hM⟩ := exists_bound_of_hasCompactSupport hψc
  exact ⟨contDiff_perSum hc hψ (fun z hz => hA z (subset_tsupport _ hz)), perSum_add ψ,
    ⟨R, fun z hz => perSum_eq_zero hM hz⟩⟩

end PerSum

/-! ### Unfolding integrals over `ℝ²` to the cell -/

section Unfold

/-- `ℤ ≃ cℤ × {0}`. -/
def zEquiv (hc : 0 < c) : ℤ ≃ AddSubgroup.zmultiples ((c, 0) : ℝ × ℝ) :=
  Equiv.ofBijective (fun m => ⟨m • ((c, 0) : ℝ × ℝ), m, rfl⟩) ⟨fun m n h => by
    have h0 := congrArg Subtype.val h
    change m • ((c, 0) : ℝ × ℝ) = n • ((c, 0) : ℝ × ℝ) at h0
    have h1 := congrArg Prod.fst h0
    rw [Prod.smul_fst, Prod.smul_fst, zsmul_eq_mul, zsmul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ hc.ne' h1, fun g => by
    obtain ⟨v, m, hm⟩ := g
    exact ⟨m, Subtype.ext hm⟩⟩

theorem coe_zEquiv (hc : 0 < c) (m : ℤ) : ((zEquiv hc m : ℝ × ℝ)) = m • ((c, 0) : ℝ × ℝ) := rfl

theorem isAddFundamentalDomain_cylCell (hc : 0 < c) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples ((c, 0) : ℝ × ℝ)) (cylCell c) volume := by
  have := Cyl.isAddFundamentalDomain_cell hc
  rwa [cyl_cell_eq] at this

theorem neg_zEquiv_vadd (hc : 0 < c) (m : ℤ) (z : ℝ × ℝ) :
    -(zEquiv hc ((Equiv.neg ℤ) m)) +ᵥ z = z + ((m : ℝ) * c, 0) := by
  rw [AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg, coe_zEquiv]
  ext <;> simp [zsmul_eq_mul] <;> ring

/-- **Unfolding** (lower integral): `∫⁻_{ℝ²} h = ∑'_m ∫⁻_{cell} h(· + (mc, 0))`. -/
theorem lintegral_unfold (hc : 0 < c) (h : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ z, h z = ∑' m : ℤ, ∫⁻ z in cylCell c, h (z + ((m : ℝ) * c, 0)) := by
  rw [(isAddFundamentalDomain_cylCell hc).lintegral_eq_tsum', ← (zEquiv hc).tsum_eq,
    ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  simp_rw [neg_zEquiv_vadd]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Unfolding** (Bochner integral). -/
theorem integral_unfold [CompleteSpace F] (hc : 0 < c) {h : ℝ × ℝ → F} (hh : Integrable h) :
    ∫ z, h z = ∑' m : ℤ, ∫ z in cylCell c, h (z + ((m : ℝ) * c, 0)) := by
  rw [(isAddFundamentalDomain_cylCell hc).integral_eq_tsum' h hh, ← (zEquiv hc).tsum_eq,
    ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  simp_rw [neg_zEquiv_vadd]

theorem measurableSet_absSnd_le (M : ℝ) : MeasurableSet {z : ℝ × ℝ | |z.2| ≤ M} :=
  measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const

/-- **`∫_{ℝ²} χ • perExt f = ∫_{cell} perSum χ • f`** for a compactly supported continuous `χ`
and `f` integrable on every `cell ∩ {|η| ≤ M}`. -/
theorem integral_smul_perExt [CompleteSpace F] (hc : 0 < c) {χ : ℝ × ℝ → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) {f : ℝ × ℝ → F} (hfm : StronglyMeasurable f)
    (hf : ∀ M, IntegrableOn f (cylCell c ∩ {z | |z.2| ≤ M})) :
    Integrable (fun z => χ z • perExt hc f z) ∧
      ∫ z, χ z • perExt hc f z = ∫ z in cylCell c, perSum c χ z • f z := by
  obtain ⟨R, hA, hM⟩ := exists_bound_of_hasCompactSupport hχc
  have hA' : ∀ z, χ z ≠ 0 → |z.1| ≤ R := fun z hz => hA z (subset_tsupport _ hz)
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  set S := Finset.Icc (-⌈(R + c / 2) / c⌉) ⌈(R + c / 2) / c⌉ with hS
  have hcell : ∀ z ∈ cylCell c, |z.1| ≤ c / 2 := fun z hz =>
    abs_le.mpr ⟨hz.1.1, hz.1.2.le⟩
  have hzS : ∀ z ∈ cylCell c, ∀ m ∉ S, χ (z + ((m : ℝ) * c, 0)) = 0 := by
    intro z hz m hm
    by_contra hne
    exact hm (mem_idx_of_ne_zero hc hA' (hcell z hz) hne)
  -- each translate is integrable on the cell
  have hm_int : ∀ m : ℤ, IntegrableOn (fun z => χ (z + ((m : ℝ) * c, 0)) • f z) (cylCell c) := by
    intro m
    have hB := measurableSet_absSnd_le R
    have h1 : IntegrableOn (fun z => χ (z + ((m : ℝ) * c, 0)) • f z)
        (cylCell c ∩ {z | |z.2| ≤ R}) := by
      refine (hf R).smul_of_top_right (memLp_top_of_bound
        (hχ.comp (continuous_id.add continuous_const)).aestronglyMeasurable C
        (Eventually.of_forall fun z => hC _))
    refine h1.of_forall_sdiff_eq_zero (measurableSet_cylCell c) fun z hz => ?_
    have h2 : R < |z.2| := by
      by_contra hle
      push_neg at hle
      exact hz.2 ⟨hz.1, hle⟩
    rw [hM _ (by simpa using h2), zero_smul]
  have hG : ∀ m : ℤ, ∀ z ∈ cylCell c, χ (z + ((m : ℝ) * c, 0)) • perExt hc f (z + ((m : ℝ) * c, 0)) =
      χ (z + ((m : ℝ) * c, 0)) • f z := fun m z hz => by
    rw [perExt_add_int_of_mem hc f m hz]
  have hmeas : AEStronglyMeasurable (fun z => χ z • perExt hc f z) volume :=
    hχ.aestronglyMeasurable.smul (stronglyMeasurable_perExt hc hfm).aestronglyMeasurable
  have hint : Integrable (fun z => χ z • perExt hc f z) := by
    refine ⟨hmeas, ?_⟩
    show ∫⁻ z, ‖χ z • perExt hc f z‖ₑ < ⊤
    rw [lintegral_unfold hc, tsum_eq_sum (s := S) fun m hm => ?_]
    · refine ENNReal.sum_lt_top.mpr fun m _ => ?_
      rw [setLIntegral_congr_fun (measurableSet_cylCell c) fun z hz => by rw [hG m z hz]]
      exact (hm_int m).2
    · rw [setLIntegral_congr_fun (measurableSet_cylCell c) (g := fun _ => (0 : ℝ≥0∞))
        fun z hz => by rw [hG m z hz, hzS z hz m hm, zero_smul, enorm_zero], lintegral_zero]
  refine ⟨hint, ?_⟩
  rw [integral_unfold hc hint, tsum_eq_sum (s := S) fun m hm => ?_]
  · rw [← integral_finsetSum S fun m _ => ?_]
    · refine setIntegral_congr_fun (measurableSet_cylCell c) fun z hz => ?_
      rw [perSum_eq_sum hc hA' (hcell z hz), Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hG m z hz]
    · exact (hm_int m).congr_fun (fun z hz => (hG m z hz).symm) (measurableSet_cylCell c)
  · rw [setIntegral_congr_fun (measurableSet_cylCell c) (g := fun _ => (0 : F))
      fun z hz => by rw [hG m z hz, hzS z hz m hm, zero_smul], integral_zero]

/-- **`ℝ²` weak derivatives of periodic extensions** (S14 direction cylinder ⇒ `ℝ²`): a periodic
weak derivative identity on the cylinder gives the weak derivative identity of the periodic
extensions with `C_c^∞(ℝ²)` tests. -/
theorem hasWeakDeriv_perExt [CompleteSpace F] (hc : 0 < c) {vs : List (ℝ × ℝ)}
    {f g : ℝ × ℝ → F} (hfm : StronglyMeasurable f) (hgm : StronglyMeasurable g)
    (hf : ∀ M, IntegrableOn f (cylCell c ∩ {z | |z.2| ≤ M}))
    (hg : ∀ M, IntegrableOn g (cylCell c ∩ {z | |z.2| ≤ M}))
    (h : HasWeakDeriv (cylinder c) vs f g) :
    HasWeakDeriv (wholeSpaceOf (ℝ × ℝ) volume cylDir) vs (perExt hc f) (perExt hc g) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hψ' := (wholeSpaceOf (ℝ × ℝ) volume cylDir).adm_iterDirDeriv hψ vs
    exact (integral_smul_perExt hc hψ'.1.continuous hψ'.2 hfm hf).1
  · exact (integral_smul_perExt hc hψ.1.continuous hψ.2 hgm hg).1
  · have hψ' := (wholeSpaceOf (ℝ × ℝ) volume cylDir).adm_iterDirDeriv hψ vs
    obtain ⟨R, hA, -⟩ := exists_bound_of_hasCompactSupport hψ.2
    simp only [wholeSpaceOf_μ]
    rw [(integral_smul_perExt hc hψ'.1.continuous hψ'.2 hfm hf).2,
      (integral_smul_perExt hc hψ.1.continuous hψ.2 hgm hg).2,
      ← iterDirDeriv_perSum hc hψ.1 hA vs]
    have := h.identity _ (isCylTest_perSum hc hψ.1 hψ.2)
    simpa only [cylinder_μ] using this

/-- The fields of a periodic weak derivative are integrable on every `cell ∩ {|η| ≤ M}`. -/
theorem integrableOn_of_hasWeakDeriv_cylinder {vs : List (ℝ × ℝ)} {f g : ℝ × ℝ → F}
    (h : HasWeakDeriv (cylinder c) vs f g) (M : ℝ) :
    IntegrableOn g (cylCell c ∩ {z | |z.2| ≤ M}) := by
  let b : ContDiffBump (0 : ℝ) := ⟨|M| + 1, |M| + 2, by positivity, by linarith⟩
  have hφ : IsCylTest c (fun z : ℝ × ℝ => b z.2) := by
    refine ⟨b.contDiff.comp contDiff_snd, fun z => by simp, ⟨|M| + 2, fun z hz => ?_⟩⟩
    exact b.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hz.le)
  have hi : IntegrableOn (fun z : ℝ × ℝ => b z.2 • g z) (cylCell c) := h.int_right _ hφ
  refine (hi.mono_set inter_subset_left).congr_fun (fun z hz => ?_)
    ((measurableSet_cylCell c).inter (measurableSet_absSnd_le M))
  have h1 : b z.2 = 1 := b.one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    have : |z.2| ≤ M := hz.2
    show |z.2| ≤ |M| + 1
    linarith [le_abs_self M])
  simp only [h1, one_smul]

/-- **Local `L^r` bound for periodic extensions**: on a box `[-A, A] × [-M, M]` the
`r`-th power integral of `perExt f` is at most a fixed number of cell integrals. -/
theorem lintegral_box_perExt_le (hc : 0 < c) (f : ℝ × ℝ → F) (r A M : ℝ) :
    ∫⁻ z in Icc (-A) A ×ˢ Icc (-M) M, ‖perExt hc f z‖ₑ ^ r ≤
      ((Finset.Icc (-⌈(A + c / 2) / c⌉) ⌈(A + c / 2) / c⌉).card : ℝ≥0∞) *
        ∫⁻ z in cylCell c ∩ {z | |z.2| ≤ M}, ‖f z‖ₑ ^ r := by
  set S := Finset.Icc (-⌈(A + c / 2) / c⌉) ⌈(A + c / 2) / c⌉ with hS
  set box : Set (ℝ × ℝ) := Icc (-A) A ×ˢ Icc (-M) M with hbox
  have hboxm : MeasurableSet box := measurableSet_Icc.prod measurableSet_Icc
  have hB := measurableSet_absSnd_le M
  have hcell : ∀ z ∈ cylCell c, |z.1| ≤ c / 2 := fun z hz => abs_le.mpr ⟨hz.1.1, hz.1.2.le⟩
  have hterm : ∀ m : ℤ, ∀ z ∈ cylCell c,
      box.indicator (fun y => ‖perExt hc f y‖ₑ ^ r) (z + ((m : ℝ) * c, 0)) ≤
        {y : ℝ × ℝ | |y.2| ≤ M}.indicator (fun y => ‖f y‖ₑ ^ r) z := by
    intro m z hz
    by_cases hzb : z + ((m : ℝ) * c, 0) ∈ box
    · rw [indicator_of_mem hzb, perExt_add_int_of_mem hc f m hz]
      have : |z.2| ≤ M := by
        have := hzb.2
        simp only [Prod.snd_add, add_zero, mem_Icc] at this
        exact abs_le.mpr this
      rw [indicator_of_mem (show z ∈ {y : ℝ × ℝ | |y.2| ≤ M} from this)]
    · rw [indicator_of_notMem hzb]
      exact zero_le
  have hzero : ∀ m ∉ S, ∀ z ∈ cylCell c,
      box.indicator (fun y => ‖perExt hc f y‖ₑ ^ r) (z + ((m : ℝ) * c, 0)) = 0 := by
    intro m hm z hz
    by_contra hne
    apply hm
    have hzb : z + ((m : ℝ) * c, 0) ∈ box := by
      by_contra h'
      exact hne (indicator_of_notMem h' _)
    have h1 : |z.1 + (m : ℝ) * c| ≤ A := by
      have := hzb.1
      simp only [Prod.fst_add, mem_Icc] at this
      exact abs_le.mpr this
    apply int_mem_Icc_of_abs_mul_le hc
    have h2 := abs_le.mp h1
    have h3 := abs_le.mp (hcell z hz)
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  calc ∫⁻ z in box, ‖perExt hc f z‖ₑ ^ r
      = ∫⁻ z, box.indicator (fun y => ‖perExt hc f y‖ₑ ^ r) z := (lintegral_indicator hboxm _).symm
    _ = ∑ m ∈ S, ∫⁻ z in cylCell c,
          box.indicator (fun y => ‖perExt hc f y‖ₑ ^ r) (z + ((m : ℝ) * c, 0)) := by
        rw [lintegral_unfold hc, tsum_eq_sum (s := S) fun m hm => ?_]
        rw [setLIntegral_congr_fun (measurableSet_cylCell c) (g := fun _ => (0 : ℝ≥0∞))
          fun z hz => hzero m hm z hz, lintegral_zero]
    _ ≤ ∑ m ∈ S, ∫⁻ z in cylCell c, {y : ℝ × ℝ | |y.2| ≤ M}.indicator (fun y => ‖f y‖ₑ ^ r) z :=
        Finset.sum_le_sum fun m _ => setLIntegral_mono' (measurableSet_cylCell c) (hterm m)
    _ = (S.card : ℝ≥0∞) * ∫⁻ z in cylCell c ∩ {z | |z.2| ≤ M}, ‖f z‖ₑ ^ r := by
        rw [Finset.sum_const, nsmul_eq_mul, lintegral_indicator hB, Measure.restrict_restrict hB,
          inter_comm]

end Unfold

end UnforcedLeray.Sob
