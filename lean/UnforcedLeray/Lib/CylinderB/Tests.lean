import UnforcedLeray.Lib.CylinderB.Space
import UnforcedLeray.Lib.CylinderB.Liouville1D
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Cylinder test functions: weak derivatives, mode tests and the embedding into `H^k`

Helpers for targets CY12 and CY13 of

The tests are those of `Sob.cylinder c` (`Sob.IsCylTest c`: smooth, `c`-periodic in `q`,
vanishing for large `|η|`; the periodic tests of `paper/main.tex` lines 4573–4577 and
13850–13852, blueprint units B0271, B0656).

## Main declarations
* `IsCylTest.isPeriodic`, `IsCylTest.sub`, `IsCylTest.smul`, `IsCylTest.integrableOn_mul`;
* `fderiv_apply_eq_partial`: `Dφ(z) v = v₁ ∂_q φ(z) + v₂ ∂_η φ(z)`;
* `hasWeakDeriv_test`: a test `φ` has the weak derivatives `∂_{vs} φ` (periodic integration
  by parts, `Lib/Cylinder/IBP`);
* `CompactlyBounded.memLp`, `testH`: a test as an element of `H^k` for every weight;
* `cosTest k ψ`, `sinTest k ψ` (`cos(kq) ψ(η)`, `sin(kq) ψ(η)` with `k = 2πn/c`), their
  first derivatives, and the operator `Lop φ = φ − ∂_q²φ − ∂_η²φ` on them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Cyl

variable {c : ℝ} {φ ψ : Plane → ℝ}

theorem _root_.UnforcedLeray.Sob.IsCylTest.isPeriodic (h : Sob.IsCylTest c φ) : IsPeriodic c φ := fun z => by
  have e : ((z.1 + c, z.2) : Plane) = z + (c, 0) := by ext <;> simp
  rw [e]; exact h.periodic z

theorem _root_.UnforcedLeray.Sob.IsCylTest.vanishes (h : Sob.IsCylTest c φ) : ∃ R : ℝ, VanishesOutside R φ :=
  h.bounded

theorem _root_.UnforcedLeray.Sob.IsCylTest.sub (h : Sob.IsCylTest c φ) (h' : Sob.IsCylTest c ψ) :
    Sob.IsCylTest c (fun z => φ z - ψ z) := by
  obtain ⟨R, hR⟩ := h.bounded
  obtain ⟨R', hR'⟩ := h'.bounded
  refine ⟨h.smooth.sub h'.smooth, fun x => by simp only [h.periodic x, h'.periodic x], ⟨max R R',
    fun x hx => ?_⟩⟩
  rw [hR x (lt_of_le_of_lt (le_max_left _ _) hx), hR' x (lt_of_le_of_lt (le_max_right _ _) hx),
    sub_zero]

theorem _root_.UnforcedLeray.Sob.IsCylTest.smul (h : Sob.IsCylTest c φ) (a : ℝ) : Sob.IsCylTest c (fun z => a * φ z) := by
  obtain ⟨R, hR⟩ := h.bounded
  exact ⟨contDiff_const.mul h.smooth, fun x => by simp only [h.periodic x],
    ⟨R, fun x hx => by rw [hR x hx, mul_zero]⟩⟩

theorem _root_.UnforcedLeray.Sob.IsCylTest.continuous (h : Sob.IsCylTest c φ) : Continuous φ := h.smooth.continuous

theorem _root_.UnforcedLeray.Sob.IsCylTest.differentiable (h : Sob.IsCylTest c φ) : Differentiable ℝ φ :=
  h.smooth.differentiable (by simp)

/-- A test times a continuous function is integrable on the cell. -/
theorem _root_.UnforcedLeray.Sob.IsCylTest.integrableOn_mul (h : Sob.IsCylTest c φ) {g : Plane → ℝ} (hg : Continuous g) :
    IntegrableOn (fun z => φ z * g z) (cell c) := by
  obtain ⟨R, hR⟩ := h.vanishes
  exact (hR.mul_right g).integrableOn_cell (h.continuous.mul hg) c

/-! ### Directional derivatives through `∂_q`, `∂_η` -/

theorem fderiv_apply_eq_partial {f : Plane → ℝ} (hf : Differentiable ℝ f) (z v : Plane) :
    fderiv ℝ f z v = v.1 * partialQ f z + v.2 * partialEta f z := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, partialQ_eq_fderiv hf, partialEta_eq_fderiv hf, smul_eq_mul,
    smul_eq_mul]

theorem isCylTest_partialQ (h : Sob.IsCylTest c φ) : Sob.IsCylTest c (Cyl.partialQ φ) := by
  have e : Cyl.partialQ φ = fun x => fderiv ℝ φ x ((1 : ℝ), (0 : ℝ)) :=
    funext fun z => partialQ_eq_fderiv h.differentiable z
  rw [e]; exact h.dirDeriv _

theorem isCylTest_partialEta (h : Sob.IsCylTest c φ) : Sob.IsCylTest c (Cyl.partialEta φ) := by
  have e : Cyl.partialEta φ = fun x => fderiv ℝ φ x ((0 : ℝ), (1 : ℝ)) :=
    funext fun z => partialEta_eq_fderiv h.differentiable z
  rw [e]; exact h.dirDeriv _

/-! ### Weak derivatives of tests -/

/-- Periodic integration by parts for two tests in a direction `v`. -/
theorem integral_fderiv_mul_test (hc : 0 < c) (hψ : Sob.IsCylTest c ψ) (hφ : Sob.IsCylTest c φ)
    (v : Plane) :
    ∫ z in cell c, fderiv ℝ ψ z v * φ z = -∫ z in cell c, ψ z * fderiv ℝ φ z v := by
  have hQ := integral_cell_partialQ_mul hc hψ.differentiable hφ.differentiable hψ.isPeriodic
    hφ.isPeriodic ((isCylTest_partialQ hψ).integrableOn_mul hφ.continuous)
    (hψ.integrableOn_mul (isCylTest_partialQ hφ).continuous)
  have hE := integral_cell_partialEta_mul (c := c) hψ.differentiable hφ.differentiable
    (hψ.integrableOn_mul hφ.continuous) ((isCylTest_partialEta hψ).integrableOn_mul hφ.continuous)
    (hψ.integrableOn_mul (isCylTest_partialEta hφ).continuous)
  have e1 : (fun z => fderiv ℝ ψ z v * φ z) = fun z =>
      v.1 * (Cyl.partialQ ψ z * φ z) + v.2 * (Cyl.partialEta ψ z * φ z) := by
    funext z; rw [fderiv_apply_eq_partial hψ.differentiable]; ring
  have e2 : (fun z => ψ z * fderiv ℝ φ z v) = fun z =>
      v.1 * (ψ z * Cyl.partialQ φ z) + v.2 * (ψ z * Cyl.partialEta φ z) := by
    funext z; rw [fderiv_apply_eq_partial hφ.differentiable]; ring
  rw [e1, e2, integral_add (((isCylTest_partialQ hψ).integrableOn_mul hφ.continuous).const_mul _)
    (((isCylTest_partialEta hψ).integrableOn_mul hφ.continuous).const_mul _),
    integral_add ((hψ.integrableOn_mul (isCylTest_partialQ hφ).continuous).const_mul _)
    ((hψ.integrableOn_mul (isCylTest_partialEta hφ).continuous).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hQ, hE]
  ring

theorem cylinder_integral (c : ℝ) (f : Plane → ℝ) :
    ∫ x, f x ∂(Sob.cylinder c).μ = ∫ z in cell c, f z := by
  rw [cylinder_μ_eq]; rfl

theorem cylinder_integrable {c : ℝ} {f : Plane → ℝ} :
    Integrable f (Sob.cylinder c).μ ↔ IntegrableOn f (cell c) := by
  rw [cylinder_μ_eq]; rfl

/-- **A test has its classical derivative as periodic weak derivative.** -/
theorem hasWeakDeriv_test_single (hc : 0 < c) (hφ : Sob.IsCylTest c φ) (v : Plane) :
    Sob.HasWeakDeriv (Sob.cylinder c) [v] φ (fun x => fderiv ℝ φ x v) := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · rw [cylinder_integrable]
    simp only [Sob.iterDirDeriv_singleton, smul_eq_mul]
    exact (hψ.dirDeriv v).integrableOn_mul hφ.continuous
  · rw [cylinder_integrable]
    simp only [smul_eq_mul]
    exact hψ.integrableOn_mul (hφ.dirDeriv v).continuous
  · simp only [Sob.iterDirDeriv_singleton, smul_eq_mul, cylinder_integral, List.length_singleton,
      pow_one, neg_one_mul]
    exact integral_fderiv_mul_test hc hψ hφ v

/-- **Weak derivatives of a test along any word.** -/
theorem hasWeakDeriv_test (hc : 0 < c) (hφ : Sob.IsCylTest c φ) :
    ∀ vs : List Plane, Sob.HasWeakDeriv (Sob.cylinder c) vs φ (Sob.iterDirDeriv vs φ)
  | [] => Sob.HasWeakDeriv.nil fun ψ hψ => by
      rw [cylinder_integrable]
      simp only [smul_eq_mul]
      exact hψ.integrableOn_mul hφ.continuous
  | v :: vs => (hasWeakDeriv_test hc hφ vs).cons
      (hasWeakDeriv_test_single hc ((Sob.cylinder c).adm_iterDirDeriv hφ vs) v)

/-! ### Tests as elements of `H^k` -/

section Embed

variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {ρ : Sob.Weight E}

/-- A compactly bounded multiplier lies in every `L^q(ρ dμ)`. -/
theorem CompactlyBounded.memLp {f : E → ℝ} (hf : Sob.CompactlyBounded μ f) (q : ℝ≥0∞) :
    MemLp f q (Sob.wμ μ ρ) := by
  obtain ⟨K, hK, ⟨M, hM⟩, hz⟩ := hf.bdd
  have hsm : AEStronglyMeasurable f (Sob.wμ μ ρ) := hf.aesm.mono_ac (Sob.wμ_ac μ ρ)
  have hind : f =ᵐ[Sob.wμ μ ρ] K.indicator f := by
    rw [Sob.ae_eq_wμ_iff]
    filter_upwards [hz] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK, hx hxK]
  refine MemLp.ae_eq hind.symm ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet]
  have : IsFiniteMeasure ((Sob.wμ μ ρ).restrict K) :=
    isFiniteMeasure_restrict.mpr (Sob.wμ_lt_top hK).ne
  refine MemLp.of_bound hsm.restrict M ?_
  exact ae_restrict_of_forall_mem hK.measurableSet fun x hx => by
    rw [Real.norm_eq_abs]; exact hM x hx

end Embed

/-- **A test as an element of `H^k`** for every weight `ρ`: the tuple `(∂^α φ)_{|α| ≤ k}`. -/
def testH (hc : 0 < c) (hφ : Sob.IsCylTest c φ) (ρ : Sob.Weight Plane) (k : ℕ) :
    Sob.W (Sob.cylinder c) ρ ℝ ℝ k 2 :=
  Sob.W.ofFields (fun α => Sob.iterDirDeriv ((Sob.cylinder c).word α) φ)
    (fun α => CompactlyBounded.memLp (Sob.CompactlyBounded.of_adm
      ((Sob.cylinder c).adm_iterDirDeriv hφ _)) 2)
    (fun α => by
      simp only [word_zero, Sob.iterDirDeriv_nil]
      exact hasWeakDeriv_test hc hφ _)

theorem coeFn_deriv_testH (hc : 0 < c) (hφ : Sob.IsCylTest c φ) (ρ : Sob.Weight Plane) (k : ℕ)
    (α : Sob.Idx 2 k) :
    (Sob.W.deriv (Sob.cylinder c) ρ ℝ ℝ k 2 α (testH hc hφ ρ k) : Plane → ℝ) =ᵐ[(Sob.cylinder c).μ]
      Sob.iterDirDeriv ((Sob.cylinder c).word α) φ := by
  rw [testH, Sob.W.deriv_ofFields]
  exact (Sob.ae_eq_wμ_iff _ ρ).mp (MemLp.coeFn_toLp _)

/-! ### Mode tests `cos(kq) ψ(η)`, `sin(kq) ψ(η)` -/

/-- The frequency `k_n = 2πn/c` of the `n`-th `q`-mode. -/
def freq (c : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / c

/-- `cos(kq) ψ(η)`. -/
def cosTest (k : ℝ) (ψ : ℝ → ℝ) (z : Plane) : ℝ := Real.cos (k * z.1) * ψ z.2

/-- `sin(kq) ψ(η)`. -/
def sinTest (k : ℝ) (ψ : ℝ → ℝ) (z : Plane) : ℝ := Real.sin (k * z.1) * ψ z.2

theorem freq_mul (hc : 0 < c) (n : ℤ) (q : ℝ) :
    freq c n * (q + c) = freq c n * q + (n : ℝ) * (2 * Real.pi) := by
  simp only [freq]; field_simp

theorem isCylTest_cosTest (hc : 0 < c) (n : ℤ) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    Sob.IsCylTest c (cosTest (freq c n) ψ) := by
  obtain ⟨M, -, hM⟩ := hψ.exists_bound
  refine ⟨?_, fun x => ?_, ⟨M, fun x hx => ?_⟩⟩
  · exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_fst)).mul
      (hψ.smooth.comp contDiff_snd)
  · simp only [cosTest, Prod.fst_add, Prod.snd_add, add_zero]
    rw [freq_mul hc, Real.cos_add_int_mul_two_pi]
  · simp only [cosTest]; rw [hM _ hx.le, mul_zero]

theorem isCylTest_sinTest (hc : 0 < c) (n : ℤ) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    Sob.IsCylTest c (sinTest (freq c n) ψ) := by
  obtain ⟨M, -, hM⟩ := hψ.exists_bound
  refine ⟨?_, fun x => ?_, ⟨M, fun x hx => ?_⟩⟩
  · exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)).mul
      (hψ.smooth.comp contDiff_snd)
  · simp only [sinTest, Prod.fst_add, Prod.snd_add, add_zero]
    rw [freq_mul hc, Real.sin_add_int_mul_two_pi]
  · simp only [sinTest]; rw [hM _ hx.le, mul_zero]

theorem differentiable_cosTest (k : ℝ) {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    Differentiable ℝ (cosTest k ψ) :=
  ((Real.differentiable_cos.comp ((differentiable_const k).mul differentiable_fst))).mul
    (hψ.comp differentiable_snd)

theorem differentiable_sinTest (k : ℝ) {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    Differentiable ℝ (sinTest k ψ) :=
  ((Real.differentiable_sin.comp ((differentiable_const k).mul differentiable_fst))).mul
    (hψ.comp differentiable_snd)

theorem hasDerivAt_cosTest_q (k : ℝ) (ψ : ℝ → ℝ) (z : Plane) :
    HasDerivAt (fun q : ℝ => cosTest k ψ (q, z.2)) (-k * sinTest k ψ z) z.1 := by
  have h : HasDerivAt (fun q : ℝ => Real.cos (k * q) * ψ z.2)
      (-Real.sin (k * z.1) * (k * 1) * ψ z.2) z.1 :=
    (((Real.hasDerivAt_cos _).comp z.1 ((hasDerivAt_id z.1).const_mul k))).mul_const _
  have e : -k * sinTest k ψ z = -Real.sin (k * z.1) * (k * 1) * ψ z.2 := by
    simp only [sinTest]; ring
  rw [e]; exact h

theorem hasDerivAt_sinTest_q (k : ℝ) (ψ : ℝ → ℝ) (z : Plane) :
    HasDerivAt (fun q : ℝ => sinTest k ψ (q, z.2)) (k * cosTest k ψ z) z.1 := by
  have h : HasDerivAt (fun q : ℝ => Real.sin (k * q) * ψ z.2)
      (Real.cos (k * z.1) * (k * 1) * ψ z.2) z.1 :=
    (((Real.hasDerivAt_sin _).comp z.1 ((hasDerivAt_id z.1).const_mul k))).mul_const _
  have e : k * cosTest k ψ z = Real.cos (k * z.1) * (k * 1) * ψ z.2 := by
    simp only [cosTest]; ring
  rw [e]; exact h

theorem partialQ_cosTest (k : ℝ) (ψ : ℝ → ℝ) :
    Cyl.partialQ (cosTest k ψ) = fun z => -k * sinTest k ψ z :=
  funext fun z => (hasDerivAt_cosTest_q k ψ z).deriv

theorem partialQ_sinTest (k : ℝ) (ψ : ℝ → ℝ) :
    Cyl.partialQ (sinTest k ψ) = fun z => k * cosTest k ψ z :=
  funext fun z => (hasDerivAt_sinTest_q k ψ z).deriv

theorem partialEta_cosTest (k : ℝ) {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    Cyl.partialEta (cosTest k ψ) = cosTest k (deriv ψ) := by
  funext z
  simp only [Cyl.partialEta, cosTest]
  rw [deriv_const_mul _ (hψ z.2)]

theorem partialEta_sinTest (k : ℝ) {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    Cyl.partialEta (sinTest k ψ) = sinTest k (deriv ψ) := by
  funext z
  simp only [Cyl.partialEta, sinTest]
  rw [deriv_const_mul _ (hψ z.2)]

/-- `∂_q`, `∂_η` as the directional derivatives along `(1,0)`, `(0,1)`. -/
theorem dir10_eq (hf : Differentiable ℝ φ) :
    (fun x => fderiv ℝ φ x ((1 : ℝ), (0 : ℝ))) = Cyl.partialQ φ :=
  funext fun z => (partialQ_eq_fderiv hf z).symm

theorem dir01_eq (hf : Differentiable ℝ φ) :
    (fun x => fderiv ℝ φ x ((0 : ℝ), (1 : ℝ))) = Cyl.partialEta φ :=
  funext fun z => (partialEta_eq_fderiv hf z).symm

/-- `Lop φ = φ − ∂_q²φ − ∂_η²φ`, the operator `1 − Δ` of the `H¹` Riesz map. -/
def Lop (φ : Plane → ℝ) (z : Plane) : ℝ :=
  φ z - Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ z -
    Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ z

theorem iterDirDeriv_two_eq (v : Plane) (φ : Plane → ℝ) :
    Sob.iterDirDeriv [v, v] φ = fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x v := rfl

theorem Lop_cosTest (k : ℝ) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    Lop (cosTest k ψ) = cosTest k (fun y => (1 + k ^ 2) * ψ y - deriv (deriv ψ) y) := by
  have hd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hd' : Differentiable ℝ (deriv ψ) := hψ.deriv.smooth.differentiable (by simp)
  have hq : Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] (cosTest k ψ) =
      fun z => -k ^ 2 * cosTest k ψ z := by
    rw [iterDirDeriv_two_eq, dir10_eq (differentiable_cosTest k hd), partialQ_cosTest]
    have hdiff : Differentiable ℝ fun z => -k * sinTest k ψ z :=
      (differentiable_sinTest k hd).const_mul _
    rw [dir10_eq hdiff]
    funext z
    simp only [Cyl.partialQ]
    rw [((hasDerivAt_sinTest_q k ψ z).const_mul (-k)).deriv]; ring
  have he : Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] (cosTest k ψ) =
      cosTest k (deriv (deriv ψ)) := by
    rw [iterDirDeriv_two_eq, dir01_eq (differentiable_cosTest k hd), partialEta_cosTest k hd,
      dir01_eq (differentiable_cosTest k hd'), partialEta_cosTest k hd']
  funext z
  simp only [Lop, hq, he, cosTest]
  ring

theorem Lop_sinTest (k : ℝ) {ψ : ℝ → ℝ} (hψ : OneD.Test ψ) :
    Lop (sinTest k ψ) = sinTest k (fun y => (1 + k ^ 2) * ψ y - deriv (deriv ψ) y) := by
  have hd : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hd' : Differentiable ℝ (deriv ψ) := hψ.deriv.smooth.differentiable (by simp)
  have hq : Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] (sinTest k ψ) =
      fun z => -k ^ 2 * sinTest k ψ z := by
    rw [iterDirDeriv_two_eq, dir10_eq (differentiable_sinTest k hd), partialQ_sinTest]
    have hdiff : Differentiable ℝ fun z => k * cosTest k ψ z :=
      (differentiable_cosTest k hd).const_mul _
    rw [dir10_eq hdiff]
    funext z
    simp only [Cyl.partialQ]
    rw [((hasDerivAt_cosTest_q k ψ z).const_mul k).deriv]; ring
  have he : Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] (sinTest k ψ) =
      sinTest k (deriv (deriv ψ)) := by
    rw [iterDirDeriv_two_eq, dir01_eq (differentiable_sinTest k hd), partialEta_sinTest k hd,
      dir01_eq (differentiable_sinTest k hd'), partialEta_sinTest k hd']
  funext z
  simp only [Lop, hq, he, sinTest]
  ring

theorem isCylTest_Lop (h : Sob.IsCylTest c φ) : Sob.IsCylTest c (Lop φ) :=
  (h.sub ((Sob.cylinder c).adm_iterDirDeriv h _)).sub ((Sob.cylinder c).adm_iterDirDeriv h _)

/-- `Lop` commutes with a directional derivative. -/
theorem Lop_dir (h : Sob.IsCylTest c φ) (v : Plane) :
    Lop (fun x => fderiv ℝ φ x v) = fun x => fderiv ℝ (Lop φ) x v := by
  have hs := h.smooth
  have h1 := (Sob.cylinder c).adm_iterDirDeriv h [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))]
  have h2 := (Sob.cylinder c).adm_iterDirDeriv h [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  have hp1 : Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] (fun x => fderiv ℝ φ x v) =
      fun x => fderiv ℝ (Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ) x v := by
    have e1 : (fun x => fderiv ℝ φ x v) = Sob.iterDirDeriv [v] φ := rfl
    rw [e1, ← Sob.iterDirDeriv_append]
    rw [Sob.iterDirDeriv_perm (List.perm_append_comm) hs]
    rfl
  have hp2 : Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] (fun x => fderiv ℝ φ x v) =
      fun x => fderiv ℝ (Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ) x v := by
    have e1 : (fun x => fderiv ℝ φ x v) = Sob.iterDirDeriv [v] φ := rfl
    rw [e1, ← Sob.iterDirDeriv_append]
    rw [Sob.iterDirDeriv_perm (List.perm_append_comm) hs]
    rfl
  funext x
  have hd0 : DifferentiableAt ℝ φ x := h.differentiable x
  have hd1 : DifferentiableAt ℝ (Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ) x :=
    (h1.differentiable) x
  have hd2 : DifferentiableAt ℝ (Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ) x :=
    (h2.differentiable) x
  have e : Lop φ = fun y => φ y - Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ y -
      Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ y := rfl
  rw [e, fderiv_fun_sub (hd0.fun_sub hd1) hd2, fderiv_fun_sub hd0 hd1]
  simp only [Lop, ContinuousLinearMap.sub_apply]
  rw [hp1, hp2]

end UnforcedLeray.Cyl
