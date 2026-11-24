import UnforcedLeray.Lib.Sobolev.TestDomain
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The cylinder test domain (INF11 target S0, cylinder instance)

Scoping note `INF11-INF14-Sobolev.md` §5.0 (`def cylinder … : TestDomain 2`: smooth tests,
`c`-periodic in coordinate `0`, compact in coordinate `1`, volume on one cell); decision D1 of
the scoping README §3 (carrier `ℝ × ℝ`, centred cell `Ico (-c/2) (c/2) ×ˢ univ`) and D3
(`Cyl.H c m k = W (cylinder c) (ρw c ^ m) ℂ F k 2`).

The manuscript: on `C_c = ℝ/cℤ × ℝ`, "Derivatives are periodic weak derivatives, never
derivatives of zero extensions" (tex 4573–4577, 13850–13852), with the unweighted pairing
on one cell (tex 13876–13886). Blueprint units: B0271 (tex 4569–4578), B0662, B0892, B0912.

The pairing measure is Lebesgue measure on the cell `[-c/2, c/2) × ℝ`; the tests are the
smooth functions on `ℝ × ℝ` that are `c`-periodic in `q` and vanish for `|η|` large. A weak
derivative for this test class is exactly the periodic weak derivative of the manuscript.

## Main declarations
* `cylCell c`, `cylDir`, `IsCylTest c φ`;
* `exists_isCylTest_eq`: the periodization of a test supported in the open cell is a cylinder
  test agreeing with it on the cell;
* `cylinder c : TestDomain (ℝ × ℝ) 2`, with the fundamental lemma `ae_zero` proved from
  Mathlib's open-set version through the periodization (for `c ≤ 0` the cell is empty).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

/-- The centred cell `[-c/2, c/2) × ℝ` (decision D1). -/
def cylCell (c : ℝ) : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ univ

theorem measurableSet_cylCell (c : ℝ) : MeasurableSet (cylCell c) :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- The coordinate directions `∂_q = (1, 0)` and `∂_η = (0, 1)`. -/
def cylDir : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- **Cylinder tests**: smooth, `c`-periodic in `q`, and zero for `|η|` large. -/
structure IsCylTest (c : ℝ) (φ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ x, φ (x + (c, 0)) = φ x
  bounded : ∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0

theorem IsCylTest.dirDeriv {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : IsCylTest c φ) (v : ℝ × ℝ) :
    IsCylTest c (fun x => fderiv ℝ φ x v) := by
  refine ⟨contDiff_dirDeriv hφ.smooth v, fun x => ?_, ?_⟩
  · show fderiv ℝ φ (x + (c, 0)) v = fderiv ℝ φ x v
    have e : (fun y => φ (y + (c, 0))) = φ := funext hφ.periodic
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) ((c, 0) : ℝ × ℝ)
    rw [e] at this
    rw [← this]
  · obtain ⟨R, hR⟩ := hφ.bounded
    refine ⟨R, fun x hx => ?_⟩
    have hopen : IsOpen {y : ℝ × ℝ | R < |y.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => hR y hy
    show fderiv ℝ φ x v = 0
    rw [hev.fderiv_eq]
    simp

/-! ### Periodization of a test supported in the open cell -/

section Periodize

variable {c : ℝ} (hc : 0 < c)

/-- `|m c| < c` forces `m = 0`. -/
theorem int_eq_zero_of_abs_mul_lt {m : ℤ} (h1 : -c < (m : ℝ) * c) (h2 : (m : ℝ) * c < c) :
    m = 0 := by
  have hc' : 0 < c := by linarith
  have a1 : (m : ℝ) < 1 := by
    by_contra h; push_neg at h
    have := mul_le_mul_of_nonneg_right h hc'.le
    linarith
  have a2 : (-1 : ℝ) < m := by
    by_contra h; push_neg at h
    have := mul_le_mul_of_nonneg_right h hc'.le
    linarith
  have b1 : m < 1 := by exact_mod_cast a1
  have b2 : -1 < m := by exact_mod_cast a2
  omega

include hc in
/-- **Periodization** (S0): a smooth test with compact support in the open cell
`(-c/2, c/2) × ℝ` agrees on the cell with a cylinder test. -/
theorem exists_isCylTest_eq {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ Ioo (-(c / 2)) (c / 2) ×ˢ univ) :
    ∃ Φ : ℝ × ℝ → ℝ, IsCylTest c Φ ∧ ∀ x ∈ cylCell c, Φ x = ψ x := by
  set a : ℝ := -(c / 2) with ha
  have hac : a + c = c / 2 := by rw [ha]; ring
  have hU : IsOpen (Ioo a (a + c) ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  obtain ⟨δ, hδ, hδU⟩ := hψc.isCompact.exists_thickening_subset_open hU
    (by rw [hac]; exact hψU)
  -- where `ψ ≠ 0`, the first coordinate is `δ`-inside the cell
  have hin : ∀ x : ℝ × ℝ, ψ x ≠ 0 → a + δ ≤ x.1 ∧ x.1 ≤ a + c - δ := by
    intro x hx
    have hxs : x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.mpr hx)
    have hxU := hψU hxs
    rw [← hac] at hxU
    have hx1 : a < x.1 ∧ x.1 < a + c := hxU.1
    constructor
    · by_contra h
      push_neg at h
      have hm : ((a, x.2) : ℝ × ℝ) ∈ thickening δ (tsupport ψ) := by
        rw [mem_thickening_iff]
        refine ⟨x, hxs, ?_⟩
        rw [Prod.dist_eq]
        simp only [Real.dist_eq, sub_self, abs_zero]
        rw [abs_of_neg (by linarith)]
        exact max_lt (by linarith) hδ
      exact (lt_irrefl a) (hδU hm).1.1
    · by_contra h
      push_neg at h
      have hm : ((a + c, x.2) : ℝ × ℝ) ∈ thickening δ (tsupport ψ) := by
        rw [mem_thickening_iff]
        refine ⟨x, hxs, ?_⟩
        rw [Prod.dist_eq]
        simp only [Real.dist_eq, sub_self, abs_zero]
        rw [abs_of_pos (by linarith)]
        exact max_lt (by linarith) hδ
      exact (lt_irrefl (a + c)) (hδU hm).1.2
  -- `ψ` vanishes for `|η|` large
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp
    hψc.isCompact.isBounded
  have hψR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have := hR hxs
    rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
    have h2 : ‖x.2‖ ≤ R := (le_max_right _ _).trans this
    rw [Real.norm_eq_abs] at h2
    linarith
  set Φ : ℝ × ℝ → ℝ := fun x => ψ (toIcoMod hc a x.1, x.2) with hΦ
  -- locally, `Φ` is a translate of `ψ`
  have hloc : ∀ x₀ : ℝ × ℝ, Φ =ᶠ[𝓝 x₀]
      fun x => ψ (x.1 - toIcoDiv hc a x₀.1 • c, x.2) := by
    intro x₀
    have hr₀ := toIcoMod_mem_Ico hc a x₀.1
    rw [← self_sub_toIcoDiv_zsmul, zsmul_eq_mul] at hr₀
    have hnb : {x : ℝ × ℝ | |x.1 - x₀.1| < δ} ∈ 𝓝 x₀ :=
      (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const))
        continuous_const).mem_nhds (by simpa using hδ)
    filter_upwards [hnb] with x hx
    simp only [mem_setOf_eq, abs_lt] at hx
    rw [zsmul_eq_mul]
    generalize toIcoDiv hc a x₀.1 = J at hr₀ ⊢
    have hs1 : a - δ < x.1 - J * c := by linarith [hr₀.1, hx.1]
    have hs2 : x.1 - J * c < a + c + δ := by linarith [hr₀.2, hx.2]
    by_cases hrs : toIcoMod hc a x.1 = x.1 - J * c
    · simp only [hΦ, hrs]
    · have h1 : ψ (x.1 - J * c, x.2) = 0 := by
        by_contra hne
        obtain ⟨hl, hu⟩ := hin (x.1 - J * c, x.2) hne
        have hl' : a + δ ≤ x.1 - J * c := hl
        have hu' : x.1 - J * c ≤ a + c - δ := hu
        apply hrs
        rw [toIcoMod_eq_iff]
        exact ⟨⟨by linarith, by linarith⟩, J, by rw [zsmul_eq_mul]; ring⟩
      have h2 : ψ (toIcoMod hc a x.1, x.2) = 0 := by
        by_contra hne
        obtain ⟨hl, hu⟩ := hin _ hne
        have hl' : a + δ ≤ toIcoMod hc a x.1 := hl
        have hu' : toIcoMod hc a x.1 ≤ a + c - δ := hu
        apply hrs
        have hdiff : toIcoMod hc a x.1 - (x.1 - J * c) =
            ((J - toIcoDiv hc a x.1 : ℤ) : ℝ) * c := by
          rw [← self_sub_toIcoDiv_zsmul hc a x.1, zsmul_eq_mul]
          push_cast; ring
        have hm := int_eq_zero_of_abs_mul_lt (c := c) (m := J - toIcoDiv hc a x.1)
          (by rw [← hdiff]; linarith) (by rw [← hdiff]; linarith)
        rw [hm, Int.cast_zero, zero_mul] at hdiff
        linarith
      simp only [hΦ]
      rw [h1, h2]
  refine ⟨Φ, ⟨?_, fun x => ?_, ⟨R, fun x hx => ?_⟩⟩, fun x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
    have hsm : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ψ (x.1 - toIcoDiv hc a x₀.1 • c, x.2)) :=
      hψ.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
    exact hsm.contDiffAt.congr_of_eventuallyEq (hloc x₀)
  · simp only [hΦ, Prod.fst_add, Prod.snd_add, add_zero, toIcoMod_add_right]
  · exact hψR (toIcoMod hc a x.1, x.2) hx
  · simp only [hΦ]
    have hx1 : x.1 ∈ Ico a (a + c) := by rw [hac]; exact hx.1
    rw [(toIcoMod_eq_self hc).mpr hx1]

end Periodize

/-! ### The cylinder test domain -/

theorem cylCell_eq_empty {c : ℝ} (hc : c ≤ 0) : cylCell c = ∅ := by
  rw [cylCell, Set.prod_eq_empty_iff]
  left
  exact Set.Ico_eq_empty (by linarith)

/-- Lebesgue-almost every point of `ℝ × ℝ` has first coordinate `≠ a`. -/
theorem ae_fst_ne (a : ℝ) : ∀ᵐ x : ℝ × ℝ ∂volume, x.1 ≠ a := by
  have h0 : volume ({a} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  simp only [ne_eq, not_not, mem_setOf_eq] at hx
  exact ⟨hx, mem_univ _⟩

/-- **The cylinder** `ℝ/cℤ × ℝ` as a test domain on the carrier `ℝ × ℝ` (S0, decision D1):
Lebesgue measure on the cell `[-c/2, c/2) × ℝ`, directions `∂_q, ∂_η`, and the `c`-periodic
tests of `IsCylTest`. Weak derivatives for it are periodic weak derivatives (tex 4573–4577,
13850–13852). -/
def cylinder (c : ℝ) : TestDomain (ℝ × ℝ) 2 where
  μ := volume.restrict (cylCell c)
  dir := cylDir
  Adm := IsCylTest c
  smooth h := h.smooth
  deriv_mem h v := h.dirDeriv v
  supp {φ} h := by
    obtain ⟨R, hR⟩ := h.bounded
    refine ⟨Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R, isCompact_Icc.prod isCompact_Icc, ?_⟩
    refine ae_restrict_of_forall_mem (measurableSet_cylCell c) fun x hx hxK => ?_
    apply hR
    by_contra hle
    push_neg at hle
    exact hxK ⟨Ico_subset_Icc_self hx.1, abs_le.mp hle⟩
  finite := inferInstance
  ae_zero g hg hφ := by
    rcases le_or_gt c 0 with hc | hc
    · rw [cylCell_eq_empty hc, Measure.restrict_empty, Filter.EventuallyEq,
        MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    set U : Set (ℝ × ℝ) := Ioo (-(c / 2)) (c / 2) ×ˢ univ with hUdef
    have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
    have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (μ := volume.restrict (cylCell c)) (hg.locallyIntegrableOn U) (fun ψ hψ hψc hψU => by
        obtain ⟨Φ, hΦ, hΦψ⟩ := exists_isCylTest_eq hc hψ hψc hψU
        rw [← hφ Φ hΦ]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem (measurableSet_cylCell c)] with x hx
        rw [hΦψ x hx, smul_eq_mul])
    have hmemU : ∀ᵐ x ∂(volume.restrict (cylCell c)), x ∈ U := by
      rw [ae_restrict_iff' (measurableSet_cylCell c)]
      filter_upwards [ae_fst_ne (-(c / 2))] with x hx hxc
      exact ⟨⟨lt_of_le_of_ne hxc.1.1 (Ne.symm hx), hxc.1.2⟩, mem_univ _⟩
    filter_upwards [key, hmemU] with x h1 h2
    exact h1 h2

@[simp] theorem cylinder_adm (c : ℝ) (φ : ℝ × ℝ → ℝ) : (cylinder c).Adm φ ↔ IsCylTest c φ :=
  Iff.rfl

@[simp] theorem cylinder_μ (c : ℝ) : (cylinder c).μ = volume.restrict (cylCell c) := rfl

@[simp] theorem cylinder_dir (c : ℝ) : (cylinder c).dir = cylDir := rfl

end UnforcedLeray.Sob
