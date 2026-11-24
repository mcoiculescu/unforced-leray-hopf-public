import UnforcedLeray.Short.PartI.Sub.PartI_T08_6_2

/-!
# Cutoff helpers for the order-zero pressure orthogonality (`PartI:T08/6/2`)

Shared by `Zero/IBP.lean` (`etaCutIBP_proof`) and `Zero/Tail.lean` (`etaCutTail_proof`).
Source: `the November 2 reference manuscript`, line 346.

* the slab `{|η| ≤ 2R}` meets the centred cell in a box of measure `c · 4R`;
* a bounded measurable function vanishing for `|η| > 2R`, times an `L²(cell)` function, is
  integrable on the cell (the slab has finite measure);
* the derivative `η ↦ deriv (etaCut R) η` is `R⁻¹ · etaBump'(R⁻¹ η)`, bounded by `K / R` and
  zero for `|η| > 2R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The slab `|η| ≤ 2R` in the plane. -/
def slab (R : ℝ) : Set Plane := {z | |z.2| ≤ 2 * R}

theorem measurableSet_slab (R : ℝ) : MeasurableSet (slab R) :=
  measurableSet_le (continuous_abs.comp continuous_snd).measurable measurable_const

theorem volume_cell_inter_slab {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) :
    volume (Cyl.cell c ∩ slab R) = ENNReal.ofReal (c * (4 * R)) := by
  have hset : Cyl.cell c ∩ slab R = Ico (-c / 2) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) := by
    ext z
    simp only [Cyl.cell, slab, mem_inter_iff, mem_prod, mem_Ico, mem_univ, and_true,
      mem_setOf_eq, mem_Icc, abs_le]
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ c / 2 - -c / 2 by linarith)]
  congr 1
  ring

/-- A bounded measurable function vanishing for `|η| > 2R`, times an `L²` function, is
integrable on the centred cell. -/
theorem integrableOn_cell_mul_of_slab {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R)
    {φ g : Plane → ℝ} (hφm : Measurable φ) {B : ℝ} (hB : ∀ z, |φ z| ≤ B)
    (hsupp : ∀ z : Plane, 2 * R < |z.2| → φ z = 0)
    (hg : MemLp g 2 (Cyl.cellμ c)) :
    IntegrableOn (fun z => φ z * g z) (Cyl.cell c) := by
  have hfin : Cyl.cellμ c (slab R) ≠ ⊤ := by
    rw [Cyl.cellμ, Measure.restrict_apply (measurableSet_slab R), Set.inter_comm,
      volume_cell_inter_slab hc hR]
    exact ENNReal.ofReal_ne_top
  have : IsFiniteMeasure ((Cyl.cellμ c).restrict (slab R)) := isFiniteMeasure_restrict.2 hfin
  have hgS : Integrable g ((Cyl.cellμ c).restrict (slab R)) :=
    (hg.restrict (slab R)).integrable (show (1 : ENNReal) ≤ 2 by norm_num)
  have hint : Integrable (fun z => φ z * g z) ((Cyl.cellμ c).restrict (slab R)) :=
    hgS.bdd_mul hφm.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hB z)
  have hsupp' : Function.support (fun z => φ z * g z) ⊆ slab R := by
    intro z hz
    by_contra h
    apply hz
    have h' : 2 * R < |z.2| := by
      simp only [slab, mem_setOf_eq, not_le] at h
      exact h
    simp [hsupp z h']
  have hI : IntegrableOn (fun z => φ z * g z) (slab R) (Cyl.cellμ c) := hint
  exact (integrableOn_iff_integrable_of_support_subset hsupp').1 hI

/-- Bounded measurable factor times an integrable function on the cell. -/
theorem integrableOn_cell_mul_of_bdd {c : ℝ} {φ g : Plane → ℝ} (hg : IntegrableOn g (Cyl.cell c))
    (hφm : Measurable φ) {B : ℝ} (hB : ∀ z, |φ z| ≤ B) :
    IntegrableOn (fun z => φ z * g z) (Cyl.cell c) :=
  hg.bdd_mul hφm.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB z)

/-- Pointwise equal integrands. -/
theorem integrableOn_congr_pt {f g : Plane → ℝ} {s : Set Plane} (h : IntegrableOn f s)
    (e : ∀ z, f z = g z) : IntegrableOn g s :=
  h.congr (Eventually.of_forall e)

/-- The cutoff derivative is continuous and measurable in the plane. -/
theorem etaBump_contDiff : ContDiff ℝ ∞ (⇑etaBump) := etaBump.contDiff

theorem measurable_deriv_etaCut (R : ℝ) :
    Measurable (fun z : Plane => deriv (etaCut R) z.2) := by
  have hc : Continuous (deriv (etaCut R)) :=
    (contDiff_etaCut R).continuous_deriv (by norm_num)
  exact hc.measurable.comp measurable_snd

theorem etaBump_deriv_bound : ∃ K : ℝ, ∀ x : ℝ, ‖deriv (⇑etaBump) x‖ ≤ K := by
  have hc : Continuous (deriv (⇑etaBump)) :=
    etaBump_contDiff.continuous_deriv (by norm_num)
  exact etaBump.hasCompactSupport.deriv.exists_bound_of_continuous hc

theorem etaCut_deriv_eq (R η : ℝ) :
    deriv (etaCut R) η = deriv (⇑etaBump) (R⁻¹ * η) * R⁻¹ := by
  have hb : HasDerivAt (⇑etaBump) (deriv (⇑etaBump) (R⁻¹ * η)) (R⁻¹ * η) :=
    ((etaBump_contDiff.differentiable (by norm_num)) (R⁻¹ * η)).hasDerivAt
  have hl : HasDerivAt (fun x : ℝ => R⁻¹ * x) R⁻¹ η := by
    simpa using (hasDerivAt_id η).const_mul R⁻¹
  exact (hb.comp η hl).deriv

theorem etaCut_deriv_abs_le {R : ℝ} (hR : 0 < R) {K : ℝ}
    (hK : ∀ x : ℝ, ‖deriv (⇑etaBump) x‖ ≤ K) (η : ℝ) :
    |deriv (etaCut R) η| ≤ K * R⁻¹ := by
  rw [etaCut_deriv_eq, abs_mul, abs_of_pos (inv_pos.2 hR)]
  have h := hK (R⁻¹ * η)
  rw [Real.norm_eq_abs] at h
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.2 hR.le)

theorem etaCut_deriv_eq_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (h : 2 * R < |η|) :
    deriv (etaCut R) η = 0 := by
  have hopen : IsOpen {x : ℝ | 2 * R < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 η] etaCut R := by
    filter_upwards [hopen.mem_nhds h] with x hx
    exact (etaCut_eq_zero hR (le_of_lt (show 2 * R < |x| from hx))).symm
  rw [← hev.deriv_eq]
  simp

end UnforcedLeray.Short.PartI
