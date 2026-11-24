import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt.Cover

/-!
# Leaf `T12/1/3/1/d`: `ρ * D ∈ L^r(avgμ c)`

Proves `cylMollMemLp : CylMollMemLp` (SP 1923-1926). Steps.
* `D` is a.e. strongly measurable on the plane (`aestronglyMeasurable_of_cell`).
* A strongly measurable, everywhere `c`-periodic representative `g'` of `D` is built by the
  floor shift `g'(q, η) = g₀(q - c⌊q/c⌋, η)` (as in `flatHeatContraction`); `g' = D` a.e.
* `cylMoll ρ D = cylMoll ρ g'` pointwise, since the integrands agree a.e. in `y`
  (`y ↦ z - y` is measure preserving).
* Minkowski on the cell (`UnforcedLeray.Cyl.eLpNorm_planarConv_periodic_le`) with the kernel
  `ρ.normed volume` (`L^1` norm finite, continuous with compact support) gives
  `‖ρ * g'‖_{L^r(cellμ c)} ≤ ‖ρ.normed‖_{L^1} ‖D‖_{L^r(cellμ c)} < ∞`.
* Strong measurability of `ρ * g'` comes from `StronglyMeasurable.integral_prod_right'`.
* `avgμ c = ofReal c⁻¹ • cellμ c` gives the statement for the normalized measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- A strongly measurable, everywhere `c`-periodic representative of an a.e. strongly measurable
periodic field. -/
theorem exists_periodic_sm {c : ℝ} (hc : 0 < c) {D : ℝ × ℝ → CMerid}
    (hper : UnforcedLeray.Cyl.IsPeriodic c D) (hD : AEStronglyMeasurable D (volume : Measure (ℝ × ℝ))) :
    ∃ g' : ℝ × ℝ → CMerid, StronglyMeasurable g' ∧ UnforcedLeray.Cyl.IsPeriodic c g' ∧
      g' =ᵐ[volume] D := by
  set g₀ : ℝ × ℝ → CMerid := hD.mk D with hg₀def
  have hg₀m : StronglyMeasurable g₀ := hD.stronglyMeasurable_mk
  have hg₀ : g₀ =ᵐ[volume] D := hD.ae_eq_mk.symm
  have hfl : Measurable (fun z : ℝ × ℝ => ((⌊z.1 / c⌋ : ℤ) : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (Int.measurable_floor.comp (measurable_fst.div_const c))
  have hS : Measurable (fun z : ℝ × ℝ => (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2)) :=
    (measurable_fst.sub (hfl.mul_const c)).prodMk measurable_snd
  refine ⟨fun z => g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2), hg₀m.comp_measurable hS, ?_, ?_⟩
  · intro z
    show g₀ ((z.1 + c) - ((⌊(z.1 + c) / c⌋ : ℤ) : ℝ) * c, z.2) =
      g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2)
    have hfl1 : ⌊(z.1 + c) / c⌋ = ⌊z.1 / c⌋ + 1 := by
      rw [add_div, div_self hc.ne']
      exact Int.floor_add_one _
    have e : z.1 + c - (((⌊z.1 / c⌋ + 1 : ℤ)) : ℝ) * c = z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [hfl1, e]
  · have hA : ∀ k : ℤ, ∀ᵐ z : ℝ × ℝ, g₀ (z.1 + ((-k : ℤ) : ℝ) * c, z.2) = D z := by
      intro k
      have h1 : ∀ᵐ z : ℝ × ℝ, g₀ (z.1 + ((-k : ℤ) : ℝ) * c, z.2) =
          D (z.1 + ((-k : ℤ) : ℝ) * c, z.2) :=
        (UnforcedLeray.Cyl.measurePreserving_shift (((-k : ℤ) : ℝ) * c)).quasiMeasurePreserving.ae
          (p := fun w => g₀ w = D w) hg₀
      filter_upwards [h1] with z hz
      rw [hz]
      exact UnforcedLeray.Cyl.IsPeriodic.add_int_mul hper (-k) z
    have hall : ∀ᵐ z : ℝ × ℝ, ∀ k : ℤ, g₀ (z.1 + ((-k : ℤ) : ℝ) * c, z.2) = D z :=
      (ae_all_iff (p := fun (z : ℝ × ℝ) (k : ℤ) => g₀ (z.1 + ((-k : ℤ) : ℝ) * c, z.2) = D z)).2 hA
    filter_upwards [hall] with z hz
    show g₀ (z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) = D z
    have h2 := hz ⌊z.1 / c⌋
    have e : z.1 - ((⌊z.1 / c⌋ : ℤ) : ℝ) * c = z.1 + ((-⌊z.1 / c⌋ : ℤ) : ℝ) * c := by
      push_cast; ring
    rw [e]
    exact h2

theorem cylMollMemLp : CylMollMemLp := by
  intro c r hc hr D hD ρ
  have hr0 : 0 < r := by linarith
  have hper : UnforcedLeray.Cyl.IsPeriodic c D := hD.1
  have hcell : MemLp D (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) :=
    CylLocIntCover.memLp_cell_of_avg hc hD.2
  have hAE : AEStronglyMeasurable D (volume : Measure (ℝ × ℝ)) :=
    CylLocIntCover.aestronglyMeasurable_of_cell hc hper hcell.aestronglyMeasurable
  obtain ⟨g', hg'm, hg'per, hg'eq⟩ := exists_periodic_sm hc hper hAE
  have hcyl : cylMoll ρ D = cylMoll ρ g' := by
    funext z
    unfold cylMoll
    apply integral_congr_ae
    have h1 : ∀ᵐ y : ℝ × ℝ, g' (z - y) = D (z - y) :=
      (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae
        (p := fun w => g' w = D w) hg'eq
    filter_upwards [h1] with y hy
    rw [hy]
  have hk : StronglyMeasurable (ρ.normed volume) :=
    ρ.continuous_normed.stronglyMeasurable
  have hkfin : eLpNorm (ρ.normed volume) 1 volume < ∞ :=
    (ρ.continuous_normed.memLp_of_hasCompactSupport (p := 1)
      ρ.hasCompactSupport_normed).eLpNorm_lt_top
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  have hbound := UnforcedLeray.Cyl.eLpNorm_planarConv_periodic_le hc hk hg'm hg'per hp
    ENNReal.ofReal_ne_top
  have hae : g' =ᵐ[UnforcedLeray.Cyl.cellμ c] D := ae_restrict_of_ae hg'eq
  have hg'L : eLpNorm g' (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) =
      eLpNorm D (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) := eLpNorm_congr_ae hae
  have hfin : eLpNorm (cylMoll ρ g') (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) < ∞ := by
    rw [hg'L] at hbound
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hkfin hcell.eLpNorm_lt_top)
  have hsm : StronglyMeasurable (cylMoll ρ g') := by
    have h2 : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        ρ.normed volume p.2 • g' (p.1 - p.2)) :=
      (hk.comp_measurable measurable_snd).smul
        (hg'm.comp_measurable (measurable_fst.sub measurable_snd))
    exact StronglyMeasurable.integral_prod_right' (ν := volume) h2
  have hMemCell : MemLp (cylMoll ρ g') (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) :=
    ⟨hsm.aestronglyMeasurable, hfin⟩
  rw [hcyl]
  exact hMemCell.smul_measure (ENNReal.ofReal_ne_top (r := c⁻¹))

end UnforcedLeray.Short.IIb
