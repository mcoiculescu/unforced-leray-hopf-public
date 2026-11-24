import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.Compact

/-!
# A dense domain of compactly supported complex L² functions

The support condition is stated almost everywhere on representatives, so it
defines a genuine submodule of Lebesgue L². Its inclusion has dense range, and
every representative is integrable. This domain supports extension of the
actual one-dimensional Green operator from compactly supported inputs.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Sturm

abbrev ComplexL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- L² equivalence classes whose representatives vanish a.e. outside some
compact interval. -/
def compactL2 : Submodule ℂ ComplexL2 where
  carrier := {f | ∃ a b : ℝ, ∀ᵐ x, x ∉ Icc a b → f x = 0}
  zero_mem' := by
    refine ⟨0, 0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    intro _
    exact hx
  add_mem' := by
    rintro f g ⟨a, b, hf⟩ ⟨c, d, hg⟩
    refine ⟨min a c, max b d, ?_⟩
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx hfg
    intro hx
    have hxab : x ∉ Icc a b := by
      intro h
      exact hx ⟨(min_le_left a c).trans h.1, h.2.trans (le_max_left b d)⟩
    have hxcd : x ∉ Icc c d := by
      intro h
      exact hx ⟨(min_le_right a c).trans h.1, h.2.trans (le_max_right b d)⟩
    simpa only [Pi.add_apply, hfx hxab, hgx hxcd, zero_add] using hfg
  smul_mem' := by
    rintro c f ⟨a, b, hf⟩
    refine ⟨a, b, ?_⟩
    filter_upwards [hf, Lp.coeFn_smul c f] with x hfx hcf
    intro hx
    simpa only [Pi.smul_apply, hfx hx, smul_zero] using hcf

@[simp]
theorem mem_compactL2_iff (f : ComplexL2) :
    f ∈ compactL2 ↔ ∃ a b : ℝ, ∀ᵐ x, x ∉ Icc a b → f x = 0 := Iff.rfl

/-- Actual compact support gives the interval support condition used by the
Green-kernel estimates. -/
theorem exists_interval_of_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ a b : ℝ, ∀ x, x ∉ Icc a b → f x = 0 := by
  obtain ⟨a, ha⟩ := hf.bddBelow
  obtain ⟨b, hb⟩ := hf.bddAbove
  refine ⟨a, b, fun x hx => ?_⟩
  by_contra hfx
  have hxs : x ∈ tsupport f := subset_tsupport f hfx
  exact hx ⟨ha hxs, hb hxs⟩

/-- An L² class with a compactly supported representative belongs to the domain. -/
theorem mem_compactL2_of_ae_eq_hasCompactSupport {f : ComplexL2} {g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) (hg : HasCompactSupport g) : f ∈ compactL2 := by
  obtain ⟨a, b, hab⟩ := exists_interval_of_hasCompactSupport hg
  refine ⟨a, b, ?_⟩
  filter_upwards [hfg] with x hx
  intro hxab
  exact hx.trans (hab x hxab)

theorem dense_compactL2 : Dense (compactL2 : Set ComplexL2) := by
  have hd := Lp.dense_hasCompactSupport_contDiff
    (E := ℝ) (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)
  apply hd.mono
  rintro f ⟨g, hfg, hg, _⟩
  exact mem_compactL2_of_ae_eq_hasCompactSupport hfg hg

theorem denseRange_compactL2_subtypeL : DenseRange compactL2.subtypeL := by
  exact denseRange_subtype_val.mpr dense_compactL2

/-- Every L² representative supported a.e. in a compact interval is in L¹. -/
theorem integrable_of_mem_compactL2 {f : ComplexL2} (hf : f ∈ compactL2) :
    Integrable f := by
  obtain ⟨a, b, hab⟩ := hf
  have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hi : IntegrableOn f (Icc a b) := ((Lp.memLp f).restrict _).integrable one_le_two
  exact hi.integrable_of_ae_notMem_eq_zero hab

namespace CompactL2

theorem integrable (f : compactL2) : Integrable (f : ComplexL2) :=
  integrable_of_mem_compactL2 f.property

theorem exists_interval (f : compactL2) :
    ∃ a b : ℝ, ∀ᵐ x, x ∉ Icc a b → (f : ComplexL2) x = 0 := f.property

end CompactL2

end UnforcedLeray.Sturm
