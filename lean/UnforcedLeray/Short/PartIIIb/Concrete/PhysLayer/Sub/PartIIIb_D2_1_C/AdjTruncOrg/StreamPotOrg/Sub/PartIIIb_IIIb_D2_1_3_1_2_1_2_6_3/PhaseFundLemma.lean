import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PeriodicBump
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.AePeriodicExtend
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Fundamental lemma over smooth periodic multipliers

Proves `PhaseFundLemma` (source `the November 2 reference manuscript`
lines 1351-1362 and 1334-1337). For a locally integrable `H` on one period, orthogonal to every
smooth `P`-periodic `s`, and a.e. `P`-periodic, `H = 0` a.e.

Route: real test functions `g` supported in `(0,P)` are turned into smooth periodic multipliers
by `periodicBump`; then the Mathlib fundamental lemma on the open set `Ioo 0 P` gives `H = 0` a.e.
there; the a.e. statement is transported to the whole line by `aePeriodicExtend`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phaseFundLemma : PhaseFundLemma := by
  intro P hP H hH hper hS
  -- Step 1: real test functions supported in `(0,P)` annihilate `H`.
  have htest : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo 0 P →
      ∫ x, g x • H x = 0 := by
    intro g hg hgc hgs
    obtain ⟨s, hsC, hsP, hsEq⟩ := periodicBump P hP (fun t => ((g t : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp hg)
      (hgc.comp_left (map_zero Complex.ofRealCLM))
      ((tsupport_comp_subset (map_zero Complex.ofRealCLM) g).trans hgs)
    have hA : ∫ x, g x • H x = ∫ x in Ioc 0 P, g x • H x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : x ∉ tsupport g := fun h => hx (Ioo_subset_Ioc_self (hgs h))
      rw [image_eq_zero_of_notMem_tsupport hx', zero_smul]
    have hB : ∫ x in Ioc 0 P, g x • H x = ∫ t in Ioc 0 P, s t * H t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      simp only [hsEq x hx, Complex.real_smul]
    rw [hA, hB]
    exact hS s hsC hsP
  -- Step 2: `H = 0` a.e. on the open period `Ioo 0 P`.
  have hloc : LocallyIntegrableOn H (Ioo 0 P) volume :=
    (hH.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 P → H x = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
      (fun g hg hgc hgs => htest g hg hgc hgs)
  -- Step 3: pass from `Ioo 0 P` to `Ioc 0 P` (the endpoints differ by a null set).
  have hEq : volume.restrict (Ioo 0 P) = volume.restrict (Ioc 0 P) :=
    Measure.restrict_congr_set (μ := volume) Ioo_ae_eq_Ioc
  have hae' : ∀ᵐ x ∂(volume.restrict (Ioc 0 P)), H x = 0 := by
    rw [← hEq]
    exact (ae_restrict_iff' measurableSet_Ioo).2 hae
  -- Step 4: extend a.e. from one period to the line using periodicity of `H`.
  exact aePeriodicExtend P hP (fun t => H t = 0) hae' (by
    filter_upwards [hper] with t ht
    show H (t + P) = 0 ↔ H t = 0
    rw [ht])

end UnforcedLeray.Short.PartIIIb.Concrete
