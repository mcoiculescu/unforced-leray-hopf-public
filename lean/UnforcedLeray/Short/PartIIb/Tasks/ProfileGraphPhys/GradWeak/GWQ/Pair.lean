import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.HolderBound
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: phase pairings (integrability, linearity, a.e. congruence)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem slab_ac (P : ℝ) : hSlab P ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) (Measure.AbsolutelyContinuous.refl _)

theorem integrable_pair {P r : ℝ} (hP : 0 < P) (hr : 1 < r) {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) {u : ℝ × Space → CVec3}
    (hm : AEStronglyMeasurable u volume) (hfin : phaseLpNorm P r u ≠ ⊤) :
    Integrable (fun z => dotL (Φ z) (u z)) (hSlab P) := by
  set u' := hm.mk u with hu'
  have hae : u =ᵐ[volume] u' := hm.ae_eq_mk
  have hmeas : Measurable u' := hm.stronglyMeasurable_mk.measurable
  have hn : phaseLpNorm P r u = phaseLpNorm P r u' := phaseLpNorm_congr_ae hae
  obtain ⟨K, hK⟩ := phase_holder_bound P r hP hr Φ hΦ
  have h1 := (hK u' hmeas (by rw [← hn]; exact hfin)).1
  refine h1.congr ?_
  have : ∀ᵐ z ∂(hSlab P), u z = u' z := (slab_ac P).ae_eq hae
  filter_upwards [this] with z hz
  rw [hz]

theorem phaseInt_congr_ae {P : ℝ} {f f' : ℝ × Space → ℂ} (h : f =ᵐ[volume] f') :
    phaseInt P f = phaseInt P f' := by
  unfold phaseInt
  congr 1
  have h2 : ∀ᵐ t : ℝ, ∀ᵐ y : Space, f (t, y) = f' (t, y) := by
    rw [Measure.volume_eq_prod] at h
    exact Measure.ae_ae_of_ae_prod h
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h2] with t ht
  exact integral_congr_ae ht

theorem phaseInt_add' {P : ℝ} {f g : ℝ × Space → ℂ} (hf : Integrable f (hSlab P))
    (hg : Integrable g (hSlab P)) :
    phaseInt P (fun z => f z + g z) = phaseInt P f + phaseInt P g := by
  rw [phaseInt_eq_slab (f := fun z => f z + g z) (hf.add hg), phaseInt_eq_slab hf,
    phaseInt_eq_slab hg, integral_add hf hg, smul_add]

theorem phaseInt_neg' {P : ℝ} {f : ℝ × Space → ℂ} :
    phaseInt P (fun z => -f z) = -phaseInt P f := by
  unfold phaseInt
  simp [integral_neg]

theorem phaseInt_add3 {P : ℝ} {f0 f1 f2 : ℝ × Space → ℂ} (h0 : Integrable f0 (hSlab P))
    (h1 : Integrable f1 (hSlab P)) (h2 : Integrable f2 (hSlab P)) :
    phaseInt P (fun x => f0 x + f1 x + f2 x) = phaseInt P f0 + phaseInt P f1 + phaseInt P f2 := by
  have := phaseInt_add' (f := fun x => f0 x + f1 x) (g := f2) (h0.add h1) h2
  rw [this, phaseInt_add' h0 h1]

theorem pairF_add3 {P r : ℝ} (hP : 0 < P) (hr : 1 < r) {F0 F1 F2 : ℝ × Space → CVec3}
    (h0 : IsPhaseTest P F0) (h1 : IsPhaseTest P F1) (h2 : IsPhaseTest P F2)
    {u : ℝ × Space → CVec3} (hm : AEStronglyMeasurable u volume) (hfin : phaseLpNorm P r u ≠ ⊤) :
    pairF P (fun x => F0 x + F1 x + F2 x) u = pairF P F0 u + pairF P F1 u + pairF P F2 u := by
  have i0 := integrable_pair hP hr h0 hm hfin
  have i1 := integrable_pair hP hr h1 hm hfin
  have i2 := integrable_pair hP hr h2 hm hfin
  unfold pairF
  have e : (fun x => dotL (F0 x + F1 x + F2 x) (u x)) =
      fun x => (dotL (F0 x) (u x) + dotL (F1 x) (u x)) + dotL (F2 x) (u x) := by
    funext x; simp [map_add, ContinuousLinearMap.add_apply, add_assoc]
  rw [e]
  exact phaseInt_add3 i0 i1 i2

end UnforcedLeray.Short.IIb.GWQ
