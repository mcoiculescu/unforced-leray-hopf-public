import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Unique

/-!
# `PartIII-a:T21/2/2/3/6/1/2`: `WeakFieldBandInt` from three leaves

Source: `the November 2 reference manuscript` lines 3052-3058 (adjoint localized
interaction in `H^1_{-m,d}`), 3044-3047 (the weight `jb^{-m}` is bounded below on bands).

A field with weak gradient `g'` and finite `h1Norm` has finite `X_{-m,d}` norms of `χ'`, `g'_j`
(proved here).  A.e. measurability on bands comes from the integrability against the tests
(`TestMeasF`, `TestMeasDeriv`: countable cover of the band by cos/sin times bump tests);
`BandIntOfL2` is the local `L²` to `L¹` step using the weight lower bound on a band.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Leaf A: a field integrable against every cylinder test is a.e. strongly measurable on every
band (countable cover of the band by the nonvanishing sets of the tests
`bump(η) cos(2πq/d)`, `bump(η) sin(2πq/d)`; on each, `f = (f ψ)/ψ`). -/
def TestMeasF : Prop :=
  ∀ (d : ℝ) (f : ℝ × ℝ → ℂ), 0 < d →
    (∀ ψ, B0579.IsCylTest d ψ → IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell d)) →
    ∀ R : ℝ, AEStronglyMeasurable f (volume.restrict (bandSet d R))

/-- Leaf B: as `TestMeasF`, but with integrability against `∂_jψ` (the tests `∂_j ψ` for the
same cos/sin-bump family have nonvanishing sets covering the band). -/
def TestMeasDeriv : Prop :=
  ∀ (d : ℝ) (j : Fin 2) (f : ℝ × ℝ → ℂ), 0 < d →
    (∀ ψ, B0579.IsCylTest d ψ → IntegrableOn (fun x => f x * (B0579.pd j ψ x : ℂ)) (B0579.cell d)) →
    ∀ R : ℝ, AEStronglyMeasurable f (volume.restrict (bandSet d R))

/-- Leaf C: an a.e. measurable field of finite `X_{-m,d}` norm is integrable on every band
(the density `jb^{-m}` is bounded below on the band, which has finite measure). -/
def BandIntOfL2 : Prop :=
  ∀ (d m : ℝ) (f : ℝ × ℝ → ℂ), 0 < d → xNorm d (-m) f ≠ ⊤ →
    ∀ R : ℝ, AEStronglyMeasurable f (volume.restrict (bandSet d R)) →
      IntegrableOn f (bandSet d R)

theorem h1Norm_components_ne_top {d m : ℝ} {φ : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (h : h1Norm d m φ g ≠ ⊤) : xNorm d (-m) φ ≠ ⊤ ∧ ∀ j, xNorm d (-m) (g j) ≠ ⊤ := by
  unfold h1Norm at h
  have hS : xNorm d (-m) φ ^ 2 + ∑ j, xNorm d (-m) (g j) ^ 2 ≠ ⊤ := by
    intro hS
    exact h (by rw [hS]; exact ENNReal.top_rpow_of_pos (by norm_num))
  have h0 : xNorm d (-m) φ ^ 2 ≠ ⊤ := ne_top_of_le_ne_top hS le_self_add
  have hs : ∑ j, xNorm d (-m) (g j) ^ 2 ≠ ⊤ := ne_top_of_le_ne_top hS le_add_self
  refine ⟨fun h' => h0 (by rw [h']; exact ENNReal.top_pow (by norm_num)), fun j h' => ?_⟩
  have hj : xNorm d (-m) (g j) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top hs (Finset.single_le_sum (f := fun j => xNorm d (-m) (g j) ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ j))
  exact hj (by rw [h']; exact ENNReal.top_pow (by norm_num))

theorem weakFieldBandInt_of (m : ℝ) (a : TestMeasF) (b : TestMeasDeriv) (c : BandIntOfL2) :
    WeakFieldBandInt m := by
  intro d χ' g' hd hw hne R
  obtain ⟨hx0, hxj⟩ := h1Norm_components_ne_top hne
  have hχm : AEStronglyMeasurable χ' (volume.restrict (bandSet d R)) :=
    b d 0 χ' hd (fun ψ hψ => ((hw 0).1 ψ hψ).1) R
  refine ⟨c d m χ' hd hx0 R hχm, fun j => ?_⟩
  exact c d m (g' j) hd (hxj j) R (a d (g' j) hd (fun ψ hψ => ((hw j).1 ψ hψ).2) R)

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.weakFieldBandInt_of
