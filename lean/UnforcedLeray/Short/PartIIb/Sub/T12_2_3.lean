import UnforcedLeray.Short.PartIIb.Sub.T12_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePeriodicRep
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Part II-b, task `PartII-b:T12/2/3` (`SliceJointHelmholtz`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1923-1926 ("`P_0` applied at
each age"). Target: `LerayLiftSub.SliceJointHelmholtz` (`Sub/T12_2.lean`).

Four sub-lemma Props (true source facts) and the conditional assembly `sliceJointHelmholtz_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem fact_one_le_ofReal {r : ℝ} (hr : 1 < r) : Fact (1 ≤ ENNReal.ofReal r) :=
  ⟨by simpa using ENNReal.ofReal_le_ofReal hr.le⟩

/-- **Sub-lemma `T12/2/3/1`** (class path of slices is strongly measurable; SP 1923-1926). For strongly
measurable `F'` with `hNorm c r F' < ⊤`, there is a strongly measurable path `u : ℝ → Lp` into the
cell `L^r` classes with `u s = [F'(s,·)]` for a.e. `s > 0`. Proof: Tonelli shows `{s | slice ∈ L^r}`
is measurable and conull in `(0,∞)`; approximate `F'` by simple functions `φ_n` (dominated
convergence in the slice norm), put `u s = [slice]` there and `0` elsewhere. -/
def SliceClassPath : Prop :=
  ∀ (c r : ℝ) (hc : 0 < c) (hr : 1 < r) (F' : CProf), StronglyMeasurable F' →
    (∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z)) →
    hNorm c r F' < ⊤ →
    haveI := fact_one_le_ofReal hr
    ∃ u : ℝ → Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c), StronglyMeasurable u ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (u s : ℝ × ℝ → CMerid) =ᵐ[UnforcedLeray.Cyl.avgμ c] (fun z => F' (s, z))

/-- **Sub-lemma `T12/2/3/2`** (`P` acts continuously on cell classes; SP 1923-1926). If `P` satisfies
`HelmBoundP c r C` and `HelmLinP c r`, then there is a continuous map `Φ` on the cell `L^r` classes with
`Φ [F] = [P F]` for every `CylLp` field `F`. Proof: well defined by `HelmLinP` (with `a = -1`) and the
bound (`P(F₁ - F₂)` has norm `≤ C·‖F₁-F₂‖ = 0` if `F₁ = F₂` a.e.); every class has a `c`-periodic
representative (`redQ`), so `Φ [F] := [P F]` is defined on all of `Lp`, and it is Lipschitz with constant
`C` by linearity and the bound. -/
def HelmClassExt : Prop :=
  ∀ (c r C : ℝ) (P : (ℝ × ℝ → CMerid) → (ℝ × ℝ → CMerid)), 0 < c → (hr : 1 < r) → 0 < C →
    HelmBoundP c r C P → HelmLinP c r P →
    haveI := fact_one_le_ofReal hr
    ∃ Φ : Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
        Lp CMerid (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c),
      Continuous Φ ∧ ∀ (F : ℝ × ℝ → CMerid) (h : CylLp c r F),
        (Φ (h.2.toLp F) : ℝ × ℝ → CMerid) =ᵐ[UnforcedLeray.Cyl.avgμ c] P F

/-- **Sub-lemma `T12/2/3/3`** (a.e. reduction to the cell is the identity for `avgμ`). The normalized
cell measure `avgμ c = c⁻¹ vol|_{[-c/2,c/2)} ⊗ vol` is carried by `{redQ c z.1 = z.1}`: `cellμ = volume.restrict (cell c)`,
`cell c = [-c/2, c/2) × ℝ`, and `redQ_of_mem_cell` (`LerayLift/SlicePeriodicRep.lean`). -/
def AvgRedQId : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), (redQ c z.1, z.2) = z

/-- **Joint representative of the slice operator** (non-periodic form): from `SliceClassPath`,
`HelmClassExt`, `SliceCylLpAe` and `exists_stronglyMeasurable_rep`. -/
theorem sliceJointRep_of (h2 : SliceCylLpAe) (h1 : SliceClassPath) (h3 : HelmClassExt)
    (c r C : ℝ) (P : (ℝ × ℝ → CMerid) → (ℝ × ℝ → CMerid)) (hc : 0 < c) (hr : 1 < r) (hC : 0 < C)
    (hB : HelmBoundP c r C P) (hL : HelmLinP c r P) (F' : CProf) (hF : StronglyMeasurable F')
    (hper : ∀ (s : ℝ) (z : ℝ × ℝ), F' (s, (z.1 + c, z.2)) = F' (s, z)) (hfin : hNorm c r F' < ⊤) :
    ∃ G0 : CProf, StronglyMeasurable G0 ∧
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (fun z => G0 (s, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c] P (fun z => F' (s, z)) := by
  haveI := fact_one_le_ofReal hr
  obtain ⟨u, hu, hue⟩ := h1 c r hc hr F' hF hper hfin
  obtain ⟨Φ, hΦ, hΦe⟩ := h3 c r C P hc hr hC hB hL
  have hm : StronglyMeasurable (fun s => Φ (u s)) := hΦ.comp_stronglyMeasurable hu
  obtain ⟨G0, hG0, hG0e⟩ := Infra.JointMeasurableRep.exists_stronglyMeasurable_rep hm
  refine ⟨G0, hG0, ?_⟩
  have hcyl := h2 c r hc hr F' hF hper hfin
  filter_upwards [hue, hcyl] with s hs hcs
  have hus : u s = hcs.2.toLp (fun z => F' (s, z)) := by
    exact Lp.ext_iff.mpr (hs.trans (MemLp.coeFn_toLp hcs.2).symm)
  calc (fun z => G0 (s, z)) =ᵐ[UnforcedLeray.Cyl.avgμ c] (Φ (u s) : ℝ × ℝ → CMerid) := hG0e s
    _ =ᵐ[UnforcedLeray.Cyl.avgμ c] P (fun z => F' (s, z)) := by
      rw [hus]; exact hΦe _ hcs

/-- **Conditional assembly of the target** `SliceJointHelmholtz` from the sub-lemmas. -/
theorem sliceJointHelmholtz_of (h1 : SliceClassPath) (h2 : SliceCylLpAe) (h3 : HelmClassExt)
    (h4 : AvgRedQId) : SliceJointHelmholtz := by
  intro c r C P hc hr hC hB hL F' hF hper hfin
  obtain ⟨G0, hG0, hG0e⟩ := sliceJointRep_of h2 h1 h3 c r C P hc hr hC hB hL F' hF hper hfin
  refine ⟨fun x => G0 (redCoord c x), ?_, ?_, ?_⟩
  · exact hG0.comp_measurable (measurable_redCoord c)
  · intro s z
    simp only [redCoord, redQ_add_period hc]
  · filter_upwards [hG0e] with s hs
    have hred : (fun z : ℝ × ℝ => G0 (redCoord c (s, z))) =ᵐ[UnforcedLeray.Cyl.avgμ c]
        (fun z => G0 (s, z)) := by
      filter_upwards [h4 c hc] with z hz
      simp only [redCoord]
      rw [hz]
    exact hred.trans hs

end UnforcedLeray.Short.IIb.LerayLiftSub
