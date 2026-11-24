import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2

/-!
# Part III-a, `PartIII-a:T21/2/2/1`: continuity of `E_0, E_1`, decomposed

Source of record: `the November 2 reference manuscript` lines 3060-3071.

`revE0 ν c m φ s = adjF0 ν c m φ ∘ revAge ν s` and `revE1 ν c m φ s = adjF1 ν c m φ ∘ revAge ν s`
(definitionally), where `adjF0, adjF1` are the energies as functions of the age `r`. Continuity then
splits into: the age map (A), `E_0` as a function of the age on `[t, s]` (B, from `strongCont`),
`E_1` as a function of the age on `[t, s)` (C, from `jointSmooth`, `memH1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `E_0` as a function of the age `r` (the moving cell has length `c/√a(r)`). -/
def adjF0 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  adjE0 (cellLen c (clockA ν r)) m (movingPhi ν φ r)

/-- `E_1` as a function of the age `r`. -/
def adjF1 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  adjE1 (cellLen c (clockA ν r)) m (movingPhi ν φ r)

/-- Lemma A: the age map `ζ ↦ revAge ν s ζ` is continuous on `[0, Δz]` and sends `[0, Δz]` into
`[t, s]` and `(0, Δz]` into `[t, s)` (SP 2857, 3077). -/
def AdjAgeMap : Prop :=
  ∀ ν t s : ℝ, 0 < ν → 0 ≤ t → t < s →
    ContinuousOn (revAge ν s) (Icc 0 (deltaZ ν t s)) ∧
    MapsTo (revAge ν s) (Icc 0 (deltaZ ν t s)) (Icc t s) ∧
    MapsTo (revAge ν s) (Ioc 0 (deltaZ ν t s)) (Ico t s)

/-- Lemma B: `E_0` is continuous in the age on `[t, s]` for an adjoint flow (SP 3060-3071; from
`IsAdjointFlow.strongCont` and `memX`). -/
def AdjF0Cont : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 0 < ν → 0 < c → 0 ≤ t → t < s →
    IsAdjointFlow ν c m tr t s g φ → ContinuousOn (adjF0 ν c m φ) (Icc t s)

/-- Lemma C: `E_1` is continuous in the age on `[t, s)` for an adjoint flow (SP 3060-3071; from
`IsAdjointFlow.jointSmooth`, `memH1`, dominated convergence on compact subintervals). -/
def AdjF1Cont : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 0 < ν → 0 < c → 0 ≤ t → t < s →
    IsAdjointFlow ν c m tr t s g φ → ContinuousOn (adjF1 ν c m φ) (Ico t s)

theorem adjointEnergyCont_of (m : ℝ) (hA : AdjAgeMap) (hB : AdjF0Cont) (hC : AdjF1Cont) :
    AdjointEnergyCont m := by
  refine ⟨0, fun b _ => ⟨0, 1, le_rfl, one_pos, ?_⟩⟩
  intro ν hν tr _ t s ht hts _ _ G _ φ hφ
  obtain ⟨hcont, hm1, hm2⟩ := hA ν t s hν.1 ht hts
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν.1 _
  refine ⟨?_, ?_⟩
  · exact (hB ν _ m tr t s _ φ hν.1 hc ht hts hφ).comp hcont hm1
  · exact (hC ν _ m tr t s _ φ hν.1 hc ht hts hφ).comp (hcont.mono Ioc_subset_Icc_self) hm2

end UnforcedLeray.Short.IIIa
