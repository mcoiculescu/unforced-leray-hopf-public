import UnforcedLeray.Short.PartIIb.Bridge.Consequences
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1

/-!
# Bridge: the `r = 2` adjoint in the field model

Source of record: `the November 2 reference manuscript`, lines 1359-1361 (the adjoint
has the same maximal graph and bound at `r = 2`, Leray projection of the datum), 1426-1440
(`L* = -𝒯 - νΔ + 1`, reversed phase window).

`field_adjoint_exists_of` : from the abstract `CommonBodyAdjoint` (Part II-a) and the source fact
`AdjSolSolenoidal` (the adjoint solution with a solenoidal datum is solenoidal: `𝐏` commutes with
the adjoint resolvent, 1498-1500), every weakly solenoidal `f ∈ Y_2` is `(μ + L₀)ᵗΦ` for a `Φ` with
all the `FWUAdjDom` clauses of `PartIIIb.Concrete` (this is `FWUAdjSolve`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-- `L₀Ψ` is a phase test for a phase test `Ψ`. -/
theorem isPhaseTest_L0 {P : ℝ} {Ψ : ℝ × Space → CVec3} (hΨ : IsPhaseTest P Ψ) (ν : ℝ) :
    IsPhaseTest P (L0 ν Ψ) := by
  have h := ((hΨ.dτ.sub (hΨ.radialT.const_smul (1 / 2 : ℝ))).sub
    (hΨ.lapT.const_smul ν)).sub (hΨ.const_smul (1 / 2 : ℝ))
  convert h using 1
  funext p
  simp [L0, T0]

/-- **Adjoint solenoidality** (source 1359-1361, 1498-1500): for a solenoidal datum `F ∈ Y_{2,σ}`, a
distributional solution `W ∈ Y_2` of the adjoint equation `(μ̄ + L₀)ᵗ`-pairing is solenoidal
(`𝐏` commutes with the adjoint heat/dilation/phase semigroup; uniqueness from the `r = 2`
graph bound). -/
def AdjSolSolenoidal : Prop :=
  ∀ (P ν μ : ℝ) [Fact (0 < P)], P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 → ∀ Fq Wq : Yq P 2,
    Fq ∈ Ysigma P 2 →
      HasPhaseOp (fun Φ => (starRingEnd ℂ) (μ : ℂ) • Φ + L0 ν Φ) Wq Fq → Wq ∈ Ysigma P 2

/-- **(e)** Adjoint solvability in the field model (`FWUAdjSolve` of
`Short/PartIII-b/Sub/PartIII-b_IIIb-D2_1_3_1.lean`). -/
theorem field_adjoint_exists_of (hAdj : CommonBodyAdjoint) (hSol : AdjSolSolenoidal) :
    ∀ (P ν μ : ℝ), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
      ∀ f : ℝ × Space → CVec3, IsInYr P 2 f → UnforcedLeray.Short.PartIIIb.Concrete.IsWeakSolenoidal P f →
        ∃ Φ, UnforcedLeray.Short.PartIIIb.Concrete.FWUAdjDom P ν μ Φ f := by
  intro P ν μ hP hP1 hν hμ f hf hweak
  haveI : Fact (0 < P) := ⟨hP⟩
  have h2 : (ENNReal.toReal 2) = 2 := by simp
  obtain ⟨Fq, hFrep, -⟩ := exists_hasRepY_q P 2 (by norm_num) (q := 2) (by simp) h2 f hf
  have hFs : Fq ∈ Ysigma P 2 := by
    intro φ hφ
    rw [phasePair_eq_pairF_of_hasRepY Fq f hFrep hφ.gradT]
    exact hweak φ hφ
  obtain ⟨C, -, hC⟩ := hAdj
  obtain ⟨⟨Wq, hWeq⟩, hmax⟩ := hC P hP1 ν hν (μ : ℂ) (by simpa using hμ) Fq
  obtain ⟨hD, -⟩ := hmax Wq hWeq
  have hWs : Wq ∈ Ysigma P 2 := hSol P ν μ hP1 hν hμ Fq Wq hFs hWeq
  obtain ⟨Wf, hWin, hWrep, -⟩ := exists_isInYr_hasRepY_q P 2 (by norm_num) (q := 2) (by simp) h2 Wq
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := mem_D.1 hD
  obtain ⟨a, ha, hArep, -⟩ := exists_isInYr_hasRepY_q P 2 (by norm_num) (q := 2) (by simp) h2 A
  obtain ⟨b, hb, hBrep, -⟩ := exists_isInYr_hasRepY_q P 2 (by norm_num) (q := 2) (by simp) h2 B
  refine ⟨Wf, hWin, hf, ?_, hweak, ⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩, ?_⟩
  · intro φ hφ
    rw [← phasePair_eq_pairF_of_hasRepY Wq Wf hWrep hφ.gradT]
    exact hWs φ hφ
  · exact (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => isPhaseTest_nuLapT hΦ ν) hWrep hArep).2 hA
  · exact (hasPtwOp_iff_hasPhaseOp (fun Φ hΦ => hΦ.driftT) hWrep hBrep).2 hB
  · intro Ψ hΨ
    have hT : IsPhaseTest P ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) :=
      (hΨ.1.const_smul _).add (isPhaseTest_L0 hΨ.1 ν)
    have hTeq : (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) =
        ((starRingEnd ℂ) (μ : ℂ) • Ψ + L0 ν Ψ) := by
      funext x
      simp [Complex.conj_ofReal, add_comm]
    rw [hTeq, ← phasePair_eq_pairF_of_hasRepY Wq Wf hWrep hT, hWeq Ψ hΨ.1,
      phasePair_eq_pairF_of_hasRepY Fq f hFrep hΨ.1]

end UnforcedLeray.Short.IIb
