import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8
import UnforcedLeray.Short.PartIIa.ComposeFree
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound

/-!
# No hidden null space on the solenoidal sector (source 1393-1400, 1409-1412, 1358-1359)

Task `PartIII-b:C/ward/12/3/1/2/8/2` (Sub file, decomposed).  Source of record
`the November 2 reference manuscript`.

Decomposition.  The step that turns "`⟪L₀ᵗΦ, v⟫ = 0` for solenoidal tests `Φ`" into the same
identity for every phase test is the analytic content of this task.  It is isolated as the
Prop `L0TSolExtension`.  Everything after it is proved here from compiled library results:
`v` is then a distributional solution of `L₀v = 0` with `v ∈ Y_{q₀}`, so `v ∈ D` by
`commonBodyMaximalDomain` (μ = 0, f = 0), `L₀v = L₀D v = 0` (`L0D_eq`), and injectivity of
`μ + L` on `D` (`bodyOp_injective_of_bound`, `commonBodyGraphBound`) forces `v = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (IsSolTest)

/-- **Extension of the adjoint identity from solenoidal to all phase tests** (the analytic step,
source 1393-1400, 1409-1412). For `v ∈ Y_{q₀}` solenoidal with `⟪L₀ᵗΦ, v⟫ = 0` for all solenoidal

identity `⟪𝔓Φ, v⟫ = ⟪Φ, v⟫` for solenoidal `v` (`phasePair_lerayProjected_eq_of_phaseSolenoidal`)
and solenoidal approximants of `𝔓Φ` (`SolTestApprox`, reduced to curl cutoffs), but the
approximants are needed in the graph sense, `L₀ᵗΨₙ → L₀ᵗ𝔓Φ`, which is not in the library. -/
def L0TSolExtension : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ v : Yq P UnforcedLeray.B0412.q0E,
    v ∈ Ysigma P UnforcedLeray.B0412.q0E →
    (∀ Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3, IsSolTest P Φ →
      phasePair P UnforcedLeray.B0412.q0E (L0T ν Φ) v = 0) →
    ∀ Φ : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3, IsPhaseTest P Φ →
      phasePair P UnforcedLeray.B0412.q0E (L0T ν Φ) v = 0

/-- **Uniqueness on the solenoidal sector**, conditional on `L0TSolExtension`. -/
theorem gEBodyUniqueSol_of (hext : L0TSolExtension) : GEBodyUniqueSol := by
  intro P ν _ hP1 hν v hvσ hsol
  have hall := hext P ν hν v hvσ hsol
  have hL0 : HasPhaseOp (L0T ν) v 0 := fun Φ hΦ => by
    rw [map_zero]
    exact hall Φ hΦ
  have hH : HasPhaseOp (fun Φ => (0 : ℂ) • Φ + L0T ν Φ) v 0 := fun Φ hΦ => by
    show phasePair P UnforcedLeray.B0412.q0E (0 • Φ + L0T ν Φ) v =
      phasePair P UnforcedLeray.B0412.q0E Φ 0
    rw [zero_smul, zero_add, map_zero]
    exact hall Φ hΦ
  have hD : v ∈ D P ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.Short.PartIIa.commonBodyMaximalDomain UnforcedLeray.B0412.q0E
      UnforcedLeray.B0412.one_lt_q0E UnforcedLeray.B0412.q0E_lt_three P hP1 ν hν 0
      (by simpa using gammaR_q0E_pos) v 0 hH
  have hz : L0L (⟨v, hD⟩ : D P ν UnforcedLeray.B0412.q0E) = 0 := L0D_eq hL0
  have hb : UnforcedLeray.Short.PartIIa.bodyOp P ν UnforcedLeray.B0412.q0E 0
      (⟨v, hD⟩ : D P ν UnforcedLeray.B0412.q0E) = 0 := by
    rw [UnforcedLeray.Short.PartIIa.bodyOp, LinearMap.add_apply, LinearMap.smul_apply, zero_smul,
      zero_add]
    exact hz
  have hinj := UnforcedLeray.Short.PartIIa.bodyOp_injective_of_bound
    UnforcedLeray.Short.PartIIa.commonBodyGraphBound UnforcedLeray.B0412.q0E
    UnforcedLeray.B0412.one_lt_q0E UnforcedLeray.B0412.q0E_lt_three P hP1 ν hν 0
    (by simpa using gammaR_q0E_pos)
  have h0 : (⟨v, hD⟩ : D P ν UnforcedLeray.B0412.q0E) = 0 :=
    hinj (hb.trans (map_zero (UnforcedLeray.Short.PartIIa.bodyOp P ν
      UnforcedLeray.B0412.q0E 0)).symm)
  simpa using congrArg Subtype.val h0

end UnforcedLeray.Short.PartIIIb.Concrete
