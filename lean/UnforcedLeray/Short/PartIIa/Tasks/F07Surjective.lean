import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain
import UnforcedLeray.Units.B0411

/-!
# Part II-a, task `PartII-a:F07`: surjectivity of `μ + L : D_r → Y_r`

Source of record: `the November 2 reference manuscript`, lines 1363-1370 and
1424-1431. For `f ∈ Y_r` put `w = R_μ f` (`PartII-a:F01`). By `PartII-a:F02` the distribution
`(μ + L₀) w` equals `f`; by `PartII-a:F04` (maximal domain) `w ∈ D_r`. Then `L₀ w` is the unique
distributional representative of `L₀ w` (`B0411.L0D_eq`), so `bodyOp w = μ w + L₀ w = f`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **`PartII-a:F07`**: `μ + L : D_r → Y_r` is surjective (`CommonBodySurjective`). -/
theorem commonBodySurjective : CommonBodySurjective := by
  intro r hr h1 h3 P hP hPle ν hν μ hμ f
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists r h1 h3 P ν hν μ hμ
  have hsol : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (Rm f) f :=
    bodyResolvent_solves r h1 h3 P ν hν μ hμ Rm hRm f
  have hmem : Rm f ∈ D P ν r :=
    commonBodyMaximalDomain r h1 h3 P hPle ν hν μ hμ (Rm f) f hsol
  -- the distributional identity `L₀ (R_μ f) = f - μ R_μ f`
  have hL0 : HasPhaseOp (L0T ν) (Rm f) (f - μ • Rm f) := by
    intro Φ hΦ
    have h := hsol Φ hΦ
    simp only at h
    rw [phasePair_add (hΦ.const_smul μ) (isPhaseTest_L0T hΦ ν),
      phasePair_const_smul hΦ] at h
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination h
  refine ⟨⟨Rm f, hmem⟩, ?_⟩
  have hw : L0D (⟨Rm f, hmem⟩ : D P ν r) = f - μ • Rm f := L0D_eq hL0
  simp only [bodyOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_subtype,
    L0L_apply]
  rw [hw]
  abel

end UnforcedLeray.Short.PartIIa
