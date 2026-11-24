import UnforcedLeray.Short.PartIIa.Sub.F14_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F14_1_3

/-!
# Part II-a, `PartII-a:F14/1/3`: the solution of `(μ+L)w = 𝐏 f` at `r = 2` is solenoidal

Source `the November 2 reference manuscript` lines 1358-1359, 1480-1481.
`w = R_μ 𝐏 f`; `𝐏` commutes with `R_μ` (`lerayYResolventComm`, from `lerayCFreeComm`,
`lerayYPhaseTComm` in `Sub/PartIIa_F14_1_3.lean`), so `𝐏 w = w`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

theorem solenoidalBodySolution : SolenoidalBodySolution := by
  intro P _ hP ν hν μ hμ f
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ2 : 0 < μ.re + gammaR 2 := by
    have : gammaR 2 = 1 / 4 := by
      simp only [gammaR, ENNReal.toReal_ofNat]; norm_num
    rw [this]; exact hμ
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 ENNReal.one_lt_two h3 P ν hν μ hμ2
  set g : Yq P 2 := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f with hg
  have hsol : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (Rm g) g :=
    bodyResolvent_solves 2 ENNReal.one_lt_two h3 P ν hν μ hμ2 Rm hRm g
  have hmem : Rm g ∈ D P ν 2 :=
    commonBodyMaximalDomain 2 ENNReal.one_lt_two h3 P hP ν hν μ hμ2 (Rm g) g hsol
  have hL0 : HasPhaseOp (L0T ν) (Rm g) (g - μ • Rm g) := by
    intro Φ hΦ
    have h := hsol Φ hΦ
    simp only at h
    rw [phasePair_add (hΦ.const_smul μ) (isPhaseTest_L0T hΦ ν),
      phasePair_const_smul hΦ] at h
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination h
  have hcomm : lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (Rm f) =
      Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f) :=
    lerayYResolventComm 2 ENNReal.one_lt_two h3 P ν hν μ hμ2 Rm hRm f
  have hsolY : Rm g ∈ B0414.solenoidalY P := by
    rw [hg, ← hcomm]
    exact B0414.lerayY_two_mem _
  refine ⟨⟨Rm g, hmem⟩, hsolY, ?_⟩
  have hw : L0D (⟨Rm g, hmem⟩ : D P ν 2) = g - μ • Rm g := L0D_eq hL0
  simp only [bodyOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_subtype,
    L0L_apply]
  rw [hw]
  abel

end UnforcedLeray.Short.PartIIa
