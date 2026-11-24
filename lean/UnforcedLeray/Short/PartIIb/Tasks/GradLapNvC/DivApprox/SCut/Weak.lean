import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_2_1
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.EtaCut

/-!
# Part II-b, task `PartII-b:T09/2/1/1` (`DivSCutWeak`): weak Leibniz rule for the `s`-cut

Source of record: `the November 2 reference manuscript`, lines 1912-1918.
`DivEtaCutHelp.hasWeakVec_cut` with `χ(x) = sBump k x.1`: the commutator coefficient is
`cutD (vQ ε) χ = -2ε s χ'(s)` (only the `s`-coefficient of `vQ ε` meets `∂_s χ`) and
`cutD vEta χ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T09/2/1/1`.** -/
theorem divSCutWeak_proof : UnforcedLeray.Short.IIb.DivSCutWeak := by
  intro c r ε k b Qb Eb hc hr hk hb hwQ hwE
  have hχ : ContDiff ℝ ∞ (fun y : Coord => DriftSCutHelp.sBump k y.1) :=
    (DriftSCutHelp.sBump_smooth hk).comp contDiff_fst
  have hbd : ∃ C : ℝ, ∀ x : Coord, ‖(fun y : Coord => DriftSCutHelp.sBump k y.1) x‖ ≤ C :=
    ⟨1, fun x => by
      show ‖DriftSCutHelp.sBump k x.1‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (DriftSCutHelp.sBump_nonneg _ _)]
      exact DriftSCutHelp.sBump_le_one _ _⟩
  have hfd : ∀ x : Coord, HasFDerivAt (fun y : Coord => DriftSCutHelp.sBump k y.1)
      (deriv (DriftSCutHelp.sBump k) x.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x := fun x =>
    (((DriftSCutHelp.sBump_smooth hk).differentiable (by simp) x.1).hasDerivAt).comp_hasFDerivAt
      x hasFDerivAt_fst
  have hcQ : ∀ x : Coord,
      DivEtaCutHelp.cutD (vQ ε) (fun y : Coord => DriftSCutHelp.sBump k y.1) x =
        -2 * ε * (x.1 * deriv (DriftSCutHelp.sBump k) x.1) := by
    intro x
    simp [DivEtaCutHelp.cutD, cpd, (hfd x).fderiv, cdir, vQ, Fin.sum_univ_three]
    ring
  have hcE : ∀ x : Coord,
      DivEtaCutHelp.cutD vEta (fun y : Coord => DriftSCutHelp.sBump k y.1) x = 0 := by
    intro x
    simp [DivEtaCutHelp.cutD, cpd, (hfd x).fderiv, cdir, vEta, Fin.sum_univ_three]
  have hDcQ : Continuous (DivEtaCutHelp.cutD (vQ ε) (fun y : Coord => DriftSCutHelp.sBump k y.1)) := by
    rw [show DivEtaCutHelp.cutD (vQ ε) (fun y : Coord => DriftSCutHelp.sBump k y.1) =
      fun x => -2 * ε * (x.1 * deriv (DriftSCutHelp.sBump k) x.1) from funext hcQ]
    exact continuous_const.mul (DriftSCutHelp.sD_continuous hk)
  have hDcE : Continuous (DivEtaCutHelp.cutD vEta (fun y : Coord => DriftSCutHelp.sBump k y.1)) := by
    rw [show DivEtaCutHelp.cutD vEta (fun y : Coord => DriftSCutHelp.sBump k y.1) =
      fun _ => (0 : ℝ) from funext hcE]
    exact continuous_const
  have h1 := DivEtaCutHelp.hasWeakVec_cut hχ (DivEtaCutHelp.vQ_cd ε) hbd hDcQ hc hr hb hwQ
  have h2 := DivEtaCutHelp.hasWeakVec_cut hχ DivEtaCutHelp.vEta_cd hbd hDcE hc hr hb hwE
  have eQ : (fun x => ((DriftSCutHelp.sBump k x.1 : ℝ) : ℂ) • Qb x +
      ((DivEtaCutHelp.cutD (vQ ε) (fun y : Coord => DriftSCutHelp.sBump k y.1) x : ℝ) : ℂ) • b x) =
      sCutQ ε k b Qb := by
    funext x
    simp only [sCutQ, sCutB, sCutD, hcQ x]
  have eE : (fun x => ((DriftSCutHelp.sBump k x.1 : ℝ) : ℂ) • Eb x +
      ((DivEtaCutHelp.cutD vEta (fun y : Coord => DriftSCutHelp.sBump k y.1) x : ℝ) : ℂ) • b x) =
      sCutB k Eb := by
    funext x
    simp [sCutB, hcE x]
  refine ⟨?_, ?_⟩
  · rw [← eQ]
    exact h1
  · rw [← eE]
    exact h2

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSCutWeak_proof
