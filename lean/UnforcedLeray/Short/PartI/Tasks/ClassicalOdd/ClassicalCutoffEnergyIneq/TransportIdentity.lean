import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportIdentity

/-!
# Part I, task `PartI:T02/3/11`: `ccTransportIdentity` (leaf `CcTransportIdentity`)

Source of record: `the November 2 reference manuscript`, lines 276-288.
Target: `ccTransportIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero →
CcSliceSmooth → CcTransportIdentity` (the Prop `CcTransportIdentity` in `Short/PartI/Sub/T02_3_11.lean`,
line 230).

Route. This is the classical analogue of `transportIdentity`
(`Tasks/TrainCutoffEnergyProof/TransportIdentity.lean`). Fix `s ∈ [0, T]`, `R ≥ 1`, `φ = etaCutoff R`,
and let `w = ccDiffV v v' s = v s - v' s`. The core computation `tp_core` (imported) gives
`-2 ∫_cell φ ⟨w, (v·∇)w⟩ = ∫_cell |w|² v₁ φ'` for a smooth, `c`-periodic, divergence-free `v` and a
smooth periodic `w`, using `CellIntegrableOfSupport` and `CellDerivZero`. Here `v = v s`, which is
divergence-free on `[0, T]` by `IsClassicalOn.solenoidal`, and `w` is smooth and periodic since both
`v s` and `v' s` are (`CcSliceSmooth`, `IsClassicalOn.periodic_v`).

The cutoff facts give `φ' = 0` on `2R ≤ |η|`, from `|φ'| ≤ (C₀/R) √φ` and `φ = 0` there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **Leaf `CcTransportIdentity`**: `T_trans = ∫_cell |w|² v₁ φ'` for the difference
`w = v s - v' s` of two classical solutions, from the transport computation `tp_core` on `v s`. -/
theorem ccTransportIdentity (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport) (hZ : CellDerivZero)
    (hS : CcSliceSmooth) : CcTransportIdentity := by
  intro ν c T M v v' p p' h R hR1 s hs
  obtain ⟨_C₀, -, hcut⟩ := hη
  obtain ⟨hφ, -, -, hφ0, hφ'⟩ := hcut R hR1
  have hc : 0 < c := by linarith [h.c_ge]
  have hR : 0 < R := by linarith
  have hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη'
    have h1 := hφ' η
    rw [hφ0 η hη', Real.sqrt_zero, mul_zero, abs_nonpos_iff] at h1
    exact h1
  -- smoothness, periodicity and solenoidality of `v s` and of `w = v s - v' s`
  have hvS : ContDiff ℝ ∞ (v s) := (hS ν c T v p h.cl s hs).1
  have hv'S : ContDiff ℝ ∞ (v' s) := (hS ν c T v' p' h.cl' s hs).1
  have hwS : ContDiff ℝ ∞ (ccDiffV v v' s) := hvS.sub hv'S
  have hvp : Cyl.IsPeriodic c (v s) := h.cl.periodic_v s hs
  have hv'p : Cyl.IsPeriodic c (v' s) := h.cl'.periodic_v s hs
  have hwp : Cyl.IsPeriodic c (ccDiffV v v' s) := by
    intro z
    show v s (z.1 + c, z.2) - v' s (z.1 + c, z.2) = v s z - v' s z
    rw [hvp z, hv'p z]
  have hdiv : ∀ z : Plane, Cyl.divergence (v s) z = 0 := fun z => h.cl.solenoidal s hs z
  have hcore := tp_core c R hc hR (etaCutoff R) hφ hφ0 hφ1 (v s) (ccDiffV v v' s) hvS hwS
    hvp hwp hdiv hI hZ
  unfold ccTransport ccTransportRhs
  exact hcore

end UnforcedLeray.Short.PartI
