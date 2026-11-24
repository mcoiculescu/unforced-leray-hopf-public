import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportIdentity

/-!
# Part I, task `PartI:T02/3/10`: the convective identity `EbConvIdentity`

Source of record: `the November 2 reference manuscript`, lines 276-282.

Target: `ebConvIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero → EbSliceSmooth →
EbConvIdentity` (`Short/PartI/Sub/T02_3_10.lean`, the leaf `EbConvIdentity`).

Mathematics. Fix `s ∈ [0, T]`, `R ≥ 1`, `v = v s`, `φ = etaCutoff R`. The statement
`ebConv c v R s = ebConvRhs c v R s` is
`-2 ∫_cell φ ⟨v, (v·∇)v⟩ = ∫_cell |v|² v₁ φ'`.  This is the transport identity of the train
analogue (`tp_core`, `Tasks/TrainCutoffEnergyProof/TransportIdentity.lean`) with the pair `(v, w)`
taken equal: `w = v` gives `bilinAdv v v = Train.advection v` definitionally.

Hypotheses used. `EtaCutoffFacts` gives the cutoff facts `φ' = 0` for `2R ≤ |η|` and `φ = 0` there;
`IsClassicalOn` gives smoothness, `c`-periodicity and the divergence-free condition of `v(s)`;
`EbSliceSmooth` gives `C^∞` of the slice; `CellIntegrableOfSupport` and `CellDerivZero` are the
cell toolkit leaves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- **`PartI:T02/3/10`, leaf `EbConvIdentity`.** Uses the cutoff facts (`EtaCutoffFacts`), the two
cell toolkit leaves (`CellIntegrableOfSupport`, `CellDerivZero`) and the slice smoothness
(`EbSliceSmooth`), as black boxes. -/
theorem ebConvIdentity : EtaCutoffFacts → CellIntegrableOfSupport → CellDerivZero →
    EbSliceSmooth → EbConvIdentity := by
  intro hη hI hZ hS ν c T v p hc hcl R hR1 s hs
  obtain ⟨C₀, _hC₀, hcut⟩ := hη
  have hR : 0 < R := by linarith
  obtain ⟨hφ, _, _, hφ0, hφ'⟩ := hcut R hR1
  have hφ1 : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    have h1 := hφ' η
    rw [hφ0 η hη, Real.sqrt_zero, mul_zero, abs_nonpos_iff] at h1
    exact h1
  have hvS : ContDiff ℝ ∞ (v s) := (hS ν c T v p hcl s hs).1
  have hvp : Cyl.IsPeriodic c (v s) := hcl.periodic_v s hs
  have hdiv : ∀ z : Plane, Cyl.divergence (v s) z = 0 := fun z => hcl.solenoidal s hs z
  have hcore := tp_core c R hc hR (etaCutoff R) hφ hφ0 hφ1 (v s) (v s) hvS hvS
    hvp hvp hdiv hI hZ
  unfold ebConv ebConvRhs
  exact hcore

end UnforcedLeray.Short.PartI
