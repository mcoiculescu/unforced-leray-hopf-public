import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2` (`VelJetLocalLate`): decomposition

Source: `the November 2 reference manuscript` lines 261-288 (finite-energy
solution, energy identities on each finite interval, Gronwall continuation of `L²` membership).

`VelJetLocalLate` follows from the single uniform leaf `VelJetUniformL2`: a bound on `L²(cell)`
norms of all word derivatives of `v(r)`, uniform on `0 ≤ r ≤ S`, with no age condition. At age
`s` take `S = 2 s` and `ε = s / 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartI

/-- Leaf: uniform-in-time `L²(cell)` bound on word derivatives of the BUC train velocity on every
finite interval `[0, S]` (lines 261-288: the datum is in `H^k` for all `k`, energy inequality for
`∂_w v` with cutoffs, Gronwall on `[0, S]`). No age condition. -/
def VelJetUniformL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ S : ℝ, 0 < S → ∀ (w : List Bool) (k : Fin 2),
      ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ S →
        MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2 ≤ B

/-- `VelJetLocalLate` from the uniform leaf. -/
theorem velJetLocalLate_of (h : VelJetUniformL2) : VelJetLocalLate := by
  intro ν c hν hc tr htr s hs _ w k
  obtain ⟨B, hB⟩ := h ν c hν hc tr htr (2 * s) (by linarith) w k
  refine ⟨s / 2, by linarith, B, fun r hr hrs => ?_⟩
  have h1 := (abs_lt.mp hrs)
  exact hB r hr.le (by linarith [h1.2])

end UnforcedLeray.Short.PartI
