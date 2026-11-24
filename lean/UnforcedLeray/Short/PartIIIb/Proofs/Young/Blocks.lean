import UnforcedLeray.Short.PartIIIb.Concrete.YoungBlocks
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Assembly
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Gronwall

/-!
# Retained block estimates, unconditional (source 4376-4411)

Combines the Gronwall step `blockGronwall_holds` (`Blocks/Gronwall.lean`) with the assembly
`blocksFromRetained_of_gronwall` (`Blocks/Assembly.lean`). Both are proved unconditionally, so
`BlocksFromRetained` and `BlocksFromTrain` hold for every package, residual and train input.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

open ConcreteYF

/-- The retained block estimates hold unconditionally (source 4396-4411). -/
theorem blocksFromRetained_holds (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ)
    (δ : ℕ → ℝ) : ConcreteYF.BlocksFromRetained pk ν lam κ Sg α δ :=
  blocksFromRetained_of_gronwall pk ν lam κ Sg α δ blockGronwall_holds

/-- The full chain from the train evolution holds unconditionally. -/
theorem blocksFromTrain_holds (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ)
    (δ : ℕ → ℝ) (m : ℝ)
    (tr : ∀ n, UnforcedLeray.B0140.TrainSol (ν n) (ν n ^ (-2 : ℝ)))
    (emb : ∀ n, (pk n).X → ℝ × ℝ → ℂ) :
    ConcreteYF.BlocksFromTrain pk ν lam κ Sg α δ m tr emb :=
  blocksFromTrain_of pk ν lam κ Sg α δ m tr emb (blocksFromRetained_holds pk ν lam κ Sg α δ)

end UnforcedLeray.Short.PartIIIb
