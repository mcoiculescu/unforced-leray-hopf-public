import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Sub-lemmas for `PartIII-b:C/ret/4` (`h^p_A = J ∇ψ^p_A`, source lines 4991-4994)

Two true source facts: the termwise identity `[V_j, B x_j] = J ∇[(tr B)ψ_j - (B x_j)·∇ψ_j]`
(line 4993, algebra with the Gaussian `V_j = J∇ψ_j`), and the termwise differentiation of the
Gaussian lattice sum (line 4991, Gaussian decay locally uniformly in `x`).
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `j`-th summand of `ψ^p` for a matrix `B`. -/
def gjPsi (ν s : ℝ) (B : Mat3) (j : ℤ) (y : ℝ × ℝ) : ℝ :=
  merTrace B * psij ν s j y - fderiv ℝ (psij ν s j) y (merApply B (xj ν j y))

/-- Termwise identity (source 4993): `[V_j, B x_j] = J ∇ [(tr B) ψ_j - (B x_j)·∇ψ_j]`.
Pure algebra: `V_j = J∇ψ_j`, `D(B x_j) = B`, symmetry of `D²ψ_j`, and `B_mer J = J[(tr B) - Bᵀ]`. -/
def HpTermIdentity (ν : ℝ) : Prop :=
  ∀ (s : ℝ) (j : ℤ) (B : Mat3) (x : ℝ × ℝ),
    merApply B (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))
      = Jrot (mgrad (gjPsi ν s B j) x)

/-- Termwise differentiation of the Gaussian lattice sum (source 4991): the series of gradients
converges and is the gradient of the sum; source `ν > 0` (`a = 1 + νs > 0`, `c = ν⁻²`),
false for `ν ≤ 0`. -/
def HpTsumGrad (ν : ℝ) : Prop :=
  0 < ν → ∀ (s : ℝ), 0 < s → ∀ (B : Mat3) (x : ℝ × ℝ),
    Summable (fun j : ℤ => mgrad (gjPsi ν s B j) x) ∧
      mgrad (fun y => ∑' j : ℤ, gjPsi ν s B j y) x = ∑' j : ℤ, mgrad (gjPsi ν s B j) x

/-- `J` as a continuous linear map. -/
def JlinCLM : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

lemma JlinCLM_apply (x : ℝ × ℝ) : JlinCLM x = Jrot x := by
  simp [JlinCLM, Jrot]

theorem hpIsJGrad_proof_of (ν : ℝ) (hν : 0 < ν) (h1 : HpTermIdentity ν) (h2 : HpTsumGrad ν)
    (χ : ℝ → ℝ) (A : ℝ → Mat3) : HpIsJGrad ν χ A := by
  refine ⟨hν, ?_⟩
  intro s hs x
  obtain ⟨hsum, heq⟩ := h2 hν s hs (Ay ν χ A s) x
  have hpsi : psipA ν χ A s = fun y => ∑' j : ℤ, gjPsi ν s (Ay ν χ A s) j y := rfl
  rw [hpsi, heq]
  have hterm : hpA ν χ A s x = ∑' j : ℤ, Jrot (mgrad (gjPsi ν s (Ay ν χ A s) j) x) := by
    unfold hpA
    exact tsum_congr (fun j => h1 s j (Ay ν χ A s) x)
  rw [hterm]
  have := ContinuousLinearMap.map_tsum JlinCLM hsum
  simpa [JlinCLM_apply] using this.symm

end UnforcedLeray.Short.PartIIIb.Concrete
