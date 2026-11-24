import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_4.TsumGrad
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_4.Termwise
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ret_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff

/-!
# `PartIII-b:C/ret/4`: `h^p_A = J ∇ψ^p_A` (source lines 4991-4994)

Assembles the two sub-lemmas `hpTermIdentity_proof` (termwise identity, source 4993) and
`hpTsumGrad_proof` (termwise differentiation of the lattice sum, source 4991) through
`hpIsJGrad_proof_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpIsJGrad_proof (ν : ℝ) (hν : 0<ν) (χ : ℝ → ℝ) (A : ℝ → Mat3) : HpIsJGrad ν χ A :=
  hpIsJGrad_proof_of ν hν (hpTermIdentity_proof ν) (hpTsumGrad_proof ν) χ A

end UnforcedLeray.Short.PartIIIb.Concrete
