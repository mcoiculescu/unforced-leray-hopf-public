import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Leaves

/-!
# `PartIII-b:C/rep/4/1/org/3/org` (leaves): the thin-to-repair kernel and the thin source lift

Source `the November 2 reference manuscript` 5336-5338 ("the thin-to-repair entry
uses the order-four kernel from `L²` to `L^{22/3}`, with off-diagonal norm `D^{-23/11}`, followed
by `√ρ`"), 3624-3646 (`sep:young`), 5303-5306 (far mask `s < S`, `t > e^δs`, `S = ε^{-b}`),
2683-2689 (lifts `𝒩_TT = sT`, `‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`), 2697 (`Z₁`).

The two analytic leaves of `farLateThinRep_of` (`Props.lean`); they import only the shared
far-kernel file `YRepStream/LateRepRep/SepKernel/Leaves.lean` (where the `p = 22/19` twin
`FarVelYoungBox`, the pointwise majorant `FarVelPointwise` and the receiver conversion
`RepRecvConv` are stated).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(B) The order-four separated kernel `L² → L^{22/3}` on the far mask** (source 5336-5338:
"the thin-to-repair entry uses the order-four kernel from `L²` to `L^{22/3}`, with off-diagonal
norm `D^{-23/11}`"; `sep:young` 3624-3646 with `j = 0`, `p = 2`, `q = 22/3`, `b = 11/7`,
`1 + 3/22 = 1/2 + 7/11`, `-4 + 3/b = -23/11`, `2μ + 3/2 > 1` for `μ > -1/4`; far mask 5303-5306,
3902-3912): there is an absolute `C` such that for `ε, c, ν, δ, S > 0`, `μ > -1/4`, every box
tensor `f` and every measurable `b` a.e. equal to the far output `farOut f` (the exact kernel
realization of `S_far`, `IsFarMaskG`),
`‖𝒩_vb‖_{L²_τL^{22/3}} ≤ C(1-e^{-δ/2})^{-23/11}ε^{23/11}S^{23/22}‖𝒩_Tf‖_{L²_τL²}`
(`= C D₀^{-23/11}‖·‖`, `D₀ = (1-e^{-δ/2})ε⁻¹S^{-1/2}`), period `P = 2εc`.  The `p = 2` twin of
`FarVelYoungBox`: from `FarVelPointwise`, `dilMaj μ d = IIIa.sepDom (2μ+2) 0 d`,
`IIIa.sepDomYoung` (proved), `srcNorm (cartLift f) = gAx` off the null axis. -/
def FarVelYoungBoxL2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε c ν δ S μ : ℝ), 0 < ε → 0 < c → 0 < ν → 0 < δ → 0 < S →
    -(1 / 4) < μ → ∀ f : Chart → Ten3, NearInst.IsBoxTensor f →
      ∀ b : Chart → Merid, Measurable b →
        b =ᵐ[ageμ c (-3 / 2)] NearInst.Masked.farOut ε⁻¹ c ν μ δ S f →
        UnforcedLeray.Short.IIIa.ltauLq (2 * ε * c) (22 / 3)
            (fun τ y => ‖velPhys ε⁻¹ c b (τ, y)‖ₑ) ≤
          ENNReal.ofReal (C * (1 - Real.exp (-δ / 2)) ^ (-(23 / 11 : ℝ)) *
              ε ^ (23 / 11 : ℝ) * S ^ (23 / 22 : ℝ)) *
            phaseL2Lr (2 * ε * c) 2 (strPhys ε⁻¹ c f)

/-- **The thin source lift** (source 2683-2689: `‖𝒩_TT‖²_{Y₂} = πR²‖T‖²_{H_T}`, `𝒩_TT = sT`;
2697: `Z₁ = L²(W²s^{-1/2}dς)`, `W = ⟨η/√(1+s)⟩^{m_Z} ≥ 1`): for `ε, c > 0`, `m_Z ≥ 0` and
measurable `f`, `‖𝒩_Tf‖_{L²_τL²} ≤ √π ε⁻¹ ‖f‖_{Z₁}` (period `P = 2εc`, `R = ε⁻¹`; the lift keeps
the symmetric no-swirl part `nsSym f`, `|nsSym f| ≤ |f|`). -/
def ThinLiftZ1 : Prop :=
  ∀ (ε c mZ : ℝ), 0 < ε → 0 < c → 0 ≤ mZ → ∀ f : Chart → Ten3, Measurable f →
    phaseL2Lr (2 * ε * c) 2 (strPhys ε⁻¹ c f) ≤
      ENNReal.ofReal (Real.sqrt Real.pi * ε⁻¹) * z1Ung c mZ f

end UnforcedLeray.Short.PartIIIb.Concrete
