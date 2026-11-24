import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise.DivEpsRealLeaf

/-!
# `PartIII-b:C/near/pins/5/2/1`: reality of `div_ε` of a real tensor test

Source `the November 2 reference manuscript` 1660-1665 (`div_ε`) and 1650
(`Q_ε = ∂_q - ε(K+1)`, `K = 2S + η∂_η`).

For a smooth tensor test `M` whose components `tv4 (M x)` are real, the components of
`divEps ε (tv4 ∘ M)` have zero imaginary part.  The leaves `pdQOfRealLeaf`, `pdSOfRealLeaf`,
`pdEtaOfRealLeaf` of `DivEpsRealLeaf` identify the complex partial derivatives of a complexified
real function with the complexified real partial derivatives, and `compSmoothLeaf` gives the
smoothness and the real parts of the components.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem swDivEpsReal : SWDivEpsReal := by
  intro c ε M hM x i
  have hc := compSmoothLeaf c M hM
  obtain ⟨hA1, -⟩ := hc (cmpA M) (by simp)
  obtain ⟨hB1, -⟩ := hc (cmpB M) (by simp)
  obtain ⟨hC1, -⟩ := hc (cmpC M) (by simp)
  obtain ⟨hD1, -⟩ := hc (cmpD M) (by simp)
  have dA : DifferentiableAt ℝ (cmpA M) x := (hA1.differentiable (by simp)) x
  have dB : DifferentiableAt ℝ (cmpB M) x := (hB1.differentiable (by simp)) x
  have dC : DifferentiableAt ℝ (cmpC M) x := (hC1.differentiable (by simp)) x
  have tA : ∀ y : Chart, tv4 (M y) 0 = ((cmpA M y : ℝ) : ℂ) := fun y => by
    simp [tv4, cmpA]
  have tB : ∀ y : Chart, tv4 (M y) 1 = ((cmpB M y : ℝ) : ℂ) := fun y => by
    simp [tv4, cmpB]
  have tC : ∀ y : Chart, tv4 (M y) 2 = ((cmpC M y : ℝ) : ℂ) := fun y => by
    simp [tv4, cmpC]
  have tD : ∀ y : Chart, tv4 (M y) 3 = ((cmpD M y : ℝ) : ℂ) := fun y => by
    simp [tv4, cmpD]
  have qA := pdQOfRealLeaf dA
  have sA := pdSOfRealLeaf dA
  have eA := pdEtaOfRealLeaf dA
  have qB := pdQOfRealLeaf dB
  have sB := pdSOfRealLeaf dB
  have eB := pdEtaOfRealLeaf dB
  have eC := pdEtaOfRealLeaf dC
  fin_cases i
  · simp only [UnforcedLeray.Short.PartIIa.divEps, UnforcedLeray.Short.PartIIa.opQ,
      UnforcedLeray.Short.PartIIa.opK, UnforcedLeray.Short.PartIIa.opS, tA, tB, tC, tD,
      qA, sA, eA, qB, sB, eB, eC, PiLp.smul_apply, smul_eq_mul, Complex.real_smul,
      PiLp.toLp_apply, Fin.isValue]
    simp
  · simp only [UnforcedLeray.Short.PartIIa.divEps, UnforcedLeray.Short.PartIIa.opQ,
      UnforcedLeray.Short.PartIIa.opK, UnforcedLeray.Short.PartIIa.opS, tA, tB, tC, tD,
      qA, sA, eA, qB, sB, eB, eC, PiLp.smul_apply, smul_eq_mul, Complex.real_smul,
      PiLp.toLp_apply, Fin.isValue]
    simp

end UnforcedLeray.Short.PartIIIb.NearInst
