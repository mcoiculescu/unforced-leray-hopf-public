import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.LjOld.Reduction
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtCongr

/-!
# `IsLjOld` for the source-class `𝓛` (source 4762-4796, 5800-5803)

Source of record: `the November 2 reference manuscript` (73 pages).

The map `𝓛` sees an old thin tensor only through `χ_o M` (source 4766-4796), and the old data of
`H T` depends only on `χ_o T` (source 5800-5803). The unconditional statement is obtained from the
reduction `isLjOld_of_xmtCongr` (`Concrete/PhysLayer/LjOld/Reduction.lean`) applied to the
congruence `xmtCongr` (`Concrete/SourceL/XmtCongr.lean`, task `PartIII-b:C/srcL/5`).

The conclusion is the body of `PhysLayer.IsLjOld B hχo`, written out, because
`Concrete/PhysLayer.lean` and `Concrete/SourceL.lean` both declare `Concrete.streamCut` and cannot be
imported together.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `𝓛` of a stress with `χ_o T = 0` vanishes, for every `𝓛`-pinned source (source 4762-4796,
5800-5803). -/
theorem isLjOld_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}
    {S : ConcreteYF.FlatSetting} {lam κ ell : ℂ} {J : ℂ → ℂ} {ε μ : ℝ} {χo χy χf : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (hι : Function.Injective ι) (hν : 0 < ν)
    (hL : IsSourceLPinned B ι S lam κ ell J ε μ χo χy χf) :
    ∀ T : StrG c mZ ρb γ ν, chiOStr c mZ ρb γ ν hχo T = 0 → B.Lj T = 0 :=
  isLjOld_of_xmtCongr B hχo hι hν hL xmtCongr

end UnforcedLeray.Short.PartIIIb.Concrete
