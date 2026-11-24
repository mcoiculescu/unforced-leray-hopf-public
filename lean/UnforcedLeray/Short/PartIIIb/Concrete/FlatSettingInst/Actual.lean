import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatForceCurl
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatForceLocal
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatForceDecay
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatXiRegular
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.KcPathEnergy
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatColumnVorticity
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.VorticityToVelocity
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.BodyColumnFlat

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem isFlatDuhamelColumn_actual (hPC : UnforcedLeray.Short.IIIa.PolyCausal)
    {P : UnforcedLeray.Blueprint.Planar.PlanarData}
    (hP : UnforcedLeray.Blueprint.Planar.IsPlanarReference P)
    {Kset : Set ℝ} (hK : IsCompact Kset) (hKs : Kset ⊆ Set.Ioo 0 (1 / 4)) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Set.Ioc 0 ν₀, ∀ (m : ℝ) [Fact (1 < m)] [Fact (0 < cOf ν)]
      (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels)
      (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ (D : FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε : ℝ) (hc : 0 < cOf ν),
        ∀ μ ∈ Kset, ∀ (as : ℝ) (χf : ℝ → ℝ),
          UnforcedLeray.Short.PartIIIb.NearInst.Kflat.IsFlatDuhamelColumn
            (actualFlatSetting D χo ε) hc tr μ as χf := by
  exact isFlatDuhamelColumn_of_leaves flatForceCurl flatForceLocal flatForceDecay flatXiRegular
    kcPathEnergy flatColumnVorticity vorticityToVelocity bodyColumnFlat hPC hP hK hKs

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
