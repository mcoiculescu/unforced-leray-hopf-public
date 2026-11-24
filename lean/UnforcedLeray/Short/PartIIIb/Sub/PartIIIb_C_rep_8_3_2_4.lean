import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# `PartIII-b:C/rep/8/3/2/4`: `TrainGaussCell` from Part I `sct:fixed-band`

Source `the November 2 reference manuscript` 5484-5492, Part I 468-478.
Leaf 1 (`TrainPartICell`): Part I's `TrainFixedBand` at `ρ = 2`, `Sg = 11/10`, `m = 0`, `L = 0`,
`k = 2`, rewritten for a `ReturnLevel`.  Leaf 2 (`GaussCellFromPartI`): pointwise conversion plus
cell-integral bookkeeping.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Leaf 1** (source 468-478 at `ρ = 2`, `Sg = 11/10`, `m = 0`, `L = 0`, `k = 2`; transport of
`L.train : TrainSol ν (cOf ν)` to the period `trainPeriod 2 ν = ν^(-2)`, `cOf ν = (ν²)⁻¹`;
`sigmaJet ν 0 j F s = jet j (F s)`, `wCellL2 c 0 f = eLpNorm f 2 (cellμ c)`,
`‖jet 0 f z‖ = ‖f z‖`): there are `C, N, CS, bS, ν₀` such that for the BUC train of a level with
`ν ≤ ν₀` and `0 < s ≤ (11/10)/ν`, with `c = cOf ν`, `dv = v - V_c^p`, `dp = p - p_c^p`, the cell
`L²` norms of `‖dv‖`, `‖D²dv‖`, `‖∇_S dp‖` have sum `≤ C(1+c+ν⁻¹)^N e^{CS/ν - bS c²}`. -/
def TrainPartICell : Prop :=
  ∃ (C : ℝ) (N : ℕ) (CS bS ν₀ : ℝ), 0 < C ∧ 0 < bS ∧ 0 < ν₀ ∧
    ∀ L : ReturnLevel, UnforcedLeray.Short.PartI.IsBUCTrain L.train → L.ν ≤ ν₀ →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / L.ν →
        eLpNorm (fun x => ‖L.train.v s x - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s x‖) 2
            (UnforcedLeray.Cyl.cellμ (cOf L.ν)) +
          eLpNorm (fun x => ‖iteratedFDeriv ℝ 2
              (fun z => L.train.v s z - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s z) x‖) 2
            (UnforcedLeray.Cyl.cellμ (cOf L.ν)) +
          eLpNorm (fun x => ‖UnforcedLeray.Train.gradS
              (fun w => L.train.p s w - UnforcedLeray.Train.pc L.ν (cOf L.ν) s w) x‖) 2
            (UnforcedLeray.Cyl.cellμ (cOf L.ν)) ≤
        ENNReal.ofReal (C * (1 + cOf L.ν + L.ν⁻¹) ^ N *
          Real.exp (CS / L.ν - bS * cOf L.ν ^ 2))

/-- **Leaf 2**: from `TrainGaussPt` (`jet ≤ 4(a+b+c)`, so `jet² ≤ 48(a²+b²+c²)`) and
`TrainPartICell`: `∫⁻ ofReal(jet²) d avgμ ≤ ofReal((C ν^{-k} δ_base)²)`.  Bookkeeping:
`∫⁻ ofReal(a²) d cellμ = eLpNorm(a)² ` (`eLpNorm_eq_lintegral_rpow_enorm`), `lintegral_add`
(measurability: continuity of the slices), `avgμ c = ofReal c⁻¹ • cellμ c` with `c ≥ 1`,
`C(1+c+ν⁻¹)^N ≤ C 3^N (ν⁻¹)^{2N}` for `ν ≤ 1`, `exp(CS/ν - bS c²) = deltaBase CS bS ν`. -/
def GaussCellFromPartI : Prop :=
  TrainGaussPt → TrainSliceSmooth → TrainPartICell → TrainGaussCell

/-- `TrainGaussCell` from `TrainFixedBand` and `TrainGaussPt`. -/
theorem trainGaussCell_of_leaves (h1 : UnforcedLeray.Short.PartI.TrainFixedBand → TrainPartICell)
    (h2 : GaussCellFromPartI) (hS : TrainSliceSmooth)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) (hP : TrainGaussPt) : TrainGaussCell :=
  h2 hP hS (h1 hF)

end UnforcedLeray.Short.PartIIIb.Concrete

end
