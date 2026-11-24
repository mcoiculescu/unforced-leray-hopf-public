import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Kflat

/-!
# The train evolution at old ages: kinetic bound and old absolute stress (source 2819-2860,
# 3020-3022, 3233-3289, 4432-4458, 4677-4694)

Source of record: `the November 2 reference manuscript` (73 pages).

Part of `PartIII-b:C/asrc/kflat/1/org`.  The old moment `N₀(𝔗A)` of the flat return
(`FrakTOldFinite`, `FrakTN0Bound` of `Kflat.lean`) is the absolute stress functional of the train
evolution started at the end `T = 1.1/ν` of the source band: for `u ≥ T` the Duhamel state is
`ξ_B(u) = (T/u)^μ 𝒰(u,T)ξ_B(T)` (`g_B = 0` above `1.1/ν`, cocycle).  The source bounds this
functional only

* for `ν` small: `prop:short-full-clock` (2836-2860) holds "for all sufficiently small `ν`" and on
  `0 < t < s ≤ H = ν⁻¹((νb)⁻¹ - 1)` only, with the exponential relative weight
  `g(s) = exp(γs/(1+νs))` and the polynomial loss `ν^{-M_s}` (3025-3100);
* beyond `H` not through an operator bound on `X_{m,c}` (the weighted norm of the heat-like flow
  grows polynomially in the age, `eq:short-causal-scales` 3031-3036) but through the velocity
  energy: the long-clock bound `eq:short-causal-long-forward` (3020-3022) carries a state at `H`
  to the clock `b` (4440-4446), the kinetic impulse estimate `eq:ct-kinetic-impulse` (3242-3251)
  and the embedding `‖K_d f‖₂ ≤ C_m‖f‖_{X_{m,d}}` (`eq:ct-embeddings`, 3228-3240) bound the
  velocity, and `eq:ct-absolute-impulse` (3277-3289, train energy `‖v‖₂ ≤ Cνθ`) bounds the absolute
  stress;
* for the actual train: the BUC train of `sct:train` (270-288), `PartI.IsBUCTrain`; the train
  estimates used (`sct:integrated`, the train energy bounds) do not follow from `B0140.IsTrain`
  (see `Short/PartI/TrainClass.lean`), and `X_{m,c}` has `m > 8` (2826, 4350).

A uniform bound `‖𝒰(s,t)‖ ≤ C` for all `0 ≤ t ≤ s` is not a source statement (and fails for the
heat part of the flow in `X_{m,c}`, `m > 5/2`); it is not used.

* `TrainFlowKinetic` (source leaf): the velocity of the train evolution from age `T = 1.1/ν` is
  bounded in `L²(cell)` by `C‖w‖_{X_{m,c}}` at every later age;
* `TrainEnergyUnif`: the train energy `‖v(s)‖_{L²(cell)}` is bounded uniformly in the age, for
  small `ν` and BUC trains (`sct:integrated`, source 314-322; from `PartI.TrainL2Decay`);
* `SymOuterSliceProp`: Cauchy-Schwarz on one cell for the readout,
  `c⁻¹∫_cell |v ⊗ b + b ⊗ v| ≤ 2c⁻¹‖v‖_{L²(cell)}‖b‖_{L²(cell)}` (source 3283-3287);
* `TrainOldStressBound`: the old absolute stress functional of the evolution from `T`,
  `∫_{1.2/ν}^∞ u^{-3/2} c⁻¹∫_cell |v ⊗ K_c𝒰(u,T)w + K_c𝒰(u,T)w ⊗ v| ≤ C‖w‖`; it follows from the
  three above (`∫_{1.2/ν}^∞ u^{-3/2} du < ∞`; task `PartIII-b:C/asrc/kflat/1/2/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- **Kinetic bound of the train evolution from the end of the source band** (source 2836-2860,
3020-3022, 3233-3251, 4440-4446): for `m > 8` there is `ν₀ > 0` such that for `0 < ν ≤ ν₀`, every
BUC train `tr` at `c = ν⁻²` and its evolution `𝒰 = FI.ev.U` (the weak linearised flow,
`TrainEvolution.flow`) there is `C` with `‖K_c 𝒰(u, 1.1/ν)w‖_{L²(cell)} ≤ C‖w‖_{X_{m,c}}` for all
`u ≥ 1.1/ν` and `w ∈ X_{m,c}`.  On `1.1/ν ≤ u ≤ H` this is the full forward estimate with the
embedding `K_c : X_{m,c} → L²`; beyond `H` the physical kinetic norm of the flow is carried with
constant `C_b` by the velocity energy inequality and the integrated strain (3242-3251: "the input
physical kinetic norm is `νr‖K_{d(r)}h‖₂` and the integrated strain costs at most `C(r+e)`"). -/
def TrainFlowKinetic (m : ℝ) [Fact (1 < m)] : Prop :=
  8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν : ℝ) (hν : 0 < ν), ν ≤ ν₀ →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatInstData κ ν (cOf ν) m tr),
      haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
      ∃ C : ℝ, ∀ u : ℝ, 11 / 10 / ν ≤ u → ∀ w : Xmc (cOf ν) m,
        ‖kcLp (FI.ev.U u (11 / 10 / ν) w)‖ ≤ C * ‖w‖

/-- **Uniform train energy** (source 314-322, `sct:integrated`: `‖v(s)‖₂ ≤ Ca(s)⁻¹` for `s ≤ s_c`,
`‖v(s)‖₂ ≤ Cc⁻²(s/s_c)^{-3/4}` for `s ≥ s_c`, on one unnormalized cell, for `ν` small; the BUC
train of 270-288): there are `ν₀ > 0` and `E` with `‖v(s)‖_{L²(cell)} ≤ E` for `0 < ν ≤ ν₀`, every
BUC train at `c = ν⁻²` and every age `s ≥ 0`. -/
def TrainEnergyUnif : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∃ E : ℝ, ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) ≤ ENNReal.ofReal E

/-- **Cauchy-Schwarz on one cell for the stress readout** (source 3283-3287, 4610-4612):
`∫ |v(u) ⊗ K_c y + K_c y ⊗ v(u)| dq/c dη ≤ 2c⁻¹ ‖v(u)‖_{L²(cell)} ‖K_c y‖_{L²(cell)}` for the train
velocity `v` (read through `trainMer`) and `y ∈ X_{m,c}` (`K_c y` read through its Lebesgue value
`kcMer`, equal to `kcLp y` a.e. on the cell). -/
def SymOuterSliceProp (m : ℝ) [Fact (1 < m)] : Prop :=
  ∀ (ν : ℝ) (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)),
    haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
    ∀ (u : ℝ) (y : Xmc (cOf ν) m),
      ∫⁻ x, ENNReal.ofReal (frob (UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
          (kcMer y x))) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤
        2 * ENNReal.ofReal (cOf ν)⁻¹ * UnforcedLeray.Train.cellL2 (cOf ν) (tr.v u) *
          ENNReal.ofReal ‖kcLp y‖

/-- **The old absolute stress of the train evolution from the end of the source band** (source
4677-4694 with 3277-3289, 4432-4458, 4855-4857): for `m > 8` there is `ν₀ > 0` such that for
`0 < ν ≤ ν₀`, every BUC train `tr` at `c = ν⁻²` and its evolution `𝒰 = FI.ev.U` there is `C` with
`∫_{u > 1.2/ν} u^{-3/2} ∫ |v(u) ⊗ K_c𝒰(u,1.1/ν)w + K_c𝒰(u,1.1/ν)w ⊗ v(u)| dq/c dη du ≤ C‖w‖`
for every `w ∈ X_{m,c}` (`symOuter` is the stress readout `v ⊗ b + b ⊗ v` of 4610-4612, `frob` its
Frobenius norm, `kcMer` the Lebesgue value of `K_c`). -/
def TrainOldStressBound (m : ℝ) [Fact (1 < m)] : Prop :=
  8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν : ℝ) (hν : 0 < ν), ν ≤ ν₀ →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatInstData κ ν (cOf ν) m tr),
      haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
      ∃ C : ℝ, ∀ w : Xmc (cOf ν) m,
        ∫⁻ u in Ioi (6 / 5 / ν), ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
            frob (UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
              (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤
          ENNReal.ofReal (C * ‖w‖)

end UnforcedLeray.Short.PartIIIb.Concrete
