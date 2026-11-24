import UnforcedLeray.Short.PartIIIb.Near
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIb.NearInst.GainMul
import UnforcedLeray.Short.PartIIIb.NearInst.Chart
import UnforcedLeray.Short.PartIIIa.Defs
import UnforcedLeray.Short.PartIIIa.StressSpaces
import UnforcedLeray.Short.PartIIb.ExactSplit

/-!
# The near operators on the concrete spaces (source `near/equation-comparison.tex`, lines 3861-3951;
`near/flat-causal.tex`, 3405-3581; `near/free-comparison.tex`, 1638-1690; `stress-spaces.tex`,
2664-2770)

Instantiates `NearPkg` (`Near.lean`) by the Banach spaces of `Concrete/Spaces.lean`
(`H`, `Z = Z_1 ⊕ ρ_b^{-1/2} H_T`, source 2664-2701).

## Objects

* `gainEquiv` : the gain multiplication `𝖦 T = g T` on `Z` (source 3875-3880,
  `g(s) = e^{γ s/(1+νs)}`), a continuous linear equivalence (`|g|, |g⁻¹| ≤ e^{|γ|/ν}`); `gainH` the
  same multiplication on `H`; `gainConjS γ hν S = g⁻¹ S g : Z → H`.
* `NearOps` : the four operators `S₀, S_N : Z → H`, `M₀, M_U : H → Z` as continuous linear maps;
  `D₀ = I + M₀S₀`, `D_N = I + M_US_N` (source 3880, 3914).
* The pins, which identify each operator with its source definition (each determines the operator
  uniquely: pointwise for the multipliers, by uniqueness of the causal solution for `S₀`, by
  density of smooth tensors (`PartIIa.IsStressMap`) for `S_ε`, by density of `IsBoxTensor` for
  `S_far`):
  - `IsFlatMult M tr` : `M₀ u = (v⊗u + u⊗v, 0)`, `v` the actual planar train (source 2763-2764,
    3566-3567, 3876-3877);
  - `IsSplitMult M R V rb` : `M_U u = (v⊗u + u⊗v, v_b⊗u + u⊗v_b)`, `v = s^{-1/2}V`,
    `v_b = s^{-1/2}r_b` for the exact split `U = V + r_b` (source 2706, 2758-2762, 3877-3878);
  - `IsFreeStress S ν μ` : `S₀ F` is the causal zero-entrance energy solution of the free flat
    equation `b_s + (μ/s)b - νΔb = 𝒫₀ div (F₁+F₂)` on the meridional block (source 3420-3440 with
    `v = 0`, 3561-3571, 1686-1689);
  - `IsStressTransport S S'` / `IsBodyTransport R R'` : `S` (resp. `R`) is the real form, on the
    spaces of `Concrete/Spaces.lean`, of the complex operator `S'` (resp. `R'`) of
    `PartII-a/StatementsNear.lean` (dictionary `tv4`, `merC`, `cellPt` of `NearInst/Chart.lean`);
  - `IsFarMask R ν μ δ S Sf` : `S_far = 1_{s<S, t>e^δ s} S_ε` in its exact kernel realization
    (source 3905-3912 with `sep:resolvent`, 3621), pinned on the dense class `IsBoxTensor`;
  - `IsMaskedNear p μ δ S SN` : `S_N = S_ε - S_far` with `S_ε` the curved free inverse
    `T_ε s div_ε` (`PartIIa.IsStressMap` for `PartIIa.Teps`, source 1675-1679, 3888-3897);
  - `IsActualNear p V rb μ δ S o` : the four pins at the background level `p`.
* `NearOps.pkgOf` : the `NearPkg` of the operators, with `D₀⁻¹ = Ring.inverse D₀` (the direct causal
  inverse; `IsUnit D₀` is part of the target `NearFlatBoundC`, `NearInst/Targets.lean`).
* `nearParamsOf` : the `NearParams` record of a level.

All operators act through the symmetric axisymmetric-without-swirl part `nsSym` of a tensor
(`NearInst/Chart.lean`), which is the identity on the source's tensor class `Sym_3`.

The targets (`near:flat-bound`, `near:deltaN`, `near:masked-free-bound`, the near solver and the
forced column) are in `NearInst/Targets.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## The gain multiplication -/

/-- The gain `g(s) = e^{γ s/(1+νs)}` as a function on the cylinder chart (source 2825, 3875); for the
(null) set `s ≤ 0` outside the age range the value at `max s 0` is used. -/
def gainFun (γ ν : ℝ) (p : Chart) : ℝ := UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0)

/-- The inverse gain `g⁻¹`. -/
def gainInvFun (γ ν : ℝ) (p : Chart) : ℝ := (gainFun γ ν p)⁻¹

theorem gainFun_measurable (γ ν : ℝ) : Measurable (gainFun γ ν) := by
  unfold gainFun UnforcedLeray.Short.IIIa.gainG
  fun_prop

theorem gainFun_pos (γ ν : ℝ) (p : Chart) : 0 < gainFun γ ν p := Real.exp_pos _

theorem gainExp_abs_le {γ ν : ℝ} (hν : 0 < ν) (p : Chart) :
    |γ * max p.1 0 / (1 + ν * max p.1 0)| ≤ |γ| / ν := by
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  have hd : 0 < 1 + ν * max p.1 0 := by positivity
  rw [abs_div, abs_mul, abs_of_nonneg hs, abs_of_pos hd, div_le_div_iff₀ hd hν]
  nlinarith [mul_nonneg (abs_nonneg γ) hs, abs_nonneg γ]

theorem gainFun_le {γ ν : ℝ} (hν : 0 < ν) (p : Chart) :
    |gainFun γ ν p| ≤ Real.exp (|γ| / ν) := by
  rw [abs_of_pos (gainFun_pos γ ν p)]
  unfold gainFun UnforcedLeray.Short.IIIa.gainG
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (gainExp_abs_le hν p))

theorem gainInvFun_le {γ ν : ℝ} (hν : 0 < ν) (p : Chart) :
    |gainInvFun γ ν p| ≤ Real.exp (|γ| / ν) := by
  unfold gainInvFun
  rw [abs_of_pos (inv_pos.2 (gainFun_pos γ ν p))]
  unfold gainFun UnforcedLeray.Short.IIIa.gainG
  rw [← Real.exp_neg]
  exact Real.exp_le_exp.2 ((neg_le_abs _).trans (gainExp_abs_le hν p))

theorem gainInvFun_mul {γ ν : ℝ} (p : Chart) : gainInvFun γ ν p * gainFun γ ν p = 1 :=
  inv_mul_cancel₀ (gainFun_pos γ ν p).ne'

/-- For `γ ≥ 0`: `1 ≤ g` (so `g⁻¹ ≤ 1`, source 4092). -/
theorem one_le_gainFun {γ ν : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (p : Chart) : 1 ≤ gainFun γ ν p := by
  unfold gainFun UnforcedLeray.Short.IIIa.gainG
  have hs : 0 ≤ max p.1 0 := le_max_right _ _
  exact Real.one_le_exp (by positivity)

/-- Gain on a cylinder `L²` space (measure `μ` on the chart). -/
def gainLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure Chart)
    (γ : ℝ) {ν : ℝ} (hν : 0 < ν) : Lp E 2 μ ≃L[ℝ] Lp E 2 μ :=
  mulBddEquiv (gainFun γ ν) (gainInvFun γ ν) (gainFun_measurable γ ν)
    ((gainFun_measurable γ ν).inv) (Real.exp (|γ| / ν)) (Real.exp (|γ| / ν)) (gainFun_le hν)
    (gainInvFun_le hν) gainInvFun_mul

/-- The gain multiplication `𝖦 T = g T` on `Z = Z_1 ⊕ ρ_b^{-1/2} H_T` (source 3875-3880). -/
def gainEquiv (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) : Zsp c mZ ρb ≃L[ℝ] Zsp c mZ ρb :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ (Z1sp c mZ) (HTrho c ρb)).trans
    (((gainLp (z1Measure c mZ) γ hν).prodCongr (gainLp (htRhoMeasure c ρb) γ hν)).trans
      (WithLp.prodContinuousLinearEquiv 1 ℝ (Z1sp c mZ) (HTrho c ρb)).symm)

/-- The gain multiplication on velocities `H` (source 4029-4031: `g⁻¹ S_N g : H_T → H`). -/
def gainH (c γ : ℝ) {ν : ℝ} (hν : 0 < ν) : Hsp c ≃L[ℝ] Hsp c := gainLp (ageμ c (-3 / 2)) γ hν

/-- `g⁻¹ S g : Z → H` for a stress-to-velocity map `S`. -/
def gainConjS {c mZ ρb : ℝ} (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (S : Zsp c mZ ρb →L[ℝ] Hsp c) :
    Zsp c mZ ρb →L[ℝ] Hsp c :=
  ((gainH c γ hν).symm : Hsp c →L[ℝ] Hsp c) ∘L S ∘L
    (gainEquiv c mZ ρb γ hν : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb)

/-! ## The operators -/

/-- The four operators of `near/equation-comparison.tex` (lines 3866-3897) on the concrete spaces:
the stress inverses `S₀, S_N : Z → H` (the stress inverse acts on the sum of the two components of
`Z`) and the multipliers `M₀, M_U : H → Z`. Their source definitions are the pins below. -/
structure NearOps (c mZ ρb : ℝ) where
  S0 : Zsp c mZ ρb →L[ℝ] Hsp c
  SN : Zsp c mZ ρb →L[ℝ] Hsp c
  M0 : Hsp c →L[ℝ] Zsp c mZ ρb
  MU : Hsp c →L[ℝ] Zsp c mZ ρb

section Ops

variable {c mZ ρb : ℝ}

/-- `D₀ = I + M₀ S₀` (line 3880). -/
def NearOps.D0 (o : NearOps c mZ ρb) : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb :=
  1 + o.M0.comp o.S0

/-- `D_N = I + M_U S_N` (line 3914). -/
def NearOps.DN (o : NearOps c mZ ρb) : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb :=
  1 + o.MU.comp o.SN

theorem NearOps.DN_sub_D0 (o : NearOps c mZ ρb) :
    o.DN - o.D0 = o.MU.comp o.SN - o.M0.comp o.S0 := by
  unfold NearOps.DN NearOps.D0; abel

/-! ## Pins -/

/-- `M₀` is multiplication by the actual planar train `v = tr` (source 2763-2764, 3566-3567,
3876-3877): first output `v ⊗ u + u ⊗ v` (order `(r, φ, z)`), second output `0`. -/
def IsFlatMult (M : Hsp c →L[ℝ] Zsp c mZ ρb) {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) :
    Prop :=
  ∀ u : Hsp c,
    ((M u).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
        (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter (trainMer tr p) (u p))) ∧
      (M u).snd = 0

/-- `M_U` is the exact split multiplier `M_U u = (v⊗u + u⊗v, v_b⊗u + u⊗v_b)` with the chart
coefficients `v = s^{-1/2}V`, `v_b = s^{-1/2}r_b` of the exact split `U = V + r_b`
(source 2706, 2758-2762, 3877-3878). -/
def IsSplitMult (M : Hsp c →L[ℝ] Zsp c mZ ρb) (R : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField) :
    Prop :=
  ∀ u : Hsp c,
    ((M u).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
        (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff R V p) (u p))) ∧
      ((M u).snd : Chart → Ten3) =ᵐ[htRhoMeasure c ρb]
        (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter
          (UnforcedLeray.Short.IIIa.chartCoeff R rb p) (u p)))

/-- `S₀` is the flat free causal response (source 3420-3440 with `v = 0`, 3561-3571, 1686-1689):
for every `F ∈ Z`, `S₀F` has a representative `b` which, with some weak gradient `G`, is the causal
zero-entrance energy solution of `b_s + (μ/s)b - νΔb = 𝒫₀ div T`, `T` the meridional block of
`F₁ + F₂`.  By uniqueness of that solution this determines `S₀`. -/
def IsFreeStress (S : Zsp c mZ ρb →L[ℝ] Hsp c) (ν μ : ℝ) : Prop :=
  ∀ F : Zsp c mZ ρb, ∃ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
    b =ᵐ[ageμ c (-3 / 2)] velC (S F) ∧
      UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν (μ : ℂ) (fun _ _ _ => 0)
        (merBlockC (zsum F)) b G

/-- `S : Z → H` is the real form of the complex stress map `S' : H_T → H` of `PartII-a` (dictionary
`tv4`, `merC`, `cellPt`; source 1641-1646, 2676-2679). -/
def IsStressTransport (S : Zsp c mZ ρb →L[ℝ] Hsp c)
    (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) : Prop :=
  ∀ (F : Zsp c mZ ρb) (F' : UnforcedLeray.Short.PartIIa.HTSpace c),
    (F' : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
        =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] (fun p => tv4 (zsum F (cellPt c p))) →
      (S' F' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => merC (S F (cellPt c p)))

/-- `R : H → H` is the real form of the complex body operator `R'` of `PartII-a`
(`Teps`, `T0flat`, source 1675-1677). -/
def IsBodyTransport (R : Hsp c →L[ℝ] Hsp c)
    (R' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) : Prop :=
  ∀ (f : Hsp c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => merC (f (cellPt c p))) →
      (R' f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => merC (R f (cellPt c p)))

/-- `Sf = S_far = 1_{s<S, t>e^δ s} S_ε` in its exact kernel realization (source 3905-3912): on the
dense class `IsBoxTensor`, `S_far F (s,q,η) = 1_{s<S} s^{-1/2} (S_μ[1_{t>e^δ s} 𝒩_T(F₁+F₂)])_{r,z}`
at `(y, τ) = (chartY, chartTau)`, with `S_μ T = -W_μ` (`sep:resolvent`, source 3621) and the
output lift `𝒩_v b = √s b` (source 2683). -/
def IsFarMask (R ν μ δ S : ℝ) (Sf : Zsp c mZ ρb →L[ℝ] Hsp c) : Prop :=
  ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f → zsum F =ᵐ[ageμ c (-1 / 2)] f →
    (Sf F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] fun p =>
      if p.1 < S then
        (Real.sqrt p.1)⁻¹ • merRe (-sepWfar ν (μ : ℂ) R δ p.1 (cartLift R c f) (chartY R p)
          (chartTau R p))
      else 0

end Ops

open UnforcedLeray.Cons.C03.Concrete

/-- `S_N = S_ε - S_far` (source 3905-3914): `S_ε` is the curved free inverse `T_ε s div_ε` of
`near/free-comparison.tex` (`PartIIa.IsStressMap` for `PartIIa.Teps` at the level `p`, `P = 2εc`,
source 1675-1679, 3888-3897), in real form, and `S_far` its masked part `IsFarMask` with output cut
`S` and log gap `δ`. -/
def IsMaskedNear {mZ ρb : ℝ} (p : Params) (μ δ S : ℝ) (SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c) : Prop :=
  ∃ (Seps Sf : Zsp p.c mZ ρb →L[ℝ] Hsp p.c)
    (Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ]
      UnforcedLeray.B0220.HSpace p.c UnforcedLeray.B0223.MeridC),
    UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
        (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
        Seps' ∧
      IsStressTransport Seps Seps' ∧ IsFarMask p.R p.ν μ δ S Sf ∧ SN = Seps - Sf

/-- The near operators at the background level `p` (source 3866-3914): the actual flat train
`p.trainData`, the exact split `(V, r_b)` in the chart of radius `R = ε⁻¹`, the flat free response
at `(ν, μ)`, and the masked curved free inverse with gap `δ` and output cut `S`. -/
structure IsActualNear {mZ ρb : ℝ} (p : Params) (V rb : ℝ → UnforcedLeray.SpatialField)
    (μ δ S : ℝ) (o : NearOps p.c mZ ρb) : Prop where
  flat : IsFlatMult o.M0 p.trainData
  split : IsSplitMult o.MU p.R V rb
  free : IsFreeStress o.S0 p.ν μ
  near : IsMaskedNear p μ δ S o.SN

/-! ## The package -/

section Pkg

variable {c mZ ρb : ℝ}

/-- The `NearPkg` of the concrete near operators at gain exponent `γ` and viscosity `ν > 0`, with the
direct causal inverse `D₀⁻¹ = Ring.inverse D₀` (two-sided when `D₀` is a unit). -/
def NearOps.pkgOf (o : NearOps c mZ ρb) (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (hU : IsUnit o.D0) :
    NearPkg where
  Z := Zsp c mZ ρb
  G := gainEquiv c mZ ρb γ hν
  D0 := o.D0
  DN := o.DN
  D0inv := Ring.inverse o.D0
  D0_left := Ring.inverse_mul_cancel o.D0 hU
  D0_right := Ring.mul_inverse_cancel o.D0 hU

theorem NearOps.pkgOf_deltaN (o : NearOps c mZ ρb) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (hU : IsUnit o.D0) :
    (o.pkgOf γ hν hU).deltaN = ‖conjG (gainEquiv c mZ ρb γ hν) (o.DN - o.D0)‖ := rfl

theorem NearOps.pkgOf_flatNorm (o : NearOps c mZ ρb) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (hU : IsUnit o.D0) :
    (o.pkgOf γ hν hU).flatNorm = ‖conjG (gainEquiv c mZ ρb γ hν) (Ring.inverse o.D0)‖ := rfl

end Pkg

/-- The `NearParams` record (`Near.lean`) of the level `p` with Floquet exponent `μ`, exponents
`a, b`, log gap `δ`, background loss `m₀` and transverse accuracy `D_⊥` (source 3927-3930). -/
def nearParamsOf (p : Params) (μ a b δ m0 Dp : ℝ) : NearParams :=
  ⟨p.ν, p.ε, μ, a, b, δ, m0, Dp⟩

end UnforcedLeray.Short.PartIIIb.NearInst
