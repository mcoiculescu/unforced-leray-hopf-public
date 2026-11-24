import UnforcedLeray.Short.PartIIIb.Return
import UnforcedLeray.Short.PartIIIb.StatementsA
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.NearInst.GainMul
import UnforcedLeray.Short.PartIIIa.Defs

/-!
# The return operators on the concrete gain-normed spaces (source 5118-5143, 5536-5662, 5777-5833)

This file instantiates `ReturnOps` (`Return.lean`) on concrete Banach spaces.

## Spaces (all over the cylinder chart `(s, (q, η))`, source 2666-2701)

`g(s) = e^{γ s/(1+νs)}` is the gain (source 3875, 5117); `ginv = g⁻¹`.

* `VelG c γ ν` (`Vel`): meridional velocity coefficients `b` (physical field `𝒩_v b = √s b`,
  source 2683) with the normalized gain body norm
  `G(w) = R⁻¹‖g⁻¹ w‖_{Y_2} = √π ‖g⁻¹ b‖_H` (source 5143 with the lift identity 2685-2689),
  realized as `L²(π g⁻² s^{-3/2} dς; ℝ²)`.  Velocities are axisymmetric without swirl
  (source 5141-5142); solenoidality is not part of the space (source 5142, 5643).
* `SrcG c` (`Src`): body forces `f = 𝒩_v b` in the *ungained* normalized body norm
  `R⁻¹‖f‖_{Y_2} = √π ‖b‖_H` (source 2683-2689), realized as `L²(π s^{-3/2} dς; ℝ²)`.  This is
  the norm in which the source measures every body force: the general affine bounds for
  `F_A, E_A, 𝔯_A` (5009-5016), the body errors (5250, 5291, 5501, 5512) and the near-solver
  mapping bound `‖g⁻¹M_U R_μ f‖_Z ≤ P_ν R⁻¹‖f‖_{Y_2}` (5542, 5552).  The gained force bound
  `R⁻¹‖g⁻¹F_A‖_{Y_2} ≤ P_ν‖A‖_𝒜` (5099-5103) is an additional estimate for `F_A` only and is
  not the norm of `Src`.  (The `L^{22/19}` class of source 4157 is the class of the old *repair
  stress*; it enters through the repair component of `Str`.)
* `StrG c mZ ρb γ ν` (`Str`): stresses with the gain norm `A = ‖g⁻¹ T‖_Z`,
  `Z = Z_1 ⊕ ρ_b^{-1/2} H_T` with the sum norm (source 2697-2700, 5609), realized as the
  `ℓ¹` product of `L²(g⁻² s^{-1/2} W² dς)` and `L²(g⁻² ρ_b⁻¹ s^{-1/2} dς)`.
* `PairSp M a ν` (`Gam`): the closed graph `𝓔_ν = {(T, w) : T = M w}` (source 5640-5643)
  with the pair norm `‖T‖ + e^{-a/ν}‖w‖` (source 5658, `a = γ/8`), a Banach space because `M`
  is bounded (source 5645-5647; proved here: `PairSp.instCompleteSpace`).
* `Aff`: the space `𝒜` (source 4741-4752).  It is a type parameter here; the concrete
  instance at `Aff = AffSp a_s` (task `PartIII-b:C/ret/1`) is assembled downstream.

## Operators

`ReturnBase` holds the source's primary operators as continuous linear maps between the
concrete spaces, together with the two-sided inverse `D_N⁻¹` of `D_N = I + M S_N` (source
5787, `near:equation-comparison`).  `ReturnBase.toOps` builds the `ReturnOps` of source
5785-5833; the derived fields are *defined* by the source's formulas:

* `Tc`, `wc` : the two components of a graph element;
* `𝒥(v) = (D_N⁻¹ M v, v - S_N D_N⁻¹ M v)` (source 5790-5793), which lies in the graph
  (`jlift_graph`, "Its components satisfy `T = Mw` exactly", source 5794);
* `𝒫 A = 𝒥(R_μ F_A)`, `𝒬(T, w) = -𝒥(v_Q(T))`, `L(T, w) = L T` (source 5815-5818).

Proved: `toOps_isGraphLift`, `toOps_isNearInverse`, `toOps_isGraphInj`, `toOps_pairNorm`
(the pair-norm clause of `PairNormAndNearSolver`), and `hNilpotent_of_support` (source
4314-4319, 5813-5814: old dependence in kernel form plus young support give `H² = 0`).

Pinning statements (the source definitions of the primary fields, consumed downstream):

* `chiOStr` : the outward cutoff `χ_o` (source 4163-4166, 5148-5150) as a concrete
  multiplication operator on `Str`; `HOldKernel`/`HYoungSupport` (StatementsA) for the
  concrete instance are stated with it (`ReturnBase.toOps_hNilpotent`);
* `IsAffinePinned` : `ĥ_A, F_A, E_A` are the concrete fields of `Concrete/ReturnAff.lean`
  (source 4969-4985), read in the coefficient convention `b = s^{-1/2} · (physical field)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Gain-normed concrete spaces -/

/-- The inverse gain `g⁻¹(s) = e^{-γ s/(1+νs)}` on the chart (source 3875, 5117); on the null set
`s ≤ 0` outside the age range the value at `max s 0` is used. -/
def ginv (γ ν : ℝ) (p : Chart) : ℝ := (UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0))⁻¹

/-- The measure `π g⁻² s^{-3/2} dς` of the normalized gain body norm
`R⁻¹‖g⁻¹ 𝒩_v b‖_{Y_2} = √π ‖g⁻¹ b‖_H` (source 2683-2689, 5143). -/
def bodyMeasure (c γ ν : ℝ) : Measure Chart :=
  (ageμ c (-3 / 2)).withDensity fun p => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2)

/-- Body velocities (`Vel`), source 5141-5143. -/
abbrev VelG (c γ ν : ℝ) := Lp (α := Chart) Merid 2 (bodyMeasure c γ ν)

/-- The measure `π s^{-3/2} dς` of the ungained normalized body norm
`R⁻¹‖𝒩_v b‖_{Y_2} = √π ‖b‖_H` (source 2683-2689). -/
def srcMeasure (c : ℝ) : Measure Chart := ENNReal.ofReal Real.pi • ageμ c (-3 / 2)

/-- Body forces (`Src`) in the ungained normalized body norm `R⁻¹‖f‖_{Y_2}` (source 2683-2689;
used in 5009-5016, 5250, 5291, 5501, 5512, 5542, 5552). -/
abbrev SrcG (c : ℝ) := Lp (α := Chart) Merid 2 (srcMeasure c)

/-- `g⁻² W² s^{-1/2} dς`: the gain-weighted measure of `Z_1` (source 2697, 5609). -/
def gainZ1Measure (c mZ γ ν : ℝ) : Measure Chart :=
  (z1Measure c mZ).withDensity fun p => ENNReal.ofReal (ginv γ ν p ^ 2)

/-- `g⁻² ρ_b⁻¹ s^{-1/2} dς`: the gain-weighted measure of `ρ_b^{-1/2} H_T` (source 2698-2700). -/
def gainHTMeasure (c ρb γ ν : ℝ) : Measure Chart :=
  (htRhoMeasure c ρb).withDensity fun p => ENNReal.ofReal (ginv γ ν p ^ 2)

/-- Stresses (`Str`) with the gain norm `‖g⁻¹T‖_Z = ‖g⁻¹T₁‖_{Z_1} + ρ_b^{-1/2}‖g⁻¹T₂‖_{H_T}`
(source 2698-2700, 5609). -/
abbrev StrG (c mZ ρb γ ν : ℝ) :=
  WithLp 1 (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν) ×
    Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))

example (c mZ ρb γ ν : ℝ) : CompleteSpace (StrG c mZ ρb γ ν) := inferInstance
example (c γ ν : ℝ) : CompleteSpace (VelG c γ ν) := inferInstance

/-! ## 2. The pair space `𝓔_ν` (source 5640-5662) -/

section Pair

variable {V S : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The graph `{(T, w) : T = M w}` of the multiplier (source 5640). -/
def graphSub (M : V →L[ℝ] S) : Submodule ℝ (S × V) where
  carrier := {p | p.1 = M p.2}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at hx hy ⊢
    rw [hx, hy]
  zero_mem' := by simp
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, map_smul] at hx ⊢
    rw [hx]

/-- The pair space `𝓔_ν`: the graph of `M`, to be normed by `‖T‖ + e^{-a/ν}‖w‖`
(source 5640-5662). -/
def PairSp (M : V →L[ℝ] S) (_a _ν : ℝ) : Type := graphSub M

namespace PairSp

variable {M : V →L[ℝ] S} {a ν : ℝ}

instance : AddCommGroup (PairSp M a ν) := inferInstanceAs (AddCommGroup (graphSub M))
instance : Module ℝ (PairSp M a ν) := inferInstanceAs (Module ℝ (graphSub M))

/-- The underlying graph element. -/
def toGraph : PairSp M a ν →ₗ[ℝ] graphSub M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The stress component `T`. -/
def TL : PairSp M a ν →ₗ[ℝ] S := LinearMap.fst ℝ S V ∘ₗ (graphSub M).subtype ∘ₗ toGraph

/-- The velocity witness `w`. -/
def wL : PairSp M a ν →ₗ[ℝ] V := LinearMap.snd ℝ S V ∘ₗ (graphSub M).subtype ∘ₗ toGraph

theorem graph (x : PairSp M a ν) : TL x = M (wL x) := (toGraph x).2

theorem ext' {x y : PairSp M a ν} (h1 : TL x = TL y) (h2 : wL x = wL y) : x = y := by
  have h : ((toGraph x : graphSub M) : S × V) = (toGraph y : graphSub M) := Prod.ext h1 h2
  exact Subtype.ext h

/-- A graph element from its components. -/
def mk (T : S) (w : V) (h : T = M w) : PairSp M a ν := (⟨(T, w), h⟩ : graphSub M)

@[simp] theorem TL_mk (T : S) (w : V) (h : T = M w) : TL (mk T w h : PairSp M a ν) = T := rfl
@[simp] theorem wL_mk (T : S) (w : V) (h : T = M w) : wL (mk T w h : PairSp M a ν) = w := rfl

variable (M a ν) in
/-- The embedding `(T, w) ↦ (T, e^{-a/ν} w)` into the `ℓ¹` product; it defines the pair norm. -/
def embL : PairSp M a ν →ₗ[ℝ] WithLp 1 (S × V) :=
  (WithLp.linearEquiv 1 ℝ (S × V)).symm.toLinearMap ∘ₗ
    LinearMap.prod TL (Real.exp (-a / ν) • wL)

theorem embL_apply (x : PairSp M a ν) :
    embL M a ν x = WithLp.toLp 1 (TL x, Real.exp (-a / ν) • wL x) := rfl

theorem embL_injective : Function.Injective (embL M a ν) := by
  intro x y h
  rw [embL_apply, embL_apply] at h
  have h' := congrArg WithLp.ofLp h
  simp only [Prod.mk.injEq] at h'
  exact ext' h'.1 (smul_right_injective V (Real.exp_pos _).ne' h'.2)

instance : NormedAddCommGroup (PairSp M a ν) :=
  NormedAddCommGroup.induced (PairSp M a ν) (WithLp 1 (S × V)) (embL M a ν) embL_injective

instance : NormedSpace ℝ (PairSp M a ν) :=
  NormedSpace.induced ℝ (PairSp M a ν) (WithLp 1 (S × V)) (embL M a ν)

/-- The pair norm `‖(T, w)‖ = ‖T‖ + e^{-a/ν}‖w‖` (source 5658). -/
theorem norm_eq (x : PairSp M a ν) : ‖x‖ = ‖TL x‖ + Real.exp (-a / ν) * ‖wL x‖ := by
  show ‖embL M a ν x‖ = _
  rw [WithLp.prod_norm_eq_of_L1, embL_apply]
  simp [norm_smul]

theorem isometry_embL : Isometry (embL M a ν) :=
  AddMonoidHomClass.isometry_of_norm (embL M a ν) (fun _ => rfl)

theorem range_embL :
    Set.range (embL M a ν) =
      {p : WithLp 1 (S × V) | p.fst = M (Real.exp (a / ν) • p.snd)} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simp only [Set.mem_setOf_eq, embL_apply, WithLp.toLp_fst, WithLp.toLp_snd, smul_smul,
      ← Real.exp_add]
    rw [show a / ν + -a / ν = 0 by ring, Real.exp_zero, one_smul]
    exact graph x
  · intro hp
    refine ⟨mk p.fst (Real.exp (a / ν) • p.snd) hp, ?_⟩
    rw [embL_apply]
    simp only [TL_mk, wL_mk, smul_smul, ← Real.exp_add]
    rw [show -a / ν + a / ν = 0 by ring, Real.exp_zero, one_smul]
    rfl

/-- `𝓔_ν` is a Banach space (source 5645-5647: the multiplier is bounded, so the graph is
closed). -/
instance [CompleteSpace V] [CompleteSpace S] : CompleteSpace (PairSp M a ν) := by
  rw [completeSpace_iff_isComplete_range isometry_embL.isUniformInducing, range_embL]
  apply IsClosed.isComplete
  exact isClosed_eq (WithLp.fstL 1 ℝ S V).continuous
    (M.continuous.comp ((continuous_const_smul _).comp (WithLp.sndL 1 ℝ S V).continuous))

/-- The embedding as a continuous linear map. -/
def embCLM : PairSp M a ν →L[ℝ] WithLp 1 (S × V) := ⟨embL M a ν, isometry_embL.continuous⟩

/-- The stress component as a continuous linear map. -/
def TcL : PairSp M a ν →L[ℝ] S := (WithLp.fstL 1 ℝ S V).comp embCLM

theorem TcL_apply (x : PairSp M a ν) : TcL x = TL x := rfl

/-- A linear map into `𝓔_ν` whose embedded version is continuous is continuous. -/
def liftCLM {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X →ₗ[ℝ] PairSp M a ν)
    (g : X →L[ℝ] WithLp 1 (S × V)) (h : ∀ x, embL M a ν (f x) = g x) :
    X →L[ℝ] PairSp M a ν :=
  ⟨f, by
    rw [isometry_embL.isUniformInducing.isInducing.continuous_iff]
    have hfg : (embL M a ν) ∘ f = g := funext h
    change Continuous ((embL M a ν) ∘ f)
    rw [hfg]
    exact g.continuous⟩

theorem liftCLM_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →ₗ[ℝ] PairSp M a ν) (g : X →L[ℝ] WithLp 1 (S × V))
    (h : ∀ x, embL M a ν (f x) = g x) (x : X) : liftCLM f g h x = f x := rfl

end PairSp

end Pair

/-! ## 3. The primary operators and the instance -/

/-- The primary operators of the exact return system at one regime (source 5777-5833), as
continuous linear maps between the concrete spaces:

| field | source object |
|---|---|
| `M` | exact multiplier `M_U` with the prescribed normalization maps (3876-3877, 4147, 5782) |
| `S`, `SN` | full tensor inverse `S_μ`, near inverse `S_N` (4144-4146, 3912-3920) |
| `R` | physical body inverse `R_μ`, including the Leray projection (4144-4146, 5781, 5820) |
| `Yf`, `hf`, `Ef` | Ward fields `Y[T]`, `h[T]` and the residual `ℙẼ_μ[T]` (4171-4177, 4267-4280) |
| `Lj` | complete old-thin-to-young-jet map `𝓛` (`source-class:L`, 4792-4796) |
| `hA`, `FA`, `EA`, `rA` | physical affine fields `ĥ_A, F_A, E_A, 𝔯_A` (4980-5008) |
| `DNinv` | `D_N⁻¹`, two-sided inverse of `D_N = I + M S_N` (3917, 5787) |
| `aMu`, `Lam`, `Kflat` | `a_μ`, `Λ_{μ,ν}`, `𝒦^flat_{μ,ν}` (4814-4820) |

The pins identifying the fields with their source definitions are separate statements
(`chiOStr`/`HOldKernel`, `IsAffinePinned`, and the follow-ups of the physical layer). -/
structure ReturnBase (c mZ ρb γ ν : ℝ) (Aff : Type) [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] where
  M : VelG c γ ν →L[ℝ] StrG c mZ ρb γ ν
  S : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν
  SN : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν
  R : SrcG c →L[ℝ] VelG c γ ν
  Yf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν
  hf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν
  Ef : StrG c mZ ρb γ ν →L[ℝ] SrcG c
  Lj : StrG c mZ ρb γ ν →L[ℝ] Aff
  hA : Aff →L[ℝ] VelG c γ ν
  FA : Aff →L[ℝ] SrcG c
  EA : Aff →L[ℝ] SrcG c
  rA : Aff →L[ℝ] SrcG c
  DNinv : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν
  DNinv_left : ∀ T, DNinv (T + M (SN T)) = T
  DNinv_right : ∀ T, DNinv T + M (SN (DNinv T)) = T
  aMu : Aff
  Lam : Aff →L[ℝ] ℝ
  Kflat : Aff →L[ℝ] Aff

namespace ReturnBase

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)

/-- The pair space `𝓔_ν` of this regime, with `a = γ/8` (source 5657). -/
abbrev Gam := PairSp B.M (γ / 8) ν

/-- The near graph lift lies in the graph (source 5794): `D_N⁻¹ M v = M (v - S_N D_N⁻¹ M v)`. -/
theorem jlift_graph (v : VelG c γ ν) :
    B.DNinv (B.M v) = B.M (v - B.SN (B.DNinv (B.M v))) := by
  rw [map_sub]
  exact eq_sub_of_add_eq (B.DNinv_right (B.M v))

/-- `𝒥` as a linear map into `𝓔_ν`. -/
def jliftₗ : VelG c γ ν →ₗ[ℝ] B.Gam where
  toFun v := PairSp.mk (B.DNinv (B.M v)) (v - B.SN (B.DNinv (B.M v))) (B.jlift_graph v)
  map_add' u v := PairSp.ext' (by simp) (by simp; abel)
  map_smul' r v := PairSp.ext' (by simp) (by simp [smul_sub])

/-- The embedded near graph lift `v ↦ (D_N⁻¹ M v, e^{-a/ν}(v - S_N D_N⁻¹ M v))`. -/
def jliftE : VelG c γ ν →L[ℝ] WithLp 1 (StrG c mZ ρb γ ν × VelG c γ ν) :=
  ((WithLp.prodContinuousLinearEquiv 1 ℝ (StrG c mZ ρb γ ν) (VelG c γ ν)).symm :
      StrG c mZ ρb γ ν × VelG c γ ν →L[ℝ] WithLp 1 (StrG c mZ ρb γ ν × VelG c γ ν)).comp
    ((B.DNinv.comp B.M).prod
      (Real.exp (-(γ / 8) / ν) •
        (ContinuousLinearMap.id ℝ (VelG c γ ν) - B.SN.comp (B.DNinv.comp B.M))))

/-- The near graph lift `𝒥(v) = (D_N⁻¹Mv, v - S_N D_N⁻¹Mv)` (source 5790-5793). -/
def jlift : VelG c γ ν →L[ℝ] B.Gam :=
  PairSp.liftCLM B.jliftₗ B.jliftE (fun v => by rw [PairSp.embL_apply]; rfl)

/-- The error velocity `v_Q(T) = S_far T + Y + R_μ(E - E_{LT} - r_{LT})` (source 5807). -/
def vQL : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν :=
  (B.S - B.SN) + B.Yf + B.R.comp (B.Ef - B.EA.comp B.Lj - B.rA.comp B.Lj)

/-- The `ReturnOps` of the concrete regime (source 5785-5833). -/
def toOps : ReturnOps (VelG c γ ν) (StrG c mZ ρb γ ν) (SrcG c) Aff B.Gam where
  M := B.M
  S := B.S
  SN := B.SN
  R := B.R
  Yf := B.Yf
  hf := B.hf
  Ef := B.Ef
  Lj := B.Lj
  hA := B.hA
  FA := B.FA
  EA := B.EA
  rA := B.rA
  DNinv := B.DNinv
  Tc := PairSp.TL
  wc := PairSp.wL
  P := B.jlift.comp (B.R.comp B.FA)
  Q := -(B.jlift.comp (B.vQL.comp PairSp.TcL))
  Lg := B.Lj.comp PairSp.TcL
  aMu := B.aMu
  Lam := B.Lam
  Kflat := B.Kflat

/-- The graph and lift identities hold by construction (source 5790-5818). -/
theorem toOps_isGraphLift : B.toOps.IsGraphLift := by
  refine ⟨fun V => PairSp.graph V, fun V => rfl, fun x => rfl, fun V => ?_⟩
  refine Prod.ext ?_ ?_
  · show -(B.DNinv (B.M (B.vQL (PairSp.TL V)))) = _
    simp [ReturnOps.Jlift, ReturnOps.vQ, ReturnOps.Sfar, vQL, toOps]
  · show -(B.vQL (PairSp.TL V) - B.SN (B.DNinv (B.M (B.vQL (PairSp.TL V))))) = _
    simp [ReturnOps.Jlift, ReturnOps.vQ, ReturnOps.Sfar, vQL, toOps]

/-- `D_N⁻¹` is a two-sided inverse of `D_N` (source 5787). -/
theorem toOps_isNearInverse : B.toOps.IsNearInverse :=
  ⟨fun T => B.DNinv_left T, fun T => B.DNinv_right T⟩

/-- A graph element is determined by its components. -/
theorem toOps_isGraphInj : B.toOps.IsGraphInj := fun _ _ h1 h2 => PairSp.ext' h1 h2

/-- The pair norm of `𝓔_ν` (source 5657-5658), the last clause of `PairNormAndNearSolver`. -/
theorem toOps_pairNorm (V : B.Gam) :
    ‖V‖ = ‖B.toOps.Tc V‖ + Real.exp (-(γ / 8) / ν) * ‖B.toOps.wc V‖ :=
  PairSp.norm_eq V

end ReturnBase

/-! ## 4. Nilpotency from old dependence and young support (source 4314-4319, 5813-5814) -/

/-- "`H` depends only on `χ_oT` and has young support, so `H² = 0`" (source 4314-4316,
5813-5814): `χ_o T = 0 → H T = 0` and `χ_o H T = 0` give `H² = 0`. -/
theorem hNilpotent_of_support {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str)
    (h1 : HOldKernel o chiO) (h2 : HYoungSupport o chiO) : o.HNilpotent :=
  fun T => h1 _ (h2 T)

/-! ## 5. Pins: the outward cutoff and the physical affine fields -/

/-- The outward source cutoff profile `χ̂_o` (source 4163-4166, 5148-5150):
`χ_o(s) = χ̂_o(νs)` vanishes for `s ≤ 1.2/ν` and equals one for `s ≥ 1.5/ν`.  `C^∞`
(`(⊤ : ℕ∞)`, not the analytic `ω`). -/
structure IsOutwardCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  zero : ∀ t, t ≤ 6 / 5 → χ t = 0
  one : ∀ t, 3 / 2 ≤ t → χ t = 1
  range : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1

/-- The source cutoff profile `χ̂_f` (source 4750-4752, 4955-4956): `χ_f(s) = χ̂_f(νs)` equals one
for `s ≤ 1/ν` and vanishes for `s ≥ 1.1/ν`; `C^∞`. -/
structure IsSourceCutoffC (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  one : ∀ t, t ≤ 1 → χ t = 1
  zero : ∀ t, 11 / 10 ≤ t → χ t = 0
  range : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1

/-- `p ↦ χ̂(ν s)` on the chart. -/
def cutFun (χ : ℝ → ℝ) (ν : ℝ) (p : Chart) : ℝ := χ (ν * p.1)

theorem cutFun_measurable {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ) (ν : ℝ) :
    Measurable (cutFun χ ν) :=
  hχ.smooth.continuous.measurable.comp (measurable_const.mul measurable_fst)

theorem cutFun_bound {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ) (ν : ℝ) (p : Chart) :
    |cutFun χ ν p| ≤ 1 := by
  unfold cutFun
  rw [abs_of_nonneg (hχ.range _).1]
  exact (hχ.range _).2

/-- The outward cutoff `χ_o` acting on stresses, componentwise multiplication by `χ̂_o(νs)`
(source 4163-4166, 4171: `W_μ = -S_μ(χ_o T)`). -/
def chiOStr (c mZ ρb γ ν : ℝ) {χ : ℝ → ℝ} (hχ : IsOutwardCutoff χ) :
    StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν :=
  let e := WithLp.prodContinuousLinearEquiv 1 ℝ
    (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))
  (e.symm : _ →L[ℝ] StrG c mZ ρb γ ν).comp
    (((NearInst.mulBdd (E := Ten3) (μ := gainZ1Measure c mZ γ ν) (cutFun χ ν)
        (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν)).prodMap
      (NearInst.mulBdd (E := Ten3) (μ := gainHTMeasure c ρb γ ν) (cutFun χ ν)
        (cutFun_measurable hχ ν) 1 (cutFun_bound hχ ν))).comp
      (e : StrG c mZ ρb γ ν →L[ℝ] _))

/-- The `(r, z)` components of a vector in the order `(r, φ, z)`. -/
def merOf (v : Vec3) : Merid := !₂[v 0, v 2]

/-- The physical affine fields of the instance are those of `Concrete/ReturnAff.lean`
(source 4969-4985: `ĥ_A`, `F_A = s^{3/2} f_A`, `E_A = s^{3/2} e_A`), in the coefficient
convention `b = s^{-1/2} ·` (physical field) of `VelG`/`SrcG`.  `ι` is the inclusion of `𝒜` into
matrix functions, `χf` the source cutoff profile, `ε = R⁻¹`.  The azimuthal component of these
fields vanishes for `A ∈ 𝒜` (no entry with exactly one azimuthal index), so only `(r, z)`
components are recorded. -/
def IsAffinePinned {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (ι : Aff →ₗ[ℝ] (ℝ → Mat3))
    (χf : ℝ → ℝ) (μ ε : ℝ) : Prop :=
  ∀ A : Aff,
    ((B.hA A : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
      fun p => merOf ((Real.sqrt p.1)⁻¹ • hhatA ν ε χf (ι A) p.1 p.2)) ∧
    ((B.FA A : Chart → Merid) =ᵐ[srcMeasure c]
      fun p => merOf ((Real.sqrt p.1)⁻¹ • FA ν μ χf (ι A) p.1 p.2)) ∧
    ((B.EA A : Chart → Merid) =ᵐ[srcMeasure c]
      fun p => merOf ((Real.sqrt p.1)⁻¹ • EA ν μ χf (ι A) p.1 p.2))

/-- Concrete nilpotency: for the instance, `H² = 0` follows from old dependence in kernel form
(`χ_oT = 0 → HT = 0`) and young support with respect to the concrete outward cutoff
(source 4314-4319, 5813-5814).  Both hypotheses are reduced to the pins of the instance in
`Concrete/PhysLayer.lean` (`ReturnBase.hOldKernel_of`, `ReturnBase.hYoungSupport_of`). -/
theorem ReturnBase.toOps_hNilpotent {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) {χ : ℝ → ℝ}
    (hχ : IsOutwardCutoff χ)
    (h1 : HOldKernel B.toOps (chiOStr c mZ ρb γ ν hχ : StrG c mZ ρb γ ν →ₗ[ℝ] _))
    (h2 : HYoungSupport B.toOps (chiOStr c mZ ρb γ ν hχ : StrG c mZ ρb γ ν →ₗ[ℝ] _)) :
    B.toOps.HNilpotent :=
  hNilpotent_of_support B.toOps _ h1 h2

end UnforcedLeray.Short.PartIIIb.Concrete
