import UnforcedLeray.Units.B0220
import UnforcedLeray.Units.B0221.LineCalculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Order.CompletePartialOrder

/-!
# B0221 helper: the profile operators `S, K, Q_ε, A_ε, A_0` and the outer operator

Blueprint unit B0221 (label `eq:st18-t00114`), `paper/main.tex` lines 3316–3346.

Profile variables are `p = (s, q, η)` (`B0220.Profile`, tex line 3292). For a scalar profile
`f : Profile → ℝ` the classical partial derivatives are `∂_s f = Df(p)(1,0,0)`,
`∂_q f = Df(p)(0,1,0)`, `∂_η f = Df(p)(0,0,1)` (`dS`, `dQ`, `dEta`), and (tex lines 3318–3326)

* `S = s ∂_s` (`opS`), `K = 2 s ∂_s + η ∂_η` (`opK`), `Q_ε = ∂_q - ε(K + 1)` (`opQ`), tex lines 3318–3322;
* `A_ε = -S + ν s [Q_ε² + ∂_η²]` (`Aeps`, display `eq:st18-t00114`, tex lines 3323–3326);
* `A_0 = -S + ν s Δ_{q,η}` (`A0`, tex lines 3335–3338), and `A_ε = A_0` at `ε = 0` (`Aeps_zero`).

The outer operator `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` (tex lines 3343–3347) acts on scalar
fields `U : Space × ℝ → ℝ`, `U = U(x, τ)` (`outerGen`). Its Laplacian is the sum of the
classical second coordinate derivatives (`spatialLap`, the scalar form of the library's
`spatialLaplacian`); for `C²` fields it is Mathlib's Laplacian (`spatialLap_eq_laplacian`).

On a function that is not differentiable the Lean `fderiv` is `0`; every statement about
these operators below assumes `C²` regularity at the point, as in the manuscript.

`fderiv_opQ` and `Aeps_expand` express `A_ε b(p)` through the first and second derivatives of
`b` at `p`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open UnforcedLeray.B0220

namespace UnforcedLeray.B0221

/-! ### Directions and partial derivatives in the profile variables -/

/-- The `s` direction `(1, 0, 0)`. -/
def eS : Profile := (1, 0, 0)
/-- The `q` direction `(0, 1, 0)`. -/
def eQ : Profile := (0, 1, 0)
/-- The `η` direction `(0, 0, 1)`. -/
def eEta : Profile := (0, 0, 1)

@[simp] theorem eS_fst : eS.1 = 1 := rfl
@[simp] theorem eS_snd_fst : eS.2.1 = 0 := rfl
@[simp] theorem eS_snd_snd : eS.2.2 = 0 := rfl
@[simp] theorem eQ_fst : eQ.1 = 0 := rfl
@[simp] theorem eQ_snd_fst : eQ.2.1 = 1 := rfl
@[simp] theorem eQ_snd_snd : eQ.2.2 = 0 := rfl
@[simp] theorem eEta_fst : eEta.1 = 0 := rfl
@[simp] theorem eEta_snd_fst : eEta.2.1 = 0 := rfl
@[simp] theorem eEta_snd_snd : eEta.2.2 = 1 := rfl

/-- A continuous linear map on profiles through its values on `eS, eQ, eEta`. -/
theorem clm_apply_triple {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (M : Profile →L[ℝ] G) (a b c : ℝ) : M (a, b, c) = a • M eS + b • M eQ + c • M eEta := by
  have h : ((a, b, c) : Profile) = a • eS + b • eQ + c • eEta := by
    simp [eS, eQ, eEta]
  rw [h, map_add, map_add, map_smul, map_smul, map_smul]

/-- `∂_s f`. -/
def dS (f : Profile → ℝ) (p : Profile) : ℝ := fderiv ℝ f p eS
/-- `∂_q f`. -/
def dQ (f : Profile → ℝ) (p : Profile) : ℝ := fderiv ℝ f p eQ
/-- `∂_η f`. -/
def dEta (f : Profile → ℝ) (p : Profile) : ℝ := fderiv ℝ f p eEta

/-! ### The profile operators (tex lines 3318–3338) -/

/-- `S = s ∂_s` (tex line 3320). -/
def opS (f : Profile → ℝ) (p : Profile) : ℝ := p.1 * dS f p

/-- `K = 2 s ∂_s + η ∂_η` (tex line 3320). -/
def opK (f : Profile → ℝ) (p : Profile) : ℝ := 2 * p.1 * dS f p + p.2.2 * dEta f p

/-- `Q_ε = ∂_q - ε (K + 1)` (tex line 3321). -/
def opQ (ε : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ := dQ f p - ε * (opK f p + f p)

/-- The exact scalar conjugated free generator `A_ε = -S + ν s [Q_ε² + ∂_η²]`
(display `eq:st18-t00114`, tex lines 3323–3326), acting on `C²` profiles. -/
def Aeps (ν ε : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  -opS f p + ν * p.1 * (opQ ε (opQ ε f) p + dEta (dEta f) p)

/-- The limiting generator `A_0 = -S + ν s Δ_{q,η}` (tex line 3337). -/
def A0 (ν : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  -opS f p + ν * p.1 * (dQ (dQ f) p + dEta (dEta f) p)

theorem opQ_zero (f : Profile → ℝ) : opQ 0 f = dQ f := by
  funext p
  simp [opQ]

/-- `A_ε` at `ε = 0` is the limiting generator `A_0` (tex lines 3325, 3337). -/
theorem Aeps_zero (ν : ℝ) (f : Profile → ℝ) : Aeps ν 0 f = A0 ν f := by
  funext p
  simp only [Aeps, A0, opQ_zero]

/-! ### Derivatives of `Q_ε b` -/

section Expand

variable {b : Profile → ℝ} {p : Profile}

theorem hasFDerivAt_fderiv_apply (hD : DifferentiableAt ℝ (fderiv ℝ b) p) (v : Profile) :
    HasFDerivAt (fun p' => fderiv ℝ b p' v) ((fderiv ℝ (fderiv ℝ b) p).flip v) p := by
  have := hD.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  simpa using this

theorem fderiv_fderiv_apply (hD : DifferentiableAt ℝ (fderiv ℝ b) p) (v w : Profile) :
    fderiv ℝ (fun p' => fderiv ℝ b p' v) p w = fderiv ℝ (fderiv ℝ b) p w v := by
  rw [(hasFDerivAt_fderiv_apply hD v).fderiv]
  rfl

theorem differentiableAt_fderiv_of_contDiffAt (hb : ContDiffAt ℝ 2 b p) :
    DifferentiableAt ℝ (fderiv ℝ b) p :=
  (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- The derivative of `Q_ε b` at `p` in the direction `w`, for `b` of class `C²` at `p`. -/
theorem fderiv_opQ (ε : ℝ) (hb : ContDiffAt ℝ 2 b p) (w : Profile) :
    fderiv ℝ (opQ ε b) p w =
      fderiv ℝ (fderiv ℝ b) p w eQ - ε * (2 * w.1 * fderiv ℝ b p eS +
        2 * p.1 * fderiv ℝ (fderiv ℝ b) p w eS +
        (w.2.2 * fderiv ℝ b p eEta + p.2.2 * fderiv ℝ (fderiv ℝ b) p w eEta) +
        fderiv ℝ b p w) := by
  have hD := differentiableAt_fderiv_of_contDiffAt hb
  have hb1 : HasFDerivAt b (fderiv ℝ b p) p :=
    (hb.differentiableAt (by norm_num)).hasFDerivAt
  have hfst : HasFDerivAt (fun p' : Profile => 2 * p'.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    (hasFDerivAt_fst).const_mul 2
  have hsnd : HasFDerivAt (fun p' : Profile => p'.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_snd).snd
  have h := (hasFDerivAt_fderiv_apply hD eQ).sub
    ((((hfst.mul (hasFDerivAt_fderiv_apply hD eS)).add
      (hsnd.mul (hasFDerivAt_fderiv_apply hD eEta))).add hb1).const_mul ε)
  have hQ : HasFDerivAt (opQ ε b) _ p := h
  rw [hQ.fderiv]
  simp only [sub_apply, smul_apply, add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  ring

/-- `A_ε b(p)` through the derivatives of `b` at `p` (`D = Db(p)`, `D² = D²b(p)`). -/
theorem Aeps_expand (ν ε : ℝ) (hb : ContDiffAt ℝ 2 b p) :
    Aeps ν ε b p = -(p.1 * fderiv ℝ b p eS) + ν * p.1 *
      ((fderiv ℝ (fderiv ℝ b) p eQ eQ - ε * (2 * p.1 * fderiv ℝ (fderiv ℝ b) p eQ eS +
          p.2.2 * fderiv ℝ (fderiv ℝ b) p eQ eEta + fderiv ℝ b p eQ) -
        ε * (2 * p.1 * (fderiv ℝ (fderiv ℝ b) p eS eQ - ε * (2 * fderiv ℝ b p eS +
            2 * p.1 * fderiv ℝ (fderiv ℝ b) p eS eS + p.2.2 * fderiv ℝ (fderiv ℝ b) p eS eEta +
            fderiv ℝ b p eS)) +
          p.2.2 * (fderiv ℝ (fderiv ℝ b) p eEta eQ - ε * (2 * p.1 * fderiv ℝ (fderiv ℝ b) p eEta eS +
            (fderiv ℝ b p eEta + p.2.2 * fderiv ℝ (fderiv ℝ b) p eEta eEta) +
            fderiv ℝ b p eEta)) +
          (fderiv ℝ b p eQ - ε * (2 * p.1 * fderiv ℝ b p eS + p.2.2 * fderiv ℝ b p eEta +
            b p)))) +
        fderiv ℝ (fderiv ℝ b) p eEta eEta) := by
  have hD := differentiableAt_fderiv_of_contDiffAt hb
  have h1 : opQ ε (opQ ε b) p = fderiv ℝ (opQ ε b) p eQ - ε * (2 * p.1 * fderiv ℝ (opQ ε b) p eS +
      p.2.2 * fderiv ℝ (opQ ε b) p eEta + opQ ε b p) := rfl
  have h2 : dEta (dEta b) p = fderiv ℝ (fderiv ℝ b) p eEta eEta :=
    fderiv_fderiv_apply hD eEta eEta
  rw [Aeps, h1, h2, fderiv_opQ ε hb, fderiv_opQ ε hb, fderiv_opQ ε hb]
  simp only [opS, opQ, opK, dS, dQ, dEta, eS_fst, eS_snd_snd, eQ_fst, eQ_snd_snd, eEta_fst,
    eEta_snd_snd]
  ring

end Expand

/-! ### The outer operator `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` (tex lines 3343–3347) -/

/-- The spatial partial derivative `∂_i U(x, τ)`. -/
def spatialPartial (U : Space × ℝ → ℝ) (i : Fin 3) (y : Space × ℝ) : ℝ :=
  fderiv ℝ (fun x => U (x, y.2)) y.1 (coordinateVector i)

/-- The spatial Laplacian `Δ_x U(x, τ) = ∑ᵢ ∂ᵢ∂ᵢ U(x, τ)` (scalar form of the library's
`spatialLaplacian`). -/
def spatialLap (U : Space × ℝ → ℝ) (y : Space × ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ (fun x' => U (x', y.2)) x (coordinateVector i))
    y.1 (coordinateVector i)

/-- The phase derivative `∂_τ U(x, τ)`. -/
def timePartial (U : Space × ℝ → ℝ) (y : Space × ℝ) : ℝ := deriv (fun σ => U (y.1, σ)) y.2

/-- The outer operator `ν ε² Δ_x + (x·∇)/2 + 1/2 - ∂_τ` on scalar fields (tex lines
3343–3347). -/
def outerGen (ν ε : ℝ) (U : Space × ℝ → ℝ) (y : Space × ℝ) : ℝ :=
  ν * ε ^ 2 * spatialLap U y + (∑ i : Fin 3, y.1 i * spatialPartial U i y) / 2 + U y / 2 -
    timePartial U y

open Laplacian in
/-- For a field of class `C²` in `x`, `spatialLap` is Mathlib's Laplacian. -/
theorem spatialLap_eq_laplacian {U : Space × ℝ → ℝ} {x : Space} {τ : ℝ}
    (hU : ContDiffAt ℝ 2 (fun x' => U (x', τ)) x) :
    spatialLap U (x, τ) = Δ (fun x' => U (x', τ)) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ fun x' => U (x', τ)) x :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [spatialLap, iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_clm_apply hD (differentiableAt_const _)]
  simp [coordinateVector]

end UnforcedLeray.B0221
