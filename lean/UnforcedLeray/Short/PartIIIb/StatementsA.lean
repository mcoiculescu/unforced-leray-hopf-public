import UnforcedLeray.Short.PartIIIb.Return
import UnforcedLeray.Short.PartIIIb.Scalar

/-!
# Statements A: Ward, physical affine, source class, repair, closure budget

Source: `the November 2 reference manuscript`.
Each `def ... : Prop` below is one numbered result of the source, over the operators of
`ReturnOps` (see `Return.lean`) on a sequence of regimes `ReturnSeq` (the phase-locked sequence
`ν_n`, with `μ = μ_n(z)`, `z ∈ [-1,1]`, as in lines 5926-5950).

Norms (`R = ε⁻¹`, `c = ν⁻²`, `g(s) = e^{γs/(1+νs)}`, lines 5116-5117; the normalized
`Y_2` norms of the lifts, lines 2681-2689):

* `Str` carries the gain norm `‖T‖ = ‖g⁻¹T‖_Z` (`A = ‖T‖`, lines 5118-5128, 5609);
* `Vel` carries the *gained* (`g⁻¹`-weighted) normalized body norm `‖w‖ = R⁻¹‖g⁻¹w‖_{Y_2}`
  (`G(w) = ‖w‖`, lines 5143, 5527-5531);
* `Src` (body forces) carries the *ungained* normalized body norm `‖f‖ = R⁻¹‖f‖_{Y_2}`: the
  factor `R⁻¹ = ε` of the source estimates for `F_A, E_A, 𝔯_A` (5009-5016), the body errors
  (5250, 5291, 5501, 5512) and the near-solver bound `‖g⁻¹M_U R_μ f‖_Z ≤ P_ν R⁻¹‖f‖_{Y_2}`
  (5542) is part of the norm of `Src`, not a separate factor;
* `Grd` (the gradient `∇ĥ_A` of the affine lift, a `3×3` tensor field) carries the ungained
  normalized norm `R⁻¹‖·‖_{Y_2}` (5009-5016, 5078-5079);
* `Gam = 𝓔_ν` carries the pair norm `A + e^{-a/ν} G` with `a = γ/8` (lines 5640-5662).

(Concrete realization: `Concrete/ReturnOps.lean` (`VelG`, `SrcG`, `StrG`, `PairSp`) and
`Concrete/AffineBoundSpaces.lean` (`GrdG`).)
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

/-- A sequence of regimes: the phase-locked viscosities `ν_n`, and for each `n`, `z ∈ [-1,1]`
the operators at `μ_n(z)` on fixed spaces (lines 5926-5950).

Besides the operators `ops n z : ReturnOps …` of the exact return system, a regime carries the
gradient `gradhA n z : A ↦ ∇ĥ_A` of the physical affine lift `ĥ_A = (ops n z).hA A`
(lines 4991-4997), valued in the tensor space `Grd n` with the normalized norm `R⁻¹‖·‖_{Y_2}`;
it enters the first line of `ret:general-affine-bounds` (lines 5009-5016).  It is not a field
of `ReturnOps` because the closing argument (lines 5785-5833) never uses it.  In a concrete
instance it must be the physical spatial gradient of the pinned `ĥ_A` (ring-chart rules
5036-5039, `r = R/√s`, lines 4163, 4996-4997). -/
structure ReturnSeq where
  Vel : ℕ → Type
  Str : ℕ → Type
  Src : ℕ → Type
  Aff : ℕ → Type
  Gam : ℕ → Type
  Grd : ℕ → Type
  [iVel : ∀ n, NormedAddCommGroup (Vel n)]
  [sVel : ∀ n, NormedSpace ℝ (Vel n)]
  [iStr : ∀ n, NormedAddCommGroup (Str n)]
  [sStr : ∀ n, NormedSpace ℝ (Str n)]
  [iSrc : ∀ n, NormedAddCommGroup (Src n)]
  [sSrc : ∀ n, NormedSpace ℝ (Src n)]
  [iAff : ∀ n, NormedAddCommGroup (Aff n)]
  [sAff : ∀ n, NormedSpace ℝ (Aff n)]
  [cAff : ∀ n, CompleteSpace (Aff n)]
  [iGam : ∀ n, NormedAddCommGroup (Gam n)]
  [sGam : ∀ n, NormedSpace ℝ (Gam n)]
  [cGam : ∀ n, CompleteSpace (Gam n)]
  [iGrd : ∀ n, NormedAddCommGroup (Grd n)]
  [sGrd : ∀ n, NormedSpace ℝ (Grd n)]
  ν : ℕ → ℝ
  ops : ∀ n, ℝ → ReturnOps (Vel n) (Str n) (Src n) (Aff n) (Gam n)
  /-- `A ↦ ∇ĥ_A` at `μ = μ_n(z)` (lines 4991-4997, 5009-5016). -/
  gradhA : ∀ n, ℝ → (Aff n →ₗ[ℝ] Grd n)

attribute [instance] ReturnSeq.iVel ReturnSeq.sVel ReturnSeq.iStr ReturnSeq.sStr
  ReturnSeq.iSrc ReturnSeq.sSrc ReturnSeq.iAff ReturnSeq.sAff ReturnSeq.cAff
  ReturnSeq.iGam ReturnSeq.sGam ReturnSeq.cGam ReturnSeq.iGrd ReturnSeq.sGrd

/-- `A_* = ε³ 𝒜_ν = ε³ |N_ν| ν^{5+2μ}` (lines 4565-4570, with `c = ν⁻²`), at `μ = μ_n(z)`. -/
def Astar (lam κ : ℂ) (Cσ : ℂ) (σ₀ ν z : ℝ) : ℝ :=
  epsCube lam.re κ σ₀ Cσ ν * ‖Nnu lam κ ν‖ * ν ^ (5 + 2 * muWin σ₀ ν z)

/-! ## Module `ward-identity.tex` (lines 4133-4332) -/

/-- Support (line 4311): `χ_o M (Y + h) = 0`, `χ_o` the outward cutoff acting on stresses
(`χ_o = 0` for `s ≤ 1.2/ν`, `= 1` for `s ≥ 1.5/ν`, line 4160). -/
def WardSupportZero {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str) : Prop :=
  ∀ T, chiO (o.M (o.Yf T + o.hf T)) = 0

/-- The change of unknown depends only on old data (lines 4314-4319, 5813-5814): "`H_o`
depends only on `χ_oT`", in kernel form `χ_oT = 0 → HT = 0`.  The source does not assert
`HT = H(χ_oT)`: `χ_o = χ̂_o(νs)` is a smooth cutoff with values in `[0,1]`, not idempotent, and
the Ward fields `Y[T], h[T]` are built from `W_μ = -S_μ(χ_oT)` (line 4171).  With the young
support `HYoungSupport` this gives `H² = 0` (`hNilpotent_of_support`, WardProofs).  The same
definition is `Concrete.HOldKernel` (Concrete/PhysLayer.lean), reduced there to the pins of the
concrete instance (`ReturnBase.hOldKernel_of`). -/
def HOldKernel {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str) : Prop :=
  ∀ T, chiO T = 0 → o.Hop T = 0

/-- The change of unknown has young support (lines 4314-4319, 5813-5814): `χ_o H T = 0`. -/
def HYoungSupport {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str) : Prop :=
  ∀ T, chiO (o.Hop T) = 0

/-- Free resolvent data of the Ward section (lines 4143-4200): `D_μ`, `R_μ = D_μ⁻¹`, the shifted
`D_{μ+1} = D_μ + I`, `R_{μ+1}`, the stress-to-velocity inverses `S_μ = R_μ ℙ div`,
`S_{μ+1} = R_{μ+1} ℙ div`, the outward cutoff `χ_o` and the solenoidal stream cutoff `𝒞_y`. -/
structure WardFields (Vel Str : Type) [AddCommGroup Vel] [Module ℝ Vel]
    [AddCommGroup Str] [Module ℝ Str] where
  Dmu : Vel →ₗ[ℝ] Vel
  Rmu : Vel →ₗ[ℝ] Vel
  Rmu1 : Vel →ₗ[ℝ] Vel
  Pdiv : Str →ₗ[ℝ] Vel
  chiO : Str →ₗ[ℝ] Str
  Cy : Vel →ₗ[ℝ] Vel

namespace WardFields

variable {Vel Str : Type} [AddCommGroup Vel] [Module ℝ Vel] [AddCommGroup Str] [Module ℝ Str]
  (F : WardFields Vel Str)

/-- `D_{μ+1} = D_μ + I`. -/
def Dmu1 : Vel →ₗ[ℝ] Vel := F.Dmu + LinearMap.id

/-- `W_μ = -S_μ(χ_o T)`, `W_{μ+1} = -S_{μ+1}(χ_o T)` (line 4171). -/
def W (T : Str) : Vel := -(F.Rmu (F.Pdiv (F.chiO T)))
def W1 (T : Str) : Vel := -(F.Rmu1 (F.Pdiv (F.chiO T)))
/-- `X₀ = W_μ - W_{μ+1}`, `X = 𝒞_y X₀`, `Y = D_{μ+1} X` (line 4171-4172). -/
def X0 (T : Str) : Vel := F.W T - F.W1 T
def Y (T : Str) : Vel := F.Dmu1 (F.Cy (F.X0 T))

/-- The free resolvent hypotheses: `R_μ`, `R_{μ+1}` are two-sided inverses of `D_μ`, `D_{μ+1}`. -/
def IsFreeResolvent : Prop :=
  (∀ v, F.Dmu (F.Rmu v) = v) ∧ (∀ v, F.Rmu (F.Dmu v) = v) ∧
  (∀ v, F.Dmu1 (F.Rmu1 v) = v) ∧ (∀ v, F.Rmu1 (F.Dmu1 v) = v)

/-- `ward:shifted-resolvent` (lines 4199-4201): `X₀ = R_{μ+1} W_μ`, `D_{μ+1} X₀ = W_μ`. -/
def ShiftedResolvent : Prop := ∀ T, F.X0 T = F.Rmu1 (F.W T) ∧ F.Dmu1 (F.X0 T) = F.W T

/-- `ward:cutoff-source` (lines 4203-4205):
`Y = 𝒞_y W_μ + [D_{μ+1}, 𝒞_y] X₀`. -/
def CutoffSource : Prop :=
  ∀ T, F.Y T = F.Cy (F.W T) + (F.Dmu1 (F.Cy (F.X0 T)) - F.Cy (F.Dmu1 (F.X0 T)))

end WardFields

/-! ## Module `return/physical-affine.tex` (lines 4951-5110)

`ReturnOps.PhysAffineIdentity` (Return.lean) is the identity of Lemma `ret:physical-affine`.
The bounds `ret:general-affine-bounds` (lines 5009-5016), on `μ = μ_n(z)`, for `0 < ε, ν ≤ 1`:
`R⁻¹(‖F_A‖_{Y_2} + ‖E_A‖_{Y_2} + ‖ĥ_A‖_{Y_2} + ‖∇ĥ_A‖_{Y_2}) ≤ P_ν M(A)` and
`R⁻¹‖𝔯_A‖_{Y_2} ≤ P_ν (ε + δ_base + δ_U) M(A)`, `P_ν = C ν^{-k}`.

Norm reading (module header): the factor `R⁻¹` is part of the norms of `Src` (for `F_A`, `E_A`,
`𝔯_A`) and of `Grd` (for `∇ĥ_A = S.gradhA n z A`).  `ĥ_A` is measured in the gained norm of
`Vel`, `R⁻¹‖g⁻¹ĥ_A‖_{Y_2}`; since `g ≥ 1` on the age range, this term is bounded by the source's
ungained `R⁻¹‖ĥ_A‖_{Y_2}`, so the first line below is implied by the source's first line.
`MA n : Aff n → ℝ` is `M(A) = sup_{0<s≤1.1/ν} s^{-5/2} Σ_{j≤6}|(s∂_s)^j(χ_f A)(s)|` (lines
4955-4962; concrete form `Concrete.affM` in `Concrete/AffineBoundSpaces.lean`), and `eps`,
`dBase`, `dU` are the sequences `ε_n = R_n⁻¹` (line 5945), `δ_base` (lines 4371, 5018-5020) and
`δ_U = ‖U - U_raw‖_{W^{1,∞}}` (line 5008).  The stronger weighted force estimate
`R⁻¹‖g⁻¹F_A‖_{Y_2} ≤ P_ν‖A‖_𝒜` (lines 5099-5103) is a separate remark of the source, not part of
this display. -/
def GeneralAffineBounds (S : ReturnSeq) (MA : ∀ n, S.Aff n → ℝ) (eps dBase dU : ℕ → ℝ) :
    Prop :=
  ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, 0 < eps n → eps n ≤ 1 → 0 < S.ν n → S.ν n ≤ 1 →
    ∀ z ∈ Icc (-1 : ℝ) 1, ∀ A : S.Aff n,
    ‖(S.ops n z).FA A‖ + ‖(S.ops n z).EA A‖ + ‖(S.ops n z).hA A‖ + ‖S.gradhA n z A‖ ≤
        C * (S.ν n)⁻¹ ^ k * MA n A ∧
    ‖(S.ops n z).rA A‖ ≤ C * (S.ν n)⁻¹ ^ k * (eps n + dBase n + dU n) * MA n A

/-! ## Module `return/source-class.tex` (lines 4733-4950) -/

/-- `source-class:flat-limit` (lines 4821-4845): uniformly for `μ ∈ K` (here `μ = μ_n(z)`),
`‖𝒦^flat - a_μ Λ‖ ≤ C A_*[ν + η_ν + ω_can + P e^{-γ'/√ν} + P e^{-4a_s/(5ν)}]`
(`η_ν = O(ν)` is absorbed in the first term), `‖a_μ‖ ≤ C`, `‖Λ‖ ≤ C A_*`, and
`Λ(a_μ) = 2ε³ν^{5+2μ} Re[𝒞(μ) N_ν] + O(A_* P e^{-b/ν})`. -/
def FlatLimit (S : ReturnSeq) (lam κ ell : ℂ) (J : ℂ → ℂ) (σ₀ a_s : ℝ) : Prop :=
  ∃ (ωcan : ℕ → ℝ) (C : ℝ) (k : ℕ) (γ' b : ℝ) (N : ℕ),
    Tendsto ωcan atTop (𝓝 0) ∧ 0 < γ' ∧ γ' < lam.re ∧ 0 < b ∧
    ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      ‖(S.ops n z).Kflat - (S.ops n z).Lam.smulRight (S.ops n z).aMu‖ ≤
        C * Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z *
          (S.ν n + ωcan n + (S.ν n)⁻¹ ^ k * Real.exp (-γ' / Real.sqrt (S.ν n))
            + (S.ν n)⁻¹ ^ k * Real.exp (-(4 * a_s / 5) / S.ν n)) ∧
      ‖(S.ops n z).aMu‖ ≤ C ∧
      ‖(S.ops n z).Lam‖ ≤ C * Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z ∧
      |(S.ops n z).Lam (S.ops n z).aMu -
          unitResp lam κ (mellinC lam ell J)
            (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) (S.ν n)) (S.ν n)
            (muWin σ₀ (S.ν n) z)| ≤
        C * Astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ (S.ν n) z *
          (S.ν n)⁻¹ ^ k * Real.exp (-b / S.ν n)

/-! ## Module `repair/proposition.tex` and the budget (lines 5111-5707, 5835-5920) -/

/-- Lines 5883-5890 (`closure:source-and-extraction`): `‖𝒫‖_{𝒜→𝓔} ≤ P_ν e^{1.1a_s/ν}` and
`‖L‖_{𝓔→𝒜} ≤ P_ν`. -/
def PLBound (S : ReturnSeq) (a_s : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
    ‖(S.ops n z).P‖ ≤ C * (S.ν n)⁻¹ ^ k * Real.exp (1.1 * a_s / S.ν n) ∧
    ‖(S.ops n z).Lg‖ ≤ C * (S.ν n)⁻¹ ^ k

/-- Lines 5896-5899: the curved loop `L𝒫` is exponentially close to the flat return:
`‖L𝒫 - 𝒦^flat‖ ≤ P_ν e^{-(c_N - 1.1a_s)/ν}` for the given `c_N > 0` (the body-column comparison,
from `near:equation-comparison` and the forced-column comparison, lines 4084-4132). -/
def CurvedFlatComparison (S : ReturnSeq) (a_s cN : ℝ) : Prop :=
  0 < cN ∧ ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
    ‖(S.ops n z).Lg ∘L (S.ops n z).P - (S.ops n z).Kflat‖ ≤
      C * (S.ν n)⁻¹ ^ k * Real.exp (-(cN - 1.1 * a_s) / S.ν n)

/-- `repair:complete-graph-error` / `closure:Q-small` (lines 5666-5686, 5869-5871):
`‖𝒬‖_{𝓔_ν → 𝓔_ν} ≤ P_ν e^{-γ/(100ν)}`. -/
def QSmall (S : ReturnSeq) (γ : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
    ‖(S.ops n z).Q‖ ≤ C * (S.ν n)⁻¹ ^ k * Real.exp (-(γ / 100) / S.ν n)

/-- The error-family bounds of the repair section (lines 5622-5660): there are
`δ_A = P e^{-(γ/15-ω_b-3m₀/2)/ν}`, `δ_G = P e^{-(19γ/66-ω_b-3m₀/2)/ν}`,
`χ_A = P e^{(γ/10+ω_b+3m₀/2)/ν}`, `χ_G = P e^{-(31γ/165-ω_b-3m₀/2)/ν}` with, for the error
velocity `v_Q(T)` of every `V = (T,w) ∈ 𝓔_ν`,
`‖M v_Q(T)‖ ≤ δ_A‖T‖ + δ_G‖w‖` and `‖v_Q(T)‖ ≤ χ_A‖T‖ + χ_G‖w‖`. -/
def ErrorFamilyBounds (S : ReturnSeq) (γ ωb m0 : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ V : S.Gam n,
    ‖(S.ops n z).M ((S.ops n z).vQ ((S.ops n z).Tc V))‖ ≤
      C * (S.ν n)⁻¹ ^ k * Real.exp (-(γ / 15 - ωb - 3 * m0 / 2) / S.ν n) *
          ‖(S.ops n z).Tc V‖ +
      C * (S.ν n)⁻¹ ^ k * Real.exp (-(19 * γ / 66 - ωb - 3 * m0 / 2) / S.ν n) *
          ‖(S.ops n z).wc V‖ ∧
    ‖(S.ops n z).vQ ((S.ops n z).Tc V)‖ ≤
      C * (S.ν n)⁻¹ ^ k * Real.exp ((γ / 10 + ωb + 3 * m0 / 2) / S.ν n) *
          ‖(S.ops n z).Tc V‖ +
      C * (S.ν n)⁻¹ ^ k * Real.exp (-(31 * γ / 165 - ωb - 3 * m0 / 2) / S.ν n) *
          ‖(S.ops n z).wc V‖

/-- The direct near solver (lines 5540-5547): `‖D_N⁻¹‖ ≤ P_ν`, `‖S_N‖ ≤ P_ν e^{η_δ/ν}`, in the
gain norms, and the pair norm of `𝓔_ν` (lines 5640-5662, with `a = γ/8`). -/
def PairNormAndNearSolver (S : ReturnSeq) (γ ηδ : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
    (∀ T, ‖(S.ops n z).DNinv T‖ ≤ C * (S.ν n)⁻¹ ^ k * ‖T‖) ∧
    (∀ T, ‖(S.ops n z).SN T‖ ≤ C * (S.ν n)⁻¹ ^ k * Real.exp (ηδ / S.ν n) * ‖T‖) ∧
    (∀ V : S.Gam n, ‖V‖ = ‖(S.ops n z).Tc V‖ +
        Real.exp (-(γ / 8) / S.ν n) * ‖(S.ops n z).wc V‖)

end UnforcedLeray.Short.PartIIIb
