import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2

/-!
# `PartIII-a:T21/2/7/2/1`: `AdjointWeakSmoothVersion` from interior smoothing and the endpoint

Source: `the November 2 reference manuscript` (SP) lines 3060-3061 (reverse-time
adjoint `-∂_rφ = νΔφ + v·∇φ - K_c^T(φ∇E)`, smooth coefficients, nonlocal term of order `-1`),
3052-3058 (localized term maps `X_{-m}` to `H^1_{-m}`), 270-288 (the train: the unique global mild
solution in `BUC`, smooth for positive time).

Both statements are for the BUC train (`PartI.IsBUCTrain`) with the bounds `LadTrainBdd`, as
`AdjointWeakSmoothVersion` (`Sub/PartIIIa_T21_2_7_2.lean`): `C^∞` in the age needs every weighted
space-time jet of the train (the age derivatives of `K_c^T(φ∇E)`, SP 3052-3058), which `LadTrainBdd`
does not record (`PartIII-a:T21/2/7/2/1/1/1/org`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Interior parabolic regularity** (SP 3060-3061): for `ν ≤ 1`, a BUC train (`PartI.IsBUCTrain`,
SP 270-288) with `LadTrainBdd`, and a weak adjoint `φ`, there is a version `φ'` (equal to `φ r` a.e.
for `r ∈ (t, s)`) jointly `C^∞` on `(t, s) × ℝ²`. (Weak identity + `strongCont` give the
distributional equation; the coefficients `v` are smooth, `K_c^T(φ∇E) ∈ H^1_loc`; bootstrap `H^k_loc`
estimates and Sobolev embedding.) -/
def AdjointInteriorSmooth (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∃ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] φ r) ∧
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ)

/-- **Regularity up to the age `t`** (SP 3060: the reverse-time evolution runs from `s` down to
`t`, so `t` is the end of the evolution and parabolic smoothing holds up to it): for `ν ≤ 1` and a
BUC train (`PartI.IsBUCTrain`, SP 270-288) with `LadTrainBdd`, a version smooth on `(t, s) × ℝ²` of
a weak adjoint can be replaced by a version smooth on `[t, s) × ℝ²` (the weak identity on `[t, r]`
with `strongCont` at `t`; the weak solution is the restriction of a solution on a slightly larger
interval of the smooth train, or one-sided interior estimates). -/
def AdjointEndpointSmooth (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ G : ℝ × ℝ → ℂ,
      MemLp G 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (-m)) →
      ∀ φ : ℝ → ℝ × ℝ → ℂ,
        IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s (physAdj (clockA ν s) G) φ →
        ∀ φ' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ioo t s, φ' r =ᵐ[volume] φ r) →
          ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ) →
          ∃ φ'' : ℝ → ℝ × ℝ → ℂ, (∀ r ∈ Ico t s, φ'' r =ᵐ[volume] φ r) ∧
            ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ'' p.1 p.2) (Ico t s ×ˢ univ)

/-- `AdjointWeakSmoothVersion` from interior smoothing and the endpoint. -/
theorem adjointWeakSmoothVersion_of (m : ℝ) (h1 : AdjointInteriorSmooth m)
    (h2 : AdjointEndpointSmooth m) : AdjointWeakSmoothVersion m := by
  intro ν hν hν1 tr htr hb t s ht hts G hG φ hφ
  obtain ⟨φ', h', hs⟩ := h1 ν hν hν1 tr htr hb t s ht hts G hG φ hφ
  exact h2 ν hν hν1 tr htr hb t s ht hts G hG φ hφ φ' h' hs

end UnforcedLeray.Short.IIIa
