import UnforcedLeray.Short.PartIIa.Sub.R02

/-!


Target: `profileCommutators` proves `ProfileCommutators` (`Short/PartII-a/Sub/R02.lean`, line 314),
the clause `comm` of `LateIngredients`.

Source of record: `the November 2 reference manuscript`, lines 1259-1276 (the late
residual table, which uses the commutators of `K = η∂_η + 2s∂_s` with `∂_η`, `∂_q`, `∂_s`). The
operator `K` is `ageOperator` (`Units/B0184.lean`, lines 63-72).

Statement (no hypothesis beyond `f` of class `C²` at the point `x`):
* `K(∂_η f) = ∂_η(Kf) - ∂_η f`, that is `[K, ∂_η] = -∂_η`;
* `K(∂_q f) = ∂_q(Kf)`, that is `[K, ∂_q] = 0` (this is `partialQ_ageOperator`, INF31 of B0188);
* `∂_s(Kf) = K(∂_s f) + 2∂_s f`, that is `[∂_s, K] = 2∂_s`.

Proof route. Write `H = fderiv (fderiv f) x` for the second derivative at `x`, which exists because
`f` is `C²` at `x`. Differentiating `Kf = η·∂_η f + 2s·∂_s f` at `x` gives its derivative in an
arbitrary direction (`commut_fderiv_ageOperator`). The derivatives of `∂_η f` and `∂_s f` are `H`
applied to `eηDir` and `esDir` (`commut_fderiv_partialEta`, `commut_fderiv_partialAge`). The only
non-formal input is the mixed-partial symmetry `H v w = H w v` (`ContDiffAt.isSymmSndFDerivAt`),
which gives `∂_η∂_s f = ∂_s∂_η f` (`commut_partialEta_partialAge`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188

/-- The derivative of `K f` at a point where `f` is `C²`, in an arbitrary direction `w`:
`D(Kf)(x) w = w_η ∂_η f(x) + η D(∂_η f)(x) w + 2 (w_s ∂_s f(x) + s D(∂_s f)(x) w)`, where
`x = (q, (η, s))`. -/
theorem commut_fderiv_ageOperator {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) (w : ProfilePoint) :
    fderiv ℝ (ageOperator f) x w =
      w.2.1 * partialEta f x + x.2.1 * fderiv ℝ (partialEta f) x w +
        2 * (w.2.2 * partialAge f x + x.2.2 * fderiv ℝ (partialAge f) x w) := by
  have he : HasFDerivAt (partialEta f) (fderiv ℝ (partialEta f) x) x :=
    (differentiableAt_partialEta hf).hasFDerivAt
  have hs : HasFDerivAt (partialAge f) (fderiv ℝ (partialAge f) x) x :=
    (differentiableAt_partialAge hf).hasFDerivAt
  have hK := ((hasFDerivAt_eta x).fun_mul he).fun_add
    (((hasFDerivAt_age x).const_mul 2).fun_mul hs)
  have hK' : HasFDerivAt (ageOperator f) _ x := hK
  rw [hK'.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  ring

/-- The derivative of `∂_η f` at a point where `f` is `C²`: `D(∂_η f)(x) w = H w eηDir`. -/
theorem commut_fderiv_partialEta {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) (w : ProfilePoint) :
    fderiv ℝ (partialEta f) x w = fderiv ℝ (fderiv ℝ f) x w eηDir := by
  have hd := differentiableAt_fderiv_of_contDiffAt hf
  have h := (hasFDerivAt_fderiv_apply hd eηDir).fderiv
  show fderiv ℝ (fun y => fderiv ℝ f y eηDir) x w = _
  rw [h, ContinuousLinearMap.flip_apply]

/-- The derivative of `∂_s f` at a point where `f` is `C²`: `D(∂_s f)(x) w = H w esDir`. -/
theorem commut_fderiv_partialAge {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) (w : ProfilePoint) :
    fderiv ℝ (partialAge f) x w = fderiv ℝ (fderiv ℝ f) x w esDir := by
  have hd := differentiableAt_fderiv_of_contDiffAt hf
  have h := (hasFDerivAt_fderiv_apply hd esDir).fderiv
  show fderiv ℝ (fun y => fderiv ℝ f y esDir) x w = _
  rw [h, ContinuousLinearMap.flip_apply]

/-- Mixed partials commute at a point where `f` is `C²`: `∂_η∂_s f = ∂_s∂_η f`. -/
theorem commut_partialEta_partialAge {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) :
    partialEta (partialAge f) x = partialAge (partialEta f) x := by
  have hsym : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  show fderiv ℝ (partialAge f) x eηDir = fderiv ℝ (partialEta f) x esDir
  rw [commut_fderiv_partialAge hf eηDir, commut_fderiv_partialEta hf esDir]
  exact hsym eηDir esDir

/-- `∂_η(Kf) = ∂_η f + η∂_η∂_η f + 2s∂_η∂_s f` at a point where `f` is `C²`. -/
theorem commut_partialEta_ageOperator {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) :
    partialEta (ageOperator f) x =
      partialEta f x + x.2.1 * partialEta (partialEta f) x +
        2 * x.2.2 * partialEta (partialAge f) x := by
  show fderiv ℝ (ageOperator f) x eηDir =
    partialEta f x + x.2.1 * fderiv ℝ (partialEta f) x eηDir +
      2 * x.2.2 * fderiv ℝ (partialAge f) x eηDir
  rw [commut_fderiv_ageOperator hf eηDir]
  simp only [eηDir]
  ring

/-- `∂_s(Kf) = η∂_s∂_η f + 2∂_s f + 2s∂_s∂_s f` at a point where `f` is `C²`. -/
theorem commut_partialAge_ageOperator {f : ProfilePoint → ℝ} {x : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f x) :
    partialAge (ageOperator f) x =
      x.2.1 * partialAge (partialEta f) x + 2 * partialAge f x +
        2 * x.2.2 * partialAge (partialAge f) x := by
  show fderiv ℝ (ageOperator f) x esDir =
    x.2.1 * fderiv ℝ (partialEta f) x esDir + 2 * partialAge f x +
      2 * x.2.2 * fderiv ℝ (partialAge f) x esDir
  rw [commut_fderiv_ageOperator hf esDir]
  simp only [esDir]
  ring

/-- **Target.** Commutators of `K = η∂_η + 2s∂_s` with the profile derivatives, at every point where
the profile is `C²`: `[K, ∂_η] = -∂_η`, `[K, ∂_q] = 0`, and `∂_s(Kf) = K(∂_s f) + 2∂_s f`. -/
theorem profileCommutators : ProfileCommutators := by
  unfold ProfileCommutators
  intro f x hf
  refine ⟨?_, (partialQ_ageOperator hf).symm, ?_⟩
  · rw [commut_partialEta_ageOperator hf, commut_partialEta_partialAge hf]
    unfold ageOperator
    ring
  · rw [commut_partialAge_ageOperator hf]
    unfold ageOperator
    rw [commut_partialEta_partialAge hf]
    ring

end UnforcedLeray.Short.PartIIa
