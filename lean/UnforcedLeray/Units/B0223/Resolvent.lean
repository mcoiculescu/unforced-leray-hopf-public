import UnforcedLeray.Units.B0223.Semigroup
import UnforcedLeray.Units.B0223.Lift

/-!
# B0223 helper: the resolvent as a Laplace transform, its conjugation to `H`, its inverse property

Blueprint unit B0223 (label `eq:st18-t00116`), `paper/main.tex` lines 3355–3368.


§4, INF07): no generator theory is developed; the resolvent is the Laplace transform
`R(μ) = ∫_0^∞ e^{-μt} S(t) dt` of the explicit semigroup (`Infra.ExpSemigroup.laplace`), and
"`R(μ) = (μ - A)^{-1}`" is expressed on the graph of the generator, read off from the orbits:
`IsGenPair S x y` means `d/dt S(t)x = S(t)y` for `t > 0` (for a strongly continuous semigroup
this is exactly `x ∈ dom A`, `Ax = y`). The core lemma `laplace_leftInverse'` and the
derivative `hasDerivAt_T_laplace` of `Lib/Semigroups/Laplace.lean` give both inverse identities.

Conjugation to `H` by an isometry `J : H → L²` (tex line 3363, "conjugated to `H` by `J_ε`"):
`compress J R = J† R J`. It always satisfies `‖J† R J‖ ≤ ‖R‖`, is holomorphic with `R`, and is a
left inverse of `μ - A_H` on the conjugated generator graph `{(b, c) : IsGenPair S (Jb) (Jc)}`
(the conjugate of the generator, as in B0221 `AepsOp` / B0222 `AepsVecOp`). If the semigroup
maps the range of `J` (the axisymmetric fields) into itself (`LiftInvariant`), then
`J (J† R J) = R J` and `J† R J` is also a right inverse.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0223

open UnforcedLeray.Infra

section Generic

variable {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The conjugate `J† R J` of an operator `R` on `Y` by an isometry `J : H → Y`. -/
def compress (J : H →ₗᵢ[ℂ] Y) (R : Y →L[ℂ] Y) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint J.toContinuousLinearMap ∘L R ∘L J.toContinuousLinearMap

theorem compress_apply (J : H →ₗᵢ[ℂ] Y) (R : Y →L[ℂ] Y) (b : H) :
    compress J R b = ContinuousLinearMap.adjoint J.toContinuousLinearMap (R (J b)) := rfl

/-- `J† J = 1` for an isometry. -/
theorem adjoint_lift_apply (J : H →ₗᵢ[ℂ] Y) (b : H) :
    ContinuousLinearMap.adjoint J.toContinuousLinearMap (J b) = b := by
  refine ext_inner_right ℂ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact J.inner_map_map b v

theorem norm_compress_le (J : H →ₗᵢ[ℂ] Y) (R : Y →L[ℂ] Y) : ‖compress J R‖ ≤ ‖R‖ := by
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 := J.norm_toContinuousLinearMap_le
  have hJa : ‖ContinuousLinearMap.adjoint J.toContinuousLinearMap‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact hJ
  calc ‖compress J R‖ ≤ ‖ContinuousLinearMap.adjoint J.toContinuousLinearMap‖ *
        (‖R‖ * ‖J.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖R‖ * 1) := by gcongr
    _ = ‖R‖ := by ring

theorem differentiableOn_compress (J : H →ₗᵢ[ℂ] Y) {R : ℂ → Y →L[ℂ] Y} {s : Set ℂ}
    (hR : DifferentiableOn ℂ R s) : DifferentiableOn ℂ (fun μ => compress J (R μ)) s :=
  (differentiableOn_const _).clm_comp (hR.clm_comp (differentiableOn_const _))

/-- The graph of the generator of `S`, read off from the orbits: `d/dt S(t)x = S(t)y`, `t > 0`. -/
def IsGenPair (S : ExpSemigroup Y) (x y : Y) : Prop :=
  ∀ t : ℝ, 0 < t → HasDerivAt (fun t => S.T t x) (S.T t y) t

/-- **Left inverse**: `R(μ)(μx - Ax) = x` on the generator graph. -/
theorem laplace_left (S : ExpSemigroup Y) {μ : ℂ} (hμ : S.ω < μ.re) {x y : Y}
    (h : IsGenPair S x y) : S.laplace μ (μ • x - y) = x :=
  S.laplace_leftInverse' hμ h

/-- **Right inverse**: `R(μ)z` lies in the generator graph with `A R(μ)z = μ R(μ)z - z`. -/
theorem laplace_right (S : ExpSemigroup Y) {μ : ℂ} (hμ : S.ω < μ.re) (z : Y) :
    IsGenPair S (S.laplace μ z) (μ • S.laplace μ z - z) :=
  fun _ ht => S.hasDerivAt_T_laplace hμ z ht

/-- **Invariance of the lifted fields.** `S(t)` maps the range of the lift `J` (the
axisymmetric fields of the given type) into itself. For `S_ε(t)` this is the commutation with
the isometries of `ℝ³` fixing the `e₃` axis, used at tex lines 3341–3347 ("they are the
conjugates"); it is proved in `B0223/Invariance.lean` (`liftInvariant_sc`, scalar lift) and
`B0223/VecInvariance.lean` (`liftInvariant_vec`, meridional lift). -/
def LiftInvariant (S : ExpSemigroup Y) (J : H →ₗᵢ[ℂ] Y) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ b : H, ∃ b' : H, S.T t (J b) = J b'

/-- The Laplace formula of the conjugated resolvent:
`J† R(μ) J b = ∫_0^∞ e^{-μt} J† S(t) J b dt`. -/
theorem compress_laplace_apply (S : ExpSemigroup Y) (J : H →ₗᵢ[ℂ] Y) {μ : ℂ}
    (hμ : S.ω < μ.re) (b : H) :
    compress J (S.laplace μ) b = ∫ t in Ioi (0 : ℝ), Complex.exp (-(μ * t)) •
      ContinuousLinearMap.adjoint J.toContinuousLinearMap (S.T t (J b)) := by
  rw [compress_apply, S.laplace_apply' hμ,
    ← (ContinuousLinearMap.adjoint J.toContinuousLinearMap).integral_comp_comm
      (S.integrableOn_lapInt hμ (J b))]
  simp only [ExpSemigroup.lapInt_def, map_smul]

/-- Under `LiftInvariant`, `J (J† R(μ) J) = R(μ) J`: the conjugate is a genuine conjugation. -/
theorem lift_compress_laplace (S : ExpSemigroup Y) (J : H →ₗᵢ[ℂ] Y) (hS : LiftInvariant S J)
    {μ : ℂ} (hμ : S.ω < μ.re) (b : H) :
    J (compress J (S.laplace μ) b) = S.laplace μ (J b) := by
  set Q : Y →L[ℂ] Y := J.toContinuousLinearMap ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
  have hQ : ∀ t, 0 ≤ t → Q (S.T t (J b)) = S.T t (J b) := by
    intro t ht
    obtain ⟨b', hb'⟩ := hS t ht b
    rw [hb']
    change J (ContinuousLinearMap.adjoint J.toContinuousLinearMap (J b')) = J b'
    rw [adjoint_lift_apply]
  change Q (S.laplace μ (J b)) = _
  rw [S.laplace_apply' hμ, ← Q.integral_comp_comm (S.integrableOn_lapInt hμ (J b))]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [ExpSemigroup.lapInt_def, map_smul]
  rw [hQ t (le_of_lt ht)]

/-- **Left inverse on `H`**: on the conjugated generator graph, `J† R(μ) J (μ b - c) = b`. -/
theorem compress_left (S : ExpSemigroup Y) (J : H →ₗᵢ[ℂ] Y) {μ : ℂ} (hμ : S.ω < μ.re)
    {b c : H} (h : IsGenPair S (J b) (J c)) : compress J (S.laplace μ) (μ • b - c) = b := by
  rw [compress_apply, map_sub, map_smul, laplace_left S hμ h, adjoint_lift_apply]

/-- **Right inverse on `H`** (under `LiftInvariant`): `J† R(μ) J z` lies in the conjugated
generator graph, with image `μ J† R(μ) J z - z`. -/
theorem compress_right (S : ExpSemigroup Y) (J : H →ₗᵢ[ℂ] Y) (hS : LiftInvariant S J) {μ : ℂ}
    (hμ : S.ω < μ.re) (z : H) :
    IsGenPair S (J (compress J (S.laplace μ) z))
      (J (μ • compress J (S.laplace μ) z - z)) := by
  rw [map_sub, map_smul, lift_compress_laplace S J hS hμ z]
  exact laplace_right S hμ (J z)

end Generic

end UnforcedLeray.B0223
