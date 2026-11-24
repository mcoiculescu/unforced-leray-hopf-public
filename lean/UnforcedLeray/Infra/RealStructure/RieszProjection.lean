import UnforcedLeray.Infra.RealStructure.Riesz
import UnforcedLeray.Infra.RieszProjection.Basic

/-!
# Real structure and the Riesz projections of `Infra/RieszProjection`

Bridge to the definitions of `UnforcedLeray.Infra.RieszProjection` (`RieszProjection/Basic.lean`):
`rieszProj T r = (2πi)⁻¹ ∮_{|z|=r} (z - T)⁻¹ dz` (the projection `P_-` of `paper/main.tex`,
line 359), the contour operators `contourOp T r f` and the outer inverse `rieszOuterInv T r`
(`𝓜_+⁻¹`, line 366). For `T` commuting with a conjugation `J`:

* `CommutesWith.rieszProj_commutesWith`, `CommutesWith.one_sub_rieszProj_commutesWith`:
  `P_-` and `P_+ = 1 - P_-` commute with `J`;
* `CommutesWith.rieszProj_mem_fixedSubmodule`, `…one_sub_rieszProj_mem_fixedSubmodule`:
  **both projections preserve real fields** (manuscript line 361);
* `CommutesWith.contourOp_commutesWith`: the same for `contourOp T r f` with `f` real on real
  arguments (`conj (f (conj z)) = f z`), in particular `CommutesWith.rieszOuterInv_commutesWith`
  for `f z = z⁻¹`.

No hypothesis on the circle is needed for these identities.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate

namespace UnforcedLeray.Infra.RealStructure

namespace Conjugation

open UnforcedLeray.Infra.RieszProjection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {J : Conjugation X}

theorem rieszProj_eq_rieszIntegral (T : X →L[ℂ] X) (r : ℝ) :
    rieszProj T r = rieszIntegral T 0 r := rfl

theorem contourOp_eq_dunfordIntegral (T : X →L[ℂ] X) (r : ℝ) (f : ℂ → ℂ) :
    contourOp T r f = dunfordIntegral f T 0 r := rfl

/-- `P_- = rieszProj T r` commutes with `J`. -/
theorem CommutesWith.rieszProj_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T) (r : ℝ) :
    J.CommutesWith (rieszProj T r) :=
  hT.rieszIntegral_zero_commutesWith r

/-- `P_+ = 1 - rieszProj T r` commutes with `J`. -/
theorem CommutesWith.one_sub_rieszProj_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) : J.CommutesWith (1 - rieszProj T r) :=
  J.commutesWith_one.sub (hT.rieszProj_commutesWith r)

/-- **`P_-` preserves real fields.** -/
theorem CommutesWith.rieszProj_mem_fixedSubmodule {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) {x : X} (hx : x ∈ J.fixedSubmodule) : rieszProj T r x ∈ J.fixedSubmodule :=
  (hT.rieszProj_commutesWith r).apply_mem_fixedSubmodule hx

/-- **`P_+` preserves real fields.** -/
theorem CommutesWith.one_sub_rieszProj_mem_fixedSubmodule {T : X →L[ℂ] X}
    (hT : J.CommutesWith T) (r : ℝ) {x : X} (hx : x ∈ J.fixedSubmodule) :
    (1 - rieszProj T r) x ∈ J.fixedSubmodule :=
  (hT.one_sub_rieszProj_commutesWith r).apply_mem_fixedSubmodule hx

/-- The contour operator `(2πi)⁻¹ ∮_{|z|=r} f(z) (z - T)⁻¹ dz` commutes with `J` when `f` is
real on real arguments. -/
theorem CommutesWith.contourOp_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    {f : ℂ → ℂ} (hf : ∀ z, conj (f (conj z)) = f z) (r : ℝ) :
    J.CommutesWith (contourOp T r f) := by
  rw [J.commutesWith_iff_conjOp_eq, contourOp_eq_dunfordIntegral,
    hT.conjOp_dunfordIntegral hf, map_zero]

/-- The outer inverse `𝓜_+⁻¹ = rieszOuterInv T r` commutes with `J`. -/
theorem CommutesWith.rieszOuterInv_commutesWith {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) : J.CommutesWith (rieszOuterInv T r) := by
  have h := hT.contourOp_commutesWith (f := fun z => z⁻¹)
    (fun z => by simp only [map_inv₀, Complex.conj_conj]) r
  intro x
  simp only [rieszOuterInv, neg_apply, map_neg, h x]

/-- The exterior space `P_+ X = range (1 - rieszProj T r)` is `J`-invariant, so it carries the
restricted conjugation `J.restrict`. -/
theorem CommutesWith.mem_range_one_sub_rieszProj {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) {x : X}
    (hx : x ∈ LinearMap.range ((1 - rieszProj T r : X →L[ℂ] X) : X →ₗ[ℂ] X)) :
    J x ∈ LinearMap.range ((1 - rieszProj T r : X →L[ℂ] X) : X →ₗ[ℂ] X) :=
  (hT.one_sub_rieszProj_commutesWith r).apply_mem_range hx

/-- The interior space `P_- X = range (rieszProj T r)` is `J`-invariant. -/
theorem CommutesWith.mem_range_rieszProj {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) {x : X} (hx : x ∈ LinearMap.range ((rieszProj T r : X →L[ℂ] X) : X →ₗ[ℂ] X)) :
    J x ∈ LinearMap.range ((rieszProj T r : X →L[ℂ] X) : X →ₗ[ℂ] X) :=
  (hT.rieszProj_commutesWith r).apply_mem_range hx

end Conjugation

end UnforcedLeray.Infra.RealStructure
