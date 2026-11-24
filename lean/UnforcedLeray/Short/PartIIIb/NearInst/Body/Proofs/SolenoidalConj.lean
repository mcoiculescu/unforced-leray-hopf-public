import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# `SolenoidalConj` (source 1675-1676)

The exact solenoidal subspace `solenoidalHC ε c` is the orthogonal complement of the span of the
complexified real gradients `cgrad ε Φ`, each fixed by conjugation.  If `g` is orthogonal to that
span then so is `cjLp g`: for a generator `v` one has `cjLp v = v`, hence
`⟪v, cj g⟫ = ⟪cj v, cj g⟫ = conj ⟪v, g⟫ = 0`, and the span is handled by induction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile cell)

/-- Orthogonality to the generators of a span passes to the conjugate of `g`, when the generators
are fixed by the conjugation. -/
theorem orth_conj_gen {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {cj : X →L⋆[ℂ] X} (h : IsConj cj) (K : Set X) (g : X) (hK : ∀ v ∈ K, cj v = v)
    (hg : ∀ v ∈ K, ⟪v, g⟫_ℂ = 0) : ∀ u ∈ Submodule.span ℂ K, ⟪u, cj g⟫_ℂ = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    have h1 : ⟪x, cj g⟫_ℂ = ⟪cj x, cj g⟫_ℂ := by rw [hK x hx]
    rw [h1, h.2, hg x hx, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **The exact solenoidal subspace is conjugation invariant** (source 1675-1676). -/
theorem solenoidalConj : SolenoidalConj := by
  intro ε c g hg
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC at hg ⊢
  rw [Submodule.mem_orthogonal] at hg ⊢
  refine orth_conj_gen (isConj_cjLp (measureH c) 2) _ g ?_ ?_
  · rintro v ⟨Φ, hm, rfl⟩
    apply Lp.ext
    filter_upwards [coeFn_cjLp (measureH c) 2 (hm.toLp (UnforcedLeray.Short.PartIIa.cgrad ε Φ.1)),
      MemLp.coeFn_toLp hm] with p h1 h2
    rw [h1, h2]
    ext i
    fin_cases i <;> simp [UnforcedLeray.Short.PartIIa.cgrad, conjV_apply, Complex.conj_ofReal]
  · intro v hv
    exact hg v (Submodule.subset_span hv)

end UnforcedLeray.Short.PartIIIb.NearInst.Body
