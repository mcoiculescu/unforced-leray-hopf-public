import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3

/-!
# `PepsLerayInvisible` decomposed (task `PartIII-b:C/near/pins/3/3`)

Source `the November 2 reference manuscript`:
1675-1677 (`P_ε` the Leray projection, orthogonal to lifted gradients), 1339-1362, 4139-4146.

Two physical-dictionary leaves; the Hilbert-space algebra (`(1-P_ε)h'` lies in the closure of the
span of the gradient lifts, so a bounded functional killing the lifts kills it) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **Leaf 1 (pairing dictionary, bounded functional)**: for a solenoidal phase test `Φ` the
physical pairing `⟨Φ, 𝒩_v ·⟩` of the chart lift (2683; `velPhys`, azimuthal average of `Φ`, change
of variables `(τ,y) ↦ (s,q,η)` of 1640-1641, Cauchy-Schwarz against the `H` norm) is a bounded
linear functional of the `H`-class of the chart field. -/
def PairFunctional : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
    ∃ ℓ : HSpace c MeridC →L[ℂ] ℂ, ∀ (g : HSpace c MeridC) (f : Chart → Merid),
      ChartRep c g f → ℓ g = pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)

/-- **Leaf 2 (gradient lifts pair to zero with solenoidal tests)** (source 1666, 1675-1677): the
lift `(D_εΨ, ∂_ηΨ)` of a profile test has a real chart form `f` whose physical velocity is the
gradient of the axisymmetric scalar `Ψ` (`𝒩_v f = ∇ψ`, `D_ε`, `∂_η` the chart derivatives, `1666`),
and `⟨Φ, ∇ψ⟩ = -scalarPair ψ Φ = 0` for `div Φ = 0` (`scalarPair_sol`). -/
def GradLiftPairZero : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
    ∀ (Ψ : UnforcedLeray.B0226.ProfileTest c)
      (hm : MemLp (UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1) 2 (measureH c)),
      ∃ f : Chart → Merid, ChartRep c (hm.toLp _) f ∧
        pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f) = 0

theorem pepsLerayInvisible_of (h1 : PairFunctional) (h2 : GradLiftPairZero) :
    PepsLerayInvisible := by
  intro p f h' wk hf hwk Φ hΦ
  obtain ⟨ℓ, hℓ⟩ := h1 p.c p.ε p.c_pos p.ε_pos Φ hΦ
  set S := (Submodule.span ℂ {g : HSpace p.c MeridC | ∃ Φ : UnforcedLeray.B0226.ProfileTest
    p.c, ∃ _ : MemLp (UnforcedLeray.Short.PartIIa.cgrad p.ε Φ.1) 2 (measureH p.c),
      g = (‹MemLp (UnforcedLeray.Short.PartIIa.cgrad p.ε Φ.1) 2 (measureH p.c)›).toLp _}) with hS
  have hmem : h' - UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h' ∈
      (UnforcedLeray.Short.PartIIa.solenoidalHC p.ε p.c)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal
      (K := UnforcedLeray.Short.PartIIa.solenoidalHC p.ε p.c) h'
  change _ ∈ Sᗮᗮ at hmem
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hmem
  have hker : (S : Set (HSpace p.c MeridC)) ⊆ (LinearMap.ker ℓ.toLinearMap : Set _) := by
    intro g hg
    have hg' : g ∈ (Submodule.span ℂ _ : Submodule ℂ (HSpace p.c MeridC)) := hg
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg'
    · rintro g ⟨Ψ, hm, rfl⟩
      obtain ⟨f', hf', hz⟩ := h2 p.c p.ε p.c_pos p.ε_pos Φ hΦ Ψ hm
      show ℓ _ = 0
      rw [hℓ _ f' hf', hz]
    · exact map_zero ℓ
    · intro x y _ _ hx hy
      have hx' : ℓ x = 0 := hx
      have hy' : ℓ y = 0 := hy
      show ℓ (x + y) = 0
      rw [map_add, hx', hy', add_zero]
    · intro a x _ hx
      have hx' : ℓ x = 0 := hx
      show ℓ (a • x) = 0
      rw [map_smul, hx', smul_zero]
  have hcl : (S.topologicalClosure : Set (HSpace p.c MeridC)) ⊆
      (LinearMap.ker ℓ.toLinearMap : Set _) := by
    have hclosed : IsClosed (LinearMap.ker ℓ.toLinearMap : Set (HSpace p.c MeridC)) :=
      ℓ.isClosed_ker
    exact closure_minimal hker hclosed
  have h0 : ℓ (h' - UnforcedLeray.Short.PartIIa.PepsC p.ε p.c h') = 0 := hcl hmem
  rw [map_sub, sub_eq_zero] at h0
  rw [← hℓ _ wk hwk, ← hℓ _ f hf, h0]

end UnforcedLeray.Short.PartIIIb.NearInst
