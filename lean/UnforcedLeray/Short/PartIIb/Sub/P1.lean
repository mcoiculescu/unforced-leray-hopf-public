import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Part II-b, task `PartII-b:P1`: the body lift `J` (conditional)

Source of record: `the November 2 reference manuscript`, lines 1902-1906 (the lift
`Mb = √s b` and the norm factor `(πR²)^{1/r}` cancel), as used in `PhysicalRowReduction`
(`StatementsNonlinear.lean`, SP 2490-2504).

`BodyLift`: for every regime point there is a bounded linear `J : Y → H_p` (real classes) with
`‖J‖ ≤ s⁻¹`, `s = (πR²)^{1/p}`, representing every `f ∈ Y` as `f = N_v (J f)` almost everywhere
and `‖f‖_Y = s ‖J f‖_{H_p}`.

Leaves:
* `BodyLiftLinear` (`P1/1`): a linear map `J₀ : Y → H_p` with `rep f = N_v (J₀ f)` a.e. (every real
  solenoidal `𝒪`-invariant element of `Y_{q₀}` is the ring lift of a unique `c`-periodic profile;
  inverse chart `(τ, ϱ, z) ↔ (s, q, η)`; uniqueness gives linearity);
* `BodyLiftNorm` (`P1/2`, uses `T07`): if `rep f = N_v g` a.e. then `‖f‖_Y = s ‖g‖_{H_p}`.

Proved here: `bodyLift_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-- **`PartII-b:P1`** (`bodyLift_iso`; SP 1902-1906, 2490-2504). -/
def BodyLift : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ), BgRegime p d dm dp →
    ∃ J : p.Y →L[ℝ] HpR p.c,
      ‖J‖ ≤ ((Real.pi * p.R ^ 2) ^ (1 / bgp))⁻¹ ∧
      (∀ f : p.Y, ∀ᵐ x : ℝ × Space, rep (f : Yq p.period q0E) x.1 x.2 =
        NvC p.R (toProf p.c (J f)) x) ∧
      ∀ f : p.Y, ‖f‖ = (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖J f‖

/-- **Leaf `PartII-b:P1/1`** (SP 1902-1906): a linear representing map.  Proof: every real
axisymmetric no-swirl element of `Y_{q₀}` is `N_v b` for a unique `c`-periodic real profile `b`
(`Lib/AxisymmetricB/Range.lean`, `Bridge.lean`; the inverse chart is a bijection
`(τ, ϱ, z) ↔ (s, q, η)` mod the period); uniqueness (a.e.) gives linearity of `f ↦ b`. -/
def BodyLiftLinear : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ), BgRegime p d dm dp →
    ∃ J₀ : p.Y →ₗ[ℝ] HpR p.c, ∀ f : p.Y, ∀ᵐ x : ℝ × Space,
      rep (f : Yq p.period q0E) x.1 x.2 = NvC p.R (toProf p.c (J₀ f)) x

/-- **Leaf `PartII-b:P1/2`** (uses `T07`, `phaseLpNorm_NvC`; SP 1902-1906): the norm factor
`‖f‖_Y = (πR²)^{1/p} ‖g‖_{H_p}` when `f = N_v g` a.e. (`Yq` norm is `phaseLpNorm` of `rep f`,
which only depends on the a.e. class). -/
def BodyLiftNorm : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ), BgRegime p d dm dp →
    ∀ (f : p.Y) (g : HpR p.c), (∀ᵐ x : ℝ × Space, rep (f : Yq p.period q0E) x.1 x.2 =
        NvC p.R (toProf p.c g) x) →
      ‖f‖ = (Real.pi * p.R ^ 2) ^ (1 / bgp) * ‖g‖

/-- `BodyLift` from its two leaves. -/
theorem bodyLift_of (h1 : BodyLiftLinear) (h2 : BodyLiftNorm) : BodyLift := by
  intro dm dp hdm p d hreg
  obtain ⟨J₀, hJ₀⟩ := h1 dm dp hdm p d hreg
  have hε : 0 < p.ε := p.ε_pos
  have hs : 0 < (Real.pi * p.R ^ 2) ^ (1 / bgp) := by
    have : 0 < p.R := by unfold Params.R; positivity
    positivity
  have hb : ∀ f : p.Y, ‖J₀ f‖ ≤ ((Real.pi * p.R ^ 2) ^ (1 / bgp))⁻¹ * ‖f‖ := by
    intro f
    have := h2 dm dp hdm p d hreg f (J₀ f) (hJ₀ f)
    rw [this, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  refine ⟨J₀.mkContinuous _ hb, ?_, hJ₀, ?_⟩
  · exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.2 hs.le) _
  · intro f
    exact h2 dm dp hdm p d hreg f _ (hJ₀ f)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.bodyLift_of
