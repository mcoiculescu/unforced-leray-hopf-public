import UnforcedLeray.Units.B0009

/-!
# Part I, task `PartI:S13a`: the free transport group on `H^j_M` (conditional)

Source of record: `the November 2 reference manuscript`, lines 841-852
("the chain rule gives `‖T(t)‖ ≤ C_j (1+|t|)^j`; density and differentiation of the flow give the
generator domain; the converse inclusion follows from `T(t)f - f = -∫₀ᵗ T(s) Ω∂_ϑ f ds`").

The free transport `T(t)f(r, ϑ) = f(r, ϑ - Ω(r)t)` is, in Cartesian coordinates,
`freeFlow t f y = f (e^{-i t Ω(|y|)} y)` (`Ω = B0009.Omega`). It is a volume- and weight-preserving
rotation by the radius-dependent angle `-Ω(|y|)t`. Its formal generator is `-Ω∂_ϑ`
(`d/dt f(r, ϑ - Ω t) = -Ω ∂_ϑ f`), where `Ω∂_ϑ f` is the weak transport of
`B0009.HasWeakTransport`; the domain of the generator is `B0009.transportDomain j M`, so the
generator value at `F` is `-B0009.transport ⟨F, hF⟩`.

Five Props isolate the analytic content; `transport_group_HjM_of` assembles the target from them.
The unconditional theorem `transport_group_HjM` is the task `PartI:S13a`
(`Short/PartI/Tasks/TransportGroupHjM.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The free differential rotation `f ↦ f(r, ϑ - Ω(r)t)` in Cartesian form
(`y ↦ e^{-itΩ(|y|)} y`; source lines 841-852). -/
def freeFlow (t : ℝ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  f (Complex.exp (((-(t * B0009.Omega y) : ℝ) : ℂ) * Complex.I) * y)

/-- **Existence of the free flow on `H^j_M`** (source lines 841-852; HEAVY chain-rule core): for
`M > 1` there are bounded operators `T(t)` on `H^j_M` whose functions are `f ∘ Φ_t` almost
everywhere (`Φ_t y = e^{-itΩ(|y|)} y`, a volume-preserving smooth diffeomorphism commuting with
the radial weight) with `‖T(t)‖ ≤ C_j (1+|t|)^j`. For `j = 0` this is an isometry; for general `j`
the weak chain rule gives `∂^α(f ∘ Φ_t)` as a sum of `(∂^β f) ∘ Φ_t` times polynomials of degree
`≤ |α|` in `t` and derivatives of `Ω`. -/
def FreeFlowExists (j : ℕ) : Prop :=
  ∀ {M : ℝ}, 1 < M → ∃ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
    (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C * (1 + |t|) ^ j

/-- **Group law** (source lines 841-852): any family `T(t)` representing the free flow satisfies
`T(s+t) = T(s) T(t)` and `T(0) = 1`. Proof: `Φ_t ∘ Φ_s = Φ_{s+t}` pointwise because
`|Φ_s y| = |y|`; `Φ_s` preserves null sets (`B0009.Omega` is radial and `Φ_s` is a volume-preserving
shear in polar coordinates), so a.e.-equal functions have a.e.-equal flows, and `HjM.ext`
(an element is determined by its function) finishes. -/
def FreeFlowGroup (j : ℕ) : Prop :=
  ∀ {M : ℝ}, 1 < M → ∀ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
    (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) →
      (∀ s t, T (s + t) = T s * T t) ∧ T 0 = 1

/-- **Strong continuity** (source lines 841-852, "density"): a family representing the free flow
with the polynomial bound is strongly continuous. Proof: for a test function (dense in `H^j_M`)
`t ↦ φ ∘ Φ_t` is continuous into `H^j_M` (smooth in `(t, y)` with compact support locally
uniformly in `t`), then the uniform local bound extends it to all of `H^j_M`. -/
def FreeFlowStrongCont (j : ℕ) : Prop :=
  ∀ {M : ℝ}, 1 < M → ∀ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
    (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C * (1 + |t|) ^ j) →
        ∀ F, Continuous fun t => T t F

/-- **Generator, forward inclusion** (source lines 841-852, "differentiation of the flow"): for `F`
in the weak transport domain, `(T(t)F - F)/t → -Ω∂_ϑ F = -B0009.transport F` in `H^j_M` as
`t → 0`. Proof: `T(t)F - F = -∫₀ᵗ T(s) (Ω∂_ϑ F) ds`, tested against test functions `φ` using
`∫ F · (φ ∘ Φ_{-t}) = ∫ (F ∘ Φ_t) φ` (the flow preserves volume), then strong continuity at `0`
(`FreeFlowStrongCont`) gives the limit in the norm of `H^j_M`. -/
def FreeFlowGeneratorForward (j : ℕ) : Prop :=
  ∀ {M : ℝ}, 1 < M → ∀ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
    (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C * (1 + |t|) ^ j) →
        (∀ F, Continuous fun t => T t F) →
          ∀ (F : B0008.HjM j M) (hF : F ∈ B0009.transportDomain j M),
            Tendsto (fun t : ℝ => t⁻¹ • (T t F - F)) (𝓝[≠] 0)
              (𝓝 (-(B0009.transport (⟨F, hF⟩ : B0009.transportDomain j M))))

/-- **Generator, converse inclusion** (source lines 841-852, "converse inclusion by
`T(t)f - f = -∫ T(s) Ω∂_ϑ f ds`"): if the difference quotients `(T(t)F - F)/t` converge in `H^j_M`
to some `G` as `t → 0`, then `F` is in the weak transport domain and `G = -B0009.transport F`.
Proof: for a test function `φ`, `∫ ((T(t)F - F)/t) φ = ∫ F ((φ ∘ Φ_{-t} - φ)/t)` tends to
`∫ F · Ω∂_ϑφ` (dominated convergence: `φ` is smooth with compact support and `Ω` is bounded) and,
by convergence in `H^j_M ⊂ L²_M`, to `∫ G φ`; hence `∫ F · Ω∂_ϑφ = -∫ (-G) φ`, i.e.
`HasWeakTransport F (-G)`. -/
def FreeFlowGeneratorConverse (j : ℕ) : Prop :=
  ∀ {M : ℝ}, 1 < M → ∀ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
    (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) →
      ∀ (F G : B0008.HjM j M),
        Tendsto (fun t : ℝ => t⁻¹ • (T t F - F)) (𝓝[≠] 0) (𝓝 G) →
          ∃ hF : F ∈ B0009.transportDomain j M,
            -(B0009.transport (⟨F, hF⟩ : B0009.transportDomain j M)) = G

/-- **The free transport group on `H^j_M`** (source lines 841-852): `T(t)f(r, ϑ) = f(r, ϑ - Ω(r)t)`
is a strongly continuous group on `H^j_M` (`M > 1`) with `‖T(t)‖ ≤ C_j (1+|t|)^j`, its generator
has domain `B0009.transportDomain j M` (`F` is in the domain iff the difference quotients
converge in `H^j_M`) and acts there as `-Ω∂_ϑ = -B0009.transport`. -/
theorem transport_group_HjM_of {j : ℕ} (hE : FreeFlowExists j) (hG : FreeFlowGroup j)
    (hS : FreeFlowStrongCont j) (hF : FreeFlowGeneratorForward j)
    (hC : FreeFlowGeneratorConverse j) {M : ℝ} (hM : 1 < M) :
    ∃ T : ℝ → (B0008.HjM j M →L[ℂ] B0008.HjM j M),
      (∀ t F, ((T t F).value : ℂ → ℂ) =ᵐ[volume] freeFlow t (F.value : ℂ → ℂ)) ∧
      (∀ s t, T (s + t) = T s * T t) ∧ T 0 = 1 ∧
      (∀ F, Continuous fun t => T t F) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖T t‖ ≤ C * (1 + |t|) ^ j) ∧
      (∀ F : B0008.HjM j M, F ∈ B0009.transportDomain j M ↔
        ∃ G : B0008.HjM j M,
          Tendsto (fun t : ℝ => t⁻¹ • (T t F - F)) (𝓝[≠] 0) (𝓝 G)) ∧
      (∀ (F : B0008.HjM j M) (hF : F ∈ B0009.transportDomain j M),
        Tendsto (fun t : ℝ => t⁻¹ • (T t F - F)) (𝓝[≠] 0)
          (𝓝 (-(B0009.transport (⟨F, hF⟩ : B0009.transportDomain j M))))) := by
  obtain ⟨T, hrep, hbd⟩ := hE hM
  have hcont := hS hM T hrep hbd
  have hfwd := hF hM T hrep hbd hcont
  obtain ⟨hadd, hzero⟩ := hG hM T hrep
  refine ⟨T, hrep, hadd, hzero, hcont, hbd, fun F => ⟨fun hFm => ⟨_, hfwd F hFm⟩, ?_⟩, hfwd⟩
  rintro ⟨G, hG'⟩
  exact (hC hM T hrep F G hG').1

end UnforcedLeray.Short.PartI
