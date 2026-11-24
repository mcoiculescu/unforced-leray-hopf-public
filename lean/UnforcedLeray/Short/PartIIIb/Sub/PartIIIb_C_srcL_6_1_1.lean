import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1
import UnforcedLeray.Loc.L09CompactDatum.ParamIntegral

/-!
# Decomposition of `NewtonVSmooth` (task `PartIII-b:C/srcL/6/1/1`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
`newtonV x i = -2 ∫_{(0,1]} F_i(t, x) dt` with `F_i(t,x) = t^{2μ+2} ∫_{ℝ²} Σ_{jk} ∂_i∂_j∂_k N(x - t(x',0)) Σ_M(x')_{jk} dx'`.
The outer `t`-integral is handled here by `UnforcedLeray.L09.contDiffOn_integral`; the three
hypotheses of that theorem for the family `F_i` (smoothness for each `t`, measurability in `t` of the
iterated derivatives, local domination) are the leaves `NewtonFamSmooth`, `NewtonFamMeas`,
`NewtonFamDom`, each an application of the same theorem (and of `norm_iteratedFDeriv_integral_le`)
to the inner `x'`-integral, using `newtonD3` smooth off `0` and `Σ_M` supported in `|x'|² < 5ν/6`
and integrable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `i`-th component of the integrand of the outer `t`-integral of `newtonV` (source 4776-4782):
`F_i(t, x) = t^{2μ+2} ∫_{ℝ²} Σ_{j,k} ∂_i∂_j∂_k N(x - t(x',0)) Σ_M(x')_{jk} dx'`. -/
def newtonFam (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (i : Fin 3) (t : ℝ) (x : Vec3) : ℝ :=
  t ^ (2 * μ + 2) *
    ∫ x' : ℝ × ℝ, ∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k

theorem newtonV_apply (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (x : Vec3) (i : Fin 3) :
    newtonV c ν μ χo M x i = -2 * ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν μ χo M i t x := rfl

/-- **Leaf 1** (smoothness of each `F_i(t, ·)`, `t ∈ (0,1]`, on the region; source 4776-4782):
for `x` in the region `|x'|² < 5ν/6 <` `cylR x ^ 2`, `t ≤ 1`, the kernel argument `x - t(x',0)` stays
at distance `≥ cylR x - |x'| > 0` from `0` locally uniformly, `newtonD3` is `C^∞` off `0`, `Σ_M`
vanishes for `|x'|² ≥ 5ν/6` (`IsOutwardCutoff.zero`) and is integrable (`OldThinFinite`, polar
coordinates `u = ρ⁻²`); apply `UnforcedLeray.L09.contDiffOn_integral` to the `x'`-integral. -/
def NewtonFamSmooth : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M → ∀ (i : Fin 3), ∀ t ∈ Ioc (0 : ℝ) 1,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonFam c ν μ χo M i t)
        {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}

/-- **Leaf 2** (measurability in `t` of the iterated derivatives, on the region): for `x'` in the
disc the map `t ↦ D^n_x[F_i(t,·)](y)` is the `x'`-integral (`iteratedFDeriv_integral_eq`) of an
expression continuous in `t` on `(0,1]`. -/
def NewtonFamMeas : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M → ∀ (i : Fin 3) (n : ℕ),
      ∀ y ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2},
        AEStronglyMeasurable (fun t : ℝ => iteratedFDeriv ℝ n (newtonFam c ν μ χo M i t) y)
          (volume.restrict (Ioc (0 : ℝ) 1))

/-- **Leaf 3** (local domination, source 4917-4937): for each `n` and `x` in the region there are a
neighbourhood `s` and an integrable `g` on `(0,1]` (a constant multiple of `t^{2μ+2}`, `μ > 0`)
bounding `‖D^n_x F_i(t,·)(y)‖` for `t ∈ (0,1]`, `y ∈ s`: by `norm_iteratedFDeriv_integral_le` the
norm is `≤ t^{2μ+2} ∫ ‖D^n[newtonD3 (· - t(x',0)) ⋯ Σ_M(x')]‖ dx'`, the iterated derivative of the
kernel is bounded on the compact set of kernel arguments avoiding `0`, and `∫ ‖Σ_M‖ < ∞`. -/
def NewtonFamDom : Prop :=
  ∀ (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3), 0 < c → 0 < ν → 0 < μ →
    IsOutwardCutoff χo → OldThinFinite c ν M → ∀ (i : Fin 3) (n : ℕ),
      ∀ x ∈ {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2}, ∃ s ∈ nhds x, ∃ g : ℝ → ℝ,
        IntegrableOn g (Ioc (0 : ℝ) 1) ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y ∈ s,
          ‖iteratedFDeriv ℝ n (newtonFam c ν μ χo M i t) y‖ ≤ g t

theorem isOpen_newtonRegion (ν : ℝ) : IsOpen {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} :=
  isOpen_lt continuous_const (by fun_prop)

theorem newtonVSmooth_of (h1 : NewtonFamSmooth) (h2 : NewtonFamMeas) (h3 : NewtonFamDom) :
    NewtonVSmooth := by
  intro c ν μ χo M hc hν hμ hχ hM
  have hU := isOpen_newtonRegion ν
  rw [contDiffOn_pi]
  intro i
  have key : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ∫ t in Ioc (0 : ℝ) 1, newtonFam c ν μ χo M i t x)
      {x : Vec3 | 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2} := by
    refine UnforcedLeray.L09.contDiffOn_integral (μ := volume.restrict (Ioc (0 : ℝ) 1)) hU ?_
      (fun n x hx => h2 c ν μ χo M hc hν hμ hχ hM i n x hx) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact h1 c ν μ χo M hc hν hμ hχ hM i t ht
    · intro n x hx
      obtain ⟨s, hs, g, hg, hb⟩ := h3 c ν μ χo M hc hν hμ hχ hM i n x hx
      refine ⟨s, hs, g, hg, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact fun y hy => hb t ht y hy
  exact (key.const_smul (-2 : ℝ)).congr fun x _ => by
    simp only [Pi.smul_apply, smul_eq_mul]; rfl

end UnforcedLeray.Short.PartIIIb.Concrete
