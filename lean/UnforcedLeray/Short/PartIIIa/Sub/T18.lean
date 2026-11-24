import UnforcedLeray.Short.PartIIIa.FlatCausal

/-!
# Part III-a, task `PartIII-a:T18`: the free causal solver (conditional)

Source of record: `the November 2 reference manuscript`, lines 3427-3440 (the free
instance of the zero-entrance construction, "start from zero at `s = δ`, let `δ ↓ 0`") and
3541-3552 (uniqueness: a homogeneous difference has `δ_j ↓ 0` with `δ_j^{-1/2}‖u(δ_j)‖² → 0`,
apply the tail energy identity on `[δ_j, B]`).

## Decomposition

`FreeCausalExistsUnique` (`FlatCausal.lean`) is existence + two energy bounds + uniqueness. The

the weak formulation, a Galerkin/semigroup existence theorem and a limit `δ → 0`, none of which is in
the library. Here it is cut into three facts, each a true statement of the source:

* `CausalSolSub` (`PartIII-a:T18/1`): the class `IsCausalEnergySolution` is a real vector space,
  i.e. the difference of two solutions solves the equation with the difference of the forcings (the
  `N8` linearity; in the source "the homogeneous difference in the energy class").
* `FreeCausalEnergyBound` (`PartIII-a:T18/3`): EVERY causal zero-entrance energy solution of the
  free equation with `‖g⁻¹F‖_𝒯 < ∞` satisfies `‖g⁻¹b‖_𝓗 ≤ (2√(k_*ν))⁻¹‖g⁻¹F‖_𝒯` and
  `‖g⁻¹G‖_𝒯 ≤ ν⁻¹‖g⁻¹F‖_𝒯`. This is the weighted energy identity of SP 3541-3552 on `[δ_j, B]` with
  the `liminf` argument of SP 3541-3546 (it holds for any solution, not only the constructed one,
  and contains the uniqueness).
* `FreeCausalExistence` (`PartIII-a:T18/2`): existence of some causal zero-entrance energy
  solution (SP 3427-3440).

`freeCausalExistsUnique_of` assembles the target: existence from `FreeCausalExistence`, bounds from
`FreeCausalEnergyBound`, uniqueness by `CausalSolSub` (difference solves the equation with force
`F - F = 0`) and `FreeCausalEnergyBound` applied with force `0` (`‖g⁻¹(b' - b)‖_𝓗 ≤ 0`), then
`ageμ c (-3/2) ≪` and `≫` Lebesgue measure on `(0,∞) × cell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Linearity of the solution class** (`PartIII-a:T18/1`; SP 3541-3552, "a homogeneous difference
in the energy class"). If `(b, G)` solves the equation with force `F` and `(b', G')` solves it with
force `F'` (same `c, ν, μ` and coefficient field `vel`), then `(b - b', G - G')` is a causal
zero-entrance energy solution with force `F - F'`. All clauses of `IsCausalEnergySolution` are linear;
for `zeroEntrance` take the smaller of the two `δ`, for the integrability and weak clauses use that
`flatIntegrand` is affine-linear in `(F, b)`. -/
def CausalSolSub : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F F' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    IsCausalEnergySolution c ν μ vel F b G → IsCausalEnergySolution c ν μ vel F' b' G' →
      IsCausalEnergySolution c ν μ vel (fun p i j => F p i j - F' p i j)
        (fun p i => b p i - b' p i) (fun p i j => G p i j - G' p i j)

/-- **Existence** of a causal zero-entrance energy solution of the free equation (`PartIII-a:T18/2`;
SP 3427-3440): for `K ⋐ {0 < Re μ < 1/4}` and small `ν`, every symmetric measurable `F` with
`‖g⁻¹F‖_𝒯 < ∞` has some `(b, G)` with `IsCausalEnergySolution (ν⁻²) ν μ 0 F b G`. Proof in the
source: solve on `[δ, B]` with `u(δ) = 0`, bound uniformly in `δ` by the energy identity, let
`δ ↓ 0` (weak limit; equivalently `b_δ` is Cauchy in `𝓗` and `∇b_δ` in `𝒯` by the energy bound and
linearity). -/
def FreeCausalExistence : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ μ ∈ K,
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
        ∃ b G, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b G

/-- **A priori energy bounds for every causal zero-entrance energy solution** (`PartIII-a:T18/3`;
SP 3427-3440 and 3541-3552). With `u = g⁻¹b`, `g = exp(γ s/(1+νs))`, `γ = Re λ > 0` and `h = g'/g =
γ/(1+νs)² ≥ 0`, the weighted energy identity of the free equation
`u_s + (μ/s + h)u - νΔu = P div(g⁻¹F)` reads
`d/ds(s^{-1/2}‖u‖²) + (2 Re μ + 1/2) s^{-3/2}‖u‖² + 2h s^{-1/2}‖u‖² + 2ν s^{-1/2}‖∇u‖²
 = -2 s^{-1/2} Re ⟨g⁻¹F, ∇u⟩`
on `[δ, B]`. Zero entrance gives `δ_j ↓ 0` with `δ_j^{-1/2}‖u(δ_j)‖² → 0` (because
`∫ s^{-3/2}‖u‖² ds < ∞` near `0`), and Young's inequality with `k_* = inf_K (Re μ + 1/4)` yields
`‖u‖_𝓗 ≤ (2√(k_*ν))⁻¹‖g⁻¹F‖_𝒯` and `‖∇u‖_𝒯 ≤ ν⁻¹‖g⁻¹F‖_𝒯`. -/
def FreeCausalEnergyBound : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ μ ∈ K,
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
        ∀ b G, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b G →
          hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) ≤
            ENNReal.ofReal ((2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹) *
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ∧
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G) ≤
            ENNReal.ofReal ν⁻¹ * tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F)

/-! ### Bridges used by the assembly -/

/-- `ageμ c (-3/2)` charges every positive-Lebesgue-measure subset of `(0,∞) × cell`, i.e. Lebesgue
measure on `(0,∞) × cell` is absolutely continuous with respect to `ageμ c (-3/2)`. -/
theorem restrict_ac_ageμ {c : ℝ} (hc : 0 < c) :
    (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) ≪
      ageμ c (-3 / 2) := by
  have h1 : (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) ≪
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow _).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs _)).ne'
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  have h2 : (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) ≪ UnforcedLeray.Cyl.avgμ c := by
    rw [hcell]
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  have h3 := Measure.AbsolutelyContinuous.prod h1 h2
  have e : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        ((volume : Measure (ℝ × ℝ)).restrict (B0579.cell c)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [e]
  exact h3

/-- The conjugated pointwise norm is measurable. -/
theorem measurable_vnorm2_gainConj (γ ν : ℝ) {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    (hf : ∀ i, Measurable fun p => f p i) :
    Measurable fun p => vnorm2 (gainConj γ ν f p) := by
  unfold vnorm2 gainConj
  refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ := by
    unfold gainG
    exact (Real.measurable_exp.comp ((measurable_const.mul measurable_fst).div
      (measurable_const.add (measurable_const.mul measurable_fst)))).inv
  have h : Measurable fun p : ℝ × (ℝ × ℝ) => (gainG γ ν p.1)⁻¹ • f p i := hg.smul (hf i)
  simpa only [Pi.smul_apply] using h.norm.pow_const 2

/-- If the conjugated pointwise norm vanishes at `p`, then `f p = 0`. -/
theorem eq_zero_of_vnorm2_gainConj {γ ν : ℝ} {f : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {p : ℝ × (ℝ × ℝ)} (h : vnorm2 (gainConj γ ν f p) = 0) : f p = 0 := by
  unfold vnorm2 at h
  have hs : ∑ i : Fin 2, ‖gainConj γ ν f p i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).1 h
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖gainConj γ ν f p i‖).1 hs
  funext i
  have h0 : gainConj γ ν f p i = 0 := by
    have := hi i (Finset.mem_univ i)
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  unfold gainConj at h0
  simp only [Pi.smul_apply] at h0
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (inv_ne_zero (Real.exp_pos _).ne')
  · simpa using h1

/-- **Conditional free causal solver** (target of `PartIII-a:T18`). -/
theorem freeCausalExistsUnique_of (hLin : CausalSolSub) (hEx : FreeCausalExistence)
    (hBd : FreeCausalEnergyBound) : FreeCausalExistsUnique := by
  intro P hP K hK
  obtain ⟨ν₁, hν₁, hE⟩ := hEx P hP K hK
  obtain ⟨ν₂, hν₂, hB⟩ := hBd P hP K hK
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν μ hμ F hFs hFm hFT
  have hν1 : ν ∈ Ioc 0 ν₁ := ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  have hν2 : ν ∈ Ioc 0 ν₂ := ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν.1 _
  obtain ⟨b, G, hsol⟩ := hE ν hν1 μ hμ F hFs hFm hFT
  obtain ⟨hH, hG⟩ := hB ν hν2 μ hμ F hFs hFm hFT b G hsol
  refine ⟨b, G, hsol, hH, hG, ?_⟩
  intro b' G' hsol'
  -- the difference solves the equation with force `F - F = 0`
  have hdiff := hLin (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F F b' b G' G hsol' hsol
  have hF0 : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => F p i j - F p i j) =
      fun _ _ _ => (0 : ℂ) := by
    funext p i j
    exact sub_self _
  rw [hF0] at hdiff
  have hz : tCalNorm (ν ^ (-2 : ℝ))
      (gainConj P.eigenvalue.re ν (fun (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ))) = 0 := by
    have e : gainConj P.eigenvalue.re ν (fun (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ)) =
        fun _ _ _ => (0 : ℂ) := by
      funext p i j
      simp [gainConj]
    rw [e]
    simp [tCalNorm, tnorm2]
  obtain ⟨hH0, -⟩ := hB ν hν2 μ hμ (fun _ _ _ => 0) (fun _ _ _ => rfl)
    (fun _ _ => measurable_const) (by rw [hz]; exact ENNReal.zero_lt_top)
    (fun p i => b' p i - b p i) (fun p i j => G' p i j - G p i j) hdiff
  rw [hz, mul_zero] at hH0
  have h0 : hCalNorm (ν ^ (-2 : ℝ))
      (gainConj P.eigenvalue.re ν (fun p i => b' p i - b p i)) = 0 := le_antisymm hH0 zero_le
  unfold hCalNorm at h0
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      vnorm2 (gainConj P.eigenvalue.re ν (fun p i => b' p i - b p i) p) :=
    measurable_vnorm2_gainConj P.eigenvalue.re ν fun i => (hsol'.measurable i).sub (hsol.measurable i)
  have hae := (eLpNorm_eq_zero_iff hm.aestronglyMeasurable (by norm_num)).1 h0
  have hae' : b' =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-3 / 2)] b := by
    filter_upwards [hae] with p hp
    have hp' : vnorm2 (gainConj P.eigenvalue.re ν (fun p i => b' p i - b p i) p) = 0 := hp
    have := eq_zero_of_vnorm2_gainConj hp'
    funext i
    have hi := congrFun this i
    simpa [sub_eq_zero] using hi
  exact (restrict_ac_ageμ hc).ae_eq hae'

end UnforcedLeray.Short.IIIa
