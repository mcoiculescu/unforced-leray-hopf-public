import UnforcedLeray.Short.PartIIIa.Sub.T18

/-!
# Part III-a, task `PartIII-a:T18/3`: the free a priori energy bounds (conditional)

Target (`Sub/T18.lean`): `FreeCausalEnergyBound`: for `P` a planar reference, `K ⋐ {0 < Re μ < 1/4}`,
`ν ≤ ν₀`, `μ ∈ K`, `F` symmetric measurable with `‖g⁻¹F‖_𝒯 < ∞` and EVERY causal zero-entrance
energy solution `(b, G)` of the free equation with force `F`,
`‖g⁻¹b‖_𝓗 ≤ (2√(k_*ν))⁻¹‖g⁻¹F‖_𝒯` and `‖g⁻¹G‖_𝒯 ≤ ν⁻¹‖g⁻¹F‖_𝒯`, `k_* = inf_K(Re μ' + 1/4)`.
Source of record: `the November 2 reference manuscript`, lines 3427-3440 (zero
entrance) and 3541-3552 (the energy identity on `[δ_j, B]`, `δ_j^{-1/2}‖u(δ_j)‖² → 0`).

## Mathematical proof

Put `u = g⁻¹b`, `G̃ = g⁻¹G = ∇u`, `F̃ = g⁻¹F`, `g = exp(γs/(1+νs))`, `γ = Re λ ≥ 0`, `h = g'/g =
γ/(1+νs)² ≥ 0`, `E(s) = ∫_cell |u(s)|² `. Then `u_s + (μ/s + h)u - νΔu = 𝒫₀ div F̃` weakly, and
testing with `u` (real and imaginary parts) gives, for `0 < s₁ < s₂`,
`s₂^{-1/2}E(s₂) - s₁^{-1/2}E(s₁) + ∫_{s₁}^{s₂}[(1/2 + 2Re μ)s^{-3/2}E + 2h s^{-1/2}E +
2ν s^{-1/2}‖G̃‖²] ds = -2∫_{s₁}^{s₂} s^{-1/2}Re⟨F̃, G̃⟩ ds`.
It is used in the distributional form (`WeightedEnergyIdentity`, dropping `2h s^{-1/2}E ≥ 0` and
bounding `-Re⟨F̃, G̃⟩ ≤ |F̃||G̃|`) against a cutoff `ψ ≥ 0` which rises linearly on `[δ, 2δ]`, equals
`1` on `[2δ, B]` and falls linearly on `[B, 2B]`: the rising part is `≤ 2∫_δ^{2δ}s^{-3/2}E ds → 0`
(zero entrance: `∫_0^{δ₀}s^{-3/2}E < ∞`), the falling part has a good sign, and `δ → 0`, `B → ∞`
by monotone convergence. Young's inequality `2|F̃||G̃| ≤ ν|G̃|² + |F̃|²/ν` gives
`2k_*‖u‖_𝓗² + ν‖G̃‖_𝒯² ≤ ν⁻¹‖F̃‖_𝒯²` and `2|F̃||G̃| ≤ 2ν|G̃|² + |F̃|²/(2ν)` gives
`2k_*‖u‖_𝓗² ≤ (2ν)⁻¹‖F̃‖_𝒯²` (`FreeEnergyInequalities`); square roots give the two bounds.

Proved here, from the Prop `FreeEnergyInequalities`: `freeCausalEnergyBound_of` (the arithmetic with
`ENNReal.ofReal`, `k_* ≥ 1/4 > 0`). The remaining two statements are the analytic core
(`WeightedEnergyIdentity`, task `PartIII-a:T18/3/1`: Lions-Magenes on the cylinder) and the cutoff
argument (`FreeEnergyInequalities` from it, task `PartIII-a:T18/3/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Distributional weighted energy inequality** (`PartIII-a:T18/3/1`; SP 3541-3552). Let `c, ν > 0`,
`γ ≥ 0`, `μ ∈ ℂ`, `F ∈ L²_loc((0,∞) × cell)` and `(b, G)` a causal zero-entrance energy solution of
the free equation (`vel = 0`) with force `F`. With `u = g⁻¹b`, `G̃ = g⁻¹G`, `F̃ = g⁻¹F`
(`gainConj γ ν`, `g(s) = exp(γ s/(1+ν s))`) and `E(s) = ∫_cell |u(s)|²`,
for every `C¹` cutoff `ψ ≥ 0` with compact support in `(0,∞)`:
`∫ ψ[(1/2 + 2Re μ)s^{-3/2}E + 2ν s^{-1/2}∫|G̃|²] ds ≤ ∫ ψ' s^{-1/2}E ds + 2∫ ψ s^{-1/2}∫|F̃||G̃| ds`.
This is the weighted energy identity of the equation `u_s + (μ/s + h)u - νΔu = 𝒫₀ div F̃`
(`d/ds(s^{-1/2}E) + (1/2 + 2Re μ)s^{-3/2}E + 2h s^{-1/2}E + 2ν s^{-1/2}‖G̃‖² =
-2 s^{-1/2}Re⟨F̃, G̃⟩`, with `h = γ/(1+νs)² ≥ 0` dropped and `-Re⟨F̃,G̃⟩ ≤ |F̃||G̃|`) in
distributional form in `s`. Route (Lions-Magenes on the cylinder `V = div-free H¹_per(q) × H¹(η)`
fields): (N1) energy identity `d/ds‖u‖² = 2⟨u',u⟩` for `u ∈ L²_loc(V)`, `u' ∈ L²_loc(V')` (only the
`H`-valued version exists: `Lib/BochnerTime/Energy.lean`, `HasWeakDerivTime.norm_sq_sub`); (N2) the
`IsFlatTest` weak identity extends from smooth compactly supported divergence-free tests to
`ψ(s)φ(x)` with `φ ∈ V` (density of divergence-free fields compactly supported in `η`, via a stream
function and cutoff in `η`, plus the horizontal mean flows `(φ(η), 0)`); (N3) combine with the
`C¹` weight.


added: without it the Prop is FALSE (junk value of the Bochner integral `∫_cell |F̃||G̃|` for a
non-measurable `F`). Counterexample: `μ = -1`, `b = s^{-μ} b₀(x)` with `b₀` a smooth divergence-free
periodic compactly supported field, `F = F_m + 1_A · Id` with `F_m = -ν∇b` and `A = ℝ × A'`, `A'` a
non-null-measurable subset of the plane with inner measure `0`; the trace part `1_A Id` is invisible
to every divergence-free test (`1_A · div Φ = 0`), `∫⁻ |F|² < ⊤` over every compact box, `(b, G=∇b)`
is a causal zero-entrance energy solution, and every slice integral `∫_cell |F̃||G̃|` is a Bochner
integral of a non-AE-measurable function, hence `0`, so the right-hand side loses the
`2ν∫ψ s^{-1/2}‖G̃‖²`-sized term that the true identity has. All uses (`FreeEnergyInequalities`)
have `F` measurable. -/
def WeightedEnergyIdentity : Prop :=
  ∀ (c ν γ : ℝ) (μ : ℂ), 0 < c → 0 < ν → 0 ≤ γ →
    ∀ (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
      (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (F p) ^ 2) < ⊤) →
    (∀ i j, Measurable fun p => F p i j) →
    IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
    ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi 0 → (∀ s, 0 ≤ ψ s) →
      (∫ s in Ioi (0 : ℝ), ψ s *
          ((1 / 2 + 2 * μ.re) * s ^ (-3 / 2 : ℝ) *
              (∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2) +
            2 * ν * s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2))
        ≤ (∫ s in Ioi (0 : ℝ), deriv ψ s *
            (s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2)) +
          2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) *
            ∫ x in B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) * tnorm2 (gainConj γ ν G (s, x))

/-- **The two squared energy inequalities** (`PartIII-a:T18/3/2`; SP 3541-3552). For every causal
zero-entrance energy solution `(b, G)` of the free equation with `‖g⁻¹F‖_𝒯 < ∞`
(hypotheses of `FreeCausalEnergyBound`), with `k_* = inf_K(Re μ' + 1/4)`,
`2k_*‖g⁻¹b‖_𝓗² + ν‖g⁻¹G‖_𝒯² ≤ ν⁻¹‖g⁻¹F‖_𝒯²` and `2k_*‖g⁻¹b‖_𝓗² ≤ (2ν)⁻¹‖g⁻¹F‖_𝒯²`.
Proof from `WeightedEnergyIdentity` (with `c = ν⁻²`, `γ = Re λ > 0`, `μ ∈ K`): choose the cutoff
`ψ_{δ,B}` (linear on `[δ,2δ]` and `[B,2B]`), Young's inequality pointwise
(`2xy ≤ νx² + y²/ν`, resp. `2xy ≤ 2νx² + y²/(2ν)`), absorb the finite `ψ`-weighted `G̃` term,
`(1/2 + 2Re μ) ≥ 2k_*`, `∫_δ^{2δ}s^{-1/2}E ≤ 2δ∫_δ^{2δ}s^{-3/2}E`, zero entrance
(`∫_0^{δ₀} s^{-3/2}E < ∞`) and monotone convergence in `δ → 0`, `B → ∞`; convert between the
`ageμ c a` norms (`Axi.lintegral_ageμ`, `Lib/AxisymmetricB/Lift.lean`) and the iterated integrals
`∫ s^a ∫_cell`. -/
def FreeEnergyInequalities : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ μ ∈ K,
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
        ∀ b G, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b G →
          (ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) *
              hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) ^ 2 +
            ENNReal.ofReal ν * tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G) ^ 2 ≤
              ENNReal.ofReal ν⁻¹ * tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ^ 2) ∧
          (ENNReal.ofReal (2 * (⨅ μ' : K, μ'.1.re + 1 / 4)) *
              hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) ^ 2 ≤
            ENNReal.ofReal (2 * ν)⁻¹ *
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ^ 2)

/-! ## The arithmetic -/

/-- `k_* = inf_K (Re μ' + 1/4) ≥ 1/4` for `K` in the right half-plane, `K` nonempty. -/
theorem kStar_ge {K : Set ℂ} {μ : ℂ} (hμ : μ ∈ K) (hK : ∀ μ' ∈ K, 0 < μ'.re) :
    (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 := by
  haveI : Nonempty K := ⟨⟨μ, hμ⟩⟩
  refine le_ciInf fun μ' => ?_
  have := hK μ'.1 μ'.2
  linarith

/-- From `a² c ≤ x² b` conclude `a ≤ …`: the square-root step in `ℝ≥0∞`. -/
theorem le_of_sq_le_sq {x y : ℝ≥0∞} (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem freeCausalEnergyBound_of (hI : FreeEnergyInequalities) : FreeCausalEnergyBound := by
  intro P hP K hK
  obtain ⟨ν₀, hν₀, H⟩ := hI P hP K hK
  refine ⟨ν₀, hν₀, fun ν hν μ hμ F hs hm hF b G hsol => ?_⟩
  obtain ⟨I1, I2⟩ := H ν hν μ hμ F hs hm hF b G hsol
  have hνpos : 0 < ν := hν.1
  have hk : (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 := kStar_ge hμ (fun μ' h => (hK.2 μ' h).1)
  set k : ℝ := ⨅ μ' : K, μ'.1.re + 1 / 4 with hkdef
  have hkpos : 0 < k := by linarith
  set a := hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b) with ha
  set g := tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G) with hg
  set f := tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) with hf
  constructor
  · -- the `𝓗` bound
    apply le_of_sq_le_sq
    have h1 : ENNReal.ofReal (2 * k) * a ^ 2 ≤ ENNReal.ofReal (2 * ν)⁻¹ * f ^ 2 := I2
    have h2 : a ^ 2 ≤ ENNReal.ofReal (2 * k)⁻¹ * (ENNReal.ofReal (2 * ν)⁻¹ * f ^ 2) := by
      calc a ^ 2 = ENNReal.ofReal (2 * k)⁻¹ * (ENNReal.ofReal (2 * k) * a ^ 2) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr
    have h3 : ENNReal.ofReal (2 * k)⁻¹ * (ENNReal.ofReal (2 * ν)⁻¹ * f ^ 2) =
        (ENNReal.ofReal ((2 * Real.sqrt (k * ν))⁻¹) * f) ^ 2 := by
      rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hs : Real.sqrt (k * ν) ^ 2 = k * ν := Real.sq_sqrt (by positivity)
      rw [inv_pow, mul_pow, hs]
      field_simp
    rw [← h3]
    exact h2
  · -- the `𝒯` bound for `G`
    apply le_of_sq_le_sq
    have h1 : ENNReal.ofReal ν * g ^ 2 ≤ ENNReal.ofReal ν⁻¹ * f ^ 2 :=
      le_trans le_add_self I1
    have h2 : g ^ 2 ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν⁻¹ * f ^ 2) := by
      calc g ^ 2 = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν * g ^ 2) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              inv_mul_cancel₀ hνpos.ne', ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr
    have h3 : ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν⁻¹ * f ^ 2) =
        (ENNReal.ofReal ν⁻¹ * f) ^ 2 := by
      rw [mul_pow, ← mul_assoc, ← pow_two]
    rw [← h3]
    exact h2

end UnforcedLeray.Short.IIIa
