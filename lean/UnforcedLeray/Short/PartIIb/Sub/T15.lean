import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b, task `PartII-b:T15`: the Hilbert energy tools (conditional)

Source of record: `the November 2 reference manuscript`, lines 1955-1983 (first part
of the proof of `bg:lp-free-comparison`): the drift identity (1975-1979)

`Re ⟨S w, χ² w⟩_{H_2} = (1/4)‖χ w‖²_{H_2} - ∫ s χ χ_s |w|² dH_2`

and the two-term principal diffusion difference (1960-1966)

`ν ε ⟨√s L_1 v, √s Q_ε(χ² w)⟩ + ν ε ⟨√s ∂_q v, √s L_1(χ² w)⟩`, `L_1 = 2S + η∂_η + 1`.




Lean statement) cannot be proved as it stands. Here both lemmas are given exact Lean statements.

* `drift_identity_H2` is stated for `w, Sw ∈ H_2` with `Sw` the weak `S`-derivative of `w` in
  distributions on `s > 0` (`HasWeakVec vS dZero w Sw`) and a smooth `q`-periodic cutoff `χ`
  compactly supported in `(s, η)` inside `s > 0`. Proof: periodic weak identity in the measure
  `s^{-3/2} ds` (`WeakSPeriodicExtension`), then the weak product rule `S|w|² = 2 Re(Sw w̄)`
  (`WeakProductRuleH2`); the drift identity is that rule for `ψ = χ²`.
* `diffusion_difference_terms` is the exact algebra behind the "two terms". With
  `Q_ε = ∂_q - ε L_1` (so `∂_q = Q_ε + ε L_1`), pointwise
  `∂_q v \bar{∂_q t} - Q_ε v \bar{Q_ε t} = ε L_1 v \bar{Q_ε t} + ε ∂_q v \bar{L_1 t}`
  (both sides of the identity integrate with weight `s` against `H_2`, i.e. `⟨√s ·, √s ·⟩`). It is
  stated for arbitrary profiles `v, t` with the four weak derivatives
  (`∂_q, Q_ε, S, ∂_η`); the relation `∂_q = Q_ε + ε(2S + η∂_η + 1)` between the weak
  derivatives (`WeakQDecomposition`) is the only analytic input.

What this task does NOT supply (belongs to `PartII-b:T16`): the chart-level weak equations of
`u = T_εF` and `v = T_0F` tested against `χ² w`, i.e. the extension of the weak response equations
(`IsResponse`, tested against smooth Cartesian phase tests; `IsFlatResponse`, tested against planar
solenoidal tests) to the test `χ² w` of first-derivative regularity. These are not stated
anywhere in Lean yet.

Proved here: `driftIdentityH2_of`, `diffusionDifferenceTerms_of`, `hilbertEnergy_of`. Leaves:
`WeakSPeriodicExtension` (`PartII-b:T15/1`), `WeakProductRuleH2` (`PartII-b:T15/2`),
`WeakQDecomposition` (`PartII-b:T15/3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A cutoff of the drift identity: smooth, `c`-periodic in `q`, vanishing outside
`σ ≤ s ≤ H`, `|η| ≤ L` for some `σ > 0` (SP 1692-1694: `χ` supported in `σ ≤ s ≤ H_1`,
`|η| ≤ L_1`). -/
structure DriftCutoff (c : ℝ) (χ : Coord → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  periodic : ∀ x, χ (qShift c x) = χ x
  supp : ∃ σ H L : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → χ x = 0

/-- The weak identity `S w = Sw` against `q`-periodic tests, in the measure `s^a ds ⊗ dq/c dη`
(`ageμ c a`): for `φ` smooth, `c`-periodic in `q`, compactly supported in `(s, η)` inside `s > 0`,
`∫ Sw φ = -∫ w ((1 + a) φ + s ∂_sφ)` componentwise (transpose of `S = s∂_s` in the measure
`s^a ds` is `-(1 + a) - s∂_s`). -/
def PeriodicWeakS (c a : ℝ) (w Sw : CProf) : Prop :=
  ∀ φ : Coord → ℝ, ContDiff ℝ ∞ φ → (∀ x, φ (qShift c x) = φ x) →
    (∃ σ H L : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → φ x = 0) →
    ∀ i : Fin 2, ∫ x, Sw x i * (φ x : ℂ) ∂(Axi.ageμ c a) =
      -∫ x, w x i * (((1 + a) * φ x + x.1 * cpd 0 φ x : ℝ) : ℂ) ∂(Axi.ageμ c a)

/-- **Leaf `PartII-b:T15/1`** (SP 1975-1979, periodization). `HasWeakVec vS dZero` tests only
functions with compact support in all of `Coord` (including `q`); for `c`-periodic `w, Sw ∈ H_2`
it extends to `q`-periodic tests (`PeriodicWeakS` at `a = -3/2`, the `H_2` weight). Proof: `S`
has no `q`-derivative, so with `θ ∈ C_c^∞(ℝ)`, `Σ_n θ(q - nc) = 1`, the test `s^a θ(q)φ` is
admissible and `S^T(θφ s^a) = θ S^T(φ s^a)`; unfold `∫_ℝ θ f = ∫_cell f` for periodic `f`
(`Lib/CylinderB/Periodize.lean`: `integral_cell_periodize_mul`). Convert between `ageμ c a` and
Lebesgue with `lintegral_ageμ` / `prod_withDensity_left` (`Lib/AxisymmetricB/Lift.lean`). -/
def WeakSPeriodicExtension : Prop :=
  ∀ (c : ℝ) (w Sw : CProf), 0 < c → InHr c 2 w → InHr c 2 Sw → HasWeakVec vS dZero w Sw →
    PeriodicWeakS c (-3 / 2) w Sw

/-- **Leaf `PartII-b:T15/2`** (SP 1975-1979, weak product rule in the `H_2` measure). If the
periodic weak identity `PeriodicWeakS c (-3/2) w Sw` holds with `w, Sw ∈ H_2`, then for every
smooth `q`-periodic `ψ` compactly supported in `(s, η)` inside `s > 0`:
`Re ⟨Sw, ψ w⟩_{H_2} = (1/4)∫ ψ |w|² dH_2 - (1/2)∫ s ψ_s |w|² dH_2`, i.e. `S|w|² = 2 Re(Sw \bar w)`
tested in the measure `s^{-3/2} ds` (`S^T = -(1 + a) - s∂_s`, `a = -3/2`).
Proof: on `s ∈ [σ, H]` the weight is bounded above and below, so `w, Sw ∈ L²_{loc}` in
`(s, q, η)`. Mollify `w` in `s` only (Friedrichs): `w_δ = ρ_δ *_s w` satisfies `∂_s w_δ` classical,
`S w_δ = (Sw)_δ + [commutator]` with commutator `→ 0` in `L²` on the support of `ψ`; for `w_δ`
the identity is the classical 1D product rule; let `δ → 0` (`L²` convergence of `w_δ`, `Sw_δ`).
The integrals are finite: `ψ`, `s ψ_s` are bounded (continuous, periodic, compact in `(s, η)`)
and `w, Sw ∈ L²(hMeas c 2)` (Hölder, `MemLp.integrable_mul`). -/
def WeakProductRuleH2 : Prop :=
  ∀ (c : ℝ) (w Sw : CProf), 0 < c → InHr c 2 w → InHr c 2 Sw → PeriodicWeakS c (-3 / 2) w Sw →
    ∀ ψ : Coord → ℝ, ContDiff ℝ ∞ ψ → (∀ x, ψ (qShift c x) = ψ x) →
      (∃ σ H L : ℝ, 0 < σ ∧ ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → ψ x = 0) →
      (∫ x, ∑ i : Fin 2, Sw x i * (starRingEnd ℂ) (((ψ x : ℝ) : ℂ) * w x i) ∂(hMeas c 2)).re =
        (1 / 4) * ∫ x, ψ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) -
          (1 / 2) * ∫ x, x.1 * cpd 0 ψ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2)

/-- **`drift_identity_H2`** (SP 1975-1979): for `w, Sw ∈ H_2` with `Sw` the weak `S`-derivative of
`w` and a cutoff `χ`, `Re ⟨S w, χ² w⟩_{H_2} = (1/4)‖χ w‖²_{H_2} - ∫ s χ χ_s |w|² dH_2`. -/
def DriftIdentityH2 : Prop :=
  ∀ (c : ℝ) (w Sw : CProf) (χ : Coord → ℝ), 0 < c → InHr c 2 w → InHr c 2 Sw →
    HasWeakVec vS dZero w Sw → DriftCutoff c χ →
    (∫ x, ∑ i : Fin 2, Sw x i * (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * w x i) ∂(hMeas c 2)).re =
      (1 / 4) * ∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) -
        ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2)

/-- **Leaf `PartII-b:T15/3`** (SP 1960-1966, `∂_q = Q_ε + ε L_1`). If a profile `b` has the four weak
first-order derivatives `∂_q b = Db`, `Q_ε b = Qb` (with `Q_ε = ∂_q - ε(2S + η∂_η + 1)`, i.e.
`vQ ε`, `dQ ε`), `S b = Sb`, `∂_η b = Eb` in distributions on `s > 0`, then
`Db = Qb + ε(2 Sb + η Eb + b)` almost everywhere on `s > 0` (hence `hMeas c 2`-a.e.).
Proof: `coordTranspose` is linear in the coefficient pair `(v, d)`; for every test `φ`,
`transpose_Q φ + ε(2 S^Tφ + (η ·)^T-term + φ) = -∂_qφ` (direct computation with
`vQ ε = (-2εs, 1, -εη)`, `dQ ε = -ε`, using the test `ηφ` for the `η Eb` term). So
`Db - (Qb + ε(2 Sb + η Eb + b))` has all pairings against tests zero and is locally integrable on
`s > 0`; apply the fundamental lemma (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` or
the repository's `hasWeakFO_unique`). -/
def WeakQDecomposition : Prop :=
  ∀ (c ε : ℝ) (b Db Qb Sb Eb : CProf), 0 < c →
    HasWeakVec vQ0 dZero b Db → HasWeakVec (vQ ε) (dQ ε) b Qb →
    HasWeakVec vS dZero b Sb → HasWeakVec vEta dZero b Eb →
    ∀ᵐ x ∂(hMeas c 2), ∀ i : Fin 2,
      Db x i = Qb x i + (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i)

/-- **`diffusion_difference_terms`** (SP 1960-1966): for profiles `v` (the flat response) and `t`
(the test profile `χ² w`) with the four weak derivatives, the weighted difference of the `q`-Dirichlet
forms `ν s(∂_q v \bar{∂_q t} - Q_ε v \bar{Q_ε t})` has exactly the two terms
`ν ε s(L_1 v \bar{Q_ε t})` and `ν ε s(∂_q v \bar{L_1 t})`, `L_1 = 2S + η∂_η + 1`; here
`⟨√s a, √s b⟩_{H_2} = ∫ s a \bar b dH_2`. -/
def DiffusionDifferenceTerms : Prop :=
  ∀ (c ε ν : ℝ) (v Dv Qv Sv Ev t Dt Qt St Et : CProf), 0 < c →
    HasWeakVec vQ0 dZero v Dv → HasWeakVec (vQ ε) (dQ ε) v Qv →
    HasWeakVec vS dZero v Sv → HasWeakVec vEta dZero v Ev →
    HasWeakVec vQ0 dZero t Dt → HasWeakVec (vQ ε) (dQ ε) t Qt →
    HasWeakVec vS dZero t St → HasWeakVec vEta dZero t Et →
    (ν : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        (Dv x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i)) ∂(hMeas c 2) =
      (ν : ℂ) * (ε : ℂ) * ∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
        ((2 * Sv x i + (x.2.2 : ℂ) * Ev x i + v x i) * (starRingEnd ℂ) (Qt x i) +
          Dv x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i)) ∂(hMeas c 2)

/-- `fderiv` of `χ²` in the `s` direction. -/
theorem cpd_zero_sq {χ : Coord → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : Coord) :
    cpd 0 (fun y => χ y ^ 2) x = 2 * χ x * cpd 0 χ x := by
  have hd : DifferentiableAt ℝ χ x := (hχ.differentiable (by simp)) x
  have h : HasFDerivAt (fun y => χ y ^ 2) ((2 * χ x) • fderiv ℝ χ x) x := by
    have := hd.hasFDerivAt.pow 2
    simpa [pow_one] using this
  unfold cpd
  rw [h.fderiv]
  simp [mul_comm]

/-- **Conditional drift identity.** -/
theorem driftIdentityH2_of (h1 : WeakSPeriodicExtension) (h2 : WeakProductRuleH2) :
    DriftIdentityH2 := by
  intro c w Sw χ hc hw hSw hS hχ
  have hP := h1 c w Sw hc hw hSw hS
  have key := h2 c w Sw hc hw hSw hP (fun x => χ x ^ 2) (hχ.smooth.pow 2)
    (fun x => by simp [hχ.periodic x])
    (by
      obtain ⟨σ, H, L, hσ, hs⟩ := hχ.supp
      exact ⟨σ, H, L, hσ, fun x hx => by simp [hs x hx]⟩)
  rw [key]
  have e : ∀ x : Coord, x.1 * cpd 0 (fun y => χ y ^ 2) x * ∑ i : Fin 2, ‖w x i‖ ^ 2 =
      2 * (x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2) := by
    intro x
    rw [cpd_zero_sq hχ.smooth x]
    ring
  simp_rw [e]
  rw [integral_const_mul]
  ring

/-- **Conditional diffusion difference.** -/
theorem diffusionDifferenceTerms_of (hQ : WeakQDecomposition) : DiffusionDifferenceTerms := by
  intro c ε ν v Dv Qv Sv Ev t Dt Qt St Et hc h1 h2 h3 h4 h5 h6 h7 h8
  have hv := hQ c ε v Dv Qv Sv Ev hc h1 h2 h3 h4
  have ht := hQ c ε t Dt Qt St Et hc h5 h6 h7 h8
  have hae : (fun x : Coord => (x.1 : ℂ) * ∑ i : Fin 2,
        (Dv x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i))) =ᵐ[hMeas c 2]
      fun x => (ε : ℂ) * ((x.1 : ℂ) * ∑ i : Fin 2,
        ((2 * Sv x i + (x.2.2 : ℂ) * Ev x i + v x i) * (starRingEnd ℂ) (Qt x i) +
          Dv x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))) := by
    filter_upwards [hv, ht] with x hx1 hx2
    have hsum : ∑ i : Fin 2, (Dv x i * (starRingEnd ℂ) (Dt x i) -
          Qv x i * (starRingEnd ℂ) (Qt x i)) =
        (ε : ℂ) * ∑ i : Fin 2, ((2 * Sv x i + (x.2.2 : ℂ) * Ev x i + v x i) *
          (starRingEnd ℂ) (Qt x i) +
            Dv x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx2 i, hx1 i]
      simp only [map_add, map_mul, Complex.conj_ofReal]
      ring
    rw [hsum]
    ring
  rw [integral_congr_ae hae, integral_const_mul]
  ring

/-- **Conditional Hilbert energy tools** (target of `PartII-b:T15`). -/
theorem hilbertEnergy_of (h1 : WeakSPeriodicExtension) (h2 : WeakProductRuleH2)
    (hQ : WeakQDecomposition) : DriftIdentityH2 ∧ DiffusionDifferenceTerms :=
  ⟨driftIdentityH2_of h1 h2, diffusionDifferenceTerms_of hQ⟩

end UnforcedLeray.Short.IIb
