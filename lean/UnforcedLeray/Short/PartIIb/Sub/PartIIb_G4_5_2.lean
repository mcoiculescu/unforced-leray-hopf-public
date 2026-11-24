import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5

/-!
# Part II-b, task `PartII-b:G4/5/2` (`InletJetBound`): decomposition

Source of record: `the November 2 reference manuscript`, lines 2316-2318 (inlet
with an age cutoff equal to one near zero and zero before the terminal time), 2346-2359 (the
periodized stream and every fixed derivative have exponential transverse decay with polynomial
`c` costs), 2360-2366 (the normalized lift `e_ε = e_0 + ε e_1` of the cut stream `χ(s)ψ`), 2386-2387
(`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|`).

Correction to the task spec: `χ = ageCutoff H` equals `1` for `s ≤ H/4` (far from the axis, large
`ϱ`) and `0` for `s ≥ H/2` (age `s = R²/ϱ²` is large NEAR the axis), so the inlet profile vanishes
for `s > H/2` and `E_i` vanishes in a neighbourhood of the axis; no planar-stream lift is needed.

Two true source facts:

* `RingLiftJet`: pure ring-chart calculus.  For a smooth profile `b` supported in `{s ≤ S}` and
  `R ≥ 1`, every Cartesian derivative of `N_v b(τ, ·)` of order `j` is bounded by
  `C_j (1+S)^{k_j} · M`, where `M` bounds the transversally weighted chart derivatives
  `(1+|η|)^j ‖D^l b‖`, `l ≤ j`.  The weight is forced: `η = R y₃/ϱ` has `∂_ϱ η = -η/ϱ`, so every
  Cartesian derivative of the chart carries one factor `1+|η|` (and no other unbounded factor:
  `ϱ⁻¹ = √s/R ≤ √S`), and the chain rule of order `j` produces at most `(1+|η|)^j`.  Without the
  weight the statement is false (`not_chartJets`, `Sub/PartII-b_G4_5_2_1_2.lean`, refutes the
  unweighted chart bound; `b = θ(s) sin η m₀` kills the unweighted lift bound).  A bound by a
  power of `|y₃|` cannot replace the weight: on `{age < S}` one has `|y₃| = ϱ|η|/R` with `ϱ`
  unbounded above.
* `InletProfileWeightedJets`: the inlet profile `ringStreamProfile R (χ(s) ψ_i)` is `C^∞`, vanishes
  for `s > H/2`, and for every weight `w` its chart derivatives of order `≤ j` satisfy
  `(1+|η|)^w ‖D^l b‖ ≤ C ν^{-k}` (exponential transverse decay of the stream, SP 2356-2358, with
  polynomial `c = ν⁻²` costs; the assembly is `inletProfileWeightedJets_of`,
  `Sub/PartII-b_G4_5_2_2_w.lean`).

`InletProfileJets` (the unweighted bound) is true but is no longer on the path of `InletJetBound`;
it is kept because `Sub/PartII-b_G4_5_2_2.lean` and `Sub/PartII-b_G4_5_2_2_4.lean` are built on it.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-- **Leaf A: Cartesian jet bound for a ring lift** (SP 2360-2366, 2386-2387; `R ≥ 1`, profile
supported in `s ≤ S`). The profile jets of order `≤ j` carry the transverse weight `(1+|η|)^j`,
which absorbs the factors `1+|η|` of the chart derivatives (`∂_ϱ η = -η/ϱ`). -/
def RingLiftJet : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R τ M : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 0 < S → 1 ≤ R → 0 ≤ M →
      ContDiff ℝ ∞ b → (∀ x : ℝ × (ℝ × ℝ), S < x.1 → b x = 0) →
      (∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ), (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l b x‖ ≤ M) →
      ∀ y : Space, ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤ C * (1 + S) ^ k * M

/-- **Chart jets of the inlet profile, unweighted** (true; not used by `inletJetBound_of`, which
needs `InletProfileWeightedJets`). -/
def InletProfileJets : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2), ContDiff ℝ ∞ (p.inletProfile i) ∧
        (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) ∧
        ∀ l ≤ j, ∀ x, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ C * (p.ν ^ k)⁻¹

/-- **Leaf B: transversally weighted chart jets of the inlet profile** (SP 2346-2366): the inlet
profile `e_ε = ringStreamProfile R (χ(s)ψ_i)` is `C^∞`, vanishes for `s > H/2`, and for all
orders `j` and weights `w`, `(1+|η|)^w ‖D^l e_ε‖ ≤ C ν^{-k}` for `l ≤ j` (the periodized stream and
every fixed derivative have exponential transverse decay with polynomial `c = ν⁻²` costs,
SP 2356-2358; `s ≤ H/2 = Σ/(2ν)` on the support; `ε ≤ 1`). -/
def InletProfileWeightedJets : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∀ j w : ℕ, ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2), ContDiff ℝ ∞ (p.inletProfile i) ∧
        (∀ x : ℝ × (ℝ × ℝ), p.H / 2 < x.1 → p.inletProfile i x = 0) ∧
        ∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ),
          (1 + |x.2.2|) ^ w * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ C * (p.ν ^ k)⁻¹

/-- **Conditional assembly of `InletJetBound`** (weight `w = j`). -/
theorem inletJetBound_of (hA : RingLiftJet) (hB : InletProfileWeightedJets) : InletJetBound := by
  intro Sig lam q hSig hq dm dp hdm j
  obtain ⟨CA, kA, hCA, hA'⟩ := hA j
  obtain ⟨CB, kB, ν₀, hCB, hν₀, hB'⟩ := hB Sig lam q hSig hq dm dp hdm j j
  refine ⟨CA * (1 + Sig) ^ kA * CB, kA + kB, min ν₀ 1, by positivity, lt_min hν₀ one_pos, ?_⟩
  intro p d hreg hν hSig' hmode i τ y
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  obtain ⟨hsm, hvan, hjet⟩ := hB' p d hreg hν0 hSig' hmode i
  have hH : 0 < p.H := p.H_pos
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  have hM : 0 ≤ CB * (p.ν ^ kB)⁻¹ := by positivity
  have hmain := hA' (p.H / 2) p.R τ (CB * (p.ν ^ kB)⁻¹) (p.inletProfile i) (by positivity) hR1 hM
    hsm hvan (fun l hl x => hjet l hl x) y
  have hS : 1 + p.H / 2 ≤ (1 + Sig) * (p.ν)⁻¹ := by
    have hHe : p.H = Sig / p.ν := by rw [Params.H, hSig']
    rw [hHe]
    have h1 : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv₀ hνpos |>.mpr hν1
    have h2 : 0 ≤ Sig / p.ν := by positivity
    have e : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by rw [div_eq_mul_inv]; ring
    rw [e]
    nlinarith [div_nonneg hSig.le hνpos.le]
  have hpow : (1 + p.H / 2) ^ kA ≤ ((1 + Sig) * p.ν⁻¹) ^ kA :=
    pow_le_pow_left₀ (by positivity) hS _
  have hCA' : 0 ≤ CA * CB * (p.ν ^ kB)⁻¹ := by positivity
  calc ‖iteratedFDeriv ℝ j (p.inlet i τ) y‖
      ≤ CA * (1 + p.H / 2) ^ kA * (CB * (p.ν ^ kB)⁻¹) := hmain
    _ ≤ CA * ((1 + Sig) * p.ν⁻¹) ^ kA * (CB * (p.ν ^ kB)⁻¹) := by
        gcongr
    _ = CA * (1 + Sig) ^ kA * CB * (p.ν ^ (kA + kB))⁻¹ := by
        rw [mul_pow, inv_pow, pow_add, mul_inv]; ring

end UnforcedLeray.Short.IIb
