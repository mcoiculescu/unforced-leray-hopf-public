import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/2` (`RawJetRaised`): decomposition

Source of record: `the November 2 reference manuscript` (SP) 2419-2423, 2412-2423
(`H = ψ - η∂_ηψ - 2s∂_sψ = (1-K)ψ`), `sct:train` 261-291, `sct:transverse` 463-467.

`H`, `∂_qH`, `∂_ηH`, `KH` are linear in the jets `∂_s^ℓ D^j ψ`, `ℓ + j ≤ 2`, with coefficients
polynomial in `(1, η, s)` (`RaisedChartBridge`).  Those jets are bounded by `RawPsiJets`: the
jets with `j ≥ 1` are first jets of `v` (`∂_ηψ = -v₀`, `∂_qψ = v₁`, `IsTrain.stream`, so
`RawVelJets` of the sibling task `PartII-b:G4/3/6/1` applies), and `ψ, ∂_sψ, ∂_s²ψ` come from the
tails (`RawPsiTailJets`) integrated in `η` over the band of length `≈ 2C'/ν`.
Proved here: `rawJetRaised_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartI

/-- **Chart bridge for the raised stream** (SP 2412-2423): for `s > 0`, with `A` the sum of the
norms of the six jets `ℓ + j ≤ 2` of `ψ` at `(s, z)`,
`|H| + |∂_qH| + |∂_ηH| + |KH| ≤ 20 (1 + |η| + s)² A`, where
`H = ψ - η∂_ηψ - 2s∂_sψ` (`C03.raisedStream`, `raisedProf`),
`∂_sH = -∂_sψ - η∂_s∂_ηψ - 2s∂_s²ψ`, `∂_ηH = -η∂_η²ψ - 2s∂_s∂_ηψ`,
`∂_qH = ∂_qψ - η∂_q∂_ηψ - 2s∂_s∂_qψ`, `KH = 2s∂_sH + η∂_ηH`.  Uses `BgRegime.train_stream_smooth`
(joint smoothness, symmetry of second derivatives), `Axi.dS/dQ/dEta` as `fderiv` in unit
directions. -/
def RaisedChartBridge : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → ∀ x : Coord, 0 < x.1 →
    |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x| +
        |kAge (raisedProf p) x| ≤
      20 * (1 + |x.2.2| + x.1) ^ 2 *
        (‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖)

/-- **Tail jets of the stream** (SP 463-467 with `l = 0`, `S_* = Σ/ν`, `c = ν⁻²`;
`TrainTransverseTails` for `ρ = 2`, the `tr.ψ` clause, jets `(0,0),(1,0),(2,0)`): there is `C'`
such that for `|η| ≥ C'/ν + 2` the jets `ψ, ∂_sψ, ∂_s²ψ` are `≤ Cν^{-N}`.  Transport of `p.train`
as in `trainTransverseTailsUniform_of`. -/
def RawPsiTailJets : Prop :=
  ∃ Cp : ℝ, 0 < Cp ∧ ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H → Cp / p.ν + 2 ≤ |x.2.2| →
        ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 2 0 p.train.ψ x.1 x.2‖ ≤ C * (p.ν ^ N)⁻¹

/-- **Jets of the stream** (SP 2419-2423): on `0 < s ≤ Σ/ν`, uniformly in `η`, the six jets
`ℓ + j ≤ 2` of `ψ` are `≤ Cν^{-N}`.  Proof from `RawPsiTailJets`, `RawVelJets`, `TrainVelSmooth`
and `IsTrain.stream` (`∂_ηψ = -v₀`, `∂_qψ = v₁`, `B0140.IsTrain`): the jets with `j ≥ 1` are
jets of `v` of order `≤ 1`, resp. `∂_s v`; `ψ, ∂_sψ, ∂_s²ψ` at `(s,q,η)` equal their value at
`η* = ±(C'/ν + 2)` minus `∫ ∂_η ∂_s^ℓ ψ = ∓∫ ∂_s^ℓ v₀` over a segment of length `≤ 2C'/ν + 4 + |η|`
... (take `η*` the nearest of `±(C'/ν+2)` when `|η| < C'/ν + 2`; length `≤ 2C'/ν + 4`). -/
def RawPsiJets : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
        ‖ageJet 0 0 p.train.ψ x.1 x.2‖ + ‖ageJet 1 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 0 1 p.train.ψ x.1 x.2‖ + ‖ageJet 2 0 p.train.ψ x.1 x.2‖ +
          ‖ageJet 1 1 p.train.ψ x.1 x.2‖ + ‖ageJet 0 2 p.train.ψ x.1 x.2‖ ≤ C * (p.ν ^ N)⁻¹

/-- Assembly of the raised-stream jets from the bridge and `RawPsiJets`: `s ≤ Σ/ν` gives
`(1 + |η| + s)² ≤ (1+Σ)²ν⁻²(1+|η|)²`, so `k = N + 2`. -/
theorem rawJetRaised_of_leaves (hB : RaisedChartBridge) (hJ : RawPsiJets) : RawJetRaised := by
  intro Sig hS dm dp hdm
  obtain ⟨C, N, ν₀, hC, hν₀, H⟩ := hJ Sig hS dm dp hdm
  refine ⟨20 * (1 + Sig) ^ 2 * C, N + 2, 2, min ν₀ 1, by positivity, lt_min hν₀ one_pos, ?_⟩
  intro p d hd hν hS' x hx0 hxH
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have h1 := hB p d dm dp hd x hx0
  have h2 := H p d hd hν0 hS' x hx0 hxH
  set B : ℝ := C * (p.ν ^ N)⁻¹ with hBdef
  have hBn : 0 ≤ B := by positivity
  have hH : x.1 ≤ Sig / p.ν := by
    have : p.H = p.ageCut / p.ν := rfl
    rw [← hS', ← this]; exact hxH
  have hinv : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνp).2 hν1
  have hsx : x.1 ≤ Sig * p.ν⁻¹ := by rw [← div_eq_mul_inv]; exact hH
  have ha : 0 ≤ |x.2.2| := abs_nonneg _
  have hi := inv_nonneg.2 hνp.le
  have hsum : 1 + |x.2.2| + x.1 ≤ (1 + Sig) * (1 + |x.2.2|) * p.ν⁻¹ := by
    have hS0 := hS.le
    nlinarith [mul_nonneg hS0 ha, mul_nonneg hS0 hi, mul_nonneg (mul_nonneg hS0 ha) hi,
      mul_nonneg ha hi]
  have hsq : (1 + |x.2.2| + x.1) ^ 2 ≤ ((1 + Sig) * (1 + |x.2.2|) * p.ν⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hsum 2
  have hpow : (p.ν ^ (N + 2))⁻¹ = (p.ν ^ N)⁻¹ * p.ν⁻¹ ^ 2 := by
    rw [pow_add, mul_inv, inv_pow]
  calc _ ≤ 20 * (1 + |x.2.2| + x.1) ^ 2 * B := h1.trans
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ ≤ 20 * ((1 + Sig) * (1 + |x.2.2|) * p.ν⁻¹) ^ 2 * B := by
        apply mul_le_mul_of_nonneg_right _ hBn
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by rw [hBdef, hpow]; ring

end UnforcedLeray.Short.IIb
