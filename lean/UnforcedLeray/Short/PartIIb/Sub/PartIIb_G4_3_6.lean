import UnforcedLeray.Short.PartIIb.Sub.G4_3_org

/-!
# Part II-b, task `PartII-b:G4/3/6` (`RawJetBound`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 2419-2423
(`b = (v₁, v₂ + εH)`, derivative types `s∂_ηb`, `s[∂_q - ε(K+1)]b`, `εsv₁`), Part I `sct:train`
(SP 261-291), `sct:transverse` (463-467), `sct:fixed-band` (468-478), polynomial convention
(255-258).  `RawJetBound` splits into the velocity jets and the raised-stream jets.

Proved here: `rawJetBound_of_parts` (merging the constants), `JetSplit`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- **Velocity jets** (SP 2419-2423; `sct:train`, `sct:transverse`, `sct:fixed-band`): on
`0 < s ≤ H = Σ/ν`, `v`, `∂_qv`, `∂_ηv`, `Kv` are `≤ Cν^{-k}(1+|η|)^N`.  Transport `p.train` along
`BgRegime.c_eq` (`p.c = ν⁻² = PartI.trainPeriod 2 ν`, pattern of `trainTransverseTailsUniform_of`,
`Short/PartIII-a/Sub/T23_4_6_Uniform.lean`); `|η| ≥ C'/ν + 2`: `TrainTransverseTails` (jets of `v`
with `S_* = Σ/ν`); `|η| < C'/ν + 2`: `TrainFixedBand` (`σ = νs`, `e^{C_Σ/ν - b_Σc²} ≤ 1`) plus
polynomial jets of the periodized vortex `Train.Vc` (`Lib/Train/PeriodizedVortex.lean`). -/
def RawJetVelocity : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
        ‖trainProf p x‖ + ‖Axi.dQ (trainProf p) x‖ + ‖Axi.dEta (trainProf p) x‖ +
            ‖kAge (trainProf p) x‖ ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N

/-- **Raised-stream jets** (SP 2419-2423): on `0 < s ≤ H`, `H = (1-K)ψ = ψ - η∂_ηψ - 2s∂_sψ`
and `∂_qH`, `∂_ηH`, `KH` are `≤ Cν^{-k}(1+|η|)^N`.  `ψ`, `∂_sψ`, `∂_s²ψ` are obtained by
integrating `∂_ηψ = -v₀` (`IsTrain.stream`) in `η` from the tail region (`TrainTransverseTails`,
which also bounds `ψ`), `ψ` smooth on `s > 0` by `BgRegime.train_stream_smooth`; fixed band as
for `RawJetVelocity`. -/
def RawJetRaised : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
        |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x| +
            |kAge (raisedProf p) x| ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N

theorem jet_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {k k' : ℕ} (hk : k ≤ k') :
    (ν ^ k)⁻¹ ≤ (ν ^ k')⁻¹ := by
  apply inv_anti₀ (pow_pos hν k')
  exact pow_le_pow_of_le_one hν.le hν1 hk

theorem rawJetBound_of_parts (h1 : RawJetVelocity) (h2 : RawJetRaised) : RawJetBound := by
  intro Sig hS dm dp hdm
  obtain ⟨C1, k1, N1, ν1, hC1, hν1, H1⟩ := h1 Sig hS dm dp hdm
  obtain ⟨C2, k2, N2, ν2, hC2, hν2, H2⟩ := h2 Sig hS dm dp hdm
  refine ⟨C1 + C2, max k1 k2, max N1 N2, min (min ν1 ν2) 1, by positivity, ?_, ?_⟩
  · exact lt_min (lt_min hν1 hν2) one_pos
  intro p d hd hν hS' x hx0 hxH
  have hνp : 0 < p.ν := p.ν_pos
  have hle1 : p.ν ≤ ν1 := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle2 : p.ν ≤ ν2 := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have a1 := H1 p d hd hle1 hS' x hx0 hxH
  have a2 := H2 p d hd hle2 hS' x hx0 hxH
  have hb : (1 : ℝ) ≤ 1 + |x.2.2| := by linarith [abs_nonneg x.2.2]
  have hpos : (0 : ℝ) ≤ 1 + |x.2.2| := by linarith
  have key : ∀ (C : ℝ) (k N : ℕ), 0 < C → k ≤ max k1 k2 → N ≤ max N1 N2 →
      C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N ≤
        C * (p.ν ^ max k1 k2)⁻¹ * (1 + |x.2.2|) ^ max N1 N2 := by
    intro C k N hC hk hN
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (jet_mono hνp hle3 hk) hC.le
    · exact pow_le_pow_right₀ hb hN
    · positivity
    · exact mul_nonneg hC.le (inv_nonneg.2 (pow_pos hνp _).le)
  have b1 := key C1 k1 N1 hC1 (le_max_left _ _) (le_max_left _ _)
  have b2 := key C2 k2 N2 hC2 (le_max_right _ _) (le_max_right _ _)
  calc _ = (‖trainProf p x‖ + ‖Axi.dQ (trainProf p) x‖ + ‖Axi.dEta (trainProf p) x‖ +
            ‖kAge (trainProf p) x‖) +
          (|raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x| +
            |kAge (raisedProf p) x|) := by ring
    _ ≤ _ := by
      calc _ ≤ C1 * (p.ν ^ k1)⁻¹ * (1 + |x.2.2|) ^ N1 + C2 * (p.ν ^ k2)⁻¹ * (1 + |x.2.2|) ^ N2 :=
            add_le_add a1 a2
        _ ≤ _ := add_le_add b1 b2
        _ = _ := by ring

end UnforcedLeray.Short.IIb
