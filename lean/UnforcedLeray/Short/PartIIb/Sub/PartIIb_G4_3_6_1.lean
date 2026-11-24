import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Part II-b, task `PartII-b:G4/3/6/1` (`RawJetVelocity`): decomposition

Source of record: `the November 2 reference manuscript` (SP) 2419-2423 (jets of
`b = (v₁, v₂ + εH)`), `sct:train` 261-291, `sct:transverse` 463-467, `sct:fixed-band` 468-478,
polynomial convention 255-258.

`RawJetVelocity` is reduced to bounds on the age/space jets `∂_s^ℓ D^j v` (`RawVelJets`), which come
from the tails (`RawVelTailJets`, `TrainTransverseTails`) and the fixed band (`RawVelBandJets`,
`TrainFixedBand` + the periodized vortex), plus the chart bridge `TrainChartBridge`
(`Axi.dS/dQ/dEta` of the chart function `trainProf` are bounded by the jets of `v`).
Proved here: `rawJetVelocity_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartI

/-- **Joint smoothness of the train velocity** for `s > 0`: from `BgRegime.train_stream_smooth`
(SP 397) and `v = ∇^⊥ψ` (`B0140.IsTrain.stream`, SP 261-291): `(s,z) ↦ v s z` is `C^∞` on
`(0,∞) × ℝ²`. -/
def TrainVelSmooth : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp →
    ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.v x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **Chart bridge for the velocity** (SP 2419-2423): at `s > 0` the chart derivatives of
`trainProf p = v` in the directions `s, q, η` are the jets `∂_s v`, `D v` of `v`, so their norms are
bounded by the norms of `ageJet 1 0`, `ageJet 0 1` (use `TrainVelSmooth`; `Axi.dS/dQ/dEta` are
`fderiv` in the unit directions, `Lib/Axisymmetric/RingChart.lean:56-60`). -/
def TrainChartBridge : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → ∀ x : Coord, 0 < x.1 →
    ‖trainProf p x‖ ≤ ‖ageJet 0 0 p.train.v x.1 x.2‖ ∧
    ‖Axi.dS (trainProf p) x‖ ≤ ‖ageJet 1 0 p.train.v x.1 x.2‖ ∧
    ‖Axi.dQ (trainProf p) x‖ ≤ ‖ageJet 0 1 p.train.v x.1 x.2‖ ∧
    ‖Axi.dEta (trainProf p) x‖ ≤ ‖ageJet 0 1 p.train.v x.1 x.2‖

/-- **Velocity jets** (SP 2419-2423): on `0 < s ≤ H = Σ/ν`, the jets `v, ∂_sv, Dv, ∂_s²v` of the
train velocity are `≤ C ν^{-N}`, uniformly in `η`.  Combination of `RawVelTailJets` and
`RawVelBandJets`. -/
def RawVelJets : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
        ‖ageJet 0 0 p.train.v x.1 x.2‖ + ‖ageJet 1 0 p.train.v x.1 x.2‖ +
          ‖ageJet 0 1 p.train.v x.1 x.2‖ + ‖ageJet 2 0 p.train.v x.1 x.2‖ ≤ C * (p.ν ^ N)⁻¹

/-- **Tail region** (SP 463-467 with `l = 0`, `S_* = Σ/ν`, `c = ν⁻²`): there is `C'` such that for
`|η| ≥ C'/ν + 2` the four jets of `v` are `≤ C ν^{-N}` (`TrainTransverseTails` for `ρ = 2`, jets
`(0,0),(1,0),(0,1),(2,0)`, `C'` the max of the four; `polyPS C N ν ν⁻² (Σ/ν)` is polynomial in
`ν⁻¹`; transport of `p.train` along `BgRegime.c_eq` as in `trainTransverseTailsUniform_of`,
`Short/PartIII-a/Sub/T23_4_6_Uniform.lean`). -/
def RawVelTailJets : Prop :=
  ∃ Cp : ℝ, 0 < Cp ∧ ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H → Cp / p.ν + 2 ≤ |x.2.2| →
        ‖ageJet 0 0 p.train.v x.1 x.2‖ + ‖ageJet 1 0 p.train.v x.1 x.2‖ +
          ‖ageJet 0 1 p.train.v x.1 x.2‖ + ‖ageJet 2 0 p.train.v x.1 x.2‖ ≤ C * (p.ν ^ N)⁻¹

/-- **Band region** (SP 468-478, `TrainFixedBand` for `ρ = 2`, `σ = νs`, plus the periodized
vortex `Train.Vc`): for every `Cp > 0`, for `|η| < Cp/ν + 2` the four jets of `v` are `≤ Cν^{-N}`.
Proof: `ageJet` of `v = (v - Vc) + Vc`, additive on `s > 0` by `TrainVelSmooth` and
`VcSmooth`, with `FixedBandJets` and `VcJetSup`. -/
def RawVelBandJets : Prop :=
  ∀ Cp : ℝ, 0 < Cp → ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H → |x.2.2| < Cp / p.ν + 2 →
        ‖ageJet 0 0 p.train.v x.1 x.2‖ + ‖ageJet 1 0 p.train.v x.1 x.2‖ +
          ‖ageJet 0 1 p.train.v x.1 x.2‖ + ‖ageJet 2 0 p.train.v x.1 x.2‖ ≤ C * (p.ν ^ N)⁻¹

/-- The periodized vortex is jointly smooth for `s > 0` (`Vc = periodize c (isoV ν s)`, explicit
heat vortex, `Lib/Train/PeriodizedVortex.lean`). -/
def VcSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c →
    ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => Train.Vc ν c x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **Sup jets of the periodized vortex** (SP 2205; `Train.Vc_bounds`, `Lib/Train/VortexBounds.lean:40`
gives the spatial derivatives pointwise `≤ C width^{-(3+j)/2}`, `1 ≤ width ν s ≤ c²`; the age
derivatives come from the heat equation for `isoV`): for each `ℓ, j`, `∂_s^ℓ D^j Vc ≤ Cν^{-N}` on
`0 < s ≤ Σ/ν`, `c = (ν²)⁻¹`. -/
def VcJetSup : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ ℓ j : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ s : ℝ, 0 < s → s ≤ Sig / ν → ∀ z : UnforcedLeray.Cyl.Plane,
      ‖ageJet ℓ j (fun r w => Train.Vc ν ((ν ^ 2)⁻¹) r w) s z‖ ≤ C * (ν ^ N)⁻¹

/-- **Fixed-band jets of `v - Vc`** (SP 468-478, `TrainFixedBand` with `ρ = 2`, `m = 0`, `L = ℓ`,
`k = j`): pointwise `‖∂_s^ℓ D^j (v - Vc)‖ ≤ Cν^{-N}` on `0 < s ≤ Σ/ν`.  Uses `‖f z‖ ≤ wSupNorm 0 f`
(`jap 0 = 1`), `sigmaJet ν ℓ j F s = ν^ℓ · ageJet ℓ j F s`, `trainPeriod 2 ν = (ν²)⁻¹`, and
`e^{C_Σ/ν - b_Σ c²} ≤ 1` for small `ν`. -/
def FixedBandJets : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ ℓ j : ℕ, ∃ (C : ℝ) (N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod 2 ν), IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ Sig / ν → ∀ z : UnforcedLeray.Cyl.Plane,
        ‖ageJet ℓ j (fun r w => tr.v r w - Train.Vc ν (trainPeriod 2 ν) r w) s z‖ ≤
          C * (ν ^ N)⁻¹

/-- Assembly of the velocity jets from the bridge and `RawVelJets`: for `s ≤ H = Σ/ν`,
`‖kAge b‖ ≤ (2s + |η|)·max(‖∂_s v‖,‖∂_η v‖)`, so `k = N + 1`. -/
theorem rawJetVelocity_of_leaves (hB : TrainChartBridge) (hJ : RawVelJets) : RawJetVelocity := by
  intro Sig hS dm dp hdm
  obtain ⟨C, N, ν₀, hC, hν₀, H⟩ := hJ Sig hS dm dp hdm
  refine ⟨C * (3 + 2 * Sig), N + 1, 1, min ν₀ 1, by positivity, lt_min hν₀ one_pos, ?_⟩
  intro p d hd hν hS' x hx0 hxH
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0 : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  obtain ⟨b0, b1, b2, b3⟩ := hB p d dm dp hd x hx0
  have hJ' := H p d hd hν0 hS' x hx0 hxH
  set B : ℝ := C * (p.ν ^ N)⁻¹ with hBdef
  have hBn : 0 ≤ B := by positivity
  have n0 := norm_nonneg (ageJet 0 0 p.train.v x.1 x.2)
  have n1 := norm_nonneg (ageJet 1 0 p.train.v x.1 x.2)
  have n2 := norm_nonneg (ageJet 0 1 p.train.v x.1 x.2)
  have n3 := norm_nonneg (ageJet 2 0 p.train.v x.1 x.2)
  have hH : x.1 ≤ Sig / p.ν := by
    have : p.H = p.ageCut / p.ν := rfl
    rw [← hS', ← this]; exact hxH
  have hs : x.1 * p.ν ≤ Sig := by
    rwa [le_div_iff₀ hνp] at hH
  have hk : ‖kAge (trainProf p) x‖ ≤ 2 * x.1 * B + |x.2.2| * B := by
    unfold kAge
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (b1.trans (by linarith)) (by linarith)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (b3.trans (by linarith)) (abs_nonneg _)
  have hpow : (p.ν ^ (N + 1))⁻¹ = (p.ν ^ N)⁻¹ * p.ν⁻¹ := by
    rw [pow_succ, mul_inv]
  have hinv : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνp).2 hν1
  have hsx : x.1 ≤ Sig * p.ν⁻¹ := by
    rw [← div_eq_mul_inv]; exact hH
  have ha : 0 ≤ |x.2.2| := abs_nonneg _
  have hB1 : B * p.ν⁻¹ = C * (p.ν ^ (N + 1))⁻¹ := by rw [hpow, hBdef]; ring
  have hfin : ‖trainProf p x‖ + ‖Axi.dQ (trainProf p) x‖ + ‖Axi.dEta (trainProf p) x‖ +
      ‖kAge (trainProf p) x‖ ≤ B * (3 + 2 * Sig * p.ν⁻¹ + |x.2.2|) := by
    have : 2 * x.1 * B ≤ 2 * (Sig * p.ν⁻¹) * B := by
      apply mul_le_mul_of_nonneg_right _ hBn; linarith
    nlinarith
  have hrhs : B * (3 + 2 * Sig * p.ν⁻¹ + |x.2.2|) ≤
      C * (3 + 2 * Sig) * (p.ν ^ (N + 1))⁻¹ * (1 + |x.2.2|) ^ 1 := by
    rw [pow_one]
    have : 3 + 2 * Sig * p.ν⁻¹ + |x.2.2| ≤ (3 + 2 * Sig) * (1 + |x.2.2|) * p.ν⁻¹ := by
      have hS0 := hS.le
      have hi := inv_nonneg.2 hνp.le
      nlinarith [mul_nonneg hS0 ha, mul_nonneg hS0 hi, mul_nonneg (mul_nonneg hS0 ha) hi, mul_nonneg ha hi]
    calc B * (3 + 2 * Sig * p.ν⁻¹ + |x.2.2|) ≤ B * ((3 + 2 * Sig) * (1 + |x.2.2|) * p.ν⁻¹) :=
          mul_le_mul_of_nonneg_left this hBn
      _ = _ := by rw [hBdef, hpow]; ring
  exact hfin.trans hrhs

end UnforcedLeray.Short.IIb
