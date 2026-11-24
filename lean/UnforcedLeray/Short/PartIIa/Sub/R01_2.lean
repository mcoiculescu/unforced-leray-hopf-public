import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `PartII-a:R01/2`: the zero-age pressure profile (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`, third component: the decaying-gauge pressure itself), read at ages
`0 < s ≤ 1`.

Target: `EarlyPressureProfile` (`Sub/R01.lean`): for every mixed jet
`∂_s^ℓ ∂_η^a ∂_q^b p` of the pressure profile of an exact train, `(1+η²)^m |·| ≤ C (1+c+ν⁻¹)^d`
for `0 < s ≤ 1`.


partials `∂_η, ∂_q, ∂_s` of `trainProfile T.p` to the jets `ageJet` of `TrainFluctuationDecay`.
That calculus is the three leaves `ProfileIterComm`, `ProfileDict`, `SliceJetBound` of
`Sub/R02_2.lean` (shared with `PartII-a:R02/2`; their proofs are the tasks
`Tasks/R02/FluctuationProfile/{IterComm,ProfileDict,SliceJetBound}.lean`).  Granting them, this file
proves `earlyPressureProfile_of_sub`:

* `ProfileIterComm` with `i = 0` moves `∂_s^ℓ` inside: `∂_s^ℓ ∂_η^a ∂_q^b p = ∂_η^a ∂_q^b ∂_s^ℓ p`
  for `s > 0` (smoothness of `trainProfile T.p` for `s > 0` from `LateProfileSmooth`);
* `ProfileJetBound` (`profileJetBound_of`, from `ProfileDict` and `SliceJetBound`) bounds this by
  `‖ageJet ℓ (a+b) T.p s (q, η)‖`;
* the third component of `TrainFluctuationDecay` with weight `2m` (`√(jap (2m) z) = (1+η²)^m`,
  `sqrt_jap_even`) bounds the latter by `polyP C N ν c · e^{-κνs/c²} ≤ polyP C N ν c = polyConst C N ν c`
  (the pressure has no mean part, and the exponential is `≤ 1` for `s > 0`).

The unconditional statement `earlyPressureProfile_of (hF) (hS) : EarlyPressureProfile` is the task
file `Short/PartII-a/Tasks/R01/EarlyPressureProfile.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (ageJet)

/-- **`PartII-a:R01/2`, conditional** (`EarlyPressureProfile`): the zero-age pressure profile
bounds follow from `TrainFluctuationDecay` (third component), the profile smoothness, and the
calculus leaves `ProfileIterComm`, `ProfileDict`, `SliceJetBound`. -/
theorem earlyPressureProfile_of_sub (hC : ProfileIterComm) (hD : ProfileDict)
    (hJ : SliceJetBound) (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hS : LateProfileSmooth) : EarlyPressureProfile := by
  intro ρ m a b ℓ hρ
  obtain ⟨C, N, κ, ν₀, hC0, hκ, hν₀, H⟩ := hF ρ hρ (2 * m) ℓ (a + b)
  refine ⟨ν₀, C, N, hν₀, ?_⟩
  intro ν hν ψ p hψ x hx0 hx1
  obtain ⟨T, hT, rfl, rfl⟩ := hψ
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hsm : ContDiffOn ℝ ∞ (trainProfile T.p) {y : ProfilePoint | 0 < y.2.2} :=
    (hS ν (ν ^ (-ρ)) hν0 hc T hT).2
  -- the third component of `TrainFluctuationDecay` at age `s = x.2.2`
  have Hs := H ν hν0 hν.2.le T hT x.2.2 hx0
  obtain ⟨_, _, ⟨_, hp⟩⟩ := Hs
  have hpos : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν0
    linarith
  have hP : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) := by
    unfold UnforcedLeray.Short.PartI.polyP
    positivity
  have hE : Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2 := by positivity
    linarith
  have hB : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
      Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) :=
    mul_nonneg hP (Real.exp_pos _).le
  -- pointwise bound on the jet norm
  have h2 := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm hB hp (x.1, x.2.1)
  rw [sqrt_jap_even] at h2
  -- commute `∂_s^ℓ` inside, then bound by the jet
  have hcomm := hC (trainProfile T.p) hsm 0 a b ℓ x hx0
  simp only [Function.iterate_zero, id_eq, zero_add] at hcomm
  rw [hcomm]
  have h1 := profileJetBound_of hD hJ T.p hsm a b ℓ x hx0
  calc (1 + x.2.1 ^ 2) ^ m *
        |(partialEta^[a] (partialQ^[b] (partialAge^[ℓ] (trainProfile T.p)))) x|
      ≤ (1 + x.2.1 ^ 2) ^ m * ‖ageJet ℓ (a + b) T.p x.2.2 (x.1, x.2.1)‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
          Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := h2
    _ ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) * 1 :=
        mul_le_mul_of_nonneg_left hE hP
    _ = polyConst C N ν (ν ^ (-ρ)) := by
        unfold UnforcedLeray.Short.PartI.polyP polyConst
        ring

end UnforcedLeray.Short.PartIIa
