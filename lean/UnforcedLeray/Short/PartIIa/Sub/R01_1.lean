import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIa.Sub.R02_3

/-!
# Part II-a, task `PartII-a:R01/1`: the zero-age stream profile (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 439-446
(`sct:fluctuation`), 447-459 (`sct:expansion`), read at ages `0 < s ≤ 1`, and 1294-1297 ("at zero
age the integrands are bounded").

Target: `EarlyStreamProfile` (`Sub/R01.lean`): every mixed jet `∂_s^ℓ ∂_η^a ∂_q^b ψ` of the stream
profile of an exact train, weighted by `(1+η²)^m`, is bounded by `C (1+c+ν⁻¹)^d` for `0 < s ≤ 1`.


of `trainProfile T.ψ` to the jets `ageJet` of `TrainFluctuationDecay` (the leaves `ProfileIterComm`,
`ProfileDict`, `SliceJetBound` of `Sub/R02_2.lean`, shared with `PartII-a:R02/2` and `R01/2`) and
the pointwise reading of `TrainMeanExpansion` (shared with `PartII-a:R02/3`: `SliceDerivContinuous`,
`EssSupPointwise` of `Sub/R02_3.lean`).

Route (all proved here except the two new leaves):

* `ψ = ψ̃ + S` with `ψ̃ r z = ψ r z - S(r, z.2)` and `S = meanStream`.  The profile of `ψ` is the sum
  of the profiles of `ψ̃` and of `S`, both `C^∞` for `s > 0`; the mixed jet is additive on such
  functions (`ProfileJetAdd`, new leaf);
* fluctuation (`earlyFluct_of_sub`): `ProfileIterComm` with `i = 0` moves `∂_s^ℓ` inside,
  `ProfileJetBound` bounds `∂_η^a ∂_q^b ∂_s^ℓ ψ̃` by the jet `‖ageJet ℓ (a+b) ψ̃ s (q, η)‖`, and the
  first component of `TrainFluctuationDecay` with weight `2m` bounds the latter by
  `polyP · e^{-κνs/c²} ≤ polyP` (`e^{-…} ≤ 1`);
* mean stream (`earlyMeanProfile_of`): `S` does not depend on `q`, so by `ProfileDict`
  `∂_s^ℓ ∂_η^a ∂_q^b S = 0` for `b ≥ 1` and `= ∂_η^a ∂_s^ℓ S(s, η)` for `b = 0`
  (`meanProfile_jet`); the last conjunct of `TrainMeanExpansion` at `p = ∞` and `N = 0` bounds
  `|η|^{m'} |∂_η^a ∂_s^ℓ S|` by `P (1+s)^{(m'-a-1)/2-ℓ} ≤ 2^{|…|} P` for `0 < s ≤ 1`
  (`meanStreamPointwise_of`, via continuity and `EssSupPointwise`), and the weight
  `(1+η²)^m ≤ 2^m (1 + |η|^{2m})` (`earlyMeanSlice_of`) finishes.

New leaves (each a Haiku-sized task, proofs in `Short/PartII-a/Tasks/R01/EarlyStreamProfile/`):
`ProfileJetAdd` (calculus: the mixed jet is additive on functions that are `C^∞` for `s > 0`) and
`MeanStreamSmooth` (`S` is `C^∞` on `(0,∞) × ℝ`; from `LateProfileSmooth` and `hmeanContDiff`).

The unconditional statement `earlyStreamProfile_of (hF) (hM) (hS) : EarlyStreamProfile` is the task
file `Short/PartII-a/Tasks/R01/EarlyStreamProfile.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream ageJet)

/-! ### Leaves -/

/-- **Additivity of the mixed jet** (calculus): for `f, g` that are `C^∞` on the open set
`{s > 0}`, at every point with `s > 0`,
`∂_s^ℓ ∂_η^a ∂_q^b (f + g) = ∂_s^ℓ ∂_η^a ∂_q^b f + ∂_s^ℓ ∂_η^a ∂_q^b g`.  (Each of `∂_q, ∂_η, ∂_s`
is additive on `C^∞` functions on an open set, `fderiv_add`, and preserves the class and equality on
the open set, by induction on the number of derivatives; the helper
`Tasks/R01/EarlyCalculus/Framework.lean` has `iter_add`, `jet_add` and `jet_eq` for exactly this.) -/
def ProfileJetAdd : Prop :=
  ∀ (ℓ a b : ℕ) (f g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ f {y : ProfilePoint | 0 < y.2.2} →
    ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2} → ∀ x : ProfilePoint, 0 < x.2.2 →
      (partialAge^[ℓ] (partialEta^[a] (partialQ^[b] (fun y => f y + g y)))) x =
        (partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f))) x +
          (partialAge^[ℓ] (partialEta^[a] (partialQ^[b] g))) x

/-- **Smoothness of the mean stream** (source lines 397-404): `S(s, η) = \bar ψ(s, η)` is `C^∞` on
`(0,∞) × ℝ`.  (`ψ` is jointly `C^∞` for `s > 0` by `LateProfileSmooth` composed with the coordinate
change `(s, (q, η)) ↦ (q, η, s)`; then `hmeanContDiff : HmeanContDiff`, `PartI/Sub/T01.lean`,
proved in `Short/PartI/Tasks/TrainMeanEquations/HmeanContDiff.lean`.) -/
def MeanStreamSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **The mean stream at `p = ∞`, read pointwise** (source lines 447-459, last display, `N = 0`): for
`0 < s` and every `η`, `|η|^{m'} |∂_η^{b'} ∂_s^{l'} S(s, η)| ≤ P (1+s)^{(m'-b'-1)/2-l'}`. -/
def MeanStreamPointwise : Prop :=
  ∀ (ρ : ℝ) (m' b' l' : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → ∀ η : ℝ,
        |η| ^ m' * |iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanStream tr r e) s) η| ≤
          polyConst C M ν (ν ^ (-ρ)) * (1 + s) ^ (((m' : ℝ) - b' - 1) / 2 - l')

/-! ### The mean stream, read pointwise (proved from `TrainMeanExpansion`) -/

theorem meanStreamPointwise_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hSm : MeanStreamSmooth) (hSC : SliceDerivContinuous) (hES : EssSupPointwise) :
    MeanStreamPointwise := by
  intro ρ m' b' l' hρ
  obtain ⟨C, M, ν₀, hC, hν₀, hbd⟩ := hM ρ hρ 0 m' b' l' ⊤ le_top
  refine ⟨C, M, ν₀, hC, hν₀, fun ν hν hνle tr hb s hs η => ?_⟩
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  obtain ⟨-, -, -, hR⟩ := hbd ν hν hνle tr hb
  have hR' := hR s hs.le
  simp only [ENNReal.toReal_top, inv_zero, zero_div, add_zero] at hR'
  have hD : Continuous (fun η : ℝ =>
      iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanStream tr r e) s) η) :=
    hSC (fun r e => meanStream tr r e) (hSm ν (ν ^ (-ρ)) hν hc tr hb) b' l' s hs
  have hfc : Continuous (fun η : ℝ =>
      η ^ m' * iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanStream tr r e) s) η) :=
    (continuous_pow m').mul hD
  have hbase : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.mpr hν
    linarith
  have hB0 : 0 ≤ polyConst C M ν (ν ^ (-ρ)) * (1 + s) ^ (((m' : ℝ) - b' - 1) / 2 - l') := by
    unfold polyConst
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg hbase.le M))
      (Real.rpow_nonneg (by linarith) _)
  have hES' := hES _ hfc _ hB0 hR'
  calc |η| ^ m' * |iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanStream tr r e) s) η|
      = |η ^ m' * iteratedDeriv b' (fun e => iteratedDeriv l' (fun r => meanStream tr r e) s) η| := by
        rw [abs_mul, abs_pow]
    _ ≤ _ := hES' η

theorem rpow_one_add_le (e s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 + s) ^ e ≤ 2 ^ |e| := by
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he]
    exact Real.rpow_le_rpow (by linarith) (by linarith) he
  · calc (1 + s) ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he
      _ ≤ 2 ^ |e| := Real.one_le_rpow (by norm_num) (abs_nonneg e)

/-- The weighted slice bound for `0 < s ≤ 1`: `(1+η²)^m |∂_η^a ∂_s^ℓ S(s, η)| ≤ P`. -/
theorem earlyMeanSlice_of (hPt : MeanStreamPointwise) (ρ : ℝ) (m a ℓ : ℕ) (hρ : 1 / 2 < ρ) :
    ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ η : ℝ,
          (1 + η ^ 2) ^ m *
              |iteratedDeriv a (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| ≤
            polyConst C M ν (ν ^ (-ρ)) := by
  obtain ⟨CA, MA, νA, hCA, hνA, HA⟩ := hPt ρ 0 a ℓ hρ
  obtain ⟨CB, MB, νB, hCB, hνB, HB⟩ := hPt ρ (2 * m) a ℓ hρ
  refine ⟨2 ^ m * (CA * 2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| +
      CB * 2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ|), MA + MB, min νA νB, by positivity,
    lt_min hνA hνB, ?_⟩
  intro ν hν hνle tr hb s hs0 hs1 η
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
  have hA := HA ν hν (hνle.trans (min_le_left _ _)) tr hb s hs0 η
  have hB := HB ν hν (hνle.trans (min_le_right _ _)) tr hb s hs0 η
  have hsA := rpow_one_add_le ((((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ) s hs0.le hs1
  have hsB := rpow_one_add_le ((((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ) s hs0.le hs1
  have hbase : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.mpr hν
    linarith
  have hpA : 0 ≤ polyConst CA MA ν (ν ^ (-ρ)) := by
    unfold polyConst; exact mul_nonneg hCA.le (pow_nonneg hbase.le _)
  have hpB : 0 ≤ polyConst CB MB ν (ν ^ (-ρ)) := by
    unfold polyConst; exact mul_nonneg hCB.le (pow_nonneg hbase.le _)
  have hmA : polyConst CA MA ν (ν ^ (-ρ)) ≤ polyConst CA (MA + MB) ν (ν ^ (-ρ)) :=
    polyConst_mono hν hc le_rfl hCA.le (Nat.le_add_right _ _)
  have hmB : polyConst CB MB ν (ν ^ (-ρ)) ≤ polyConst CB (MA + MB) ν (ν ^ (-ρ)) :=
    polyConst_mono hν hc le_rfl hCB.le (Nat.le_add_left _ _)
  have hnA : 0 ≤ polyConst CA (MA + MB) ν (ν ^ (-ρ)) := hpA.trans hmA
  have hnB : 0 ≤ polyConst CB (MA + MB) ν (ν ^ (-ρ)) := hpB.trans hmB
  set d := |iteratedDeriv a (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) s) η| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have t1 : |η| ^ 0 * d ≤ polyConst CA (MA + MB) ν (ν ^ (-ρ)) *
      2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| :=
    hA.trans (mul_le_mul hmA hsA (Real.rpow_nonneg (by linarith) _) hnA)
  have t2 : |η| ^ (2 * m) * d ≤ polyConst CB (MA + MB) ν (ν ^ (-ρ)) *
      2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ| :=
    hB.trans (mul_le_mul hmB hsB (Real.rpow_nonneg (by linarith) _) hnB)
  have hpow := pow_one_add_le m (sq_nonneg η)
  have hη : (η ^ 2) ^ m = |η| ^ (2 * m) := by rw [pow_mul, sq_abs]
  rw [hη] at hpow
  have key : polyConst CA (MA + MB) ν (ν ^ (-ρ)) * 2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| +
      polyConst CB (MA + MB) ν (ν ^ (-ρ)) * 2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ| =
      polyConst (CA * 2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| +
        CB * 2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ|) (MA + MB) ν (ν ^ (-ρ)) := by
    unfold polyConst; ring
  have key2 : polyConst (2 ^ m * (CA * 2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| +
        CB * 2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ|)) (MA + MB) ν (ν ^ (-ρ)) =
      2 ^ m * polyConst (CA * 2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| +
        CB * 2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ|) (MA + MB) ν (ν ^ (-ρ)) := by
    unfold polyConst; ring
  rw [key2, ← key]
  calc (1 + η ^ 2) ^ m * d ≤ (2 ^ m * (1 + |η| ^ (2 * m))) * d :=
        mul_le_mul_of_nonneg_right hpow hd0
    _ = 2 ^ m * (|η| ^ 0 * d + |η| ^ (2 * m) * d) := by ring
    _ ≤ 2 ^ m * (polyConst CA (MA + MB) ν (ν ^ (-ρ)) *
          2 ^ |(((0 : ℕ) : ℝ) - a - 1) / 2 - ℓ| +
        polyConst CB (MA + MB) ν (ν ^ (-ρ)) * 2 ^ |(((2 * m : ℕ) : ℝ) - a - 1) / 2 - ℓ|) :=
        mul_le_mul_of_nonneg_left (add_le_add t1 t2) (by positivity)

/-! ### The jets of the mean-stream profile -/

/-- The jets of the profile of the mean stream: `∂_q` kills it, and for `b = 0` the jet is the
nested slice derivative `∂_η^a ∂_s^ℓ S(s, η)`. -/
theorem meanProfile_jet (hC : ProfileIterComm) (hD : ProfileDict) (hMS : MeanStreamSmooth)
    {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) (a b ℓ : ℕ)
    (x : ProfilePoint) (hx : 0 < x.2.2) :
    (partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
        (trainProfile fun s z => meanStream tr s z.2)))) x =
      if b = 0 then
        iteratedDeriv a (fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) x.2.2) x.2.1
      else 0 := by
  have hsm : ContDiffOn ℝ ∞ (trainProfile fun s z => meanStream tr s z.2)
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_trainProfile_of_eta (G := fun s η => meanStream tr s η) (hMS ν c hν hc tr hbuc)
  have hcomm := hC _ hsm 0 a b ℓ x hx
  simp only [Function.iterate_zero, id_eq, zero_add] at hcomm
  rw [hcomm, hD (fun s z => meanStream tr s z.2) hsm a b ℓ x hx]
  have hconst : ∀ e : ℝ, iteratedDeriv b (fun q' : ℝ => iteratedDeriv ℓ
      (fun r => meanStream tr r e) x.2.2) x.1 =
      if b = 0 then iteratedDeriv ℓ (fun r => meanStream tr r e) x.2.2 else 0 := by
    intro e
    exact iteratedDeriv_const
  by_cases hb : b = 0
  · simp only [hb, ite_true] at hconst ⊢
    have : (fun e => iteratedDeriv 0 (fun q' : ℝ => iteratedDeriv ℓ
        (fun r => meanStream tr r e) x.2.2) x.1) =
        fun e => iteratedDeriv ℓ (fun r => meanStream tr r e) x.2.2 := by
      funext e
      exact hconst e
    simp only [this]
  · simp only [hb, ite_false] at hconst ⊢
    have : (fun e => iteratedDeriv b (fun q' : ℝ => iteratedDeriv ℓ
        (fun r => meanStream tr r e) x.2.2) x.1) = fun _ => (0 : ℝ) := by
      funext e
      simpa [hb] using hconst e
    simp only [this]
    exact iteratedDeriv_fun_const_zero

/-- The mean-stream part of the zero-age bound. -/
theorem earlyMeanProfile_of (hC : ProfileIterComm) (hD : ProfileDict) (hMS : MeanStreamSmooth)
    (hPt : MeanStreamPointwise) (ρ : ℝ) (m a b ℓ : ℕ) (hρ : 1 / 2 < ρ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν ∈ Ioo 0 ν₀, ∀ T : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain T → ∀ x : ProfilePoint,
        0 < x.2.2 → x.2.2 ≤ 1 →
          (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => meanStream T s z.2)))) x| ≤ polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨C, M, ν₀, hC0, hν₀, H⟩ := earlyMeanSlice_of hPt ρ m a ℓ hρ
  refine ⟨ν₀, C, M, hν₀, hC0.le, ?_⟩
  intro ν hν T hT x hx0 hx1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν.1 _
  rw [meanProfile_jet hC hD hMS hν.1 hc T hT a b ℓ x hx0]
  by_cases hb : b = 0
  · simp only [hb, ite_true]
    exact H ν hν.1 hν.2.le T hT x.2.2 hx0 hx1 x.2.1
  · simp only [hb, ite_false, abs_zero, mul_zero]
    unfold polyConst
    have hbase : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
      have : 0 < ν⁻¹ := inv_pos.mpr hν.1
      linarith
    exact mul_nonneg hC0.le (pow_nonneg hbase.le _)

/-! ### The fluctuation part -/

theorem fluctProfileSmoothEarly_of (hS : LateProfileSmooth) (hMS : MeanStreamSmooth) :
    FluctProfileSmooth := by
  intro ν c hν hc tr hbuc
  have h1 := (hS ν c hν hc tr hbuc).1
  have h2 : ContDiffOn ℝ ∞ (trainProfile fun s z => meanStream tr s z.2)
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_trainProfile_of_eta (G := fun s η => meanStream tr s η) (hMS ν c hν hc tr hbuc)
  exact h1.sub h2

/-- The fluctuation part of the zero-age bound. -/
theorem earlyFluct_of_sub (hC : ProfileIterComm) (hD : ProfileDict) (hJ : SliceJetBound)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) (hFS : FluctProfileSmooth)
    (ρ : ℝ) (m a b ℓ : ℕ) (hρ : 1 / 2 < ρ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν ∈ Ioo 0 ν₀, ∀ T : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain T → ∀ x : ProfilePoint,
        0 < x.2.2 → x.2.2 ≤ 1 →
          (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => T.ψ s z - meanStream T s z.2)))) x| ≤
            polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨C, N, κ, ν₀, hC0, hκ, hν₀, H⟩ := hF ρ hρ (2 * m) ℓ (a + b)
  refine ⟨ν₀, C, N, hν₀, hC0.le, ?_⟩
  intro ν hν T hT x hx0 hx1
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hsm := hFS ν (ν ^ (-ρ)) hν0 hc T hT
  have Hs := H ν hν0 hν.2.le T hT x.2.2 hx0
  obtain ⟨⟨_, hψ⟩, _, _⟩ := Hs
  have hpos : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
    have : 0 < ν⁻¹ := inv_pos.2 hν0
    linarith
  have hP : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) := by
    unfold UnforcedLeray.Short.PartI.polyP
    have := hC0.le
    positivity
  have hE : Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2 := by positivity
    linarith
  have hB : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
      Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) :=
    mul_nonneg hP (Real.exp_pos _).le
  have h2 := pointwise_of_wSupNorm hB hψ (x.1, x.2.1)
  rw [sqrt_jap_even] at h2
  have hcomm := hC (trainProfile fun s z => T.ψ s z - meanStream T s z.2) hsm 0 a b ℓ x hx0
  simp only [Function.iterate_zero, id_eq, zero_add] at hcomm
  rw [hcomm]
  have h1 := profileJetBound_of hD hJ (fun s z => T.ψ s z - meanStream T s z.2) hsm a b ℓ x hx0
  calc (1 + x.2.1 ^ 2) ^ m *
        |(partialEta^[a] (partialQ^[b] (partialAge^[ℓ]
          (trainProfile fun s z => T.ψ s z - meanStream T s z.2)))) x|
      ≤ (1 + x.2.1 ^ 2) ^ m * ‖ageJet ℓ (a + b) (fun s z => T.ψ s z - meanStream T s z.2)
          x.2.2 (x.1, x.2.1)‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) *
          Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := h2
    _ ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ (-ρ)) * 1 :=
        mul_le_mul_of_nonneg_left hE hP
    _ = polyConst C N ν (ν ^ (-ρ)) := by
        unfold UnforcedLeray.Short.PartI.polyP polyConst
        ring

/-! ### The conditional theorem -/

/-- **`PartII-a:R01/1`, conditional** (`EarlyStreamProfile`): the zero-age stream profile bounds
follow from `TrainFluctuationDecay`, `TrainMeanExpansion`, the profile smoothness
(`LateProfileSmooth`, `MeanStreamSmooth`), the profile calculus leaves `ProfileIterComm`,
`ProfileDict`, `SliceJetBound` (shared with `R02/2`), `ProfileJetAdd`, and the pointwise-reading
leaves `SliceDerivContinuous`, `EssSupPointwise` (shared with `R02/3`). -/
theorem earlyStreamProfile_of_sub (hC : ProfileIterComm) (hD : ProfileDict) (hJ : SliceJetBound)
    (hAdd : ProfileJetAdd) (hMS : MeanStreamSmooth) (hSC : SliceDerivContinuous)
    (hES : EssSupPointwise) (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) (hS : LateProfileSmooth) :
    EarlyStreamProfile := by
  intro ρ m a b ℓ hρ
  have hFS : FluctProfileSmooth := fluctProfileSmoothEarly_of hS hMS
  have hPt : MeanStreamPointwise := meanStreamPointwise_of hM hMS hSC hES
  obtain ⟨ν₁, C₁, d₁, hν₁, hC₁, H₁⟩ := earlyFluct_of_sub hC hD hJ hF hFS ρ m a b ℓ hρ
  obtain ⟨ν₂, C₂, d₂, hν₂, hC₂, H₂⟩ := earlyMeanProfile_of hC hD hMS hPt ρ m a b ℓ hρ
  refine ⟨min ν₁ ν₂, C₁ + C₂, max d₁ d₂, lt_min hν₁ hν₂, ?_⟩
  intro ν hν ψ p hψ x hx0 hx1
  obtain ⟨T, hT, rfl, rfl⟩ := hψ
  have hν0 : 0 < ν := hν.1
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have m1 : ν ∈ Ioo 0 ν₁ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_left _ _)⟩
  have m2 : ν ∈ Ioo 0 ν₂ := ⟨hν0, lt_of_lt_of_le hν.2 (min_le_right _ _)⟩
  have hFl := hFS ν (ν ^ (-ρ)) hν0 hc T hT
  have hSm : ContDiffOn ℝ ∞ (trainProfile fun s z => meanStream T s z.2)
      {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_trainProfile_of_eta (G := fun s η => meanStream T s η) (hMS ν (ν ^ (-ρ)) hν0 hc T hT)
  have hsplit : trainProfile T.ψ =
      fun y => trainProfile (fun s z => T.ψ s z - meanStream T s z.2) y +
        trainProfile (fun s z => meanStream T s z.2) y := by
    funext y
    simp [trainProfile]
  rw [hsplit, hAdd ℓ a b _ _ hFl hSm x hx0]
  have e1 := H₁ ν m1 T hT x hx0 hx1
  have e2 := H₂ ν m2 T hT x hx0 hx1
  have hm1 : polyConst C₁ d₁ ν (ν ^ (-ρ)) ≤ polyConst (C₁ + C₂) (max d₁ d₂) ν (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (by linarith) (by linarith) (le_max_left _ _)
  have hm2 : polyConst C₂ d₂ ν (ν ^ (-ρ)) ≤ polyConst (C₁ + C₂) (max d₁ d₂) ν (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc (by linarith) (by linarith) (le_max_right _ _)
  have hsum : polyConst C₁ d₁ ν (ν ^ (-ρ)) + polyConst C₂ d₂ ν (ν ^ (-ρ)) ≤
      polyConst (C₁ + C₂) (max d₁ d₂) ν (ν ^ (-ρ)) := by
    have hb : 0 < 1 + ν ^ (-ρ) + ν⁻¹ := by
      have : 0 < ν⁻¹ := inv_pos.2 hν0
      linarith
    have h1 : polyConst C₁ d₁ ν (ν ^ (-ρ)) ≤ polyConst C₁ (max d₁ d₂) ν (ν ^ (-ρ)) :=
      polyConst_mono hν0 hc le_rfl hC₁ (le_max_left _ _)
    have h2 : polyConst C₂ d₂ ν (ν ^ (-ρ)) ≤ polyConst C₂ (max d₁ d₂) ν (ν ^ (-ρ)) :=
      polyConst_mono hν0 hc le_rfl hC₂ (le_max_right _ _)
    have h3 : polyConst C₁ (max d₁ d₂) ν (ν ^ (-ρ)) + polyConst C₂ (max d₁ d₂) ν (ν ^ (-ρ)) =
        polyConst (C₁ + C₂) (max d₁ d₂) ν (ν ^ (-ρ)) := by
      unfold polyConst; ring
    linarith
  calc (1 + x.2.1 ^ 2) ^ m *
        |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => T.ψ s z - meanStream T s z.2)))) x +
          (partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => meanStream T s z.2)))) x|
      ≤ (1 + x.2.1 ^ 2) ^ m * (|(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => T.ψ s z - meanStream T s z.2)))) x| +
          |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => meanStream T s z.2)))) x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ = (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => T.ψ s z - meanStream T s z.2)))) x| +
          (1 + x.2.1 ^ 2) ^ m * |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b]
            (trainProfile fun s z => meanStream T s z.2)))) x| := by ring
    _ ≤ polyConst (C₁ + C₂) (max d₁ d₂) ν (ν ^ (-ρ)) := by linarith

end UnforcedLeray.Short.PartIIa
