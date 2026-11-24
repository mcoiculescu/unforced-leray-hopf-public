import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Sub.R02_2
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.ExpPowAbsorb
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.KExpansion

/-!
# Part II-a, block `B₁` of the late residual table: mean cancellation and assembly

Organizer file of `PartII-a:R02/9/org`.  Target of the block: `RingLateB1`
(`Short/PartII-a/Sub/R02.lean`), i.e. for `B₁ = -νK(K+2)v₁` (`B0188.coeffB₁`, source line 1255)
the late sizes `s^{-2}` (`B₁`), `s^{-5/2}` (`∂_ηB₁`), `s^{-2}` (`(K+3)B₁`) with the normalized
weight `⟨η/√s⟩^{2m}`, and `∂_qB₁` exponentially small (source lines 1259-1276, rows `A₁, B₁`).

Source of record: `the November 2 reference manuscript`, lines 1243-1276 (the
coefficients and the late table, "The heat identity `K∂_η^jG_{νs} = -(j+1)∂_η^jG_{νs}` and Lemma
`sct:heat` give the following complete late residual table"), lines 397-404 (`sct:mean`: the mean
stream `S = \bar ψ`, `\bar v₁ = -S_η`) and lines 437-481 (Lemma `sct:heat`: `sct:fluctuation`
439-446, `sct:expansion` 447-459).

## The mathematics (why the table entry holds)

Write `ψ = S + ψ̃` (`S = meanP`, `q`-independent; `ψ̃ = fluctP`, `sct:fluctuation`) and
`S = a₀G + a₂∂_η²G + R₁` (`sct:expansion` with `N = 1`, `G = G_{νs}` = `heatProfile ν`,
`R₁ = remP · 1`).  Since `B₁` is linear in `ψ`, on `{s > 0}`

* `B₁ = ν (K² + 2K)∂_ηψ`, `∂_ηB₁ = ν (K+1)(K+3)∂_η²ψ = ν (K² + 4K + 3)∂_η²ψ`
  (`[K, ∂_η] = -∂_η`), `(K+3)B₁ = ν (K³ + 5K² + 6K)∂_ηψ`, `∂_qB₁ = ν (K² + 2K)∂_η∂_qψ`
  (`[K, ∂_q] = 0`) — leaves `CoeffB1Eq`, `CoeffB1EtaEq`, `CoeffB1ShiftEq`, `CoeffB1QEq`;
* the heat identity `K∂_η^jG = -(j+1)∂_η^jG` (`HeatJetEigen`) turns a polynomial `p(K)` acting on
  `∂_η^jG` into the number `p(-(j+1))`.  **Mean cancellation** (source 1255-1257): the polynomials
  above vanish at `K = -2` (on `∂_ηG`) resp. `K = -3` (on `∂_η²G`): `(K+2)∂_ηG = 0`, `(K+3)∂_η²G = 0`.
  So the `a₀` part of the mean drops out; the `a₂` part is `8a₂∂_η³G`, `8a₂∂_η⁴G`, `-8a₂∂_η³G`
  of size `ν(νs)^{-2}`, `ν(νs)^{-5/2}` with the weight (`LateHeatProfile` (ii)), `|a₂| ≤ P`
  (`LateMeanCoeff`); the remainder part `p(K)∂_η^aR₁` is `O(s^{-(a+5)/2}) ⊂ O(s^{-3})`
  (`LateMeanRemainder`, `RemJetUnif`); the fluctuation part is exponentially small
  (`LateFluctuationProfile`, `FluctJetUnif`), hence `≤ P s^{-3}` (`expToPow`, from `ExpPowAbsorb`).
* `∂_qB₁` sees only `ψ̃` (`S` is `q`-independent), so it is exponentially small.

## Layout

* Leaves (`Prop`s, proved by separate tasks `PartII-a:R02/9/1`-`/9`): `CoeffB1Eq`, `CoeffB1EtaEq`,
  `CoeffB1ShiftEq`, `CoeffB1QEq`, `HeatJetEigen`, `JetLinear`, `TrainPartsSmooth`,
  `FluctJetUnif`, `RemJetUnif`.
* Proved here: `jet_congr`, `jet_zero`, `meanP_decomp`, `jet_split`, `jet_split_q`, `expToPow`,
  the generic weighted assembly `wtd_of_expand`, the `∂_q` assembly `q_of_expand`, and
  `ringLateB1_of_parts` (the block from the leaves and `LateIngredients`).

Everything is in the namespace `UnforcedLeray.Short.PartIIa.BlockB1`.  The block is linear in `ψ`,
so it needs no product (Leibniz) calculus and does not use `Calc/JetClass.lean`
(`PartII-a:R02/8/org`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.BlockB1

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream meanRemainder meanCoeff heatKernel1)

/-! ### Jets and the three parts of the stream -/

/-- The jet `K^ℓ ∂_η^a ∂_q^b g` (`K = ageOperator = η∂_η + 2s∂_s`), in the order of
`LateFluctuationProfile` and `LateMeanRemainder` (`K` outermost). -/
def jet (ℓ a b : ℕ) (g : ProfilePoint → ℝ) : ProfilePoint → ℝ :=
  ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] g))

/-- Profile of the mean stream `S(η, s) = \bar ψ` (source line 397, `sct:mean`). -/
def meanP {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) : ProfilePoint → ℝ :=
  trainProfile fun s z => meanStream tr s z.2

/-- Profile of the stream fluctuation `ψ̃ = ψ - S` (source lines 439-446). -/
def fluctP {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) : ProfilePoint → ℝ :=
  trainProfile fun s z => tr.ψ s z - meanStream tr s z.2

/-- Profile of the mean remainder `R_N = S - ∑_{j≤N} a_{2j}∂_η^{2j}G_{νs}` (source lines 447-449). -/
def remP {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (N : ℕ) : ProfilePoint → ℝ :=
  trainProfile fun s z => meanRemainder tr N s z.2

/-! ### Leaves -/

/-- **`B₁` as a polynomial in `K`** (source line 1255, `B₁ = -νK(K+2)v₁`, `v₁ = -∂_ηψ`): for `g`
smooth on `{s > 0}`, there `B₁[g] = ν(K²∂_ηg + 2K∂_ηg)`.  (Linearity of `K` at points where the
argument is differentiable: `B0188.ageOperator_add_mul`, `kx_ageOp_const_mul`, `kx_ageOp_congr`.) -/
def CoeffB1Eq : Prop :=
  ∀ (ν : ℝ) (g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2} →
    ∀ x : ProfilePoint, 0 < x.2.2 →
      coeffB₁ ν g x = ν * (2 * jet 1 1 0 g x + jet 2 1 0 g x)

/-- **`∂_ηB₁`** (source lines 1255, 1268-1270: "an `η` derivative gains `s^{-1/2}`"): with
`∂_ηK = (K+1)∂_η` (`[K, ∂_η] = -∂_η`, `ProfileCommutators`),
`∂_ηB₁[g] = ν(K+1)(K+3)∂_η²g = ν(3∂_η²g + 4K∂_η²g + K²∂_η²g)` on `{s > 0}`. -/
def CoeffB1EtaEq : Prop :=
  ∀ (ν : ℝ) (g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2} →
    ∀ x : ProfilePoint, 0 < x.2.2 →
      partialEta (coeffB₁ ν g) x = ν * (3 * jet 0 2 0 g x + 4 * jet 1 2 0 g x + jet 2 2 0 g x)

/-- **`(K+3)B₁`** (source line 1272, column "`(K+3)` size"): `(K+3)B₁[g] = ν(K+3)K(K+2)∂_ηg =
ν(6K∂_ηg + 5K²∂_ηg + K³∂_ηg)` on `{s > 0}`. -/
def CoeffB1ShiftEq : Prop :=
  ∀ (ν : ℝ) (g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2} →
    ∀ x : ProfilePoint, 0 < x.2.2 →
      ageShift 3 (coeffB₁ ν g) x = ν * (6 * jet 1 1 0 g x + 5 * jet 2 1 0 g x + jet 3 1 0 g x)

/-- **`∂_qB₁`** (source line 1276 context: `∂_q` derivatives see only the fluctuation): with
`[K, ∂_q] = 0` and `∂_q∂_η = ∂_η∂_q`, `∂_qB₁[g] = ν(2K∂_η∂_qg + K²∂_η∂_qg)` on `{s > 0}`. -/
def CoeffB1QEq : Prop :=
  ∀ (ν : ℝ) (g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2} →
    ∀ x : ProfilePoint, 0 < x.2.2 →
      partialQ (coeffB₁ ν g) x = ν * (2 * jet 1 1 1 g x + jet 2 1 1 g x)

/-- **Heat identity, iterated** (source line 1255: `K∂_η^jG_{νs} = -(j+1)∂_η^jG_{νs}`):
`K^ℓ∂_η^jG = (-(j+1))^ℓ ∂_η^jG` on `{s > 0}` (from `LateHeatProfile` (i) by induction on `ℓ`). -/
def HeatJetEigen : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ (ℓ j : ℕ) (x : ProfilePoint), 0 < x.2.2 →
    jet ℓ j 0 (heatProfile ν) x = (-((j : ℝ) + 1)) ^ ℓ * (partialEta^[j] (heatProfile ν)) x

/-- **Jets are linear on smooth profiles** (calculus): for `g₁, g₂` smooth on `{s > 0}`,
`K^ℓ∂_η^a∂_q^b(αg₁ + βg₂) = αK^ℓ∂_η^a∂_q^bg₁ + βK^ℓ∂_η^a∂_q^bg₂` on `{s > 0}`. -/
def JetLinear : Prop :=
  ∀ g₁ g₂ : ProfilePoint → ℝ, ContDiffOn ℝ ∞ g₁ {y : ProfilePoint | 0 < y.2.2} →
    ContDiffOn ℝ ∞ g₂ {y : ProfilePoint | 0 < y.2.2} →
    ∀ (α β : ℝ) (ℓ a b : ℕ) (x : ProfilePoint), 0 < x.2.2 →
      jet ℓ a b (fun y => α * g₁ y + β * g₂ y) x = α * jet ℓ a b g₁ x + β * jet ℓ a b g₂ x

/-- **Smoothness of the parts** (source lines 397-404, 447-449): for a BUC train, the mean `S`, the
fluctuation `ψ̃`, the remainder `R₁` and the heat profile `G_{νs}` are `C^∞` on `{s > 0}`
(from `LateProfileSmooth`, `hmeanContDiff`, `fluctProfileSmooth_of`, `heatKernelIterSmooth`). -/
def TrainPartsSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
    UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ContDiffOn ℝ ∞ (meanP tr) {y : ProfilePoint | 0 < y.2.2} ∧
      ContDiffOn ℝ ∞ (fluctP tr) {y : ProfilePoint | 0 < y.2.2} ∧
      ContDiffOn ℝ ∞ (remP tr 1) {y : ProfilePoint | 0 < y.2.2} ∧
      ContDiffOn ℝ ∞ (heatProfile ν) {y : ProfilePoint | 0 < y.2.2}

/-- **Uniform fluctuation jets** (`sct:fluctuation`, source lines 439-446): one set of constants
for all `K^ℓ∂_η^a∂_q^bψ̃` with `ℓ ≤ 3`, `a ≤ 2`, `b ≤ 1` (finitely many instances of
`LateFluctuationProfile`, merged). -/
def FluctJetUnif : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ (ℓ a b : ℕ), ℓ ≤ 3 → a ≤ 2 → b ≤ 1 → ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        (1 + x.2.1 ^ 2 / x.2.2) ^ m * |jet ℓ a b (fluctP tr) x| ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))

/-- **Uniform remainder jets** (`sct:expansion` with `N = 1`, source lines 447-459): for `ℓ ≤ 3`,
`1 ≤ a ≤ 2`, `(1+η²/s)^m |K^ℓ∂_η^aR₁| ≤ P s^{-3}` for `s ≥ 1` (the source exponent is
`-(a+5)/2 ≤ -3`; finitely many instances of `LateMeanRemainder`, merged). -/
def RemJetUnif : Prop :=
  ∀ (ρ : ℝ) (m : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (M : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ (ℓ a : ℕ), ℓ ≤ 3 → 1 ≤ a → a ≤ 2 → ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        (1 + x.2.1 ^ 2 / x.2.2) ^ m * |jet ℓ a 0 (remP tr 1) x| ≤
          polyConst C M ν (ν ^ (-ρ)) * x.2.2 ^ (-3 : ℝ)

/-! ### Smoothness helpers (for the leaves) -/

theorem contDiffOn_ageOperator {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) :
    ContDiffOn ℝ ∞ (ageOperator F) {y : ProfilePoint | 0 < y.2.2} := by
  have h1 := contDiffOn_fderiv_apply hF eηDir
  have h2 := contDiffOn_fderiv_apply hF esDir
  have he : ContDiff ℝ ∞ (fun y : ProfilePoint => y.2.1) := by fun_prop
  have hs : ContDiff ℝ ∞ (fun y : ProfilePoint => y.2.2) := by fun_prop
  exact (he.contDiffOn.mul h1).add ((contDiffOn_const.mul hs.contDiffOn).mul h2)

/-- Jets of a profile smooth on `{s > 0}` are smooth there. -/
theorem contDiffOn_jet {g : ProfilePoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2}) (ℓ a b : ℕ) :
    ContDiffOn ℝ ∞ (jet ℓ a b g) {y : ProfilePoint | 0 < y.2.2} :=
  contDiffOn_iterate ageOperator (fun _ h => contDiffOn_ageOperator h)
    (contDiffOn_partialEta_iter (contDiffOn_partialQ_iter hg b) a) ℓ

theorem differentiableAt_of_late {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    DifferentiableAt ℝ F x :=
  (hF.contDiffAt (isOpen_late.mem_nhds hx)).differentiableAt (by simp)

theorem contDiffAt_two_of_late {F : ProfilePoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    ContDiffAt ℝ 2 F x :=
  (hF.contDiffAt (isOpen_late.mem_nhds hx)).of_le (by norm_num)

theorem eventuallyEq_of_late {F G : ProfilePoint → ℝ}
    (h : EqOn F G {y : ProfilePoint | 0 < y.2.2}) {x : ProfilePoint} (hx : 0 < x.2.2) :
    F =ᶠ[𝓝 x] G :=
  Filter.eventually_of_mem (isOpen_late.mem_nhds hx) (fun z hz => h hz)

/-! ### Jet calculus proved here -/

theorem iterLifts_ageOperator : IterComm.iterLifts ageOperator := by
  intro F F' h y hy
  have hev : F =ᶠ[𝓝 y] F' :=
    Filter.eventually_of_mem (isOpen_late.mem_nhds hy) (fun z hz => h hz)
  exact kx_ageOp_congr hev

/-- Jets only see the profile on `{s > 0}`. -/
theorem jet_congr {g₁ g₂ : ProfilePoint → ℝ} (h : EqOn g₁ g₂ {y : ProfilePoint | 0 < y.2.2})
    (ℓ a b : ℕ) : EqOn (jet ℓ a b g₁) (jet ℓ a b g₂) {y : ProfilePoint | 0 < y.2.2} :=
  IterComm.iterLifts_iter iterLifts_ageOperator ℓ
    (IterComm.iterLifts_iter IterComm.iterLifts_eta a
      (IterComm.iterLifts_iter IterComm.iterLifts_q b h))

theorem jet_zero (ℓ a b : ℕ) : jet ℓ a b (fun _ => (0 : ℝ)) = fun _ => 0 := by
  have hq : ∀ n : ℕ, partialQ^[n] (fun _ : ProfilePoint => (0 : ℝ)) = fun _ => 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext y
      simp [partialQ]
  have he : ∀ n : ℕ, partialEta^[n] (fun _ : ProfilePoint => (0 : ℝ)) = fun _ => 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext y
      simp [partialEta]
  have hk : ∀ n : ℕ, ageOperator^[n] (fun _ : ProfilePoint => (0 : ℝ)) = fun _ => 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext y
      simp [ageOperator, partialEta, partialAge]
  unfold jet
  rw [hq, he, hk]

theorem wt_nonneg (m : ℕ) {x : ProfilePoint} (hs : 0 < x.2.2) :
    0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m := by
  have h := div_nonneg (sq_nonneg x.2.1) hs.le
  exact pow_nonneg (by linarith) m

/-- `S = a₀G + a₂∂_η²G + R₁` on `{s > 0}` (definition of `meanRemainder`, source 448-449, with the
profile/one-variable identification `LateHeatProfile` (iii)). -/
theorem meanP_decomp (hH : LateHeatProfile) {ν c : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) (hx : 0 < x.2.2) :
    meanP tr x = meanCoeff tr 0 * heatProfile ν x +
      meanCoeff tr 1 * (partialEta^[2] (heatProfile ν)) x + remP tr 1 x := by
  rw [hH.2.2 ν hν 2 x hx]
  simp only [meanP, remP, trainProfile, meanRemainder, heatProfile]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [mul_zero, mul_one, iteratedDeriv_zero]
  ring

/-- `∂_q` of a profile that does not depend on `q` vanishes. -/
theorem partialQ_eq_zero_of_snd {g : ProfilePoint → ℝ} (hg : ∀ y : ProfilePoint, g y = g (0, y.2))
    {y : ProfilePoint} (hd : DifferentiableAt ℝ g y) : partialQ g y = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • eqDir) eqDir 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const eqDir).const_add y
  have h1 : HasDerivAt (fun t : ℝ => g (y + t • eqDir)) (fderiv ℝ g y eqDir) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have h2 : (fun t : ℝ => g (y + t • eqDir)) = fun _ => g y := by
    funext t
    rw [hg (y + t • eqDir), hg y]
    simp [eqDir, Prod.mk_zero_zero]
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const 0 (g y))

/-- **Jet split of the stream** on `{s > 0}`: `K^ℓ∂_η^aψ = a₀K^ℓ∂_η^aG + a₂K^ℓ∂_η^{a+2}G
+ K^ℓ∂_η^aR₁ + K^ℓ∂_η^aψ̃`. -/
theorem jet_split (hL : JetLinear) (hP : TrainPartsSmooth) (hH : LateHeatProfile)
    {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) (ℓ a : ℕ) (x : ProfilePoint)
    (hx : 0 < x.2.2) :
    jet ℓ a 0 (trainProfile tr.ψ) x =
      meanCoeff tr 0 * jet ℓ a 0 (heatProfile ν) x +
        meanCoeff tr 1 * jet ℓ (a + 2) 0 (heatProfile ν) x +
        jet ℓ a 0 (remP tr 1) x + jet ℓ a 0 (fluctP tr) x := by
  obtain ⟨hS, hf, hR, hG⟩ := hP ν c hν hc tr hb
  have hG2 : ContDiffOn ℝ ∞ (partialEta^[2] (heatProfile ν)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_partialEta_iter hG 2
  have hψ : trainProfile tr.ψ = fun y => 1 * meanP tr y + 1 * fluctP tr y := by
    funext y
    simp only [meanP, fluctP, trainProfile]
    ring
  have hin : ContDiffOn ℝ ∞ (fun y => meanCoeff tr 1 * (partialEta^[2] (heatProfile ν)) y +
      1 * remP tr 1 y) {y : ProfilePoint | 0 < y.2.2} :=
    (contDiffOn_const.mul hG2).add (contDiffOn_const.mul hR)
  have hSe : EqOn (meanP tr) (fun y => meanCoeff tr 0 * heatProfile ν y +
      1 * (meanCoeff tr 1 * (partialEta^[2] (heatProfile ν)) y + 1 * remP tr 1 y))
      {y : ProfilePoint | 0 < y.2.2} := by
    intro y hy
    simp only
    rw [meanP_decomp hH hν tr y hy]
    ring
  have h2 : jet ℓ a 0 (partialEta^[2] (heatProfile ν)) = jet ℓ (a + 2) 0 (heatProfile ν) := by
    simp only [jet, Function.iterate_zero, id_eq, Function.iterate_add_apply]
  rw [hψ, hL _ _ hS hf 1 1 ℓ a 0 x hx, jet_congr hSe ℓ a 0 hx, hL _ _ hG hin _ 1 ℓ a 0 x hx,
    hL _ _ hG2 hR _ 1 ℓ a 0 x hx, h2]
  ring

/-- **`∂_q` jets of the stream see only the fluctuation** on `{s > 0}`. -/
theorem jet_split_q (hL : JetLinear) (hP : TrainPartsSmooth) {ν c : ℝ} (hν : 0 < ν)
    (hc : 0 < c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) (ℓ a : ℕ) (x : ProfilePoint)
    (hx : 0 < x.2.2) :
    jet ℓ a 1 (trainProfile tr.ψ) x = jet ℓ a 1 (fluctP tr) x := by
  obtain ⟨hS, hf, -, -⟩ := hP ν c hν hc tr hb
  have hψ : trainProfile tr.ψ = fun y => 1 * meanP tr y + 1 * fluctP tr y := by
    funext y
    simp only [meanP, fluctP, trainProfile]
    ring
  have hq : EqOn (partialQ (meanP tr)) (fun _ => (0 : ℝ)) {y : ProfilePoint | 0 < y.2.2} := by
    intro y hy
    have hd : DifferentiableAt ℝ (meanP tr) y :=
      (hS.contDiffAt (isOpen_late.mem_nhds hy)).differentiableAt (by simp)
    exact partialQ_eq_zero_of_snd (fun z => rfl) hd
  have h0 : jet ℓ a 1 (meanP tr) x = 0 := by
    have h1 := jet_congr hq ℓ a 0 hx
    rw [jet_zero] at h1
    exact h1
  rw [hψ, hL _ _ hS hf 1 1 ℓ a 1 x hx, h0]
  ring

/-! ### Elementary estimates -/

/-- `e^{-κνs/c²} ≤ P s^{-3}` for `s ≥ 1` (from `ExpPowAbsorb` with `k = 3`). -/
theorem expToPow (κ : ℝ) (hκ : 0 < κ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ ν c s : ℝ, 0 < ν → 0 < c → 1 ≤ s →
      Real.exp (-(κ * ν * s / c ^ 2)) ≤ polyConst C N ν c * s ^ (-3 : ℝ) := by
  obtain ⟨C, N, hC, H⟩ := expPowAbsorb κ 3 hκ
  refine ⟨C, N, hC, fun ν c s hν hc hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have h1 := H ν c s hν hc hs0.le
  have hP : 0 ≤ polyConst C N ν c := by
    unfold polyConst
    have := inv_pos.2 hν
    exact mul_nonneg hC (pow_nonneg (by linarith) N)
  have hexp : Real.exp (-(κ / 2 * ν * s / c ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ κ / 2 * ν * s / c ^ 2 := by positivity
    linarith
  have h2 : s ^ 3 * Real.exp (-(κ * ν * s / c ^ 2)) ≤ polyConst C N ν c :=
    h1.trans (by simpa using mul_le_mul_of_nonneg_left hexp hP)
  have h3 : s ^ (-3 : ℝ) = (s ^ 3)⁻¹ := by
    rw [Real.rpow_neg hs0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [mul_comm (s ^ 3) (Real.exp (-(κ * ν * s / c ^ 2)))]

theorem pc_le {C : ℝ} {N D : ℕ} {ν c : ℝ} (hND : N ≤ D) (hν : 0 < ν) (hc : 0 < c) :
    polyConst C N ν c ≤ |C| * (1 + c + ν⁻¹) ^ D := by
  unfold polyConst
  have hY : 1 ≤ 1 + c + ν⁻¹ := by
    have := inv_pos.2 hν
    linarith
  calc C * (1 + c + ν⁻¹) ^ N ≤ |C| * (1 + c + ν⁻¹) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)
    _ ≤ |C| * (1 + c + ν⁻¹) ^ D :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY hND) (abs_nonneg C)

/-- `ν (νs)^{-r} ≤ (1+c+ν⁻¹)³ s^{-e}` for `ν ≤ 1 ≤ s`, `e ≤ r ≤ 3`. -/
theorem heat_term {ν c s r e : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) (hs : 1 ≤ s)
    (hr : r ≤ 3) (her : e ≤ r) :
    ν * (ν * s) ^ (-r) ≤ (1 + c + ν⁻¹) ^ 3 * s ^ (-e) := by
  have hs0 : 0 < s := by linarith
  rw [Real.mul_rpow hν.le hs0.le]
  have h1 : ν ^ (-r) ≤ ν ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
  have h2 : ν ^ (-3 : ℝ) = ν⁻¹ ^ 3 := by
    rw [Real.rpow_neg hν.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      inv_pow]
  have h3 : ν⁻¹ ^ 3 ≤ (1 + c + ν⁻¹) ^ 3 :=
    pow_le_pow_left₀ (inv_pos.2 hν).le (by linarith) 3
  have h4 : s ^ (-r) ≤ s ^ (-e) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have h5 : 0 ≤ ν ^ (-r) := Real.rpow_nonneg hν.le _
  have h6 : 0 ≤ s ^ (-r) := Real.rpow_nonneg hs0.le _
  calc ν * (ν ^ (-r) * s ^ (-r)) ≤ 1 * (ν ^ (-r) * s ^ (-r)) :=
        mul_le_mul_of_nonneg_right hν1 (mul_nonneg h5 h6)
    _ = ν ^ (-r) * s ^ (-r) := one_mul _
    _ ≤ (1 + c + ν⁻¹) ^ 3 * s ^ (-e) :=
        mul_le_mul ((h1.trans (le_of_eq h2)).trans h3) h4 h6 (by positivity)

theorem abs4 (w₀ w₁ w₂ w₃ r₀ r₁ r₂ r₃ t : ℝ) (ht : 0 ≤ t) :
    t * |w₀ * r₀ + w₁ * r₁ + w₂ * r₂ + w₃ * r₃| ≤
      |w₀| * (t * |r₀|) + |w₁| * (t * |r₁|) + |w₂| * (t * |r₂|) + |w₃| * (t * |r₃|) := by
  have h1 : |w₀ * r₀ + w₁ * r₁ + w₂ * r₂ + w₃ * r₃| ≤
      |w₀| * |r₀| + |w₁| * |r₁| + |w₂| * |r₂| + |w₃| * |r₃| := by
    calc |w₀ * r₀ + w₁ * r₁ + w₂ * r₂ + w₃ * r₃|
        ≤ |w₀ * r₀ + w₁ * r₁ + w₂ * r₂| + |w₃ * r₃| := abs_add_le _ _
      _ ≤ |w₀ * r₀ + w₁ * r₁| + |w₂ * r₂| + |w₃ * r₃| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ |w₀ * r₀| + |w₁ * r₁| + |w₂ * r₂| + |w₃ * r₃| := by
          gcongr
          exact abs_add_le _ _
      _ = |w₀| * |r₀| + |w₁| * |r₁| + |w₂| * |r₂| + |w₃| * |r₃| := by
          simp only [abs_mul]
  calc t * |w₀ * r₀ + w₁ * r₁ + w₂ * r₂ + w₃ * r₃|
      ≤ t * (|w₀| * |r₀| + |w₁| * |r₁| + |w₂| * |r₂| + |w₃| * |r₃|) :=
        mul_le_mul_of_nonneg_left h1 ht
    _ = _ := by ring

/-- Four nonnegative weighted terms, each bounded by `Q`. -/
theorem sum4_le {w₀ w₁ w₂ w₃ t₀ t₁ t₂ t₃ Q ν : ℝ} (_hν : 0 < ν) (hν1 : ν ≤ 1)
    (h₀ : 0 ≤ t₀) (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃)
    (b₀ : t₀ ≤ Q) (b₁ : t₁ ≤ Q) (b₂ : t₂ ≤ Q) (b₃ : t₃ ≤ Q) :
    ν * (|w₀| * t₀ + |w₁| * t₁ + |w₂| * t₂ + |w₃| * t₃) ≤
      (|w₀| + |w₁| + |w₂| + |w₃|) * Q := by
  have hS : 0 ≤ |w₀| * t₀ + |w₁| * t₁ + |w₂| * t₂ + |w₃| * t₃ := by positivity
  have hle : |w₀| * t₀ + |w₁| * t₁ + |w₂| * t₂ + |w₃| * t₃ ≤
      |w₀| * Q + |w₁| * Q + |w₂| * Q + |w₃| * Q := by
    have := mul_le_mul_of_nonneg_left b₀ (abs_nonneg w₀)
    have := mul_le_mul_of_nonneg_left b₁ (abs_nonneg w₁)
    have := mul_le_mul_of_nonneg_left b₂ (abs_nonneg w₂)
    have := mul_le_mul_of_nonneg_left b₃ (abs_nonneg w₃)
    linarith
  calc ν * (|w₀| * t₀ + |w₁| * t₁ + |w₂| * t₂ + |w₃| * t₃)
      ≤ 1 * (|w₀| * t₀ + |w₁| * t₁ + |w₂| * t₂ + |w₃| * t₃) :=
        mul_le_mul_of_nonneg_right hν1 hS
    _ ≤ (|w₀| + |w₁| + |w₂| + |w₃|) * Q := by linarith

/-! ### Assembly -/

/-- **Generic weighted block** (the mean cancellation of source 1255-1257): if `X ν g` is, on
`{s > 0}`, `ν` times a cubic polynomial `w₀ + w₁K + w₂K² + w₃K³` applied to `∂_η^ag` (`1 ≤ a ≤ 2`),
and the polynomial vanishes at `K = -(a+1)` (so it kills `∂_η^aG_{νs}`), then `X ν ψ` has the late
weighted size `s^{-e}` for every `e ≤ (a+3)/2`, uniformly over exact trains. -/
theorem wtd_of_expand (h : LateIngredients) (hHe : HeatJetEigen) (hL : JetLinear)
    (hP : TrainPartsSmooth) (hF : FluctJetUnif) (hR : RemJetUnif)
    (X : ℝ → (ProfilePoint → ℝ) → ProfilePoint → ℝ) (a : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (w₀ w₁ w₂ w₃ e : ℝ)
    (hw : w₀ + w₁ * (-((a : ℝ) + 1)) + w₂ * (-((a : ℝ) + 1)) ^ 2 +
      w₃ * (-((a : ℝ) + 1)) ^ 3 = 0)
    (he : e ≤ ((a : ℝ) + 3) / 2)
    (hX : ∀ (ν : ℝ) (g : ProfilePoint → ℝ), ContDiffOn ℝ ∞ g {y : ProfilePoint | 0 < y.2.2} →
      ∀ x : ProfilePoint, 0 < x.2.2 →
        X ν g x = ν * (w₀ * jet 0 a 0 g x + w₁ * jet 1 a 0 g x + w₂ * jet 2 a 0 g x +
          w₃ * jet 3 a 0 g x)) :
    LateStmt (fun ν _ _ B m ψ _ => WtdBound m (X ν ψ) e B) := by
  intro ρ m hρ
  obtain ⟨Ca, Na, νa, hνa, Ha⟩ := h.coeff ρ 1 hρ
  obtain ⟨Ch, hCh, Hh⟩ := h.heat.2.1 m (a + 2)
  obtain ⟨CR, NR, νR, hνR, HR⟩ := hR ρ m hρ
  obtain ⟨Cf, Nf, κf, νf, hκf, hνf, HF⟩ := hF ρ m hρ
  obtain ⟨Ce, Ne, hCe, He⟩ := expToPow κf hκf
  obtain ⟨Hw, hHw⟩ : ∃ Hw : ℝ, Hw = w₀ + w₁ * (-((a : ℝ) + 3)) + w₂ * (-((a : ℝ) + 3)) ^ 2 +
      w₃ * (-((a : ℝ) + 3)) ^ 3 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = |w₀| + |w₁| + |w₂| + |w₃| := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = Na + 3 + NR + Nf + Ne := ⟨_, rfl⟩
  refine ⟨min (min νa νR) (min νf 1), lt_min (lt_min hνa hνR) (lt_min hνf one_pos),
    |Hw| * |Ca| * Ch + W * |CR| + W * (|Cf| * Ce), D, 1, one_pos, ?_⟩
  intro ν hν ψ p hψ
  obtain ⟨T, hT, rfl, -⟩ := hψ
  have hν0 : 0 < ν := hν.1
  have hνa' : ν ≤ νa := hν.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνR' : ν ≤ νR := hν.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνf' : ν ≤ νf := hν.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : ν ≤ 1 := hν.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hψs : ContDiffOn ℝ ∞ (trainProfile T.ψ) {y : ProfilePoint | 0 < y.2.2} :=
    (h.smooth ν _ hν0 hc T hT).1
  have hY : 1 ≤ 1 + ν ^ (-ρ) + ν⁻¹ := by
    have := inv_pos.2 hν0
    linarith
  show ∀ x : ProfilePoint, 1 ≤ x.2.2 →
    (1 + x.2.1 ^ 2 / x.2.2) ^ m * |X ν (trainProfile T.ψ) x| ≤
      polyConst (|Hw| * |Ca| * Ch + W * |CR| + W * (|Cf| * Ce)) D ν (ν ^ (-ρ)) * x.2.2 ^ (-e)
  intro x hx
  have hs : 0 < x.2.2 := by linarith
  have hwt := wt_nonneg m hs
  -- the decomposition: the `a₀` part cancels
  have hdec : X ν (trainProfile T.ψ) x = ν * (meanCoeff T 1 * Hw *
      (partialEta^[a + 2] (heatProfile ν)) x +
      (w₀ * jet 0 a 0 (remP T 1) x + w₁ * jet 1 a 0 (remP T 1) x + w₂ * jet 2 a 0 (remP T 1) x +
        w₃ * jet 3 a 0 (remP T 1) x) +
      (w₀ * jet 0 a 0 (fluctP T) x + w₁ * jet 1 a 0 (fluctP T) x + w₂ * jet 2 a 0 (fluctP T) x +
        w₃ * jet 3 a 0 (fluctP T) x)) := by
    rw [hX ν _ hψs x hs, jet_split hL hP h.heat hν0 hc T hT 0 a x hs,
      jet_split hL hP h.heat hν0 hc T hT 1 a x hs, jet_split hL hP h.heat hν0 hc T hT 2 a x hs,
      jet_split hL hP h.heat hν0 hc T hT 3 a x hs, hHe ν hν0 0 a x hs, hHe ν hν0 1 a x hs,
      hHe ν hν0 2 a x hs, hHe ν hν0 3 a x hs, hHe ν hν0 0 (a + 2) x hs,
      hHe ν hν0 1 (a + 2) x hs, hHe ν hν0 2 (a + 2) x hs, hHe ν hν0 3 (a + 2) x hs, hHw]
    push_cast
    linear_combination (ν * meanCoeff T 0 * (partialEta^[a] (heatProfile ν)) x) * hw
  -- abbreviations
  set Y : ℝ := 1 + ν ^ (-ρ) + ν⁻¹ with hYdef
  set wt : ℝ := (1 + x.2.1 ^ 2 / x.2.2) ^ m with hwtdef
  have hZ : 0 ≤ Y ^ D * x.2.2 ^ (-e) :=
    mul_nonneg (pow_nonneg (by linarith) D) (Real.rpow_nonneg hs.le _)
  have hs3e : x.2.2 ^ (-3 : ℝ) ≤ x.2.2 ^ (-e) :=
    Real.rpow_le_rpow_of_exponent_le hx (by
      have : ((a : ℝ)) ≤ 2 := by exact_mod_cast ha2
      linarith)
  -- the heat term
  have hT1 : ν * (|meanCoeff T 1| * |Hw| * (wt * |(partialEta^[a + 2] (heatProfile ν)) x|)) ≤
      |Hw| * |Ca| * Ch * (Y ^ D * x.2.2 ^ (-e)) := by
    have hg := Hh ν hν0 hν1 x hx
    have ha' : |meanCoeff T 1| ≤ |Ca| * Y ^ Na :=
      (Ha ν hν0 hνa' T hT).trans (pc_le le_rfl hν0 hc)
    have hr3 : (((a + 2 : ℕ) : ℝ) + 1) / 2 ≤ 3 := by
      have : ((a : ℝ)) ≤ 2 := by exact_mod_cast ha2
      push_cast
      linarith
    have her : e ≤ (((a + 2 : ℕ) : ℝ) + 1) / 2 := by
      push_cast
      linarith
    have hht := heat_term hν0 hν1 hc hx hr3 her
    have hYD : Y ^ (Na + 3) ≤ Y ^ D := pow_le_pow_right₀ hY (by omega)
    have hp0 : 0 ≤ (ν * x.2.2) ^ (-((((a + 2 : ℕ) : ℝ) + 1) / 2)) :=
      Real.rpow_nonneg (mul_nonneg hν0.le hs.le) _
    calc ν * (|meanCoeff T 1| * |Hw| * (wt * |(partialEta^[a + 2] (heatProfile ν)) x|))
        ≤ ν * (|meanCoeff T 1| * |Hw| *
            (Ch * (ν * x.2.2) ^ (-((((a + 2 : ℕ) : ℝ) + 1) / 2)))) := by
          gcongr
      _ = |meanCoeff T 1| * |Hw| * Ch *
            (ν * (ν * x.2.2) ^ (-((((a + 2 : ℕ) : ℝ) + 1) / 2))) := by ring
      _ ≤ (|Ca| * Y ^ Na) * |Hw| * Ch * (Y ^ 3 * x.2.2 ^ (-e)) := by
          gcongr
      _ = |Hw| * |Ca| * Ch * (Y ^ (Na + 3) * x.2.2 ^ (-e)) := by ring
      _ ≤ |Hw| * |Ca| * Ch * (Y ^ D * x.2.2 ^ (-e)) := by
          gcongr
  -- the remainder terms
  have hRb : ∀ i : ℕ, i ≤ 3 → wt * |jet i a 0 (remP T 1) x| ≤ |CR| * (Y ^ D * x.2.2 ^ (-e)) := by
    intro i hi
    have h1 := HR ν hν0 hνR' T hT i a hi ha1 ha2 x hx
    have hYD : Y ^ NR ≤ Y ^ D := pow_le_pow_right₀ hY (by omega)
    calc wt * |jet i a 0 (remP T 1) x| ≤ polyConst CR NR ν (ν ^ (-ρ)) * x.2.2 ^ (-3 : ℝ) := h1
      _ ≤ (|CR| * Y ^ D) * x.2.2 ^ (-e) :=
          mul_le_mul (pc_le (by omega) hν0 hc) hs3e (Real.rpow_nonneg hs.le _)
            (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _))
      _ = |CR| * (Y ^ D * x.2.2 ^ (-e)) := by ring
  -- the fluctuation terms
  have hFb : ∀ i : ℕ, i ≤ 3 →
      wt * |jet i a 0 (fluctP T) x| ≤ |Cf| * Ce * (Y ^ D * x.2.2 ^ (-e)) := by
    intro i hi
    have h1 := HF ν hν0 hνf' T hT i a 0 hi ha2 (by norm_num) x hx
    have hE := He ν (ν ^ (-ρ)) x.2.2 hν0 hc hx
    have hE' : Real.exp (-(κf * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) ≤ Ce * Y ^ Ne * x.2.2 ^ (-e) := by
      calc Real.exp (-(κf * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))
          ≤ polyConst Ce Ne ν (ν ^ (-ρ)) * x.2.2 ^ (-3 : ℝ) := hE
        _ ≤ (Ce * Y ^ Ne) * x.2.2 ^ (-e) :=
            mul_le_mul (le_of_eq rfl) hs3e (Real.rpow_nonneg hs.le _)
              (mul_nonneg hCe (pow_nonneg (by linarith) _))
    have hYD : Y ^ (Nf + Ne) ≤ Y ^ D := pow_le_pow_right₀ hY (by omega)
    calc wt * |jet i a 0 (fluctP T) x|
        ≤ polyConst Cf Nf ν (ν ^ (-ρ)) * Real.exp (-(κf * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) := h1
      _ ≤ (|Cf| * Y ^ Nf) * (Ce * Y ^ Ne * x.2.2 ^ (-e)) :=
          mul_le_mul (pc_le le_rfl hν0 hc) hE' (Real.exp_pos _).le
            (mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _))
      _ = |Cf| * Ce * (Y ^ (Nf + Ne) * x.2.2 ^ (-e)) := by ring
      _ ≤ |Cf| * Ce * (Y ^ D * x.2.2 ^ (-e)) := by
          gcongr
  -- the triangle inequality
  have hkey : wt * |X ν (trainProfile T.ψ) x| ≤
      ν * (|meanCoeff T 1| * |Hw| * (wt * |(partialEta^[a + 2] (heatProfile ν)) x|)) +
      ν * (|w₀| * (wt * |jet 0 a 0 (remP T 1) x|) + |w₁| * (wt * |jet 1 a 0 (remP T 1) x|) +
        |w₂| * (wt * |jet 2 a 0 (remP T 1) x|) + |w₃| * (wt * |jet 3 a 0 (remP T 1) x|)) +
      ν * (|w₀| * (wt * |jet 0 a 0 (fluctP T) x|) + |w₁| * (wt * |jet 1 a 0 (fluctP T) x|) +
        |w₂| * (wt * |jet 2 a 0 (fluctP T) x|) + |w₃| * (wt * |jet 3 a 0 (fluctP T) x|)) := by
    rw [hdec]
    have hR4 := abs4 w₀ w₁ w₂ w₃ (jet 0 a 0 (remP T 1) x) (jet 1 a 0 (remP T 1) x)
      (jet 2 a 0 (remP T 1) x) (jet 3 a 0 (remP T 1) x) wt hwt
    have hF4 := abs4 w₀ w₁ w₂ w₃ (jet 0 a 0 (fluctP T) x) (jet 1 a 0 (fluctP T) x)
      (jet 2 a 0 (fluctP T) x) (jet 3 a 0 (fluctP T) x) wt hwt
    set A := meanCoeff T 1 * Hw * (partialEta^[a + 2] (heatProfile ν)) x with hA
    set Rs := w₀ * jet 0 a 0 (remP T 1) x + w₁ * jet 1 a 0 (remP T 1) x +
      w₂ * jet 2 a 0 (remP T 1) x + w₃ * jet 3 a 0 (remP T 1) x with hRs
    set Fs := w₀ * jet 0 a 0 (fluctP T) x + w₁ * jet 1 a 0 (fluctP T) x +
      w₂ * jet 2 a 0 (fluctP T) x + w₃ * jet 3 a 0 (fluctP T) x with hFs
    have htri : |A + Rs + Fs| ≤ |A| + |Rs| + |Fs| := by
      calc |A + Rs + Fs| ≤ |A + Rs| + |Fs| := abs_add_le _ _
        _ ≤ |A| + |Rs| + |Fs| := by
            have := abs_add_le A Rs
            linarith
    have hAabs : wt * |A| =
        |meanCoeff T 1| * |Hw| * (wt * |(partialEta^[a + 2] (heatProfile ν)) x|) := by
      rw [hA, abs_mul, abs_mul]
      ring
    calc wt * |ν * (A + Rs + Fs)| = ν * (wt * |A + Rs + Fs|) := by
          rw [abs_mul, abs_of_pos hν0]
          ring
      _ ≤ ν * (wt * (|A| + |Rs| + |Fs|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htri hwt) hν0.le
      _ = ν * (wt * |A|) + ν * (wt * |Rs|) + ν * (wt * |Fs|) := by ring
      _ ≤ _ := by
          rw [hAabs]
          have h1 := mul_le_mul_of_nonneg_left hR4 hν0.le
          have h2 := mul_le_mul_of_nonneg_left hF4 hν0.le
          linarith
  -- the final bound
  have hT2 := sum4_le (w₀ := w₀) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) hν0 hν1
    (mul_nonneg hwt (abs_nonneg _)) (mul_nonneg hwt (abs_nonneg _))
    (mul_nonneg hwt (abs_nonneg _)) (mul_nonneg hwt (abs_nonneg _))
    (hRb 0 (by norm_num)) (hRb 1 (by norm_num)) (hRb 2 (by norm_num)) (hRb 3 (by norm_num))
  have hT3 := sum4_le (w₀ := w₀) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃) hν0 hν1
    (mul_nonneg hwt (abs_nonneg _)) (mul_nonneg hwt (abs_nonneg _))
    (mul_nonneg hwt (abs_nonneg _)) (mul_nonneg hwt (abs_nonneg _))
    (hFb 0 (by norm_num)) (hFb 1 (by norm_num)) (hFb 2 (by norm_num)) (hFb 3 (by norm_num))
  rw [← hW] at hT2 hT3
  have hfin : polyConst (|Hw| * |Ca| * Ch + W * |CR| + W * (|Cf| * Ce)) D ν (ν ^ (-ρ)) *
      x.2.2 ^ (-e) = |Hw| * |Ca| * Ch * (Y ^ D * x.2.2 ^ (-e)) +
        W * (|CR| * (Y ^ D * x.2.2 ^ (-e))) + W * (|Cf| * Ce * (Y ^ D * x.2.2 ^ (-e))) := by
    unfold polyConst
    ring
  rw [hfin]
  linarith

/-- **The `∂_q` entry**: `∂_qB₁` is exponentially small (only `ψ̃` enters). -/
theorem q_of_expand (hsm : LateProfileSmooth) (hL : JetLinear) (hP : TrainPartsSmooth)
    (hF : FluctJetUnif) (hQ : CoeffB1QEq) :
    LateStmt (fun ν c κ B m ψ _ => ExpBound κ ν c m (partialQ (coeffB₁ ν ψ)) B) := by
  intro ρ m hρ
  obtain ⟨Cf, Nf, κf, νf, hκf, hνf, HF⟩ := hF ρ m hρ
  refine ⟨min νf 1, lt_min hνf one_pos, 3 * |Cf|, Nf, κf, hκf, ?_⟩
  intro ν hν ψ p hψ
  obtain ⟨T, hT, rfl, -⟩ := hψ
  have hν0 : 0 < ν := hν.1
  have hνf' : ν ≤ νf := hν.2.le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν.2.le.trans (min_le_right _ _)
  have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hψs : ContDiffOn ℝ ∞ (trainProfile T.ψ) {y : ProfilePoint | 0 < y.2.2} :=
    (hsm ν _ hν0 hc T hT).1
  show ∀ x : ProfilePoint, 1 ≤ x.2.2 →
    (1 + x.2.1 ^ 2 / x.2.2) ^ m * |partialQ (coeffB₁ ν (trainProfile T.ψ)) x| ≤
      polyConst (3 * |Cf|) Nf ν (ν ^ (-ρ)) * Real.exp (-(κf * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))
  intro x hx
  have hs : 0 < x.2.2 := by linarith
  have hwt := wt_nonneg m hs
  rw [hQ ν _ hψs x hs, jet_split_q hL hP hν0 hc T hT 1 1 x hs,
    jet_split_q hL hP hν0 hc T hT 2 1 x hs]
  have h1 := HF ν hν0 hνf' T hT 1 1 1 (by norm_num) (by norm_num) le_rfl x hx
  have h2 := HF ν hν0 hνf' T hT 2 1 1 (by norm_num) (by norm_num) le_rfl x hx
  have hpc : polyConst Cf Nf ν (ν ^ (-ρ)) ≤ |Cf| * (1 + ν ^ (-ρ) + ν⁻¹) ^ Nf :=
    pc_le le_rfl hν0 hc
  set E := Real.exp (-(κf * ν * x.2.2 / (ν ^ (-ρ)) ^ 2)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  set wt : ℝ := (1 + x.2.1 ^ 2 / x.2.2) ^ m with hwtdef
  set j₁ := jet 1 1 1 (fluctP T) x
  set j₂ := jet 2 1 1 (fluctP T) x
  have habs : |2 * j₁ + j₂| ≤ 2 * |j₁| + |j₂| := by
    calc |2 * j₁ + j₂| ≤ |2 * j₁| + |j₂| := abs_add_le _ _
      _ = 2 * |j₁| + |j₂| := by rw [abs_mul, abs_two]
  have hsum : 2 * (wt * |j₁|) + wt * |j₂| ≤ 3 * (polyConst Cf Nf ν (ν ^ (-ρ)) * E) := by
    linarith
  have hnn : 0 ≤ 2 * (wt * |j₁|) + wt * |j₂| := by
    have := mul_nonneg hwt (abs_nonneg j₁)
    have := mul_nonneg hwt (abs_nonneg j₂)
    linarith
  calc wt * |ν * (2 * j₁ + j₂)| = ν * (wt * |2 * j₁ + j₂|) := by
        rw [abs_mul, abs_of_pos hν0]
        ring
    _ ≤ ν * (wt * (2 * |j₁| + |j₂|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hwt) hν0.le
    _ = ν * (2 * (wt * |j₁|) + wt * |j₂|) := by ring
    _ ≤ 1 * (2 * (wt * |j₁|) + wt * |j₂|) := mul_le_mul_of_nonneg_right hν1 hnn
    _ ≤ 3 * (polyConst Cf Nf ν (ν ^ (-ρ)) * E) := by linarith
    _ ≤ 3 * ((|Cf| * (1 + ν ^ (-ρ) + ν⁻¹) ^ Nf) * E) := by
        gcongr
    _ = polyConst (3 * |Cf|) Nf ν (ν ^ (-ρ)) * E := by
        unfold polyConst
        ring

/-- **`PartII-a:R02/9`, conditional on the leaves**: the `B₁` block of the late table. -/
theorem ringLateB1_of_parts (h : LateIngredients) (h1 : CoeffB1Eq) (h2 : CoeffB1EtaEq)
    (h3 : CoeffB1ShiftEq) (h4 : CoeffB1QEq) (hHe : HeatJetEigen) (hL : JetLinear)
    (hP : TrainPartsSmooth) (hF : FluctJetUnif) (hR : RemJetUnif) : RingLateB1 := by
  have A := wtd_of_expand h hHe hL hP hF hR (fun ν g => coeffB₁ ν g) 1 le_rfl (by norm_num)
    0 2 1 0 2 (by norm_num) (by norm_num) (fun ν g hg x hx => by rw [h1 ν g hg x hx]; ring)
  have B := wtd_of_expand h hHe hL hP hF hR (fun ν g => partialEta (coeffB₁ ν g)) 2
    (by norm_num) le_rfl 3 4 1 0 (5 / 2) (by norm_num) (by norm_num)
    (fun ν g hg x hx => by rw [h2 ν g hg x hx]; ring)
  have Cc := wtd_of_expand h hHe hL hP hF hR (fun ν g => ageShift 3 (coeffB₁ ν g)) 1 le_rfl
    (by norm_num) 0 6 5 1 2 (by norm_num) (by norm_num)
    (fun ν g hg x hx => by rw [h3 ν g hg x hx]; ring)
  have Dq := q_of_expand h.smooth hL hP hF h4
  have mW : ∀ (Y : ℝ → (ProfilePoint → ℝ) → ProfilePoint → ℝ) (e : ℝ),
      LateMono (fun ν _ _ B m ψ _ => WtdBound m (Y ν ψ) e B) :=
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hW => WtdBound.mono' hB hW
  have mE : LateMono (fun ν c κ B m ψ _ => ExpBound κ ν c m (partialQ (coeffB₁ ν ψ)) B) :=
    fun _ _ _ _ _ _ _ _ _ hν hc hκ hB hE => ExpBound.mono' hν hc hκ hB hE
  have CD := LateStmt.and (mW _ _) mE Cc Dq
  have BCD := LateStmt.and (mW _ _) ((mW _ _).and mE) B CD
  exact LateStmt.and (mW _ _) ((mW _ _).and ((mW _ _).and mE)) A BCD

end UnforcedLeray.Short.PartIIa.BlockB1
