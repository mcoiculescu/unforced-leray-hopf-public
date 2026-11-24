import UnforcedLeray.Short.PartIIa.Calc.JetClass

/-!
# Part II-a, base jets of the train (task `PartII-a:R02/8/org`)

Source of record: `the November 2 reference manuscript`, lines 397-404 (the mean
stream `S = \bar ψ`, `sct:mean`), 437-480 (Lemma `sct:heat`: `sct:fluctuation` 439-446 for the
fluctuation `ψ̃ = ψ - S` and the pressure `p`; `sct:expansion` 447-459 for
`S = a₀ G_{νs} + R₀`), 1267-1268 (the heat identity `K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}`).

The stream splits as `ψ = S + ψ̃` (`psiFam_eq`).  The base jets are

* `ψ̃`, `p`: every word `K^ℓ ∂_η^a ∂_q^b` is exponentially small (`FluctWords`, from
  `LateFluctuationProfile`), hence `∀ n, JE n` (`JE_of_words`);
* `S`: `q`-independent and every word `K^ℓ ∂_η^b S` has size `s^{-(b+1)/2}` (`WordsW (1/2)`), from
  `S = a₀ G + R₀`, `K^ℓ ∂_η^b G = (-(b+1))^ℓ ∂_η^b G` (`HeatWords`), `|a₀| ≤ P`, the heat size
  `(νs)^{-(b+1)/2}` (`MeanHeatPart`) and the remainder size `s^{-(b+3)/2}` (`MeanRemPart`); hence
  `∀ n, JQ n (1/2)` (`JQ_of_words`).

## Exports

`psiFam, presFam, meanFam, fluctFam, remFam0, psiFam_eq, meanFam_eq`; the statements
`FluctWords, MeanSmoothQ, HeatWords, MeanHeatPart, MeanRemPart` (leaves `PartII-a:R02/8/<k>`);
`baseJets_of (hJ : JetCalculus) (hWE : WordShiftE) (hWW : WordShiftW) (hF : FluctWords)
(hM : WordsW (1/2) meanFam) (n : ℕ) : JQ n (1/2) meanFam ∧ JE n fluctFam ∧ JE n presFam ∧
JQ n (1/2) psiFam`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanStream meanRemainder meanCoeff heatKernel1)

/-- The stream profile `ψ(q, η, s)` of the train. -/
def psiFam : Fam := fun _ _ tr => trainProfile tr.ψ

/-- The pressure profile `p(q, η, s)` (decaying gauge, line 445). -/
def presFam : Fam := fun _ _ tr => trainProfile tr.p

/-- The mean stream `S = \bar ψ` (line 397) as a profile (independent of `q`). -/
def meanFam : Fam := fun _ _ tr => trainProfile fun s z => meanStream tr s z.2

/-- The stream fluctuation `ψ̃ = ψ - S` (line 439). -/
def fluctFam : Fam := fun _ _ tr => trainProfile fun s z => tr.ψ s z - meanStream tr s z.2

/-- The remainder `R₀ = S - a₀ G_{νs}` of the mean expansion (lines 447-449, `N = 0`). -/
def remFam0 : Fam := fun _ _ tr => trainProfile fun s z => meanRemainder tr 0 s z.2

theorem psiFam_eq : psiFam = meanFam + fluctFam := by
  funext ν c tr x
  show trainProfile tr.ψ x = trainProfile (fun s z => meanStream tr s z.2) x +
    trainProfile (fun s z => tr.ψ s z - meanStream tr s z.2) x
  simp only [trainProfile]
  ring

/-- `S = R₀ + a₀ G_{νs}` everywhere (definition of `meanRemainder` with `N = 0`). -/
theorem meanFam_eq (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ProfilePoint) :
    meanFam ν c tr x = remFam0 ν c tr x + meanCoeff tr 0 * heatProfile ν x := by
  simp [meanFam, remFam0, meanRemainder, trainProfile, heatProfile]

/-! ### Statements of the base jets (leaves `PartII-a:R02/8/<k>`) -/

/-- **Fluctuation and pressure words** (`sct:fluctuation`, lines 439-446, in profile form
`LateFluctuationProfile`): `ψ̃` and `p` are smooth for `s > 0` and every word
`K^ℓ ∂_η^a ∂_q^b` of them is exponentially small. -/
def FluctWords : Prop := WordsE fluctFam ∧ WordsE presFam

/-- **The mean stream is smooth and `q`-independent** (lines 397-404): `S` is `C^∞` for `s > 0`
and `∂_q S = 0` there. -/
def MeanSmoothQ : Prop := JSmooth meanFam ∧ LateEq (famQ meanFam) 0

/-- **Heat words** (lines 1267-1268, `K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}`, iterated): the heat
profile is smooth for `s > 0` and `K^ℓ ∂_η^b G_{νs} = (-(b+1))^ℓ ∂_η^b G_{νs}` there. -/
def HeatWords : Prop :=
  ∀ ν : ℝ, 0 < ν → ContDiffOn ℝ ∞ (heatProfile ν) {x : ProfilePoint | 0 < x.2.2} ∧
    ∀ ℓ b : ℕ, EqOn (ageOperator^[ℓ] (partialEta^[b] (heatProfile ν)))
      (fun x => (-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) x)
      {x : ProfilePoint | 0 < x.2.2}

/-- **Size of the leading mean term** (`sct:expansion`, lines 453-455 for `|a₀| ≤ P`, and the heat
size `(1+η²/s)^m |∂_η^b G_{νs}| ≤ C (νs)^{-(b+1)/2}` for `ν ≤ 1`, `s ≥ 1`): the word
`a₀ (-(b+1))^ℓ ∂_η^b G_{νs}` has size `s^{-(b+1)/2}`. -/
def MeanHeatPart : Prop :=
  ∀ ℓ b : ℕ, WW (1 / 2 + (b : ℝ) / 2)
    (fun ν _ tr x => meanCoeff tr 0 * ((-((b : ℝ) + 1)) ^ ℓ * (partialEta^[b] (heatProfile ν)) x))

/-- **Size of the mean remainder** (`sct:expansion`, lines 457-458 with `N = 0`, `p = ∞`, in profile
form `LateMeanRemainder`): `K^ℓ ∂_η^b R₀` has size `s^{-(b+3)/2} ≤ s^{-(b+1)/2}`. -/
def MeanRemPart : Prop := ∀ ℓ b : ℕ, WW (1 / 2 + (b : ℝ) / 2) (wordW ℓ b remFam0)

/-! ### The base jets -/

/-- **Base jets** of the train from the word statements. -/
theorem baseJets_of (hJ : JetCalculus) (hWE : WordShiftE) (hWW : WordShiftW) (hF : FluctWords)
    (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n (1 / 2) meanFam ∧ JE n fluctFam ∧ JE n presFam ∧ JQ n (1 / 2) psiFam := by
  have h1 := JQ_of_words hJ hWW n _ _ hM
  have h2 := JE_of_words hWE n _ hF.1
  have h3 := JE_of_words hWE n _ hF.2
  refine ⟨h1, h2, h3, ?_⟩
  rw [psiFam_eq]
  exact hJ.qadd h1 (hJ.qofE _ h2)

end UnforcedLeray.Short.PartIIa.Jet
