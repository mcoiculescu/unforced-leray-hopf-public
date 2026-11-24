import UnforcedLeray.Short.PartIIa.Calc.BaseJets

/-!
# Part II-a, block `A₂` of the late residual table on the jet-class calculus

Organizer file of `PartII-a:R02/12/org`.  Target of the block: `RingLateA2`
(`Short/PartII-a/Sub/R02.lean`), i.e. for
`A₂ = (∂_s + v·∇ - νΔ)H + H(v₂)_η - v₁(K+1)v₂ + 2ν(K+1)(v₂)_q` (`B0188.coeffA₂`, source lines
1253-1254) the four quantities `A₂`, `∂_ηA₂`, `(K+3)A₂`, `∂_qA₂` are exponentially small
`P e^{-κνs/c²}` with the normalized weight (table row `A₂`, line 1278; "Every `q` derivative is
exponentially small", line 1281).

Source of record: `the November 2 reference manuscript`, lines 1243-1285 (the
coefficients 1249-1257; the late table 1267-1280; "Also `(∂_s - ν∂_η²)(S - KS) = -(K+1)g`, and every
remaining term of `A₂` has a fluctuation factor", 1284-1285), lines 397-404 (`sct:mean`:
`S_s - νS_ηη = g := \overline{v₁v₂}`, `\bar v₁ = -S_η`, `\bar v₂ = 0`), and lines 437-481
(Lemma `sct:heat`: `sct:fluctuation` 439-446, every mixed age/spatial derivative of
`(ψ̃, ṽ, p)` is `≤ P e^{-κνs/c²}`).

## The mathematics

Write `ψ = S + ψ̃` (`psiFam = meanFam + fluctFam`, `Calc/BaseJets.lean`), `H = (1-K)ψ`
(`defectFam`), `\bar H = S - KS` (`defectMean`), `H̃ = ψ̃ - Kψ̃` (`defectFluct`), so
`H = \bar H + H̃` for `s > 0` (`defect_split`), `v₁ = -∂_ηψ` (`v1`), `v₂ = ∂_qψ` (`v2`).

* (i) **Algebraic decomposition** (`coeffA2_late`, pure algebra): with the heat operator
  `heatOp F = (∂_s - ν∂_η²)F`,
  `A₂ = (∂_s - ν∂_η²)H + v₁∂_qH + v₂∂_ηH - ν∂_q²H + H∂_ηv₂ - v₁(K+1)v₂ + 2ν(K+1)∂_qv₂`.
* (ii) **Mean-stress cancellation** (line 1284, `meanStressCancel_of`):
  `(∂_s - ν∂_η²)(S - KS) = -(K+1)g`, from the mean equation `(∂_s - ν∂_η²)S = g` (`MeanHeatEq`,
  line 399) and the commutation `(∂_s - ν∂_η²)K = (K+2)(∂_s - ν∂_η²)` (`HeatOpK`, from
  `[∂_s, K] = 2∂_s` and `∂_η²K = (K+2)∂_η²`); `g` is exponentially small with all its jets
  (`StressWords`).
* (iii) **Fluctuation factors** (line 1285): `(∂_s - ν∂_η²)H̃ ∈ JE` (an age derivative of an
  exponentially small jet is exponentially small: `2s∂_s = K - η∂_η`, `AgeWE`, and `∂_s` commutes
  with `∂_η, ∂_q` and `K∂_s = ∂_s(K - 2)`, `AgeComm`; `ageJE_of`, `heatJE_of`); every other term
  contains `∂_q` of a weighted jet (`∂_qH`, `∂_q²H`) or the factor `v₂ = ∂_qψ = ∂_qψ̃`, so it is in
  `JE` by the product closure with the polynomially bounded companions `v₁, H, ∂_ηH ∈ JQ 0`
  (`a2Jets_of`).
* (iv) **Block extraction**: `JE 1 A₂` gives `RingLateA2` by `lateStmt_of_JE`
  (`Calc/JetClass.lean`), `ringLateA2_of_parts`.

## Leaf statements (tasks `PartII-a:R02/12/<k>`, files `Calc/BlockA2Calc/<Name>.lean`)

`AgeSmoothLocal` (`/1`), `HeatOpLin` (`/2`), `AgeComm` (`/3`, from `ProfileCommutators`),
`AgeWE` (`/4`), `HeatOpK` (`/5`, from `ProfileCommutators` and `IterCalcComm`), `MeanHeatEq`
(`/6`, from `TrainMeanEquations`), `StressWords` (`/7`, from `LateIngredients`).

## Proved here

`heatOp_congr`, `jsmooth_sub`, `ageJE_of`, `heatJE_of`, `meanStressCancel_of`, `defect_split`,
`heat_defect_split`, `coeffA2_late`, `a2Jets_of`, `ringLateA2_of_jets`, and
**`ringLateA2_of_parts (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1/2) meanFam)
(hA : AgeSmoothLocal) (hL : HeatOpLin) (hC : AgeComm) (hW : AgeWE) (hK : HeatOpK)
(hE : MeanHeatEq) (hG : StressWords) : RingLateA2`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet.A2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (IsBUCTrain meanStream meanStress)

/-! ### Families and the heat operator -/

/-- `∂_s F` (`partialAge`). -/
def famAge (F : Fam) : Fam := fun ν c tr => partialAge (F ν c tr)

/-- The heat operator `(∂_s - ν∂_η²)F` of the mean equation (line 399) and of line 1284. -/
def heatOp (F : Fam) : Fam := famAge F - famNu (famEta (famEta F))

/-- The mean stress `g = \overline{v₁v₂}` (`sct:mean`, line 399) as a profile (independent of
`q`). -/
def stressFam : Fam := fun _ _ tr => trainProfile fun s z => meanStress tr s z.2

/-- `v₁ = -∂_ηψ` (`streamV1`). -/
def v1 : Fam := -(famEta psiFam)

/-- `v₂ = ∂_qψ` (`streamV2`). -/
def v2 : Fam := famQ psiFam

/-- `H = (1-K)ψ` (`ageDefect`). -/
def defectFam : Fam := psiFam - famK psiFam

/-- The mean part `\bar H = S - KS` of `H`. -/
def defectMean : Fam := meanFam - famK meanFam

/-- The fluctuation part `H̃ = ψ̃ - Kψ̃` of `H`. -/
def defectFluct : Fam := fluctFam - famK fluctFam

/-- The coefficient `A₂` as a residual coefficient (it does not depend on the pressure). -/
def coefA2 : ℝ → (ProfilePoint → ℝ) → (ProfilePoint → ℝ) → ProfilePoint → ℝ :=
  fun ν ψ _ => coeffA₂ ν ψ

/-! ### Leaf statements (tasks `PartII-a:R02/12/<k>`) -/

/-- **`∂_s` is smooth and local** (calculus on the open set `{s > 0}`): `∂_s` of a family smooth
for `s > 0` is smooth there (`contDiffOn_fderiv_apply`, `Sub/R02_2.lean`), and families equal
for `s > 0` have equal `∂_s` there (`Filter.EventuallyEq.fderiv_eq`).  Needed to read the age
derivatives of `sct:fluctuation` (lines 439-446) and of `sct:mean` (line 399) in the jet classes. -/
def AgeSmoothLocal : Prop :=
  (∀ F : Fam, JSmooth F → JSmooth (famAge F)) ∧
  (∀ F G : Fam, LateEq F G → LateEq (famAge F) (famAge G))

/-- **The heat operator `∂_s - ν∂_η²` is additive on smooth families** (calculus on `{s > 0}`:
`fderiv_add`/`fderiv_sub` at points of differentiability; the inner `∂_η` of a sum agrees near the
point with the sum of the `∂_η`'s).  Used for `H = \bar H + H̃` and `\bar H = S - KS`
(lines 1284-1285). -/
def HeatOpLin : Prop :=
  ∀ F G : Fam, JSmooth F → JSmooth G →
    LateEq (heatOp (F + G)) (heatOp F + heatOp G) ∧
    LateEq (heatOp (F - G)) (heatOp F - heatOp G)

/-- **Commutators of `∂_s`** (`K = η∂_η + 2s∂_s`; `[∂_s, K] = 2∂_s` is the third conjunct of
`ProfileCommutators`, and `∂_s` commutes with `∂_η, ∂_q` by the symmetry of second derivatives,
`FluctuationProfile.profile_fderiv_comm_at`): for `F` smooth for `s > 0`,
`K∂_sF = ∂_sKF - 2∂_sF`, `∂_η∂_sF = ∂_s∂_ηF`, `∂_q∂_sF = ∂_s∂_qF` there.  These make the age
derivatives of `sct:fluctuation` (lines 439-446, "every fixed mixed age/spatial derivative")
available as jets. -/
def AgeComm : Prop :=
  ∀ F : Fam, JSmooth F →
    LateEq (famK (famAge F)) (famAge (famK F) - (2 : ℝ) • famAge F) ∧
    LateEq (famEta (famAge F)) (famAge (famEta F)) ∧
    LateEq (famQ (famAge F)) (famAge (famQ F))

/-- **An age derivative of an exponentially small family is exponentially small**
(`sct:fluctuation`, lines 439-446, with `ℓ = 1`): from `2s∂_sF = KF - η∂_ηF` and, for `s ≥ 1`,
`|η|/(2s) ≤ 1 + η²/s`, the weighted bound of `∂_sF` at weight `m` follows from those of `KF` at
weight `m` and of `∂_ηF` at weight `m + 1`. -/
def AgeWE : Prop := ∀ F : Fam, WE (famK F) → WE (famEta F) → WE (famAge F)

/-- **The heat operator and `K`** (calculus on `{s > 0}`, used for line 1284):
`(∂_s - ν∂_η²)K = (K+2)(∂_s - ν∂_η²)` on families smooth for `s > 0`, from `[∂_s, K] = 2∂_s`
(`ProfileCommutators`) and `∂_η²K = (K+2)∂_η²` (`IterCalcComm` with `a = 2`). -/
def HeatOpK : Prop :=
  ∀ F : Fam, JSmooth F → LateEq (heatOp (famK F)) (famShift 2 (heatOp F))

/-- **The mean equation in profile variables** (`sct:mean`, line 399: `S_s - νS_ηη = g`):
`(∂_s - ν∂_η²)S = g` for `s > 0` (from `TrainMeanEquations`, second conjunct, converting the
one-variable derivatives into the profile partials with `profileDict`). -/
def MeanHeatEq : Prop := LateEq (heatOp meanFam) stressFam

/-- **The mean stress is an exponentially small jet** (`sct:mean`, line 399, `g = \overline{v₁v₂}`,
with `sct:fluctuation`, lines 439-446): `g` is smooth for `s > 0` (`MeanStressSmooth`), every word
`K^ℓ∂_η^a g` is exponentially small (`LateMeanStress`), and `∂_q g = 0` (`g` does not depend on
`q`), so every word `K^ℓ∂_η^a∂_q^b g` with `b ≥ 1` vanishes. -/
def StressWords : Prop := WordsE stressFam

/-! ### Elementary closure facts -/

theorem jsmooth_sub (hT : JetToolkit) {F G : Fam} (hF : JSmooth F) (hG : JSmooth G) :
    JSmooth (F - G) := by
  rw [sub_eq_add_neg', neg_eq_smul]
  exact (hT.smooth F _ hF ((hT.smooth G G hG hG).2.2.1 (-1))).1

/-- The heat operator only sees `s > 0`. -/
theorem heatOp_congr (hT : JetToolkit) (hA : AgeSmoothLocal) {F G : Fam} (h : LateEq F G) :
    LateEq (heatOp F) (heatOp G) := by
  have h1 := hA.2 F G h
  have h2 := (hT.eqOps _ _ (hT.eqOps F G h).2.1).2.1
  intro ν c hν hc tr htr x hx
  have e1 := h1 ν c hν hc tr htr hx
  have e2 := h2 ν c hν hc tr htr hx
  simp only [heatOp, famNu, Pi.sub_apply]
  rw [e1, e2]

/-- **Age derivatives of exponentially small jets** (line 439-446 for `ℓ = 1`, in jet form). -/
theorem ageJE_of (hJ : JetCalculus) (hA : AgeSmoothLocal) (hC : AgeComm) (hW : AgeWE) :
    ∀ (n : ℕ) (F : Fam), JE (n + 1) F → JE n (famAge F)
  | 0, F, h => JE.mk0 (hA.1 F h.smooth) (hW F h.k.we h.eta.we)
  | n + 1, F, h => by
    obtain ⟨hK, hEta, hQ⟩ := hC F h.smooth
    refine JE.mk (hA.1 F h.smooth) (hW F h.k.we h.eta.we) ?_ ?_ ?_
    · exact hJ.econgr hK.symm (hJ.esub (ageJE_of hJ hA hC hW n _ h.k)
        (hJ.esmul 2 (ageJE_of hJ hA hC hW n F h.down)))
    · exact hJ.econgr hEta.symm (ageJE_of hJ hA hC hW n _ h.eta)
    · exact hJ.econgr hQ.symm (ageJE_of hJ hA hC hW n _ h.q)

/-- The heat operator of an exponentially small jet is exponentially small. -/
theorem heatJE_of (hJ : JetCalculus) (hA : AgeSmoothLocal) (hC : AgeComm) (hW : AgeWE)
    (n : ℕ) (F : Fam) (h : JE (n + 2) F) : JE n (heatOp F) :=
  hJ.esub (ageJE_of hJ hA hC hW n F h.down) (hJ.enu h.eta.eta)

/-! ### (ii) Mean-stress cancellation (line 1284) -/

/-- **`(∂_s - ν∂_η²)(S - KS) = -(K+1)g`** (line 1284): `(∂_s - ν∂_η²)S = g` and
`(∂_s - ν∂_η²)KS = (K+2)(∂_s - ν∂_η²)S = (K+2)g`, so the difference is `g - (K+2)g = -(K+1)g`. -/
theorem meanStressCancel_of (hT : JetToolkit) (hL : HeatOpLin) (hK : HeatOpK) (hM : MeanHeatEq)
    (hS : JSmooth meanFam) : LateEq (heatOp defectMean) (-(famShift 1 stressFam)) := by
  show LateEq (heatOp (meanFam - famK meanFam)) (-(famShift 1 stressFam))
  have h1 := (hL meanFam (famK meanFam) hS (hT.smooth meanFam meanFam hS hS).2.2.2.2.1).2
  have h2 := hK meanFam hS
  have h3 := (hT.eqOps _ _ hM).1
  intro ν c hν hc tr htr x hx
  have e1 := h1 ν c hν hc tr htr hx
  have e2 := h2 ν c hν hc tr htr hx
  have e3 := h3 ν c hν hc tr htr hx
  have e4 := hM ν c hν hc tr htr hx
  simp only [Pi.sub_apply, Pi.neg_apply, famShift, ageShift, famK] at e1 e2 e3 e4 ⊢
  linarith

/-! ### (iii) The split `H = \bar H + H̃` and the fluctuation terms -/

theorem defect_split (hT : JetToolkit) (hS : JSmooth meanFam) (hFl : JSmooth fluctFam) :
    LateEq defectFam (defectMean + defectFluct) := by
  have h1 := (hT.linOps meanFam fluctFam hS hFl 0).1
  intro ν c hν hc tr htr x hx
  have e1 := h1 ν c hν hc tr htr hx
  have e0 : psiFam ν c tr x = meanFam ν c tr x + fluctFam ν c tr x := by
    rw [psiFam_eq]; rfl
  have e0' : famK psiFam ν c tr x = famK (meanFam + fluctFam) ν c tr x := by
    rw [psiFam_eq]
  simp only [defectFam, defectMean, defectFluct, Pi.add_apply, Pi.sub_apply] at e1 ⊢
  linarith

theorem heat_defect_split (hT : JetToolkit) (hA : AgeSmoothLocal) (hL : HeatOpLin)
    (hS : JSmooth meanFam) (hFl : JSmooth fluctFam) :
    LateEq (heatOp defectFam) (heatOp defectMean + heatOp defectFluct) :=
  (heatOp_congr hT hA (defect_split hT hS hFl)).trans
    (hL _ _ (jsmooth_sub hT hS (hT.smooth _ _ hS hS).2.2.2.2.1)
      (jsmooth_sub hT hFl (hT.smooth _ _ hFl hFl).2.2.2.2.1)).1

/-! ### (i) The algebraic decomposition of `A₂` (lines 1253-1254) -/

/-- **`A₂` as a combination of jets**: `transportDiffusion ν ψ H = ∂_sH + v₁∂_qH + v₂∂_ηH -
ν(∂_q²H + ∂_η²H)`, regrouped as `(∂_s - ν∂_η²)H + v₁∂_qH + v₂∂_ηH - ν∂_q²H`. -/
theorem coeffA2_late :
    LateEq (heatOp defectFam + v1 * famQ defectFam + v2 * famEta defectFam -
        famNu (famQ (famQ defectFam)) + defectFam * famEta v2 - v1 * famShift 1 v2 +
        (2 : ℝ) • famNu (famShift 1 (famQ v2))) (coefFam coefA2) := by
  intro ν c _ _ tr _ x _
  show partialAge (ageDefect (trainProfile tr.ψ)) x
      - ν * partialEta (partialEta (ageDefect (trainProfile tr.ψ))) x
      + streamV1 (trainProfile tr.ψ) x * partialQ (ageDefect (trainProfile tr.ψ)) x
      + streamV2 (trainProfile tr.ψ) x * partialEta (ageDefect (trainProfile tr.ψ)) x
      - ν * partialQ (partialQ (ageDefect (trainProfile tr.ψ))) x
      + ageDefect (trainProfile tr.ψ) x * partialEta (streamV2 (trainProfile tr.ψ)) x
      - streamV1 (trainProfile tr.ψ) x * ageShift 1 (streamV2 (trainProfile tr.ψ)) x
      + 2 * (ν * ageShift 1 (partialQ (streamV2 (trainProfile tr.ψ))) x)
      = coeffA₂ ν (trainProfile tr.ψ) x
  simp only [coeffA₂, transportDiffusion, profileLap]
  ring

/-! ### The jets of `A₂` and the block -/

/-- **`A₂` is an exponentially small jet** at every depth (lines 1278, 1281, 1284-1285). -/
theorem a2Jets_of (hJ : JetCalculus) (hA : AgeSmoothLocal) (hC : AgeComm) (hW : AgeWE)
    (hψ : ∀ n, JQ n (1 / 2) psiFam) (hFl : ∀ n, JE n fluctFam) (hG : ∀ n, JE n stressFam)
    (hcancel : LateEq (heatOp defectMean) (-(famShift 1 stressFam)))
    (hsplit : LateEq (heatOp defectFam) (heatOp defectMean + heatOp defectFluct)) (n : ℕ) :
    JE n (coefFam coefA2) := by
  have hH : ∀ n, JQ n (1 / 2) defectFam := fun n => hJ.qsub (hψ n) (hψ (n + 1)).k
  have hv1 : ∀ n, JQ n 0 v1 := fun n => hJ.qmono (by norm_num) (hJ.qneg (hψ (n + 1)).eta)
  have hv2 : ∀ n, JE n v2 := fun n => (hψ (n + 1)).q
  have hHt : ∀ n, JE n defectFluct := fun n => hJ.esub (hFl n) (hFl (n + 1)).k
  have hH0 : ∀ n, JQ n 0 defectFam := fun n => hJ.qmono (by norm_num) (hH n)
  have t1 : JE n (heatOp defectFam) :=
    hJ.econgr hsplit.symm (hJ.eadd (hJ.econgr hcancel.symm (hJ.eneg (hJ.eshift 1 (hG (n + 1)))))
      (heatJE_of hJ hA hC hW n _ (hHt (n + 2))))
  have t2 : JE n (v1 * famQ defectFam) := hJ.qmulE (hv1 n) (hH (n + 1)).q
  have t3 : JE n (v2 * famEta defectFam) :=
    hJ.emulQ (hv2 n) (hJ.qmono (by norm_num) (hH (n + 1)).eta)
  have t4 : JE n (famNu (famQ (famQ defectFam))) := hJ.enu (hH (n + 2)).q.q
  have t5 : JE n (defectFam * famEta v2) := hJ.qmulE (hH0 n) (hv2 (n + 1)).eta
  have t6 : JE n (v1 * famShift 1 v2) := hJ.qmulE (hv1 n) (hJ.eshift 1 (hv2 (n + 1)))
  have t7 : JE n ((2 : ℝ) • famNu (famShift 1 (famQ v2))) :=
    hJ.esmul 2 (hJ.enu (hJ.eshift 1 (hv2 (n + 2)).q))
  exact hJ.econgr coeffA2_late
    (hJ.eadd (hJ.esub (hJ.eadd (hJ.esub (hJ.eadd (hJ.eadd t1 t2) t3) t4) t5) t6) t7)

/-- **(iv) The `A₂` block from the jets** (block extraction `lateStmt_of_JE`). -/
theorem ringLateA2_of_jets (h : JE 1 (coefFam coefA2)) : RingLateA2 :=
  lateStmt_of_JE coefA2 h

/-- **`PartII-a:R02/12`, conditional on the calculus, the base words and the seven leaves.** -/
theorem ringLateA2_of_parts (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam)
    (hA : AgeSmoothLocal) (hL : HeatOpLin) (hC : AgeComm) (hW : AgeWE) (hK : HeatOpK)
    (hE : MeanHeatEq) (hG : StressWords) : RingLateA2 := by
  have hB := baseJets_of hT.jc hT.wordE hT.wordW hF hM
  have hS : JSmooth meanFam := hM.1
  have hFl : JSmooth fluctFam := hF.1.1
  exact ringLateA2_of_jets (a2Jets_of hT.jc hA hC hW (fun n => (hB n).2.2.2) (fun n => (hB n).2.1)
    (fun n => JE_of_words hT.wordE n stressFam hG) (meanStressCancel_of hT hL hK hE hS)
    (heat_defect_split hT hA hL hS hFl) 1)

end UnforcedLeray.Short.PartIIa.Jet.A2
