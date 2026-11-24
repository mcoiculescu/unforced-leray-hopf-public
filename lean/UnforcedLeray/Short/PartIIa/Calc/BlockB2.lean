import UnforcedLeray.Short.PartIIa.Calc.BaseJets
import UnforcedLeray.Short.PartIIa.Tasks.R02.HeatProfile

/-!
# Part II-a, block `B₂` of the late residual table: mean cancellation and assembly

Organizer file of `PartII-a:R02/10/org`.  Target of the block: `RingLateB2`
(`Short/PartII-a/Sub/R02.lean`), i.e. for
`B₂ = -v₁(K+1)H + HH_η + 2ν(K+1)H_q - ν(K+1)²v₂` (`B0188.coeffB₂`, source line 1256) the late
sizes `s^{-3/2}` (`B₂`), `s^{-2}` (`∂_ηB₂`), `s^{-5/2}` (`(K+3)B₂`) with the normalized weight
`⟨η/√s⟩^{2m}`, and `∂_qB₂` exponentially small (source lines 1267-1281, row `B₂, B₃`).

Source of record: `the November 2 reference manuscript`, lines 1243-1283 (the
coefficients; "The heat identity `K∂_η^jG_{νs} = -(j+1)∂_η^jG_{νs}` and Lemma `sct:heat` give the
following complete late residual table", 1267-1268; "the leading means of `B₂, B₃` are
`4a₀²G_{νs}∂_ηG_{νs}` and … both have `K` degree `-3`", 1281-1283), lines 397-404 (`sct:mean`: the
mean stream `S = \bar ψ`, `\bar v₁ = -S_η`, `\bar v₂ = 0`) and 437-481 (Lemma `sct:heat`:
`sct:fluctuation` 439-446, `sct:expansion` 447-459).

## The mathematics

Write `ψ = S + ψ̃` (`psiFam = meanFam + fluctFam`, `Calc/BaseJets.lean`) and
`S = a₀G + R₀` (`G = G_{νs}` = `heatProfile ν`, `R₀ = remFam0`, `sct:expansion` with `N = 0`).
* Generic sizes (jet calculus of `Calc/JetClass.lean`): `ψ ∈ JQ (1/2)`, `v₁ = -∂_ηψ ∈ JQ 1`,
  `H = (1-K)ψ ∈ JQ (1/2)`, so `v₁(K+1)H, HH_η ∈ JQ (3/2)`; the `∂_q` terms are in `JE`
  (`coefB2_JQ`).  This gives the sizes of `B₂` and `∂_ηB₂`.
* Mean part `M₂ = -\bar v₁(K+1)\bar H + \bar H\bar H_η` (`meanB2`): with `\bar H = (1-K)S`,
  `KG = -G` gives `\bar H = 2a₀G + h₁`, `h₁ = (1-K)R₀` of size `s^{-3/2}` (`hbar_split`), and
  `(K+1)\bar H = (K+1)h₁` (`hbar_shift1`).  Hence `M₂ = 4a₀²G∂_ηG + M_r` (`meanB2_split`), with
  `M_r = -\bar v₁(K+1)h₁ + 2a₀G∂_ηh₁ + h₁∂_η\bar H` of size `s^{-5/2}` (`meanRest_JQ`).
  **Mean cancellation**: the leading mean `4a₀²G∂_ηG` has `K` degree `-3`:
  `K(G∂_ηG) = (KG)∂_ηG + G(K∂_ηG) = -3G∂_ηG` (heat identity and Leibniz), so `(K+3)` kills it
  (`bB2_K3_GG`, `lead_shift3`).
* Fluctuation part `B₂ - M₂` (`fluctB2`): every term carries a factor `ψ̃` (or `∂_q`), so it is
  exponentially small (`fluct_JE`).
* So `(K+3)B₂ = (K+3)M_r + (K+3)(B₂ - M₂)` has size `s^{-5/2}`, and the block follows by the
  extraction `lateStmt_grpW` (`ringLateB2_of_parts`).

## Layout

* Concrete heat calculus (namespace `UnforcedLeray.Short.PartIIa`, proved): `bB2_ageOperator_congr`,
  `bB2_ageOperator_mul`, `bB2_ageOperator_const_mul`, `bB2_partialEta_const_mul`, `bB2_K_lhP`,
  `bB2_ageDefect_lhP`, `bB2_K3_GG`, `bB2_Kp1_ageDefect_G`.
* Families and the block (namespace `UnforcedLeray.Short.PartIIa.Jet.B2`, proved from the jet
  toolkit): `leadG`, `v1bar`, `hbar`, `h1`, `lead`, `meanB2`, `meanRest`, `coefB2`, `fluctB2`;
  `meanFam_split`, `leadG_K`, `leadG_shift1`, `lead_shift3`, `hbar_split`, `hbar_shift1`,
  `hbar_eta`, `meanB2_split`, `coefB2_late`, `coefB2_JQ`, `meanRest_JQ`, `fluct_JE`,
  **`ringLateB2_of_parts (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1/2) meanFam)
  (hR : WordsW (3/2) remFam0) : RingLateB2`**.
* The only block-specific leaf: `WordsW (3/2) remFam0` (the remainder `R₀ = S - a₀G` is smooth,
  `q`-independent, and `K^ℓ∂_η^bR₀` has size `s^{-(b+3)/2}`: `LateMeanRemainder` with `N = 0`,
  source 447-459), task `PartII-a:R02/10/1`, theorem
  `remWords32_of (h : LateIngredients) (hS : MeanSmoothQ) (hH : HeatWords) : WordsW (3 / 2) remFam0`
  in `Short/PartII-a/Calc/BlockB2/RemWords.lean`.
* Unconditional target (`PartII-a:R02/10`, `Tasks/R02/BlockB2.lean`):
  `ringLateB2_of h = Jet.B2.ringLateB2_of_parts jetToolkit (fluctWords_of h) (meanWords_of …)
  (remWords32_of h (meanSmoothQ_of h) (heatWords_of h.heat jetToolkit.iterLin))`, with the leaves
  `PartII-a:R02/8/15-21` of `Calc/JetClass.lean` and `Calc/BaseJets.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188

/-! ### Pointwise calculus of `K` -/

/-- `K` is determined by the germ of the function. -/
theorem bB2_ageOperator_congr {f g : ProfilePoint → ℝ} {y : ProfilePoint} (h : f =ᶠ[𝓝 y] g) :
    ageOperator f y = ageOperator g y := by
  unfold ageOperator partialEta partialAge
  rw [h.fderiv_eq]

/-- Leibniz rule for `K = η∂_η + 2s∂_s` at a point of differentiability. -/
theorem bB2_ageOperator_mul {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    ageOperator (fun z => f z * g z) y = ageOperator f y * g y + f y * ageOperator g y := by
  unfold ageOperator partialEta partialAge
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `K (a f) = a K f`. -/
theorem bB2_ageOperator_const_mul {f : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (a : ℝ) :
    ageOperator (fun z => a * f z) y = a * ageOperator f y := by
  unfold ageOperator partialEta partialAge
  rw [fderiv_const_mul hf a]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `∂_η (a f) = a ∂_η f`. -/
theorem bB2_partialEta_const_mul {f : ProfilePoint → ℝ} {y : ProfilePoint}
    (hf : DifferentiableAt ℝ f y) (a : ℝ) :
    partialEta (fun z => a * f z) y = a * partialEta f y := by
  unfold partialEta
  rw [fderiv_const_mul hf a]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### The heat identity on the explicit profiles `lhP ν j = ∂_η^j G_{νs}` -/

/-- Heat identity (source 1267): `K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}` for `s > 0`. -/
theorem bB2_K_lhP (ν : ℝ) (j : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ageOperator (lhP ν j) y = -((j : ℝ) + 1) * lhP ν j y := by
  have hy0 : y.2.2 ≠ 0 := hy.ne'
  unfold ageOperator
  rw [lhPartialEta ν j hy, lhPartialAge ν j hy]
  field_simp
  ring

/-- `(1-K) ∂_η^j G_{νs} = (j+2) ∂_η^j G_{νs}` for `s > 0`. -/
theorem bB2_ageDefect_lhP (ν : ℝ) (j : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ageDefect (lhP ν j) y = ((j : ℝ) + 2) * lhP ν j y := by
  unfold ageDefect
  rw [bB2_K_lhP ν j hy]
  ring

/-- **`K`-degree `-3` of the leading mean of `B₂`** (source 1281-1283): `(K+3)(G ∂_ηG) = 0` for
`s > 0`, by the Leibniz rule and `KG = -G`, `K∂_ηG = -2∂_ηG`. -/
theorem bB2_K3_GG (ν : ℝ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ageShift 3 (fun z => lhP ν 0 z * lhP ν 1 z) y = 0 := by
  unfold ageShift
  rw [bB2_ageOperator_mul (lhDiff ν 0 hy) (lhDiff ν 1 hy), bB2_K_lhP ν 0 hy, bB2_K_lhP ν 1 hy]
  push_cast
  ring

/-- `(K+1)(1-K)G = 0` for `s > 0` (`(1-K)G = 2G` near the point, `(K+1)G = 0`). -/
theorem bB2_Kp1_ageDefect_G (ν : ℝ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    ageShift 1 (ageDefect (lhP ν 0)) y = 0 := by
  have hev : ageDefect (lhP ν 0) =ᶠ[𝓝 y] fun z => 2 * lhP ν 0 z :=
    Filter.eventuallyEq_of_mem (lhMemNhds hy) (by
      intro z hz
      have hz' : 0 < z.2.2 := hz
      rw [bB2_ageDefect_lhP ν 0 hz']
      push_cast
      ring)
  unfold ageShift
  rw [bB2_ageOperator_congr hev, hev.eq_of_nhds, bB2_ageOperator_const_mul (lhDiff ν 0 hy),
    bB2_K_lhP ν 0 hy]
  push_cast
  ring

end UnforcedLeray.Short.PartIIa

namespace UnforcedLeray.Short.PartIIa.Jet.B2

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanCoeff)

/-! ### Algebra of `LateEq` -/

theorem leq_add {F F' G G' : Fam} (h₁ : LateEq F F') (h₂ : LateEq G G') :
    LateEq (F + G) (F' + G') := by
  intro ν c hν hc tr htr x hx
  show F ν c tr x + G ν c tr x = F' ν c tr x + G' ν c tr x
  rw [h₁ ν c hν hc tr htr hx, h₂ ν c hν hc tr htr hx]

theorem leq_sub {F F' G G' : Fam} (h₁ : LateEq F F') (h₂ : LateEq G G') :
    LateEq (F - G) (F' - G') := by
  intro ν c hν hc tr htr x hx
  show F ν c tr x - G ν c tr x = F' ν c tr x - G' ν c tr x
  rw [h₁ ν c hν hc tr htr hx, h₂ ν c hν hc tr htr hx]

theorem leq_mul {F F' G G' : Fam} (h₁ : LateEq F F') (h₂ : LateEq G G') :
    LateEq (F * G) (F' * G') := by
  intro ν c hν hc tr htr x hx
  show F ν c tr x * G ν c tr x = F' ν c tr x * G' ν c tr x
  rw [h₁ ν c hν hc tr htr hx, h₂ ν c hν hc tr htr hx]

theorem leq_neg {F F' : Fam} (h : LateEq F F') : LateEq (-F) (-F') := by
  intro ν c hν hc tr htr x hx
  show -F ν c tr x = -F' ν c tr x
  rw [h ν c hν hc tr htr hx]

theorem leq_smul (k : ℝ) {F F' : Fam} (h : LateEq F F') : LateEq (k • F) (k • F') := by
  intro ν c hν hc tr htr x hx
  show k * F ν c tr x = k * F' ν c tr x
  rw [h ν c hν hc tr htr hx]

/-- `(K + k)` respects `LateEq`. -/
theorem shift_congr (hT : JetToolkit) {F G : Fam} (h : LateEq F G) (k : ℝ) :
    LateEq (famShift k F) (famShift k G) := by
  rw [famShift_eq, famShift_eq]
  exact leq_add (hT.eqOps F G h).1 (leq_smul k h)

/-- `(K + k)` is additive on smooth families. -/
theorem shift_add (hT : JetToolkit) {F G : Fam} (hF : JSmooth F) (hG : JSmooth G) (k : ℝ) :
    LateEq (famShift k (F + G)) (famShift k F + famShift k G) := by
  rw [famShift_eq, famShift_eq, famShift_eq]
  refine (leq_add (hT.linOps F G hF hG 0).1 (LateEq.refl _)).trans (LateEq.of_eq ?_)
  rw [smul_add]
  abel

/-- `(K + k)` commutes with real scalars on smooth families. -/
theorem shift_smul (hT : JetToolkit) {F : Fam} (hF : JSmooth F) (a k : ℝ) :
    LateEq (famShift k (a • F)) (a • famShift k F) := by
  rw [famShift_eq, famShift_eq]
  refine (leq_add (hT.linOps F F hF hF a).2.2.2.1 (LateEq.refl _)).trans (LateEq.of_eq ?_)
  rw [smul_add, smul_comm]

/-- `∂_η` respects `LateEq`, is additive and commutes with real scalars on smooth families. -/
theorem eta_add_smul (hT : JetToolkit) {F G : Fam} (hF : JSmooth F) (hG : JSmooth G) (a : ℝ) :
    LateEq (famEta (a • F + G)) (a • famEta F + famEta G) :=
  ((hT.linOps (a • F) G ((hT.smooth F G hF hG).2.2.1 a) hG 0).2.1).trans
    (leq_add (hT.linOps F G hF hG a).2.2.2.2.1 (LateEq.refl _))

/-! ### The families of the block -/

/-- The leading mean `a₀ G_{νs}` (`sct:expansion`, `N = 0`). -/
def leadG : Fam := fun ν _ tr x => meanCoeff tr 0 * heatProfile ν x

/-- `\bar v₁ = -S_η` (line 400). -/
def v1bar : Fam := -famEta meanFam

/-- `\bar H = (1-K)S`. -/
def hbar : Fam := meanFam - famK meanFam

/-- `h₁ = (1-K)R₀`, so that `\bar H = 2a₀G + h₁` for `s > 0`. -/
def h1 : Fam := remFam0 - famK remFam0

/-- The leading mean of `B₂` divided by `4`: `a₀G · ∂_η(a₀G)` (`= a₀²G∂_ηG`, line 1282). -/
def lead : Fam := leadG * famEta leadG

/-- The mean part `M₂ = -\bar v₁(K+1)\bar H + \bar H\bar H_η` of `B₂`. -/
def meanB2 : Fam := -(v1bar * famShift 1 hbar) + hbar * famEta hbar

/-- The rest `M_r` of the mean part, `M₂ = 4a₀²G∂_ηG + M_r`. -/
def meanRest : Fam :=
  -(v1bar * famShift 1 h1) + ((2 : ℝ) • leadG) * famEta h1 +
    h1 * ((2 : ℝ) • famEta leadG + famEta h1)

/-- The coefficient `B₂` of the train (`B0188.coeffB₂`). -/
def coefB2 : Fam := coefFam fun ν ψ _ => coeffB₂ ν ψ

/-- The fluctuation part `B₂ - M₂`. -/
def fluctB2 : Fam := coefB2 - meanB2

/-- `v₁ = -∂_ηψ`, `H = (1-K)ψ`, `v₂ = ∂_qψ` of the train. -/
def v1P : Fam := fun _ _ tr => streamV1 (trainProfile tr.ψ)
def hP : Fam := fun _ _ tr => ageDefect (trainProfile tr.ψ)
def v2P : Fam := fun _ _ tr => streamV2 (trainProfile tr.ψ)

theorem v1P_eq : v1P = -famEta psiFam := rfl
theorem hP_eq : hP = psiFam - famK psiFam := rfl
theorem v2P_eq : v2P = famQ psiFam := rfl

/-- The fluctuation parts `ṽ₁ = -∂_ηψ̃`, `H̃ = (1-K)ψ̃`. -/
def v1t : Fam := -famEta fluctFam
def ht : Fam := fluctFam - famK fluctFam

/-- The explicit fluctuation sum. -/
def fsum : Fam :=
  -(v1t * famShift 1 hP) - v1bar * famShift 1 ht + ht * famEta hP + hbar * famEta ht +
    (2 : ℝ) • famNu (famShift 1 (famQ hP)) - famNu (famShift 1 (famShift 1 v2P))

theorem meanFam_split : meanFam = remFam0 + leadG := by
  funext ν c tr x
  exact meanFam_eq ν c tr x

theorem leadG_eq : leadG = meanFam - remFam0 := by
  rw [meanFam_split]
  abel

/-! ### Heat calculus of the leading mean -/

theorem heatProfile_diff (ν : ℝ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    DifferentiableAt ℝ (heatProfile ν) y := by
  rw [lhProfileEq]
  exact lhDiff ν 0 hy

/-- `K(a₀G) = -a₀G` (heat identity, `j = 0`). -/
theorem leadG_K : LateEq (famK leadG) (-leadG) := by
  intro ν c _ _ tr _ y hy
  have hy' : 0 < y.2.2 := hy
  show ageOperator (fun x => meanCoeff tr 0 * heatProfile ν x) y =
    -(meanCoeff tr 0 * heatProfile ν y)
  rw [bB2_ageOperator_const_mul (heatProfile_diff ν hy'), lhProfileEq, bB2_K_lhP ν 0 hy']
  push_cast
  ring

/-- `(K+1)(a₀G) = 0`. -/
theorem leadG_shift1 : LateEq (famShift 1 leadG) 0 := by
  intro ν c hν hc tr htr y hy
  have h := leadG_K ν c hν hc tr htr hy
  show ageOperator (leadG ν c tr) y + 1 * leadG ν c tr y = 0
  have h' : ageOperator (leadG ν c tr) y = -leadG ν c tr y := h
  rw [h']
  ring

/-- Near a point with `s > 0`, `a₀G · ∂_η(a₀G) = a₀² (G ∂_ηG)`. -/
theorem lead_eventually (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) {y : ProfilePoint}
    (hy : 0 < y.2.2) :
    lead ν c tr =ᶠ[𝓝 y] fun z => (meanCoeff tr 0 * meanCoeff tr 0) * (lhP ν 0 z * lhP ν 1 z) := by
  refine Filter.eventuallyEq_of_mem (lhMemNhds hy) ?_
  intro z hz
  have hz' : 0 < z.2.2 := hz
  show meanCoeff tr 0 * heatProfile ν z *
      partialEta (fun x => meanCoeff tr 0 * heatProfile ν x) z = _
  rw [bB2_partialEta_const_mul (heatProfile_diff ν hz'), lhProfileEq, lhPartialEta ν 0 hz']
  ring

/-- **Mean cancellation for `B₂`** (source 1281-1283): `(K+3)(a₀²G∂_ηG) = 0` for `s > 0`. -/
theorem lead_shift3 : LateEq (famShift 3 lead) 0 := by
  intro ν c _ _ tr _ y hy
  have hy' : 0 < y.2.2 := hy
  have hev := lead_eventually ν c tr hy'
  show ageOperator (lead ν c tr) y + 3 * lead ν c tr y = 0
  rw [bB2_ageOperator_congr hev, hev.eq_of_nhds,
    bB2_ageOperator_const_mul (show DifferentiableAt ℝ (fun z => lhP ν 0 z * lhP ν 1 z) y from
      (lhDiff ν 0 hy').mul (lhDiff ν 1 hy'))]
  have h := bB2_K3_GG ν hy'
  unfold ageShift at h
  beta_reduce at h ⊢
  linear_combination (meanCoeff tr 0 * meanCoeff tr 0) * h

/-! ### Sizes of the mean objects -/

theorem meanFam_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n (1 / 2) meanFam :=
  JQ_of_words hT.jc hT.wordW n _ _ hM

theorem remFam0_JQ (hT : JetToolkit) (hR : WordsW (3 / 2) remFam0) (n : ℕ) :
    JQ n (3 / 2) remFam0 :=
  JQ_of_words hT.jc hT.wordW n _ _ hR

theorem leadG_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (hR : WordsW (3 / 2) remFam0)
    (n : ℕ) : JQ n (1 / 2) leadG := by
  rw [leadG_eq]
  exact hT.jc.qsub (meanFam_JQ hT hM n) (hT.jc.qmono (by norm_num) (remFam0_JQ hT hR n))

theorem v1bar_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (n : ℕ) : JQ n 1 v1bar :=
  hT.jc.qneg ((meanFam_JQ hT hM (n + 1)).eta.cast (by norm_num))

theorem hbar_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (n : ℕ) : JQ n (1 / 2) hbar :=
  hT.jc.qsub (meanFam_JQ hT hM n) (meanFam_JQ hT hM (n + 1)).k

theorem h1_JQ (hT : JetToolkit) (hR : WordsW (3 / 2) remFam0) (n : ℕ) : JQ n (3 / 2) h1 :=
  hT.jc.qsub (remFam0_JQ hT hR n) (remFam0_JQ hT hR (n + 1)).k

theorem lead_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (hR : WordsW (3 / 2) remFam0)
    (n : ℕ) : JQ n (3 / 2) lead :=
  (hT.jc.qmul (by norm_num) (by norm_num) (leadG_JQ hT hM hR n)
    (leadG_JQ hT hM hR (n + 1)).eta).cast (by norm_num)

/-- **The rest of the mean part has size `s^{-5/2}`** (`(1 + 3/2)`, `(1/2 + 2)`, `(3/2 + 1)`). -/
theorem meanRest_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (hR : WordsW (3 / 2) remFam0)
    (n : ℕ) : JQ n (5 / 2) meanRest := by
  have t1 : JQ n (5 / 2) (-(v1bar * famShift 1 h1)) :=
    hT.jc.qneg ((hT.jc.qmul (by norm_num) (by norm_num) (v1bar_JQ hT hM n)
      (hT.jc.qshift 1 (h1_JQ hT hR (n + 1)))).cast (by norm_num))
  have t2 : JQ n (5 / 2) (((2 : ℝ) • leadG) * famEta h1) :=
    (hT.jc.qmul (by norm_num) (by norm_num) (hT.jc.qsmul 2 (leadG_JQ hT hM hR n))
      (h1_JQ hT hR (n + 1)).eta).cast (by norm_num)
  have hs : JQ n 1 ((2 : ℝ) • famEta leadG + famEta h1) :=
    hT.jc.qadd (hT.jc.qsmul 2 ((leadG_JQ hT hM hR (n + 1)).eta.cast (by norm_num)))
      (hT.jc.qmono (by norm_num) (h1_JQ hT hR (n + 1)).eta)
  have t3 : JQ n (5 / 2) (h1 * ((2 : ℝ) • famEta leadG + famEta h1)) :=
    (hT.jc.qmul (by norm_num) (by norm_num) (h1_JQ hT hR n) hs).cast (by norm_num)
  exact hT.jc.qadd (hT.jc.qadd t1 t2) t3

theorem meanB2_JQ (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n (3 / 2) meanB2 := by
  have t1 : JQ n (3 / 2) (-(v1bar * famShift 1 hbar)) :=
    hT.jc.qneg ((hT.jc.qmul (by norm_num) (by norm_num) (v1bar_JQ hT hM n)
      (hT.jc.qshift 1 (hbar_JQ hT hM (n + 1)))).cast (by norm_num))
  have t2 : JQ n (3 / 2) (hbar * famEta hbar) :=
    (hT.jc.qmul (by norm_num) (by norm_num) (hbar_JQ hT hM n)
      (hbar_JQ hT hM (n + 1)).eta).cast (by norm_num)
  exact hT.jc.qadd t1 t2

/-! ### The mean part: `\bar H = 2a₀G + h₁` and the cancellation -/

theorem hbar_split (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam)
    (hR : WordsW (3 / 2) remFam0) : LateEq hbar ((2 : ℝ) • leadG + h1) := by
  have hL := (leadG_JQ hT hM hR 0).smooth
  have hK : LateEq (famK meanFam) (famK remFam0 + -leadG) := by
    rw [meanFam_split]
    exact (hT.linOps remFam0 leadG hR.1 hL 0).1.trans (leq_add (LateEq.refl _) leadG_K)
  refine (leq_sub (LateEq.of_eq meanFam_split) hK).trans (LateEq.of_eq ?_)
  unfold h1
  rw [two_smul]
  abel

theorem hbar_shift1 (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam)
    (hR : WordsW (3 / 2) remFam0) : LateEq (famShift 1 hbar) (famShift 1 h1) := by
  have hL := (leadG_JQ hT hM hR 0).smooth
  have hL2 := (hT.jc.qsmul 2 (leadG_JQ hT hM hR 0)).smooth
  have hh := (h1_JQ hT hR 0).smooth
  refine (shift_congr hT (hbar_split hT hM hR) 1).trans <| (shift_add hT hL2 hh 1).trans <|
    (leq_add (shift_smul hT hL 2 1) (LateEq.refl _)).trans <|
    (leq_add (leq_smul 2 leadG_shift1) (LateEq.refl _)).trans (LateEq.of_eq ?_)
  rw [smul_zero, zero_add]

theorem hbar_eta (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam) (hR : WordsW (3 / 2) remFam0) :
    LateEq (famEta hbar) ((2 : ℝ) • famEta leadG + famEta h1) :=
  (hT.eqOps _ _ (hbar_split hT hM hR)).2.1.trans
    (eta_add_smul hT (leadG_JQ hT hM hR 0).smooth (h1_JQ hT hR 0).smooth 2)

/-- **The mean part of `B₂`**: `M₂ = 4a₀²G∂_ηG + M_r` for `s > 0` (source 1281-1282). -/
theorem meanB2_split (hT : JetToolkit) (hM : WordsW (1 / 2) meanFam)
    (hR : WordsW (3 / 2) remFam0) : LateEq meanB2 ((4 : ℝ) • lead + meanRest) := by
  refine (leq_add (leq_neg (leq_mul (LateEq.refl v1bar) (hbar_shift1 hT hM hR)))
    (leq_mul (hbar_split hT hM hR) (hbar_eta hT hM hR))).trans (LateEq.of_eq ?_)
  funext ν c tr x
  simp only [lead, meanRest, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The coefficient and its fluctuation part -/

theorem psiFam_JQ (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n (1 / 2) psiFam :=
  (baseJets_of hT.jc hT.wordE hT.wordW hF hM n).2.2.2

theorem fluctFam_JE (hT : JetToolkit) (hF : FluctWords) (n : ℕ) : JE n fluctFam :=
  JE_of_words hT.wordE n _ hF.1

theorem v1P_JQ (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n 1 v1P := by
  rw [v1P_eq]
  exact hT.jc.qneg ((psiFam_JQ hT hF hM (n + 1)).eta.cast (by norm_num))

theorem hP_JQ (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n (1 / 2) hP := by
  rw [hP_eq]
  exact hT.jc.qsub (psiFam_JQ hT hF hM n) (psiFam_JQ hT hF hM (n + 1)).k

theorem v2P_JE (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JE n v2P := by
  rw [v2P_eq]
  exact (psiFam_JQ hT hF hM (n + 1)).q

theorem v1t_JE (hT : JetToolkit) (hF : FluctWords) (n : ℕ) : JE n v1t :=
  hT.jc.eneg (fluctFam_JE hT hF (n + 1)).eta

theorem ht_JE (hT : JetToolkit) (hF : FluctWords) (n : ℕ) : JE n ht :=
  hT.jc.esub (fluctFam_JE hT hF n) (fluctFam_JE hT hF (n + 1)).k

/-- `B₂ = -v₁(K+1)H + HH_η + 2ν(K+1)H_q - ν(K+1)²v₂` as a combination of jets (line 1256). -/
theorem coefB2_late :
    LateEq (-(v1P * famShift 1 hP) + hP * famEta hP + (2 : ℝ) • famNu (famShift 1 (famQ hP)) -
      famNu (famShift 1 (famShift 1 v2P))) coefB2 := by
  intro ν c _ _ tr _ x _
  show -(v1P ν c tr x * famShift 1 hP ν c tr x) + hP ν c tr x * famEta hP ν c tr x +
      2 * (ν * famShift 1 (famQ hP) ν c tr x) - ν * famShift 1 (famShift 1 v2P) ν c tr x =
    coeffB₂ ν (trainProfile tr.ψ) x
  simp only [coeffB₂, v1P, hP, v2P, famQ, famEta, famShift]
  ring

/-- **Generic sizes of `B₂`**: `B₂ ∈ JQ (3/2)` at every depth. -/
theorem coefB2_JQ (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JQ n (3 / 2) coefB2 := by
  have t1 : JQ n (3 / 2) (-(v1P * famShift 1 hP)) :=
    hT.jc.qneg ((hT.jc.qmul (by norm_num) (by norm_num) (v1P_JQ hT hF hM n)
      (hT.jc.qshift 1 (hP_JQ hT hF hM (n + 1)))).cast (by norm_num))
  have t2 : JQ n (3 / 2) (hP * famEta hP) :=
    (hT.jc.qmul (by norm_num) (by norm_num) (hP_JQ hT hF hM n)
      (hP_JQ hT hF hM (n + 1)).eta).cast (by norm_num)
  have t3 : JQ n (3 / 2) ((2 : ℝ) • famNu (famShift 1 (famQ hP))) :=
    hT.jc.qofE _ (hT.jc.esmul 2 (hT.jc.enu (hT.jc.eshift 1
      (hP_JQ hT hF hM (n + 2)).q)))
  have t4 : JQ n (3 / 2) (famNu (famShift 1 (famShift 1 v2P))) :=
    hT.jc.qofE _ (hT.jc.enu (hT.jc.eshift 1 (hT.jc.eshift 1 (v2P_JE hT hF hM (n + 2)))))
  exact hT.jc.qcongr coefB2_late (hT.jc.qsub (hT.jc.qadd (hT.jc.qadd t1 t2) t3) t4)

theorem v1P_split (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) :
    LateEq v1P (v1bar + v1t) := by
  rw [v1P_eq, psiFam_eq]
  refine (leq_neg (hT.linOps _ _ hM.1 hF.1.1 0).2.1).trans (LateEq.of_eq ?_)
  rw [neg_add]
  rfl

theorem hP_split (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) :
    LateEq hP (hbar + ht) := by
  rw [hP_eq, psiFam_eq]
  refine (leq_sub (LateEq.refl _) (hT.linOps _ _ hM.1 hF.1.1 0).1).trans (LateEq.of_eq ?_)
  unfold hbar ht
  abel

theorem hP_shift_split (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) :
    LateEq (famShift 1 hP) (famShift 1 hbar + famShift 1 ht) :=
  (shift_congr hT (hP_split hT hF hM) 1).trans
    (shift_add hT (hbar_JQ hT hM 0).smooth (ht_JE hT hF 0).smooth 1)

theorem hP_eta_split (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) :
    LateEq (famEta hP) (famEta hbar + famEta ht) :=
  (hT.eqOps _ _ (hP_split hT hF hM)).2.1.trans
    (hT.linOps _ _ (hbar_JQ hT hM 0).smooth (ht_JE hT hF 0).smooth 0).2.1

/-- `B₂ - M₂` is the explicit fluctuation sum for `s > 0`. -/
theorem fluct_eq (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) :
    LateEq fluctB2 fsum := by
  intro ν c hν hc tr htr x hx
  have e0 : coefB2 ν c tr x = -(v1P ν c tr x * famShift 1 hP ν c tr x) +
      hP ν c tr x * famEta hP ν c tr x + 2 * famNu (famShift 1 (famQ hP)) ν c tr x -
      famNu (famShift 1 (famShift 1 v2P)) ν c tr x :=
    (coefB2_late ν c hν hc tr htr hx).symm
  have e1 : v1P ν c tr x = v1bar ν c tr x + v1t ν c tr x := v1P_split hT hF hM ν c hν hc tr htr hx
  have e2 : hP ν c tr x = hbar ν c tr x + ht ν c tr x := hP_split hT hF hM ν c hν hc tr htr hx
  have e3 : famShift 1 hP ν c tr x = famShift 1 hbar ν c tr x + famShift 1 ht ν c tr x :=
    hP_shift_split hT hF hM ν c hν hc tr htr hx
  have e4 : famEta hP ν c tr x = famEta hbar ν c tr x + famEta ht ν c tr x :=
    hP_eta_split hT hF hM ν c hν hc tr htr hx
  show coefB2 ν c tr x - (-(v1bar ν c tr x * famShift 1 hbar ν c tr x) +
      hbar ν c tr x * famEta hbar ν c tr x) =
    -(v1t ν c tr x * famShift 1 hP ν c tr x) - v1bar ν c tr x * famShift 1 ht ν c tr x +
      ht ν c tr x * famEta hP ν c tr x + hbar ν c tr x * famEta ht ν c tr x +
      2 * famNu (famShift 1 (famQ hP)) ν c tr x - famNu (famShift 1 (famShift 1 v2P)) ν c tr x
  rw [e0]
  linear_combination (-(famShift 1 hP ν c tr x)) * e1 + (famEta hP ν c tr x) * e2 -
    (v1bar ν c tr x) * e3 + (hbar ν c tr x) * e4

theorem fsum_JE (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JE n fsum := by
  have s1 : JE n (v1t * famShift 1 hP) :=
    hT.jc.emulQ (v1t_JE hT hF n)
      (hT.jc.qmono (by norm_num) (hT.jc.qshift 1 (hP_JQ hT hF hM (n + 1))))
  have s2 : JE n (v1bar * famShift 1 ht) :=
    hT.jc.qmulE (hT.jc.qmono (by norm_num) (v1bar_JQ hT hM n))
      (hT.jc.eshift 1 (ht_JE hT hF (n + 1)))
  have s3 : JE n (ht * famEta hP) :=
    hT.jc.emulQ (ht_JE hT hF n) (hT.jc.qmono (by norm_num) (hP_JQ hT hF hM (n + 1)).eta)
  have s4 : JE n (hbar * famEta ht) :=
    hT.jc.qmulE (hT.jc.qmono (by norm_num) (hbar_JQ hT hM n)) (ht_JE hT hF (n + 1)).eta
  have s5 : JE n ((2 : ℝ) • famNu (famShift 1 (famQ hP))) :=
    hT.jc.esmul 2 (hT.jc.enu (hT.jc.eshift 1 (hP_JQ hT hF hM (n + 2)).q))
  have s6 : JE n (famNu (famShift 1 (famShift 1 v2P))) :=
    hT.jc.enu (hT.jc.eshift 1 (hT.jc.eshift 1 (v2P_JE hT hF hM (n + 2))))
  exact hT.jc.esub (hT.jc.eadd (hT.jc.eadd (hT.jc.eadd
    (hT.jc.esub (hT.jc.eneg s1) s2) s3) s4) s5) s6

/-- **The fluctuation part of `B₂` is exponentially small** at every depth. -/
theorem fluct_JE (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam) (n : ℕ) :
    JE n fluctB2 :=
  hT.jc.econgr (fluct_eq hT hF hM).symm (fsum_JE hT hF hM n)

/-! ### The block -/

/-- **`(K+3)B₂` has size `s^{-5/2}`** (source 1277, 1281-1283). -/
theorem coefB2_shift3 (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam)
    (hR : WordsW (3 / 2) remFam0) : WW (5 / 2) (famShift 3 coefB2) := by
  have hsplit : coefB2 = meanB2 + fluctB2 := by
    unfold fluctB2
    abel
  have hmB := (meanB2_JQ hT hM 0).smooth
  have hfl := (fluct_JE hT hF hM 0).smooth
  have hlead := (lead_JQ hT hM hR 0).smooth
  have hlead4 := (hT.jc.qsmul 4 (lead_JQ hT hM hR 0)).smooth
  have hrest := (meanRest_JQ hT hM hR 0).smooth
  have chain : LateEq (famShift 3 coefB2) (famShift 3 meanRest + famShift 3 fluctB2) := by
    refine (LateEq.of_eq (congrArg (famShift 3) hsplit)).trans <|
      (shift_add hT hmB hfl 3).trans <|
      (leq_add (shift_congr hT (meanB2_split hT hM hR) 3) (LateEq.refl _)).trans <|
      (leq_add (shift_add hT hlead4 hrest 3) (LateEq.refl _)).trans <|
      (leq_add (leq_add (shift_smul hT hlead 4 3) (LateEq.refl _)) (LateEq.refl _)).trans <|
      (leq_add (leq_add (leq_smul 4 lead_shift3) (LateEq.refl _)) (LateEq.refl _)).trans
        (LateEq.of_eq ?_)
    rw [smul_zero, zero_add]
  have hW : WW (5 / 2) (famShift 3 meanRest + famShift 3 fluctB2) :=
    (hT.jc.qshift 3 (meanRest_JQ hT hM hR 1)).ww.add
      (hT.jc.qofE (5 / 2) (hT.jc.eshift 3 (fluct_JE hT hF hM 1))).ww
  exact WW.congr chain.symm hW

/-- **`PartII-a:R02/10`, conditional on the jet toolkit and the word statements**: the `B₂` block
of the late table (sizes `s^{-3/2}`, `s^{-2}`, `s^{-5/2}`, `∂_q` exponentially small). -/
theorem ringLateB2_of_parts (hT : JetToolkit) (hF : FluctWords) (hM : WordsW (1 / 2) meanFam)
    (hR : WordsW (3 / 2) remFam0) : RingLateB2 := by
  have hc := coefB2_JQ hT hF hM 1
  have h2 : WW 2 (famEta coefB2) := (hc.eta.cast (by norm_num : (3 : ℝ) / 2 + 1 / 2 = 2)).ww
  exact lateStmt_grpW (fun ν ψ _ => coeffB₂ ν ψ) (3 / 2) 2 (5 / 2) hc.ww h2
    (coefB2_shift3 hT hF hM hR) hc.q.we

end UnforcedLeray.Short.PartIIa.Jet.B2
