import UnforcedLeray.Short.PartIIa.Calc.JetClass

/-!
# Part II-a, jet-class calculus: weighted word reduction (`WordShiftW`)

Target: `UnforcedLeray.Short.PartIIa.Jet.wordShiftW_of : WordShiftW` (`Calc/JetClass.lean`).

Source of record: `the November 2 reference manuscript`, lines 397-404 (the mean is
`q`-independent), 447-459 and 1267-1272 (word reduction `∂_η K = (K+1) ∂_η`).

Proof route, on the open set `{s > 0}`, for `f` smooth there:
* `∂_η^b (K f) = K (∂_η^b f) + b ∂_η^b f` (`IterCalcComm`, third clause), and linearity of
  `K^ℓ` (`IterCalcLin`, second clause), give `K^ℓ ∂_η^b (K f) = K^{ℓ+1} ∂_η^b f + b K^ℓ ∂_η^b f`;
* `∂_η^b (∂_η f) = ∂_η^{b+1} f` is definitional, which gives the `∂_η`-branch with size shifted by
  `1/2`;
* `∂_q (K f) = K (∂_q f)` and `∂_q (∂_η f) = ∂_η (∂_q f)` (`IterCalcComm`), together with
  `∂_q f = 0` on `{s > 0}` and the locality of `K, ∂_η` (`IterCalcLin`, first clause), give the
  `q`-independence of the two families.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- `K = ageOperator` preserves smoothness on `{s > 0}`. -/
theorem wsw_K_smooth {G : ProfilePoint → ℝ}
    (hG : ContDiffOn ℝ ∞ G {x : ProfilePoint | 0 < x.2.2}) :
    ContDiffOn ℝ ∞ (ageOperator G) {x : ProfilePoint | 0 < x.2.2} := by
  have hE := contDiffOn_fderiv_apply hG eηDir
  have hA := contDiffOn_fderiv_apply hG esDir
  have h1 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => x.2.1) {x : ProfilePoint | 0 < x.2.2} :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) {x : ProfilePoint | 0 < x.2.2} :=
    contDiffOn_const.mul (contDiff_snd.comp contDiff_snd).contDiffOn
  show ContDiffOn ℝ ∞ (fun x : ProfilePoint =>
    x.2.1 * fderiv ℝ G x eηDir + 2 * x.2.2 * fderiv ℝ G x esDir) {x : ProfilePoint | 0 < x.2.2}
  exact (h1.mul hE).add (h2.mul hA)

/-- The weighted word identity: `K^ℓ ∂_η^b (K f) = K^{ℓ+1} ∂_η^b f + b K^ℓ ∂_η^b f` on `{s > 0}`. -/
theorem wsw_K_word {f : ProfilePoint → ℝ} (hC : IterCalcComm) (hL : IterCalcLin)
    (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2}) (ℓ b : ℕ) :
    EqOn (ageOperator^[ℓ] (partialEta^[b] (ageOperator f)))
      (fun x => ageOperator^[ℓ + 1] (partialEta^[b] f) x +
        (b : ℝ) * (ageOperator^[ℓ] (partialEta^[b] f)) x)
      {x : ProfilePoint | 0 < x.2.2} := by
  have hQ : ContDiffOn ℝ ∞ (partialEta^[b] f) {x : ProfilePoint | 0 < x.2.2} :=
    contDiffOn_partialEta_iter hf b
  have hKQ : ContDiffOn ℝ ∞ (ageOperator (partialEta^[b] f)) {x : ProfilePoint | 0 < x.2.2} :=
    wsw_K_smooth hQ
  have s3 : EqOn (partialEta^[b] (ageOperator f))
      (fun x => ageOperator (partialEta^[b] f) x + (b : ℝ) * (partialEta^[b] f) x)
      {x : ProfilePoint | 0 < x.2.2} := (hC f hf b 0).2.2
  have s4 : EqOn (ageOperator^[ℓ] (partialEta^[b] (ageOperator f)))
      (ageOperator^[ℓ] (fun x => ageOperator (partialEta^[b] f) x +
        (b : ℝ) * (partialEta^[b] f) x))
      {x : ProfilePoint | 0 < x.2.2} := hL.1 _ _ s3 ℓ 0 0
  have s5 : EqOn (ageOperator^[ℓ] (fun x => ageOperator (partialEta^[b] f) x +
        (b : ℝ) * (partialEta^[b] f) x))
      (fun x => (ageOperator^[ℓ] (ageOperator (partialEta^[b] f))) x +
        (b : ℝ) * (ageOperator^[ℓ] (partialEta^[b] f)) x)
      {x : ProfilePoint | 0 < x.2.2} :=
    hL.2.1 (ageOperator (partialEta^[b] f)) (partialEta^[b] f) hKQ hQ (b : ℝ) ℓ 0 0
  intro x hx
  exact (s4 hx).trans (s5 hx)

/-- `∂_η` of the zero function is zero. -/
theorem wsw_partialEta_zero (x : ProfilePoint) : partialEta (0 : ProfilePoint → ℝ) x = 0 := by
  show fderiv ℝ (fun _ : ProfilePoint => (0 : ℝ)) x eηDir = 0
  simp

/-- `K` of the zero function is zero. -/
theorem wsw_K_zero (x : ProfilePoint) : ageOperator (0 : ProfilePoint → ℝ) x = 0 := by
  show x.2.1 * partialEta (0 : ProfilePoint → ℝ) x + 2 * x.2.2 * partialAge (0 : ProfilePoint → ℝ) x = 0
  rw [wsw_partialEta_zero]
  have hA : partialAge (0 : ProfilePoint → ℝ) x = 0 := by
    show fderiv ℝ (fun _ : ProfilePoint => (0 : ℝ)) x esDir = 0
    simp
  rw [hA]
  ring

/-- `∂_q f = 0` on `{s > 0}` gives `∂_q (∂_η f) = 0` there. -/
theorem wsw_qeta_zero (hC : IterCalcComm) (hL : IterCalcLin) {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2})
    (hq : EqOn (partialQ f) 0 {x : ProfilePoint | 0 < x.2.2}) :
    EqOn (partialQ (partialEta f)) 0 {x : ProfilePoint | 0 < x.2.2} := by
  intro x hx
  have e1 : partialQ (partialEta f) x = partialEta (partialQ f) x := (hC f hf 0 1).1 hx
  have e2 : partialEta (partialQ f) x = partialEta (0 : ProfilePoint → ℝ) x :=
    hL.1 (partialQ f) 0 hq 0 1 0 hx
  exact e1.trans (e2.trans (wsw_partialEta_zero x))

/-- `∂_q f = 0` on `{s > 0}` gives `∂_q (K f) = 0` there. -/
theorem wsw_qk_zero (hC : IterCalcComm) (hL : IterCalcLin) {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2})
    (hq : EqOn (partialQ f) 0 {x : ProfilePoint | 0 < x.2.2}) :
    EqOn (partialQ (ageOperator f)) 0 {x : ProfilePoint | 0 < x.2.2} := by
  intro x hx
  have e1 : partialQ (ageOperator f) x = ageOperator (partialQ f) x := (hC f hf 0 1).2.1 hx
  have e2 : ageOperator (partialQ f) x = ageOperator (0 : ProfilePoint → ℝ) x :=
    hL.1 (partialQ f) 0 hq 1 0 0 hx
  exact e1.trans (e2.trans (wsw_K_zero x))

/-- **Word reduction, weighted class.** -/
theorem wordShiftW_of (h1 : SmoothClosure) (hC : IterCalcComm) (hL : IterCalcLin) :
    WordShiftW := by
  intro a F hF
  unfold WordsW at hF
  obtain ⟨hFs, hFq, hFw⟩ := hF
  obtain ⟨_, _, _, _, hK, hEta, _⟩ := h1 F F hFs hFs
  refine ⟨?_, ?_⟩
  · unfold WordsW
    refine ⟨hK, ?_, fun ℓ b => ?_⟩
    · exact fun ν c hν hc tr htr => wsw_qk_zero hC hL (hFs ν c hν hc tr htr) (hFq ν c hν hc tr htr)
    · have hEq : LateEq (wordW (ℓ + 1) b F + (b : ℝ) • wordW ℓ b F) (wordW ℓ b (famK F)) :=
        fun ν c hν hc tr htr => (wsw_K_word hC hL (hFs ν c hν hc tr htr) ℓ b).symm
      exact WW.congr hEq (WW.add (hFw (ℓ + 1) b) (WW.smul (b : ℝ) (hFw ℓ b)))
  · unfold WordsW
    refine ⟨hEta, ?_, fun ℓ b => ?_⟩
    · exact fun ν c hν hc tr htr => wsw_qeta_zero hC hL (hFs ν c hν hc tr htr) (hFq ν c hν hc tr htr)
    · have h := hFw ℓ (b + 1)
      have e : a + 1 / 2 + (b : ℝ) / 2 = a + ((b + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
      rw [e]
      exact h

end UnforcedLeray.Short.PartIIa.Jet
