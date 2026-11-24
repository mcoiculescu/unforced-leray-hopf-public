import UnforcedLeray.Short.PartIIa.Calc.JetClass

/-!
# Part II-a, jet-class calculus: exponential word reduction (`WordShiftE`)

Target: `UnforcedLeray.Short.PartIIa.Jet.wordShiftE_of : WordShiftE` (`Calc/JetClass.lean`).

Source of record: `the November 2 reference manuscript`, lines 439-446 and 1267-1272.

Proof route, on the open set `{s > 0}`, for `f` smooth there, `P = ∂_q^b f`, `Q = ∂_η^a P`:
* `∂_q^b (K f) = K P` (`IterCalcComm`, second clause);
* `∂_η^a (K P) = K Q + a Q` (`IterCalcComm`, third clause);
* `K^ℓ` is linear on smooth functions (`IterCalcLin`, second clause), so
  `K^ℓ ∂_η^a ∂_q^b (K f) = K^{ℓ+1} Q + a K^ℓ Q`;
* `∂_q^b ∂_η f = ∂_η ∂_q^b f` (`IterCalcComm`, first clause) gives the `∂_η` branch;
* `∂_q (∂_q^b f) = ∂_q^{b+1} f` is definitional, giving the `∂_q` branch.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- `K = ageOperator` preserves smoothness on `{s > 0}`. -/
theorem wse_K_smooth {G : ProfilePoint → ℝ}
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

/-- The key word identity: `K^ℓ ∂_η^a ∂_q^b (K f) = K^{ℓ+1} ∂_η^a ∂_q^b f + a K^ℓ ∂_η^a ∂_q^b f`
on `{s > 0}`, for `f` smooth there. -/
theorem wse_K_word {f : ProfilePoint → ℝ} (hC : IterCalcComm) (hL : IterCalcLin)
    (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2}) (ℓ a b : ℕ) :
    EqOn (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (ageOperator f))))
      (fun x => ageOperator^[ℓ + 1] (partialEta^[a] (partialQ^[b] f)) x +
        (a : ℝ) * (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] f))) x)
      {x : ProfilePoint | 0 < x.2.2} := by
  have hP : ContDiffOn ℝ ∞ (partialQ^[b] f) {x : ProfilePoint | 0 < x.2.2} :=
    contDiffOn_partialQ_iter hf b
  have hQ : ContDiffOn ℝ ∞ (partialEta^[a] (partialQ^[b] f))
      {x : ProfilePoint | 0 < x.2.2} :=
    contDiffOn_partialEta_iter hP a
  have hKQ : ContDiffOn ℝ ∞ (ageOperator (partialEta^[a] (partialQ^[b] f)))
      {x : ProfilePoint | 0 < x.2.2} :=
    wse_K_smooth hQ
  have s1 : EqOn (partialQ^[b] (ageOperator f)) (ageOperator (partialQ^[b] f))
      {x : ProfilePoint | 0 < x.2.2} := (hC f hf a b).2.1
  have s2 : EqOn (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (ageOperator f))))
      (ageOperator^[ℓ] (partialEta^[a] (ageOperator (partialQ^[b] f))))
      {x : ProfilePoint | 0 < x.2.2} := hL.1 _ _ s1 ℓ a 0
  have s3 : EqOn (partialEta^[a] (ageOperator (partialQ^[b] f)))
      (fun x => ageOperator (partialEta^[a] (partialQ^[b] f)) x +
        (a : ℝ) * (partialEta^[a] (partialQ^[b] f)) x)
      {x : ProfilePoint | 0 < x.2.2} := (hC (partialQ^[b] f) hP a 0).2.2
  have s4 : EqOn (ageOperator^[ℓ] (partialEta^[a] (ageOperator (partialQ^[b] f))))
      (ageOperator^[ℓ] (fun x => ageOperator (partialEta^[a] (partialQ^[b] f)) x +
        (a : ℝ) * (partialEta^[a] (partialQ^[b] f)) x))
      {x : ProfilePoint | 0 < x.2.2} := hL.1 _ _ s3 ℓ 0 0
  have s5 : EqOn (ageOperator^[ℓ] (fun x => ageOperator (partialEta^[a] (partialQ^[b] f)) x +
        (a : ℝ) * (partialEta^[a] (partialQ^[b] f)) x))
      (fun x => (ageOperator^[ℓ] (ageOperator (partialEta^[a] (partialQ^[b] f)))) x +
        (a : ℝ) * (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] f))) x)
      {x : ProfilePoint | 0 < x.2.2} :=
    hL.2.1 (ageOperator (partialEta^[a] (partialQ^[b] f))) (partialEta^[a] (partialQ^[b] f))
      hKQ hQ (a : ℝ) ℓ 0 0
  intro x hx
  have e1 := s2 hx
  have e2 := s4 hx
  have e3 := s5 hx
  exact e1.trans (e2.trans e3)

/-- The `∂_η` word identity: `K^ℓ ∂_η^a ∂_q^b (∂_η f) = K^ℓ ∂_η^{a+1} ∂_q^b f` on `{s > 0}`. -/
theorem wse_eta_word {f : ProfilePoint → ℝ} (hC : IterCalcComm) (hL : IterCalcLin)
    (hf : ContDiffOn ℝ ∞ f {x : ProfilePoint | 0 < x.2.2}) (ℓ a b : ℕ) :
    EqOn (ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] (partialEta f))))
      (ageOperator^[ℓ] (partialEta^[a + 1] (partialQ^[b] f)))
      {x : ProfilePoint | 0 < x.2.2} := by
  have s1 : EqOn (partialQ^[b] (partialEta f)) (partialEta (partialQ^[b] f))
      {x : ProfilePoint | 0 < x.2.2} := (hC f hf a b).1
  exact hL.1 _ _ s1 ℓ a 0

/-- **Word reduction, exponential class.** -/
theorem wordShiftE_of (h1 : SmoothClosure) (hC : IterCalcComm) (hL : IterCalcLin) :
    WordShiftE := by
  intro F hF
  unfold WordsE at hF
  obtain ⟨hFs, hFw⟩ := hF
  obtain ⟨_, _, _, _, hK, hEta, hQ⟩ := h1 F F hFs hFs
  refine ⟨?_, ?_, ?_⟩
  · unfold WordsE
    refine ⟨hK, fun ℓ a b => ?_⟩
    have hEq : LateEq (wordE (ℓ + 1) a b F + (a : ℝ) • wordE ℓ a b F) (wordE ℓ a b (famK F)) :=
      fun ν c hν hc tr htr => (wse_K_word hC hL (hFs ν c hν hc tr htr) ℓ a b).symm
    exact WE.congr hEq (WE.add (hFw (ℓ + 1) a b) (WE.smul (a : ℝ) (hFw ℓ a b)))
  · unfold WordsE
    refine ⟨hEta, fun ℓ a b => ?_⟩
    have hEq : LateEq (wordE ℓ (a + 1) b F) (wordE ℓ a b (famEta F)) :=
      fun ν c hν hc tr htr => (wse_eta_word hC hL (hFs ν c hν hc tr htr) ℓ a b).symm
    exact WE.congr hEq (hFw ℓ (a + 1) b)
  · unfold WordsE
    refine ⟨hQ, fun ℓ a b => ?_⟩
    exact hFw ℓ a (b + 1)

end UnforcedLeray.Short.PartIIa.Jet
