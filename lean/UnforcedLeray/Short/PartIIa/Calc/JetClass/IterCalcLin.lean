import UnforcedLeray.Short.PartIIa.Calc.JetClass
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.IterComm

/-!
# Part II-a, jet-class calculus: words are local and linear on single profiles (`IterCalcLin`)

Target: `UnforcedLeray.Short.PartIIa.Jet.iterCalcLin : IterCalcLin` (`Calc/JetClass.lean`).

Source of record: `the November 2 reference manuscript`, lines 1243-1272.

Proof route. Call an operator `D` on profile functions *good* (`ICLinGood D`) when it
* respects `EqOn` on the open set `{s > 0}`;
* maps functions smooth on `{s > 0}` to smooth functions there;
* is linear on smooth functions at points `s > 0` (`D (F + k G) = D F + k D G`), and
* commutes with constant multiples on smooth functions (`D (k F) = k D F`).

`∂_η`, `∂_q` and `K = ageOperator` are good (pointwise `fderiv_add`, `fderiv_const_mul` at
points of differentiability, the `EqOn` lift of `IterComm`, and smoothness of `K` as in
`SmoothClosure`). Goodness is preserved under composition and iteration, so the word
`K^ℓ ∂_η^a ∂_q^b` is good, which gives the three clauses of `IterCalcLin`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190

/-- Operators on profile functions that behave well on `{s > 0}`. -/
def ICLinGood (D : (ProfilePoint → ℝ) → ProfilePoint → ℝ) : Prop :=
  (∀ {F F' : ProfilePoint → ℝ}, EqOn F F' {x : ProfilePoint | 0 < x.2.2} →
      EqOn (D F) (D F') {x : ProfilePoint | 0 < x.2.2}) ∧
  (∀ F : ProfilePoint → ℝ, ContDiffOn ℝ ∞ F {x : ProfilePoint | 0 < x.2.2} →
      ContDiffOn ℝ ∞ (D F) {x : ProfilePoint | 0 < x.2.2}) ∧
  (∀ (F G : ProfilePoint → ℝ) (k : ℝ), ContDiffOn ℝ ∞ F {x : ProfilePoint | 0 < x.2.2} →
      ContDiffOn ℝ ∞ G {x : ProfilePoint | 0 < x.2.2} →
      EqOn (D (fun x => F x + k * G x)) (fun x => D F x + k * D G x)
        {x : ProfilePoint | 0 < x.2.2}) ∧
  (∀ (F : ProfilePoint → ℝ) (k : ℝ), ContDiffOn ℝ ∞ F {x : ProfilePoint | 0 < x.2.2} →
      EqOn (D (fun x => k * F x)) (fun x => k * D F x) {x : ProfilePoint | 0 < x.2.2})

/-- `C²` at each point of `{s > 0}` for smooth functions there. -/
theorem icl_c2 {H : ProfilePoint → ℝ} (hH : ContDiffOn ℝ ∞ H {x : ProfilePoint | 0 < x.2.2})
    {x : ProfilePoint} (hx : 0 < x.2.2) : ContDiffAt ℝ 2 H x :=
  (hH.contDiffAt (UnforcedLeray.Short.PartIIa.isOpen_late.mem_nhds hx)).of_le (by norm_num)

/-- Scalar multiples commute with the fibre derivative in a fixed direction. -/
theorem icl_scal_dir {G : ProfilePoint → ℝ} {y : ProfilePoint} (d : ProfilePoint) (c : ℝ)
    (hG : DifferentiableAt ℝ G y) :
    fderiv ℝ (fun X => c * G X) y d = c * fderiv ℝ G y d := by
  rw [fderiv_const_mul hG c]
  simp

theorem icl_scal_eta {G : ProfilePoint → ℝ} {y : ProfilePoint} (c : ℝ)
    (hG : DifferentiableAt ℝ G y) :
    partialEta (fun X => c * G X) y = c * partialEta G y :=
  icl_scal_dir eηDir c hG

theorem icl_scal_q {G : ProfilePoint → ℝ} {y : ProfilePoint} (c : ℝ)
    (hG : DifferentiableAt ℝ G y) :
    partialQ (fun X => c * G X) y = c * partialQ G y :=
  icl_scal_dir eqDir c hG

theorem icl_scal_age {G : ProfilePoint → ℝ} {y : ProfilePoint} (c : ℝ)
    (hG : DifferentiableAt ℝ G y) :
    partialAge (fun X => c * G X) y = c * partialAge G y :=
  icl_scal_dir esDir c hG

theorem icl_scal_K {G : ProfilePoint → ℝ} {y : ProfilePoint} (c : ℝ)
    (hG : DifferentiableAt ℝ G y) :
    ageOperator (fun X => c * G X) y = c * ageOperator G y := by
  unfold ageOperator
  rw [icl_scal_eta c hG, icl_scal_age c hG]
  ring

/-- `K` maps functions smooth on `{s > 0}` to such functions. -/
theorem icl_smooth_K {F : ProfilePoint → ℝ} (hF : ContDiffOn ℝ ∞ F {x : ProfilePoint | 0 < x.2.2}) :
    ContDiffOn ℝ ∞ (ageOperator F) {x : ProfilePoint | 0 < x.2.2} := by
  have hE := UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hF eηDir
  have hA := UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hF esDir
  have h1 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => x.2.1) {x : ProfilePoint | 0 < x.2.2} :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) {x : ProfilePoint | 0 < x.2.2} :=
    contDiffOn_const.mul (contDiff_snd.comp contDiff_snd).contDiffOn
  show ContDiffOn ℝ ∞ (fun x : ProfilePoint =>
    x.2.1 * fderiv ℝ F x eηDir + 2 * x.2.2 * fderiv ℝ F x esDir) {x : ProfilePoint | 0 < x.2.2}
  exact (h1.mul hE).add (h2.mul hA)

/-- `K` respects equality on `{s > 0}`. -/
theorem icl_lift_K {F F' : ProfilePoint → ℝ} (h : EqOn F F' {x : ProfilePoint | 0 < x.2.2}) :
    EqOn (ageOperator F) (ageOperator F') {x : ProfilePoint | 0 < x.2.2} := by
  intro y hy
  unfold ageOperator
  rw [UnforcedLeray.Short.PartIIa.IterComm.iterLifts_eta h hy,
    UnforcedLeray.Short.PartIIa.IterComm.iterLifts_age h hy]

theorem icl_good_id : ICLinGood id := by
  unfold ICLinGood
  refine ⟨fun h => h, fun F hF => hF, ?_, ?_⟩
  · intro F G k _ _ x _
    rfl
  · intro F k _ x _
    rfl

theorem icl_good_eta : ICLinGood partialEta := by
  unfold ICLinGood
  refine ⟨fun h => UnforcedLeray.Short.PartIIa.IterComm.iterLifts_eta h,
    fun F hF => UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hF eηDir, ?_, ?_⟩
  · intro F G k hF hG x hx
    exact partialEta_add_mul ((icl_c2 hF hx).differentiableAt (by norm_num))
      ((icl_c2 hG hx).differentiableAt (by norm_num)) k
  · intro F k hF x hx
    exact icl_scal_eta k ((icl_c2 hF hx).differentiableAt (by norm_num))

theorem icl_good_q : ICLinGood partialQ := by
  unfold ICLinGood
  refine ⟨fun h => UnforcedLeray.Short.PartIIa.IterComm.iterLifts_q h,
    fun F hF => UnforcedLeray.Short.PartIIa.contDiffOn_fderiv_apply hF eqDir, ?_, ?_⟩
  · intro F G k hF hG x hx
    exact partialQ_add_mul ((icl_c2 hF hx).differentiableAt (by norm_num))
      ((icl_c2 hG hx).differentiableAt (by norm_num)) k
  · intro F k hF x hx
    exact icl_scal_q k ((icl_c2 hF hx).differentiableAt (by norm_num))

theorem icl_good_K : ICLinGood ageOperator := by
  unfold ICLinGood
  refine ⟨fun h => icl_lift_K h, fun F hF => icl_smooth_K hF, ?_, ?_⟩
  · intro F G k hF hG x hx
    exact ageOperator_add_mul ((icl_c2 hF hx).differentiableAt (by norm_num))
      ((icl_c2 hG hx).differentiableAt (by norm_num)) k
  · intro F k hF x hx
    exact icl_scal_K k ((icl_c2 hF hx).differentiableAt (by norm_num))

/-- Good operators compose. -/
theorem icl_good_comp {D E : (ProfilePoint → ℝ) → ProfilePoint → ℝ} (hD : ICLinGood D)
    (hE : ICLinGood E) : ICLinGood (fun F => D (E F)) := by
  unfold ICLinGood at hD hE ⊢
  obtain ⟨dL, dS, dLin, dSc⟩ := hD
  obtain ⟨eL, eS, eLin, eSc⟩ := hE
  refine ⟨fun h => dL (eL h), fun F hF => dS _ (eS F hF), ?_, ?_⟩
  · intro F G k hF hG
    exact (dL (eLin F G k hF hG)).trans (dLin (E F) (E G) k (eS F hF) (eS G hG))
  · intro F k hF
    exact (dL (eSc F k hF)).trans (dSc (E F) k (eS F hF))

/-- Iterates of good operators are good. -/
theorem icl_good_iter {D : (ProfilePoint → ℝ) → ProfilePoint → ℝ} (hD : ICLinGood D) (n : ℕ) :
    ICLinGood (D^[n]) := by
  induction n with
  | zero =>
    rw [Function.iterate_zero]
    exact icl_good_id
  | succ n ih =>
    have e : D^[n + 1] = fun F => D (D^[n] F) := by
      funext F
      exact Function.iterate_succ_apply' D n F
    rw [e]
    exact icl_good_comp hD ih

/-- The word `K^ℓ ∂_η^a ∂_q^b` is good. -/
theorem icl_good_word (ℓ a b : ℕ) :
    ICLinGood (fun F => ageOperator^[ℓ] (partialEta^[a] (partialQ^[b] F))) :=
  icl_good_comp (icl_good_iter icl_good_K ℓ)
    (icl_good_comp (icl_good_iter icl_good_eta a) (icl_good_iter icl_good_q b))

/-- **Words are local and linear on single profiles** (`IterCalcLin`). -/
theorem iterCalcLin : IterCalcLin := by
  unfold IterCalcLin
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg ℓ a b
    have W := icl_good_word ℓ a b
    unfold ICLinGood at W
    exact W.1 hfg
  · intro f g hf hg k ℓ a b
    have W := icl_good_word ℓ a b
    unfold ICLinGood at W
    exact W.2.2.1 f g k hf hg
  · intro f hf k ℓ a b
    have W := icl_good_word ℓ a b
    unfold ICLinGood at W
    exact W.2.2.2 f k hf

end UnforcedLeray.Short.PartIIa.Jet
