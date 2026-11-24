import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5

/-!
# Part II-b, task `PartII-b:T09/5/3` (`LapNiceClass`): the classical `Q_ε`, `∂_η` of a nice profile
are nice

Source of record: `the November 2 reference manuscript`, lines 1639-1668 and
1912-1916.

Target: `lapNiceClass_proof : UnforcedLeray.Short.IIb.LapNiceClass`.

Proof outline:
* smoothness: `fderiv` of a smooth profile is smooth; `classQ ε b` is a finite sum of smooth
  coefficients `vQ ε x j` times `∂_j b`, plus `dQ ε · b`; `classEta b = ∂_η b`;
* `c`-periodicity in `q`: `q ↦ q + c` is a translation, so `fderiv b (qShift c x) = fderiv b x`
  (`fderiv_comp_add_right`); the coefficients of `vQ` depend only on `s` and `η`;
* support: the vanishing region of `b` is open, so `b` and `fderiv b` vanish on it; the same
  parameters `s₀, s₁, L` work for `classQ ε b` and `classEta b`.
Helpers are self-contained in this file (namespace `LapNiceClassHelp`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

namespace LapNiceClassHelp

/-- `vQ ε` has smooth components. -/
lemma vQ_component_smooth (ε : ℝ) (j : Fin 3) : ContDiff ℝ ∞ (fun x : Coord => vQ ε x j) := by
  fin_cases j <;> simp [vQ] <;> fun_prop

/-- The derivative of a smooth profile is smooth. -/
lemma fderiv_smooth {b : CProf} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (fderiv ℝ b) :=
  hb.fderiv_right (by simp)

/-- Directional derivatives `∂_j b` of a smooth profile are smooth. -/
lemma fderiv_dir_smooth {b : CProf} (hb : ContDiff ℝ ∞ b) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ b x (cdir j)) :=
  (fderiv_smooth hb).clm_apply contDiff_const

/-- `classQ ε b` is smooth. -/
lemma classQ_smooth (ε : ℝ) {b : CProf} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (classQ ε b) := by
  have hdQ : ContDiff ℝ ∞ (dQ ε) := contDiff_const
  have hsum : ContDiff ℝ ∞ (fun x : Coord => ∑ j : Fin 3, vQ ε x j • fderiv ℝ b x (cdir j)) :=
    ContDiff.sum (fun j _ => (vQ_component_smooth ε j).smul (fderiv_dir_smooth hb j))
  exact hsum.add (hdQ.smul hb)

/-- `classEta b` is smooth. -/
lemma classEta_smooth {b : CProf} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (classEta b) :=
  fderiv_dir_smooth hb 2

/-- The shift `q ↦ q + c` as a translation. -/
lemma qShift_eq (c : ℝ) (z : Coord) : qShift c z = z + (0, (c, 0)) := by
  ext <;> simp [qShift]

/-- Translation invariance of the derivative of a `q`-periodic profile. -/
lemma fderiv_periodic {c : ℝ} {b : CProf} (hper : ∀ x, b (qShift c x) = b x) (y : Coord) :
    fderiv ℝ b (qShift c y) = fderiv ℝ b y := by
  have hfun : (fun z : Coord => b (z + (0, (c, 0)))) = b :=
    funext fun z => by rw [← qShift_eq]; exact hper z
  calc fderiv ℝ b (qShift c y) = fderiv ℝ b (y + (0, (c, 0))) := by rw [qShift_eq]
    _ = fderiv ℝ (fun z : Coord => b (z + (0, (c, 0)))) y := (fderiv_comp_add_right _).symm
    _ = fderiv ℝ b y := by rw [hfun]

/-- `classQ ε b` is `q`-periodic. -/
lemma classQ_periodic (ε c : ℝ) {b : CProf} (hper : ∀ x, b (qShift c x) = b x) (x : Coord) :
    classQ ε b (qShift c x) = classQ ε b x := by
  have hq : ∀ j : Fin 3, vQ ε (qShift c x) j = vQ ε x j := fun j => by
    fin_cases j <;> simp [vQ, qShift]
  simp only [classQ]
  rw [fderiv_periodic hper x, hper x]
  simp only [hq, dQ]

/-- `classEta b` is `q`-periodic. -/
lemma classEta_periodic (c : ℝ) {b : CProf} (hper : ∀ x, b (qShift c x) = b x) (x : Coord) :
    classEta b (qShift c x) = classEta b x := by
  simp only [classEta]
  rw [fderiv_periodic hper x]

/-- The region where `b` is assumed to vanish is open. -/
lemma region_open (s₀ s₁ L : ℝ) :
    IsOpen {y : Coord | y.1 < s₀ ∨ s₁ < y.1 ∨ L < |y.2.2|} := by
  have h1 : IsOpen {y : Coord | y.1 < s₀} := isOpen_lt continuous_fst continuous_const
  have h2 : IsOpen {y : Coord | s₁ < y.1} := isOpen_lt continuous_const continuous_fst
  have h3 : IsOpen {y : Coord | L < |y.2.2|} :=
    isOpen_lt continuous_const (continuous_snd.comp continuous_snd).abs
  have e : {y : Coord | y.1 < s₀ ∨ s₁ < y.1 ∨ L < |y.2.2|} =
      {y : Coord | y.1 < s₀} ∪ ({y : Coord | s₁ < y.1} ∪ {y : Coord | L < |y.2.2|}) := by
    ext y
    simp
  rw [e]
  exact h1.union (h2.union h3)

/-- A profile vanishing on an open set has zero value and zero derivative there. -/
lemma zero_on_open {b : CProf} {O : Set Coord} (hO : IsOpen O) (hb0 : ∀ y ∈ O, b y = 0)
    {x : Coord} (hx : x ∈ O) : b x = 0 ∧ fderiv ℝ b x = 0 := by
  have hev : b =ᶠ[𝓝 x] (fun _ => (0 : CMerid)) :=
    Filter.eventually_of_mem (hO.mem_nhds hx) hb0
  refine ⟨hb0 x hx, ?_⟩
  rw [hev.fderiv_eq]
  simp

end LapNiceClassHelp

open UnforcedLeray.Short.IIb.LapNiceClassHelp in
theorem lapNiceClass_proof : UnforcedLeray.Short.IIb.LapNiceClass := by
  intro c ε b hb
  unfold NiceProf at hb
  obtain ⟨hs, hper, s₀, s₁, L, hs0, hvan⟩ := hb
  have hz : ∀ x : Coord, (x.1 < s₀ ∨ s₁ < x.1 ∨ L < |x.2.2|) → b x = 0 ∧ fderiv ℝ b x = 0 :=
    fun x hx => zero_on_open (region_open s₀ s₁ L) (fun y hy => hvan y hy) hx
  refine ⟨⟨classQ_smooth ε hs, classQ_periodic ε c hper, ?_⟩,
    ⟨classEta_smooth hs, classEta_periodic c hper, ?_⟩⟩
  · refine ⟨s₀, s₁, L, hs0, fun x hx => ?_⟩
    simp [classQ, (hz x hx).1, (hz x hx).2]
  · refine ⟨s₀, s₁, L, hs0, fun x hx => ?_⟩
    simp [classEta, (hz x hx).2]

end UnforcedLeray.Short.IIb
