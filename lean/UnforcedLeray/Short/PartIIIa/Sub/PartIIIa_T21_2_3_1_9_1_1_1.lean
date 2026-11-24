import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1_1

/-!
# `PartIII-a:T21/2/3/1/9/1/1/1` (`ladDensApprox`), decomposition

Source `the November 2 reference manuscript` lines 3230-3240.
`LadDensApprox m` follows from
* `LadDensContinuous` : continuous `c`-periodic band-supported approximants (truncate by `ladCut R`,
  dominated convergence; then compactly supported continuous approximation of the truncated function
  on the cell, with a `q`-cutoff near `q = ±c/2`);
* `LadDensSmooth` : smooth approximants of those (mollification of the periodic extension; on
  `|η| ≤ R + 1` the weight `jb^m` is bounded above);
and the real/imaginary split, proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf 1** (SP 3230-3240): `L²(cellMeasure c m)` functions are `xNorm`-approximable by
continuous `c`-periodic functions vanishing for `|η|` large. -/
def LadDensContinuous : Prop :=
  ∀ (c m : ℝ), 0 < c → ∀ w : ℝ × ℝ → ℂ, MemLp w 2 (B0579.cellMeasure c m) →
    ∀ ε : ℝ, 0 < ε → ∃ g : ℝ × ℝ → ℂ, Continuous g ∧ (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) ∧
      (∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) ∧
      xNorm c m (fun x => w x - g x) < ENNReal.ofReal ε

/-- **Leaf 2** (SP 3230-3240): smoothing of such a `g` by convolution with a bump. -/
def LadDensSmooth : Prop :=
  ∀ (c m : ℝ), 0 < c → ∀ g : ℝ × ℝ → ℂ, Continuous g → (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) →
    (∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) → ∀ ε : ℝ, 0 < ε →
    ∃ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) ∧
      (∃ R : ℝ, ∀ x : ℝ × ℝ, R < |x.2| → h x = 0) ∧
      xNorm c m (fun x => g x - h x) < ENNReal.ofReal ε

theorem ladDensApprox_of (m : ℝ) (h1 : LadDensContinuous) (h2 : LadDensSmooth) :
    LadDensApprox m := by
  intro c w hc hw ε hε
  have hc0 : 0 < c := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨g, hg, hgp, hgb, hgn⟩ := h1 c m hc0 w hw (ε / 2) hε2
  obtain ⟨h, hh, hhp, ⟨R, hR⟩, hhn⟩ := h2 c m hc0 g hg hgp hgb (ε / 2) hε2
  refine ⟨fun x => (h x).re, fun x => (h x).im, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Complex.reCLM.contDiff.comp hh
  · intro x; simp [hhp x]
  · exact ⟨R, fun x hx => by simp [hR x hx]⟩
  · exact Complex.imCLM.contDiff.comp hh
  · intro x; simp [hhp x]
  · exact ⟨R, fun x hx => by simp [hR x hx]⟩
  · have e : (fun x => (((h x).re : ℝ) : ℂ) + Complex.I * (((h x).im : ℝ) : ℂ) - w x) =
        (fun x => (g x - w x) - (g x - h x)) := by
      funext x
      apply Complex.ext <;> simp
    have hgm : AEStronglyMeasurable g (B0579.cellMeasure c m) := hg.aestronglyMeasurable
    have hhm : AEStronglyMeasurable h (B0579.cellMeasure c m) :=
      hh.continuous.aestronglyMeasurable
    have hwm : AEStronglyMeasurable w (B0579.cellMeasure c m) := hw.1
    have e2 : xNorm c m (fun x => (((h x).re : ℝ) : ℂ) + Complex.I * (((h x).im : ℝ) : ℂ) - w x)
        = xNorm c m (fun x => (w x - g x) + (g x - h x)) := by
      unfold xNorm
      rw [e]
      have : (fun x => (g x - w x) - (g x - h x)) = fun x => -((w x - g x) + (g x - h x)) := by
        funext x; ring
      rw [this]
      exact eLpNorm_neg _ _ _
    rw [e2]
    unfold xNorm at hgn hhn ⊢
    have htri := eLpNorm_add_le (p := 2) (μ := B0579.cellMeasure c m)
      (f := fun x => w x - g x) (g := fun x => g x - h x) (hwm.sub hgm) (hgm.sub hhm)
      (by norm_num)
    calc _ ≤ _ := htri
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hgn hhn
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end UnforcedLeray.Short.IIIa
