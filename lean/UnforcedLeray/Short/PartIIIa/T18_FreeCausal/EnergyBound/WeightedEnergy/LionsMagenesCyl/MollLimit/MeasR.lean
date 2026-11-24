import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/12` (`MollLimit`): measurability of `R_k` in `s`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. `s ↦ R_k(s)` is a.e. strongly measurable on `(0,∞)`. On good slices
`R_k(s) = ∫_cell Re⟨F(s), J_k² G(s)⟩` (`lmMoll_pd2_eq`, which uses `LMSmoothWeakPd`), and the
integrand is jointly measurable in `(s, x)` by `IsLMMollifier.measurable` applied twice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Measurability of `R_k` in `s`** on `(0,∞)`. -/
theorem lmMollMeasurableR (hS : LMSmoothWeakPd) (hAe : LMAeGoodSlice) : LMMollMeasurableR := by
  intro c ν μ F b G hD J hJ k
  have hmeasb : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => b p i := hD.sol.measurable
  -- `p ↦ J_k (G_{p.1})_{·j}(p.2)_i`
  have hmJ : ∀ (j i : Fin 2), Measurable fun p : ℝ × (ℝ × ℝ) =>
      J k (fun y i' => G (p.1, y) i' j) p.2 i := fun j i =>
    hJ.measurable k (fun p i' => G p i' j) (fun i' => hD.sol.gradMeasurable i' j) i
  -- `p ↦ J_k² (G_{p.1})_{·j}(p.2)_i`
  have hXm : ∀ (j i : Fin 2), Measurable fun p : ℝ × (ℝ × ℝ) =>
      J k (J k (fun y i' => G (p.1, y) i' j)) p.2 i := fun j i =>
    hJ.measurable k (fun p i' => J k (fun y i'' => G (p.1, y) i'' j) p.2 i')
      (fun i' => hmJ j i') i
  have hQ : Measurable fun p : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (J k (J k (fun y i' => G (p.1, y) i' j)) p.2 i).re +
        (F p i j).im * (J k (J k (fun y i' => G (p.1, y) i' j)) p.2 i).im) := by
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    have hF1 : Measurable fun p : ℝ × (ℝ × ℝ) => (F p i j).re :=
      Complex.measurable_re.comp (hD.meas i j)
    have hF2 : Measurable fun p : ℝ × (ℝ × ℝ) => (F p i j).im :=
      Complex.measurable_im.comp (hD.meas i j)
    have hX1 : Measurable fun p : ℝ × (ℝ × ℝ) => (J k (J k (fun y i' => G (p.1, y) i' j)) p.2 i).re :=
      Complex.measurable_re.comp (hXm j i)
    have hX2 : Measurable fun p : ℝ × (ℝ × ℝ) => (J k (J k (fun y i' => G (p.1, y) i' j)) p.2 i).im :=
      Complex.measurable_im.comp (hXm j i)
    exact (hF1.mul hX1).add (hF2.mul hX2)
  have hRsm : StronglyMeasurable (fun s : ℝ => ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (B0579.cell c))
      hQ.stronglyMeasurable
  have hRcongr : (fun s : ℝ => LMMollR c J F b k s) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s : ℝ => ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im)) := by
    filter_upwards [hAe c ν μ F b G hD, ae_restrict_mem measurableSet_Ioi] with s hgood hs
    have hs' : 0 < s := hs
    unfold LMGoodSlice at hgood
    obtain ⟨hb, hcol, -⟩ := hgood
    have hA2 : ∀ (x : ℝ × ℝ) (i j : Fin 2),
        LMPd j (fun y => J k (LMMollU J b k s) y i) x
          = J k (J k (fun y i' => G (s, y) i' j)) x i :=
      fun x i j => lmMoll_pd2_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hS
        hD.pos_c hJ hb hcol (fun i' j' => hD.sol.weakGrad s hs' i' j') k i j x
    unfold LMMollR
    simp only [hA2]
  exact hRsm.aestronglyMeasurable.congr hRcongr.symm

end UnforcedLeray.Short.IIIa
