import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Loc

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: the tested equation slicewise, and `LMDerivRepAEH1`

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
`lmSliceTested`: `ExtWeakH1` for `Re w`, `Im w`, combined as `Re w - i Im w = conj w`, and Fubini on
`(0,∞) × cell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The tested equation for a complexified test, slicewise in `s`.** -/
theorem lmSliceTested : LMSliceTested := by
  intro c ν μ F b G hS hE ψ hψ hcs hts w hre him
  obtain ⟨hI1, hZ1⟩ := hE ψ hψ hcs hts _ hre
  obtain ⟨hI2, hZ2⟩ := hE ψ hψ hcs hts _ him
  have hΦ : IntegrableOn (fun p =>
      extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) p -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := hI1.sub (hI2.const_mul _)
  have hΦ0 : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
      (extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) p -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) p) = 0 := by
    rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul, hZ1, hZ2]
    simp
  have hprod := setIntegral_prod (μ := volume) (ν := volume) _ hΦ
  refine (setIntegral_congr_ae measurableSet_Ioi ?_).trans (hprod.symm.trans hΦ0)
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 (lmAeGoodSlice c ν μ F b G hS)]
    with s hsg hs0
  have hs := hsg hs0
  have hwL : LMCellL2 c w := fun i => by
    have h := (hre.l2 i).ofReal (K := ℂ) |>.add ((him.l2 i).ofReal (K := ℂ) |>.const_mul Complex.I)
    refine h.ae_eq (ae_of_all _ fun x => ?_)
    show ((w x i).re : ℂ) + Complex.I * ((w x i).im : ℂ) = w x i
    rw [mul_comm]
    exact Complex.re_add_im _
  have hdw : ∀ j : Fin 2, LMCellL2 c (fun x i => LMPd j (fun y => w y i) x) := fun j i =>
    (hre.l2grad i j).ofReal (K := ℂ) |>.add ((him.l2grad i j).ofReal (K := ℂ) |>.const_mul Complex.I)
  have hT := fun j => lmTens_col_cellL2 (ν := ν) hs j
  have hAi : Integrable (fun x => ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => lmIp_integrable hwL hs.1 i
  have hBi : ∀ i j : Fin 2, Integrable
      (fun x => starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j)
      (volume.restrict (B0579.cell c)) := fun i j => lmIp_integrable (hdw j) (hT j) i
  have hBsum : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hBi i j
  have hpt : ∀ x : ℝ × ℝ, extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) (s, x) -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) (s, x) =
      -(((deriv ψ s : ℝ) : ℂ) * ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i) +
        ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i) +
        ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2,
          starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j := by
    intro x
    have hw : ∀ i : Fin 2, starRingEnd ℂ (w x i) =
        (((w x i).re : ℝ) : ℂ) - Complex.I * (((w x i).im : ℝ) : ℂ) := fun i => by
      apply Complex.ext <;> simp
    simp only [extWeakIntegrand, lmTens, LMPd, Fin.sum_univ_two, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I, hw]
    push_cast
    ring
  have i1 : Integrable (fun x => -(((deriv ψ s : ℝ) : ℂ) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)) (volume.restrict (B0579.cell c)) :=
    (hAi.const_mul _).fun_neg
  have i2 : Integrable (fun x => ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)) (volume.restrict (B0579.cell c)) :=
    (hAi.const_mul _).const_mul _
  have i3 := hBsum.const_mul ((ψ s : ℝ) : ℂ)
  have hsum : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j =
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
        starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hBi i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hBi i j
  show _ = ∫ x in B0579.cell c,
      (extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).re) (s, x) -
        Complex.I * extWeakIntegrand ν μ F b G ψ (fun x i => (w x i).im) (s, x))
  have i12 : Integrable (fun x => -(((deriv ψ s : ℝ) : ℂ) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i) + ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) *
      ∑ i : Fin 2, starRingEnd ℂ (w x i) * b (s, x) i)) (volume.restrict (B0579.cell c)) :=
    i1.add i2
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add i12 i3, integral_add i1 i2,
    integral_neg, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hsum]
  rfl

end UnforcedLeray.Short.IIIa
