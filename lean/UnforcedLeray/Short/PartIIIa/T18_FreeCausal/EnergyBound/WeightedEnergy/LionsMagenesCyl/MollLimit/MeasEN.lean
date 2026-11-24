import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3

/-!
# Part III-a, `PartIII-a:T18/3/1/3/3/11` (`MollLimit`): measurability of `E_k`, `N_k` in `s`

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. `s ↦ E_k(s)` and `s ↦ N_k(s)` are a.e. strongly measurable on `(0,∞)`: the integrand
is jointly measurable in `(s, x)` (`IsLMMollifier.measurable`), so `E_k` is strongly measurable
by `StronglyMeasurable.integral_prod_right'`; `N_k` agrees a.e. (on good slices, `lmMoll_pd_eq`)
with the integral of a jointly measurable function.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `vnorm2 v ^ 2 = ∑ i ‖v i‖²`. -/
lemma measEN_vnorm2_sq (v : Fin 2 → ℂ) : vnorm2 v ^ 2 = ∑ i : Fin 2, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- `tnorm2 T ^ 2 = ∑ i ∑ j ‖T i j‖²`. -/
lemma measEN_tnorm2_sq (T : Fin 2 → Fin 2 → ℂ) :
    tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

/-- **Measurability of `E_k`, `N_k` in `s`** on `(0,∞)`. -/
theorem lmMollMeasurableEN (hAe : LMAeGoodSlice) : LMMollMeasurableEN := by
  intro c ν μ F b G hD J hJ k
  have hmeasb : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => b p i := hD.sol.measurable
  -- `E_k`
  have hEm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, ‖J k (fun y => b (p.1, y)) p.2 i‖ ^ 2 :=
    Finset.measurable_sum _ (fun i _ => ((hJ.measurable k b hmeasb i).norm).pow_const 2)
  have hEsm : StronglyMeasurable (fun s : ℝ =>
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y => b (s, y)) x i‖ ^ 2) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (B0579.cell c))
      hEm.stronglyMeasurable
  have hEeq : (fun s : ℝ => LMMollE c J b k s) = fun s : ℝ =>
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y => b (s, y)) x i‖ ^ 2 := by
    funext s
    unfold LMMollE LMMollU
    simp only [measEN_vnorm2_sq]
  -- `N_k`
  have hmJ : ∀ (j i : Fin 2), Measurable fun p : ℝ × (ℝ × ℝ) =>
      J k (fun y i' => G (p.1, y) i' j) p.2 i := fun j i =>
    hJ.measurable k (fun p i' => G p i' j) (fun i' => hD.sol.gradMeasurable i' j) i
  have hNm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, ∑ j : Fin 2, ‖J k (fun y i' => G (p.1, y) i' j) p.2 i‖ ^ 2 :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
      ((hmJ j i).norm).pow_const 2))
  have hNsm : StronglyMeasurable (fun s : ℝ =>
      ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (B0579.cell c))
      hNm.stronglyMeasurable
  have hNcongr : (fun s : ℝ => LMMollN c J b k s) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s : ℝ => ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2) := by
    filter_upwards [hAe c ν μ F b G hD, ae_restrict_mem measurableSet_Ioi] with s hgood hs
    have hs' : 0 < s := hs
    unfold LMGoodSlice at hgood
    obtain ⟨hb, hcol, -⟩ := hgood
    have hA : ∀ (x : ℝ × ℝ) (i j : Fin 2),
        LMPd j (fun y => LMMollU J b k s y i) x = J k (fun y i' => G (s, y) i' j) x i :=
      fun x i j => lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hJ hb
        hcol (fun i' j' => hD.sol.weakGrad s hs' i' j') k i j x
    unfold LMMollN
    refine integral_congr_ae (ae_of_all _ (fun x => ?_))
    show (tnorm2 _) ^ 2 = _
    rw [measEN_tnorm2_sq]
    simp only [hA]
  refine ⟨?_, ?_⟩
  · rw [hEeq]
    exact hEsm.aestronglyMeasurable
  · exact hNsm.aestronglyMeasurable.congr hNcongr.symm

end UnforcedLeray.Short.IIIa
