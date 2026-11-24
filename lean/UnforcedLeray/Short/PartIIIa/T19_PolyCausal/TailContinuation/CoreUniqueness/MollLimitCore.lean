import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness.MollDerivCore
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollLimit
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.CoreImpliesWeighted.CoreToSmooth

/-!
# Part III-a, helper 4 of `PartIII-a:T19/3/4`: mollified limit, core identity, and smooth weighted energy on `(0, H')`

For truncated core causal solution data `CoreTruncData c ν H' μ F b G`, letting `k → ∞` in
`mollEnergyIdentity_trunc` by dominated convergence (`lmWeightedDCT`) gives the unconjugated energy
identity (`coreIdentity_trunc`) for every smooth weight `w` with `tsupport w ⊆ Ioo 0 H'`.
Applying `CoreToSmoothAux.real_core` to `w = wWeight γ ν ψ` (whose `tsupport` is contained in
`tsupport ψ ⊆ Ioo 0 H'`) yields `coreWeightedEnergySmooth`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Pointwise limit `E_k(s) → E(s)` on a good slice. -/
theorem pointwiseE_trunc {c : ℝ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J) {s : ℝ}
    (hg : LMGoodSlice c F G b s) :
    Tendsto (fun k : ℕ => LMMollE c J b k s) atTop (𝓝 (energyE c b s)) :=
  lm_tendsto_vsq (a := fun k => J k (fun y => b (s, y))) (a₀ := fun y => b (s, y))
    (fun k => hJ.memL2 k _ hg.1) hg.1 (hJ.tendsto _ hg.1)

/-- Pointwise limit `N_k(s) → N(s)` on a good slice for `CoreTruncData`. -/
theorem pointwiseN_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) {s : ℝ} (hs : 0 < s) (hg : LMGoodSlice c F G b s) :
    Tendsto (fun k : ℕ => LMMollN c J b k s) atTop (𝓝 (energyN c G s)) := by
  have hf : LMCellL2 c (fun y => b (s, y)) := hg.1
  have hgj : ∀ j : Fin 2, LMCellL2 c (fun y i => G (s, y) i j) := hg.2.1
  have hpd : ∀ (k : ℕ) (x : ℝ × ℝ) (i j : Fin 2),
      LMPd j (fun y => LMMollU J b k s y i) x = J k (fun z i' => G (s, z) i' j) x i :=
    fun k x i j => lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j z i' => G (s, z) i' j)
      hJ hf hgj (fun i j => hD.weakGrad s hs i j) k i j x
  have hN : ∀ k : ℕ, LMMollN c J b k s =
      ∫ x in B0579.cell c, tnorm2 (fun i j => J k (fun z i' => G (s, z) i' j) x i) ^ 2 := by
    intro k
    unfold LMMollN
    congr 1
    funext x
    simp only [hpd]
  have hT : ∀ (k : ℕ) (j : Fin 2), LMCellL2 c (fun x i => J k (fun z i' => G (s, z) i' j) x i) :=
    fun k j => hJ.memL2 k _ (hgj j)
  have h : ∀ j : Fin 2, Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2,
      ‖J k (fun z i' => G (s, z) i' j) x i - G (s, x) i j‖ ^ 2) atTop (𝓝 0) :=
    fun j => hJ.tendsto _ (hgj j)
  have key := lm_tendsto_tsq (c := c)
    (T := fun k x i j => J k (fun z i' => G (s, z) i' j) x i)
    (T₀ := fun x i j => G (s, x) i j) hT hgj h
  have e1 : (fun k : ℕ => LMMollN c J b k s) =
      fun k : ℕ => ∫ x in B0579.cell c, tnorm2 (fun i j => J k (fun z i' => G (s, z) i' j) x i) ^ 2 :=
    funext hN
  show Tendsto (fun k : ℕ => LMMollN c J b k s) atTop
    (𝓝 (∫ x in B0579.cell c, tnorm2 (G (s, x)) ^ 2))
  rw [e1]
  exact key

/-- Pointwise limit `R_k(s) → R(s)` on a good slice for `CoreTruncData`. -/
theorem pointwiseR_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) {s : ℝ} (hs : 0 < s) (hg : LMGoodSlice c F G b s) :
    Tendsto (fun k : ℕ => LMMollR c J F b k s) atTop (𝓝 (energyR c F G s)) := by
  have hf : LMCellL2 c (fun y => b (s, y)) := hg.1
  have hgj : ∀ j : Fin 2, LMCellL2 c (fun y i => G (s, y) i j) := hg.2.1
  have hpd : ∀ (k : ℕ) (x : ℝ × ℝ) (i j : Fin 2),
      LMPd j (fun y => J k (LMMollU J b k s) y i) x =
        J k (J k (fun z i' => G (s, z) i' j)) x i :=
    fun k x i j => lmMoll_pd2_eq lmSmoothWeakPd hD.pos_c hJ (f := fun y => b (s, y))
      (g := fun j z i' => G (s, z) i' j) hf hgj (fun i j => hD.weakGrad s hs i j) k i j x
  have hR : ∀ k : ℕ, LMMollR c J F b k s = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun z i' => G (s, z) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun z i' => G (s, z) i' j)) x i).im) := by
    intro k
    unfold LMMollR
    congr 1
    funext x
    simp only [hpd]
  have hT : ∀ (k : ℕ) (j : Fin 2),
      LMCellL2 c (fun x i => J k (J k (fun z i' => G (s, z) i' j)) x i) :=
    fun k j => hJ.memL2 k _ (hJ.memL2 k _ (hgj j))
  have hH : ∀ j : Fin 2, LMCellL2 c (fun x i => F (s, x) i j) := hg.2.2
  have h : ∀ j : Fin 2, Tendsto (fun k : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2,
      ‖J k (J k (fun z i' => G (s, z) i' j)) x i - G (s, x) i j‖ ^ 2) atTop (𝓝 0) :=
    fun j => lmMoll_twice_tendsto hJ (hgj j)
  have key := lm_tendsto_tpair (c := c)
    (T := fun k x i j => J k (J k (fun z i' => G (s, z) i' j)) x i)
    (T₀ := fun x i j => G (s, x) i j) (H := fun x i j => F (s, x) i j) hT hgj hH h
  show Tendsto (fun k : ℕ => LMMollR c J F b k s) atTop
    (𝓝 (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)))
  simp only [hR]
  exact key

/-- Domination of `E_k`, `N_k` on a good slice for `CoreTruncData`. -/
theorem domEN_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) {s : ℝ} (hs : 0 < s) (hgs : LMGoodSlice c F G b s) (k : ℕ) :
    0 ≤ LMMollE c J b k s ∧ LMMollE c J b k s ≤ energyE c b s ∧
      0 ≤ LMMollN c J b k s ∧ LMMollN c J b k s ≤ energyN c G s := by
  obtain ⟨hb, hcol, -⟩ := hgs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact integral_nonneg (fun x => sq_nonneg _)
  · unfold LMMollE energyE
    simp only [domEN_vnorm2_sq]
    exact hJ.contr k (fun y => b (s, y)) hb
  · exact integral_nonneg (fun x => sq_nonneg _)
  · have hA : ∀ (x : ℝ × ℝ) (i j : Fin 2),
        LMPd j (fun y => LMMollU J b k s y i) x = J k (fun y i' => G (s, y) i' j) x i :=
      fun x i j => lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hJ hb
        hcol (fun i' j' => hD.weakGrad s hs i' j') k i j x
    have hT : ∀ x : ℝ × ℝ, tnorm2 (fun i j => LMPd j (fun y => LMMollU J b k s y i) x) ^ 2 =
        ∑ j : Fin 2, ∑ i : Fin 2, ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 := by
      intro x
      rw [domEN_tnorm2_sq]
      simp only [hA]
      exact Finset.sum_comm
    have hNeq : LMMollN c J b k s = ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 := by
      unfold LMMollN
      exact integral_congr_ae (ae_of_all _ (fun x => hT x))
    have hint : ∀ j : Fin 2, Integrable (fun x => ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2) (volume.restrict (B0579.cell c)) :=
      fun j => domEN_integrable_sum (hJ.memL2 k _ (hcol j))
    have hL : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2
        = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
          ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun j _ => hint j)
    have hRHS : energyN c G s = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖G (s, x) i j‖ ^ 2 := by
      have hI : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2
          = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
        integral_finsetSum Finset.univ (fun j _ => domEN_integrable_sum (hcol j))
      unfold energyN
      simp only [domEN_tnorm2_sq]
      rw [← hI]
      exact integral_congr_ae (ae_of_all _ (fun x => Finset.sum_comm))
    have hbd : ∀ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2,
          ‖G (s, x) i j‖ ^ 2 :=
      fun j => hJ.contr k _ (hcol j)
    rw [hNeq, hL, hRHS]
    exact Finset.sum_le_sum (fun j _ => hbd j)

/-- Domination of `R_k` on a good slice for `CoreTruncData`. -/
theorem domR_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) {s : ℝ} (hs : 0 < s) (hgs : LMGoodSlice c F G b s) (k : ℕ) :
    |LMMollR c J F b k s| ≤ energyN c F s + energyN c G s := by
  obtain ⟨hb, hcol, hFc⟩ := hgs
  have hA2 : ∀ (x : ℝ × ℝ) (i j : Fin 2),
      LMPd j (fun y => J k (LMMollU J b k s) y i) x = J k (J k (fun y i' => G (s, y) i' j)) x i :=
    fun x i j => lmMoll_pd2_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j)
      lmSmoothWeakPd hD.pos_c hJ hb hcol (fun i' j' => hD.weakGrad s hs i' j') k i j x
  have hR : LMMollR c J F b k s = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im) := by
    unfold LMMollR
    simp only [hA2]
  have hF1 : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) := by
    refine integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => ?_))
    exact domR_integrable_entry (hFc j) i
  have hX2 : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
      ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2) (volume.restrict (B0579.cell c)) := by
    refine integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => ?_))
    exact domR_integrable_entry (hJ.memL2 k _ (hJ.memL2 k _ (hcol j))) i
  have hG2 : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2 ≤ energyN c G s := by
    have hI : ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2
        = ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
          ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2 :=
      integral_congr_ae (ae_of_all _ (fun x => Finset.sum_comm))
    have hL : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2,
        ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2
        = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
          ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2 :=
      integral_finsetSum Finset.univ (fun j _ =>
        domR_integrable_sum (hJ.memL2 k _ (hJ.memL2 k _ (hcol j))))
    have hbd : ∀ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2
        ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
      fun j => (hJ.contr k _ (hJ.memL2 k _ (hcol j))).trans (hJ.contr k _ (hcol j))
    have hRHS : energyN c G s = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖G (s, x) i j‖ ^ 2 := by
      have hI' : ∫ x in B0579.cell c, ∑ j : Fin 2, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2
          = ∑ j : Fin 2, ∫ x in B0579.cell c, ∑ i : Fin 2, ‖G (s, x) i j‖ ^ 2 :=
        integral_finsetSum Finset.univ (fun j _ => domR_integrable_sum (hcol j))
      unfold energyN
      simp only [domR_tnorm2_sq]
      rw [← hI']
      exact integral_congr_ae (ae_of_all _ (fun x => Finset.sum_comm))
    rw [hI, hL, hRHS]
    exact Finset.sum_le_sum (fun j _ => hbd j)
  have hFE : energyN c F s = ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2 := by
    unfold energyN
    simp only [domR_tnorm2_sq]
  have hpt : ∀ x : ℝ × ℝ, |∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im)|
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, (‖F (s, x) i j‖ ^ 2 +
          ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2) := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    exact domR_re_im_bound _ _
  have hbound : |∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ((F (s, x) i j).re * (J k (J k (fun y i' => G (s, y) i' j)) x i).re +
        (F (s, x) i j).im * (J k (J k (fun y i' => G (s, y) i' j)) x i).im)|
      ≤ ∫ x in B0579.cell c, (∑ i : Fin 2, ∑ j : Fin 2, ‖F (s, x) i j‖ ^ 2 +
          ∑ i : Fin 2, ∑ j : Fin 2, ‖J k (J k (fun y i' => G (s, y) i' j)) x i‖ ^ 2) := by
    refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
      (ae_of_all _ (fun x => abs_nonneg _)) (hF1.add hX2) (ae_of_all _ (fun x => ?_)))
    exact (hpt x).trans (le_of_eq (by simp only [Finset.sum_add_distrib]))
  rw [integral_add hF1 hX2, ← hFE] at hbound
  rw [hR]
  linarith [hG2]

/-- Measurability of `E_k`, `N_k` in `s` on `(0, ∞)` for `CoreTruncData`. -/
theorem measEN_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) :
    AEStronglyMeasurable (fun s => LMMollE c J b k s) (volume.restrict (Ioi (0 : ℝ))) ∧
      AEStronglyMeasurable (fun s => LMMollN c J b k s) (volume.restrict (Ioi (0 : ℝ))) := by
  have hEm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, ‖J k (fun y => b (p.1, y)) p.2 i‖ ^ 2 :=
    Finset.measurable_sum _ (fun i _ => ((hJ.measurable k b hD.measurable i).norm).pow_const 2)
  have hEsm : StronglyMeasurable (fun s : ℝ =>
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y => b (s, y)) x i‖ ^ 2) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (B0579.cell c))
      hEm.stronglyMeasurable
  have hEeq : (fun s : ℝ => LMMollE c J b k s) = fun s : ℝ =>
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y => b (s, y)) x i‖ ^ 2 := by
    funext s
    unfold LMMollE LMMollU
    simp only [measEN_vnorm2_sq]
  have hmJ : ∀ (j i : Fin 2), Measurable fun p : ℝ × (ℝ × ℝ) =>
      J k (fun y i' => G (p.1, y) i' j) p.2 i := fun j i =>
    hJ.measurable k (fun p i' => G p i' j) (fun i' => hD.gradMeasurable i' j) i
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
    filter_upwards [aeGoodSlice_trunc hD, ae_restrict_mem measurableSet_Ioi] with s ⟨hb, hcol, _⟩ hs
    have hs' : 0 < s := hs
    have hA : ∀ (x : ℝ × ℝ) (i j : Fin 2),
        LMPd j (fun y => LMMollU J b k s y i) x = J k (fun y i' => G (s, y) i' j) x i :=
      fun x i j => lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hJ hb
        hcol (fun i' j' => hD.weakGrad s hs' i' j') k i j x
    unfold LMMollN
    refine integral_congr_ae (ae_of_all _ (fun x => ?_))
    show (tnorm2 _) ^ 2 = _
    rw [measEN_tnorm2_sq]
    simp only [hA]
  refine ⟨?_, ?_⟩
  · rw [hEeq]
    exact hEsm.aestronglyMeasurable
  · exact hNsm.aestronglyMeasurable.congr hNcongr.symm

/-- Measurability of `R_k` in `s` on `(0, ∞)` for `CoreTruncData`. -/
theorem measR_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) :
    AEStronglyMeasurable (fun s => LMMollR c J F b k s) (volume.restrict (Ioi (0 : ℝ))) := by
  have hmJ : ∀ (j i : Fin 2), Measurable fun p : ℝ × (ℝ × ℝ) =>
      J k (fun y i' => G (p.1, y) i' j) p.2 i := fun j i =>
    hJ.measurable k (fun p i' => G p i' j) (fun i' => hD.gradMeasurable i' j) i
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
    filter_upwards [aeGoodSlice_trunc hD, ae_restrict_mem measurableSet_Ioi] with s ⟨hb, hcol, _⟩ hs
    have hs' : 0 < s := hs
    have hA2 : ∀ (x : ℝ × ℝ) (i j : Fin 2),
        LMPd j (fun y => J k (LMMollU J b k s) y i) x
          = J k (J k (fun y i' => G (s, y) i' j)) x i :=
      fun x i j => lmMoll_pd2_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j)
        lmSmoothWeakPd hD.pos_c hJ hb hcol (fun i' j' => hD.weakGrad s hs' i' j') k i j x
    unfold LMMollR
    simp only [hA2]
  exact hRsm.aestronglyMeasurable.congr hRcongr.symm

/-- The `k → ∞` limit of the mollified energy integrals for `CoreTruncData`. -/
theorem mollEnergyLimit_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hcs : HasCompactSupport w) (hts : tsupport w ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun k : ℕ => ∫ s in Ioi (0 : ℝ), deriv w s * LMMollE c J b k s) atTop
        (𝓝 (∫ s in Ioi (0 : ℝ), deriv w s * energyE c b s)) ∧
      Tendsto (fun k : ℕ => ∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * LMMollE c J b k s +
          2 * ν * LMMollN c J b k s + 2 * LMMollR c J F b k s)) atTop
        (𝓝 (∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * energyE c b s +
          2 * ν * energyN c G s + 2 * energyR c F G s))) := by
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 < s ∧ LMGoodSlice c F G b s := by
    filter_upwards [aeGoodSlice_trunc hD, ae_restrict_mem measurableSet_Ioi] with s h1 h2
    exact ⟨h2, h1⟩
  refine ⟨?_, ?_⟩
  · refine lmWeightedDCT (deriv w) (hw.continuous_deriv (by simp)) hcs.deriv
      (tsupport_deriv_subset.trans hts) (fun k s => LMMollE c J b k s) (energyE c b)
      (energyE c b) (fun k => (measEN_trunc hD hJ k).1)
      (fun s₁ s₂ h0 h12 => (energyLocInt_trunc hD h0 h12).1) (fun k => ?_) ?_
    · filter_upwards [hgood] with s hs
      obtain ⟨h0, h1, -, -⟩ := domEN_trunc hD hJ hs.1 hs.2 k
      show |LMMollE c J b k s| ≤ energyE c b s
      rw [abs_of_nonneg h0]
      exact h1
    · filter_upwards [hgood] with s hs
      exact pointwiseE_trunc hJ hs.2
  · refine lmWeightedDCT w hw.continuous hcs hts
      (fun k s => 2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
        2 * LMMollR c J F b k s)
      (fun s => 2 * μ.re / s * energyE c b s + 2 * ν * energyN c G s + 2 * energyR c F G s)
      (fun s => 2 * |μ.re| / s * energyE c b s + 2 * ν * energyN c G s +
        2 * (energyN c F s + energyN c G s)) (fun k => ?_) (fun s₁ s₂ h0 h12 => ?_)
      (fun k => ?_) ?_
    · obtain ⟨hE, hN⟩ := measEN_trunc hD hJ k
      have hR := measR_trunc hD hJ k
      have hq : Measurable fun s : ℝ => 2 * μ.re / s := measurable_const.div measurable_id
      exact ((hq.aestronglyMeasurable.mul hE).add (aestronglyMeasurable_const.mul hN)).add
        (aestronglyMeasurable_const.mul hR)
    · obtain ⟨hE, hN, hF⟩ := energyLocInt_trunc hD h0 h12
      have hcont : ContinuousOn (fun s : ℝ => 2 * |μ.re| / s) (Icc s₁ s₂) :=
        continuousOn_const.div continuousOn_id (fun s hs => (h0.trans_le hs.1).ne')
      have h1 : IntegrableOn (fun s => 2 * |μ.re| / s * energyE c b s) (Icc s₁ s₂) :=
        hE.continuousOn_mul hcont isCompact_Icc
      exact Integrable.add (Integrable.add h1 (Integrable.const_mul hN (2 * ν)))
        (Integrable.const_mul (Integrable.add hF hN) 2)
    · filter_upwards [hgood] with s hs
      obtain ⟨hE0, hE1, hN0, hN1⟩ := domEN_trunc hD hJ hs.1 hs.2 k
      have hR1 := domR_trunc hD hJ hs.1 hs.2 k
      have hν : 0 ≤ 2 * ν := by linarith [hD.pos_ν]
      have e1 : |2 * μ.re / s * LMMollE c J b k s| ≤ 2 * |μ.re| / s * energyE c b s := by
        rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hs.1, abs_of_nonneg hE0]
        exact mul_le_mul_of_nonneg_left hE1 (div_nonneg (by positivity) hs.1.le)
      have e2 : |2 * ν * LMMollN c J b k s| ≤ 2 * ν * energyN c G s := by
        rw [abs_of_nonneg (mul_nonneg hν hN0)]
        exact mul_le_mul_of_nonneg_left hN1 hν
      have e3 : |2 * LMMollR c J F b k s| ≤ 2 * (energyN c F s + energyN c G s) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left hR1 (by norm_num)
      show |2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
          2 * LMMollR c J F b k s| ≤ 2 * |μ.re| / s * energyE c b s + 2 * ν * energyN c G s +
          2 * (energyN c F s + energyN c G s)
      linarith [abs_add_le (2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s)
          (2 * LMMollR c J F b k s),
        abs_add_le (2 * μ.re / s * LMMollE c J b k s) (2 * ν * LMMollN c J b k s)]
    · filter_upwards [hgood] with s hs
      exact (((pointwiseE_trunc hJ hs.2).const_mul (2 * μ.re / s)).add
        ((pointwiseN_trunc hD hJ hs.1 hs.2).const_mul (2 * ν))).add
        ((pointwiseR_trunc hD hJ hs.1 hs.2).const_mul 2)

/-- The unconjugated energy identity on `(0, H')` for `CoreTruncData`. -/
theorem coreIdentity_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hcs : HasCompactSupport w) (hts : tsupport w ⊆ Ioo 0 H') :
    ∫ s in Ioi (0 : ℝ), deriv w s * energyE c b s =
      ∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * energyE c b s +
        2 * ν * energyN c G s + 2 * energyR c F G s) := by
  obtain ⟨J, hJ⟩ := hasLMMollifier c hD.pos_c
  obtain ⟨h1, h2⟩ := mollEnergyLimit_trunc hD hJ hw hcs (fun s hs => (hts hs).1)
  exact tendsto_nhds_unique
    (h1.congr (fun k => mollEnergyIdentity_trunc hD hJ hw hcs hts k)) h2

open CoreToSmoothAux in
/-- The conjugated weighted energy inequality on `(0, H')` for smooth nonnegative weights `ψ` with
`tsupport ψ ⊆ Ioo 0 H'`. -/
theorem coreWeightedEnergySmooth {c ν H' γ : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) (hγ : 0 ≤ γ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo 0 H') (hψnn : ∀ s, 0 ≤ ψ s) :
    ∫ s in Ioi (0 : ℝ), ψ s *
        ((1 / 2 + 2 * μ.re) * s ^ (-3 / 2 : ℝ) *
            (∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2) +
          2 * ν * s ^ (-1 / 2 : ℝ) *
            (∫ x in B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2)) ≤
      (∫ s in Ioi (0 : ℝ), deriv ψ s *
          (s ^ (-1 / 2 : ℝ) * ∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2)) +
        2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) *
          (∫ x in B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) * tnorm2 (gainConj γ ν G (s, x))) := by
  have hts_pos : tsupport ψ ⊆ Ioi (0 : ℝ) := fun s hs => (hψsupp hs).1
  obtain ⟨s1, s2, hs1, hs12, hsub⟩ :=
    exists_Icc_contains (tsupport ψ) (hψc : IsCompact (tsupport ψ)) hts_pos
  obtain ⟨hEI, hNI, hRI, hJI⟩ := energyLocIntegrable_trunc hD hs1 hs12
  have hcore := coreIdentity_trunc hD (contDiff_wWeight γ ν ψ hψ hD.pos_ν hts_pos)
    (hasCompactSupport_wWeight γ ν ψ hψc) ((tsupport_wWeight_subset γ ν ψ).trans hψsupp)
  have hE0 : ∀ s, 0 ≤ energyE c b s := fun s => integral_nonneg fun x => sq_nonneg _
  have hgm : ∀ i j, Measurable fun p => G p i j := hD.gradMeasurable
  have hMfin : ∫⁻ p in Icc s1 s2 ×ˢ B0579.cell c,
      ENNReal.ofReal (tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2)) < ⊤ := by
    have hm1 : Measurable fun p => tnorm2 (F p) ^ 2 :=
      (ct_measurable_tnorm2 hD.meas).pow_const 2
    refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_add_le) ?_
    rw [lintegral_add_left hm1.ennreal_ofReal]
    exact ENNReal.add_lt_top.2 ⟨hD.l2loc s1 s2 hs1 hs12, hD.energyLoc s1 s2 hs1 hs12⟩
  have hmeasR : Measurable fun p : ℝ × (ℝ × ℝ) => ∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im) := by
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact ((Complex.measurable_re.comp (hD.meas i j)).mul
      (Complex.measurable_re.comp (hgm i j))).add
      ((Complex.measurable_im.comp (hD.meas i j)).mul (Complex.measurable_im.comp (hgm i j)))
  have hmeasT : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (F p) * tnorm2 (G p) :=
    (ct_measurable_tnorm2 hD.meas).mul (ct_measurable_tnorm2 hgm)
  have hbdR : ∀ p : ℝ × (ℝ × ℝ), |∑ i : Fin 2, ∑ j : Fin 2,
      ((F p i j).re * (G p i j).re + (F p i j).im * (G p i j).im)| ≤
      tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h1 := abs_sum_re_le_tnorm2_mul (F p) (G p)
    have h2 := ct_abs_mul_le (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    have h4 := le_abs_self (tnorm2 (F p) * tnorm2 (G p))
    linarith
  have hbdT : ∀ p : ℝ × (ℝ × ℝ), |tnorm2 (F p) * tnorm2 (G p)| ≤
      tnorm2 (F p) ^ 2 + (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) := fun p => by
    have h2 := ct_abs_mul_le (tnorm2 (F p)) (tnorm2 (G p))
    have h3 : 0 ≤ vnorm2 (b p) ^ 2 := sq_nonneg _
    linarith
  have hsR := ct_ae_slice hmeasR hbdR hMfin
  have hsT := ct_ae_slice hmeasT hbdT hMfin
  have hRJ : ∀ᵐ s ∂(volume.restrict (Icc s1 s2)), 0 ≤ energyR c F G s +
      (fun s => ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))) s := by
    filter_upwards [hsR, hsT] with s hR hT
    have hadd : (∫ x in B0579.cell c, (∑ i : Fin 2, ∑ j : Fin 2,
        ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im) +
        tnorm2 (F (s, x)) * tnorm2 (G (s, x)))) =
        (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
          ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)) +
        ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)) :=
      integral_add hR hT
    have hnn : 0 ≤ ∫ x in B0579.cell c, (∑ i : Fin 2, ∑ j : Fin 2,
        ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im) +
        tnorm2 (F (s, x)) * tnorm2 (G (s, x))) := by
      apply integral_nonneg
      intro x
      have h1 := abs_sum_re_le_tnorm2_mul (F (s, x)) (G (s, x))
      have h2 := neg_abs_le (∑ i : Fin 2, ∑ j : Fin 2,
        ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im))
      show 0 ≤ _
      linarith
    show 0 ≤ (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
          ((F (s, x) i j).re * (G (s, x) i j).re + (F (s, x) i j).im * (G (s, x) i j).im)) +
        ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x))
    linarith
  have hEu : ∀ s : ℝ, (∫ x in B0579.cell c, vnorm2 (gainConj γ ν b (s, x)) ^ 2) =
      qWt γ ν s * energyE c b s := by
    intro s
    unfold energyE
    rw [← integral_const_mul]
    congr 1
    funext x
    exact vnorm2_gainConj_sq γ ν b (s, x)
  have hNu : ∀ s : ℝ, (∫ x in B0579.cell c, tnorm2 (gainConj γ ν G (s, x)) ^ 2) =
      qWt γ ν s * energyN c G s := by
    intro s
    unfold energyN
    rw [← integral_const_mul]
    congr 1
    funext x
    exact tnorm2_gainConj_sq γ ν G (s, x)
  have hJu : ∀ s : ℝ, (∫ x in B0579.cell c, tnorm2 (gainConj γ ν F (s, x)) *
      tnorm2 (gainConj γ ν G (s, x))) =
      qWt γ ν s * ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)) := by
    intro s
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [ct_tnorm2_gainConj_eq, ct_tnorm2_gainConj_eq]
    dsimp only
    unfold qWt
    ring
  simp only [hEu, hNu, hJu]
  exact real_core γ ν μ.re s1 s2 hD.pos_ν hγ hs1 hs12 ψ hψ hsub hψnn (energyE c b) (energyN c G)
    (energyR c F G) (fun s => ∫ x in B0579.cell c, tnorm2 (F (s, x)) * tnorm2 (G (s, x)))
    hEI hNI hRI hJI hE0 hRJ hcore

end UnforcedLeray.Short.IIIa
