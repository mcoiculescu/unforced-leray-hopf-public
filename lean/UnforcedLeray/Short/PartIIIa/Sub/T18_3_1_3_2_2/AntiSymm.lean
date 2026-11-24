import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Basics
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.P0C
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Conv

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: `∂ⱼ J_k` is anti-self-adjoint; the tensor pairings

Source of record: `the November 2 reference manuscript` lines 3427-3440, 3541-3552.
`lmAntiSymm`, `lmSliceTensor`, `lmPairingSlice` (statements in `Props.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem lmPd_add_const_mul {f g : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a : ℂ) (j : Fin 2) (x : ℝ × ℝ) :
    LMPd j (fun y => f y + a * g y) x = LMPd j f x + a * LMPd j g x := by
  have hs : HasFDerivAt (fun y => f y + a * g y)
      (fderiv ℝ f x + a • fderiv ℝ g x) x :=
    (hf x).hasFDerivAt.add ((hg x).hasFDerivAt.const_smul a)
  rw [lmPd_eq_fderiv hs.differentiableAt, lmPd_eq_fderiv (hf x), lmPd_eq_fderiv (hg x), hs.fderiv]
  simp

/-- **`∂ⱼ J_k` is anti-self-adjoint on `L²(cell; ℂ²)`.** -/
theorem lmAntiSymm : LMAntiSymm := by
  intro c hc J hJ hX k j f g hf hg
  obtain ⟨C, hC⟩ := hX.gradL2 k
  have hAL : ∀ h : LMSpField, LMCellL2 c h →
      LMCellL2 c (fun x i => LMPd j (fun y => J k h y i) x) := fun h hh i => (hC h hh i j).1
  -- the smooth case `h = J n g`
  have step1 : ∀ n : ℕ, LMIp c f (fun x i => LMPd j (fun y => J k (J n g) y i) x) =
      -LMIp c (fun x i => LMPd j (fun y => J k f y i) x) (J n g) := by
    intro n
    obtain ⟨Cn, hCn⟩ := hX.gradL2 n
    have hL : LMCellL2 c (J n g) := hJ.memL2 n g hg
    have hdL : LMCellL2 c (fun x i => LMPd j (fun y => J n g y i) x) := fun i => (hCn g hg i j).1
    have hW : ∀ i : Fin 2, LMWeakPd c j (fun x => J n g x i)
        (fun x => LMPd j (fun y => J n g y i) x) := fun i =>
      lmSmoothWeakPd c hc j _ (hJ.smooth n g hg i) (fun x => hJ.periodic n g hg x i) (hL i) (hdL i)
    have hAh : (fun x i => LMPd j (fun y => J k (J n g) y i) x) =
        J k (fun x i => LMPd j (fun y => J n g y i) x) := by
      funext x i
      exact hJ.commute k (J n g) _ j hL hdL hW i x
    rw [hAh]
    have e1 : LMIp c f (J k (fun x i => LMPd j (fun y => J n g y i) x)) =
        LMIp c (J k f) (fun x i => LMPd j (fun y => J n g y i) x) :=
      (hJ.selfAdj k f _ hf hdL).symm
    rw [e1]
    have hIBP : ∀ i : Fin 2, ∫ x in B0579.cell c, starRingEnd ℂ (J k f x i) *
        LMPd j (fun y => J n g y i) x = -∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => J k f y i) x) * J n g x i := fun i =>
      lmSmoothIBP c hc j _ _ (hJ.smooth k f hf i) (hJ.smooth n g hg i)
        (fun x => hJ.periodic k f hf x i) (fun x => hJ.periodic n g hg x i)
        (hJ.memL2 k f hf i) (hL i) (hC f hf i j).1 (hdL i)
    unfold LMIp
    rw [integral_finsetSum _ fun i _ => lmIp_integrable (hJ.memL2 k f hf) hdL i,
      integral_finsetSum _ fun i _ => lmIp_integrable (hAL f hf) hL i]
    simp only [Fin.sum_univ_two, hIBP]
    ring
  -- the limit `n → ∞`
  have hlim1 := lmIpTendstoRight c (fun x i => LMPd j (fun y => J k f y i) x) g (fun n => J n g)
    (hAL f hf) hg (fun n => hJ.memL2 n g hg) (hJ.tendsto g hg)
  have hlim2 : Tendsto (fun n : ℕ => LMIp c f (fun x i => LMPd j (fun y => J k (J n g) y i) x)) atTop
      (𝓝 (LMIp c f (fun x i => LMPd j (fun y => J k g y i) x))) := by
    refine lmIpTendstoRight c f _ _ hf (hAL g hg) (fun n => hAL _ (hJ.memL2 n g hg)) ?_
    -- the difference field
    have hdL : ∀ n : ℕ, LMCellL2 c (fun x i => J n g x i + (-1 : ℂ) * g x i) := fun n i =>
      (hJ.memL2 n g hg i).add ((hg i).const_mul _)
    have hsplit : ∀ (n : ℕ) (x : ℝ × ℝ) (i : Fin 2),
        LMPd j (fun y => J k (J n g) y i) x - LMPd j (fun y => J k g y i) x =
          LMPd j (fun y => J k (fun z i' => J n g z i' + (-1 : ℂ) * g z i') y i) x := by
      intro n x i
      have e1 : J k (fun z i' => J n g z i' + (-1 : ℂ) * g z i') =
          fun y i' => J k (J n g) y i' + (-1 : ℂ) * J k g y i' := by
        rw [hJ.add k (J n g) _ (hJ.memL2 n g hg) (fun i => (hg i).const_mul _), hJ.smul k _ g hg]
      rw [e1]
      rw [lmPd_add_const_mul
        ((hJ.smooth k _ (hJ.memL2 n g hg) i).differentiable (by simp))
        ((hJ.smooth k g hg i).differentiable (by simp))]
      ring
    have hbd : ∀ n : ℕ, ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖LMPd j (fun y => J k (J n g) y i) x - LMPd j (fun y => J k g y i) x‖ ^ 2 ≤
          2 * C * ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J n g x i - g x i‖ ^ 2 := by
      intro n
      have e0 : ∀ x i, ‖LMPd j (fun y => J k (J n g) y i) x - LMPd j (fun y => J k g y i) x‖ ^ 2 =
          ‖LMPd j (fun y => J k (fun z i' => J n g z i' + (-1 : ℂ) * g z i') y i) x‖ ^ 2 :=
        fun x i => by rw [hsplit]
      have e2 : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J n g x i - g x i‖ ^ 2 =
          ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J n g x i + (-1 : ℂ) * g x i‖ ^ 2 := by
        refine integral_congr_ae (ae_of_all _ fun x => Finset.sum_congr rfl fun i _ => ?_)
        rw [neg_one_mul, sub_eq_add_neg]
      simp only [e0]
      rw [integral_finsetSum _ fun i _ => lm_sq_integrable (hC _ (hdL n) i j).1, Fin.sum_univ_two, e2]
      have h0 := (hC _ (hdL n) 0 j).2
      have h1 := (hC _ (hdL n) 1 j).2
      linarith
    have hz : Tendsto (fun n : ℕ => 2 * C * ∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖J n g x i - g x i‖ ^ 2) atTop (𝓝 0) := by
      have := (hJ.tendsto g hg).const_mul (2 * C)
      simpa using this
    exact squeeze_zero
      (fun n => integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hbd hz
  have hlim3 := hlim1.neg
  refine tendsto_nhds_unique (hlim2.congr fun n => step1 n) hlim3

/-- **The tensor term of the tested equation.** -/
theorem lmSliceTensor : LMSliceTensor := by
  intro c hc J hJ hX k χ T hχ hT
  have hL := lmP0C_cellL2 c χ
  have hZ := lmDivJ_cellL2 hX k hT
  obtain ⟨C, hC⟩ := hX.gradL2 k
  have hA : ∀ (h : LMSpField) (j : Fin 2), LMCellL2 c h →
      LMCellL2 c (fun x i => LMPd j (fun y => J k h y i) x) := fun h j hh i => (hC h hh i j).1
  rw [← lmP0CAdj c hc χ _ hχ hZ]
  have e : lmDivJ J k T = fun x i =>
      LMPd 0 (fun y => J k (fun y' i' => T y' i' 0) y i) x +
        LMPd 1 (fun y => J k (fun y' i' => T y' i' 1) y i) x := by
    funext x i
    simp only [lmDivJ, Fin.sum_univ_two]
  rw [e, lmIp_add_right hL (hA _ 0 (hT 0)) (hA _ 1 (hT 1)),
    lmAntiSymm c hc J hJ hX k 0 _ _ hL (hT 0), lmAntiSymm c hc J hJ hX k 1 _ _ hL (hT 1)]
  have hint : ∀ (i j : Fin 2), Integrable
      (fun x => starRingEnd ℂ (LMPd j (fun y => J k (P0C c χ) y i) x) * T x i j)
      (volume.restrict (B0579.cell c)) := fun i j => lmIp_integrable (hA _ j hL) (hT j) i
  unfold LMIp
  rw [integral_finsetSum _ fun i _ => hint i 0, integral_finsetSum _ fun i _ => hint i 1]
  simp only [Fin.sum_univ_two]
  ring

/-- The real part of the pairing. -/
theorem lmIp_re {c : ℝ} {f g : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g) :
    (LMIp c f g).re =
      ∫ x in B0579.cell c, ∑ i : Fin 2, ((f x i).re * (g x i).re + (f x i).im * (g x i).im) := by
  have hint : Integrable (fun x => ∑ i : Fin 2, starRingEnd ℂ (f x i) * g x i)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => lmIp_integrable hf hg i
  have h := Complex.reCLM.integral_comp_comm hint
  unfold LMIp
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **`Re ⟨𝒫₀ Z, u_k⟩ = -(ν N_k + R_k)` on a good slice.** -/
theorem lmPairingSlice : LMPairingSlice := by
  intro c ν μ F b G hS J hJ hX k s hs hg
  have hc : 0 < c := hS.pos_c
  obtain ⟨hb, hGc, hFc⟩ := hg
  have hu : LMCellL2 c (LMMollU J b k s) := hJ.memL2 k _ hb
  have hud : LMWeakDivFree c (LMMollU J b k s) :=
    lmJWeakDiv c hc J hJ hX k _ hb fun ψ hψ => hS.sol.divFree s hs ψ hψ
  have hTc : ∀ j : Fin 2, LMCellL2 c (fun y i => lmTens ν F G (s, y) i j) := fun j =>
    lmTens_col_cellL2 (ν := ν) ⟨hb, hGc, hFc⟩ j
  have hZ := lmDivJ_cellL2 hX k hTc
  obtain ⟨C, hC⟩ := hX.gradL2 k
  have hA : ∀ (h : LMSpField) (j : Fin 2), LMCellL2 c h →
      LMCellL2 c (fun x i => LMPd j (fun y => J k h y i) x) := fun h j hh i => (hC h hh i j).1
  have hAu : ∀ j : Fin 2, LMCellL2 c
      (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x) := fun j => hA _ j hu
  -- `𝒫₀ u_k = u_k`, and `Z` is the sum of its two columns
  have e1 : LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (LMMollU J b k s) =
      LMIp c (lmDivJ J k (fun y => lmTens ν F G (s, y))) (LMMollU J b k s) := by
    rw [lmP0CAdj c hc _ _ hZ hu]
    exact lmIp_congr_right (lmP0CFix c hc _ hu hud)
  have e2 : lmDivJ J k (fun y => lmTens ν F G (s, y)) = fun x i =>
      LMPd 0 (fun y => J k (fun y' i' => lmTens ν F G (s, y') i' 0) y i) x +
        LMPd 1 (fun y => J k (fun y' i' => lmTens ν F G (s, y') i' 1) y i) x := by
    funext x i
    simp only [lmDivJ, Fin.sum_univ_two]
  -- each column: conjugate of `LMAntiSymm`
  have e3 : ∀ j : Fin 2, LMIp c
      (fun x i => LMPd j (fun y => J k (fun y' i' => lmTens ν F G (s, y') i' j) y i) x)
      (LMMollU J b k s) = -LMIp c (fun y i => lmTens ν F G (s, y) i j)
        (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x) := by
    intro j
    rw [← lmIp_conj c (LMMollU J b k s), lmAntiSymm c hc J hJ hX k j _ _ hu (hTc j), map_neg,
      lmIp_conj]
  -- the identification `∂ⱼ J_k u_k = J_k J_k G_{·j}` and the viscous term
  have hGW : ∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => b (s, x) i)
      (fun x => (fun j y i => G (s, y) i j) j x i) := fun i j => hS.sol.weakGrad s hs i j
  have hpd2 : ∀ j : Fin 2, (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x) =
      J k (J k (fun y i => G (s, y) i j)) := fun j => by
    funext x i
    exact lmMoll_pd2_eq lmSmoothWeakPd hc hJ (f := fun y => b (s, y))
      (g := fun j y i => G (s, y) i j) hb hGc hGW k i j x
  have hvisc : ∀ j : Fin 2, LMIp c (fun y i => G (s, y) i j)
      (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x) =
      ((∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [hpd2 j]
    have h1 := hJ.selfAdj k (fun y i => G (s, y) i j) (J k (fun y i => G (s, y) i j)) (hGc j)
      (hJ.memL2 k _ (hGc j))
    have h2 : LMIp c (fun y i => G (s, y) i j) (J k (J k (fun y i => G (s, y) i j))) =
        LMIp c (J k (fun y i => G (s, y) i j)) (J k (fun y i => G (s, y) i j)) := h1.symm
    rw [h2, lmIp_self]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun x =>
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _))
  -- splitting `T = νG + F`
  have hsplit : ∀ j : Fin 2, (LMIp c (fun y i => lmTens ν F G (s, y) i j)
      (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x)).re =
      ν * (∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2) +
        (LMIp c (fun y i => F (s, y) i j)
          (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x)).re := by
    intro j
    have hνG : LMCellL2 c (fun y i => (ν : ℂ) * G (s, y) i j) := fun i => (hGc j i).const_mul _
    have e4 : (fun y i => lmTens ν F G (s, y) i j) =
        fun y i => (ν : ℂ) * G (s, y) i j + F (s, y) i j := rfl
    rw [e4, lmIp_add_left hνG (hFc j) (hAu j), lmIp_smul_left, hvisc j, Complex.add_re,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- `N_k` and `R_k`
  have hN : LMMollN c J b k s = ∑ j : Fin 2,
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (fun y i' => G (s, y) i' j) x i‖ ^ 2 := by
    have hpd : ∀ (x : ℝ × ℝ) (i j : Fin 2), LMPd j (fun y => LMMollU J b k s y i) x =
        J k (fun y i' => G (s, y) i' j) x i := fun x i j =>
      lmMoll_pd_eq (f := fun y => b (s, y)) (g := fun j y i => G (s, y) i j) hJ hb hGc hGW k i j x
    unfold LMMollN
    rw [← integral_finsetSum _ fun j _ => lm_vec_sq_integrable (hJ.memL2 k _ (hGc j))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show tnorm2 _ ^ 2 = _
    rw [tnorm2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp only [hpd, Fin.sum_univ_two]
    ring
  have hR : LMMollR c J F b k s = ∑ j : Fin 2, (LMIp c (fun y i => F (s, y) i j)
      (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x)).re := by
    simp only [lmIp_re (hFc _) (hAu _)]
    have hint : ∀ j : Fin 2, Integrable (fun x => ∑ i : Fin 2,
        ((F (s, x) i j).re * (LMPd j (fun y => J k (LMMollU J b k s) y i) x).re +
          (F (s, x) i j).im * (LMPd j (fun y => J k (LMMollU J b k s) y i) x).im))
        (volume.restrict (B0579.cell c)) := fun j => by
      refine integrable_finsetSum _ fun i _ => ?_
      exact (((hFc j i).re).integrable_mul ((hAu j i).re)).add
        (((hFc j i).im).integrable_mul ((hAu j i).im))
    rw [← integral_finsetSum _ fun j _ => hint j]
    unfold LMMollR
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Fin.sum_univ_two]
    ring
  rw [e1, e2, lmIp_add_left (hA _ 0 (hTc 0)) (hA _ 1 (hTc 1)) hu, e3 0, e3 1, Complex.add_re,
    Complex.neg_re, Complex.neg_re, hsplit 0, hsplit 1, hN, hR]
  simp only [Fin.sum_univ_two]
  ring

end UnforcedLeray.Short.IIIa
