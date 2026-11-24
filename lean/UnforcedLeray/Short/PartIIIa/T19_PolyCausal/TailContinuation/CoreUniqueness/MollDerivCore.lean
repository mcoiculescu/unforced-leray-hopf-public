import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness.ExtWeakCore
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity

/-!
# Part III-a, helper 3 of `PartIII-a:T19/3/4`: mollified weak derivative and energy identity on `(0, H')`

For truncated core causal solution data `CoreTruncData c ν H' μ F b G` and a cylinder mollifier
family `J`, the mollified field `u_k(s) = J_k b(s)` has weak time derivative
`u'_k(s) = -(μ/s) u_k(s) + 𝒫₀ Z(s)` against smooth test weights `ψ` supported in `(0, H')`.
Cutting off `(u_k, u'_k)` in time by a smooth transition function `η` equal to `1` on a
neighborhood of `tsupport w ⊂ (0, H')` and supported in `(-∞, b] ⊂ (-∞, H')` yields a global
`LMWeakDeriv` pair on `(0, ∞)`, to which `lmEnergyBridge` applies directly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `u_k = J_k b ∈ L²_loc((0, ∞); L²(cell))` for `CoreTruncData`. -/
theorem ukL2Loc_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) (s₁ s₂ : ℝ) (h1 : 0 < s₁) (h2 : s₁ < s₂) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k p.1 p.2 i) ^ 2) < ⊤ := by
  have hΦ : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k p.1 p.2 i) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((aeg_measurable_vnorm2 (fun i => hJ.measurable k b hD.measurable i)).pow_const 2)
  have hΨ : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((aeg_measurable_vnorm2 hD.measurable).pow_const 2).add
        ((aeg_measurable_tnorm2 hD.gradMeasurable).pow_const 2))
  have hsub : Icc s₁ s₂ ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le h1 hs.1
  have hgood := ae_restrict_of_ae_restrict_of_subset hsub (aeGoodSlice_trunc hD)
  refine lm_L2Loc_of_slice (K := 1) hΦ hΨ ENNReal.one_ne_top ?_ (hD.energyLoc s₁ s₂ h1 h2)
  filter_upwards [hgood] with s hs
  rw [one_mul]
  have hb := hs.1
  have hu : LMCellL2 c (LMMollU J b k s) := hJ.memL2 k _ hb
  have e1 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k s x i) ^ 2) =
      ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMMollU J b k s x i‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (lm_vec_sq_integrable hu)
      (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact lintegral_congr fun x => by rw [lm_vnorm2_sq]
  have e2 : ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ‖b (s, x) i‖ ^ 2) ≤
      ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (lm_vec_sq_integrable hb)
      (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    rw [lm_vnorm2_sq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  rw [e1]
  exact (ENNReal.ofReal_le_ofReal (hJ.contr k _ hb)).trans e2

/-- `𝒫₀ Z ∈ L²_loc((0, ∞); L²(cell))` for `CoreTruncData`. -/
theorem ytL2Loc_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hX : LMMollH1 c J) (k : ℕ) (Yt : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (hYm : ∀ i, Measurable fun p => Yt p i)
    (hYae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ∀ i : Fin 2, Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i)
    (s₁ s₂ : ℝ) (h1 : 0 < s₁) (h2 : s₁ < s₂) :
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => Yt p i) ^ 2) < ⊤ := by
  have hc : 0 < c := hD.pos_c
  obtain ⟨K, hK0, hK⟩ := lmDivJ_norm_le hX k
  have hΦ : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (vnorm2 (fun i => Yt p i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hYm).pow_const 2)
  have hA : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((aeg_measurable_vnorm2 hD.measurable).pow_const 2).add
        ((aeg_measurable_tnorm2 hD.gradMeasurable).pow_const 2))
  have hB : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (tnorm2 (F p) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((aeg_measurable_tnorm2 hD.meas).pow_const 2)
  have hΨ : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (2 * ν ^ 2) * ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (F p) ^ 2) :=
    (hA.const_mul _).add (hB.const_mul _)
  have hfin : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      (ENNReal.ofReal (2 * ν ^ 2) * ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (F p) ^ 2)) < ⊤ := by
    rw [lintegral_add_left (hA.const_mul _), lintegral_const_mul _ hA, lintegral_const_mul _ hB]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hD.energyLoc s₁ s₂ h1 h2), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hD.l2loc s₁ s₂ h1 h2)⟩
  have hsub : Icc s₁ s₂ ⊆ Ioi (0 : ℝ) := fun s hs => lt_of_lt_of_le h1 hs.1
  have hgood := ae_restrict_of_ae_restrict_of_subset hsub (aeGoodSlice_trunc hD)
  have hYr := ae_restrict_of_ae_restrict_of_subset hsub hYae
  refine lm_L2Loc_of_slice (K := ENNReal.ofReal K) hΦ hΨ ENNReal.ofReal_ne_top ?_ hfin
  filter_upwards [hgood, hYr] with s hs hYs
  have hT := fun j => lmTens_col_cellL2 (ν := ν) hs j
  have hZ := lmDivJ_cellL2 hX k hT
  have hP := lmP0C_cellL2 c (lmDivJ J k (fun y => lmTens ν F G (s, y)))
  have e1 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => Yt (s, x) i) ^ 2) =
      ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2,
        ‖P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (lm_vec_sq_integrable hP)
      (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hYs] with x hx
    rw [lm_vnorm2_sq]
    simp only [hx]
  have hTint : Integrable (fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖lmTens ν F G (s, x) i j‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => lm_sq_integrable (hT j i)
  have e2 : ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ‖lmTens ν F G (s, x) i j‖ ^ 2) ≤ ∫⁻ x in B0579.cell c,
      (ENNReal.ofReal (2 * ν ^ 2) * ENNReal.ofReal (vnorm2 (b (s, x)) ^ 2 + tnorm2 (G (s, x)) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal (tnorm2 (F (s, x)) ^ 2)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hTint (ae_of_all _ fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hterm : ∀ i j : Fin 2, ‖lmTens ν F G (s, x) i j‖ ^ 2 ≤
        2 * ν ^ 2 * ‖G (s, x) i j‖ ^ 2 + 2 * ‖F (s, x) i j‖ ^ 2 := fun i j => by
      refine (lm_norm_add_sq_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      linarith
    have hsum : ∑ i : Fin 2, ∑ j : Fin 2, ‖lmTens ν F G (s, x) i j‖ ^ 2 ≤
        2 * ν ^ 2 * tnorm2 (G (s, x)) ^ 2 + 2 * tnorm2 (F (s, x)) ^ 2 := by
      simp only [lm_tnorm2_sq, Fin.sum_univ_two]
      have h00 := hterm 0 0
      have h01 := hterm 0 1
      have h10 := hterm 1 0
      have h11 := hterm 1 1
      linarith
    have hv : 0 ≤ 2 * ν ^ 2 * vnorm2 (b (s, x)) ^ 2 := by positivity
    nlinarith
  have hW0 : 0 ≤ ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
      ‖lmTens ν F G (s, x) i j‖ ^ 2 := integral_nonneg fun x =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [e1]
  calc _ ≤ ENNReal.ofReal (K * ∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖lmTens ν F G (s, x) i j‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal ((lmP0CContr c hc _ hZ).trans (hK _ hT))
    _ = ENNReal.ofReal K * ENNReal.ofReal (∫ x in B0579.cell c, ∑ i : Fin 2, ∑ j : Fin 2,
        ‖lmTens ν F G (s, x) i j‖ ^ 2) := ENNReal.ofReal_mul hK0
    _ ≤ _ := by gcongr

/-- `Re ⟨𝒫₀ Z, u_k⟩ = -(ν N_k + R_k)` on a good slice for `CoreTruncData`. -/
theorem pairingSlice_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (hX : LMMollH1 c J) (k : ℕ) {s : ℝ} (hs : 0 < s)
    (hg : LMGoodSlice c F G b s) :
    (LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (LMMollU J b k s)).re =
      -(ν * LMMollN c J b k s + LMMollR c J F b k s) := by
  have hc : 0 < c := hD.pos_c
  obtain ⟨hb, hGc, hFc⟩ := hg
  have hu : LMCellL2 c (LMMollU J b k s) := hJ.memL2 k _ hb
  have hud : LMWeakDivFree c (LMMollU J b k s) :=
    lmJWeakDiv c hc J hJ hX k _ hb fun ψ hψ => hD.divFree s hs ψ hψ
  have hTc : ∀ j : Fin 2, LMCellL2 c (fun y i => lmTens ν F G (s, y) i j) := fun j =>
    lmTens_col_cellL2 (ν := ν) ⟨hb, hGc, hFc⟩ j
  have hZ := lmDivJ_cellL2 hX k hTc
  obtain ⟨C, hC⟩ := hX.gradL2 k
  have hA : ∀ (h : LMSpField) (j : Fin 2), LMCellL2 c h →
      LMCellL2 c (fun x i => LMPd j (fun y => J k h y i) x) := fun h j hh i => (hC h hh i j).1
  have hAu : ∀ j : Fin 2, LMCellL2 c
      (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x) := fun j => hA _ j hu
  have e1 : LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (LMMollU J b k s) =
      LMIp c (lmDivJ J k (fun y => lmTens ν F G (s, y))) (LMMollU J b k s) := by
    rw [lmP0CAdj c hc _ _ hZ hu]
    exact lmIp_congr_right (lmP0CFix c hc _ hu hud)
  have e2 : lmDivJ J k (fun y => lmTens ν F G (s, y)) = fun x i =>
      LMPd 0 (fun y => J k (fun y' i' => lmTens ν F G (s, y') i' 0) y i) x +
        LMPd 1 (fun y => J k (fun y' i' => lmTens ν F G (s, y') i' 1) y i) x := by
    funext x i
    simp only [lmDivJ, Fin.sum_univ_two]
  have e3 : ∀ j : Fin 2, LMIp c
      (fun x i => LMPd j (fun y => J k (fun y' i' => lmTens ν F G (s, y') i' j) y i) x)
      (LMMollU J b k s) = -LMIp c (fun y i => lmTens ν F G (s, y) i j)
        (fun x i => LMPd j (fun y => J k (LMMollU J b k s) y i) x) := by
    intro j
    rw [← lmIp_conj c (LMMollU J b k s), lmAntiSymm c hc J hJ hX k j _ _ hu (hTc j), map_neg,
      lmIp_conj]
  have hGW : ∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => b (s, x) i)
      (fun x => (fun j y i => G (s, y) i j) j x i) := fun i j => hD.weakGrad s hs i j
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

/-- Weak derivative representation of `u_k = LMMollU J b k` against test weights supported in
`(0, H')`, together with the a.e. slice pairing identity. -/
theorem mollDeriv_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) :
    ∃ u' : ℝ → LMSpField,
      (∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => LMMollU J b k p.1 p.2 i) ∧
      (∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u' p.1 p.2 i) ∧
      (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k p.1 p.2 i) ^ 2) < ⊤) ∧
      (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
        ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => u' p.1 p.2 i) ^ 2) < ⊤) ∧
      (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        LMCellL2 c (LMMollU J b k s) ∧ LMCellL2 c (u' s)) ∧
      (∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo 0 H' →
        ∀ χ : LMSpField, LMCellL2 c χ →
          ∫ s in Ioi (0 : ℝ), ((deriv ψ s : ℝ) : ℂ) * LMIp c χ (LMMollU J b k s) =
            -∫ s in Ioi (0 : ℝ), (ψ s : ℂ) * LMIp c χ (u' s)) ∧
      (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        2 * (LMIp c (u' s) (LMMollU J b k s)).re =
          -(2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
            2 * LMMollR c J F b k s)) := by
  have hc : 0 < c := hD.pos_c
  have hX : LMMollH1 c J := ⟨hJ.gradL2, hJ.divFreeWeak⟩
  have hTm : ∀ i j, Measurable fun p => lmTens ν F G p i j := fun i j =>
    (measurable_const.mul (hD.gradMeasurable i j)).add (hD.meas i j)
  obtain ⟨Y, hYm, hYe⟩ := lmDivJMeasRep c hc J hJ k (lmTens ν F G) hTm
  obtain ⟨Yt, hYtm, hYte⟩ := lmP0Rep c hc Y hYm
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), LMGoodSlice c F G b s :=
    aeGoodSlice_trunc hD
  have hYg : ∀ s, LMGoodSlice c F G b s → ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i := by
    intro s hs
    have e : (fun y => Y (s, y)) = lmDivJ J k (fun y => lmTens ν F G (s, y)) := by
      funext x i
      exact hYe s (fun j => lmTens_col_cellL2 hs j) x i
    rw [← e]
    exact hYte s
  have hYae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      ∀ i : Fin 2, Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i := by
    filter_upwards [hgood] with s hs using hYg s hs
  set u : ℝ → LMSpField := LMMollU J b k with hu
  have hum : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i := fun i =>
    hJ.measurable k b hD.measurable i
  have huL := ukL2Loc_trunc hD hJ k
  have hYL := ytL2Loc_trunc hD hX k Yt hYtm hYae
  have hu'm : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => lmUDer μ u Yt p.1 p.2 i := fun i =>
    (((measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)).neg).mul
      (hum i)).add (hYtm i)
  have hu'L : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => lmUDer μ u Yt p.1 p.2 i) ^ 2) < ⊤ := fun s₁ s₂ h1 h2 =>
    lmUDerL2Loc c μ u Yt hum hYtm s₁ s₂ h1 h2 (huL s₁ s₂ h1 h2) (hYL s₁ s₂ h1 h2)
  have huc : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (u s) := fun s hs =>
    hJ.memL2 k _ hs.1
  have hZc : ∀ s, LMGoodSlice c F G b s →
      LMCellL2 c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) := fun s _ =>
    lmP0C_cellL2 c _
  have hYc : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (fun x i => Yt (s, x) i) := by
    intro s hs i
    refine (hZc s hs i).ae_eq ?_
    filter_upwards [hYg s hs] with x hx
    exact (hx i).symm
  have hu'c : ∀ s, LMGoodSlice c F G b s → LMCellL2 c (lmUDer μ u Yt s) := by
    intro s hs i
    exact ((huc s hs i).const_mul _).add (hYc s hs i)
  refine ⟨lmUDer μ u Yt, hum, hu'm, huL, hu'L, ?_, ?_, ?_⟩
  · filter_upwards [hgood] with s hs
    exact ⟨huc s hs, hu'c s hs⟩
  · intro ψ hψ hcs hts χ hχ
    have hts_pos : tsupport ψ ⊆ Ioi (0 : ℝ) := fun s hs => (hts hs).1
    have hP0χ : LMWeakDivFree c (P0C c χ) := fun ψ' hψ' =>
      p0DivFreeC c hc χ ψ' hψ'
    obtain ⟨hre, him⟩ := lmH1Test c hc J hJ hX k (P0C c χ) (lmP0C_cellL2 c χ) hP0χ
    have H0 := sliceTested_trunc hD hψ hcs hts (J k (P0C c χ)) hre him
    have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hsdψ : tsupport (deriv ψ) ⊆ Ioi (0 : ℝ) :=
      (tsupport_deriv_subset (𝕜 := ℝ)).trans hts_pos
    have hI1 := lmIpWeightedInt c χ u (deriv ψ) hχ hum huL hdψ hcs.deriv hsdψ
    have hI2 := lmIpWeightedInt c χ (lmUDer μ u Yt) ψ hχ hu'm hu'L hψ.continuous hcs hts_pos
    have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (-(((deriv ψ s : ℝ) : ℂ) * LMIp c (J k (P0C c χ)) (fun y => b (s, y))) +
          ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * LMIp c (J k (P0C c χ)) (fun y => b (s, y))) +
          ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
            starRingEnd ℂ (LMPd j (fun y => J k (P0C c χ) y i) x) * lmTens ν F G (s, x) i j) =
        -(((deriv ψ s : ℝ) : ℂ) * LMIp c χ (u s)) -
          ((ψ s : ℝ) : ℂ) * LMIp c χ (lmUDer μ u Yt s) := by
      filter_upwards [hgood, ae_restrict_mem measurableSet_Ioi] with s hs hs0
      have hs0' : (0 : ℝ) < s := hs0
      have hP1 : LMIp c (J k (P0C c χ)) (fun y => b (s, y)) = LMIp c χ (u s) :=
        lmSliceScalar lmP0CAdj lmP0CFix lmJWeakDiv hc hJ hX k hχ hs.1
          (fun ψ' hψ' => hD.divFree s hs0' ψ' hψ')
      have hQ := lmSliceTensor c hc J hJ hX k χ (fun y => lmTens ν F G (s, y)) hχ
        (fun j => lmTens_col_cellL2 hs j)
      have hYp : LMIp c χ (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) =
          LMIp c χ (fun x i => Yt (s, x) i) :=
        lmIp_congr_right (by
          filter_upwards [hYg s hs] with x hx i
          exact (hx i).symm)
      have hsplit : LMIp c χ (lmUDer μ u Yt s) =
          -(μ / (s : ℂ)) * LMIp c χ (u s) + LMIp c χ (fun x i => Yt (s, x) i) := by
        have h1 : lmUDer μ u Yt s = fun x i => -(μ / (s : ℂ)) * u s x i + Yt (s, x) i := rfl
        have hsm : LMCellL2 c (fun x i => -(μ / (s : ℂ)) * u s x i) := fun i =>
          (huc s hs i).const_mul _
        rw [h1, lmIp_add_right hχ hsm (hYc s hs), lmIp_smul_right]
      rw [hP1, hQ, hYp, hsplit]
      ring
    rw [integral_congr_ae hae, integral_sub hI1.fun_neg hI2, integral_neg] at H0
    linear_combination -H0
  · filter_upwards [hgood, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    have hs0' : (0 : ℝ) < s := hs0
    have hP := pairingSlice_trunc hD hJ hX k hs0' hs
    have hYp : LMIp c (fun x i => Yt (s, x) i) (u s) =
        LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (u s) :=
      lmIp_congr_left (hYg s hs)
    have hsm : LMCellL2 c (fun x i => -(μ / (s : ℂ)) * u s x i) := fun i =>
      (huc s hs i).const_mul _
    have hsplit : LMIp c (lmUDer μ u Yt s) (u s) =
        starRingEnd ℂ (-(μ / (s : ℂ))) * LMIp c (u s) (u s) +
          LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (u s) := by
      have h1 : lmUDer μ u Yt s = fun x i => -(μ / (s : ℂ)) * u s x i + Yt (s, x) i := rfl
      rw [h1, lmIp_add_left hsm (hYc s hs) (huc s hs), lmIp_smul_left, hYp]
    have hE' : LMIp c (u s) (u s) = ((LMMollE c J b k s : ℝ) : ℂ) := lmIp_self c (u s)
    rw [hsplit, hE', Complex.add_re, hP]
    have hre : (starRingEnd ℂ (-(μ / (s : ℂ))) * ((LMMollE c J b k s : ℝ) : ℂ)).re =
        -(μ.re / s) * LMMollE c J b k s := by
      rw [Complex.re_mul_ofReal, Complex.conj_re, Complex.neg_re, Complex.div_ofReal_re]
    rw [hre]
    ring

/-- The mollified energy identity on `(0, H')`: for any smooth `w` with `tsupport w ⊆ Ioo 0 H'`,
`∫ w' E_k = ∫ w (2 Re μ s⁻¹ E_k + 2 ν N_k + 2 R_k)`. -/
theorem mollEnergyIdentity_trunc {c ν H' : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hD : CoreTruncData c ν H' μ F b G) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hcs : HasCompactSupport w) (hts : tsupport w ⊆ Ioo 0 H') (k : ℕ) :
    ∫ s in Ioi (0 : ℝ), deriv w s * LMMollE c J b k s =
      ∫ s in Ioi (0 : ℝ), w s * (2 * μ.re / s * LMMollE c J b k s +
        2 * ν * LMMollN c J b k s + 2 * LMMollR c J F b k s) := by
  obtain ⟨u', hum, hu'm, huL, hu'L, hcell, hid_core, hpair⟩ := mollDeriv_trunc hD hJ k
  set u : ℝ → LMSpField := LMMollU J b k
  obtain ⟨s₁, s₂, _hs₁, hs₂H', hsub_w⟩ := exists_Icc_of_tsupport_Ioo hD.pos_H' hcs hts
  set a : ℝ := (2 * s₂ + H') / 3
  set b_cut : ℝ := (s₂ + 2 * H') / 3
  have hs₂a : s₂ < a := by unfold a; linarith
  have hab : a < b_cut := by unfold a b_cut; linarith
  have hbH' : b_cut < H' := by unfold b_cut; linarith
  have hba_pos : 0 < b_cut - a := sub_pos.2 hab
  set η : ℝ → ℝ := fun s => Real.smoothTransition ((b_cut - s) / (b_cut - a))
  have hη : ContDiff ℝ ∞ η :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const (b_cut - a))
  have hη_one : ∀ s ≤ a, η s = 1 := by
    intro s hs
    exact Real.smoothTransition.one_of_one_le ((one_le_div hba_pos).2 (by linarith))
  have hη_deriv_zero : ∀ s < a, deriv η s = 0 := by
    intro s hs
    have hev : η =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      exact hη_one t (le_of_lt ht)
    rw [hev.deriv_eq, deriv_const]
  have hη_zero : ∀ s, b_cut ≤ s → η s = 0 := by
    intro s hs
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hba_pos.le)
  have hη_ts : tsupport η ⊆ Iic b_cut :=
    closure_minimal (fun s hs => le_of_not_gt fun hgt => hs (hη_zero s hgt.le)) isClosed_Iic
  have hη_norm : ∀ s, ‖(η s : ℂ)‖ ≤ 1 := by
    intro s
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  set u_η : ℝ → LMSpField := fun s x i => (η s : ℂ) * u s x i
  set u'_η : ℝ → LMSpField := fun s x i => (η s : ℂ) * u' s x i + ((deriv η s : ℝ) : ℂ) * u s x i
  have huηm : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u_η p.1 p.2 i := fun i =>
    ((Complex.measurable_ofReal.comp (hη.continuous.measurable)).comp measurable_fst).mul (hum i)
  have hu'ηm : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u'_η p.1 p.2 i := fun i =>
    (((Complex.measurable_ofReal.comp (hη.continuous.measurable)).comp measurable_fst).mul
      (hu'm i)).add
      (((Complex.measurable_ofReal.comp ((hη.continuous_deriv (by simp)).measurable)).comp
        measurable_fst).mul (hum i))
  have huηL : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
      ∫⁻ p in Icc t₁ t₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (fun i => u_η p.1 p.2 i) ^ 2) < ⊤ := by
    intro t₁ t₂ ht₁ ht₂
    refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) (huL t₁ t₂ ht₁ ht₂)
    simp only [lm_vnorm2_sq, u_η]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_pow]
    have h1 := hη_norm p.1
    have h2 : ‖(η p.1 : ℂ)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (η p.1 : ℂ)]
    nlinarith [sq_nonneg ‖u p.1 p.2 i‖]
  have hu'ηL : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
      ∫⁻ p in Icc t₁ t₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (fun i => u'_η p.1 p.2 i) ^ 2) < ⊤ := by
    intro t₁ t₂ ht₁ ht₂
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := deriv η) (hη.continuous_deriv (by simp)).continuousOn (s := Icc t₁ t₂)
    set M' : ℝ := max M 0
    have hM'0 : 0 ≤ M' := le_max_right _ _
    have hmU : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hum).pow_const 2)
    have hmU' : Measurable fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (vnorm2 (fun i => u' p.1 p.2 i) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((aeg_measurable_vnorm2 hu'm).pow_const 2)
    have hS : MeasurableSet (Icc t₁ t₂ ×ˢ B0579.cell c) :=
      measurableSet_Icc.prod (B0579.measurableSet_cell c)
    have hle : ∫⁻ p in Icc t₁ t₂ ×ˢ B0579.cell c,
          ENNReal.ofReal (vnorm2 (fun i => u'_η p.1 p.2 i) ^ 2) ≤
        ∫⁻ p in Icc t₁ t₂ ×ˢ B0579.cell c,
          (ENNReal.ofReal 2 * ENNReal.ofReal (vnorm2 (fun i => u' p.1 p.2 i) ^ 2) +
            ENNReal.ofReal (2 * M' ^ 2) * ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2)) := by
      refine setLIntegral_mono' hS fun p hp => ?_
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [lm_vnorm2_sq, Fin.sum_univ_two, u'_η]
      have hdM : ‖((deriv η p.1 : ℝ) : ℂ)‖ ≤ M' := by
        rw [Complex.norm_real]
        exact (hM p.1 hp.1).trans (le_max_left _ _)
      have hdM2 : ‖((deriv η p.1 : ℝ) : ℂ)‖ ^ 2 ≤ M' ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdM 2
      have hη1 := hη_norm p.1
      have hη2 : ‖(η p.1 : ℂ)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (η p.1 : ℂ)]
      have hterm : ∀ i : Fin 2,
          ‖(η p.1 : ℂ) * u' p.1 p.2 i + ((deriv η p.1 : ℝ) : ℂ) * u p.1 p.2 i‖ ^ 2 ≤
            2 * ‖u' p.1 p.2 i‖ ^ 2 + 2 * M' ^ 2 * ‖u p.1 p.2 i‖ ^ 2 := fun i => by
        refine (lm_norm_add_sq_le _ _).trans ?_
        rw [norm_mul, norm_mul, mul_pow, mul_pow]
        nlinarith [sq_nonneg ‖u' p.1 p.2 i‖, sq_nonneg ‖u p.1 p.2 i‖]
      linarith [hterm 0, hterm 1]
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_add_left (hmU'.const_mul _), lintegral_const_mul _ hmU', lintegral_const_mul _ hmU]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu'L t₁ t₂ ht₁ ht₂),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (huL t₁ t₂ ht₁ ht₂)⟩
  have hWD : LMWeakDeriv c u_η u'_η := by
    refine ⟨huηm, hu'ηm, huηL, hu'ηL, fun ψ hψ hψc hψts χ hχ => ?_⟩
    set ψη : ℝ → ℝ := fun s => ψ s * η s
    have hψη : ContDiff ℝ ∞ ψη := hψ.mul hη
    have hψηc : HasCompactSupport ψη := hψc.mul_right
    have hψηts : tsupport ψη ⊆ Ioo 0 H' := fun s hs =>
      ⟨hψts (tsupport_mul_subset_left hs),
        lt_of_le_of_lt (hη_ts (tsupport_mul_subset_right hs)) hbH'⟩
    have hcore_ψη := hid_core ψη hψη hψηc hψηts χ hχ
    have hI1 := lmIpWeightedInt c χ u_η (deriv ψ) hχ huηm huηL
      (hψ.continuous_deriv (by simp)) hψc.deriv (tsupport_deriv_subset.trans hψts)
    have hI2 := lmIpWeightedInt c χ u'_η ψ hχ hu'ηm hu'ηL hψ.continuous hψc hψts
    have hI3 := lmIpWeightedInt c χ u (deriv ψη) hχ hum huL
      (hψη.continuous_deriv (by simp)) hψηc.deriv
      (tsupport_deriv_subset.trans (fun s hs => (hψηts hs).1))
    have hI4 := lmIpWeightedInt c χ u' ψη hχ hu'm hu'L hψη.continuous hψηc
      (fun s hs => (hψηts hs).1)
    have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ((deriv ψ s : ℝ) : ℂ) * LMIp c χ (u_η s) + ((ψ s : ℝ) : ℂ) * LMIp c χ (u'_η s) =
          ((deriv ψη s : ℝ) : ℂ) * LMIp c χ (u s) + ((ψη s : ℝ) : ℂ) * LMIp c χ (u' s) := by
      filter_upwards [hcell] with s ⟨huc, hu'c⟩
      have h1 : LMIp c χ (u_η s) = (η s : ℂ) * LMIp c χ (u s) := lmIp_smul_right _ _ _ _
      have h2 : LMIp c χ (u'_η s) =
          (η s : ℂ) * LMIp c χ (u' s) + ((deriv η s : ℝ) : ℂ) * LMIp c χ (u s) := by
        have hsm1 : LMCellL2 c (fun x i => (η s : ℂ) * u' s x i) := fun i => (hu'c i).const_mul _
        have hsm2 : LMCellL2 c (fun x i => ((deriv η s : ℝ) : ℂ) * u s x i) := fun i => (huc i).const_mul _
        rw [show u'_η s = fun x i => (η s : ℂ) * u' s x i + ((deriv η s : ℝ) : ℂ) * u s x i from rfl,
          lmIp_add_right hχ hsm1 hsm2, lmIp_smul_right, lmIp_smul_right]
      have hd : deriv ψη s = deriv ψ s * η s + ψ s * deriv η s :=
        deriv_mul (hψ.differentiable (by simp)).differentiableAt
          (hη.differentiable (by simp)).differentiableAt
      rw [h1, h2, hd]
      simp only [ψη]
      push_cast
      ring
    have hint_eq := integral_congr_ae hae
    rw [integral_add hI1 hI2, integral_add hI3 hI4] at hint_eq
    linear_combination hint_eq + hcore_ψη
  have hts_pos : tsupport w ⊆ Ioi (0 : ℝ) := fun s hs => (hts hs).1
  have hbridge := lmEnergyBridge c hD.pos_c u_η u'_η hWD w hw hcs hts_pos
  have hLHS : (fun s => deriv w s * LMMollE c J b k s) =
      fun s => deriv w s * ∫ x in B0579.cell c, vnorm2 (u_η s x) ^ 2 := by
    funext s
    by_cases hs : s ∈ Icc s₁ s₂
    · have hsa : s < a := lt_of_le_of_lt hs.2 hs₂a
      have hη1 : η s = 1 := hη_one s hsa.le
      have hu_eq : u_η s = u s := by
        funext x i
        simp [u_η, hη1]
      rw [hu_eq]
      rfl
    · rw [(weight_zero_of_not_mem_Icc hsub_w hs).2, zero_mul, zero_mul]
  rw [hLHS, hbridge, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hpair] with s hs_pair
  by_cases hs : s ∈ Icc s₁ s₂
  · have hsa : s < a := lt_of_le_of_lt hs.2 hs₂a
    have hη1 : η s = 1 := hη_one s hsa.le
    have hdη0 : deriv η s = 0 := hη_deriv_zero s hsa
    have hu_eq : u_η s = u s := by funext x i; simp [u_η, hη1]
    have hu'_eq : u'_η s = u' s := by funext x i; simp [u'_η, hη1, hdη0]
    rw [hu_eq, hu'_eq, hs_pair]
    ring
  · rw [(weight_zero_of_not_mem_Icc hsub_w hs).1, zero_mul, neg_zero, zero_mul]

end UnforcedLeray.Short.IIIa
