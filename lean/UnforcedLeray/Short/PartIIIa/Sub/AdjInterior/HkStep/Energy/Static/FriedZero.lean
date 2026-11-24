import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Reg

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/2`: Friedrichs' commutator at level zero (`StFriedZero`)

Source of record: `the November 2 reference manuscript` lines 3060-3071 (the
regularized transport term; SP 3044-3047, the weight is translation quasi-invariant, through
`CellConvBound`).  From the pointwise bound `StFriedPointwise`, `|stFried n a f| ≤ L K_n ⋆ |f|`, the
weighted Young inequality `CellConvBound` for the kernel `K_n = Σ_l |∂_lρ_n| ‖·‖` and the moment
bound `StMolMoment` (`∫ K_n ≤ 2 C`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`StFriedZero` from its leaves.** -/
theorem stFriedZero_of (hCB : CellConvBound) (hMom : StMolMoment) (hPw : StFriedPointwise) :
    StFriedZero := by
  intro c m hc
  obtain ⟨C₁, hC₁0, hC₁⟩ := hCB c m hc
  obtain ⟨Cm, hCm⟩ := hMom
  have hCm0 : 0 ≤ max Cm 0 := le_max_right _ _
  refine ⟨C₁ * (2 * max Cm 0), mul_nonneg hC₁0 (mul_nonneg zero_le_two hCm0), ?_⟩
  intro n a A L f hac hab hlip hfp hfm
  obtain ⟨hcont, hpt⟩ := hPw c m n a A L f hc hac hab hlip hfp hfm
  have hL : 0 ≤ L := by
    have h := hlip 0 ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ))
    have hn : ‖((0 : ℝ), (0 : ℝ)) - ((1 : ℝ), (0 : ℝ))‖ = 1 := by
      simp [Prod.norm_def]
    rw [hn, mul_one] at h
    exact (abs_nonneg _).trans h
  -- the kernel `K_n`
  have hKc : Continuous (fun y : ℝ × ℝ => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖) :=
    continuous_finset_sum _ fun l _ => ((hCm n l).1.abs).mul continuous_norm
  have hK1 : ∀ y : ℝ × ℝ, 1 < ‖y‖ → (∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖) = 0 := by
    intro y hy
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [(hCm n l).2.1 y hy, abs_zero, zero_mul]
  have hKnn : ∀ y : ℝ × ℝ, 0 ≤ ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ :=
    fun y => Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hKint : ∫ y, |∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖| ≤ 2 * max Cm 0 := by
    have e : (fun y : ℝ × ℝ => |∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖|) =
        fun y => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖ :=
      funext fun y => abs_of_nonneg (hKnn y)
    rw [e, integral_finset_sum _ fun l _ => (hCm n l).2.2.1]
    calc ∑ l : Fin 2, ∫ y, |B0579.pd l (molKer n) y| * ‖y‖ ≤ ∑ _l : Fin 2, max Cm 0 :=
          Finset.sum_le_sum fun l _ => ((hCm n l).2.2.2).trans (le_max_left _ _)
      _ = 2 * max Cm 0 := by simp
  have hKint0 : 0 ≤ ∫ y, |∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖| :=
    integral_nonneg fun _ => abs_nonneg _
  -- the field `|f|`
  have hfnp : ∀ x : ℝ × ℝ, (fun y => ((‖f y‖ : ℝ) : ℂ)) (x.1 + c, x.2) =
      (fun y => ((‖f y‖ : ℝ) : ℂ)) x := fun x => by
    simp only
    rw [hfp x]
  have hfnm : MemLp (fun y => ((‖f y‖ : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) := hfm.norm.ofReal
  have hfnx : xNorm c (-m) (fun y => ((‖f y‖ : ℝ) : ℂ)) = xNorm c (-m) f := by
    unfold xNorm
    exact eLpNorm_congr_norm_ae (ae_of_all _ fun y => by simp)
  obtain ⟨hcm, hcb⟩ := hC₁ _ _ hKc hK1 hfnp hfnm
  have hle : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), ‖stFried n a f x‖ ≤
      L * ‖cellConv (fun y => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖)
        (fun y => ((‖f y‖ : ℝ) : ℂ)) x‖ := ae_of_all _ hpt
  refine ⟨hcm.of_le_mul hcont.aestronglyMeasurable hle, ?_⟩
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hle 2
  have hfin := hcm.eLpNorm_lt_top.ne
  have h2 : (xNorm c (-m) (stFried n a f)).toReal ≤
      L * (xNorm c (-m) (cellConv (fun y => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖)
        (fun y => ((‖f y‖ : ℝ) : ℂ)))).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at this
  have hffin : xNorm c (-m) (fun y => ((‖f y‖ : ℝ) : ℂ)) ≠ ⊤ := hfnm.eLpNorm_lt_top.ne
  have h3 : (xNorm c (-m) (cellConv (fun y => ∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖)
        (fun y => ((‖f y‖ : ℝ) : ℂ)))).toReal ≤
      (C₁ * ∫ y, |∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖|) * (xNorm c (-m) f).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hffin) hcb
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC₁0 hKint0), hfnx] at this
  have hf0 : 0 ≤ (xNorm c (-m) f).toReal := ENNReal.toReal_nonneg
  have h4 : (C₁ * ∫ y, |∑ l : Fin 2, |B0579.pd l (molKer n) y| * ‖y‖|) * (xNorm c (-m) f).toReal ≤
      (C₁ * (2 * max Cm 0)) * (xNorm c (-m) f).toReal :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKint hC₁0) hf0
  calc (xNorm c (-m) (stFried n a f)).toReal
      ≤ L * ((C₁ * (2 * max Cm 0)) * (xNorm c (-m) f).toReal) :=
        h2.trans (mul_le_mul_of_nonneg_left (h3.trans h4) hL)
    _ = C₁ * (2 * max Cm 0) * L * (xNorm c (-m) f).toReal := by ring

end UnforcedLeray.Short.IIIa
