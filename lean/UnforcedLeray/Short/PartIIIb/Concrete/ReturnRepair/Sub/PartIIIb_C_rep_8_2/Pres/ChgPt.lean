import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef

/-!
# `WardEXYChgPt`: the pointwise change of the Ward residual (`PartIII-b:C/rep/8/2/pres/1`)

Source: `the November 2 reference manuscript`, 4276-4282 (the four Ward terms
`2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX+DXᵀ)∇p`), with the algebra of `PresCoef.lean`
(`WardEXYChgPt`).  Pure algebra: no differentiability is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Elementary estimates on `Space = EuclideanSpace ℝ (Fin 3)` -/

lemma chgPt_norm_le_three (v : Space) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_three] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  have a0 := abs_nonneg (v 0)
  have a1 := abs_nonneg (v 1)
  have a2 := abs_nonneg (v 2)
  have hn := norm_nonneg v
  have hsq : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [h]
    nlinarith [mul_nonneg a0 a1, mul_nonneg a1 a2, mul_nonneg a0 a2, sq_abs (v 0),
      sq_abs (v 1), sq_abs (v 2)]
  nlinarith [hsq, hn, add_nonneg (add_nonneg a0 a1) a2]

lemma chgPt_abs_coord_le (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le v i

lemma chgPt_single_le {f : Fin 3 → Fin 3 → ℝ} (hf : ∀ j l, 0 ≤ f j l) (j l : Fin 3) :
    f j l ≤ ∑ j' : Fin 3, ∑ l' : Fin 3, f j' l' := by
  calc f j l ≤ ∑ l' : Fin 3, f j l' :=
        Finset.single_le_sum (fun l' _ => hf j l') (Finset.mem_univ l)
    _ ≤ ∑ j' : Fin 3, ∑ l' : Fin 3, f j' l' :=
        Finset.single_le_sum (f := fun j' => ∑ l' : Fin 3, f j' l')
          (fun j' _ => Finset.sum_nonneg (fun l' _ => hf j' l')) (Finset.mem_univ j)

/-- The jet density bounds each of its summands. -/
lemma chgPt_jet_bounds (X Y : Space → Space) (y : Space) :
    ‖fderiv ℝ Y y‖ ≤ meanJetDens X Y y ∧
    (∀ j : Fin 3, ‖physPd X j y‖ ≤ meanJetDens X Y y) ∧
    (∀ j l : Fin 3, ‖physPd2 X j l y‖ ≤ meanJetDens X Y y) := by
  have hA := norm_nonneg (fderiv ℝ Y y)
  have hS1 : 0 ≤ ∑ j : Fin 3, ‖physPd X j y‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hS2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 X j l y‖ :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · unfold meanJetDens; linarith
  · intro j
    have h : ‖physPd X j y‖ ≤ ∑ j' : Fin 3, ‖physPd X j' y‖ :=
      Finset.single_le_sum (f := fun j' => ‖physPd X j' y‖) (fun j' _ => norm_nonneg _)
        (Finset.mem_univ j)
    unfold meanJetDens; linarith
  · intro j l
    have h : ‖physPd2 X j l y‖ ≤ ∑ j' : Fin 3, ∑ l' : Fin 3, ‖physPd2 X j' l' y‖ :=
      chgPt_single_le (f := fun j l => ‖physPd2 X j l y‖) (fun j l => norm_nonneg _) j l
    unfold meanJetDens; linarith

/-- The coefficient-change density bounds each of its summands. -/
lemma chgPt_coef_bounds (u₁ u₂ : Space → Space) (y : Space) :
    ‖u₁ y - u₂ y‖ ≤ coefChgDens u₁ u₂ y ∧
    (∀ j : Fin 3, ‖physPd u₁ j y - physPd u₂ j y‖ ≤ coefChgDens u₁ u₂ y) ∧
    (∀ j l : Fin 3, ‖physPd2 u₁ j l y - physPd2 u₂ j l y‖ ≤ coefChgDens u₁ u₂ y) := by
  have hA := norm_nonneg (u₁ y - u₂ y)
  have hB := norm_nonneg (fderiv ℝ u₁ y - fderiv ℝ u₂ y)
  have hC := norm_nonneg (secondJet u₁ y - secondJet u₂ y)
  refine ⟨?_, fun j => ?_, fun j l => ?_⟩
  · unfold coefChgDens; linarith
  · have := norm_physPd_sub_le u₁ u₂ y j
    unfold coefChgDens; linarith
  · have := norm_physPd2_sub_le u₁ u₂ y j l
    unfold coefChgDens; linarith

/-! ## The four Ward terms -/

/-- Product estimate: `|a_j a_l - b_j b_l| ≤ c(|a| + |b|)` when `|a - b| ≤ c`. -/
lemma chgPt_prod_le (a b : Space) (c : ℝ) (hc : 0 ≤ c) (hab : ‖a - b‖ ≤ c) (j l : Fin 3) :
    |a j * a l - b j * b l| ≤ c * (‖a‖ + ‖b‖) := by
  have e : a j * a l - b j * b l = (a j - b j) * a l + b j * (a l - b l) := by ring
  have h1 : |a j - b j| ≤ c := by
    have h := chgPt_abs_coord_le (a - b) j
    rw [PiLp.sub_apply] at h
    exact h.trans hab
  have h2 : |a l - b l| ≤ c := by
    have h := chgPt_abs_coord_le (a - b) l
    rw [PiLp.sub_apply] at h
    exact h.trans hab
  have h3 : |a l| ≤ ‖a‖ := chgPt_abs_coord_le a l
  have h4 : |b j| ≤ ‖b‖ := chgPt_abs_coord_le b j
  rw [e]
  calc |(a j - b j) * a l + b j * (a l - b l)|
      ≤ |(a j - b j) * a l| + |b j * (a l - b l)| := abs_add_le _ _
    _ = |a j - b j| * |a l| + |b j| * |a l - b l| := by rw [abs_mul, abs_mul]
    _ ≤ c * ‖a‖ + ‖b‖ * c :=
        add_le_add (mul_le_mul h1 h3 (abs_nonneg _) hc)
          (mul_le_mul h4 h2 (abs_nonneg _) (norm_nonneg _))
    _ = c * (‖a‖ + ‖b‖) := by ring

/-- The `C_diff` term changes by at most `18 c J`. -/
lemma chgPt_cdiff (u₁ u₂ X : Space → Space) (y : Space) (c J : ℝ) (hc : 0 ≤ c) (hJ : 0 ≤ J)
    (hd : ∀ j : Fin 3, ‖physPd u₁ j y - physPd u₂ j y‖ ≤ c)
    (hdd : ∀ j l : Fin 3, ‖physPd2 u₁ j l y - physPd2 u₂ j l y‖ ≤ c)
    (hX : ∀ j : Fin 3, ‖physPd X j y‖ ≤ J)
    (hXX : ∀ j l : Fin 3, ‖physPd2 X j l y‖ ≤ J) :
    ‖physCdiff u₁ X y - physCdiff u₂ X y‖ ≤ 18 * c * J := by
  have hdecomp : physCdiff u₁ X y - physCdiff u₂ X y = ∑ j : Fin 3, ∑ l : Fin 3,
      (((physPd u₁ j y - physPd u₂ j y) l) • physPd2 X j l y -
        ((physPd X j y) l) • (physPd2 u₁ j l y - physPd2 u₂ j l y)) := by
    unfold physCdiff
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [PiLp.sub_apply, sub_smul, smul_sub]
    abel
  rw [hdecomp]
  have hterm : ∀ j l : Fin 3,
      ‖((physPd u₁ j y - physPd u₂ j y) l) • physPd2 X j l y -
        ((physPd X j y) l) • (physPd2 u₁ j l y - physPd2 u₂ j l y)‖ ≤ 2 * c * J := by
    intro j l
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |(physPd u₁ j y - physPd u₂ j y) l| ≤ c :=
      (chgPt_abs_coord_le _ l).trans (hd j)
    have h2 : |(physPd X j y) l| ≤ J := (chgPt_abs_coord_le _ l).trans (hX j)
    calc |(physPd u₁ j y - physPd u₂ j y) l| * ‖physPd2 X j l y‖ +
          |(physPd X j y) l| * ‖physPd2 u₁ j l y - physPd2 u₂ j l y‖
        ≤ c * J + J * c :=
          add_le_add (mul_le_mul h1 (hXX j l) (norm_nonneg _) hc)
            (mul_le_mul h2 (hdd j l) (norm_nonneg _) hJ)
      _ = 2 * c * J := by ring
  calc ‖∑ j : Fin 3, ∑ l : Fin 3, _‖ ≤ ∑ j : Fin 3, ‖∑ l : Fin 3, _‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖_‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, 2 * c * J :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
    _ = 18 * c * J := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The `(U⊗U):D²X` term changes by at most `9 c (|U₁| + |U₂|) J`. -/
lemma chgPt_uud2 (u₁ u₂ X : Space → Space) (y : Space) (c J : ℝ) (hc : 0 ≤ c) (hJ : 0 ≤ J)
    (hab : ‖u₁ y - u₂ y‖ ≤ c)
    (hXX : ∀ j l : Fin 3, ‖physPd2 X j l y‖ ≤ J) :
    ‖physUUD2 u₁ X y - physUUD2 u₂ X y‖ ≤ 9 * c * (‖u₁ y‖ + ‖u₂ y‖) * J := by
  have hdecomp : physUUD2 u₁ X y - physUUD2 u₂ X y = ∑ j : Fin 3, ∑ l : Fin 3,
      ((u₁ y j * u₁ y l - u₂ y j * u₂ y l) • physPd2 X j l y) := by
    unfold physUUD2
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sub_smul]
  rw [hdecomp]
  have hA0 : 0 ≤ c * (‖u₁ y‖ + ‖u₂ y‖) := mul_nonneg hc (add_nonneg (norm_nonneg _) (norm_nonneg _))
  calc ‖∑ j : Fin 3, ∑ l : Fin 3, _‖ ≤ ∑ j : Fin 3, ‖∑ l : Fin 3, _‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖_‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, (c * (‖u₁ y‖ + ‖u₂ y‖)) * J := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (chgPt_prod_le (u₁ y) (u₂ y) c hc hab j l) (hXX j l)
          (norm_nonneg _) hA0
    _ = 9 * c * (‖u₁ y‖ + ‖u₂ y‖) * J := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The `(DX+DXᵀ)∇p` term changes by at most `18 J P`. -/
lemma chgPt_dxp (X : Space → Space) (p₁ p₂ : Space → ℝ) (y : Space) (J P : ℝ)
    (hJ : 0 ≤ J) (hJx : ∀ j : Fin 3, ‖physPd X j y‖ ≤ J) (hP : 0 ≤ P)
    (hgrad : ‖physGrad p₁ y - physGrad p₂ y‖ ≤ P) :
    ‖physDXp X p₁ y - physDXp X p₂ y‖ ≤ 18 * J * P := by
  set d : Fin 3 → ℝ := fun j => fderiv ℝ p₁ y (coordinateVector j) -
    fderiv ℝ p₂ y (coordinateVector j) with hd_def
  have hd : ∀ j : Fin 3, |d j| ≤ P := by
    intro j
    have h := chgPt_abs_coord_le (physGrad p₁ y - physGrad p₂ y) j
    have e : (physGrad p₁ y - physGrad p₂ y) j = d j := by
      simp [physGrad, hd_def, PiLp.sub_apply]
    rw [e] at h
    exact h.trans hgrad
  have hcomp : ∀ i : Fin 3, (physDXp X p₁ y - physDXp X p₂ y) i =
      ∑ j : Fin 3, (physPd X j y i + physPd X i y j) * d j := by
    intro i
    simp only [physDXp, PiLp.sub_apply, ← Finset.sum_sub_distrib, mul_sub,
      hd_def]
  have hbi : ∀ i : Fin 3, |(physDXp X p₁ y - physDXp X p₂ y) i| ≤ 6 * J * P := by
    intro i
    rw [hcomp i, Fin.sum_univ_three]
    have hc : ∀ j : Fin 3, |physPd X j y i + physPd X i y j| ≤ 2 * J := fun j => by
      calc |physPd X j y i + physPd X i y j|
          ≤ |physPd X j y i| + |physPd X i y j| := abs_add_le _ _
        _ ≤ J + J := add_le_add ((chgPt_abs_coord_le _ i).trans (hJx j))
            ((chgPt_abs_coord_le _ j).trans (hJx i))
        _ = 2 * J := by ring
    have hk : ∀ j : Fin 3, |(physPd X j y i + physPd X i y j) * d j| ≤ 2 * J * P := fun j => by
      rw [abs_mul]
      exact mul_le_mul (hc j) (hd j) (abs_nonneg _) (by positivity)
    have t1 := abs_add_le ((physPd X 0 y i + physPd X i y 0) * d 0 +
      (physPd X 1 y i + physPd X i y 1) * d 1) ((physPd X 2 y i + physPd X i y 2) * d 2)
    have t2 := abs_add_le ((physPd X 0 y i + physPd X i y 0) * d 0)
      ((physPd X 1 y i + physPd X i y 1) * d 1)
    have k0 := hk 0
    have k1 := hk 1
    have k2 := hk 2
    linarith
  have hfin := chgPt_norm_le_three (physDXp X p₁ y - physDXp X p₂ y)
  have b0 := hbi 0
  have b1 := hbi 1
  have b2 := hbi 2
  linarith

/-- The main pointwise estimate, in the form of the four terms. -/
lemma chgPt_main (ν : ℝ) (u₁ u₂ X Y : Space → Space) (p₁ p₂ : Space → ℝ) (y : Space) :
    ‖((2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 * ν) • physCdiff u₁ X y + physUUD2 u₁ X y -
          physDXp X p₁ y) -
        ((2 : ℝ) • fderiv ℝ Y y (u₂ y) - (2 * ν) • physCdiff u₂ X y + physUUD2 u₂ X y -
          physDXp X p₂ y)‖ ≤
      100 * (1 + |ν| + ‖u₁ y‖ + ‖u₂ y‖) * (coefChgDens u₁ u₂ y + presChgDens p₁ p₂ y) *
        meanJetDens X Y y := by
  obtain ⟨hJ0, hJx, hJxx⟩ := chgPt_jet_bounds X Y y
  obtain ⟨hcab, hcd, hcdd⟩ := chgPt_coef_bounds u₁ u₂ y
  have hJnn : 0 ≤ meanJetDens X Y y := meanJetDens_nonneg X Y y
  have hc0 : 0 ≤ coefChgDens u₁ u₂ y := coefChgDens_nonneg _ _ _
  have hP0 : 0 ≤ presChgDens p₁ p₂ y := presChgDens_nonneg _ _ _
  have hPg : ‖physGrad p₁ y - physGrad p₂ y‖ ≤ presChgDens p₁ p₂ y := le_of_eq rfl
  set J := meanJetDens X Y y with hJdef
  set c := coefChgDens u₁ u₂ y with hcdef
  set P := presChgDens p₁ p₂ y with hPdef
  have hA : ‖(2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 : ℝ) • fderiv ℝ Y y (u₂ y)‖ ≤ 2 * J * c := by
    have e : (2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 : ℝ) • fderiv ℝ Y y (u₂ y) =
        (2 : ℝ) • fderiv ℝ Y y (u₁ y - u₂ y) := by
      rw [map_sub, smul_sub]
    rw [e, norm_smul, Real.norm_eq_abs, abs_two]
    calc 2 * ‖fderiv ℝ Y y (u₁ y - u₂ y)‖ ≤ 2 * (‖fderiv ℝ Y y‖ * ‖u₁ y - u₂ y‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
      _ ≤ 2 * (J * c) := mul_le_mul_of_nonneg_left (mul_le_mul hJ0 hcab (norm_nonneg _) hJnn)
          (by norm_num)
      _ = 2 * J * c := by ring
  have hB : ‖(2 * ν) • physCdiff u₁ X y - (2 * ν) • physCdiff u₂ X y‖ ≤ 36 * |ν| * c * J := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have hcd' := chgPt_cdiff u₁ u₂ X y c J hc0 hJnn hcd hcdd hJx hJxx
    calc 2 * |ν| * ‖physCdiff u₁ X y - physCdiff u₂ X y‖
        ≤ 2 * |ν| * (18 * c * J) := by
          have : 0 ≤ 2 * |ν| := by positivity
          exact mul_le_mul_of_nonneg_left hcd' this
      _ = 36 * |ν| * c * J := by ring
  have hC := chgPt_uud2 u₁ u₂ X y c J hc0 hJnn hcab hJxx
  have hD := chgPt_dxp X p₁ p₂ y J P hJnn hJx hP0 hPg
  have hsplit : ((2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 * ν) • physCdiff u₁ X y + physUUD2 u₁ X y -
          physDXp X p₁ y) -
        ((2 : ℝ) • fderiv ℝ Y y (u₂ y) - (2 * ν) • physCdiff u₂ X y + physUUD2 u₂ X y -
          physDXp X p₂ y) =
      (((2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 : ℝ) • fderiv ℝ Y y (u₂ y)) -
        ((2 * ν) • physCdiff u₁ X y - (2 * ν) • physCdiff u₂ X y)) +
        (physUUD2 u₁ X y - physUUD2 u₂ X y) - (physDXp X p₁ y - physDXp X p₂ y) := by
    abel
  rw [hsplit]
  have t1 := norm_sub_le ((((2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 : ℝ) • fderiv ℝ Y y (u₂ y)) -
        ((2 * ν) • physCdiff u₁ X y - (2 * ν) • physCdiff u₂ X y)) +
        (physUUD2 u₁ X y - physUUD2 u₂ X y)) (physDXp X p₁ y - physDXp X p₂ y)
  have t2 := norm_add_le (((2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 : ℝ) • fderiv ℝ Y y (u₂ y)) -
        ((2 * ν) • physCdiff u₁ X y - (2 * ν) • physCdiff u₂ X y))
        (physUUD2 u₁ X y - physUUD2 u₂ X y)
  have t3 := norm_sub_le ((2 : ℝ) • fderiv ℝ Y y (u₁ y) - (2 : ℝ) • fderiv ℝ Y y (u₂ y))
    ((2 * ν) • physCdiff u₁ X y - (2 * ν) • physCdiff u₂ X y)
  have hPJ : 0 ≤ (|ν| + (‖u₁ y‖ + ‖u₂ y‖)) * P * J := by positivity
  have hcJ : 0 ≤ c * J := mul_nonneg hc0 hJnn
  have hcJν : 0 ≤ |ν| * c * J := by positivity
  have hcJA : 0 ≤ (‖u₁ y‖ + ‖u₂ y‖) * c * J := by positivity
  have hPJ' : 0 ≤ P * J := mul_nonneg hP0 hJnn
  nlinarith [t1, t2, t3, hA, hB, hC, hD, hPJ, hcJ, hcJν, hcJA, hPJ']

/-! ## The Ward-term change -/

theorem wardEXYChgPt : WardEXYChgPt := by
  unfold WardEXYChgPt
  intro ν μ R U₁ U₂ p₁ p₂ X Y τ y
  exact chgPt_main ν (U₁ τ) (U₂ τ) (X τ) (Y τ) (p₁ τ) (p₂ τ) y

end UnforcedLeray.Short.PartIIIb.Concrete
