import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable

/-!
# `C/inst/3` (audit decomposition): summability of the lattice terms of `e_A` (source 4971-4972, 4978)

Source of record: `the November 2 reference manuscript`, lines 4963-4972
(`V_j`, `p_j`, `e_A`) and 4978 (Gaussian decay).  The `j`-th term is
`2 B V_j + 2ν A^y : D²V_j - (A^y + (A^y)ᵀ) ∇p_j` with fixed matrices `B, A^y`.

Two analytic leaves (pure calculus on explicit Gaussians, same shape as `gp_fderiv_Vj_norm`):

* `HessVjBound` : the second derivatives of `V_j` are `≤ K (1+|q-jc|)³ e^{-(q-jc)²/(4a)}`
  (`V_j(y) = (a²)⁻¹ e^{-|y-jc e₁|²/(4a)} J(y - jc e₁)`, `a = 1+νs`, `c = ν⁻²`);
* `MgradPjBound` : `∇p_j` is `≤ K (1+|q-jc|)³ e^{-(q-jc)²/(4a)}`
  (`p_j = -a⁻³ e^{-|x_j|²/(2a)}`; the exponent is at least that of `e^{-(q-jc)²/(4a)}`).

`eATermSummable_of` assembles `EATermSummable` from them (`Summable.of_norm_bounded` against the
summable majorant `gp_poly_summable`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf 1: second derivatives of `V_j` (source 4963-4966, 4978). -/
def HessVjBound : Prop :=
  ∀ (ν s : ℝ), 0 < ageA ν s → ∀ x : ℝ × ℝ, ∃ K : ℝ, ∀ (j : ℤ) (a b : Fin 2),
    ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei a)‖ ≤
      K * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))

/-- Leaf 2: the meridional gradient of `p_j` (source 4964-4966, 4978). -/
def MgradPjBound : Prop :=
  ∀ (ν s : ℝ), 0 < ageA ν s → ∀ x : ℝ × ℝ, ∃ K : ℝ, ∀ j : ℤ,
    ‖mgrad (pj ν s j) x‖ ≤
      K * ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
        Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))

theorem eATermSummable_of (hH : HessVjBound) (hP : MgradPjBound) : EATermSummable := by
  intro ν μ χ A s x hν hs
  have ha : 0 < ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hc : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  have hα : 0 < 1 / (4 * ageA ν s) := div_pos one_pos (by linarith)
  obtain ⟨KH, hKH⟩ := hH ν s ha x
  obtain ⟨KP, hKP⟩ := hP ν s ha x
  have hS := gp_poly_summable x.1 (1 / (4 * ageA ν s)) (cOf ν) hα hc
  set G : ℤ → ℝ := fun j => (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
    Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) with hG
  have hG0 : ∀ j, 0 ≤ G j := fun j => by simp only [hG]; positivity
  set B := Bmat ν μ χ A s with hB
  set Ay' := Ay ν χ A s with hAy
  set M : Mat3 := fun a b => Ay' a b + Ay' b a with hMdef
  set SB := ∑ i, ∑ j, |B i j| with hSB
  set SM := ∑ i, ∑ j, |M i j| with hSM
  set SA := ∑ a : Fin 2, ∑ b : Fin 2, |Ay' (mi a) (mi b)| with hSA
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSM0 : 0 ≤ SM := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSA0 : 0 ≤ SA := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  -- bound on `V_j`
  have hV : ∀ j : ℤ, ‖Vj ν s j x‖ ≤ ((ageA ν s ^ 2)⁻¹ * (1 + |x.2|)) * G j := by
    intro j
    rw [gp_Vj_norm_eq]
    have hκ : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
    have hEb := gp_exp_le ν s ha j x
    have hu : 1 ≤ 1 + |x.1 - (j : ℝ) * cOf ν| := by linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν)]
    have h1 : ‖xj ν j x‖ ≤ (1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
      have h2 := gp_one_add_norm ν j x
      have h3 : (1 + |x.1 - (j : ℝ) * cOf ν|) ≤ (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
        have := one_le_pow₀ (n := 2) hu
        nlinarith [this]
      have h4 : (1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|) ≤
          (1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith [norm_nonneg (xj ν j x)]
    have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
    calc (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖
        ≤ (ageA ν s ^ 2)⁻¹ * Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) *
          ((1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hEb hκ) h1 (norm_nonneg _)
            (mul_nonneg hκ (Real.exp_pos _).le)
      _ = ((ageA ν s ^ 2)⁻¹ * (1 + |x.2|)) * G j := by simp only [hG]; ring
  have hmv1 : ∀ j : ℤ, ‖mv B (emb (Vj ν s j x))‖ ≤ SB * (((ageA ν s ^ 2)⁻¹ * (1 + |x.2|)) * G j) := by
    intro j
    exact (fa_mv_norm_le B _).trans (mul_le_mul_of_nonneg_left
      ((fa_emb_norm_le _).trans (hV j)) hSB0)
  have hmv2 : ∀ j : ℤ, ‖mv M (emb (mgrad (pj ν s j) x))‖ ≤ SM * (KP * G j) := by
    intro j
    exact (fa_mv_norm_le M _).trans (mul_le_mul_of_nonneg_left
      ((fa_emb_norm_le _).trans (hKP j)) hSM0)
  have hhess : ∀ j : ℤ, ‖hessContr Ay' (Vj ν s j) x‖ ≤ SA * (KH * G j) := by
    intro j
    unfold hessContr
    refine (fa_emb_norm_le _).trans ?_
    rw [hSA, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hKH j a b) (abs_nonneg _)
  refine Summable.of_norm_bounded
    (hS.mul_left (2 * (SB * ((ageA ν s ^ 2)⁻¹ * (1 + |x.2|))) + |2 * ν| * (SA * KH) + SM * KP))
    (fun j => ?_)
  show ‖eATerm ν μ χ A s x j‖ ≤ _
  unfold eATerm
  have t1 : ‖(2 : ℝ) • mv B (emb (Vj ν s j x))‖ ≤ 2 * (SB * (((ageA ν s ^ 2)⁻¹ * (1 + |x.2|)) * G j)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hmv1 j) (by norm_num)
  have t2 : ‖(2 * ν) • hessContr Ay' (Vj ν s j) x‖ ≤ |2 * ν| * (SA * (KH * G j)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hhess j) (abs_nonneg _)
  calc ‖(2 : ℝ) • mv B (emb (Vj ν s j x)) + (2 * ν) • hessContr Ay' (Vj ν s j) x -
        mv M (emb (mgrad (pj ν s j) x))‖
      ≤ ‖(2 : ℝ) • mv B (emb (Vj ν s j x))‖ + ‖(2 * ν) • hessContr Ay' (Vj ν s j) x‖ +
        ‖mv M (emb (mgrad (pj ν s j) x))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * (SB * (((ageA ν s ^ 2)⁻¹ * (1 + |x.2|)) * G j)) + |2 * ν| * (SA * (KH * G j)) +
        SM * (KP * G j) := add_le_add (add_le_add t1 t2) (hmv2 j)
    _ = _ := by simp only [hG]; ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
