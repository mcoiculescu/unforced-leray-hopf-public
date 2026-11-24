import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Defs

/-!
# `PartIII-b:C/rep/8/1/1/1/asm/1`: the derivative of the stream cutoff

Source `the November 2 reference manuscript`
lines 4161-4186.  Pure calculus: `StreamCutAlgStmt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open GeomXAsm

namespace GeomXAsm.StreamCutAlgAux

lemma bdd_of_vanish {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t, t ∉ Icc (4 / 5 : ℝ) 1 → f t = 0) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |f t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (4 / 5 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (4 / 5 : ℝ) 1
  · have := hM t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [h t ht]; simp

lemma stream_cutoff_const (χ : ℝ → ℝ) (hχ : IsStreamCutoff χ) :
    Differentiable ℝ χ ∧ Differentiable ℝ (deriv χ) ∧
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ (∀ t, |deriv χ t| ≤ M₁) ∧ (∀ t, |deriv (deriv χ) t| ≤ M₂) := by
  have h1 := contDiff_infty_iff_deriv.1 hχ.smooth
  have h2 := contDiff_infty_iff_deriv.1 h1.2
  have h3 := contDiff_infty_iff_deriv.1 h2.2
  have hc1 : Continuous (deriv χ) := h1.2.continuous
  have hc2 : Continuous (deriv (deriv χ)) := h2.2.continuous
  have hv1 : ∀ t, t ∉ Icc (4 / 5 : ℝ) 1 → deriv χ t = 0 := by
    intro t ht
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · have : χ =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
        Filter.mem_of_superset (Iio_mem_nhds ht) fun s hs => hχ.one s (le_of_lt hs)
      rw [this.deriv_eq]; simp
    · have : χ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
        Filter.mem_of_superset (Ioi_mem_nhds ht) fun s hs => hχ.zero s (le_of_lt hs)
      rw [this.deriv_eq]; simp
  have hv2 : ∀ t, t ∉ Icc (4 / 5 : ℝ) 1 → deriv (deriv χ) t = 0 := by
    intro t ht
    have : deriv χ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds ht) fun s hs => hv1 s hs
    rw [this.deriv_eq]; simp
  obtain ⟨M₁, hM₁, hb₁⟩ := bdd_of_vanish hc1 hv1
  obtain ⟨M₂, hM₂, hb₂⟩ := bdd_of_vanish hc2 hv2
  exact ⟨h1.1, h2.1, M₁, M₂, hM₁, hM₂, hb₁, hb₂⟩

lemma hasDerivAt_a (ν R r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => ν * (R ^ 2 / t ^ 2)) (-2 * ν * R ^ 2 / r ^ 3) r := by
  have h1 := ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).const_mul (ν * R ^ 2)
  have hf : (fun t : ℝ => ν * (R ^ 2 / t ^ 2)) = fun y => ν * R ^ 2 * (fun x : ℝ => x ^ 2)⁻¹ y := by
    funext t; simp only [Pi.inv_apply, div_eq_mul_inv]; ring
  rw [hf]
  refine h1.congr_deriv ?_
  field_simp
  norm_num
  ring

lemma hasDerivAt_phi (χ : ℝ → ℝ) (hd : Differentiable ℝ χ) (ν R r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => χ (ν * (R ^ 2 / t ^ 2)))
      (deriv χ (ν * (R ^ 2 / r ^ 2)) * (-2 * ν * R ^ 2 / r ^ 3)) r :=
  (hd (ν * (R ^ 2 / r ^ 2))).hasDerivAt.comp r (hasDerivAt_a ν R r hr)

lemma hasDerivAt_coef (χ : ℝ → ℝ) (hd2 : Differentiable ℝ (deriv χ)) (ν R r : ℝ)
    (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => deriv χ (ν * (R ^ 2 / t ^ 2)) * (-2 * ν * R ^ 2 / t ^ 3) / t)
      (4 * (ν * (R ^ 2 / r ^ 2)) ^ 2 * deriv (deriv χ) (ν * (R ^ 2 / r ^ 2)) / r ^ 3 +
        8 * (ν * (R ^ 2 / r ^ 2)) * deriv χ (ν * (R ^ 2 / r ^ 2)) / r ^ 3) r := by
  have h1 : HasDerivAt (fun t : ℝ => deriv χ (ν * (R ^ 2 / t ^ 2)))
      (deriv (deriv χ) (ν * (R ^ 2 / r ^ 2)) * (-2 * ν * R ^ 2 / r ^ 3)) r :=
    by have h := (hd2 (ν * (R ^ 2 / r ^ 2))).hasDerivAt.comp r (hasDerivAt_a ν R r hr); exact h
  have h2 : HasDerivAt (fun t : ℝ => -2 * ν * R ^ 2 / t ^ 3)
      ((0 * r ^ 3 - (-2 * ν * R ^ 2) * ((3 : ℕ) * r ^ (3 - 1))) / (r ^ 3) ^ 2) r :=
    (hasDerivAt_const r (-2 * ν * R ^ 2)).div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr)
  have h3 : HasDerivAt
      (fun t : ℝ => deriv χ (ν * (R ^ 2 / t ^ 2)) * (-2 * ν * R ^ 2 / t ^ 3) / t) _ r :=
    (h1.mul h2).div (hasDerivAt_id' r) hr
  refine h3.congr_deriv ?_
  simp only [Pi.mul_apply]
  push_cast
  generalize deriv χ (ν * (R ^ 2 / r ^ 2)) = c1
  generalize deriv (deriv χ) (ν * (R ^ 2 / r ^ 2)) = c2
  field_simp
  ring

lemma hpt0 (r z : ℝ) : (hpt r z) 0 = r := rfl
lemma hpt1 (r z : ℝ) : (hpt r z) 1 = 0 := rfl
lemma hpt2 (r z : ℝ) : (hpt r z) 2 = z := rfl

lemma varrho_hpt {r : ℝ} (hr : 0 < r) (z : ℝ) : ϱ (hpt r z) = r := by
  unfold ϱ
  rw [hpt0, hpt1]
  simp [Real.sqrt_sq hr.le]

lemma hpt_not_axis {r : ℝ} (hr : 0 < r) (z : ℝ) : hpt r z ∉ axis := by
  intro h
  have := h.1
  rw [hpt0] at this
  exact hr.ne' this

lemma norm_varrhoD_le (y : Space) : ‖ϱD y‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [ϱD_apply, one_mul]
  by_cases hy : ϱ y = 0
  · simp [hy]
  · have hpos : 0 < ϱ y := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hy)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hv : v 0 ^ 2 + v 1 ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_three]
      nlinarith [sq_nonneg (v 2)]
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have hs := ϱ_sq y
    calc (y 0 * v 0 + y 1 * v 1) ^ 2 ≤ (y 0 ^ 2 + y 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
          nlinarith [sq_nonneg (y 0 * v 1 - y 1 * v 0)]
      _ ≤ (y 0 ^ 2 + y 1 ^ 2) * ‖v‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left hv; positivity
      _ = (‖v‖ * ϱ y) ^ 2 := by rw [mul_pow, hs]; ring

/-- `ν R²/r²`. -/
def cA (ν R r : ℝ) : ℝ := ν * (R ^ 2 / r ^ 2)

/-- `d/dr χ(νR²/r²)`. -/
def cPhi (χ : ℝ → ℝ) (ν R r : ℝ) : ℝ := deriv χ (cA ν R r) * (-2 * ν * R ^ 2 / r ^ 3)

/-- The coefficient `χ_y'/r`. -/
def cCoef (χ : ℝ → ℝ) (ν R r : ℝ) : ℝ := cPhi χ ν R r / r

/-- `d/dr (χ_y'/r)`. -/
def cCoef' (χ : ℝ → ℝ) (ν R r : ℝ) : ℝ :=
  4 * cA ν R r ^ 2 * deriv (deriv χ) (cA ν R r) / r ^ 3 +
    8 * cA ν R r * deriv χ (cA ν R r) / r ^ 3

lemma hasFDerivAt_ward (χ : ℝ → ℝ) (hd : Differentiable ℝ χ)
    (hd2 : Differentiable ℝ (deriv χ)) (ν R r z τ : ℝ) (hr : 0 < r)
    (Z : ℝ → Space → Space) (hZ : DifferentiableAt ℝ (Z τ) (hpt r z))
    (hP : PrimData Z τ r z) :
    ∃ D : Space →L[ℝ] Space, HasFDerivAt (wardStreamCut ν R χ Z τ) D (hpt r z) ∧
      ∀ v : Space, D v = χ (cA ν R r) • fderiv ℝ (Z τ) (hpt r z) v +
        (cPhi χ ν R r * ϱD (hpt r z) v) • Z τ (hpt r z) +
        (cCoef χ ν R r * ((r * Z τ (hpt r z) 2) * ϱD (hpt r z) v + (-primDz Z τ r z) * v 2) +
          outPrim Z τ r z * (cCoef' χ ν R r * ϱD (hpt r z) v)) • coordinateVector 2 := by
  have hr0 : r ≠ 0 := hr.ne'
  have hne : hpt r z ∉ axis := hpt_not_axis hr z
  have hρ : HasFDerivAt ϱ (ϱD (hpt r z)) (hpt r z) := hasFDerivAt_ϱ hne
  have hρr : r = ϱ (hpt r z) := (varrho_hpt hr z).symm
  have hφ : HasFDerivAt (fun y => χ (ν * (R ^ 2 / ϱ y ^ 2)))
      (cPhi χ ν R r • ϱD (hpt r z)) (hpt r z) :=
    (hasDerivAt_phi χ hd ν R r hr0).comp_hasFDerivAt_of_eq (hpt r z) hρ hρr
  have hc : HasFDerivAt (fun y => deriv χ (ν * (R ^ 2 / ϱ y ^ 2)) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y)
      (cCoef' χ ν R r • ϱD (hpt r z)) (hpt r z) :=
    (hasDerivAt_coef χ hd2 ν R r hr0).comp_hasFDerivAt_of_eq (hpt r z) hρ hρr
  have hm : HasFDerivAt (fun y : Space => (ϱ y, y 2))
      (merD (hpt r z)) (hpt r z) :=
    hρ.prodMk (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hΨ : HasFDerivAt (fun y : Space => outPrim Z τ (ϱ y) (y 2))
      (((r * Z τ (hpt r z) 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-primDz Z τ r z) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp (merD (hpt r z))) (hpt r z) := by
    have hpt' : (ϱ (hpt r z), (hpt r z) 2) = (r, z) := by
      rw [varrho_hpt hr z, hpt2]
    have hg : HasFDerivAt (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
        ((r * Z τ (hpt r z) 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (-primDz Z τ r z) • ContinuousLinearMap.snd ℝ ℝ ℝ) (ϱ (hpt r z), (hpt r z) 2) := by
      rw [hpt']; exact hP.2.2
    exact hg.comp (hpt r z) hm
  have hZd : HasFDerivAt (Z τ) (fderiv ℝ (Z τ) (hpt r z)) (hpt r z) := hZ.hasFDerivAt
  have h1 := hφ.smul hZd
  have h2 := (hc.mul hΨ).smul_const (coordinateVector 2 : Space)
  have hW := h1.add h2
  refine ⟨_, hW, fun v => ?_⟩
  · simp [ContinuousLinearMap.smulRight_apply, merD_apply,
      varrho_hpt hr z, hpt2, cCoef, cCoef', cPhi, cA]
    module

lemma cA_nonneg (ν R r : ℝ) (hν : 0 < ν) : 0 ≤ cA ν R r := by
  unfold cA; positivity

lemma cPhi_bound (χ : ℝ → ℝ) (ν R r M₁ : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (hA : cA ν R r ≤ 1) (hM : ∀ t, |deriv χ t| ≤ M₁) :
    |cPhi χ ν R r| ≤ 2 * M₁ * r⁻¹ := by
  have hA0 := cA_nonneg ν R r hν
  have hM0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM 0)
  have h : cPhi χ ν R r = deriv χ (cA ν R r) * (-(2 * cA ν R r * r⁻¹)) := by
    unfold cPhi cA; field_simp
  rw [h, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * cA ν R r * r⁻¹)]
  calc |deriv χ (cA ν R r)| * (2 * cA ν R r * r⁻¹) ≤ M₁ * (2 * 1 * r⁻¹) := by
        gcongr
        exact hM _
    _ = 2 * M₁ * r⁻¹ := by ring

lemma cCoef_bound (χ : ℝ → ℝ) (ν R r M₁ : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (hA : cA ν R r ≤ 1) (hM : ∀ t, |deriv χ t| ≤ M₁) :
    |cCoef χ ν R r| ≤ 2 * M₁ * r⁻¹ ^ 2 := by
  have h := cPhi_bound χ ν R r M₁ hν hr hA hM
  unfold cCoef
  rw [abs_div, abs_of_pos hr, div_eq_mul_inv]
  calc |cPhi χ ν R r| * r⁻¹ ≤ 2 * M₁ * r⁻¹ * r⁻¹ := by gcongr
    _ = 2 * M₁ * r⁻¹ ^ 2 := by ring

lemma cCoef'_bound (χ : ℝ → ℝ) (ν R r M₁ M₂ : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (hA : cA ν R r ≤ 1) (hM₁ : ∀ t, |deriv χ t| ≤ M₁)
    (hM₂ : ∀ t, |deriv (deriv χ) t| ≤ M₂) :
    |cCoef' χ ν R r| ≤ (4 * M₂ + 8 * M₁) * r⁻¹ ^ 3 := by
  have hA0 := cA_nonneg ν R r hν
  have hM0 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ 0)
  have hM0' : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ 0)
  have h : cCoef' χ ν R r = (4 * cA ν R r ^ 2 * deriv (deriv χ) (cA ν R r) +
      8 * cA ν R r * deriv χ (cA ν R r)) * r⁻¹ ^ 3 := by
    unfold cCoef'; rw [inv_pow]; field_simp
  rw [h, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r⁻¹ ^ 3)]
  have hA2 : cA ν R r ^ 2 ≤ 1 := pow_le_one₀ hA0 hA
  have t1 : |4 * cA ν R r ^ 2 * deriv (deriv χ) (cA ν R r)| ≤ 4 * M₂ := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * cA ν R r ^ 2)]
    calc 4 * cA ν R r ^ 2 * |deriv (deriv χ) (cA ν R r)| ≤ 4 * 1 * M₂ := by
          gcongr
          exact hM₂ _
      _ = 4 * M₂ := by ring
  have t2 : |8 * cA ν R r * deriv χ (cA ν R r)| ≤ 8 * M₁ := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 8 * cA ν R r)]
    calc 8 * cA ν R r * |deriv χ (cA ν R r)| ≤ 8 * 1 * M₁ := by
          gcongr
          exact hM₁ _
      _ = 8 * M₁ := by ring
  gcongr
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

lemma norm_e2 : ‖(coordinateVector 2 : Space)‖ = 1 := by
  simp [coordinateVector]

lemma abs_varrhoD_le (y v : Space) : |ϱD y v| ≤ ‖v‖ := by
  calc |ϱD y v| = ‖ϱD y v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ϱD y‖ * ‖v‖ := (ϱD y).le_opNorm v
    _ ≤ 1 * ‖v‖ := by gcongr; exact norm_varrhoD_le y
    _ = ‖v‖ := one_mul _

lemma abs_apply_two_le (v : Space) : |v 2| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v 2
  rwa [Real.norm_eq_abs] at this

end GeomXAsm.StreamCutAlgAux

set_option maxHeartbeats 1600000 in
open GeomXAsm.StreamCutAlgAux in
/-- **(a1) The derivative of the stream cutoff** (source 4178-4186). -/
theorem streamCutAlg : StreamCutAlgStmt := by
  intro χ hχ
  obtain ⟨hd, hd2, M₁, M₂, hM₁, hM₂, hb₁, hb₂⟩ := stream_cutoff_const χ hχ
  refine ⟨1 + 8 * M₁ + 4 * M₂, by positivity, ?_⟩
  intro ν R r z τ Z₁ Z₂ hν hR hr hA hZ₁ hZ₂ hP₁ hP₂
  have hA' : cA ν R r ≤ 1 := hA
  obtain ⟨D₁, hD₁, e₁⟩ := hasFDerivAt_ward χ hd hd2 ν R r z τ hr Z₁ hZ₁ hP₁
  obtain ⟨D₂, hD₂, e₂⟩ := hasFDerivAt_ward χ hd hd2 ν R r z τ hr Z₂ hZ₂ hP₂
  rw [hD₁.fderiv, hD₂.fderiv]
  have hφ := cPhi_bound χ ν R r M₁ hν hr hA' hb₁
  have hc := cCoef_bound χ ν R r M₁ hν hr hA' hb₁
  have hc' := cCoef'_bound χ ν R r M₁ M₂ hν hr hA' hb₁ hb₂
  have hχA : |χ (cA ν R r)| ≤ 1 := by
    rw [abs_of_nonneg (hχ.range _).1]; exact (hχ.range _).2
  set i : ℝ := r⁻¹ with hi
  have hi0 : 0 < i := inv_pos.2 hr
  have hri : r * i = 1 := mul_inv_cancel₀ hr.ne'
  have hi2 : i ^ 2 * r = i := by
    calc i ^ 2 * r = i * (r * i) := by ring
      _ = i := by rw [hri, mul_one]
  set dd := dDiff Z₁ Z₂ τ (hpt r z) with hdd
  set zn := ‖Z₁ τ (hpt r z) - Z₂ τ (hpt r z)‖ with hzn
  set dP := |outPrim Z₁ τ r z - outPrim Z₂ τ r z| with hdP
  set dq := |primDz Z₁ τ r z - primDz Z₂ τ r z| with hdq
  have hdd0 : 0 ≤ dd := norm_nonneg _
  have hzn0 : 0 ≤ zn := norm_nonneg _
  have hdP0 : 0 ≤ dP := abs_nonneg _
  have hdq0 : 0 ≤ dq := abs_nonneg _
  have hB : 0 ≤ (1 + 8 * M₁ + 4 * M₂) * (dd + i * zn + i ^ 3 * dP + i ^ 2 * dq) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hB (fun v => ?_)
  have hnv : 0 ≤ ‖v‖ := norm_nonneg _
  have key : (D₁ - D₂) v = χ (cA ν R r) • ((fderiv ℝ (Z₁ τ) (hpt r z) -
        fderiv ℝ (Z₂ τ) (hpt r z)) v) +
      (cPhi χ ν R r * ϱD (hpt r z) v) • (Z₁ τ (hpt r z) - Z₂ τ (hpt r z)) +
      (cCoef χ ν R r * ((r * (Z₁ τ (hpt r z) 2 - Z₂ τ (hpt r z) 2)) * ϱD (hpt r z) v +
          (-(primDz Z₁ τ r z - primDz Z₂ τ r z)) * v 2) +
        (outPrim Z₁ τ r z - outPrim Z₂ τ r z) * (cCoef' χ ν R r * ϱD (hpt r z) v)) •
        coordinateVector 2 := by
    rw [sub_apply, e₁ v, e₂ v, sub_apply]
    module
  rw [key]
  have b1 : ‖χ (cA ν R r) • ((fderiv ℝ (Z₁ τ) (hpt r z) - fderiv ℝ (Z₂ τ) (hpt r z)) v)‖ ≤
      dd * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |χ (cA ν R r)| * ‖(fderiv ℝ (Z₁ τ) (hpt r z) - fderiv ℝ (Z₂ τ) (hpt r z)) v‖
        ≤ 1 * (dd * ‖v‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = dd * ‖v‖ := one_mul _
  have b2 : ‖(cPhi χ ν R r * ϱD (hpt r z) v) • (Z₁ τ (hpt r z) - Z₂ τ (hpt r z))‖ ≤
      2 * M₁ * i * (zn * ‖v‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    calc |cPhi χ ν R r| * |ϱD (hpt r z) v| * zn ≤ (2 * M₁ * i) * ‖v‖ * zn := by
          gcongr
          exact abs_varrhoD_le _ _
      _ = 2 * M₁ * i * (zn * ‖v‖) := by ring
  have hz2 : |Z₁ τ (hpt r z) 2 - Z₂ τ (hpt r z) 2| ≤ zn := by
    have := PiLp.norm_apply_le (Z₁ τ (hpt r z) - Z₂ τ (hpt r z)) 2
    rwa [Real.norm_eq_abs] at this
  set s : ℝ := cCoef χ ν R r * ((r * (Z₁ τ (hpt r z) 2 - Z₂ τ (hpt r z) 2)) * ϱD (hpt r z) v +
          (-(primDz Z₁ τ r z - primDz Z₂ τ r z)) * v 2) +
        (outPrim Z₁ τ r z - outPrim Z₂ τ r z) * (cCoef' χ ν R r * ϱD (hpt r z) v) with hs
  have hs1 : |r * (Z₁ τ (hpt r z) 2 - Z₂ τ (hpt r z) 2) * ϱD (hpt r z) v +
      (-(primDz Z₁ τ r z - primDz Z₂ τ r z)) * v 2| ≤ (r * zn + dq) * ‖v‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hr]
    have h1 := abs_varrhoD_le (hpt r z) v
    have h2 := abs_apply_two_le v
    have : r * |Z₁ τ (hpt r z) 2 - Z₂ τ (hpt r z) 2| * |ϱD (hpt r z) v| ≤ r * zn * ‖v‖ := by
      gcongr
    nlinarith [mul_le_mul_of_nonneg_left h2 hdq0]
  have b3 : ‖s • (coordinateVector 2 : Space)‖ ≤
      2 * M₁ * i ^ 2 * (r * zn + dq) * ‖v‖ + dP * ((4 * M₂ + 8 * M₁) * i ^ 3) * ‖v‖ := by
    rw [norm_smul, norm_e2, mul_one, Real.norm_eq_abs, hs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      calc |cCoef χ ν R r| * _ ≤ (2 * M₁ * i ^ 2) * ((r * zn + dq) * ‖v‖) := by
            gcongr
        _ = _ := by ring
    · rw [abs_mul, abs_mul]
      calc |outPrim Z₁ τ r z - outPrim Z₂ τ r z| * (|cCoef' χ ν R r| * |ϱD (hpt r z) v|)
          ≤ dP * (((4 * M₂ + 8 * M₁) * i ^ 3) * ‖v‖) := by
            gcongr
            exact abs_varrhoD_le _ _
        _ = _ := by ring
  have e3 : 2 * M₁ * i ^ 2 * (r * zn + dq) = 2 * M₁ * i * zn + 2 * M₁ * i ^ 2 * dq := by
    have : i ^ 2 * r = i := hi2
    calc 2 * M₁ * i ^ 2 * (r * zn + dq) = 2 * M₁ * (i ^ 2 * r) * zn + 2 * M₁ * i ^ 2 * dq := by
          ring
      _ = _ := by rw [this]
  have X1 : 0 ≤ dd * ‖v‖ := by positivity
  have X2 : 0 ≤ i * zn * ‖v‖ := by positivity
  have X3 : 0 ≤ i ^ 3 * dP * ‖v‖ := by positivity
  have X4 : 0 ≤ i ^ 2 * dq * ‖v‖ := by positivity
  calc _ ≤ ‖χ (cA ν R r) • ((fderiv ℝ (Z₁ τ) (hpt r z) - fderiv ℝ (Z₂ τ) (hpt r z)) v)‖ +
        ‖(cPhi χ ν R r * ϱD (hpt r z) v) • (Z₁ τ (hpt r z) - Z₂ τ (hpt r z))‖ +
        ‖s • (coordinateVector 2 : Space)‖ := norm_add₃_le
    _ ≤ dd * ‖v‖ + 2 * M₁ * i * (zn * ‖v‖) + (2 * M₁ * i ^ 2 * (r * zn + dq) * ‖v‖ +
        dP * ((4 * M₂ + 8 * M₁) * i ^ 3) * ‖v‖) := by gcongr
    _ ≤ _ := by
        rw [e3]
        nlinarith [mul_nonneg hM₁ X1, mul_nonneg hM₂ X1, mul_nonneg hM₁ X2, mul_nonneg hM₂ X2,
          mul_nonneg hM₁ X3, mul_nonneg hM₂ X3, mul_nonneg hM₁ X4, mul_nonneg hM₂ X4]

end UnforcedLeray.Short.PartIIIb.Concrete
