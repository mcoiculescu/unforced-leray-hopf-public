import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2

/-!
# Reality and absence of swirl for `sepW` (source 3586-3626, 3611-3617)

Route.
* Reality: for real `μ`, each component of `sepW` is the integral of a real function times the
  real power `l^(2μ+2)`, so it is `(real number)` cast to `ℂ` (`integral_ofReal`, no integrability).
* No swirl: the reflection `S = diag(1,-1,1)` satisfies `K_t(Sx) = S K_t(x) S` (`kernelEquivariance`),
  `cartLift τ (Sz) = S cartLift τ z S`.  The first component of the inner `z`-integral is odd under
  `z ↦ Sz` (a measure-preserving substitution, no integrability needed), and at a `S`-fixed point
  `y` (here `y₂ = 0`) this forces it to vanish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst (cartLift chartOf cylFrame hRad nsSym symRZ)

/-- The real integrand of the `z`-integral in `sepW` at the outer age `l`. -/
def rnsTerm (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ l : ℝ)
    (y z : Space) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) (y - l • z) (coordinateVector k) *
      T (τ + 2 * Real.log l) z j k

/-- The complex inner integral `∫ rnsTerm dz` of `sepW`. -/
def rnsInt (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ l : ℝ)
    (y : Space) : ℂ :=
  ∫ z : Space, ((rnsTerm ν i T τ l y z : ℝ) : ℂ)

theorem sepW_eq_rns (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space)
    (τ : ℝ) (i : Fin 3) :
    IIIa.sepW ν μ T y τ i =
      -2 * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) * rnsInt ν i T τ l y := by
  simp only [IIIa.sepW, rnsInt, rnsTerm, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Reality: for real `μ` every component of `sepW` has zero imaginary part. -/
theorem sepW_im_zero (ν : ℝ) (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space)
    (τ : ℝ) (i : Fin 3) : (IIIa.sepW ν (μ : ℂ) T y τ i).im = 0 := by
  rw [sepW_eq_rns]
  have hR : ∀ l ∈ Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * (μ : ℂ) + 2) * rnsInt ν i T τ l y =
      ((l ^ (2 * μ + 2) * ∫ z : Space, rnsTerm ν i T τ l y z : ℝ) : ℂ) := by
    intro l hl
    have hl0 : (0 : ℝ) ≤ l := le_of_lt hl.1
    have hc : (l : ℂ) ^ (2 * (μ : ℂ) + 2) = ((l ^ (2 * μ + 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hl0]
      congr 1
      simp
    rw [hc, rnsInt, integral_complex_ofReal, Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioo hR, integral_complex_ofReal]
  simp

/-- The reflection `y₁ ↦ -y₁` as a `LinearIsometryEquiv`-measure-preserving substitution. -/
theorem hint_refl (g : Space → ℂ) : ∫ z : Space, g (actM reflM z) = ∫ z : Space, g z := by
  have hmp : MeasurePreserving (fun x : Space => actM reflM x) volume volume :=
    (lieOf reflM_orth).measurePreserving
  have hme : MeasurableEmbedding (fun x : Space => actM reflM x) :=
    (cleOf reflM_orth).toHomeomorph.measurableEmbedding
  exact hmp.integral_comp hme g

lemma reflM_t : reflM.transpose = reflM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [reflM]

lemma actM_reflM_invol (x : Space) : actM reflM (actM reflM x) = x := by
  have h := actM_actM' reflM_orth x
  rw [reflM_t] at h
  exact h

lemma actM_reflM_basis (k : Fin 3) :
    actM reflM (coordinateVector k) = reflM k k • coordinateVector k := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [actM, reflM, coordinateVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.single_apply]

lemma reflM_entry (X : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    (reflM * X * reflM) j k = reflM j j * X j k * reflM k k := by
  fin_cases j <;> fin_cases k <;>
    simp [reflM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

lemma fderiv_const_mul_any {g : Space → ℝ} {c : ℝ} (hc : c ≠ 0) (w v : Space) :
    fderiv ℝ (fun x => c * g x) w v = c * fderiv ℝ g w v := by
  by_cases hd : DifferentiableAt ℝ g w
  · rw [fderiv_const_mul hd]
    simp
  · have hd' : ¬ DifferentiableAt ℝ (fun x => c * g x) w := by
      intro h
      apply hd
      have h2 := h.const_mul c⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hc] using h2
    rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]
    simp

lemma kernel_refl (t : ℝ) (i j : Fin 3) (x : Space) :
    IIIa.heatLerayK t i j (actM reflM x) = reflM i i * reflM j j * IIIa.heatLerayK t i j x := by
  rw [kernelEquivariance reflM reflM_orth t i j x]
  fin_cases i <;> fin_cases j <;> simp [reflM, Fin.sum_univ_three] <;> ring

lemma chain_refl (t : ℝ) (i j : Fin 3) (w v : Space) :
    fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM reflM w) (actM reflM v) =
      reflM i i * reflM j j * fderiv ℝ (fun x => IIIa.heatLerayK t i j x) w v := by
  have h1 : fderiv ℝ (fun x => IIIa.heatLerayK t i j (actM reflM x)) w v =
      fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM reflM w) (actM reflM v) :=
    fderiv_comp_actM reflM_orth (fun x => IIIa.heatLerayK t i j x) w v
  have hfun : (fun x => IIIa.heatLerayK t i j (actM reflM x)) =
      fun x => (reflM i i * reflM j j) * IIIa.heatLerayK t i j x :=
    funext fun x => kernel_refl t i j x
  rw [hfun] at h1
  rw [← h1]
  have hc : reflM i i * reflM j j ≠ 0 := by
    fin_cases i <;> fin_cases j <;> simp [reflM]
  exact fderiv_const_mul_any hc w v

lemma deriv_refl (t : ℝ) (i j k : Fin 3) (w : Space) :
    fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (actM reflM w) (coordinateVector k) =
      reflM i i * reflM j j *
        (reflM k k * fderiv ℝ (fun x => IIIa.heatLerayK t i j x) w (coordinateVector k)) := by
  have h := chain_refl t i j w (actM reflM (coordinateVector k))
  rw [actM_reflM_invol, actM_reflM_basis, map_smul, smul_eq_mul] at h
  exact h

lemma rnsTerm_flip (ν : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM reflM z) = reflM * T τ z * reflM) (τ l : ℝ) (y z : Space) :
    rnsTerm ν 1 T τ l (actM reflM y) (actM reflM z) = - rnsTerm ν 1 T τ l y z := by
  unfold rnsTerm
  rw [← actM_sub_smul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [deriv_refl, hT, reflM_entry]
  fin_cases j <;> fin_cases k <;> simp [reflM] <;> ring

lemma rnsInt_flip (ν : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM reflM z) = reflM * T τ z * reflM) (τ l : ℝ) (y : Space) :
    rnsInt ν 1 T τ l (actM reflM y) = - rnsInt ν 1 T τ l y := by
  unfold rnsInt
  calc ∫ z : Space, ((rnsTerm ν 1 T τ l (actM reflM y) z : ℝ) : ℂ)
      = ∫ z : Space, ((rnsTerm ν 1 T τ l (actM reflM y) (actM reflM z) : ℝ) : ℂ) :=
        (hint_refl (fun z => ((rnsTerm ν 1 T τ l (actM reflM y) z : ℝ) : ℂ))).symm
    _ = ∫ z : Space, -((rnsTerm ν 1 T τ l y z : ℝ) : ℂ) := by
        congr 1
        funext z
        rw [rnsTerm_flip ν T hT τ l y z, Complex.ofReal_neg]
    _ = - ∫ z : Space, ((rnsTerm ν 1 T τ l y z : ℝ) : ℂ) := integral_neg _

lemma cartLift_refl (R c : ℝ) (m : Chart → Ten3) (τ : ℝ) (z : Space) :
    cartLift R c m τ (actM reflM z) = reflM * cartLift R c m τ z * reflM := by
  have hr : hRad (actM reflM z) = hRad z := by
    unfold hRad
    simp [actM_apply, reflM, Fin.sum_univ_three]
  have hch : chartOf R c (actM reflM z) τ = chartOf R c z τ := by
    unfold chartOf
    rw [hr]
    simp [actM_apply, reflM, Fin.sum_univ_three]
  have hcf : cylFrame (actM reflM z) = reflM * cylFrame z * reflM := by
    unfold cylFrame
    rw [hr]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, reflM, actM_apply] <;> ring
  unfold cartLift
  rw [hch, hcf]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, reflM, cylFrame, nsSym, symRZ,
      Matrix.transpose_apply, Matrix.vecMul, dotProduct] <;> ring

/-- Absence of swirl: at an `actM reflM`-fixed point the first component of `sepW` vanishes. -/
theorem sepW_one_eq_zero (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, T τ (actM reflM z) = reflM * T τ z * reflM) (y : Space) (τ : ℝ)
    (hy : actM reflM y = y) : IIIa.sepW ν μ T y τ 1 = 0 := by
  have hA : ∀ l : ℝ, rnsInt ν 1 T τ l y = 0 := by
    intro l
    have h := rnsInt_flip ν T hT τ l y
    rw [hy] at h
    have h2 : (2 : ℂ) * rnsInt ν 1 T τ l y = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · exact h3
  rw [sepW_eq_rns]
  simp [hA]

theorem sepW_real_noswirl : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SepWRealNoSwirl := by
  intro ν R c μ _ _ _ m _ τ ρ z _
  refine ⟨fun i => sepW_im_zero ν μ _ _ τ i, ?_⟩
  have hfix : actM reflM (WithLp.toLp 2 ![ρ, 0, z] : Space) = WithLp.toLp 2 ![ρ, 0, z] := by
    ext i
    fin_cases i <;> simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  exact sepW_one_eq_zero ν (μ : ℂ) (cartLift R c m) (cartLift_refl R c m) _ τ hfix

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
