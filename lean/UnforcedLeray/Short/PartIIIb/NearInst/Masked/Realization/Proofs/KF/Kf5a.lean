import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.Kf4

/-!
# `KF5a`: space dilation of the convolution term (source 3614-3616)

Source of record: `the November 2 reference manuscript`
(lines 3614-3616: "Heat scaling contributes `λ³`, the divergence contributes `λ`, and the semigroup
amplitude and differential contribute `λ^{-1}`").

With `l = e^{-t/2}`, `R = ε⁻¹`, `θ = νε²(eᵗ-1)`:
1. the substitution `u = R z` in `convTerm` gives `R^{-3}` and the argument `y - R⁻¹ u`;
2. `KF4` with `ρ = R⁻¹` gives `∇K_θ(y - R⁻¹u) = R⁴ ∇K_{θR²}(R y - u)`, and `θR² = ν(eᵗ-1)`;
3. `KF4` with `ρ = e^{t/2} = l⁻¹` gives `∇K_{ν(eᵗ-1)}(l⁻¹ v) = l⁴ ∇K_{ν(1-l²)}(v)`.
Collecting the scalars `e^{t/2} · R^{-3} · R⁴ · l⁴ = R l³` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- Substitution `u = R z` in the convolution term (`R^{-3}` from `dz`). -/
theorem kf5a_scale (θ R : ℝ) (hR : 0 < R) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Space) (τ : ℝ) (i : Fin 3) :
    convTerm θ R T y τ i = (((R ^ 3)⁻¹ : ℝ) : ℂ) * ∫ u : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (y - R⁻¹ • u)
        (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) * ((T τ u j k : ℝ) : ℂ) := by
  unfold convTerm
  set G : Space → ℂ := fun u => ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (y - R⁻¹ • u)
        (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) * ((T τ u j k : ℝ) : ℂ) with hG
  have h1 : (∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK θ i j x) (y - z)
        (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) * ((T τ (R • z) j k : ℝ) : ℂ))
      = ∫ z : Space, G (R • z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hG, inv_smul_smul₀ hR.ne']
  rw [h1, Measure.integral_comp_smul volume G R, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hR 3)), Complex.real_smul]

/-- Pointwise scaling of the kernel derivative (two applications of `KF4`). -/
theorem kf5a_pt (ν θ R t : ℝ) (hν : 0 < ν) (hθ : 0 < θ) (hR : 0 < R) (ht : 0 < t)
    (hθR : θ * R ^ 2 = ν * (Real.exp t - 1)) (x u : Space) (i j k : Fin 3) :
    fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK θ i j y)
        (Real.exp (t / 2) • x - R⁻¹ • u) (UnforcedLeray.coordinateVector k) =
      R ^ 4 * Real.exp (-t / 2) ^ 4 *
        fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK
          (ν * (1 - Real.exp (-t / 2) ^ 2)) i j y)
          (R • x - Real.exp (-t / 2) • u) (UnforcedLeray.coordinateVector k) := by
  have K4 : KF4 := kf4
  unfold KF4 at K4
  have hpos : 0 < ν * (Real.exp t - 1) :=
    mul_pos hν (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  have hθ' : θ / (R⁻¹) ^ 2 = ν * (Real.exp t - 1) := by
    rw [← hθR]; field_simp
  set e := Real.exp (t / 2) with he_def
  have he0 : 0 < e := Real.exp_pos _
  have hl : Real.exp (-t / 2) = e⁻¹ := by
    rw [he_def, ← Real.exp_neg]; congr 1; ring
  have he2 : Real.exp t = e ^ 2 := by
    rw [he_def, sq, ← Real.exp_add]; congr 1; ring
  have hv1 : e • x - R⁻¹ • u = R⁻¹ • (R • (e • x) - u) := by
    rw [smul_sub, inv_smul_smul₀ hR.ne']
  have hv2 : R • (e • x) - u = e • (R • x - Real.exp (-t / 2) • u) := by
    simp only [smul_sub, smul_smul]
    rw [hl, mul_comm R e, mul_inv_cancel₀ he0.ne', one_smul]
  have hφ : ν * (Real.exp t - 1) / e ^ 2 = ν * (1 - Real.exp (-t / 2) ^ 2) := by
    rw [he2, hl]; field_simp
  have hK1 := K4 R⁻¹ θ (inv_pos.mpr hR) hθ i j k (R • (e • x) - u)
  rw [hθ'] at hK1
  have hK2 := K4 e (ν * (Real.exp t - 1)) he0 hpos i j k (R • x - Real.exp (-t / 2) • u)
  rw [hφ] at hK2
  rw [hv1, hK1, hv2, hK2, hl]
  simp only [inv_pow, inv_inv]
  ring

theorem kf5a : KF5a := by
  unfold KF5a
  intro ν ε hν hε T x τ t ht i
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ε⁻¹ := ⟨_, rfl⟩
  rw [← hRdef]
  have hR : 0 < R := by rw [hRdef]; exact inv_pos.mpr hε
  have hθpos : 0 < ν * ε ^ 2 * (Real.exp t - 1) :=
    mul_pos (mul_pos hν (pow_pos hε 2)) (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht))
  have hθR : ν * ε ^ 2 * (Real.exp t - 1) * R ^ 2 = ν * (Real.exp t - 1) := by
    rw [hRdef]; field_simp
  rw [kf5a_scale _ R hR T (Real.exp (t / 2) • x) τ i]
  have hint : ∀ u : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK (ν * ε ^ 2 * (Real.exp t - 1)) i j y)
        (Real.exp (t / 2) • x - R⁻¹ • u) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
        ((T τ u j k : ℝ) : ℂ)
      = (((R ^ 4 * Real.exp (-t / 2) ^ 4 : ℝ)) : ℂ) * ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK
          (ν * (1 - Real.exp (-t / 2) ^ 2)) i j y)
          (R • x - Real.exp (-t / 2) • u) (UnforcedLeray.coordinateVector k) : ℝ) : ℂ) *
          ((T τ u j k : ℝ) : ℂ) := by
    intro u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [kf5a_pt ν _ R t hν hθpos hR ht hθR x u i j k]
    push_cast
    ring
  simp only [hint]
  rw [MeasureTheory.integral_const_mul]
  unfold sepInner
  have hl' : Real.exp (-t / 2) = (Real.exp (t / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hreal : Real.exp (t / 2) * (R ^ 3)⁻¹ * (R ^ 4 * Real.exp (-t / 2) ^ 4)
      = R * Real.exp (-t / 2) ^ 3 := by
    rw [hl']
    field_simp
  have hreal_c : ((Real.exp (t / 2) : ℝ) : ℂ) * (((R ^ 3)⁻¹ : ℝ) : ℂ) *
      (((R ^ 4 * Real.exp (-t / 2) ^ 4 : ℝ)) : ℂ) = ((R * Real.exp (-t / 2) ^ 3 : ℝ) : ℂ) := by
    rw [← hreal]; push_cast; ring
  rw [← hreal_c]
  ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
