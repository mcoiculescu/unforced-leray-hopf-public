import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1_3.ModeBridge

/-!
# `PartII-b:F2/3/1/3` (`Sub/PartII-b_F2_3_1_3.lean`): `PlanarEulerSpectral`

Source of record: `the November 2 reference manuscript` (SP) lines 931-953,
2137-2140, 2145-2171.

Constructs the continuous bounded coordinate functional `π : ℝ → (Xm m →L[ℝ] E2)` on `Icc 0 Sig`
dual to the planar direct modes `ι`, proves `(π σ).comp (ι σ) = id`, intertwines `(ι σ).comp (π σ)`
with the dilated rank-two growing Riesz projection `J_a ∘ growingProjW ∘ J_a⁻¹` on `Planar.L2w m`,
and establishes the rotation action on `ι σ`, commutation with `E σ τ`, and uniform exponential
complement bound for every `η > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.IIb.PartIIbF23Sub

namespace PlanarSpectralBridge

open UnforcedLeray.Short.IIb.PlanarEulerBridge
open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

theorem toL2w_iota_coordPi {m : ℝ} (hm : 1 < m)
    {q : Blueprint.Planar.Profile} {q' : Planar.ProfL2 m}
    (hq'_ae : ⇑q' =ᵐ[Planar.profileMeasure m] q)
    {ℓ₂ ℓm : Planar.ProfL2 m →L[ℂ] ℂ}
    (hℓm_eq : ∀ x : Planar.ProfL2 m, ℓm x = conj (ℓ₂ (star x)))
    {σ : ℝ} (hσ : 0 ≤ σ) (ha : 0 < 1 + σ) {ι_σ : E2 →L[ℝ] Xm m}
    (hι : ∀ α : E2, (ι_σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x)
    (f : Xm m) :
    toL2w m (ι_σ (coordPi hm ℓ₂ σ f)) =
      (Planar.dilW hm ha ∘L
        Planar.growingProjW (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')) ∘L
        Planar.dilW hm (inv_pos.2 ha)) (toL2w m f) := by
  have hW₀_real : Planar.dilW hm (inv_pos.2 ha) (toL2w m f) =
      toL2w m (realify (Planar.dilW hm (inv_pos.2 ha)) f) :=
    ((preservesReal_dilW hm (inv_pos.2 ha)).toL2w_realify f).symm
  have hsec_m2 : Planar.secProf m (-2) (Planar.dilW hm (inv_pos.2 ha) (toL2w m f)) =
      star (Planar.secProf m 2 (Planar.dilW hm (inv_pos.2 ha) (toL2w m f))) := by
    rw [hW₀_real, secProf_neg_two_toL2w]
  have hℓm_W₀ : ℓm (Planar.secProf m (-2) (Planar.dilW hm (inv_pos.2 ha) (toL2w m f))) =
      conj (ℓ₂ (Planar.secProf m 2 (Planar.dilW hm (inv_pos.2 ha) (toL2w m f)))) := by
    rw [hsec_m2, hℓm_eq, star_star]
  have he2 : e2ToC (coordPi hm ℓ₂ σ f) =
      ℓ₂ (Planar.secProf m 2 (Planar.dilW hm (inv_pos.2 ha) (toL2w m f))) := by
    rw [coordPi_apply, e2ToC_cToE2, coordLambda_apply_of_nonneg hm ℓ₂ hσ ha]
  rw [toL2w_directMode_eq hm hq'_ae ha (hι (coordPi hm ℓ₂ σ f)), he2, ← hℓm_W₀]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Planar.growingProjW_rankOne_apply, map_add, map_smul, map_smul]

theorem coordPi_comp_iota {m : ℝ} (hm : 1 < m)
    {q : Blueprint.Planar.Profile} {q' : Planar.ProfL2 m}
    (hq'_ae : ⇑q' =ᵐ[Planar.profileMeasure m] q)
    {ℓ₂ : Planar.ProfL2 m →L[ℂ] ℂ} (h2q : ℓ₂ q' = 1)
    {σ : ℝ} (hσ : 0 ≤ σ) (ha : 0 < 1 + σ) {ι_σ : E2 →L[ℝ] Xm m}
    (hι : ∀ α : E2, (ι_σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x) :
    (coordPi hm ℓ₂ σ).comp ι_σ = ContinuousLinearMap.id ℝ E2 := by
  ext1 α
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, coordPi_apply,
    coordLambda_apply_of_nonneg hm ℓ₂ hσ ha, toL2w_directMode_eq hm hq'_ae ha (hι α),
    map_add, map_smul, map_smul, dilW_inv_apply hm ha, dilW_inv_apply hm ha,
    map_add, map_smul, map_smul, Planar.secProf_secEmb_self,
    Planar.secProf_secEmb m 2 (-2) (star q'), ite_eq_right_iff.2 (fun h => absurd h (by decide)),
    smul_zero, add_zero, map_smul, h2q, smul_eq_mul, mul_one, cToE2_e2ToC]

theorem E_pl_comp_iota_rot {m : ℝ} (hm : 1 < m) {lam : ℂ}
    {q : Blueprint.Planar.Profile} {q' : Planar.ProfL2 m}
    (hq'_ae : ⇑q' =ᵐ[Planar.profileMeasure m] q)
    {ℓ₂ ℓm : Planar.ProfL2 m →L[ℂ] ℂ} (h2q : ℓ₂ q' = 1) (hmq : ℓm (star q') = 1)
    (hP₂ : IsSimpleSpectralProj (Planar.Lsec hm 2) (rankOneProj ℓ₂ q') lam)
    (hPm : IsSimpleSpectralProj (Planar.Lsec hm (-2)) (rankOneProj ℓm (star q')) (conj lam))
    {σ : ℝ} (ha : 0 < 1 + σ) {τ : ℝ} (hτ : 0 ≤ τ) {ι_σ : E2 →L[ℝ] Xm m}
    (hι : ∀ α : E2, (ι_σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
      fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x) :
    (E_pl m σ τ).comp ι_σ =
      ι_σ.comp (rotScaleCLM (Real.exp (lam.re * τ / (1 + σ) ^ 2)) (lam.im * τ / (1 + σ) ^ 2)) := by
  ext1 α
  apply (toL2w m).injective
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    toL2w_E_pl hm ha hτ, toL2w_directMode_eq hm hq'_ae ha (hι α),
    toL2w_directMode_eq hm hq'_ae ha (hι _), Planar.dilation_conj hm ha τ]
  simp only [ContinuousLinearMap.comp_apply, map_add, map_smul, dilW_inv_apply hm ha,
    eulerGroupW_secEmb, expSec_eigen_of_proj hm h2q hP₂,
    expSec_eigen_of_proj hm hmq hPm, smul_smul]
  congr 1
  · rw [e2ToC_rotScaleCLM_exp lam τ (1 + σ) α, mul_comm]
  · rw [conj_e2ToC_rotScaleCLM_exp lam τ (1 + σ) α, mul_comm]

theorem norm_eulerGroupDil_compl_le {m : ℝ} (hm : 1 < m)
    {P₂ Pm : Planar.ProfL2 m →L[ℂ] Planar.ProfL2 m}
    {A η C₀ : ℝ} (hη : 0 < η) (hC₀ : 0 < C₀)
    (hsec : ∀ (n : ℤ) (t : ℝ), 0 ≤ t →
      ‖Planar.expSec hm t n * (1 - Planar.secProjFam P₂ Pm n)‖ ≤ C₀ * Real.exp (η * t))
    {a : ℝ} (ha : 0 < a) (ha1 : 1 ≤ a) (haA : a ≤ A) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖Planar.eulerGroupDil hm ha τ ∘L
        (1 - Planar.dilW hm ha ∘L Planar.growingProjW P₂ Pm ∘L
          Planar.dilW hm (inv_pos.2 ha))‖ ≤
      A ^ (m / 2) * C₀ * Real.exp (η * τ) := by
  set P₀ := Planar.growingProjW P₂ Pm
  have ht : 0 ≤ τ / a ^ 2 := div_nonneg hτ (sq_nonneg a)
  have hdiv : τ / a ^ 2 ≤ τ := div_le_self hτ (one_le_pow₀ ha1)
  have hCe : 0 ≤ C₀ * Real.exp (η * τ) := mul_nonneg hC₀.le (Real.exp_pos _).le
  have hSb : ‖Planar.eulerGroupW hm (τ / a ^ 2) ∘L (1 - P₀)‖ ≤ C₀ * Real.exp (η * τ) := by
    refine (Planar.norm_eulerGroupW_comp_le hm P₂ Pm (τ / a ^ 2)
      (mul_nonneg hC₀.le (Real.exp_pos _).le) fun n => hsec n _ ht).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hdiv hη.le)) hC₀.le
  have halg : Planar.eulerGroupDil hm ha τ ∘L
      (1 - Planar.dilW hm ha ∘L P₀ ∘L Planar.dilW hm (inv_pos.2 ha)) =
      Planar.dilW hm ha ∘L (Planar.eulerGroupW hm (τ / a ^ 2) ∘L (1 - P₀)) ∘L
        Planar.dilW hm (inv_pos.2 ha) := by
    rw [Planar.dilation_conj hm ha τ]
    have hJ : Planar.dilW hm (inv_pos.2 ha) * Planar.dilW hm ha = 1 :=
      Planar.dilW_inv_comp hm ha
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using
      PartI.dilation_conj_complement_alg (Planar.dilW hm ha)
        (Planar.dilW hm (inv_pos.2 ha)) (Planar.eulerGroupW hm (τ / a ^ 2)) P₀ hJ
  rw [halg]
  have hJn : ‖Planar.dilW hm ha‖ ≤ Planar.dilConst m a := Planar.norm_dilW_le hm ha
  have hJin : ‖Planar.dilW hm (inv_pos.2 ha)‖ ≤ Planar.dilConst m a⁻¹ :=
    Planar.norm_dilW_le hm (inv_pos.2 ha)
  have hmul := Planar.dilConst_mul_inv_le hm ha1 haA
  have hX : ‖Planar.dilW hm ha ∘L (Planar.eulerGroupW hm (τ / a ^ 2) ∘L (1 - P₀))‖ ≤
      Planar.dilConst m a * (C₀ * Real.exp (η * τ)) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hJn hSb (norm_nonneg _) (Planar.dilConst_nonneg m a))
  have hB : 0 ≤ Planar.dilConst m a * (C₀ * Real.exp (η * τ)) :=
    mul_nonneg (Planar.dilConst_nonneg m a) hCe
  calc ‖Planar.dilW hm ha ∘L (Planar.eulerGroupW hm (τ / a ^ 2) ∘L (1 - P₀)) ∘L
          Planar.dilW hm (inv_pos.2 ha)‖
      ≤ (Planar.dilConst m a * (C₀ * Real.exp (η * τ))) * Planar.dilConst m a⁻¹ := by
          rw [← ContinuousLinearMap.comp_assoc]
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hX hJin (norm_nonneg _) hB)
    _ = (Planar.dilConst m a * Planar.dilConst m a⁻¹) * (C₀ * Real.exp (η * τ)) := by ring
    _ ≤ A ^ (m / 2) * (C₀ * Real.exp (η * τ)) := mul_le_mul_of_nonneg_right hmul hCe
    _ = A ^ (m / 2) * C₀ * Real.exp (η * τ) := by ring

end PlanarSpectralBridge

/-- **Leaf `PartII-b:F2/3/1/3`**: coordinate functional, rotation action, commuting projection,
and uniform complement bound for the frozen planar Euler family. -/
theorem planarEulerSpectral : UnforcedLeray.Short.IIb.PlanarFrozenF231.PlanarEulerSpectral := by
  intro m hm Sig lam q hSig hEig ι _hιc hιae E T hD
  open PlanarEulerBridge PlanarSpectralBridge in
  open UnforcedLeray.Infra.Dunford (rankOneProj) in
  have hm1 : 1 < m := by linarith
  obtain ⟨q', ℓ₂, ℓm, hq'0, hq', hq'_ae, h2q, hmq, hP₂, hPm, hℓm_eq⟩ :=
    growing_spectral_data hm1 hEig
  have hπ_cont : Continuous (coordPi hm1 ℓ₂) := continuous_coordPi hm1 ℓ₂
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) Sig)
    hπ_cont.continuousOn
  refine ⟨max 1 B, coordPi hm1 ℓ₂, le_max_left 1 B, hπ_cont.continuousOn, ?_, ?_, ?_, ?_⟩
  · -- (1) `(π σ).comp (ι σ) = id` and `‖π σ‖ ≤ M`
    intro σ hσ
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    exact ⟨coordPi_comp_iota hm1 hq'_ae h2q hσ.1 ha (hιae σ hσ),
      (hB σ hσ).trans (le_max_right 1 B)⟩
  · -- (2) Rotation action
    intro σ hσ τ hτ θ r
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    have hrotMat : LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin ![![r * Real.cos θ, -r * Real.sin θ],
                                 ![r * Real.sin θ,  r * Real.cos θ]]) =
        rotScaleCLM r θ := rfl
    rw [(eulerData_unique hm hD hσ).2 τ hτ, hrotMat]
    exact E_pl_comp_iota_rot hm1 hq'_ae h2q hmq hP₂ hPm ha hτ (hιae σ hσ)
  · -- (3) Commutation
    intro σ hσ τ hτ
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    rw [(eulerData_unique hm hD hσ).2 τ hτ]
    ext1 f
    apply (toL2w m).injective
    simp only [ContinuousLinearMap.comp_apply]
    rw [toL2w_E_pl hm1 ha hτ, toL2w_iota_coordPi hm1 hq'_ae hℓm_eq hσ.1 ha (hιae σ hσ) f,
      toL2w_iota_coordPi hm1 hq'_ae hℓm_eq hσ.1 ha (hιae σ hσ) (E_pl m σ τ f),
      toL2w_E_pl hm1 ha hτ, Planar.dilation_conj hm1 ha τ]
    simp only [ContinuousLinearMap.comp_apply, dilW_inv_apply hm1 ha]
    congr 1
    have hcomm_apply := congrArg
      (fun S : Planar.L2w m →L[ℂ] Planar.L2w m =>
        S (Planar.dilW hm1 (inv_pos.2 ha) (toL2w m f)))
      (eulerGroupW_comp_growingProjW hm1 hP₂ hPm (τ / (1 + σ) ^ 2))
    simpa only [ContinuousLinearMap.comp_apply] using hcomm_apply
  · -- (4) Uniform complement bound
    intro η hη
    obtain ⟨C₀, hC₀, hsec⟩ := Planar.exists_uniform_sector_bound hm1
      (PartI.sectorOneStableAll m hm1) hEig.re_pos hq'0 hq' hP₂ hPm hη
    have hA_pos : 0 < 1 + Sig := by linarith
    refine ⟨(1 + Sig) ^ (m / 2) * C₀, mul_pos (Real.rpow_pos_of_pos hA_pos _) hC₀, ?_⟩
    intro σ hσ τ hτ
    have ha : 0 < 1 + σ := by linarith [hσ.1]
    have ha1 : 1 ≤ 1 + σ := by linarith [hσ.1]
    have haA : 1 + σ ≤ 1 + Sig := by linarith [hσ.2]
    have hrealify : (E σ τ).comp (ContinuousLinearMap.id ℝ (Xm m) - (ι σ).comp (coordPi hm1 ℓ₂ σ)) =
        realify (Planar.eulerGroupDil hm1 ha τ ∘L
          (1 - Planar.dilW hm1 ha ∘L
            Planar.growingProjW (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')) ∘L
            Planar.dilW hm1 (inv_pos.2 ha))) := by
      rw [(eulerData_unique hm hD hσ).2 τ hτ, E_pl_eq hm1 ha τ]
      ext1 f
      simp only [ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply, realify_apply,
        (toL2w m).map_sub, toL2w_iota_coordPi hm1 hq'_ae hℓm_eq hσ.1 ha (hιae σ hσ) f]
      rfl
    rw [hrealify]
    exact (norm_realify_le _).trans
      (norm_eulerGroupDil_compl_le hm1 hη hC₀ hsec ha ha1 haA hτ)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.planarEulerSpectral
