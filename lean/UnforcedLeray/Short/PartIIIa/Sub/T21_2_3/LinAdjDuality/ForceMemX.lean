import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub

/-!
# The interaction density is in `X_m` (`LadForceMemX`, SP 3053-3054)

Weighted Cauchy-Schwarz: `jb^{m/2} |pd_j E| ≤ jb^{(m+2)/2} |pd_j E| ≤ C` on the cell, so
`jb^{m/2} |u·∇E| ≤ C (|u₀| + |u₁|)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace ForceMemXAux

lemma contDiff_pd {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd k g) := by
  have hc : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact hc.clm_apply contDiff_const

lemma contDiff_Ec {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr ρ) := by
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ
  have hv1 : ContDiff ℝ 1 (tr.v ρ) := hv.of_le (by simp)
  have hf1 : ContDiff ℝ ∞ (fun w => tr.v ρ w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hf0 : ContDiff ℝ ∞ (fun w => tr.v ρ w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hfun : UnforcedLeray.B0238.Ec tr ρ
      = fun z => B0579.pd 0 (fun w => tr.v ρ w 1) z - B0579.pd 1 (fun w => tr.v ρ w 0) z := by
    funext z
    unfold UnforcedLeray.B0238.Ec
    rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 z]
    simp [B0579.pd, B0579.dir]
  rw [hfun]
  exact (contDiff_pd hf1 0).sub (contDiff_pd hf0 1)

lemma eLpNorm_cellMeasure_cx (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    eLpNorm f 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => B0579.jb x ^ (m / 2) * ‖f x‖) 2 (volume.restrict (B0579.cell c)) := by
  rw [← eLpNorm_norm, B0579.eLpNorm_cellMeasure]

end ForceMemXAux

theorem ladForceMemX (m : ℝ) : LadForceMemX m := by
  intro ν c tr S C ρ hbd hρ u hu
  have hρ0 : 0 ≤ ρ := hρ.1
  have hpdc : ∀ j : Fin 2, Continuous (B0579.pd j (UnforcedLeray.B0238.Ec tr ρ)) := fun j =>
    (ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_Ec tr hρ0) j).continuous
  -- measurability
  have hmeas : AEStronglyMeasurable (ladForce tr u ρ) (B0579.cellMeasure c m) := by
    have hm : ∀ j : Fin 2, AEStronglyMeasurable (fun x => u x j) (B0579.cellMeasure c m) :=
      fun j => (hu j).1.mono_ac (B0579.cellMeasure_ac c m)
    have hc : ∀ j : Fin 2, AEStronglyMeasurable
        (fun x => ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ))
        (B0579.cellMeasure c m) := fun j =>
      (Complex.continuous_ofReal.comp (hpdc j)).aestronglyMeasurable
    exact ((hm 0).mul (hc 0)).add ((hm 1).mul (hc 1))
  -- the key estimate
  have hC : ∀ x ∈ B0579.cell c, 0 ≤ C := fun x hx => (abs_nonneg _).trans ((hbd ρ hρ x hx).1 0)
  have hpt : ∀ x ∈ B0579.cell c,
      B0579.jb x ^ (m / 2) * ‖ladForce tr u ρ x‖ ≤ C * (‖u x 0‖ + ‖u x 1‖) := by
    intro x hx
    have hj1 : 1 ≤ B0579.jb x := by
      unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hw : B0579.jb x ^ (m / 2) ≤ B0579.jb x ^ ((m + 2) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
    have hb : ∀ j : Fin 2,
        B0579.jb x ^ (m / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x| ≤ C := fun j =>
      (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans ((hbd ρ hρ x hx).2 j)
    have hw0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have h1 : ‖ladForce tr u ρ x‖ ≤
        ‖u x 0‖ * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x| +
          ‖u x 1‖ * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x| := by
      unfold ladForce
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc B0579.jb x ^ (m / 2) * ‖ladForce tr u ρ x‖
        ≤ B0579.jb x ^ (m / 2) * (‖u x 0‖ * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x| +
          ‖u x 1‖ * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x|) :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = ‖u x 0‖ * (B0579.jb x ^ (m / 2) * |B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x|) +
          ‖u x 1‖ * (B0579.jb x ^ (m / 2) * |B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x|) := by
          ring
      _ ≤ ‖u x 0‖ * C + ‖u x 1‖ * C :=
          add_le_add (mul_le_mul_of_nonneg_left (hb 0) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hb 1) (norm_nonneg _))
      _ = C * (‖u x 0‖ + ‖u x 1‖) := by ring
  have hbound : eLpNorm (ladForce tr u ρ) 2 (B0579.cellMeasure c m) ≤
      ENNReal.ofReal C * (eLpNorm (fun x => u x 0) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => u x 1) 2 (volume.restrict (B0579.cell c))) := by
    by_cases hne : (B0579.cell c).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      have hC0 : 0 ≤ C := hC x0 hx0
      rw [ForceMemXAux.eLpNorm_cellMeasure_cx]
      have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
          ‖B0579.jb x ^ (m / 2) * ‖ladForce tr u ρ x‖‖ ≤
            ‖C • (fun x => ‖u x 0‖ + ‖u x 1‖) x‖ := by
        have hms : MeasurableSet (B0579.cell c) := by
          unfold B0579.cell
          exact measurableSet_Ico.prod MeasurableSet.univ
        filter_upwards [ae_restrict_mem hms] with x hx
        have hw0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (norm_nonneg _)),
          smul_eq_mul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hC0 (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
        exact hpt x hx
      have hu0 := (hu 0).1.norm
      have hu1 := (hu 1).1.norm
      calc _ ≤ eLpNorm (C • (fun x => ‖u x 0‖ + ‖u x 1‖)) 2 (volume.restrict (B0579.cell c)) :=
            eLpNorm_mono_ae hae
        _ = ‖C‖ₑ * eLpNorm (fun x => ‖u x 0‖ + ‖u x 1‖) 2
              (volume.restrict (B0579.cell c)) := eLpNorm_const_smul _ _ _ _
        _ ≤ ENNReal.ofReal C * (eLpNorm (fun x => ‖u x 0‖) 2 (volume.restrict (B0579.cell c)) +
              eLpNorm (fun x => ‖u x 1‖) 2 (volume.restrict (B0579.cell c))) := by
            rw [Real.enorm_eq_ofReal hC0]
            refine mul_le_mul_right ?_ _
            have := eLpNorm_add_le (μ := volume.restrict (B0579.cell c)) (p := 2)
              hu0 hu1 (by norm_num)
            simp only [eLpNorm_norm] at this ⊢
            exact this
        _ = _ := by simp only [eLpNorm_norm]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : B0579.cellMeasure c m = 0 := by
        unfold B0579.cellMeasure
        rw [hne]; simp
      rw [h0]; simp
  refine ⟨⟨hmeas, ?_⟩, hbound⟩
  refine lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.2 ⟨(hu 0).2, (hu 1).2⟩))

end UnforcedLeray.Short.IIIa
