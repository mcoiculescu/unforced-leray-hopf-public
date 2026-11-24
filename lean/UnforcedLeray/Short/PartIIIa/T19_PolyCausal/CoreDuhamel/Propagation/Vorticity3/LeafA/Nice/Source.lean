import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2_3_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.DirNice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay.FderivComm
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.DualBounds
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.WeakCellAeUnique

/-!
# `LeafA/Nice/Source`: classical Leray-projected free solution and `X_{9,c}^0` vorticity source

Constructs the smooth-in-time Leray-projected free causal solution `(b_cl, G_cl)` and explicit
`X_{9,c}^0` vorticity source `f` for a `NiceForce (ν ^ (-2 : ℝ)) F`, proving `niceSourceConstruct`
(SP 3427-3440, 3462-3466, 3481-3491, 3541-3545).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.CoreDuhamelNiceAux

open UnforcedLeray.Short.IIIa

/-! ## 1. Complex partial derivatives `pdC`, `LMPd`, and cylinder-test integration by parts -/

private theorem nsrc_pdC_add {f g : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    pdC j (fun y => f y + g y) x = pdC j f x + pdC j g x := by
  simp only [pdC]
  rw [fderiv_fun_add hf hg]
  rfl

private theorem nsrc_pdC_sub {f g : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    pdC j (fun y => f y - g y) x = pdC j f x - pdC j g x := by
  simp only [pdC]
  rw [fderiv_fun_sub hf hg]
  rfl

private theorem nsrc_pdC_mul {f g : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 2) :
    pdC j (fun y => f y * g y) x = pdC j f x * g x + f x * pdC j g x := by
  change (fderiv ℝ (f * g) x) (B0579.dir j) =
    (fderiv ℝ f x) (B0579.dir j) * g x + f x * (fderiv ℝ g x) (B0579.dir j)
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  change f x * (fderiv ℝ g x) (B0579.dir j) + g x * (fderiv ℝ f x) (B0579.dir j) = _
  ring

private theorem nsrc_pdC_ofReal {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (j : Fin 2) :
    pdC j (fun y => (f y : ℂ)) x = (B0579.pd j f x : ℂ) :=
  DFunLike.congr_fun (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv (B0579.dir j)

private theorem nsrc_pdC_pdC_eq {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) (x : ℝ × ℝ) :
    pdC i (pdC j f) x = fderiv ℝ (fderiv ℝ f) x (B0579.dir i) (B0579.dir j) := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  show fderiv ℝ (fun y => fderiv ℝ f y (B0579.dir j)) x (B0579.dir i) = _
  rw [fderiv_clm_apply (hdf x) (differentiableAt_const _)]
  simp

private theorem nsrc_pdC_comm {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) (x : ℝ × ℝ) :
    pdC i (pdC j f) x = pdC j (pdC i f) x := by
  rw [nsrc_pdC_pdC_eq hf, nsrc_pdC_pdC_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

private theorem nsrc_pdC_re {f : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) (j : Fin 2) :
    B0579.pd j (fun y => (f y).re) x = (pdC j f x).re :=
  DFunLike.congr_fun (Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv (B0579.dir j)

private theorem nsrc_pdC_im {f : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) (j : Fin 2) :
    B0579.pd j (fun y => (f y).im) x = (pdC j f x).im :=
  DFunLike.congr_fun (Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv (B0579.dir j)

private theorem nsrc_LMPd_eq_pdC {f : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (j : Fin 2) :
    LMPd j f x = pdC j f x := by
  unfold LMPd
  rw [nsrc_pdC_re hf j, nsrc_pdC_im hf j, mul_comm Complex.I]
  exact Complex.re_add_im _

private theorem nsrc_ae_zero_of_cylTest {c : ℝ} {d : ℝ × ℝ → ℂ}
    (hint : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => d x * (ψ x : ℂ)) (B0579.cell c))
    (hzero : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, d x * (ψ x : ℂ) = 0) :
    d =ᵐ[volume.restrict (B0579.cell c)] 0 := by
  have hd : HasWeakCellDerivC c 0 (fun _ => 0) d := by
    refine ⟨fun ψ hψ => ⟨by simp, hint ψ hψ⟩, fun ψ hψ => ?_⟩
    simp [hzero ψ hψ]
  exact weakCellAeUnique c 0 (fun _ => 0) d (fun _ => 0) hd (HasWeakCellDerivC.zero c 0)

private theorem nsrc_weak_ibp_complex {c : ℝ} {j : Fin 2} {φ g h : ℝ × ℝ → ℂ}
    (hg : HasWeakCellDerivC c j φ g) (hh : ContDiff ℝ ∞ h)
    (hper : ∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x)
    {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) :
    IntegrableOn (fun x => φ x * (pdC j h x * (χ x : ℂ) + h x * (B0579.pd j χ x : ℂ)))
        (B0579.cell c) ∧
      IntegrableOn (fun x => g x * (h x * (χ x : ℂ))) (B0579.cell c) ∧
      ∫ x in B0579.cell c, φ x * (pdC j h x * (χ x : ℂ) + h x * (B0579.pd j χ x : ℂ)) =
        -∫ x in B0579.cell c, g x * (h x * (χ x : ℂ)) := by
  set hR : ℝ × ℝ → ℝ := fun x => (h x).re
  set hI : ℝ × ℝ → ℝ := fun x => (h x).im
  have hhR : ContDiff ℝ ∞ hR := Complex.reCLM.contDiff.comp hh
  have hhI : ContDiff ℝ ∞ hI := Complex.imCLM.contDiff.comp hh
  have hperR : ∀ x : ℝ × ℝ, hR (x.1 + c, x.2) = hR x := fun x => congrArg Complex.re (hper x)
  have hperI : ∀ x : ℝ × ℝ, hI (x.1 + c, x.2) = hI x := fun x => congrArg Complex.im (hper x)
  have htestR : B0579.IsCylTest c (fun x => hR x * χ x) := V1.cylTest_mul_left hhR hperR hχ
  have htestI : B0579.IsCylTest c (fun x => hI x * χ x) := V1.cylTest_mul_left hhI hperI hχ
  have hdiff : Differentiable ℝ h := hh.differentiable (by simp)
  have hdiffR : Differentiable ℝ hR := hhR.differentiable (by simp)
  have hdiffI : Differentiable ℝ hI := hhI.differentiable (by simp)
  obtain ⟨IR1, IR2⟩ := hg.1 _ htestR
  obtain ⟨II1, II2⟩ := hg.1 _ htestI
  have eqR := hg.2 _ htestR
  have eqI := hg.2 _ htestI
  have hpt1 : (fun x => φ x * (pdC j h x * (χ x : ℂ) + h x * (B0579.pd j χ x : ℂ))) =
      fun x => φ x * (B0579.pd j (fun y => hR y * χ y) x : ℂ) +
        Complex.I * (φ x * (B0579.pd j (fun y => hI y * χ y) x : ℂ)) := by
    funext x
    rw [V1.pd_mul' hdiffR hχ.differentiable j x, V1.pd_mul' hdiffI hχ.differentiable j x]
    have h1 : B0579.pd j hR x = (pdC j h x).re := nsrc_pdC_re (hdiff x) j
    have h2 : B0579.pd j hI x = (pdC j h x).im := nsrc_pdC_im (hdiff x) j
    have hc1 : ((pdC j h x).re : ℂ) + Complex.I * ((pdC j h x).im : ℂ) = pdC j h x := by
      rw [mul_comm Complex.I]; exact Complex.re_add_im _
    have hc2 : (hR x : ℂ) + Complex.I * (hI x : ℂ) = h x := by
      dsimp [hR, hI]; rw [mul_comm Complex.I]; exact Complex.re_add_im _
    rw [h1, h2]
    push_cast
    linear_combination φ x * (χ x : ℂ) * hc1.symm + φ x * (B0579.pd j χ x : ℂ) * hc2.symm
  have hpt2 : (fun x => g x * (h x * (χ x : ℂ))) =
      fun x => g x * ((hR x * χ x : ℝ) : ℂ) +
        Complex.I * (g x * ((hI x * χ x : ℝ) : ℂ)) := by
    funext x
    have hc2 : (hR x : ℂ) + Complex.I * (hI x : ℂ) = h x := by
      dsimp [hR, hI]; rw [mul_comm Complex.I]; exact Complex.re_add_im _
    push_cast
    linear_combination g x * (χ x : ℂ) * hc2.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hpt1]; exact IR1.add (II1.const_mul Complex.I)
  · rw [hpt2]; exact IR2.add (II2.const_mul Complex.I)
  · rw [hpt1, hpt2, integral_add IR1 (II1.const_mul Complex.I),
      integral_add IR2 (II2.const_mul Complex.I),
      integral_const_mul, integral_const_mul, eqR, eqI]
    ring

/-! ## 2. Weighted `X_{9,c}` bilinear bounds and time-continuity -/

private theorem nsrc_eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (h : α → E) (μ : Measure α) :
    eLpNorm h 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have hpow : ((∫⁻ x, ‖h x‖ₑ ^ ENNReal.toReal 2 ∂μ) ^ (1 / ENNReal.toReal 2)) ^ 2 =
      ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hpow]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

private theorem nsrc_xNorm_mul_le {c M : ℝ} (hM : 0 ≤ M)
    {w h : ℝ × ℝ → ℂ}
    (hw : ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * ‖w x‖ ≤ M) :
    xNorm c 9 (fun x => w x * h x) ≤
      ENNReal.ofReal M * eLpNorm h 2 (volume.restrict (B0579.cell c)) := by
  have hsq : xNorm c 9 (fun x => w x * h x) ^ 2 ≤
      (ENNReal.ofReal M * eLpNorm h 2 (volume.restrict (B0579.cell c))) ^ 2 := by
    rw [CoreDuhamelRepSub.xNorm_sq_eq, mul_pow, ← ENNReal.ofReal_pow hM,
      nsrc_eLpNorm_two_sq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (B0579.measurableSet_cell c) fun x hx => ?_
    rw [← ENNReal.ofReal_mul (pow_nonneg hM 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hjb9 : B0579.jb x ^ (9 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
      rw [B0579.bracket_rpow 9 x, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (B0579.jb_pos x).le]
      norm_num
    have hwx := hw x hx
    have hnn : 0 ≤ B0579.bracket x ^ (9 : ℝ) * ‖w x‖ :=
      mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)
    calc B0579.jb x ^ (9 : ℝ) * ‖w x * h x‖ ^ 2
        = (B0579.bracket x ^ (9 : ℝ) * ‖w x‖) ^ 2 * ‖h x‖ ^ 2 := by
          rw [hjb9, norm_mul]; ring
      _ ≤ M ^ 2 * ‖h x‖ ^ 2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hwx 2) (sq_nonneg _)
  have hpow := ENNReal.rpow_le_rpow hsq (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simpa only [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one] using hpow

private theorem nsrc_eLpNorm_const_mul {α : Type*} [MeasurableSpace α] (k : ℂ)
    (h : α → ℂ) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (fun x => k * h x) p μ = ENNReal.ofReal ‖k‖ * eLpNorm h p μ := by
  change eLpNorm (k • h) p μ = _
  rw [eLpNorm_const_smul, ofReal_norm]

private theorem nsrc_memLp_xNorm_mul {c M : ℝ} (hM : 0 ≤ M)
    {w h : ℝ × ℝ → ℂ}
    (hw_m : AEStronglyMeasurable w (volume.restrict (B0579.cell c)))
    (hw : ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * ‖w x‖ ≤ M)
    (hh : MemLp h 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun x => w x * h x) 2 (B0579.cellMeasure c 9) ∧
      xNorm c 9 (fun x => w x * h x) ≤
        ENNReal.ofReal M * eLpNorm h 2 (volume.restrict (B0579.cell c)) := by
  have hbd := nsrc_xNorm_mul_le (h := h) hM hw
  refine ⟨⟨?_, ?_⟩, hbd⟩
  · exact (hw_m.mul hh.1).mono_ac (withDensity_absolutelyContinuous _ _)
  · exact hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.2)

private theorem nsrc_tendsto_xNorm_mul {c M a_zero H t : ℝ} (hM : 0 ≤ M)
    (ht : t ∈ Ioo a_zero H)
    {w h : ℝ → ℝ × ℝ → ℂ}
    (hw_m : ∀ s ∈ Ioo a_zero H, AEStronglyMeasurable (w s) (volume.restrict (B0579.cell c)))
    (hw_bd : ∀ s ∈ Ioo a_zero H, ∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * ‖w s x‖ ≤ M)
    (hw_cont : ∀ x ∈ B0579.cell c, ContinuousAt (fun s => w s x) t)
    (hh_lp : ∀ s ∈ Ioo a_zero H, MemLp (h s) 2 (volume.restrict (B0579.cell c)))
    (hh_cont : Tendsto (fun s => eLpNorm (h s - h t) 2 (volume.restrict (B0579.cell c)))
      (𝓝 t) (𝓝 0)) :
    Tendsto (fun s => xNorm c 9 (fun x => w s x * h s x - w t x * h t x)) (𝓝 t) (𝓝 0) := by
  have hT1 : Tendsto (fun s => xNorm c 9 (fun x => w s x * (h s x - h t x))) (𝓝 t) (𝓝 0) := by
    have hlim : Tendsto (fun s => ENNReal.ofReal M *
        eLpNorm (h s - h t) 2 (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hh_cont (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact nsrc_xNorm_mul_le hM (hw_bd s hs)
  have hT2_sq : Tendsto (fun s => ∫ x in B0579.cell c,
      B0579.jb x ^ (9 : ℝ) * ‖(w s x - w t x) * h t x‖ ^ 2) (𝓝 t) (𝓝 0) := by
    have hdom : Integrable (fun x => (2 * M) ^ 2 * ‖h t x‖ ^ 2)
        (volume.restrict (B0579.cell c)) :=
      ((hh_lp t ht).norm).integrable_sq.const_mul ((2 * M) ^ 2)
    have hlim0 : ∫ _x in B0579.cell c, (0 : ℝ) = 0 := by simp
    rw [← hlim0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (2 * M) ^ 2 * ‖h t x‖ ^ 2) ?_ ?_ hdom ?_
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      have hjb_m : AEStronglyMeasurable (fun x : ℝ × ℝ => B0579.jb x ^ (9 : ℝ))
          (volume.restrict (B0579.cell c)) :=
        (B0579.continuous_jb_rpow 9).aestronglyMeasurable
      exact hjb_m.mul ((((hw_m s hs).sub (hw_m t ht)).mul (hh_lp t ht).1).norm.pow 2)
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
      have hjb9 : B0579.jb x ^ (9 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
        rw [B0579.bracket_rpow 9 x, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (B0579.jb_pos x).le]
        norm_num
      have hnn : 0 ≤ B0579.jb x ^ (9 : ℝ) * ‖(w s x - w t x) * h t x‖ ^ 2 :=
        mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      have hw_diff : B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖ ≤ 2 * M := by
        calc B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖
            ≤ B0579.bracket x ^ (9 : ℝ) * (‖w s x‖ + ‖w t x‖) :=
              mul_le_mul_of_nonneg_left (norm_sub_le _ _)
                (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
          _ = B0579.bracket x ^ (9 : ℝ) * ‖w s x‖ + B0579.bracket x ^ (9 : ℝ) * ‖w t x‖ := by
              ring
          _ ≤ M + M := add_le_add (hw_bd s hs x hx) (hw_bd t ht x hx)
          _ = 2 * M := by ring
      have hnn' : 0 ≤ B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖ :=
        mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)
      calc B0579.jb x ^ (9 : ℝ) * ‖(w s x - w t x) * h t x‖ ^ 2
          = (B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖) ^ 2 * ‖h t x‖ ^ 2 := by
            rw [hjb9, norm_mul]; ring
        _ ≤ (2 * M) ^ 2 * ‖h t x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn' hw_diff 2) (sq_nonneg _)
    · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
      have hc1 : ContinuousAt (fun s => B0579.jb x ^ (9 : ℝ) * ‖(w s x - w t x) * h t x‖ ^ 2) t :=
        continuousAt_const.mul (((((hw_cont x hx).sub continuousAt_const).mul
          continuousAt_const).norm).pow 2)
      simpa using hc1.tendsto
  have hT2 : Tendsto (fun s => xNorm c 9 (fun x => (w s x - w t x) * h t x)) (𝓝 t) (𝓝 0) := by
    have h_enn : Tendsto (fun s => (ENNReal.ofReal (∫ x in B0579.cell c,
        B0579.jb x ^ (9 : ℝ) * ‖(w s x - w t x) * h t x‖ ^ 2)) ^ (1 / 2 : ℝ)) (𝓝 t) (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = (ENNReal.ofReal 0) ^ (1 / 2 : ℝ) := by simp
      rw [h0]
      exact ((ENNReal.continuous_ofReal.tendsto 0).comp hT2_sq).ennrpow_const (1 / 2)
    refine h_enn.congr' ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hint_sq : Integrable (fun x => B0579.jb x ^ (9 : ℝ) * ‖(w s x - w t x) * h t x‖ ^ 2)
        (volume.restrict (B0579.cell c)) := by
      refine (((hh_lp t ht).norm).integrable_sq.const_mul ((2 * M) ^ 2)).mono' ?_ ?_
      · exact (B0579.continuous_jb_rpow 9).aestronglyMeasurable.mul
          ((((hw_m s hs).sub (hw_m t ht)).mul (hh_lp t ht).1).norm.pow 2)
      · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
        have hjb9 : B0579.jb x ^ (9 : ℝ) = (B0579.bracket x ^ (9 : ℝ)) ^ 2 := by
          rw [B0579.bracket_rpow 9 x, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (B0579.jb_pos x).le]
          norm_num
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)),
          hjb9, norm_mul]
        have hwx : B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖ ≤ 2 * M := by
          calc B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖
              ≤ B0579.bracket x ^ (9 : ℝ) * (‖w s x‖ + ‖w t x‖) :=
                mul_le_mul_of_nonneg_left (norm_sub_le _ _)
                  (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
            _ ≤ 2 * M := by linarith [hw_bd s hs x hx, hw_bd t ht x hx]
        have hnn' : 0 ≤ B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖ :=
          mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)
        calc (B0579.bracket x ^ (9 : ℝ)) ^ 2 * (‖w s x - w t x‖ * ‖h t x‖) ^ 2
            = (B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖) ^ 2 * ‖h t x‖ ^ 2 := by ring
          _ ≤ (2 * M) ^ 2 * ‖h t x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn' hwx 2) (sq_nonneg _)
    rw [ofReal_integral_eq_lintegral_ofReal hint_sq
      (ae_of_all _ fun x => mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _)),
      ← CoreDuhamelRepSub.xNorm_sq_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have hsum : Tendsto (fun s =>
      xNorm c 9 (fun x => w s x * (h s x - h t x)) +
        xNorm c 9 (fun x => (w s x - w t x) * h t x)) (𝓝 t) (𝓝 0) := by
    simpa using hT1.add hT2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  have heq : (fun x => w s x * h s x - w t x * h t x) =
      (fun x => w s x * (h s x - h t x)) + (fun x => (w s x - w t x) * h t x) := by
    funext x; simp only [Pi.add_apply]; ring
  unfold xNorm
  rw [heq]
  have hm1 := (nsrc_memLp_xNorm_mul hM (hw_m s hs) (hw_bd s hs)
    ((hh_lp s hs).sub (hh_lp t ht))).1.1
  have hm2 := (nsrc_memLp_xNorm_mul (M := 2 * M) (mul_nonneg zero_le_two hM)
    ((hw_m s hs).sub (hw_m t ht))
    (fun x hx => by
      calc B0579.bracket x ^ (9 : ℝ) * ‖w s x - w t x‖
          ≤ B0579.bracket x ^ (9 : ℝ) * (‖w s x‖ + ‖w t x‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _)
              (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        _ ≤ 2 * M := by linarith [hw_bd s hs x hx, hw_bd t ht x hx])
    (hh_lp t ht)).1.1
  exact eLpNorm_add_le hm1 hm2 one_le_two

/-! ## 3. Train velocity and vorticity-gradient regularity & weighted bounds -/

private theorem nsrc_trainVel_bdd {ν b A_m : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (coreEnd ν b)) (j : Fin 2) :
    ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * ‖(trainVel tr s x j : ℂ)‖ ≤ A_m := by
  intro x hx
  have h1 := CoreDuhamelRepSub.trainVel_weighted_bound hbd hs x hx
  have hj : ‖(trainVel tr s x j : ℂ)‖ ≤ ‖trainVel tr s x‖ + ‖fderiv ℝ (trainVel tr s) x‖ := by
    rw [Complex.norm_real]
    exact (norm_le_pi_norm (trainVel tr s x) j).trans
      (le_add_of_nonneg_right (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (Real.sqrt_nonneg _) _)).trans h1

private theorem nsrc_contAt_trainVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t : ℝ} (ht : 0 < t) (x : ℝ × ℝ) (j : Fin 2) :
    ContinuousAt (fun s => (trainVel tr s x j : ℂ)) t := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (t, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨ht, mem_univ x⟩
  have hsub : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono Ioi_subset_Ici_self subset_rfl
  have hsm : ContDiffAt ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (t, x) :=
    (tr.isTrain.smooth_v.mono hsub).contDiffAt (hU.mem_nhds hmem)
  have hc1 : ContinuousAt ((fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) ∘ fun s : ℝ => (s, x)) t :=
    ContinuousAt.comp hsm.continuousAt (continuousAt_id.prodMk continuousAt_const)
  have hc2 : ContinuousAt (fun s : ℝ => (tr.v s x j : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.continuousAt.comp hc1)
  refine hc2.congr ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hs0 : 0 ≤ s := le_of_lt hs
  simp [trainVel, hs0]

private theorem nsrc_pdEc_bdd {ν c S C_tr : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c}
    (hLad : LadTrainBdd tr 7 S C_tr)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) S) (j : Fin 2) :
    ∀ x ∈ B0579.cell c,
      B0579.bracket x ^ (9 : ℝ) * ‖(B0579.pd j (UnforcedLeray.B0238.Ec tr s) x : ℂ)‖ ≤
        max C_tr 0 := by
  intro x hx
  have h1 := (hLad s hs x hx).2 j
  have hbr : B0579.bracket x ^ (9 : ℝ) = B0579.jb x ^ ((7 + 2) / 2 : ℝ) := by
    rw [B0579.bracket_rpow 9 x]
    norm_num
  rw [hbr, Complex.norm_real, Real.norm_eq_abs]
  exact h1.trans (le_max_left _ _)

private theorem nsrc_contAt_pdEc {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t : ℝ} (ht : 0 < t) (x : ℝ × ℝ) (j : Fin 2) :
    ContinuousAt (fun s => (B0579.pd j (UnforcedLeray.B0238.Ec tr s) x : ℂ)) t := by
  have hu := tr.isTrain.smooth_v
  have hSmW : UnforcedLeray.B0238.Sm (UnforcedLeray.B0238.Wv tr.v) :=
    ((UnforcedLeray.B0238.sm_Fc hu 1).dir UnforcedLeray.B0238.eQ).sub
      ((UnforcedLeray.B0238.sm_Fc hu 0).dir UnforcedLeray.B0238.eE)
  have hEc_eq : ∀ s : ℝ, 0 < s → ∀ z : ℝ × ℝ,
      UnforcedLeray.B0238.Ec tr s z = UnforcedLeray.B0238.Wv tr.v (s, z) := by
    intro s hs z
    rw [congrFun (V1.Ec_eq tr hs.le) z, V1.pd_eq_partialQ (V1.vC_diff tr hs.le 1),
      V1.pd_eq_partialEta (V1.vC_diff tr hs.le 0)]
    exact congrArg₂ Sub.sub (UnforcedLeray.B0238.pQ hu hs 1 z)
      (UnforcedLeray.B0238.pE hu hs 0 z)
  have htx : ((t, x) : UnforcedLeray.B0238.ST) ∈ UnforcedLeray.B0238.Opos := ht
  fin_cases j
  · have hSm0 := hSmW.dir UnforcedLeray.B0238.eQ
    have hc0 : ContinuousAt (UnforcedLeray.B0238.dir UnforcedLeray.B0238.eQ
        (UnforcedLeray.B0238.Wv tr.v) ∘ fun s : ℝ => (s, x)) t :=
      ContinuousAt.comp (hSm0.contDiffAt htx).continuousAt
        (continuousAt_id.prodMk continuousAt_const)
    have hc : ContinuousAt (fun s : ℝ =>
        (UnforcedLeray.B0238.dir UnforcedLeray.B0238.eQ
          (UnforcedLeray.B0238.Wv tr.v) (s, x) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp hc0
    refine hc.congr ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hdE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr s) :=
      (V1.Ec_contDiff tr (le_of_lt hs)).differentiable (by simp)
    have hfun : UnforcedLeray.B0238.Ec tr s = fun z => UnforcedLeray.B0238.Wv tr.v (s, z) :=
      funext (hEc_eq s hs)
    have hsx : ((s, x) : UnforcedLeray.B0238.ST) ∈ UnforcedLeray.B0238.Opos := hs
    change _ = (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ)
    rw [V1.pd_eq_partialQ hdE x, hfun, UnforcedLeray.B0238.sliceQ (hSmW.differentiableAt hsx)]
  · have hSm1 := hSmW.dir UnforcedLeray.B0238.eE
    have hc1 : ContinuousAt (UnforcedLeray.B0238.dir UnforcedLeray.B0238.eE
        (UnforcedLeray.B0238.Wv tr.v) ∘ fun s : ℝ => (s, x)) t :=
      ContinuousAt.comp (hSm1.contDiffAt htx).continuousAt
        (continuousAt_id.prodMk continuousAt_const)
    have hc : ContinuousAt (fun s : ℝ =>
        (UnforcedLeray.B0238.dir UnforcedLeray.B0238.eE
          (UnforcedLeray.B0238.Wv tr.v) (s, x) : ℂ)) t :=
      Complex.continuous_ofReal.continuousAt.comp hc1
    refine hc.congr ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hdE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr s) :=
      (V1.Ec_contDiff tr (le_of_lt hs)).differentiable (by simp)
    have hfun : UnforcedLeray.B0238.Ec tr s = fun z => UnforcedLeray.B0238.Wv tr.v (s, z) :=
      funext (hEc_eq s hs)
    have hsx : ((s, x) : UnforcedLeray.B0238.ST) ∈ UnforcedLeray.B0238.Opos := hs
    change _ = (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ)
    rw [V1.pd_eq_partialEta hdE x, hfun, UnforcedLeray.B0238.sliceE (hSmW.differentiableAt hsx)]

private theorem nsrc_Ec_memLp2 {ν b A_m : ℝ} (_hν : 0 < ν) (_hAm : 0 ≤ A_m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (coreEnd ν b)) :
    MemLp (fun x => (UnforcedLeray.B0238.Ec tr t x : ℂ)) 2
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) := by
  let c := ν ^ (-2 : ℝ)
  have hcont : Continuous (fun x => (UnforcedLeray.B0238.Ec tr t x : ℂ)) :=
    Complex.continuous_ofReal.comp (V1.Ec_contDiff tr ht.1.le).continuous
  have hm_Ec : AEStronglyMeasurable (fun x => (UnforcedLeray.B0238.Ec tr t x : ℂ))
      (volume.restrict (B0579.cell c)) := hcont.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm_Ec).2 ?_
  have hdom_1d : Integrable (fun y : ℝ => (1 + y ^ 2)⁻¹) := by
    simpa [add_comm] using integrable_inv_one_add_sq
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  have hdom_prod : Integrable (fun x : ℝ × ℝ => (2 * A_m) ^ 2 * (1 + x.2 ^ 2)⁻¹)
      (volume.restrict (B0579.cell c)) := by
    rw [← cellμ_eq c, UnforcedLeray.Cyl.cellμ_eq_prod]
    exact (hdom_1d.comp_snd _).const_mul ((2 * A_m) ^ 2)
  refine hdom_prod.mono' (hm_Ec.norm.pow 2) ?_
  filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hv_bd := CoreDuhamelRepSub.trainVel_weighted_bound hbd ht x hx
  have hv1 : ContDiff ℝ 1 (trainVel tr t) := contDiff_trainVel tr ht.1
  have hE_val : UnforcedLeray.B0238.Ec tr t x =
      B0579.pd 0 (fun y => trainVel tr t y 1) x - B0579.pd 1 (fun y => trainVel tr t y 0) x := by
    rw [congrFun (V1.Ec_eq tr ht.1.le) x, V1.trainVel_fun tr ht.1.le 1,
      V1.trainVel_fun tr ht.1.le 0]
  have hp0 : |B0579.pd 0 (fun y => trainVel tr t y 1) x| ≤ ‖fderiv ℝ (trainVel tr t) x‖ :=
    CurlDualityAux.abs_pd_coord_le hv1 1 0 x
  have hp1 : |B0579.pd 1 (fun y => trainVel tr t y 0) x| ≤ ‖fderiv ℝ (trainVel tr t) x‖ :=
    CurlDualityAux.abs_pd_coord_le hv1 0 1 x
  have hE_abs : |UnforcedLeray.B0238.Ec tr t x| ≤ 2 * ‖fderiv ℝ (trainVel tr t) x‖ := by
    rw [hE_val]
    calc |B0579.pd 0 (fun y => trainVel tr t y 1) x - B0579.pd 1 (fun y => trainVel tr t y 0) x|
        ≤ |B0579.pd 0 (fun y => trainVel tr t y 1) x| +
            |B0579.pd 1 (fun y => trainVel tr t y 0) x| := abs_sub _ _
      _ ≤ 2 * ‖fderiv ℝ (trainVel tr t) x‖ := by linarith
  have hbr_ge : Real.sqrt (1 + x.2 ^ 2) ≤ B0579.bracket x ^ (9 : ℝ) := by
    have hjb_ge : 1 + x.2 ^ 2 ≤ B0579.jb x := by
      unfold B0579.jb; linarith [sq_nonneg x.1]
    have h1 : 1 ≤ 1 + x.2 ^ 2 := by linarith [sq_nonneg x.2]
    calc Real.sqrt (1 + x.2 ^ 2)
        ≤ Real.sqrt (B0579.jb x) := Real.sqrt_le_sqrt hjb_ge
      _ = (Real.sqrt (B0579.jb x)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.sqrt (B0579.jb x)) ^ (9 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num)
          exact Real.one_le_sqrt.2 (h1.trans hjb_ge)
      _ = B0579.bracket x ^ (9 : ℝ) := rfl
  have hsqrt_pos : 0 < Real.sqrt (1 + x.2 ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hfd_le : ‖fderiv ℝ (trainVel tr t) x‖ ≤ A_m * (Real.sqrt (1 + x.2 ^ 2))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hsqrt_pos, mul_comm]
    calc Real.sqrt (1 + x.2 ^ 2) * ‖fderiv ℝ (trainVel tr t) x‖
        ≤ B0579.bracket x ^ (9 : ℝ) * ‖fderiv ℝ (trainVel tr t) x‖ :=
          mul_le_mul_of_nonneg_right hbr_ge (norm_nonneg _)
      _ ≤ B0579.bracket x ^ (9 : ℝ) * (‖trainVel tr t x‖ + ‖fderiv ℝ (trainVel tr t) x‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
            (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      _ ≤ A_m := hv_bd
  have hE_le : |UnforcedLeray.B0238.Ec tr t x| ≤ 2 * A_m * (Real.sqrt (1 + x.2 ^ 2))⁻¹ := by
    calc |UnforcedLeray.B0238.Ec tr t x|
        ≤ 2 * ‖fderiv ℝ (trainVel tr t) x‖ := hE_abs
      _ ≤ 2 * (A_m * (Real.sqrt (1 + x.2 ^ 2))⁻¹) :=
          mul_le_mul_of_nonneg_left hfd_le (by norm_num)
      _ = 2 * A_m * (Real.sqrt (1 + x.2 ^ 2))⁻¹ := by ring
  calc UnforcedLeray.B0238.Ec tr t x ^ 2
      = |UnforcedLeray.B0238.Ec tr t x| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * A_m * (Real.sqrt (1 + x.2 ^ 2))⁻¹) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hE_le 2
    _ = (2 * A_m) ^ 2 * ((Real.sqrt (1 + x.2 ^ 2)) ^ 2)⁻¹ := by rw [mul_pow, inv_pow]
    _ = (2 * A_m) ^ 2 * (1 + x.2 ^ 2)⁻¹ := by rw [Real.sq_sqrt (by positivity)]

/-! ## 4. Unprojected classical solve `u_raw`, smooth curl `ω_raw`, and Leray-projected `(b_cl, G_cl)` -/

private theorem nsrc_duhamel_zero_le (ν : ℝ) (g : ℝ × (ℝ × ℝ) → ℂ) {a : ℝ}
    (hg : ∀ s < a, ∀ x, g (s, x) = 0) :
    ∀ s ≤ a, ∀ x, duhamelHeat ν g s x = 0 := by
  intro s hs x
  unfold duhamelHeat
  have h0 : ∀ r ∈ Ioi (0 : ℝ),
      (∫ z : ℝ × ℝ, ((UnforcedLeray.B0284.heatKernel2 (ν * r) z : ℝ) : ℂ) *
        g (s - r, (x.1 - z.1, x.2 - z.2))) = 0 := by
    intro r hr
    have hlt : s - r < a := by linarith [mem_Ioi.1 hr]
    simp [hg (s - r) hlt]
  rw [setIntegral_congr_fun measurableSet_Ioi h0]
  simp

private theorem nsrc_scalar_gauss_memLp_and_cont {c : ℝ} (_hc : 0 < c)
    {om : ℝ × (ℝ × ℝ) → ℂ} (hsm : ContDiff ℝ ∞ om) (hdec : ScalarGaussDecayLoc om) :
    (∀ s : ℝ, IntegrableOn (fun x => om (s, x)) (B0579.cell c) ∧
      MemLp (fun x => om (s, x)) 2 (volume.restrict (B0579.cell c)) ∧
      ∀ j : Fin 2, MemLp (fun x => pdC j (fun y => om (s, y)) x) 2
        (volume.restrict (B0579.cell c))) ∧
    (∀ H : ℝ, ∃ M_ω : ℝ, 0 ≤ M_ω ∧ ∀ s ≤ H, ∀ j : Fin 2,
      eLpNorm (fun x => pdC j (fun y => om (s, y)) x) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal M_ω) ∧
    (∀ t : ℝ, ∀ j : Fin 2,
      Tendsto (fun s => eLpNorm
        (fun x => pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x) 2
        (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0)) := by
  have hdir : ∀ j : Fin 2, ‖B0579.dir j‖ ≤ 1 := CurlDualityAux.norm_dir_le_one
  have hpd_le : ∀ s x (j : Fin 2), ‖pdC j (fun y => om (s, y)) x‖ ≤
      ‖fderiv ℝ (fun y => om (s, y)) x‖ := by
    intro s x j
    unfold pdC
    exact ((fderiv ℝ (fun y => om (s, y)) x).le_opNorm (B0579.dir j)).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hdir j))
  have hcont_ω : ∀ s, Continuous fun x => om (s, x) := fun s =>
    hsm.continuous.comp (continuous_const.prodMk continuous_id)
  have hcont_pd : ∀ s (j : Fin 2), Continuous fun x => pdC j (fun y => om (s, y)) x := by
    intro s j
    have hC : ContDiff ℝ ∞ fun y => om (s, y) := hsm.comp (contDiff_const.prodMk contDiff_id)
    exact (hC.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcellμ : UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := cellμ_eq c
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨C, κ, hκ, hb⟩ := hdec s
    have hdom2 := (gauss_dom_memLp_aux c κ hκ).const_mul (max C 0)
    rw [hcellμ] at hdom2
    have hm_ω : MemLp (fun x => om (s, x)) 2 (volume.restrict (B0579.cell c)) := by
      refine hdom2.of_le (hcont_ω s).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      have h1 := hb s x le_rfl
      have hC0 : C ≤ max C 0 := le_max_left _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _))]
      calc ‖om (s, x)‖ ≤ C * Real.exp (-κ * x.2 ^ 2) :=
            by linarith [norm_nonneg (fderiv ℝ (fun y => om (s, y)) x)]
        _ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) :=
            mul_le_mul_of_nonneg_right hC0 (Real.exp_nonneg _)
    have hint_ω : IntegrableOn (fun x => om (s, x)) (B0579.cell c) := by
      have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ico (-c / 2) (c / 2))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
      have hg1 : Integrable (fun x : ℝ × ℝ => max C 0 * Real.exp (-κ * x.2 ^ 2))
          (volume.restrict (B0579.cell c)) := by
        rw [← hcellμ, UnforcedLeray.Cyl.cellμ_eq_prod]
        exact ((integrable_exp_neg_mul_sq hκ).comp_snd _).const_mul (max C 0)
      refine hg1.mono' (hcont_ω s).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      have h1 := hb s x le_rfl
      calc ‖om (s, x)‖ ≤ C * Real.exp (-κ * x.2 ^ 2) :=
            by linarith [norm_nonneg (fderiv ℝ (fun y => om (s, y)) x)]
        _ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    refine ⟨hint_ω, hm_ω, fun j => ?_⟩
    refine hdom2.of_le (hcont_pd s j).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have h1 := hb s x le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _))]
    calc ‖pdC j (fun y => om (s, y)) x‖
        ≤ ‖fderiv ℝ (fun y => om (s, y)) x‖ := hpd_le s x j
      _ ≤ C * Real.exp (-κ * x.2 ^ 2) := by linarith [norm_nonneg (om (s, x))]
      _ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · intro H
    obtain ⟨C, κ, hκ, hb⟩ := hdec H
    have hdom2 := (gauss_dom_memLp_aux c κ hκ).const_mul (max C 0)
    rw [hcellμ] at hdom2
    set D_norm : ℝ := (eLpNorm (fun x : ℝ × ℝ => max C 0 * Real.exp (-κ * x.2 ^ 2)) 2
      (volume.restrict (B0579.cell c))).toReal
    refine ⟨D_norm, ENNReal.toReal_nonneg, fun s hs j => ?_⟩
    have hle : eLpNorm (fun x => pdC j (fun y => om (s, y)) x) 2
        (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun x : ℝ × ℝ => max C 0 * Real.exp (-κ * x.2 ^ 2)) 2
          (volume.restrict (B0579.cell c)) := by
      refine eLpNorm_mono fun x => ?_
      have h1 := hb s x hs
      rw [Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _))]
      calc ‖pdC j (fun y => om (s, y)) x‖
          ≤ ‖fderiv ℝ (fun y => om (s, y)) x‖ := hpd_le s x j
        _ ≤ C * Real.exp (-κ * x.2 ^ 2) := by linarith [norm_nonneg (om (s, x))]
        _ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    exact hle.trans_eq (ENNReal.ofReal_toReal hdom2.2.ne).symm
  · intro t j
    obtain ⟨C, κ, hκ, hb⟩ := hdec (t + 1)
    have hdom2 := (gauss_dom_memLp_aux c κ hκ).const_mul (2 * max C 0)
    rw [hcellμ] at hdom2
    have hdom_sq : Integrable (fun x : ℝ × ℝ => (2 * max C 0 * Real.exp (-κ * x.2 ^ 2)) ^ 2)
        (volume.restrict (B0579.cell c)) := hdom2.integrable_sq
    have hsq_lim : Tendsto (fun s => ∫ x in B0579.cell c,
        ‖pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x‖ ^ 2) (𝓝 t) (𝓝 0) := by
      have h0 : ∫ _x in B0579.cell c, (0 : ℝ) = 0 := by simp
      rw [← h0]
      refine tendsto_integral_filter_of_dominated_convergence
        (fun x => (2 * max C 0 * Real.exp (-κ * x.2 ^ 2)) ^ 2) ?_ ?_ hdom_sq ?_
      · filter_upwards [Iio_mem_nhds (lt_add_one t)] with s _
        exact (((hcont_pd s j).sub (hcont_pd t j)).norm.pow 2).aestronglyMeasurable
      · filter_upwards [Iio_mem_nhds (lt_add_one t)] with s hs
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hs1 : ‖pdC j (fun y => om (s, y)) x‖ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) := by
          calc ‖pdC j (fun y => om (s, y)) x‖
              ≤ ‖fderiv ℝ (fun y => om (s, y)) x‖ := hpd_le s x j
            _ ≤ C * Real.exp (-κ * x.2 ^ 2) :=
                by linarith [hb s x (le_of_lt hs), norm_nonneg (om (s, x))]
            _ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
        have ht1 : ‖pdC j (fun y => om (t, y)) x‖ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) := by
          calc ‖pdC j (fun y => om (t, y)) x‖
              ≤ ‖fderiv ℝ (fun y => om (t, y)) x‖ := hpd_le t x j
            _ ≤ C * Real.exp (-κ * x.2 ^ 2) :=
                by linarith [hb t x (by linarith), norm_nonneg (om (t, x))]
            _ ≤ max C 0 * Real.exp (-κ * x.2 ^ 2) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
        have hsub : ‖pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x‖ ≤
            2 * max C 0 * Real.exp (-κ * x.2 ^ 2) := by
          calc ‖pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x‖
              ≤ ‖pdC j (fun y => om (s, y)) x‖ + ‖pdC j (fun y => om (t, y)) x‖ := norm_sub_le _ _
            _ ≤ 2 * max C 0 * Real.exp (-κ * x.2 ^ 2) := by linarith
        exact pow_le_pow_left₀ (norm_nonneg _) hsub 2
      · refine Eventually.of_forall fun x => ?_
        have hcs : Continuous fun s => ‖pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x‖ ^ 2 :=
          ((((cc_pdC_slice_cont hsm j x).sub continuous_const).norm).pow 2)
        simpa using hcs.tendsto t
    have h_enn : Tendsto (fun s => (ENNReal.ofReal (∫ x in B0579.cell c,
        ‖pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x‖ ^ 2)) ^ (1 / 2 : ℝ))
        (𝓝 t) (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = (ENNReal.ofReal 0) ^ (1 / 2 : ℝ) := by simp
      rw [h0]
      exact ((ENNReal.continuous_ofReal.tendsto 0).comp hsq_lim).ennrpow_const (1 / 2)
    refine h_enn.congr' ?_
    filter_upwards [Iio_mem_nhds (lt_add_one t)] with s hs
    have hmp_s : MemLp (fun x => pdC j (fun y => om (s, y)) x) 2 (volume.restrict (B0579.cell c)) := by
      refine hdom2.of_le (hcont_pd s j).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_nonneg _))]
      have h1 := hb s x (le_of_lt hs)
      calc ‖pdC j (fun y => om (s, y)) x‖
          ≤ ‖fderiv ℝ (fun y => om (s, y)) x‖ := hpd_le s x j
        _ ≤ C * Real.exp (-κ * x.2 ^ 2) := by linarith [norm_nonneg (om (s, x))]
        _ ≤ 2 * max C 0 * Real.exp (-κ * x.2 ^ 2) := by
            nlinarith [le_max_left C 0, le_max_right C 0, Real.exp_nonneg (-κ * x.2 ^ 2)]
    have hmp_t : MemLp (fun x => pdC j (fun y => om (t, y)) x) 2 (volume.restrict (B0579.cell c)) := by
      refine hdom2.of_le (hcont_pd t j).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_nonneg _))]
      have h1 := hb t x (by linarith)
      calc ‖pdC j (fun y => om (t, y)) x‖
          ≤ ‖fderiv ℝ (fun y => om (t, y)) x‖ := hpd_le t x j
        _ ≤ C * Real.exp (-κ * x.2 ^ 2) := by linarith [norm_nonneg (om (t, x))]
        _ ≤ 2 * max C 0 * Real.exp (-κ * x.2 ^ 2) := by
            nlinarith [le_max_left C 0, le_max_right C 0, Real.exp_nonneg (-κ * x.2 ^ 2)]
    have hint_sq : Integrable
        (fun x => ‖pdC j (fun y => om (s, y)) x - pdC j (fun y => om (t, y)) x‖ ^ 2)
        (volume.restrict (B0579.cell c)) := ((hmp_s.sub hmp_t).norm).integrable_sq
    rw [ofReal_integral_eq_lintegral_ofReal hint_sq
      (ae_of_all _ fun _ => sq_nonneg _), ← nsrc_eLpNorm_two_sq,
      ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num

private theorem nsrc_unproj_solve {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) (μ : ℂ)
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hF : NiceForce c F) :
    ∃ (aF : ℝ) (u_raw : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (ω_raw : ℝ × (ℝ × ℝ) → ℂ),
      0 < aF ∧
      NiceSlices c u_raw ∧
      IsClassicalFlatSol ν μ F u_raw ∧
      (∀ s ≤ aF, ∀ x i, u_raw (s, x) i = 0) ∧
      (∀ p, ω_raw p =
        pdC 0 (fun y => u_raw (p.1, y) 1) p.2 - pdC 1 (fun y => u_raw (p.1, y) 0) p.2) ∧
      ContDiff ℝ ∞ ω_raw ∧
      (∀ s x, ω_raw (s, (x.1 + c, x.2)) = ω_raw (s, x)) ∧
      ScalarGaussDecayLoc ω_raw ∧
      (∀ s ≤ aF, ∀ x, ω_raw (s, x) = 0 ∧ ∀ j, pdC j (fun y => ω_raw (s, y)) x = 0) ∧
      (∀ s j, HasWeakCellDerivC c j (fun x => ω_raw (s, x))
        (fun x => pdC j (fun y => ω_raw (s, y)) x)) := by
  set h_src : Fin 2 → ℝ × (ℝ × ℝ) → ℂ := fun i p =>
    (p.1 : ℂ) ^ μ * ∑ j : Fin 2, pdC j (fun y => F (p.1, y) i j) p.2
  have hh_nice : ∀ i : Fin 2, NiceScalar c (h_src i) := fun i => divSourceNice c μ F hF i
  obtain ⟨_, _, _, aF, _BF, _RF, haF, hF_zero⟩ := id hF
  have hh_zero : ∀ i : Fin 2, ∀ s < aF, ∀ x, h_src i (s, x) = 0 := by
    intro i s hs x
    have hF_sl : ∀ j : Fin 2, (fun y => F (s, y) i j) = fun _ => 0 :=
      fun j => funext fun y => hF_zero s y i j (Or.inl hs)
    dsimp [h_src]
    simp [hF_sl, pdC]
  set w_raw : Fin 2 → ℝ × (ℝ × ℝ) → ℂ := fun i p => duhamelHeat ν (h_src i) p.1 p.2
  have hw_sm : ∀ i, ContDiff ℝ ∞ (w_raw i) :=
    fun i => duhamelSmooth c ν (h_src i) hc hν (hh_nice i)
  have hw_per : ∀ i s x, w_raw i (s, (x.1 + c, x.2)) = w_raw i (s, x) :=
    fun i => (duhamelPeriodicZero c ν (h_src i) hc hν (hh_nice i)).1
  have hw_zero : ∀ i s x, s ≤ aF → w_raw i (s, x) = 0 :=
    fun i s x hs => nsrc_duhamel_zero_le ν (h_src i) (hh_zero i) s hs x
  have hw_eq : ∀ i, IsScalarHeatSol ν (w_raw i) (h_src i) :=
    fun i => duhamelHeatEq c ν (h_src i) hc hν (hh_nice i)
  have hw_dec : ∀ i, ScalarGaussDecayLoc (w_raw i) :=
    fun i => duhamelDecay c ν (h_src i) hc hν (hh_nice i)
  have hcp : ∀ i : Fin 2,
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ((p.1 : ℂ) ^ (-μ)) * w_raw i p) ∧
      (∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
        deriv (fun s' : ℝ => ((s' : ℂ) ^ (-μ)) * w_raw i (s', x)) s +
            (μ / (s : ℂ)) * (((s : ℂ) ^ (-μ)) * w_raw i (s, x)) -
          (ν : ℂ) * lapC (fun y => ((s : ℂ) ^ (-μ)) * w_raw i (s, y)) x =
        ((s : ℂ) ^ (-μ)) * h_src i (s, x)) ∧
      ScalarGaussDecayLoc (fun p : ℝ × (ℝ × ℝ) => ((p.1 : ℂ) ^ (-μ)) * w_raw i p) :=
    fun i => cpowScale c ν μ aF (h_src i) (w_raw i) haF (hw_sm i) (hw_per i)
      (hw_zero i) (hw_eq i) (hw_dec i)
  set u_raw : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => ((p.1 : ℂ) ^ (-μ)) * w_raw i p
  have hu_sm : ∀ i, ContDiff ℝ ∞ (fun p => u_raw p i) := fun i => (hcp i).1
  have hu_per : ∀ s x i, u_raw (s, (x.1 + c, x.2)) i = u_raw (s, x) i := by
    intro s x i; dsimp [u_raw]; rw [hw_per i s x]
  have hu_zero : ∀ s ≤ aF, ∀ x i, u_raw (s, x) i = 0 := by
    intro s hs x i; dsimp [u_raw]; rw [hw_zero i s x hs, mul_zero]
  have hu_sol : IsClassicalFlatSol ν μ F u_raw := by
    intro s hs x i
    have hmain := (hcp i).2.1 s hs x
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    have hne : (s : ℂ) ^ μ ≠ 0 := fun h => hs0 ((Complex.cpow_eq_zero_iff _ _).1 h).1
    dsimp [u_raw]
    rw [hmain]
    dsimp [h_src]
    rw [Complex.cpow_neg, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hu_dec : GaussianDecayLoc u_raw := by
    intro s₂
    obtain ⟨C0, κ0, hκ0, h0⟩ := (hcp 0).2.2 s₂
    obtain ⟨C1, κ1, hκ1, h1'⟩ := (hcp 1).2.2 s₂
    refine ⟨|C0| + |C1|, min κ0 κ1, lt_min hκ0 hκ1, fun s x i hs => ?_⟩
    have ht : 0 ≤ x.2 ^ 2 := sq_nonneg _
    fin_cases i
    · exact heatCC_decay_mono (min_le_left _ _) (by linarith [abs_nonneg C1]) ht (h0 s x hs)
    · exact heatCC_decay_mono (min_le_right _ _) (by linarith [abs_nonneg C0]) ht (h1' s x hs)
  -- Spatial partials `pdC k (u_raw · i)` via `duhDecFderivComm` + `duhDecDirNice` + `cpowScale`
  have hdu_props : ∀ (i k : Fin 2),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => pdC k (fun y => u_raw (p.1, y) i) p.2) ∧
      (∀ s x, pdC k (fun y => u_raw (s, y) i) (x.1 + c, x.2) =
        pdC k (fun y => u_raw (s, y) i) x) ∧
      ScalarGaussDecayLoc (fun p : ℝ × (ℝ × ℝ) => pdC k (fun y => u_raw (p.1, y) i) p.2) := by
    intro i k
    set hk := duhDecDirDeriv (B0579.dir k) (h_src i)
    have hhk_nice : NiceScalar c hk := duhDecDirNice c (B0579.dir k) (h_src i) (hh_nice i)
    have hhk_zero : ∀ s < aF, ∀ x, hk (s, x) = 0 := by
      intro s hs x
      have hsl : (fun y => h_src i (s, y)) = fun _ => 0 := funext (hh_zero i s hs)
      simp [hk, duhDecDirDeriv, hsl]
    set wk : ℝ × (ℝ × ℝ) → ℂ := fun p => duhamelHeat ν hk p.1 p.2
    have hcp_k := cpowScale c ν μ aF hk wk haF
      (duhamelSmooth c ν hk hc hν hhk_nice)
      (duhamelPeriodicZero c ν hk hc hν hhk_nice).1
      (fun s x hs => nsrc_duhamel_zero_le ν hk hhk_zero s hs x)
      (duhamelHeatEq c ν hk hc hν hhk_nice)
      (duhamelDecay c ν hk hc hν hhk_nice)
    have heq_du_pt : ∀ s z, pdC k (fun y => u_raw (s, y) i) z =
        ((s : ℂ) ^ (-μ)) * wk (s, z) := by
      intro s z
      dsimp [u_raw, wk, hk]
      rw [cpS_pdC_const_mul]
      congr 1
      exact duhDecFderivComm c ν (h_src i) hc hν (hh_nice i) s z (B0579.dir k)
    have heq_du : (fun p : ℝ × (ℝ × ℝ) => pdC k (fun y => u_raw (p.1, y) i) p.2) =
        fun p => ((p.1 : ℂ) ^ (-μ)) * wk p := funext fun p => heq_du_pt p.1 p.2
    rw [heq_du]
    refine ⟨hcp_k.1, fun s x => ?_, hcp_k.2.2⟩
    rw [heq_du_pt s (x.1 + c, x.2), heq_du_pt s x]
    dsimp [wk]
    rw [(duhamelPeriodicZero c ν hk hc hν hhk_nice).1 s x]
  set ω_raw : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    pdC 0 (fun y => u_raw (p.1, y) 1) p.2 - pdC 1 (fun y => u_raw (p.1, y) 0) p.2
  have hω_sm : ContDiff ℝ ∞ ω_raw := (hdu_props 1 0).1.sub (hdu_props 0 1).1
  have hω_per : ∀ s x, ω_raw (s, (x.1 + c, x.2)) = ω_raw (s, x) := by
    intro s x
    dsimp [ω_raw]
    rw [(hdu_props 1 0).2.1 s x, (hdu_props 0 1).2.1 s x]
  have hω_dec : ScalarGaussDecayLoc ω_raw := by
    intro s₂
    obtain ⟨C0, κ0, hκ0, h0⟩ := (hdu_props 1 0).2.2 s₂
    obtain ⟨C1, κ1, hκ1, h1'⟩ := (hdu_props 0 1).2.2 s₂
    refine ⟨|C0| + |C1|, min κ0 κ1, lt_min hκ0 hκ1, fun s x hs => ?_⟩
    have b0 : ‖pdC 0 (fun z => u_raw (s, z) 1) x‖ +
        ‖fderiv ℝ (fun y => pdC 0 (fun z => u_raw (s, z) 1) y) x‖ ≤
        |C0| * Real.exp (-min κ0 κ1 * x.2 ^ 2) := by
      calc ‖pdC 0 (fun z => u_raw (s, z) 1) x‖ +
            ‖fderiv ℝ (fun y => pdC 0 (fun z => u_raw (s, z) 1) y) x‖
          ≤ C0 * Real.exp (-κ0 * x.2 ^ 2) := h0 s x hs
        _ ≤ |C0| * Real.exp (-κ0 * x.2 ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.exp_nonneg _)
        _ ≤ |C0| * Real.exp (-min κ0 κ1 * x.2 ^ 2) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg C0)
            nlinarith [min_le_left κ0 κ1, sq_nonneg x.2]
    have b1 : ‖pdC 1 (fun z => u_raw (s, z) 0) x‖ +
        ‖fderiv ℝ (fun y => pdC 1 (fun z => u_raw (s, z) 0) y) x‖ ≤
        |C1| * Real.exp (-min κ0 κ1 * x.2 ^ 2) := by
      calc ‖pdC 1 (fun z => u_raw (s, z) 0) x‖ +
            ‖fderiv ℝ (fun y => pdC 1 (fun z => u_raw (s, z) 0) y) x‖
          ≤ C1 * Real.exp (-κ1 * x.2 ^ 2) := h1' s x hs
        _ ≤ |C1| * Real.exp (-κ1 * x.2 ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C1) (Real.exp_nonneg _)
        _ ≤ |C1| * Real.exp (-min κ0 κ1 * x.2 ^ 2) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg C1)
            nlinarith [min_le_right κ0 κ1, sq_nonneg x.2]
    have hdf0 : DifferentiableAt ℝ (fun y => pdC 0 (fun z => u_raw (s, z) 1) y) x :=
      (((hdu_props 1 0).1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) x
    have hdf1 : DifferentiableAt ℝ (fun y => pdC 1 (fun z => u_raw (s, z) 0) y) x :=
      (((hdu_props 0 1).1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) x
    have hfderiv : fderiv ℝ (fun y => ω_raw (s, y)) x =
        fderiv ℝ (fun y => pdC 0 (fun z => u_raw (s, z) 1) y) x -
          fderiv ℝ (fun y => pdC 1 (fun z => u_raw (s, z) 0) y) x :=
      fderiv_sub hdf0 hdf1
    calc ‖ω_raw (s, x)‖ + ‖fderiv ℝ (fun y => ω_raw (s, y)) x‖
        ≤ (‖pdC 0 (fun z => u_raw (s, z) 1) x‖ + ‖pdC 1 (fun z => u_raw (s, z) 0) x‖) +
            (‖fderiv ℝ (fun y => pdC 0 (fun z => u_raw (s, z) 1) y) x‖ +
              ‖fderiv ℝ (fun y => pdC 1 (fun z => u_raw (s, z) 0) y) x‖) := by
          rw [hfderiv]
          exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ = (‖pdC 0 (fun z => u_raw (s, z) 1) x‖ +
            ‖fderiv ℝ (fun y => pdC 0 (fun z => u_raw (s, z) 1) y) x‖) +
          (‖pdC 1 (fun z => u_raw (s, z) 0) x‖ +
            ‖fderiv ℝ (fun y => pdC 1 (fun z => u_raw (s, z) 0) y) x‖) := by ring
      _ ≤ |C0| * Real.exp (-min κ0 κ1 * x.2 ^ 2) + |C1| * Real.exp (-min κ0 κ1 * x.2 ^ 2) :=
          add_le_add b0 b1
      _ = (|C0| + |C1|) * Real.exp (-min κ0 κ1 * x.2 ^ 2) := by ring
  have hω_zero : ∀ s ≤ aF, ∀ x, ω_raw (s, x) = 0 ∧ ∀ j, pdC j (fun y => ω_raw (s, y)) x = 0 := by
    have hω_val0 : ∀ s ≤ aF, ∀ x, ω_raw (s, x) = 0 := by
      intro s hs x
      have hu1 : (fun y => u_raw (s, y) 1) = fun _ => 0 := funext fun y => hu_zero s hs y 1
      have hu0 : (fun y => u_raw (s, y) 0) = fun _ => 0 := funext fun y => hu_zero s hs y 0
      dsimp [ω_raw]
      simp [hu1, hu0, pdC]
    intro s hs x
    refine ⟨hω_val0 s hs x, fun j => ?_⟩
    have hsl : (fun y => ω_raw (s, y)) = fun _ => 0 := funext (hω_val0 s hs)
    simp [hsl, pdC]
  have hN_ω : NiceSlices c (fun p (_ : Fin 2) => ω_raw p) :=
    ⟨fun _ => hω_sm, fun s x _ => hω_per s x, fun s₂ => by
      obtain ⟨C, κ, hκ, hb⟩ := hω_dec s₂
      exact ⟨C, κ, hκ, fun s x _ hs => hb s x hs⟩⟩
  refine ⟨aF, u_raw, ω_raw, haF, ⟨hu_sm, hu_per, hu_dec⟩, hu_sol, hu_zero,
    fun _ => rfl, hω_sm, hω_per, hω_dec, hω_zero,
    fun s j => smoothSliceWeak c hc (fun p _ => ω_raw p) hN_ω s 0 j⟩

private theorem nsrc_P0C_zero_ae {c : ℝ} :
    ∀ i : Fin 2, (fun x => P0C c (fun _ _ => 0) x i) =ᵐ[volume.restrict (B0579.cell c)] 0 := by
  have h0_vec : UnforcedLeray.Cyl.vec (0 : ℝ) 0 = 0 := by
    ext j; fin_cases j <;> simp
  have hre : reVec (fun (_ : ℝ × ℝ) (_ : Fin 2) => (0 : ℂ)) = 0 := by
    funext x; simp [reVec, h0_vec]
  have him : imVec (fun (_ : ℝ × ℝ) (_ : Fin 2) => (0 : ℂ)) = 0 := by
    funext x; simp [imVec, h0_vec]
  have hto : toL2v c 0 = 0 := by
    unfold toL2v
    simp [MemLp.zero]
  have hP0re : P0re c (fun _ _ => 0) = 0 := by simp [P0re, hre, hto]
  have hP0im : P0im c (fun _ _ => 0) = 0 := by simp [P0im, him, hto]
  have hae0 : ⇑(0 : UnforcedLeray.Cyl.L2v c) =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    rw [← cellμ_eq c]
    exact Lp.coeFn_zero _ 2 _
  intro i
  filter_upwards [hae0] with x hx
  have hx0 : (0 : UnforcedLeray.Cyl.L2v c) x i = 0 := by
    have := congrArg (fun v : UnforcedLeray.Cyl.Vec2 => v i) hx
    simpa using this
  show (((P0re c (fun _ _ => 0) x i : ℝ) : ℂ) +
    Complex.I * ((P0im c (fun _ _ => 0) x i : ℝ) : ℂ)) = 0
  rw [hP0re, hP0im, hx0]
  simp

private theorem nsrc_L2v_coord_memLp_and_le {c : ℝ} (L : UnforcedLeray.Cyl.L2v c) (i : Fin 2) :
    MemLp (fun x => (L x i : ℂ)) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => (L x i : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal ‖L‖ := by
  have hL : MemLp L 2 (volume.restrict (B0579.cell c)) := by
    rw [← cellμ_eq c]; exact Lp.memLp L
  have hproj : Continuous (fun v : UnforcedLeray.Cyl.Vec2 => (v i : ℂ)) :=
    Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  have hm : AEStronglyMeasurable (fun x => (L x i : ℂ)) (volume.restrict (B0579.cell c)) :=
    hproj.comp_aestronglyMeasurable hL.1
  have hpt : ∀ x, ‖(L x i : ℂ)‖ ≤ ‖L x‖ := fun x => by
    rw [Complex.norm_real, EuclideanSpace.norm_eq]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun j : Fin 2 => ‖L x j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hle : eLpNorm (fun x => (L x i : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm L 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_mono hpt
  have hnorm_eq : eLpNorm L 2 (volume.restrict (B0579.cell c)) = ENNReal.ofReal ‖L‖ := by
    rw [← cellμ_eq c, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top L)]
  exact ⟨⟨hm, hle.trans_lt hL.2⟩, hle.trans_eq hnorm_eq⟩

private theorem nsrc_leray_solve {c ν : ℝ} (hc : 0 < c) (_hν : 0 < ν) (μ : ℂ)
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hF : NiceForce c F)
    {aF : ℝ} (haF : 0 < aF)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {ω_raw : ℝ × (ℝ × ℝ) → ℂ}
    (hN : NiceSlices c u) (hu_sol : IsClassicalFlatSol ν μ F u)
    (hu_zero : ∀ s ≤ aF, ∀ x i, u (s, x) i = 0)
    (hω_def : ∀ p, ω_raw p =
      pdC 0 (fun y => u (p.1, y) 1) p.2 - pdC 1 (fun y => u (p.1, y) 0) p.2) :
    ∃ (b_cl : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G_cl : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
      IsLerayProjection c u b_cl G_cl ∧
      IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b_cl G_cl ∧
      (∀ s ≤ aF, (∀ x i, b_cl (s, x) i = 0) ∧ (∀ x i j, G_cl (s, x) i j = 0)) ∧
      (∀ t > 0, (∀ i, MemLp (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell c))) ∧
        (∀ i j, MemLp (fun x => G_cl (t, x) i j) 2 (volume.restrict (B0579.cell c)))) ∧
      (∀ t > 0, (fun x => G_cl (t, x) 1 0 - G_cl (t, x) 0 1)
        =ᵐ[volume.restrict (B0579.cell c)] fun x => ω_raw (t, x)) ∧
      (∀ H : ℝ, ∃ M_b : ℝ, 0 ≤ M_b ∧ ∀ t ∈ Ioc (0 : ℝ) H, ∀ i : Fin 2,
        eLpNorm (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell c)) ≤
          ENNReal.ofReal M_b) ∧
      (∀ t > 0, ∀ i : Fin 2,
        Tendsto (fun s => eLpNorm (fun x => b_cl (s, x) i - b_cl (t, x) i) 2
          (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0)) := by
  classical
  obtain ⟨hc1, hc2, hc3⟩ := lerayClassCont c hc u hN
  obtain ⟨Fb, hFbm, hFb⟩ := jointRepVecC c hc _ _ hc1 hc2
  have hG : ∀ j : Fin 2, ∃ Fj : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => Fj p i) ∧
      ∀ t : ℝ, 0 < t → ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        ∀ i, Fj (t, x) i = P0C c (duSl u t j) x i := fun j =>
    jointRepVecC c hc _ _ (hc3 j).1 (hc3 j).2
  choose Fg hFgm hFg using hG
  set Z : Set ℝ := {s : ℝ | ∀ x i, u (s, x) i = 0}
  have hZ : MeasurableSet Z := (isClosed_zeroAges (fun i => (hN.smooth i).continuous)).measurableSet
  set b_cl : ℝ × (ℝ × ℝ) → Fin 2 → ℂ := fun p i => if p.1 ∈ Z then 0 else Fb p i
  set G_cl : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ := fun p i j => if p.1 ∈ Z then 0 else Fg j p i
  have hbZ : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Z → ∀ i, b_cl p i = 0 := fun p hp i => by simp [b_cl, hp]
  have hbN : ∀ p : ℝ × (ℝ × ℝ), p.1 ∉ Z → ∀ i, b_cl p i = Fb p i := fun p hp i => by simp [b_cl, hp]
  have hGZ : ∀ p : ℝ × (ℝ × ℝ), p.1 ∈ Z → ∀ i j, G_cl p i j = 0 := fun p hp i j => by simp [G_cl, hp]
  have hGN : ∀ p : ℝ × (ℝ × ℝ), p.1 ∉ Z → ∀ i j, G_cl p i j = Fg j p i := fun p hp i j => by simp [G_cl, hp]
  have hbm : ∀ i, Measurable fun p => b_cl p i :=
    fun i => Measurable.ite (measurable_fst hZ) measurable_const (hFbm i)
  have hGm : ∀ i j, Measurable fun p => G_cl p i j :=
    fun i j => Measurable.ite (measurable_fst hZ) measurable_const (hFgm j i)
  have hL : IsLerayProjection c u b_cl G_cl := by
    refine
      { measurable := hbm
        gradMeasurable := hGm
        energyLoc := ?_
        divFree := ?_
        weakGrad := ?_
        orth := ?_
        zero := fun s hs x i => hbZ (s, x) hs i }
    · intro s₁ s₂ hs₁ hs₁₂
      obtain ⟨M, hMb⟩ := lerayClassEnergy c hc u hN s₂
      have hmeas : Measurable fun p : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) := by
        refine ENNReal.measurable_ofReal.comp
          (Measurable.add (Measurable.pow_const ?_ 2) (Measurable.pow_const ?_ 2))
        · unfold vnorm2
          exact Real.continuous_sqrt.measurable.comp
            (Finset.measurable_sum _ fun i _ => (hbm i).norm.pow_const 2)
        · unfold tnorm2
          exact Real.continuous_sqrt.measurable.comp
            (Finset.measurable_sum _ fun i _ =>
              Finset.measurable_sum _ fun j _ => (hGm i j).norm.pow_const 2)
      have hprod : ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
            ENNReal.ofReal (vnorm2 (b_cl p) ^ 2 + tnorm2 (G_cl p) ^ 2) =
          ∫⁻ s in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
            ENNReal.ofReal (vnorm2 (b_cl (s, x)) ^ 2 + tnorm2 (G_cl (s, x)) ^ 2) := by
        rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), ← Measure.prod_restrict,
          lintegral_prod _ hmeas.aemeasurable]
      rw [hprod]
      calc ∫⁻ s in Icc s₁ s₂, ∫⁻ x in B0579.cell c,
            ENNReal.ofReal (vnorm2 (b_cl (s, x)) ^ 2 + tnorm2 (G_cl (s, x)) ^ 2)
          ≤ ∫⁻ s in Icc s₁ s₂, ENNReal.ofReal M := by
            refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
            have hs0 : 0 < s := lt_of_lt_of_le hs₁ hs.1
            by_cases hsZ : s ∈ Z
            · have h0 : ∀ x : ℝ × ℝ, ENNReal.ofReal
                  (vnorm2 (b_cl (s, x)) ^ 2 + tnorm2 (G_cl (s, x)) ^ 2) = 0 := by
                intro x
                have hb0 : b_cl (s, x) = fun _ => 0 := funext fun i => hbZ (s, x) hsZ i
                have hG0 : G_cl (s, x) = fun _ _ => 0 :=
                  funext fun i => funext fun j => hGZ (s, x) hsZ i j
                rw [hb0, hG0]; simp [vnorm2, tnorm2]
              simp [h0]
            · have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
                  ENNReal.ofReal (vnorm2 (b_cl (s, x)) ^ 2 + tnorm2 (G_cl (s, x)) ^ 2) =
                    ENNReal.ofReal (vnorm2 (P0C c (uSl u s) x) ^ 2 +
                      tnorm2 (fun i j => P0C c (duSl u s j) x i) ^ 2) := by
                filter_upwards [hFb s hs0, hFg 0 s hs0, hFg 1 s hs0] with x h1 h2 h3
                have hb : b_cl (s, x) = P0C c (uSl u s) x :=
                  funext fun i => (hbN (s, x) hsZ i).trans (h1 i)
                have hG' : G_cl (s, x) = fun i j => P0C c (duSl u s j) x i := by
                  funext i j; rw [hGN (s, x) hsZ i j]; fin_cases j
                  · exact h2 i
                  · exact h3 i
                rw [hb, hG']
              rw [lintegral_congr_ae hae]
              exact hMb s hs0 hs.2
        _ = ENNReal.ofReal M * volume (Icc s₁ s₂) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    · intro s hs ψ hψ
      by_cases hsZ : s ∈ Z
      · have hb0 : ∀ x i, b_cl (s, x) i = 0 := fun x i => hbZ (s, x) hsZ i
        simp [hb0]
      · refine (integral_congr_ae ?_).trans (p0DivFreeC c hc (uSl u s) ψ hψ)
        filter_upwards [hFb s hs] with x hx
        rw [hbN (s, x) hsZ 0, hbN (s, x) hsZ 1, hx 0, hx 1]
        rfl
    · intro s hs i j
      by_cases hsZ : s ∈ Z
      · have hb0 : (fun x => b_cl (s, x) i) = fun _ => 0 := funext fun x => hbZ (s, x) hsZ i
        have hG0 : (fun x => G_cl (s, x) i j) = fun _ => 0 := funext fun x => hGZ (s, x) hsZ i j
        rw [hb0, hG0]; exact HasWeakCellDerivC.zero c j
      · have hmem := gaussianSliceMemLp c hc u hN s
        have hweak := p0CommWeakC c hc (uSl u s) (fun j => duSl u s j) hmem.1 hmem.2.1
          (fun j => (hmem.2.2 j).1) (fun j => (hmem.2.2 j).2)
          (fun i j => smoothSliceWeak c hc u hN s i j) i j
        refine HasWeakCellDerivC.congr_ae ?_ ?_ hweak
        · filter_upwards [hFb s hs] with x hx; rw [hbN (s, x) hsZ i, hx i]; rfl
        · filter_upwards [hFg j s hs] with x hx; rw [hGN (s, x) hsZ i j, hx i]
    · intro s hs Ψ hΨ
      by_cases hsZ : s ∈ Z
      · have h0 : ∀ x : ℝ × ℝ, ∑ i : Fin 2, (b_cl (s, x) i - u (s, x) i) * (Ψ x i : ℂ) = 0 :=
          fun x => by simp [hbZ (s, x) hsZ, hsZ x]
        simp [h0]
      · have hmem := gaussianSliceMemLp c hc u hN s
        refine (integral_congr_ae ?_).trans (p0OrthC c hc (uSl u s) hmem.1 hmem.2.1 Ψ hΨ)
        filter_upwards [hFb s hs] with x hx
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hbN (s, x) hsZ i, hx i]
        rfl
  -- Causal solution clauses (as in `niceForceSolution_of`)
  have hsol : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b_cl G_cl := by
    have hucont : ∀ i, Continuous fun p : ℝ × (ℝ × ℝ) => u p i := fun i => (hN.smooth i).continuous
    refine
      { measurable := hL.measurable
        gradMeasurable := hL.gradMeasurable
        energyLoc := hL.energyLoc
        zeroEntrance := ?_
        divFree := hL.divFree
        weakGrad := hL.weakGrad
        integrable := fun Φ hΦ => by
          have hw := classicalToWeakFlat c ν μ hc F hF u hN.smooth hN.periodic hu_sol Φ hΦ
          exact (flatOrthSwap c ν μ hc F u b_cl G_cl hucont hL Φ hΦ hw.1 hw.2).1
        weak := fun Φ hΦ => by
          have hw := classicalToWeakFlat c ν μ hc F hF u hN.smooth hN.periodic hu_sol Φ hΦ
          exact (flatOrthSwap c ν μ hc F u b_cl G_cl hucont hL Φ hΦ hw.1 hw.2).2 }
    refine ⟨aF, haF, ?_⟩
    have hmeas : MeasurableSet (Ioo (0 : ℝ) aF ×ˢ (univ : Set (ℝ × ℝ))) :=
      measurableSet_Ioo.prod MeasurableSet.univ
    have hz : ∀ p ∈ Ioo (0 : ℝ) aF ×ˢ (univ : Set (ℝ × ℝ)),
        ENNReal.ofReal (vnorm2 (b_cl p) ^ 2) = 0 := by
      intro p hp
      have hpZ : p.1 ∈ Z := fun x i => hu_zero p.1 (le_of_lt hp.1.2) x i
      have hb0 : ∀ i, b_cl p i = 0 := hbZ p hpZ
      simp [vnorm2, hb0]
    rw [setLIntegral_congr_fun hmeas (g := fun _ => 0) hz]; simp
  -- A.e. identification `b_cl (t, ·) i =ᵐ P0C c (uSl u t) · i` and `G_cl =ᵐ P0C c (duSl u t j)` for ALL `t > 0`
  have hb_ae_all : ∀ t > 0, ∀ i,
      (fun x => b_cl (t, x) i) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => P0C c (uSl u t) x i := by
    intro t ht i
    by_cases htZ : t ∈ Z
    · have husl0 : uSl u t = fun _ _ => 0 := funext fun x => funext fun k => htZ x k
      rw [husl0]
      filter_upwards [nsrc_P0C_zero_ae (c := c) i] with x hx
      rw [hbZ (t, x) htZ i]; exact hx.symm
    · filter_upwards [hFb t ht] with x hx
      rw [hbN (t, x) htZ i, hx i]
      rfl
  have hG_ae_all : ∀ t > 0, ∀ i j,
      (fun x => G_cl (t, x) i j) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => P0C c (duSl u t j) x i := by
    intro t ht i j
    by_cases htZ : t ∈ Z
    · have hdusl0 : duSl u t j = fun _ _ => 0 := by
        funext x k
        have hsl : (fun y => u (t, y) k) = fun _ => 0 := funext fun y => htZ y k
        simp [duSl, hsl, pdC]
      rw [hdusl0]
      filter_upwards [nsrc_P0C_zero_ae (c := c) i] with x hx
      rw [hGZ (t, x) htZ i j]; exact hx.symm
    · filter_upwards [hFg j t ht] with x hx
      rw [hGN (t, x) htZ i j, hx i]
  -- `MemLp` of `P0C c f · i`
  have hP0C_memLp : ∀ (f : ℝ × ℝ → Fin 2 → ℂ) (i : Fin 2),
      MemLp (fun x => P0C c f x i) 2 (volume.restrict (B0579.cell c)) := by
    intro f i
    have h1 := (nsrc_L2v_coord_memLp_and_le (P0re c f) i).1
    have h2 := (nsrc_L2v_coord_memLp_and_le (P0im c f) i).1
    exact h1.add (h2.const_mul Complex.I)
  have hmem_slices : ∀ t > 0,
      (∀ i, MemLp (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell c))) ∧
      (∀ i j, MemLp (fun x => G_cl (t, x) i j) 2 (volume.restrict (B0579.cell c))) := by
    intro t ht
    exact ⟨fun i => (hP0C_memLp (uSl u t) i).ae_eq (hb_ae_all t ht i).symm,
      fun i j => (hP0C_memLp (duSl u t j) i).ae_eq (hG_ae_all t ht i j).symm⟩
  -- Curl identification `G_cl 1 0 - G_cl 0 1 =ᵐ ω_raw`
  have hcurl_ae : ∀ t > 0,
      (fun x => G_cl (t, x) 1 0 - G_cl (t, x) 0 1)
        =ᵐ[volume.restrict (B0579.cell c)] fun x => ω_raw (t, x) := by
    intro t ht
    set d : ℝ × ℝ → ℂ := fun x => (G_cl (t, x) 1 0 - G_cl (t, x) 0 1) - ω_raw (t, x)
    suffices hd0 : d =ᵐ[volume.restrict (B0579.cell c)] 0 by
      filter_upwards [hd0] with x hx
      exact sub_eq_zero.1 hx
    refine nsrc_ae_zero_of_cylTest (fun ψ hψ => ?_) (fun ψ hψ => ?_)
    · have IG10 := ((hL.weakGrad t ht 1 0).1 ψ hψ).2
      have IG01 := ((hL.weakGrad t ht 0 1).1 ψ hψ).2
      have Iu10 := ((smoothSliceWeak c hc u hN t 1 0).1 ψ hψ).2
      have Iu01 := ((smoothSliceWeak c hc u hN t 0 1).1 ψ hψ).2
      have heq : (fun x => d x * (ψ x : ℂ)) =
          fun x => (G_cl (t, x) 1 0 * (ψ x : ℂ) - G_cl (t, x) 0 1 * (ψ x : ℂ)) -
            (pdC 0 (fun y => u (t, y) 1) x * (ψ x : ℂ) -
              pdC 1 (fun y => u (t, y) 0) x * (ψ x : ℂ)) := by
        funext x; dsimp [d]; rw [hω_def (t, x)]; ring
      rw [heq]
      exact (IG10.sub IG01).sub (Iu10.sub Iu01)
    · have hΨ : IsDivFreeTestField c (V1.perpF ψ) :=
        ⟨fun i => V1.perpF_cylTest hψ i, (V1.perpF_isFlatSpatialTest hψ).divFree⟩
      have horth := hL.orth t ht (V1.perpF ψ) hΨ
      have wG10 := hL.weakGrad t ht 1 0
      have wG01 := hL.weakGrad t ht 0 1
      have wu10 := smoothSliceWeak c hc u hN t 1 0
      have wu01 := smoothSliceWeak c hc u hN t 0 1
      obtain ⟨Ib1_pd0, IG10⟩ := wG10.1 ψ hψ
      obtain ⟨Ib0_pd1, IG01⟩ := wG01.1 ψ hψ
      obtain ⟨Iu1_pd0, Idu10⟩ := wu10.1 ψ hψ
      obtain ⟨Iu0_pd1, Idu01⟩ := wu01.1 ψ hψ
      have horth' : (∫ x in B0579.cell c, b_cl (t, x) 0 * (B0579.pd 1 ψ x : ℂ)) -
          (∫ x in B0579.cell c, u (t, x) 0 * (B0579.pd 1 ψ x : ℂ)) -
          ((∫ x in B0579.cell c, b_cl (t, x) 1 * (B0579.pd 0 ψ x : ℂ)) -
            (∫ x in B0579.cell c, u (t, x) 1 * (B0579.pd 0 ψ x : ℂ))) = 0 := by
        have h1 := integral_sub Ib0_pd1 Iu0_pd1
        have h2 := integral_sub Ib1_pd0 Iu1_pd0
        have h3 := integral_sub (Ib0_pd1.sub Iu0_pd1) (Ib1_pd0.sub Iu1_pd0)
        dsimp only [Pi.sub_apply] at h1 h2 h3
        rw [← h1, ← h2, ← h3, ← horth]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        simp only [Fin.sum_univ_two, V1.perpF_zero, V1.perpF_one]
        push_cast; ring
      rw [wG01.2 ψ hψ, wu01.2 ψ hψ, wG10.2 ψ hψ, wu10.2 ψ hψ] at horth'
      have heq : (fun x => d x * (ψ x : ℂ)) =
          fun x => (G_cl (t, x) 1 0 * (ψ x : ℂ) - G_cl (t, x) 0 1 * (ψ x : ℂ)) -
            (pdC 0 (fun y => u (t, y) 1) x * (ψ x : ℂ) -
              pdC 1 (fun y => u (t, y) 0) x * (ψ x : ℂ)) := by
        funext x; dsimp [d]; rw [hω_def (t, x)]; ring
      have hs1 := integral_sub (IG10.sub IG01) (Idu10.sub Idu01)
      have hs2 := integral_sub IG10 IG01
      have hs3 := integral_sub Idu10 Idu01
      dsimp only [Pi.sub_apply] at hs1 hs2 hs3 horth'
      rw [heq, hs1, hs2, hs3]
      linear_combination horth'
  -- Uniform `L²` bound on `b_cl (t, ·) i` for `t ∈ Ioc 0 H`
  have hb_unif : ∀ H : ℝ, ∃ M_b : ℝ, 0 ≤ M_b ∧ ∀ t ∈ Ioc (0 : ℝ) H, ∀ i : Fin 2,
      eLpNorm (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal M_b := by
    intro H
    obtain ⟨M_E, hME⟩ := lerayClassEnergy c hc u hN H
    refine ⟨Real.sqrt (max M_E 0), Real.sqrt_nonneg _, fun t ht i => ?_⟩
    rw [eLpNorm_congr_ae (hb_ae_all t ht.1 i)]
    have hsq : eLpNorm (fun x => P0C c (uSl u t) x i) 2 (volume.restrict (B0579.cell c)) ^ 2 ≤
        ENNReal.ofReal (max M_E 0) := by
      rw [nsrc_eLpNorm_two_sq]
      refine (lintegral_mono fun x => ?_).trans ((hME t ht.1 ht.2).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ‖P0C c (uSl u t) x i‖ ^ 2 ≤ vnorm2 (P0C c (uSl u t) x) ^ 2 := by
        rw [causalLin_vnorm2_sq]
        exact Finset.single_le_sum (f := fun k => ‖P0C c (uSl u t) x k‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      linarith [sq_nonneg (tnorm2 (fun i' j' => P0C c (duSl u t j') x i'))]
    have hpow := ENNReal.rpow_le_rpow hsq (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul,
      show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by norm_num),
      ← Real.sqrt_eq_rpow] at hpow
    exact hpow
  -- `L²` continuity of `s ↦ b_cl (s, ·) i` on `Ioi 0`
  have hb_cont : ∀ t > 0, ∀ i : Fin 2,
      Tendsto (fun s => eLpNorm (fun x => b_cl (s, x) i - b_cl (t, x) i) 2
        (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0) := by
    intro t ht i
    have hlim_re : Tendsto (fun s => ENNReal.ofReal ‖P0re c (uSl u s) - P0re c (uSl u t)‖)
        (𝓝 t) (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := by simp
      rw [h0]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.1 (hc1.continuousAt (Ioi_mem_nhds ht)))
    have hlim_im : Tendsto (fun s => ENNReal.ofReal ‖P0im c (uSl u s) - P0im c (uSl u t)‖)
        (𝓝 t) (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := by simp
      rw [h0]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.1 (hc2.continuousAt (Ioi_mem_nhds ht)))
    have hsum : Tendsto (fun s =>
        ENNReal.ofReal ‖P0re c (uSl u s) - P0re c (uSl u t)‖ +
          ENNReal.ofReal ‖P0im c (uSl u s) - P0im c (uSl u t)‖) (𝓝 t) (𝓝 0) := by
      simpa using hlim_re.add hlim_im
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hae_sub : (fun x => b_cl (s, x) i - b_cl (t, x) i)
        =ᵐ[volume.restrict (B0579.cell c)]
        fun x => (((P0re c (uSl u s) - P0re c (uSl u t)) x i : ℝ) : ℂ) +
          Complex.I * (((P0im c (uSl u s) - P0im c (uSl u t)) x i : ℝ) : ℂ) := by
      have hre_sub : ⇑(P0re c (uSl u s) - P0re c (uSl u t))
          =ᵐ[volume.restrict (B0579.cell c)]
          fun x => P0re c (uSl u s) x - P0re c (uSl u t) x := by
        rw [← cellμ_eq c]; exact Lp.coeFn_sub _ _
      have him_sub : ⇑(P0im c (uSl u s) - P0im c (uSl u t))
          =ᵐ[volume.restrict (B0579.cell c)]
          fun x => P0im c (uSl u s) x - P0im c (uSl u t) x := by
        rw [← cellμ_eq c]; exact Lp.coeFn_sub _ _
      filter_upwards [hb_ae_all s hs i, hb_ae_all t ht i, hre_sub, him_sub] with x hxs hxt hxr hxi
      have hr : (P0re c (uSl u s) - P0re c (uSl u t)) x i =
          P0re c (uSl u s) x i - P0re c (uSl u t) x i :=
        congrArg (fun v : UnforcedLeray.Cyl.Vec2 => v i) hxr
      have hi : (P0im c (uSl u s) - P0im c (uSl u t)) x i =
          P0im c (uSl u s) x i - P0im c (uSl u t) x i :=
        congrArg (fun v : UnforcedLeray.Cyl.Vec2 => v i) hxi
      rw [hxs, hxt, hr, hi]
      dsimp [P0C, cplxOf]
      push_cast; ring
    rw [eLpNorm_congr_ae hae_sub]
    have hm1 := nsrc_L2v_coord_memLp_and_le (P0re c (uSl u s) - P0re c (uSl u t)) i
    have hm2 := nsrc_L2v_coord_memLp_and_le (P0im c (uSl u s) - P0im c (uSl u t)) i
    have hle1 : eLpNorm (fun x =>
        (((P0re c (uSl u s) - P0re c (uSl u t)) x i : ℝ) : ℂ) +
          Complex.I * (((P0im c (uSl u s) - P0im c (uSl u t)) x i : ℝ) : ℂ)) 2
        (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun x => (((P0re c (uSl u s) - P0re c (uSl u t)) x i : ℝ) : ℂ)) 2
          (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => Complex.I * (((P0im c (uSl u s) - P0im c (uSl u t)) x i : ℝ) : ℂ)) 2
          (volume.restrict (B0579.cell c)) :=
      eLpNorm_add_le hm1.1.1 (hm2.1.const_mul Complex.I).1 one_le_two
    have hI : eLpNorm (fun x => Complex.I *
        (((P0im c (uSl u s) - P0im c (uSl u t)) x i : ℝ) : ℂ)) 2
        (volume.restrict (B0579.cell c)) =
        eLpNorm (fun x => (((P0im c (uSl u s) - P0im c (uSl u t)) x i : ℝ) : ℂ)) 2
          (volume.restrict (B0579.cell c)) := by
      rw [nsrc_eLpNorm_const_mul, Complex.norm_I, ENNReal.ofReal_one, one_mul]
    rw [hI] at hle1
    exact hle1.trans (add_le_add hm1.2 hm2.2)
  refine ⟨b_cl, G_cl, hL, hsol, fun s hs => ?_, hmem_slices, hcurl_ae, hb_unif, hb_cont⟩
  have hsZ : s ∈ Z := fun x i => hu_zero s hs x i
  exact ⟨fun x i => hbZ (s, x) hsZ i, fun x i j => hGZ (s, x) hsZ i j⟩

/-! ## 5. Pointwise curl of `advStretch`, zero circulation, pairing identity, and free uniqueness -/

private theorem nsrc_advStretch_curl_smooth {ν c : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {t : ℝ} (ht : 0 < t)
    {u : ℝ × ℝ → Fin 2 → ℂ} {G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ} {om : ℝ × ℝ → ℂ}
    (hu_sm : ∀ i, ContDiff ℝ ∞ (fun y => u y i))
    (hG_eq : ∀ y i j, G y i j = pdC j (fun z => u z i) y)
    (hdiv_u : ∀ x, pdC 0 (fun z => u z 0) x + pdC 1 (fun z => u z 1) x = 0)
    (hω_eq : ∀ y, om y = pdC 0 (fun z => u z 1) y - pdC 1 (fun z => u z 0) y)
    (x : ℝ × ℝ) :
    -(pdC 0 (fun y => advStretch (trainVel tr t) u G y 1) x -
        pdC 1 (fun y => advStretch (trainVel tr t) u G y 0) x) =
      -(((trainVel tr t x 0 : ℂ) * pdC 0 om x + (trainVel tr t x 1 : ℂ) * pdC 1 om x) +
        (u x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
          u x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ))) := by
  have hr : 0 ≤ t := ht.le
  set v0 := V1.vC tr t 0
  set v1 := V1.vC tr t 1
  have hv0_sm : ContDiff ℝ ∞ v0 := V1.vC_contDiff tr hr 0
  have hv1_sm : ContDiff ℝ ∞ v1 := V1.vC_contDiff tr hr 1
  have hv0_d : Differentiable ℝ v0 := hv0_sm.differentiable (by simp)
  have hv1_d : Differentiable ℝ v1 := hv1_sm.differentiable (by simp)
  have hpdv0_d : ∀ j : Fin 2, Differentiable ℝ (B0579.pd j v0) :=
    fun j => (V1.pdv_contDiff tr hr 0 j).differentiable (by simp)
  have hpdv1_d : ∀ j : Fin 2, Differentiable ℝ (B0579.pd j v1) :=
    fun j => (V1.pdv_contDiff tr hr 1 j).differentiable (by simp)
  have hu_d : ∀ i : Fin 2, Differentiable ℝ (fun z => u z i) :=
    fun i => (hu_sm i).differentiable (by simp)
  have hdu_sm : ∀ i j : Fin 2, ContDiff ℝ ∞ (pdC j (fun z => u z i)) := fun i j =>
    ((contDiff_infty_iff_fderiv.1 (hu_sm i)).2).clm_apply contDiff_const
  have hdu_d : ∀ i j : Fin 2, Differentiable ℝ (pdC j (fun z => u z i)) :=
    fun i j => (hdu_sm i j).differentiable (by simp)
  have ha1_eq : (fun y => advStretch (trainVel tr t) u G y 1) =
      fun y => ((v0 y : ℂ) * pdC 0 (fun z => u z 1) y + (v1 y : ℂ) * pdC 1 (fun z => u z 1) y) +
        (u y 0 * (B0579.pd 0 v1 y : ℂ) + u y 1 * (B0579.pd 1 v1 y : ℂ)) := by
    funext y
    simp only [advStretch, Fin.sum_univ_two, V1.trainVel_of_nonneg tr hr, hG_eq, v0, v1]
    ring
  have ha0_eq : (fun y => advStretch (trainVel tr t) u G y 0) =
      fun y => ((v0 y : ℂ) * pdC 0 (fun z => u z 0) y + (v1 y : ℂ) * pdC 1 (fun z => u z 0) y) +
        (u y 0 * (B0579.pd 0 v0 y : ℂ) + u y 1 * (B0579.pd 1 v0 y : ℂ)) := by
    funext y
    simp only [advStretch, Fin.sum_univ_two, V1.trainVel_of_nonneg tr hr, hG_eq, v0, v1]
    ring
  have hω_fun : om = fun y => pdC 0 (fun z => u z 1) y - pdC 1 (fun z => u z 0) y := funext hω_eq
  have hE_fun : UnforcedLeray.B0238.Ec tr t = fun y => B0579.pd 0 v1 y - B0579.pd 1 v0 y :=
    V1.Ec_eq tr hr
  have hv0C : Differentiable ℝ (fun y => (v0 y : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hv0_sm).differentiable (by simp)
  have hv1C : Differentiable ℝ (fun y => (v1 y : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp hv1_sm).differentiable (by simp)
  have hpdv0C : ∀ j : Fin 2, Differentiable ℝ (fun y => (B0579.pd j v0 y : ℂ)) :=
    fun j => (Complex.ofRealCLM.contDiff.comp (V1.pdv_contDiff tr hr 0 j)).differentiable (by simp)
  have hpdv1C : ∀ j : Fin 2, Differentiable ℝ (fun y => (B0579.pd j v1 y : ℂ)) :=
    fun j => (Complex.ofRealCLM.contDiff.comp (V1.pdv_contDiff tr hr 1 j)).differentiable (by simp)
  have hd_mul : ∀ {f g : ℝ × ℝ → ℂ}, DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
      DifferentiableAt ℝ (fun y => f y * g y) x := fun hf hg => hf.mul hg
  have hd_add : ∀ {f g : ℝ × ℝ → ℂ}, DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
      DifferentiableAt ℝ (fun y => f y + g y) x := fun hf hg => hf.add hg
  rw [ha1_eq, ha0_eq, hω_fun, hE_fun]
  rw [nsrc_pdC_add (hd_add (hd_mul (hv0C x) (hdu_d 1 0 x)) (hd_mul (hv1C x) (hdu_d 1 1 x)))
        (hd_add (hd_mul (hu_d 0 x) (hpdv1C 0 x)) (hd_mul (hu_d 1 x) (hpdv1C 1 x))) 0,
    nsrc_pdC_add (hd_mul (hv0C x) (hdu_d 1 0 x)) (hd_mul (hv1C x) (hdu_d 1 1 x)) 0,
    nsrc_pdC_add (hd_mul (hu_d 0 x) (hpdv1C 0 x)) (hd_mul (hu_d 1 x) (hpdv1C 1 x)) 0,
    nsrc_pdC_mul (hv0C x) (hdu_d 1 0 x) 0, nsrc_pdC_mul (hv1C x) (hdu_d 1 1 x) 0,
    nsrc_pdC_mul (hu_d 0 x) (hpdv1C 0 x) 0, nsrc_pdC_mul (hu_d 1 x) (hpdv1C 1 x) 0,
    nsrc_pdC_add (hd_add (hd_mul (hv0C x) (hdu_d 0 0 x)) (hd_mul (hv1C x) (hdu_d 0 1 x)))
        (hd_add (hd_mul (hu_d 0 x) (hpdv0C 0 x)) (hd_mul (hu_d 1 x) (hpdv0C 1 x))) 1,
    nsrc_pdC_add (hd_mul (hv0C x) (hdu_d 0 0 x)) (hd_mul (hv1C x) (hdu_d 0 1 x)) 1,
    nsrc_pdC_add (hd_mul (hu_d 0 x) (hpdv0C 0 x)) (hd_mul (hu_d 1 x) (hpdv0C 1 x)) 1,
    nsrc_pdC_mul (hv0C x) (hdu_d 0 0 x) 1, nsrc_pdC_mul (hv1C x) (hdu_d 0 1 x) 1,
    nsrc_pdC_mul (hu_d 0 x) (hpdv0C 0 x) 1, nsrc_pdC_mul (hu_d 1 x) (hpdv0C 1 x) 1,
    nsrc_pdC_sub (hdu_d 1 0 x) (hdu_d 0 1 x) 0, nsrc_pdC_sub (hdu_d 1 0 x) (hdu_d 0 1 x) 1,
    V1.pd_sub (hpdv1_d 0 x) (hpdv0_d 1 x) 0, V1.pd_sub (hpdv1_d 0 x) (hpdv0_d 1 x) 1]
  simp only [nsrc_pdC_ofReal (hv0_d x), nsrc_pdC_ofReal (hv1_d x),
    nsrc_pdC_ofReal (hpdv1_d 0 x), nsrc_pdC_ofReal (hpdv1_d 1 x),
    nsrc_pdC_ofReal (hpdv0_d 0 x), nsrc_pdC_ofReal (hpdv0_d 1 x),
    V1.trainVel_of_nonneg tr hr x]
  have hcomm_u0 : pdC 1 (pdC 0 (fun z => u z 0)) x = pdC 0 (pdC 1 (fun z => u z 0)) x :=
    nsrc_pdC_comm ((hu_sm 0).of_le (by simp)) 1 0 x
  have hcomm_u1 : pdC 0 (pdC 1 (fun z => u z 1)) x = pdC 1 (pdC 0 (fun z => u z 1)) x :=
    nsrc_pdC_comm ((hu_sm 1).of_le (by simp)) 0 1 x
  have hcomm_v0 : B0579.pd 1 (B0579.pd 0 v0) x = B0579.pd 0 (B0579.pd 1 v0) x :=
    congrFun (V1.pd_comm (hv0_sm.of_le (by simp)) 1 0) x
  have hcomm_v1 : B0579.pd 0 (B0579.pd 1 v1) x = B0579.pd 1 (B0579.pd 0 v1) x :=
    congrFun (V1.pd_comm (hv1_sm.of_le (by simp)) 0 1) x
  have hdiv_v : B0579.pd 1 v1 x = -B0579.pd 0 v0 x := by
    have := V1.vC_div tr hr x; dsimp only [v0, v1]; linarith
  have hdiv_ux : pdC 1 (fun z => u z 1) x = -pdC 0 (fun z => u z 0) x :=
    eq_neg_of_add_eq_zero_right (hdiv_u x)
  rw [hcomm_u0, hcomm_u1, hcomm_v0, hcomm_v1, hdiv_v, hdiv_ux]
  dsimp only [v0, v1]
  push_cast
  ring

private theorem nsrc_ladCut_tendsto_one (x : ℝ × ℝ) :
    Tendsto (fun n : ℕ => (ladCut ((n : ℝ) + 1) x : ℂ)) atTop (𝓝 1) := by
  obtain ⟨_, _, hcut⟩ := ladCutProps
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|x.2|⌉₊) fun n hn => ?_
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hx2 : x.2 ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hle : |x.2| ≤ (n : ℝ) + 1 := by
      have : (⌈|x.2|⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [Nat.le_ceil |x.2|]
    nlinarith [abs_nonneg x.2, sq_abs x.2]
  rw [(hcut ((n : ℝ) + 1) hR).2.2.1 x hx2]
  simp

private theorem nsrc_zero_circ {ν b A_m : ℝ} (hν : 0 < ν) (hAm : 0 ≤ A_m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (coreEnd ν b))
    {u₀ : ℝ × ℝ → Fin 2 → ℂ} {ω₀ : ℝ × ℝ → ℂ} {f_t : ℝ × ℝ → ℂ}
    (hu₀_lp : ∀ i, MemLp (fun x => u₀ x i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hdiv_u₀ : ∀ ψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        (u₀ x 0 * (B0579.pd 0 ψ x : ℂ) + u₀ x 1 * (B0579.pd 1 ψ x : ℂ)) = 0)
    (hω₀_int : IntegrableOn ω₀ (B0579.cell (ν ^ (-2 : ℝ))))
    (hω₀_wk : ∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j ω₀ (pdC j ω₀))
    (hf_mem : MemLp f_t 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (hf_def : ∀ x, f_t x =
      -(((trainVel tr t x 0 : ℂ) * pdC 0 ω₀ x + (trainVel tr t x 1 : ℂ) * pdC 1 ω₀ x) +
        (u₀ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
          u₀ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)))) :
    HasZeroCirculation (ν ^ (-2 : ℝ)) f_t := by
  let c := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hint_f : IntegrableOn f_t (B0579.cell c) := zcCellIntegrable c 9 (by norm_num) f_t hf_mem
  refine ⟨hint_f, ?_⟩
  obtain ⟨K_cut, hK_cut, hcut⟩ := ladCutProps
  set χ : ℕ → ℝ × ℝ → ℝ := fun n => ladCut ((n : ℝ) + 1)
  have hχ_test : ∀ n, B0579.IsCylTest c (χ n) := fun n => (hcut ((n : ℝ) + 1) (by positivity)).1 c
  have hχ_01 : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1 := fun n => (hcut ((n : ℝ) + 1) (by positivity)).2.1
  have hχ_pd : ∀ n x j, |B0579.pd j (χ n) x| ≤ K_cut / ((n : ℝ) + 1) :=
    fun n => (hcut ((n : ℝ) + 1) (by positivity)).2.2.2.2.1
  -- Dominated convergence: `∫ f_t * χ_n → ∫ f_t`
  have hlim_lhs : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, f_t x * (χ n x : ℂ))
      atTop (𝓝 (∫ x in B0579.cell c, f_t x)) := by
    have h1 : (∫ x in B0579.cell c, f_t x) = ∫ x in B0579.cell c, f_t x * 1 := by simp
    rw [h1]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f_t x‖) ?_ hint_f.norm ?_ ?_
    · intro n
      exact hint_f.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (hχ_test n).continuous).aestronglyMeasurable
    · intro n
      filter_upwards with x
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ_01 n x).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (hχ_01 n x).2
    · filter_upwards with x
      exact tendsto_const_nhds.mul (nsrc_ladCut_tendsto_one x)
  -- Commutator formula for `∫ f_t * χ_n`
  have hEc_lp : MemLp (fun x => (UnforcedLeray.B0238.Ec tr t x : ℂ)) 2
      (volume.restrict (B0579.cell c)) := nsrc_Ec_memLp2 hν hAm hbd ht
  have hint_uE : ∀ i : Fin 2, Integrable (fun x => ‖u₀ x i‖ * |UnforcedLeray.B0238.Ec tr t x|)
      (volume.restrict (B0579.cell c)) := by
    intro i
    have h := (hu₀_lp i).norm.integrable_mul hEc_lp.norm
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hcomm_eq : ∀ n : ℕ, ∫ x in B0579.cell c, f_t x * (χ n x : ℂ) =
      (∑ j : Fin 2, ∫ x in B0579.cell c,
        ω₀ x * ((V1.vC tr t j x * B0579.pd j (χ n) x : ℝ) : ℂ)) +
      (∑ i : Fin 2, ∫ x in B0579.cell c,
        u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ)) := by
    intro n
    set ψv : Fin 2 → ℝ × ℝ → ℝ := fun j x => V1.vC tr t j x * χ n x
    have hψv : ∀ j, B0579.IsCylTest c (ψv j) := fun j =>
      V1.cylTest_mul_left (V1.vC_contDiff tr ht.1.le j) (V1.vC_periodic tr ht.1.le j) (hχ_test n)
    set ψE : ℝ × ℝ → ℝ := fun x => UnforcedLeray.B0238.Ec tr t x * χ n x
    have hψE : B0579.IsCylTest c ψE :=
      V1.cylTest_mul_left (V1.Ec_contDiff tr ht.1.le) (V1.Ec_periodic tr ht.1.le) (hχ_test n)
    -- Term 1 (`v · ∇ω₀`)
    have Iv0 := ((hω₀_wk 0).1 (ψv 0) (hψv 0)).2
    have Iv1 := ((hω₀_wk 1).1 (ψv 1) (hψv 1)).2
    have Iω0 := ((hω₀_wk 0).1 (ψv 0) (hψv 0)).1
    have Iω1 := ((hω₀_wk 1).1 (ψv 1) (hψv 1)).1
    have hω_comm_int : ∀ j : Fin 2, IntegrableOn
        (fun x => ω₀ x * ((V1.vC tr t j x * B0579.pd j (χ n) x : ℝ) : ℂ)) (B0579.cell c) := by
      intro j
      refine (hω₀_int.norm.const_mul (A_m * (K_cut / ((n : ℝ) + 1)))).mono' ?_ ?_
      · exact hω₀_int.aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp ((V1.vC_contDiff tr ht.1.le j).continuous.mul
            (hχ_test n |>.pd j).continuous)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
        have hvj : |V1.vC tr t j x| ≤ A_m := by
          have hb1 := nsrc_trainVel_bdd hbd ht j x hx
          have hbr1 : 1 ≤ B0579.bracket x ^ (9 : ℝ) := by
            refine Real.one_le_rpow (Real.one_le_sqrt.2 ?_) (by norm_num)
            unfold B0579.jb; linarith [sq_nonneg x.1, sq_nonneg x.2]
          rw [V1.trainVel_of_nonneg tr ht.1.le x j, Complex.norm_real, Real.norm_eq_abs] at hb1
          nlinarith [abs_nonneg (V1.vC tr t j x)]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_comm (A_m * _)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hvj (hχ_pd n x j) (abs_nonneg _) hAm) (norm_nonneg _)
    have hTv : ∫ x in B0579.cell c,
          ((trainVel tr t x 0 : ℂ) * pdC 0 ω₀ x + (trainVel tr t x 1 : ℂ) * pdC 1 ω₀ x) *
            (χ n x : ℂ) =
        -∑ j : Fin 2, ∫ x in B0579.cell c,
          ω₀ x * ((V1.vC tr t j x * B0579.pd j (χ n) x : ℝ) : ℂ) := by
      have heq1 : (fun x => ((trainVel tr t x 0 : ℂ) * pdC 0 ω₀ x +
            (trainVel tr t x 1 : ℂ) * pdC 1 ω₀ x) * (χ n x : ℂ)) =
          fun x => pdC 0 ω₀ x * (ψv 0 x : ℂ) + pdC 1 ω₀ x * (ψv 1 x : ℂ) := by
        funext x
        simp only [ψv, V1.trainVel_of_nonneg tr ht.1.le]
        push_cast; ring
      have hw0 : ∫ x in B0579.cell c, pdC 0 ω₀ x * (ψv 0 x : ℂ) =
          -∫ x in B0579.cell c, ω₀ x * (B0579.pd 0 (ψv 0) x : ℂ) :=
        neg_eq_iff_eq_neg.1 ((hω₀_wk 0).2 (ψv 0) (hψv 0)).symm
      have hw1 : ∫ x in B0579.cell c, pdC 1 ω₀ x * (ψv 1 x : ℂ) =
          -∫ x in B0579.cell c, ω₀ x * (B0579.pd 1 (ψv 1) x : ℂ) :=
        neg_eq_iff_eq_neg.1 ((hω₀_wk 1).2 (ψv 1) (hψv 1)).symm
      rw [heq1, integral_add Iv0 Iv1]
      change (∫ x in B0579.cell c, pdC 0 ω₀ x * (ψv 0 x : ℂ)) +
          (∫ x in B0579.cell c, pdC 1 ω₀ x * (ψv 1 x : ℂ)) = _
      rw [hw0, hw1]
      have hsum_ω : (∫ x in B0579.cell c, ω₀ x * (B0579.pd 0 (ψv 0) x : ℂ)) +
            (∫ x in B0579.cell c, ω₀ x * (B0579.pd 1 (ψv 1) x : ℂ)) =
          (∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t 0 x * B0579.pd 0 (χ n) x : ℝ) : ℂ)) +
            (∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t 1 x * B0579.pd 1 (χ n) x : ℝ) : ℂ)) := by
        rw [← integral_add Iω0 Iω1, ← integral_add (hω_comm_int 0) (hω_comm_int 1)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only [ψv]
        rw [V1.pd_mul' (V1.vC_diff tr ht.1.le 0) (hχ_test n).differentiable 0 x,
          V1.pd_mul' (V1.vC_diff tr ht.1.le 1) (hχ_test n).differentiable 1 x]
        have hdiv := V1.vC_div tr ht.1.le x
        have hdiv1 : B0579.pd 1 (V1.vC tr t 1) x = -B0579.pd 0 (V1.vC tr t 0) x := by linarith
        rw [hdiv1]
        push_cast; ring
      rw [Fin.sum_univ_two]
      linear_combination -hsum_ω
    -- Term 2 (`u₀ · ∇Ec`)
    have IuE_pd : ∀ i : Fin 2, IntegrableOn
        (fun x => u₀ x i * (B0579.pd i ψE x : ℂ)) (B0579.cell c) :=
      fun i => CoreDuhamelRepSub.integrableOn_cylTest_mul (hψE.pd i) (hu₀_lp i)
    have huE_comm_int : ∀ i : Fin 2, IntegrableOn
        (fun x => u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ))
        (B0579.cell c) := by
      intro i
      refine ((hint_uE i).const_mul (K_cut / ((n : ℝ) + 1))).mono' ?_ ?_
      · exact (hu₀_lp i).1.mul (Complex.continuous_ofReal.comp
          ((V1.Ec_contDiff tr ht.1.le).continuous.mul
            (hψE.smooth.of_le le_rfl |>.continuous |> fun _ =>
              (hχ_test n |>.pd i).continuous))).aestronglyMeasurable
      · filter_upwards with x
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        calc ‖u₀ x i‖ * (|UnforcedLeray.B0238.Ec tr t x| * |B0579.pd i (χ n) x|)
            ≤ ‖u₀ x i‖ * (|UnforcedLeray.B0238.Ec tr t x| * (K_cut / ((n : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hχ_pd n x i) (abs_nonneg _)) (norm_nonneg _)
          _ = K_cut / ((n : ℝ) + 1) * (‖u₀ x i‖ * |UnforcedLeray.B0238.Ec tr t x|) := by ring
    have IuE_main : ∀ i : Fin 2, IntegrableOn
        (fun x => u₀ x i * ((B0579.pd i (UnforcedLeray.B0238.Ec tr t) x * χ n x : ℝ) : ℂ))
        (B0579.cell c) := by
      intro i
      have heq : (fun x => u₀ x i *
            ((B0579.pd i (UnforcedLeray.B0238.Ec tr t) x * χ n x : ℝ) : ℂ)) =
          fun x => u₀ x i * (B0579.pd i ψE x : ℂ) -
            u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ) := by
        funext x
        dsimp [ψE]
        rw [V1.pd_mul' ((V1.Ec_contDiff tr ht.1.le).differentiable (by simp))
          (hχ_test n).differentiable i x]
        push_cast; ring
      rw [heq]
      exact (IuE_pd i).sub (huE_comm_int i)
    have hTE : ∫ x in B0579.cell c,
          (u₀ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
            u₀ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)) * (χ n x : ℂ) =
        -∑ i : Fin 2, ∫ x in B0579.cell c,
          u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ) := by
      have hdiv0 := hdiv_u₀ ψE hψE
      have heq_main : (fun x =>
          (u₀ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
            u₀ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)) * (χ n x : ℂ)) =
          fun x => (u₀ x 0 * (B0579.pd 0 ψE x : ℂ) + u₀ x 1 * (B0579.pd 1 ψE x : ℂ)) -
            (u₀ x 0 * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd 0 (χ n) x : ℝ) : ℂ) +
              u₀ x 1 * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd 1 (χ n) x : ℝ) : ℂ)) := by
        funext x
        dsimp [ψE]
        rw [V1.pd_mul' ((V1.Ec_contDiff tr ht.1.le).differentiable (by simp))
            (hχ_test n).differentiable 0 x,
          V1.pd_mul' ((V1.Ec_contDiff tr ht.1.le).differentiable (by simp))
            (hχ_test n).differentiable 1 x]
        push_cast; ring
      have hsub_uE := integral_sub ((IuE_pd 0).add (IuE_pd 1))
          ((huE_comm_int 0).add (huE_comm_int 1))
      dsimp only [Pi.add_apply, Pi.sub_apply] at hsub_uE
      change (∫ x in B0579.cell c, _) = _ at hdiv0
      rw [heq_main, hsub_uE, hdiv0, zero_sub,
        integral_add (huE_comm_int 0) (huE_comm_int 1), Fin.sum_univ_two]
    have hf_χ_eq : (fun x => f_t x * (χ n x : ℂ)) =
        fun x => -(((trainVel tr t x 0 : ℂ) * pdC 0 ω₀ x +
            (trainVel tr t x 1 : ℂ) * pdC 1 ω₀ x) * (χ n x : ℂ) +
          (u₀ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
            u₀ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)) * (χ n x : ℂ)) := by
      funext x; rw [hf_def x]; ring
    have ITv : IntegrableOn
        (fun x => ((trainVel tr t x 0 : ℂ) * pdC 0 ω₀ x +
          (trainVel tr t x 1 : ℂ) * pdC 1 ω₀ x) * (χ n x : ℂ)) (B0579.cell c) := by
      refine (Iv0.add Iv1).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
      simp only [Pi.add_apply, ψv, V1.trainVel_of_nonneg tr ht.1.le]; push_cast; ring
    have ITE : IntegrableOn
        (fun x => (u₀ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
          u₀ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)) * (χ n x : ℂ))
        (B0579.cell c) := by
      refine ((IuE_main 0).add (IuE_main 1)).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
      simp only [Pi.add_apply]; push_cast; ring
    rw [hf_χ_eq, integral_neg, integral_add ITv ITE, hTv, hTE]
    ring
  -- Commutator tends to `0` as `n → ∞` (`1 / (n + 1) → 0`)
  have hinv_lim : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim_rhs : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, f_t x * (χ n x : ℂ))
      atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set C_tot : ℝ := 2 * (A_m * K_cut * ∫ x in B0579.cell c, ‖ω₀ x‖) +
      K_cut * ((∫ x in B0579.cell c, ‖u₀ x 0‖ * |UnforcedLeray.B0238.Ec tr t x|) +
        (∫ x in B0579.cell c, ‖u₀ x 1‖ * |UnforcedLeray.B0238.Ec tr t x|))
    have hbd_lim : Tendsto (fun n : ℕ => C_tot * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using hinv_lim.const_mul C_tot
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hbd_lim
    rw [sub_zero, hcomm_eq n]
    have h1 : ∀ j : Fin 2, ‖∫ x in B0579.cell c,
        ω₀ x * ((V1.vC tr t j x * B0579.pd j (χ n) x : ℝ) : ℂ)‖ ≤
        (A_m * K_cut * ∫ x in B0579.cell c, ‖ω₀ x‖) * ((n : ℝ) + 1)⁻¹ := by
      intro j
      calc ‖∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t j x * B0579.pd j (χ n) x : ℝ) : ℂ)‖
          ≤ ∫ x in B0579.cell c, ‖ω₀ x * ((V1.vC tr t j x * B0579.pd j (χ n) x : ℝ) : ℂ)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in B0579.cell c, (A_m * (K_cut / ((n : ℝ) + 1))) * ‖ω₀ x‖ := by
            refine setIntegral_mono_on ?_ (hω₀_int.norm.const_mul _)
              (B0579.measurableSet_cell c) fun x hx => ?_
            · refine (hω₀_int.norm.const_mul (A_m * (K_cut / ((n : ℝ) + 1)))).mono' ?_ ?_
              · exact (hω₀_int.aestronglyMeasurable.mul
                  (Complex.continuous_ofReal.comp ((V1.vC_contDiff tr ht.1.le j).continuous.mul
                    (hχ_test n |>.pd j).continuous)).aestronglyMeasurable).norm
              · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with y hy
                rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
                  Real.norm_eq_abs, abs_mul, mul_comm (A_m * _)]
                have hvj : |V1.vC tr t j y| ≤ A_m := by
                  have hb1 := nsrc_trainVel_bdd hbd ht j y hy
                  have hbr1 : 1 ≤ B0579.bracket y ^ (9 : ℝ) := by
                    refine Real.one_le_rpow (Real.one_le_sqrt.2 ?_) (by norm_num)
                    unfold B0579.jb; linarith [sq_nonneg y.1, sq_nonneg y.2]
                  rw [V1.trainVel_of_nonneg tr ht.1.le y j, Complex.norm_real,
                    Real.norm_eq_abs] at hb1
                  nlinarith [abs_nonneg (V1.vC tr t j y)]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul hvj (hχ_pd n y j) (abs_nonneg _) hAm) (norm_nonneg _)
            · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_comm (A_m * _)]
              have hvj : |V1.vC tr t j x| ≤ A_m := by
                have hb1 := nsrc_trainVel_bdd hbd ht j x hx
                have hbr1 : 1 ≤ B0579.bracket x ^ (9 : ℝ) := by
                  refine Real.one_le_rpow (Real.one_le_sqrt.2 ?_) (by norm_num)
                  unfold B0579.jb; linarith [sq_nonneg x.1, sq_nonneg x.2]
                rw [V1.trainVel_of_nonneg tr ht.1.le x j, Complex.norm_real,
                  Real.norm_eq_abs] at hb1
                nlinarith [abs_nonneg (V1.vC tr t j x)]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hvj (hχ_pd n x j) (abs_nonneg _) hAm) (norm_nonneg _)
        _ = (A_m * K_cut * ∫ x in B0579.cell c, ‖ω₀ x‖) * ((n : ℝ) + 1)⁻¹ := by
            rw [integral_const_mul]; ring
    have h2 : ∀ i : Fin 2, ‖∫ x in B0579.cell c,
        u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ)‖ ≤
        (K_cut * ∫ x in B0579.cell c, ‖u₀ x i‖ * |UnforcedLeray.B0238.Ec tr t x|) *
          ((n : ℝ) + 1)⁻¹ := by
      intro i
      calc ‖∫ x in B0579.cell c,
              u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ)‖
          ≤ ∫ x in B0579.cell c,
              ‖u₀ x i * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd i (χ n) x : ℝ) : ℂ)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in B0579.cell c,
              (K_cut / ((n : ℝ) + 1)) * (‖u₀ x i‖ * |UnforcedLeray.B0238.Ec tr t x|) := by
            refine setIntegral_mono_on ?_ ((hint_uE i).const_mul _)
              (B0579.measurableSet_cell c) fun x _ => ?_
            · refine ((hint_uE i).const_mul (K_cut / ((n : ℝ) + 1))).mono' ?_ ?_
              · exact ((hu₀_lp i).1.mul (Complex.continuous_ofReal.comp
                  ((V1.Ec_contDiff tr ht.1.le).continuous.mul
                    (hχ_test n |>.pd i).continuous)).aestronglyMeasurable).norm
              · filter_upwards with y
                rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
                  Real.norm_eq_abs, abs_mul]
                calc ‖u₀ y i‖ * (|UnforcedLeray.B0238.Ec tr t y| * |B0579.pd i (χ n) y|)
                    ≤ ‖u₀ y i‖ * (|UnforcedLeray.B0238.Ec tr t y| * (K_cut / ((n : ℝ) + 1))) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left (hχ_pd n y i) (abs_nonneg _)) (norm_nonneg _)
                  _ = K_cut / ((n : ℝ) + 1) *
                        (‖u₀ y i‖ * |UnforcedLeray.B0238.Ec tr t y|) := by ring
            · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
              calc ‖u₀ x i‖ * (|UnforcedLeray.B0238.Ec tr t x| * |B0579.pd i (χ n) x|)
                  ≤ ‖u₀ x i‖ * (|UnforcedLeray.B0238.Ec tr t x| * (K_cut / ((n : ℝ) + 1))) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left (hχ_pd n x i) (abs_nonneg _)) (norm_nonneg _)
                _ = K_cut / ((n : ℝ) + 1) *
                      (‖u₀ x i‖ * |UnforcedLeray.B0238.Ec tr t x|) := by ring
        _ = (K_cut * ∫ x in B0579.cell c, ‖u₀ x i‖ * |UnforcedLeray.B0238.Ec tr t x|) *
              ((n : ℝ) + 1)⁻¹ := by
            rw [integral_const_mul]; ring
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    calc ‖((∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t 0 x * B0579.pd 0 (χ n) x : ℝ) : ℂ)) +
            (∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t 1 x * B0579.pd 1 (χ n) x : ℝ) : ℂ))) +
          ((∫ x in B0579.cell c,
              u₀ x 0 * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd 0 (χ n) x : ℝ) : ℂ)) +
            (∫ x in B0579.cell c,
              u₀ x 1 * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd 1 (χ n) x : ℝ) : ℂ)))‖
        ≤ (‖∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t 0 x * B0579.pd 0 (χ n) x : ℝ) : ℂ)‖ +
            ‖∫ x in B0579.cell c, ω₀ x * ((V1.vC tr t 1 x * B0579.pd 1 (χ n) x : ℝ) : ℂ)‖) +
          (‖∫ x in B0579.cell c,
              u₀ x 0 * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd 0 (χ n) x : ℝ) : ℂ)‖ +
            ‖∫ x in B0579.cell c,
              u₀ x 1 * ((UnforcedLeray.B0238.Ec tr t x * B0579.pd 1 (χ n) x : ℝ) : ℂ)‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ ((A_m * K_cut * ∫ x in B0579.cell c, ‖ω₀ x‖) * ((n : ℝ) + 1)⁻¹ +
            (A_m * K_cut * ∫ x in B0579.cell c, ‖ω₀ x‖) * ((n : ℝ) + 1)⁻¹) +
          ((K_cut * ∫ x in B0579.cell c, ‖u₀ x 0‖ * |UnforcedLeray.B0238.Ec tr t x|) *
              ((n : ℝ) + 1)⁻¹ +
            (K_cut * ∫ x in B0579.cell c, ‖u₀ x 1‖ * |UnforcedLeray.B0238.Ec tr t x|) *
              ((n : ℝ) + 1)⁻¹) := add_le_add (add_le_add (h1 0) (h1 1)) (add_le_add (h2 0) (h2 1))
      _ = C_tot * ((n : ℝ) + 1)⁻¹ := by dsimp [C_tot]; ring
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

private theorem nsrc_pairing_norm_le {c : ℝ} {h φ : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hh : MemLp h 2 (B0579.cellMeasure c 9))
    (hg : ∀ j, HasWeakCellDerivC c j φ (g j)) (hh1 : h1Norm c 9 φ g ≤ 1) :
    ENNReal.ofReal ‖∫ x in B0579.cell c, h x * φ x‖ ≤ xNorm c 9 h := by
  have hfm : AEStronglyMeasurable h (volume.restrict (B0579.cell c)) :=
    hh.1.mono_ac (B0579.ac_cellMeasure c 9)
  have hφm : AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) :=
    CoreDuhamelRepSub.aestronglyMeasurable_val_of_hasWeakCellDerivC (hg 1)
  set F₁ : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (B0579.jb x ^ (9 / 2 : ℝ)) * ‖h x‖ₑ
  set F₂ : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (B0579.jb x ^ (-9 / 2 : ℝ)) * ‖φ x‖ₑ
  have hF₁ : AEMeasurable F₁ (volume.restrict (B0579.cell c)) :=
    ((B0579.continuous_jb_rpow _).measurable.ennreal_ofReal.aemeasurable).mul hfm.enorm
  have hF₂ : AEMeasurable F₂ (volume.restrict (B0579.cell c)) :=
    ((B0579.continuous_jb_rpow _).measurable.ennreal_ofReal.aemeasurable).mul hφm.enorm
  have hpt : ∀ x : ℝ × ℝ, ‖h x * φ x‖ₑ = F₁ x * F₂ x := by
    intro x
    have hjb : B0579.jb x ^ (9 / 2 : ℝ) * B0579.jb x ^ (-9 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (B0579.jb_pos x)]; norm_num
    dsimp [F₁, F₂]
    calc ‖h x * φ x‖ₑ = 1 * (‖h x‖ₑ * ‖φ x‖ₑ) := by rw [enorm_mul, one_mul]
      _ = (ENNReal.ofReal (B0579.jb x ^ (9 / 2 : ℝ)) *
            ENNReal.ofReal (B0579.jb x ^ (-9 / 2 : ℝ))) * (‖h x‖ₑ * ‖φ x‖ₑ) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _), hjb, ENNReal.ofReal_one]
      _ = _ := by ring
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (B0579.cell c))
    Real.HolderConjugate.two_two hF₁ hF₂
  have hsq₁ : (∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = xNorm c 9 h := by
    have heq : ∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ) = xNorm c 9 h ^ 2 := by
      rw [CoreDuhamelRepSub.xNorm_sq_eq]
      refine lintegral_congr fun x => ?_
      dsimp [F₁]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos x).le _),
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) _),
        ← Real.rpow_natCast (B0579.jb x ^ (9 / 2 : ℝ)) 2, ← Real.rpow_mul (B0579.jb_pos x).le]
      norm_num
    rw [heq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have hsq₂ : (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 := by
    have heq : ∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ) = xNorm c (-9) φ ^ 2 := by
      rw [CoreDuhamelRepSub.xNorm_sq_eq]
      refine lintegral_congr fun x => ?_
      dsimp [F₂]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (Real.rpow_nonneg (B0579.jb_pos x).le _),
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) _),
        ← Real.rpow_natCast (B0579.jb x ^ (-9 / 2 : ℝ)) 2, ← Real.rpow_mul (B0579.jb_pos x).le]
      norm_num
    rw [heq]
    calc (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ)
        ≤ (xNorm c (-9) φ ^ 2 + ∑ j, xNorm c (-9) (g j) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow le_self_add (by norm_num)
      _ = h1Norm c 9 φ g := rfl
      _ ≤ 1 := hh1
  rw [ofReal_norm]
  calc ‖∫ x in B0579.cell c, h x * φ x‖ₑ
      ≤ ∫⁻ x in B0579.cell c, ‖h x * φ x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in B0579.cell c, F₁ x * F₂ x := lintegral_congr hpt
    _ ≤ (∫⁻ x in B0579.cell c, F₁ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x in B0579.cell c, F₂ x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hCS
    _ ≤ xNorm c 9 h * 1 := by rw [hsq₁]; exact mul_le_mul_of_nonneg_left hsq₂ bot_le
    _ = xNorm c 9 h := mul_one _

private theorem nsrc_pairing_slice {ν b A_m C_tr : ℝ} (hν : 0 < ν) (hAm : 0 ≤ A_m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hbd : ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m)
    (hLad : LadTrainBdd tr 7 (coreEnd ν b) C_tr)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (coreEnd ν b))
    {u₀ : ℝ × ℝ → Fin 2 → ℂ} {Gt₀ : ℝ × ℝ → Fin 2 → Fin 2 → ℂ}
    {ω₀ f_t : ℝ × ℝ → ℂ}
    (hu₀_m : ∀ i, Measurable fun x => u₀ x i)
    (hGt₀_m : ∀ i j, Measurable fun x => Gt₀ x i j)
    (hu₀_lp : ∀ i, MemLp (fun x => u₀ x i) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hGt₀_lp : ∀ i j, MemLp (fun x => Gt₀ x i j) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hdiv_u₀ : LMWeakDivFree (ν ^ (-2 : ℝ)) u₀)
    (hwk_u₀ : ∀ i j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j (fun x => u₀ x i) (fun x => Gt₀ x i j))
    (hcurl_u₀ : (fun x => Gt₀ x 1 0 - Gt₀ x 0 1)
      =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] ω₀)
    (hω₀_lp : MemLp ω₀ 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hpdω₀_lp : ∀ j, MemLp (pdC j ω₀) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))))
    (hω₀_wk : ∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j ω₀ (pdC j ω₀))
    (hf_mem : MemLp f_t 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9))
    (hf_def : ∀ x, f_t x =
      -(((trainVel tr t x 0 : ℂ) * pdC 0 ω₀ x + (trainVel tr t x 1 : ℂ) * pdC 1 ω₀ x) +
        (u₀ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
          u₀ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ))))
    {φ : ℝ × ℝ → ℂ} {g : Fin 2 → ℝ × ℝ → ℂ}
    (hg : ∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j))
    (hh1 : h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1) :
    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_t x * φ x =
      coreSrcFun (ν ^ (-2 : ℝ)) (advStretch (trainVel tr t) u₀ Gt₀) g := by
  let c := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hv1 : ContDiff ℝ 1 (trainVel tr t) := contDiff_trainVel tr ht.1
  have hv_bd := CoreDuhamelRepSub.trainVel_weighted_bound hbd ht
  -- Mollified family `(u_k, G_k, ω_k, f_k)`
  set u_k : ℕ → LMSpField := fun k => lmJ c k u₀
  set G_k : ℕ → ℝ × ℝ → Fin 2 → Fin 2 → ℂ :=
    fun k x i j => lmJs c k (fun y => Gt₀ y i j) x
  set ω_k : ℕ → ℝ × ℝ → ℂ := fun k => lmJs c k ω₀
  set f_k : ℕ → ℝ × ℝ → ℂ := fun k x =>
    -(((trainVel tr t x 0 : ℂ) * pdC 0 (ω_k k) x + (trainVel tr t x 1 : ℂ) * pdC 1 (ω_k k) x) +
      (u_k k x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
        u_k k x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)))
  have hLM_u₀ : ∀ i j, LMWeakPd c j (fun x => u₀ x i) (fun x => Gt₀ x i j) := fun i j =>
    ⟨hu₀_lp i, hGt₀_lp i j, fun ψ hψ_sm hψ_per hψ_band =>
      (hwk_u₀ i j).2 ψ ⟨hψ_sm, hψ_per, hψ_band⟩⟩
  have hLM_ω₀ : ∀ j, LMWeakPd c j ω₀ (pdC j ω₀) := fun j =>
    ⟨hω₀_lp, hpdω₀_lp j, fun ψ hψ_sm hψ_per hψ_band =>
      (hω₀_wk j).2 ψ ⟨hψ_sm, hψ_per, hψ_band⟩⟩
  have huk_sm : ∀ k i, ContDiff ℝ ∞ (fun x => u_k k x i) :=
    fun k i => lmJs_contDiff hc k (hu₀_lp i)
  have huk_per : ∀ k x i, u_k k (x.1 + c, x.2) i = u_k k x i :=
    fun k x i => lmJ_periodic hc.ne' k u₀ x i
  have huk_lp : ∀ k i, MemLp (fun x => u_k k x i) 2 (volume.restrict (B0579.cell c)) :=
    fun k i => lmJs_memLp hc k (hu₀_lp i)
  have hGk_sm : ∀ k i j, ContDiff ℝ ∞ (fun x => G_k k x i j) :=
    fun k i j => lmJs_contDiff hc k (hGt₀_lp i j)
  have hGk_per : ∀ k x i j, G_k k (x.1 + c, x.2) i j = G_k k x i j :=
    fun k x i j => lmJs_periodic hc.ne' k _ x
  have hGk_lp : ∀ k i j, MemLp (fun x => G_k k x i j) 2 (volume.restrict (B0579.cell c)) :=
    fun k i j => lmJs_memLp hc k (hGt₀_lp i j)
  have hGk_eq_pd : ∀ k x i j, G_k k x i j = pdC j (fun y => u_k k y i) x := by
    intro k x i j
    have hd : DifferentiableAt ℝ (fun y => u_k k y i) x :=
      ((huk_sm k i).differentiable (by simp)) x
    rw [← nsrc_LMPd_eq_pdC hd j]
    exact (lmJs_commute hc k j (hLM_u₀ i j) x).symm
  have hdiv_uk : ∀ k x, pdC 0 (fun y => u_k k y 0) x + pdC 1 (fun y => u_k k y 1) x = 0 := by
    intro k x
    have hd0 : DifferentiableAt ℝ (fun y => u_k k y 0) x :=
      ((huk_sm k 0).differentiable (by simp)) x
    have hd1 : DifferentiableAt ℝ (fun y => u_k k y 1) x :=
      ((huk_sm k 1).differentiable (by simp)) x
    rw [← nsrc_LMPd_eq_pdC hd0 0, ← nsrc_LMPd_eq_pdC hd1 1]
    exact lmJ_divFreeWeak hc k u₀ hu₀_lp hdiv_u₀ x
  have hωk_eq : ∀ k x, ω_k k x = pdC 0 (fun y => u_k k y 1) x - pdC 1 (fun y => u_k k y 0) x := by
    intro k x
    rw [← hGk_eq_pd k x 1 0, ← hGk_eq_pd k x 0 1]
    dsimp [ω_k, G_k, lmJs]
    have hint10 := lmJs_integrable hc k (hGt₀_lp 1 0) x
    have hint01 := lmJs_integrable hc k (hGt₀_lp 0 1) x
    rw [← integral_sub hint10 hint01]
    refine integral_congr_ae ?_
    filter_upwards [hcurl_u₀] with y hy
    rw [← hy]; ring
  have hpd_ωk_eq : ∀ k j x, pdC j (ω_k k) x = lmJs c k (pdC j ω₀) x := by
    intro k j x
    have hd : DifferentiableAt ℝ (ω_k k) x :=
      ((lmJs_contDiff hc k hω₀_lp).differentiable (by simp)) x
    rw [← nsrc_LMPd_eq_pdC hd j]
    exact lmJs_commute hc k j (hLM_ω₀ j) x
  have hpd_ωk_lp : ∀ k j, MemLp (pdC j (ω_k k)) 2 (volume.restrict (B0579.cell c)) := by
    intro k j
    have heq : pdC j (ω_k k) = lmJs c k (pdC j ω₀) := funext (hpd_ωk_eq k j)
    rw [heq]; exact lmJs_memLp hc k (hpdω₀_lp j)
  have hfk_mem : ∀ k, MemLp (f_k k) 2 (B0579.cellMeasure c 9) := by
    intro k
    have hv0_m : AEStronglyMeasurable (fun x => (trainVel tr t x 0 : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp ((continuous_apply 0).comp hv1.continuous)).aestronglyMeasurable
    have hv1_m : AEStronglyMeasurable (fun x => (trainVel tr t x 1 : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp ((continuous_apply 1).comp hv1.continuous)).aestronglyMeasurable
    have hE0_m : AEStronglyMeasurable (fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr ht.1.le 0).continuous).aestronglyMeasurable
    have hE1_m : AEStronglyMeasurable (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr ht.1.le 1).continuous).aestronglyMeasurable
    have m1 := (nsrc_memLp_xNorm_mul hAm hv0_m (nsrc_trainVel_bdd hbd ht 0) (hpd_ωk_lp k 0)).1
    have m2 := (nsrc_memLp_xNorm_mul hAm hv1_m (nsrc_trainVel_bdd hbd ht 1) (hpd_ωk_lp k 1)).1
    have m3 := (nsrc_memLp_xNorm_mul (le_max_right C_tr 0) hE0_m
      (nsrc_pdEc_bdd hLad ⟨ht.1.le, ht.2⟩ 0) (huk_lp k 0)).1
    have m4 := (nsrc_memLp_xNorm_mul (le_max_right C_tr 0) hE1_m
      (nsrc_pdEc_bdd hLad ⟨ht.1.le, ht.2⟩ 1) (huk_lp k 1)).1
    have hfk_eq : f_k k = -(((fun x => (trainVel tr t x 0 : ℂ) * pdC 0 (ω_k k) x) +
          (fun x => (trainVel tr t x 1 : ℂ) * pdC 1 (ω_k k) x)) +
        ((fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u_k k x 0) +
          (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u_k k x 1))) := by
      funext x; dsimp [f_k]; ring
    rw [hfk_eq]
    exact ((m1.add m2).add (m3.add m4)).neg
  -- Step A: For each fixed `k`, `∫ f_k * φ = coreSrcFun c (advStretch v (u_k k) (G_k k)) g`
  have hpair_k : ∀ k : ℕ,
      ∫ x in B0579.cell c, f_k k x * φ x =
        coreSrcFun c (advStretch (trainVel tr t) (u_k k) (G_k k)) g := by
    intro k
    set a_k := advStretch (trainVel tr t) (u_k k) (G_k k)
    have hak_eq : ∀ i : Fin 2, (fun x => a_k x i) = fun x =>
        ((V1.vC tr t 0 x : ℂ) * G_k k x i 0 + (u_k k x 0 * (B0579.pd 0 (V1.vC tr t i) x : ℂ))) +
          ((V1.vC tr t 1 x : ℂ) * G_k k x i 1 + (u_k k x 1 * (B0579.pd 1 (V1.vC tr t i) x : ℂ))) := by
      intro i; funext x
      simp only [a_k, advStretch, Fin.sum_univ_two, V1.trainVel_fun tr ht.1.le]
      simp only [V1.trainVel_of_nonneg tr ht.1.le]
    have hak_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => a_k x i) := by
      intro i
      rw [hak_eq i]
      exact (((Complex.ofRealCLM.contDiff.comp (V1.vC_contDiff tr ht.1.le 0)).mul (hGk_sm k i 0)).add
        ((huk_sm k 0).mul (Complex.ofRealCLM.contDiff.comp (V1.pdv_contDiff tr ht.1.le i 0)))).add
        (((Complex.ofRealCLM.contDiff.comp (V1.vC_contDiff tr ht.1.le 1)).mul (hGk_sm k i 1)).add
          ((huk_sm k 1).mul (Complex.ofRealCLM.contDiff.comp (V1.pdv_contDiff tr ht.1.le i 1))))
    have hak_per : ∀ i : Fin 2, ∀ x : ℝ × ℝ, a_k (x.1 + c, x.2) i = a_k x i := by
      intro i x
      rw [congrFun (hak_eq i) (x.1 + c, x.2), congrFun (hak_eq i) x]
      have hv0_p : V1.vC tr t 0 (x.1 + c, x.2) = V1.vC tr t 0 x := V1.vC_periodic tr ht.1.le 0 x
      have hv1_p : V1.vC tr t 1 (x.1 + c, x.2) = V1.vC tr t 1 x := V1.vC_periodic tr ht.1.le 1 x
      have hpd0_p : B0579.pd 0 (V1.vC tr t i) (x.1 + c, x.2) = B0579.pd 0 (V1.vC tr t i) x :=
        V1.pdv_periodic tr ht.1.le i 0 x
      have hpd1_p : B0579.pd 1 (V1.vC tr t i) (x.1 + c, x.2) = B0579.pd 1 (V1.vC tr t i) x :=
        V1.pdv_periodic tr ht.1.le i 1 x
      rw [hv0_p, hv1_p, hpd0_p, hpd1_p, huk_per k x 0, huk_per k x 1,
        hGk_per k x i 0, hGk_per k x i 1]
    have hcurl_ak : ∀ x, -(pdC 0 (fun y => a_k y 1) x - pdC 1 (fun y => a_k y 0) x) = f_k k x :=
      nsrc_advStretch_curl_smooth tr ht.1 (huk_sm k) (hGk_eq_pd k) (hdiv_uk k) (hωk_eq k)
    obtain ⟨K_cut, hK_cut, hcut⟩ := ladCutProps
    set χ : ℕ → ℝ × ℝ → ℝ := fun n => ladCut ((n : ℝ) + 1)
    have hχ_test : ∀ n, B0579.IsCylTest c (χ n) := fun n => (hcut ((n : ℝ) + 1) (by positivity)).1 c
    have hχ_01 : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1 := fun n => (hcut ((n : ℝ) + 1) (by positivity)).2.1
    have hχ_pd : ∀ n x j, |B0579.pd j (χ n) x| ≤ K_cut / ((n : ℝ) + 1) :=
      fun n => (hcut ((n : ℝ) + 1) (by positivity)).2.2.2.2.1
    -- Cut identity at level `n`
    have hcut_id : ∀ n : ℕ,
        (∫ x in B0579.cell c, (f_k k x * φ x) * (χ n x : ℂ)) -
          (∫ x in B0579.cell c, φ x *
            (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))) =
        ∫ x in B0579.cell c, (a_k x 1 * g 0 x - a_k x 0 * g 1 x) * (χ n x : ℂ) := by
      intro n
      obtain ⟨I0a, I0b, eq0⟩ := nsrc_weak_ibp_complex (hg 0) (hak_sm 1) (hak_per 1) (hχ_test n)
      obtain ⟨I1a, I1b, eq1⟩ := nsrc_weak_ibp_complex (hg 1) (hak_sm 0) (hak_per 0) (hχ_test n)
      have Ifk_φ : IntegrableOn (fun x => (f_k k x * φ x) * (χ n x : ℂ)) (B0579.cell c) := by
        have Ifk := CoreDuhamelRepSub.integrableOn_mul_of_memLp_h1 (hfk_mem k) hg hh1
        refine Ifk.norm.mono' ?_ ?_
        · exact Ifk.aestronglyMeasurable.mul
            (Complex.continuous_ofReal.comp (hχ_test n).continuous).aestronglyMeasurable
        · filter_upwards with x
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ_01 n x).1]
          exact mul_le_of_le_one_right (norm_nonneg _) (hχ_01 n x).2
      have Icomm : IntegrableOn (fun x => φ x *
          (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ)))
          (B0579.cell c) := by
        have heq_c : (fun x => φ x *
              (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))) =
            fun x => (φ x * (pdC 0 (fun y => a_k y 1) x * (χ n x : ℂ) +
                a_k x 1 * (B0579.pd 0 (χ n) x : ℂ)) -
              φ x * (pdC 1 (fun y => a_k y 0) x * (χ n x : ℂ) +
                a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))) +
              (f_k k x * φ x) * (χ n x : ℂ) := by
          funext x; rw [← hcurl_ak x]; ring
        rw [heq_c]
        exact (I0a.sub I1a).add Ifk_φ
      have heqL : (fun x => (f_k k x * φ x) * (χ n x : ℂ) -
            φ x * (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))) =
          fun x => φ x * (pdC 1 (fun y => a_k y 0) x * (χ n x : ℂ) +
              a_k x 0 * (B0579.pd 1 (χ n) x : ℂ)) -
            φ x * (pdC 0 (fun y => a_k y 1) x * (χ n x : ℂ) +
              a_k x 1 * (B0579.pd 0 (χ n) x : ℂ)) := by
        funext x; rw [← hcurl_ak x]; ring
      have heqR : (fun x => (a_k x 1 * g 0 x - a_k x 0 * g 1 x) * (χ n x : ℂ)) =
          fun x => g 0 x * (a_k x 1 * (χ n x : ℂ)) - g 1 x * (a_k x 0 * (χ n x : ℂ)) := by
        funext x; ring
      rw [← integral_sub Ifk_φ Icomm, heqL, integral_sub I1a I0a, eq1, eq0,
        heqR, integral_sub I0b I1b]
      ring
    -- Pass `n → ∞`
    have Ifk_φ0 := CoreDuhamelRepSub.integrableOn_mul_of_memLp_h1 (hfk_mem k) hg hh1
    have hlim1 : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, (f_k k x * φ x) * (χ n x : ℂ))
        atTop (𝓝 (∫ x in B0579.cell c, f_k k x * φ x)) := by
      have h1 : (∫ x in B0579.cell c, f_k k x * φ x) =
          ∫ x in B0579.cell c, (f_k k x * φ x) * 1 := by simp
      rw [h1]
      refine tendsto_integral_of_dominated_convergence (fun x => ‖f_k k x * φ x‖) ?_ Ifk_φ0.norm ?_ ?_
      · intro n
        exact Ifk_φ0.aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp (hχ_test n).continuous).aestronglyMeasurable
      · intro n; filter_upwards with x
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ_01 n x).1]
        exact mul_le_of_le_one_right (norm_nonneg _) (hχ_01 n x).2
      · filter_upwards with x
        exact tendsto_const_nhds.mul (nsrc_ladCut_tendsto_one x)
    have Isrc_k : IntegrableOn (fun x => a_k x 1 * g 0 x - a_k x 0 * g 1 x) (B0579.cell c) :=
      CoreDuhamelRepSub.integrableOn_coreSrc_of_slice hc hAm hv1 hv_bd
        (fun i => (huk_sm k i).continuous.measurable)
        (fun i j => (hGk_sm k i j).continuous.measurable)
        (huk_lp k) (hGk_lp k) hg hh1
    have hlim2 : Tendsto (fun n : ℕ =>
        ∫ x in B0579.cell c, (a_k x 1 * g 0 x - a_k x 0 * g 1 x) * (χ n x : ℂ))
        atTop (𝓝 (coreSrcFun c a_k g)) := by
      unfold coreSrcFun
      have h1 : (∫ x in B0579.cell c, a_k x 1 * g 0 x - a_k x 0 * g 1 x) =
          ∫ x in B0579.cell c, (a_k x 1 * g 0 x - a_k x 0 * g 1 x) * 1 := by simp
      rw [h1]
      refine tendsto_integral_of_dominated_convergence
        (fun x => ‖a_k x 1 * g 0 x - a_k x 0 * g 1 x‖) ?_ Isrc_k.norm ?_ ?_
      · intro n
        exact Isrc_k.aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp (hχ_test n).continuous).aestronglyMeasurable
      · intro n; filter_upwards with x
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hχ_01 n x).1]
        exact mul_le_of_le_one_right (norm_nonneg _) (hχ_01 n x).2
      · filter_upwards with x
        exact tendsto_const_nhds.mul (nsrc_ladCut_tendsto_one x)
    -- Commutator in `n` vanishes: `‖φ x‖ * vnorm2 (a_k x)` is integrable on `cell c`
    have hint_φ_ak : Integrable (fun x => ‖φ x‖ * vnorm2 (a_k x))
        (volume.restrict (B0579.cell c)) := by
      have hφm : AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) :=
        CoreDuhamelRepSub.aestronglyMeasurable_val_of_hasWeakCellDerivC (hg 1)
      have hφ_w : MemLp (fun x => B0579.bracket x ^ (-9 : ℝ) * ‖φ x‖) 2
          (volume.restrict (B0579.cell c)) := by
        have hm : AEStronglyMeasurable (fun x => B0579.bracket x ^ (-9 : ℝ) * ‖φ x‖)
            (volume.restrict (B0579.cell c)) := by
          have heq : (fun x : ℝ × ℝ => B0579.bracket x ^ (-9 : ℝ) * ‖φ x‖) =
              fun x => B0579.jb x ^ (-9 / 2 : ℝ) * ‖φ x‖ :=
            funext fun x => by rw [B0579.bracket_rpow (-9) x]
          rw [heq]
          exact (B0579.continuous_jb_rpow (-9 / 2)).aestronglyMeasurable.mul hφm.norm
        refine ⟨hm, ?_⟩
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
        have heq_l : ∫⁻ x in B0579.cell c,
            ‖B0579.bracket x ^ (-9 : ℝ) * ‖φ x‖‖ₑ ^ ENNReal.toReal 2 =
            xNorm c (-9) φ ^ 2 := by
          rw [CoreDuhamelRepSub.xNorm_sq_eq]
          refine lintegral_congr fun x => ?_
          have h2 : ENNReal.toReal 2 = 2 := by norm_num
          have hnn : 0 ≤ B0579.bracket x ^ (-9 : ℝ) * ‖φ x‖ :=
            mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)
          have hbr_sq : (B0579.bracket x ^ (-9 : ℝ)) ^ 2 = B0579.jb x ^ (-9 : ℝ) := by
            rw [B0579.bracket_rpow (-9) x, ← Real.rpow_natCast _ 2,
              ← Real.rpow_mul (B0579.jb_pos x).le]
            norm_num
          rw [h2, ENNReal.rpow_two, ← ofReal_norm, Real.norm_of_nonneg hnn,
            ← ENNReal.ofReal_pow hnn, mul_pow, hbr_sq]
        rw [heq_l]
        have hxφ : xNorm c (-9) φ ≤ 1 := by
          have hsq : (xNorm c (-9) φ ^ 2) ^ (1 / 2 : ℝ) ≤ 1 :=
            (ENNReal.rpow_le_rpow le_self_add (by norm_num)).trans hh1
          rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul,
            show ((2 : ℕ) : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one] at hsq
          exact hsq
        exact (pow_le_pow_left₀ bot_le hxφ 2).trans_lt (by simp)
      have hak_w : MemLp (fun x => B0579.bracket x ^ (9 : ℝ) * vnorm2 (a_k x)) 2
          (volume.restrict (B0579.cell c)) := by
        have hm : AEStronglyMeasurable (fun x => B0579.bracket x ^ (9 : ℝ) * vnorm2 (a_k x))
            (volume.restrict (B0579.cell c)) := by
          have hm_br : Measurable fun x : ℝ × ℝ => B0579.bracket x ^ (9 : ℝ) :=
            ((B0579.continuous_jb.sqrt).rpow_const (fun _ => Or.inr (by norm_num))).measurable
          exact (hm_br.mul (causalLin_measurable_vnorm2 fun i =>
            (hak_sm i).continuous.measurable)).aestronglyMeasurable
        refine ⟨hm, ?_⟩
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
        have heq_l : ∫⁻ x in B0579.cell c,
            ‖B0579.bracket x ^ (9 : ℝ) * vnorm2 (a_k x)‖ₑ ^ ENNReal.toReal 2 =
            ∫⁻ x in B0579.cell c, ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (a_k x) ^ 2) := by
          refine lintegral_congr fun x => ?_
          have h2 : ENNReal.toReal 2 = 2 := by norm_num
          have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
          have hnn : 0 ≤ B0579.bracket x ^ (9 : ℝ) * vnorm2 (a_k x) :=
            mul_nonneg (Real.rpow_nonneg hbr_pos.le _) (vnorm2_nonneg _)
          have hbr18 : (B0579.bracket x ^ (9 : ℝ)) ^ 2 = B0579.bracket x ^ (18 : ℝ) := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hbr_pos.le]; norm_num
          rw [h2, ENNReal.rpow_two, ← ofReal_norm, Real.norm_of_nonneg hnn,
            ← ENNReal.ofReal_pow hnn, mul_pow, hbr18]
        rw [heq_l]
        have hbd_ak := advStretch_weighted_l2_bound hc hAm hv1 hv_bd
          (fun i => (huk_sm k i).continuous.measurable)
          (fun i j => (hGk_sm k i j).continuous.measurable)
        have hlt_half : (∫⁻ x in B0579.cell c,
            ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (a_k x) ^ 2)) ^ (1 / 2 : ℝ) < ⊤ := by
          refine hbd_ak.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
              (CoreDuhamelRepSub.lintegral_vnorm2_sq_lt_top (huk_lp k)).ne
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
              (CoreDuhamelRepSub.lintegral_tnorm2_sq_lt_top (hGk_lp k)).ne
        have hsq_top : ((∫⁻ x in B0579.cell c,
            ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (a_k x) ^ 2)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) < ⊤ :=
          ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt_half.ne
        rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at hsq_top
        exact hsq_top
      refine (hφ_w.integrable_mul hak_w).congr (Eventually.of_forall fun x => ?_)
      dsimp only
      have hbr_pos : 0 < B0579.bracket x := Real.sqrt_pos.2 (B0579.jb_pos x)
      have hmul1 : B0579.bracket x ^ (-9 : ℝ) * B0579.bracket x ^ (9 : ℝ) = 1 := by
        rw [← Real.rpow_add hbr_pos]; norm_num
      calc (B0579.bracket x ^ (-9 : ℝ) * ‖φ x‖) * (B0579.bracket x ^ (9 : ℝ) * vnorm2 (a_k x))
          = (B0579.bracket x ^ (-9 : ℝ) * B0579.bracket x ^ (9 : ℝ)) * (‖φ x‖ * vnorm2 (a_k x)) := by ring
        _ = ‖φ x‖ * vnorm2 (a_k x) := by rw [hmul1, one_mul]
    have hlim_comm : Tendsto (fun n : ℕ => ∫ x in B0579.cell c, φ x *
        (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ)))
        atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hinv0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have hinv : Tendsto (fun n : ℕ =>
          (2 * K_cut * ∫ x in B0579.cell c, ‖φ x‖ * vnorm2 (a_k x)) * ((n : ℝ) + 1)⁻¹)
          atTop (𝓝 0) := by
        simpa using hinv0.const_mul (2 * K_cut * ∫ x in B0579.cell c, ‖φ x‖ * vnorm2 (a_k x))
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hinv
      rw [sub_zero]
      have hpt_bd : ∀ x, ‖φ x * (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) -
            a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))‖ ≤
          (2 * K_cut / ((n : ℝ) + 1)) * (‖φ x‖ * vnorm2 (a_k x)) := by
        intro x
        have ha0_le : ‖a_k x 0‖ ≤ vnorm2 (a_k x) := by
          unfold vnorm2
          refine Real.le_sqrt_of_sq_le ?_
          rw [Fin.sum_univ_two]; linarith [sq_nonneg ‖a_k x 1‖]
        have ha1_le : ‖a_k x 1‖ ≤ vnorm2 (a_k x) := by
          unfold vnorm2
          refine Real.le_sqrt_of_sq_le ?_
          rw [Fin.sum_univ_two]; linarith [sq_nonneg ‖a_k x 0‖]
        rw [norm_mul]
        have hsub_le : ‖a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ)‖ ≤
            (2 * K_cut / ((n : ℝ) + 1)) * vnorm2 (a_k x) := by
          calc ‖a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ)‖
              ≤ ‖a_k x 1‖ * |B0579.pd 0 (χ n) x| + ‖a_k x 0‖ * |B0579.pd 1 (χ n) x| := by
                refine (norm_sub_le _ _).trans ?_
                simp [Complex.norm_real, Real.norm_eq_abs]
            _ ≤ vnorm2 (a_k x) * (K_cut / ((n : ℝ) + 1)) +
                  vnorm2 (a_k x) * (K_cut / ((n : ℝ) + 1)) :=
                add_le_add (mul_le_mul ha1_le (hχ_pd n x 0) (abs_nonneg _) (vnorm2_nonneg _))
                  (mul_le_mul ha0_le (hχ_pd n x 1) (abs_nonneg _) (vnorm2_nonneg _))
            _ = (2 * K_cut / ((n : ℝ) + 1)) * vnorm2 (a_k x) := by ring
        calc ‖φ x‖ * ‖a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ)‖
            ≤ ‖φ x‖ * ((2 * K_cut / ((n : ℝ) + 1)) * vnorm2 (a_k x)) :=
              mul_le_mul_of_nonneg_left hsub_le (norm_nonneg _)
          _ = (2 * K_cut / ((n : ℝ) + 1)) * (‖φ x‖ * vnorm2 (a_k x)) := by ring
      have hφm : AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) :=
        CoreDuhamelRepSub.aestronglyMeasurable_val_of_hasWeakCellDerivC (hg 1)
      calc ‖∫ x in B0579.cell c, φ x *
              (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))‖
          ≤ ∫ x in B0579.cell c, ‖φ x *
              (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in B0579.cell c, (2 * K_cut / ((n : ℝ) + 1)) * (‖φ x‖ * vnorm2 (a_k x)) := by
            refine setIntegral_mono_on ?_ (hint_φ_ak.const_mul _)
              (B0579.measurableSet_cell c) fun x _ => hpt_bd x
            refine (hint_φ_ak.const_mul (2 * K_cut / ((n : ℝ) + 1))).mono' ?_ ?_
            · exact (hφm.mul (((hak_sm 1).continuous.aestronglyMeasurable.mul
                (Complex.continuous_ofReal.comp (hχ_test n |>.pd 0).continuous).aestronglyMeasurable).sub
                ((hak_sm 0).continuous.aestronglyMeasurable.mul
                  (Complex.continuous_ofReal.comp (hχ_test n |>.pd 1).continuous).aestronglyMeasurable))).norm
            · filter_upwards with x
              rw [Real.norm_of_nonneg (norm_nonneg _)]
              exact hpt_bd x
        _ = (2 * K_cut * ∫ x in B0579.cell c, ‖φ x‖ * vnorm2 (a_k x)) * ((n : ℝ) + 1)⁻¹ := by
            rw [integral_const_mul]; ring
    have hlim_sub : Tendsto (fun n : ℕ =>
        (∫ x in B0579.cell c, (f_k k x * φ x) * (χ n x : ℂ)) -
          (∫ x in B0579.cell c, φ x *
            (a_k x 1 * (B0579.pd 0 (χ n) x : ℂ) - a_k x 0 * (B0579.pd 1 (χ n) x : ℂ))))
        atTop (𝓝 (∫ x in B0579.cell c, f_k k x * φ x)) := by
      simpa using hlim1.sub hlim_comm
    exact tendsto_nhds_unique hlim_sub (by simpa [hcut_id] using hlim2)
  -- Step B: Pass `k → ∞` via `lmJs_tendsto`
  have hel2_u : ∀ i : Fin 2, Tendsto (fun k : ℕ =>
      eLpNorm (fun x => u_k k x i - u₀ x i) 2 (volume.restrict (B0579.cell c)))
      atTop (𝓝 0) := by
    intro i
    have hsq := lmJs_tendsto hc (hu₀_lp i)
    have h_enn : Tendsto (fun k : ℕ => (ENNReal.ofReal (∫ x in B0579.cell c,
        ‖lmJs c k (fun y => u₀ y i) x - u₀ x i‖ ^ 2)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = (ENNReal.ofReal 0) ^ (1 / 2 : ℝ) := by simp
      rw [h0]
      exact ((ENNReal.continuous_ofReal.tendsto 0).comp hsq).ennrpow_const (1 / 2)
    refine h_enn.congr fun k => ?_
    have hint_sq : Integrable
        (fun x => ‖lmJs c k (fun y => u₀ y i) x - u₀ x i‖ ^ 2)
        (volume.restrict (B0579.cell c)) := (((huk_lp k i).sub (hu₀_lp i)).norm).integrable_sq
    change (ENNReal.ofReal (∫ x in B0579.cell c,
        ‖lmJs c k (fun y => u₀ y i) x - u₀ x i‖ ^ 2)) ^ (1 / 2 : ℝ) =
      eLpNorm (fun x => lmJs c k (fun y => u₀ y i) x - u₀ x i) 2 (volume.restrict (B0579.cell c))
    rw [ofReal_integral_eq_lintegral_ofReal hint_sq
      (ae_of_all _ fun _ => sq_nonneg _), ← nsrc_eLpNorm_two_sq,
      ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have hel2_G : ∀ i j : Fin 2, Tendsto (fun k : ℕ =>
      eLpNorm (fun x => G_k k x i j - Gt₀ x i j) 2 (volume.restrict (B0579.cell c)))
      atTop (𝓝 0) := by
    intro i j
    have hsq := lmJs_tendsto hc (hGt₀_lp i j)
    have h_enn : Tendsto (fun k : ℕ => (ENNReal.ofReal (∫ x in B0579.cell c,
        ‖lmJs c k (fun y => Gt₀ y i j) x - Gt₀ x i j‖ ^ 2)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = (ENNReal.ofReal 0) ^ (1 / 2 : ℝ) := by simp
      rw [h0]
      exact ((ENNReal.continuous_ofReal.tendsto 0).comp hsq).ennrpow_const (1 / 2)
    refine h_enn.congr fun k => ?_
    have hint_sq : Integrable
        (fun x => ‖lmJs c k (fun y => Gt₀ y i j) x - Gt₀ x i j‖ ^ 2)
        (volume.restrict (B0579.cell c)) := (((hGk_lp k i j).sub (hGt₀_lp i j)).norm).integrable_sq
    change (ENNReal.ofReal (∫ x in B0579.cell c,
        ‖lmJs c k (fun y => Gt₀ y i j) x - Gt₀ x i j‖ ^ 2)) ^ (1 / 2 : ℝ) =
      eLpNorm (fun x => lmJs c k (fun y => Gt₀ y i j) x - Gt₀ x i j) 2
        (volume.restrict (B0579.cell c))
    rw [ofReal_integral_eq_lintegral_ofReal hint_sq
      (ae_of_all _ fun _ => sq_nonneg _), ← nsrc_eLpNorm_two_sq,
      ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have hel2_pdω : ∀ j : Fin 2, Tendsto (fun k : ℕ =>
      eLpNorm (fun x => pdC j (ω_k k) x - pdC j ω₀ x) 2 (volume.restrict (B0579.cell c)))
      atTop (𝓝 0) := by
    intro j
    have hsq := lmJs_tendsto hc (hpdω₀_lp j)
    have h_enn : Tendsto (fun k : ℕ => (ENNReal.ofReal (∫ x in B0579.cell c,
        ‖lmJs c k (pdC j ω₀) x - pdC j ω₀ x‖ ^ 2)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = (ENNReal.ofReal 0) ^ (1 / 2 : ℝ) := by simp
      rw [h0]
      exact ((ENNReal.continuous_ofReal.tendsto 0).comp hsq).ennrpow_const (1 / 2)
    refine h_enn.congr fun k => ?_
    have heq_k : (fun x => pdC j (ω_k k) x - pdC j ω₀ x) =
        fun x => lmJs c k (pdC j ω₀) x - pdC j ω₀ x :=
      funext fun x => by rw [hpd_ωk_eq k j x]
    have hint_sq : Integrable
        (fun x => ‖lmJs c k (pdC j ω₀) x - pdC j ω₀ x‖ ^ 2)
        (volume.restrict (B0579.cell c)) :=
      (((lmJs_memLp hc k (hpdω₀_lp j)).sub (hpdω₀_lp j)).norm).integrable_sq
    rw [heq_k, ofReal_integral_eq_lintegral_ofReal hint_sq
      (ae_of_all _ fun _ => sq_nonneg _), ← nsrc_eLpNorm_two_sq,
      ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  -- Left limit as `k → ∞`: `∫ f_k * φ → ∫ f_t * φ`
  have hfk_tendsto : Tendsto (fun k : ℕ => xNorm c 9 (fun x => f_k k x - f_t x)) atTop (𝓝 0) := by
    have hv0_m : AEStronglyMeasurable (fun x => (trainVel tr t x 0 : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp ((continuous_apply 0).comp hv1.continuous)).aestronglyMeasurable
    have hv1_m : AEStronglyMeasurable (fun x => (trainVel tr t x 1 : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp ((continuous_apply 1).comp hv1.continuous)).aestronglyMeasurable
    have hE0_m : AEStronglyMeasurable (fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr ht.1.le 0).continuous).aestronglyMeasurable
    have hE1_m : AEStronglyMeasurable (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ))
        (volume.restrict (B0579.cell c)) :=
      (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr ht.1.le 1).continuous).aestronglyMeasurable
    have hsum_lim : Tendsto (fun k : ℕ =>
        (ENNReal.ofReal A_m * eLpNorm (fun x => pdC 0 (ω_k k) x - pdC 0 ω₀ x) 2
            (volume.restrict (B0579.cell c)) +
          ENNReal.ofReal A_m * eLpNorm (fun x => pdC 1 (ω_k k) x - pdC 1 ω₀ x) 2
            (volume.restrict (B0579.cell c))) +
        (ENNReal.ofReal (max C_tr 0) * eLpNorm (fun x => u_k k x 0 - u₀ x 0) 2
            (volume.restrict (B0579.cell c)) +
          ENNReal.ofReal (max C_tr 0) * eLpNorm (fun x => u_k k x 1 - u₀ x 1) 2
            (volume.restrict (B0579.cell c)))) atTop (𝓝 0) := by
      have l1 : Tendsto (fun k => ENNReal.ofReal A_m *
          eLpNorm (fun x => pdC 0 (ω_k k) x - pdC 0 ω₀ x) 2 (volume.restrict (B0579.cell c)))
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (hel2_pdω 0) (Or.inr ENNReal.ofReal_ne_top)
      have l2 : Tendsto (fun k => ENNReal.ofReal A_m *
          eLpNorm (fun x => pdC 1 (ω_k k) x - pdC 1 ω₀ x) 2 (volume.restrict (B0579.cell c)))
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (hel2_pdω 1) (Or.inr ENNReal.ofReal_ne_top)
      have l3 : Tendsto (fun k => ENNReal.ofReal (max C_tr 0) *
          eLpNorm (fun x => u_k k x 0 - u₀ x 0) 2 (volume.restrict (B0579.cell c)))
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (hel2_u 0) (Or.inr ENNReal.ofReal_ne_top)
      have l4 : Tendsto (fun k => ENNReal.ofReal (max C_tr 0) *
          eLpNorm (fun x => u_k k x 1 - u₀ x 1) 2 (volume.restrict (B0579.cell c)))
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (hel2_u 1) (Or.inr ENNReal.ofReal_ne_top)
      simpa using (l1.add l2).add (l3.add l4)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_lim
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun k => ?_)
    have m1 := nsrc_memLp_xNorm_mul hAm hv0_m (nsrc_trainVel_bdd hbd ht 0)
      ((hpd_ωk_lp k 0).sub (hpdω₀_lp 0))
    have m2 := nsrc_memLp_xNorm_mul hAm hv1_m (nsrc_trainVel_bdd hbd ht 1)
      ((hpd_ωk_lp k 1).sub (hpdω₀_lp 1))
    have m3 := nsrc_memLp_xNorm_mul (le_max_right C_tr 0) hE0_m
      (nsrc_pdEc_bdd hLad ⟨ht.1.le, ht.2⟩ 0) ((huk_lp k 0).sub (hu₀_lp 0))
    have m4 := nsrc_memLp_xNorm_mul (le_max_right C_tr 0) hE1_m
      (nsrc_pdEc_bdd hLad ⟨ht.1.le, ht.2⟩ 1) ((huk_lp k 1).sub (hu₀_lp 1))
    have heq : (fun x => f_k k x - f_t x) = -(((fun x => (trainVel tr t x 0 : ℂ) *
          (pdC 0 (ω_k k) x - pdC 0 ω₀ x)) +
        (fun x => (trainVel tr t x 1 : ℂ) * (pdC 1 (ω_k k) x - pdC 1 ω₀ x))) +
      ((fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * (u_k k x 0 - u₀ x 0)) +
        (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * (u_k k x 1 - u₀ x 1)))) := by
      funext x; dsimp [f_k]; rw [hf_def x]; ring
    unfold xNorm
    rw [heq, eLpNorm_neg]
    exact (eLpNorm_add_le (m1.1.1.add m2.1.1) (m3.1.1.add m4.1.1) one_le_two).trans
      (add_le_add
        ((eLpNorm_add_le m1.1.1 m2.1.1 one_le_two).trans (add_le_add m1.2 m2.2))
        ((eLpNorm_add_le m3.1.1 m4.1.1 one_le_two).trans (add_le_add m3.2 m4.2)))
  have hLHS_lim : Tendsto (fun k : ℕ => ∫ x in B0579.cell c, f_k k x * φ x)
      atTop (𝓝 (∫ x in B0579.cell c, f_t x * φ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have htoR : Tendsto (fun k : ℕ => (xNorm c 9 (fun x => f_k k x - f_t x)).toReal)
        atTop (𝓝 0) :=
      ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp hfk_tendsto
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) htoR
    have Ifk := CoreDuhamelRepSub.integrableOn_mul_of_memLp_h1 (hfk_mem k) hg hh1
    have Ift := CoreDuhamelRepSub.integrableOn_mul_of_memLp_h1 hf_mem hg hh1
    have hsub_eq : (∫ x in B0579.cell c, f_k k x * φ x) - (∫ x in B0579.cell c, f_t x * φ x) =
        ∫ x in B0579.cell c, (f_k k x - f_t x) * φ x := by
      rw [← integral_sub Ifk Ift]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hsub_eq]
    have hdiff_mem : MemLp (fun x => f_k k x - f_t x) 2 (B0579.cellMeasure c 9) :=
      (hfk_mem k).sub hf_mem
    have hbd_enn := nsrc_pairing_norm_le hdiff_mem hg hh1
    have htr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hdiff_mem.2.ne).2 hbd_enn
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at htr
  -- Right limit as `k → ∞`: `coreSrcFun c (advStretch v (u_k k) (G_k k)) g → coreSrcFun c (advStretch v u₀ Gt₀) g`
  have hRHS_lim : Tendsto (fun k : ℕ =>
      coreSrcFun c (advStretch (trainVel tr t) (u_k k) (G_k k)) g)
      atTop (𝓝 (coreSrcFun c (advStretch (trainVel tr t) u₀ Gt₀) g)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsum_uG : Tendsto (fun k : ℕ => ENNReal.ofReal (8 * A_m) *
        ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u_k k x i - u₀ x i) ^ 2)) ^ (1 / 2 : ℝ) +
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (fun i j => G_k k x i j - Gt₀ x i j) ^ 2)) ^ (1 / 2 : ℝ)))
        atTop (𝓝 0) := by
      have hu_part : Tendsto (fun k : ℕ =>
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u_k k x i - u₀ x i) ^ 2)) ^ (1 / 2 : ℝ))
          atTop (𝓝 0) := by
        have h0 : Tendsto (fun k : ℕ =>
            (eLpNorm (fun x => u_k k x 0 - u₀ x 0) 2 (volume.restrict (B0579.cell c)) ^ 2 +
              eLpNorm (fun x => u_k k x 1 - u₀ x 1) 2 (volume.restrict (B0579.cell c)) ^ 2) ^ (1 / 2 : ℝ))
            atTop (𝓝 0) := by
          have p0 : Tendsto (fun k => eLpNorm (fun x => u_k k x 0 - u₀ x 0) 2
              (volume.restrict (B0579.cell c)) ^ 2) atTop (𝓝 0) := by
            simpa [ENNReal.rpow_two] using (hel2_u 0).ennrpow_const 2
          have p1 : Tendsto (fun k => eLpNorm (fun x => u_k k x 1 - u₀ x 1) 2
              (volume.restrict (B0579.cell c)) ^ 2) atTop (𝓝 0) := by
            simpa [ENNReal.rpow_two] using (hel2_u 1).ennrpow_const 2
          simpa using (p0.add p1).ennrpow_const (1 / 2)
        refine h0.congr fun k => ?_
        congr 1
        have hm0 : AEMeasurable (fun x => ENNReal.ofReal (‖u_k k x 0 - u₀ x 0‖ ^ 2))
            (volume.restrict (B0579.cell c)) :=
          (((huk_lp k 0).sub (hu₀_lp 0)).1.norm.aemeasurable.pow_const 2).ennreal_ofReal
        rw [nsrc_eLpNorm_two_sq, nsrc_eLpNorm_two_sq, ← lintegral_add_left' hm0]
        refine lintegral_congr fun x => ?_
        rw [causalLin_vnorm2_sq, Fin.sum_univ_two, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      have hG_part : Tendsto (fun k : ℕ =>
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (fun i j => G_k k x i j - Gt₀ x i j) ^ 2)) ^ (1 / 2 : ℝ))
          atTop (𝓝 0) := by
        have h0 : Tendsto (fun k : ℕ =>
            ((eLpNorm (fun x => G_k k x 0 0 - Gt₀ x 0 0) 2 (volume.restrict (B0579.cell c)) ^ 2 +
                eLpNorm (fun x => G_k k x 0 1 - Gt₀ x 0 1) 2 (volume.restrict (B0579.cell c)) ^ 2) +
              (eLpNorm (fun x => G_k k x 1 0 - Gt₀ x 1 0) 2 (volume.restrict (B0579.cell c)) ^ 2 +
                eLpNorm (fun x => G_k k x 1 1 - Gt₀ x 1 1) 2 (volume.restrict (B0579.cell c)) ^ 2)) ^ (1 / 2 : ℝ))
            atTop (𝓝 0) := by
          have p00 : Tendsto (fun k => eLpNorm (fun x => G_k k x 0 0 - Gt₀ x 0 0) 2
              (volume.restrict (B0579.cell c)) ^ 2) atTop (𝓝 0) := by
            simpa [ENNReal.rpow_two] using (hel2_G 0 0).ennrpow_const 2
          have p01 : Tendsto (fun k => eLpNorm (fun x => G_k k x 0 1 - Gt₀ x 0 1) 2
              (volume.restrict (B0579.cell c)) ^ 2) atTop (𝓝 0) := by
            simpa [ENNReal.rpow_two] using (hel2_G 0 1).ennrpow_const 2
          have p10 : Tendsto (fun k => eLpNorm (fun x => G_k k x 1 0 - Gt₀ x 1 0) 2
              (volume.restrict (B0579.cell c)) ^ 2) atTop (𝓝 0) := by
            simpa [ENNReal.rpow_two] using (hel2_G 1 0).ennrpow_const 2
          have p11 : Tendsto (fun k => eLpNorm (fun x => G_k k x 1 1 - Gt₀ x 1 1) 2
              (volume.restrict (B0579.cell c)) ^ 2) atTop (𝓝 0) := by
            simpa [ENNReal.rpow_two] using (hel2_G 1 1).ennrpow_const 2
          simpa using ((p00.add p01).add (p10.add p11)).ennrpow_const (1 / 2)
        refine h0.congr fun k => ?_
        congr 1
        have hm : ∀ i j, AEMeasurable (fun x => ENNReal.ofReal (‖G_k k x i j - Gt₀ x i j‖ ^ 2))
            (volume.restrict (B0579.cell c)) :=
          fun i j => (((hGk_lp k i j).sub (hGt₀_lp i j)).1.norm.aemeasurable.pow_const 2).ennreal_ofReal
        have hm01 : AEMeasurable (fun a => ENNReal.ofReal (‖G_k k a 0 0 - Gt₀ a 0 0‖ ^ 2) +
            ENNReal.ofReal (‖G_k k a 0 1 - Gt₀ a 0 1‖ ^ 2))
            (volume.restrict (B0579.cell c)) := (hm 0 0).add (hm 0 1)
        simp only [nsrc_eLpNorm_two_sq]
        rw [← lintegral_add_left' (hm 0 0), ← lintegral_add_left' (hm 1 0),
          ← lintegral_add_left' hm01]
        refine lintegral_congr fun x => ?_
        rw [causalLin_tnorm2_sq, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
          ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (add_nonneg (sq_nonneg _) (sq_nonneg _)),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      have h0_rhs : (0 : ℝ≥0∞) = ENNReal.ofReal (8 * A_m) * (0 + 0) := by simp
      rw [h0_rhs]
      exact ENNReal.Tendsto.const_mul (hu_part.add hG_part) (Or.inr ENNReal.ofReal_ne_top)
    have htoR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsum_uG
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) htoR
    have Ik := CoreDuhamelRepSub.integrableOn_coreSrc_of_slice hc hAm hv1 hv_bd
      (fun i => (huk_sm k i).continuous.measurable)
      (fun i j => (hGk_sm k i j).continuous.measurable) (huk_lp k) (hGk_lp k) hg hh1
    have I0 := CoreDuhamelRepSub.integrableOn_coreSrc_of_slice hc hAm hv1 hv_bd
      hu₀_m hGt₀_m hu₀_lp hGt₀_lp hg hh1
    have hsub_src : coreSrcFun c (advStretch (trainVel tr t) (u_k k) (G_k k)) g -
        coreSrcFun c (advStretch (trainVel tr t) u₀ Gt₀) g =
        coreSrcFun c (advStretch (trainVel tr t)
          (fun x i => u_k k x i - u₀ x i) (fun x i j => G_k k x i j - Gt₀ x i j)) g := by
      unfold coreSrcFun
      rw [← integral_sub Ik I0]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [advStretch, Fin.sum_univ_two]
      ring
    rw [hsub_src]
    have hdu_m : ∀ i, Measurable fun x => u_k k x i - u₀ x i :=
      fun i => (huk_sm k i).continuous.measurable.sub (hu₀_m i)
    have hdG_m : ∀ i j, Measurable fun x => G_k k x i j - Gt₀ x i j :=
      fun i j => (hGk_sm k i j).continuous.measurable.sub (hGt₀_m i j)
    have h1 := advStretch_weighted_l2_bound hc hAm hv1 hv_bd hdu_m hdG_m
    have hsrc_bd := coreSrcNorm_le_aux hc hAm hv1 hdu_m hdG_m h1
    have hle_sup : ENNReal.ofReal ‖coreSrcFun c (advStretch (trainVel tr t)
          (fun x i => u_k k x i - u₀ x i) (fun x i j => G_k k x i j - Gt₀ x i j)) g‖ ≤
        coreSrcNorm c 9 (advStretch (trainVel tr t)
          (fun x i => u_k k x i - u₀ x i) (fun x i j => G_k k x i j - Gt₀ x i j)) := by
      unfold coreSrcNorm
      exact le_iSup₂_of_le φ g (le_iSup₂_of_le hg hh1 le_rfl)
    have hfin_rhs : ENNReal.ofReal (8 * A_m) *
        ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u_k k x i - u₀ x i) ^ 2)) ^ (1 / 2 : ℝ) +
          (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (fun i j => G_k k x i j - Gt₀ x i j) ^ 2)) ^ (1 / 2 : ℝ)) < ⊤ := by
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (CoreDuhamelRepSub.lintegral_vnorm2_sq_lt_top fun i => (huk_lp k i).sub (hu₀_lp i)).ne
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
          (CoreDuhamelRepSub.lintegral_tnorm2_sq_lt_top fun i j => (hGk_lp k i j).sub (hGt₀_lp i j)).ne
    have htot := hle_sup.trans hsrc_bd
    have htr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin_rhs.ne).2 htot
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at htr
  exact tendsto_nhds_unique hLHS_lim (by simpa only [hpair_k] using hRHS_lim)

private theorem nsrc_ae_slices_of_calNorm_zero {c H : ℝ} (hc : 0 < c)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hu_m : ∀ i, Measurable fun p => u p i)
    (hG_m : ∀ i j, Measurable fun p => G p i j)
    (hh : hCalNormOn c H u = 0) (ht : tCalNormOn c H G = 0) :
    ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) H →
      (∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i, u (s, x) i = 0) ∧
      (∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i j, G (s, x) i j = 0) := by
  have hm_u : Measurable fun p : ℝ × (ℝ × ℝ) => vnorm2 (u p) ^ 2 :=
    (causalLin_measurable_vnorm2 hu_m).pow_const 2
  have hm_G : Measurable fun p : ℝ × (ℝ × ℝ) => tnorm2 (G p) ^ 2 :=
    (causalLin_measurable_tnorm2 hG_m).pow_const 2
  have hl_u : ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
      (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u (s, x)) ^ 2)) = 0 := by
    rw [← lintegral_Iio_ageμ_eq hc _ hm_u,
      ← eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => vnorm2 (u p)) (fun _ => vnorm2_nonneg _)]
    change hCalNormOn c H u ^ 2 = 0
    rw [hh]; simp
  have hl_G : ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
      (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G (s, x)) ^ 2)) = 0 := by
    rw [← lintegral_Iio_ageμ_eq hc _ hm_G,
      ← eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => tnorm2 (G p)) (fun _ => tnorm2_nonneg _)]
    change tCalNormOn c H G ^ 2 = 0
    rw [ht]; simp
  have hmeas_int_u : AEMeasurable
      (fun s : ℝ => ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u (s, x)) ^ 2)))
      (volume.restrict (Ioo (0 : ℝ) H)) :=
    ((measurable_id.pow_const (-3 / 2)).ennreal_ofReal.mul
      (measurable_const.mul (hm_u.ennreal_ofReal.lintegral_prod_right'))).aemeasurable
  have hmeas_int_G : AEMeasurable
      (fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        (ENNReal.ofReal c⁻¹ * ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G (s, x)) ^ 2)))
      (volume.restrict (Ioo (0 : ℝ) H)) :=
    ((measurable_id.pow_const (-1 / 2)).ennreal_ofReal.mul
      (measurable_const.mul (hm_G.ennreal_ofReal.lintegral_prod_right'))).aemeasurable
  have hae_u := (ae_restrict_iff' measurableSet_Ioo).1
    ((lintegral_eq_zero_iff' hmeas_int_u).1 hl_u)
  have hae_G := (ae_restrict_iff' measurableSet_Ioo).1
    ((lintegral_eq_zero_iff' hmeas_int_G).1 hl_G)
  filter_upwards [hae_u, hae_G] with s hsu hsG hs
  have hs1 : ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs.1 _)).ne'
  have hs2 : ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs.1 _)).ne'
  have hc_ne : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have hu_int0 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u (s, x)) ^ 2) = 0 := by
    have h := hsu hs
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd h0 hs1
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 hc_ne
      · exact h1
  have hG_int0 : ∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G (s, x)) ^ 2) = 0 := by
    have h := hsG hs
    rcases mul_eq_zero.1 h with h0 | h0
    · exact absurd h0 hs2
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 hc_ne
      · exact h1
  have hu_x := (lintegral_eq_zero_iff (hm_u.comp measurable_prodMk_left).ennreal_ofReal).1 hu_int0
  have hG_x := (lintegral_eq_zero_iff (hm_G.comp measurable_prodMk_left).ennreal_ofReal).1 hG_int0
  refine ⟨?_, ?_⟩
  · filter_upwards [hu_x] with x hx i
    have h0 : vnorm2 (u (s, x)) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hx
    have hi0 : ‖u (s, x) i‖ ^ 2 ≤ 0 := by
      have h1 : ‖u (s, x) i‖ ^ 2 ≤ vnorm2 (u (s, x)) ^ 2 := by
        rw [causalLin_vnorm2_sq]
        exact Finset.single_le_sum (f := fun k => ‖u (s, x) k‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      exact h1.trans h0
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 (le_antisymm hi0 (sq_nonneg _)))
  · filter_upwards [hG_x] with x hx i j
    have h0 : tnorm2 (G (s, x)) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hx
    have hij0 : ‖G (s, x) i j‖ ^ 2 ≤ 0 := by
      have h1 : ‖G (s, x) i j‖ ^ 2 ≤ tnorm2 (G (s, x)) ^ 2 := by
        rw [causalLin_tnorm2_sq]
        refine le_trans (Finset.single_le_sum (f := fun l => ‖G (s, x) i l‖ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j)) ?_
        exact Finset.single_le_sum (f := fun k => ∑ l : Fin 2, ‖G (s, x) k l‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      exact h1.trans h0
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 (le_antisymm hij0 (sq_nonneg _)))

/-! ## 6. Target theorem `niceSourceConstruct` -/

theorem niceSourceConstruct
    (P : PlanarData) (hP : IsPlanarReference P)
    (K : Set ℂ) (hK : IsAdmissibleK K)
    (b : ℝ) (hb : 1 ≤ b) :
    ∃ ν_src : ℝ, 0 < ν_src ∧
      ∀ ν ∈ Ioc 0 ν_src,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          ∀ μ : ℂ, ∀ A_m : ℝ,
            ∀ F b₀ G₀ b_sol G_sol,
              NiceForce (ν ^ (-2 : ℝ)) F →
              VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
              ∃ (b_cl : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
                (G_cl : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
                (f : ℝ → ℝ × ℝ → ℂ)
                (a_zero M_f : ℝ),
                0 < a_zero ∧ 0 ≤ M_f ∧
                IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b_cl G_cl ∧
                (∀ s ≤ a_zero, ∀ x i, b_cl (s, x) i = 0) ∧
                (∀ s ≤ a_zero, ∀ x i j, G_cl (s, x) i j = 0) ∧
                (∀ t ≤ a_zero, ∀ x, f t x = 0) ∧
                hCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b)
                  (gainConj P.eigenvalue.re ν (fun p i => b₀ p i - b_cl p i)) = 0 ∧
                tCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b)
                  (gainConj P.eigenvalue.re ν (fun p i j => G₀ p i j - G_cl p i j)) = 0 ∧
                (∀ t ∈ Ioc (0 : ℝ) (coreEnd ν b),
                  (∀ i, MemLp (fun x => b_cl (t, x) i) 2
                    (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
                  (∀ i j, MemLp (fun x => G_cl (t, x) i j) 2
                    (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) ∧
                  MemLp (f t) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
                  HasZeroCirculation (ν ^ (-2 : ℝ)) (f t) ∧
                  xNorm (ν ^ (-2 : ℝ)) 9 (f t) ≤ ENNReal.ofReal M_f ∧
                  ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
                    (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
                    h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
                    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f t x * φ x =
                      coreSrcFun (ν ^ (-2 : ℝ))
                        (advStretch (trainVel tr t)
                          (fun x => gainConj P.eigenvalue.re ν b_cl (t, x))
                          (fun x => gainConj P.eigenvalue.re ν G_cl (t, x))) g) ∧
                (∀ t ∈ Ioo (0 : ℝ) (coreEnd ν b),
                  Tendsto (fun t' => xNorm (ν ^ (-2 : ℝ)) 9 (f t' - f t)) (𝓝 t) (𝓝 0)) ∧
                (∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) (coreEnd ν b) →
                  ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
                    (∀ j, HasWeakCellDerivC (ν ^ (-2 : ℝ)) j φ (g j)) →
                    h1Norm (ν ^ (-2 : ℝ)) 9 φ g ≤ 1 →
                    ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f t x * φ x =
                      coreSrcFun (ν ^ (-2 : ℝ))
                        (coreAdvSlice P.eigenvalue.re tr b₀ G₀ t) g) := by
  obtain ⟨ν_eb, hν_eb, hEB⟩ := freeCausalEnergyBound P hP K hK
  obtain ⟨ν_lad, hν_lad, hLad_all⟩ := CutFTCDual.ladTrainBddAll_unconditional 7
  have hb_pos : 0 < 2 * b := by linarith
  set ν_src : ℝ := min (1 / 2) (min ((2 * b)⁻¹) (min ν_eb ν_lad))
  have hν_src : 0 < ν_src :=
    lt_min (by norm_num) (lt_min (inv_pos.2 hb_pos) (lt_min hν_eb hν_lad))
  refine ⟨ν_src, hν_src, fun ν hν tr μ A_m F b₀ G₀ b_sol G_sol hF hd => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_half : ν ≤ 1 / 2 := hν.2.trans (min_le_left _ _)
  have hνb : ν ≤ (2 * b)⁻¹ := (hν.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hν_eb' : ν ∈ Ioc 0 ν_eb :=
    ⟨hν0, ((hν.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)⟩
  have hν_lad' : ν ∈ Ioc 0 ν_lad :=
    ⟨hν0, ((hν.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  let H : ℝ := coreEnd ν b
  have hH_gt : 1 < H := (coreEnd_bounds hb hν0 hν_half hνb).1
  have hH_pos : 0 < H := by linarith
  let γ : ℝ := P.eigenvalue.re
  obtain ⟨htr_buc, hμK, hAm, hbd, _, _, _, hb0_sol, _⟩ := hd
  obtain ⟨C_tr, hLad⟩ := hLad_all ν hν_lad' tr htr_buc H hH_pos.le
  -- Unprojected solve & Leray projection
  obtain ⟨aF, u_raw, ω_raw, haF, hN_u, hu_sol, hu_zero, hω_def, hω_sm, hω_per,
    hω_dec, hω_zero, hω_wk⟩ := nsrc_unproj_solve hc hν0 μ hF
  obtain ⟨hω_memLp, hω_unif, hω_cont⟩ := nsrc_scalar_gauss_memLp_and_cont hc hω_sm hω_dec
  obtain ⟨M_ω, hM_ω, hMω_bd⟩ := hω_unif H
  obtain ⟨b_cl, G_cl, hL, hbcl_sol, hbG_zero, hbG_memLp, hcurl_ae, hb_unif, hb_cont⟩ :=
    nsrc_leray_solve hc hν0 μ hF haF hN_u hu_sol hu_zero hω_def
  obtain ⟨M_b, hM_b, hMb_bd⟩ := hb_unif H
  -- Gain-inverse continuity & bound on `[0, H]`
  set gInv : ℝ → ℂ := fun s => ((gainG γ ν s)⁻¹ : ℂ)
  have hgInv_eq : gInv = Complex.ofReal ∘ (gainG γ ν)⁻¹ := by
    funext s; simp [gInv]
  have hgInv_contOn : ContinuousOn gInv (Icc 0 H) := by
    rw [hgInv_eq]
    have hgain_c : ContinuousOn (gainG γ ν) (Icc 0 H) := by
      unfold gainG
      exact Real.continuous_exp.comp_continuousOn
        ((continuousOn_const.mul continuousOn_id).div
          (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
          fun s hs => by nlinarith [hs.1])
    exact Complex.continuous_ofReal.comp_continuousOn
      (hgain_c.inv₀ fun s _ => by unfold gainG; exact (Real.exp_pos _).ne')
  have hgInv_contAt : ∀ t > 0, ContinuousAt gInv t := by
    intro t ht
    rw [hgInv_eq]
    have hgain_at : ContinuousAt (gainG γ ν) t := by
      unfold gainG
      exact Real.continuous_exp.continuousAt.comp
        ((continuousAt_const.mul continuousAt_id).div
          (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) (by positivity))
    exact Complex.continuous_ofReal.continuousAt.comp
      (hgain_at.inv₀ (by unfold gainG; exact (Real.exp_pos _).ne'))
  obtain ⟨C_g0, hCg0⟩ := isCompact_Icc.exists_bound_of_continuousOn hgInv_contOn
  set C_g : ℝ := max C_g0 0
  have hC_g : 0 ≤ C_g := le_max_right _ _
  have hgInv_bd : ∀ s ∈ Icc (0 : ℝ) H, ‖gInv s‖ ≤ C_g :=
    fun s hs => (hCg0 s hs).trans (le_max_left _ _)
  -- Set `a_zero := aF / 2` and define `u₀_cl`, `ω₀_cl`, `f`
  set a_zero : ℝ := aF / 2
  have ha_zero : 0 < a_zero := half_pos haF
  have ha_zero_lt : a_zero < aF := half_lt_self haF
  set u₀_cl : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun t x i => gInv t * b_cl (t, x) i
  set ω₀_cl : ℝ → ℝ × ℝ → ℂ := fun t x => gInv t * ω_raw (t, x)
  set f : ℝ → ℝ × ℝ → ℂ := fun t x =>
    if t ≤ a_zero then 0
    else -(((trainVel tr t x 0 : ℂ) * pdC 0 (ω₀_cl t) x +
        (trainVel tr t x 1 : ℂ) * pdC 1 (ω₀_cl t) x) +
      (u₀_cl t x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) +
        u₀_cl t x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ)))
  -- Notice `f t x = 0` for ALL `t ≤ aF`!
  have hf_zero_aF : ∀ t ≤ aF, ∀ x, f t x = 0 := by
    intro t ht x
    dsimp [f]
    split_ifs with hle
    · rfl
    · have hb0 : ∀ i, b_cl (t, x) i = 0 := (hbG_zero t ht).1 x
      have hpd0 : ∀ j, pdC j (ω₀_cl t) x = 0 := by
        intro j
        dsimp [ω₀_cl]
        rw [cpS_pdC_const_mul, (hω_zero t ht x).2 j, mul_zero]
      simp [u₀_cl, hb0, hpd0]
  -- Free uniqueness `b₀ - b_cl`, `G₀ - G_cl`
  have hdiff_sol : IsCausalEnergySolution c ν μ (fun _ _ _ => 0) (fun _ _ _ => 0)
      (fun p i => b₀ p i - b_cl p i) (fun p i j => G₀ p i j - G_cl p i j) := by
    have h1 := causalSolSub c ν μ (fun _ _ _ => 0) F F b₀ b_cl G₀ G_cl hb0_sol hbcl_sol
    have hF0 : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => F p i j - F p i j) = fun _ _ _ => 0 := by
      funext p i j; exact sub_self _
    rwa [hF0] at h1
  have hz_norm : tCalNorm c (gainConj γ ν (fun (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ))) = 0 := by
    have e : gainConj γ ν (fun (_ : ℝ × (ℝ × ℝ)) (_ _ : Fin 2) => (0 : ℂ)) = fun _ _ _ => 0 := by
      funext p i j; simp [gainConj]
    rw [e]; simp [tCalNorm, tnorm2]
  obtain ⟨hH0_le, hT0_le⟩ := hEB ν hν_eb' μ hμK (fun _ _ _ => 0) (fun _ _ _ => rfl)
    (fun _ _ => measurable_const) (by rw [hz_norm]; exact ENNReal.zero_lt_top)
    (fun p i => b₀ p i - b_cl p i) (fun p i j => G₀ p i j - G_cl p i j) hdiff_sol
  rw [hz_norm, mul_zero] at hH0_le hT0_le
  have hhCal0 : hCalNormOn c H (gainConj γ ν (fun p i => b₀ p i - b_cl p i)) = 0 :=
    le_antisymm ((hCalNormOn_le_hCalNorm _ _ _).trans hH0_le) zero_le
  have htCal0 : tCalNormOn c H (gainConj γ ν (fun p i j => G₀ p i j - G_cl p i j)) = 0 :=
    le_antisymm ((tCalNormOn_le_tCalNorm _ _ _).trans hT0_le) zero_le
  -- Uniform constant `M_f`
  set M_f : ℝ := 2 * A_m * (C_g * M_ω) + 2 * max C_tr 0 * (C_g * M_b)
  have hM_f : 0 ≤ M_f := by positivity
  -- Helper properties of `u₀_cl` and `pdC j (ω₀_cl ·)` on `t ∈ Ioc 0 H`
  have hu₀_eq_gain : ∀ t x, u₀_cl t x = gainConj γ ν b_cl (t, x) := by
    intro t x; ext i; simp [u₀_cl, gInv, gainConj, Complex.real_smul]
  have hpdω₀_eq : ∀ t j x, pdC j (ω₀_cl t) x = gInv t * pdC j (fun y => ω_raw (t, y)) x :=
    fun t j x => cpS_pdC_const_mul (gInv t) (fun y => ω_raw (t, y)) j x
  have hu₀_lp_bd : ∀ t ∈ Ioc (0 : ℝ) H, ∀ i : Fin 2,
      MemLp (fun x => u₀_cl t x i) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => u₀_cl t x i) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (C_g * M_b) := by
    intro t ht i
    have hm := ((hbG_memLp t ht.1).1 i).const_mul (gInv t)
    refine ⟨hm, ?_⟩
    rw [nsrc_eLpNorm_const_mul, ENNReal.ofReal_mul hC_g]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal (hgInv_bd t ⟨ht.1.le, ht.2⟩))
      (hMb_bd t ht i) bot_le bot_le
  have hpdω₀_lp_bd : ∀ t ∈ Ioc (0 : ℝ) H, ∀ j : Fin 2,
      MemLp (pdC j (ω₀_cl t)) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (pdC j (ω₀_cl t)) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (C_g * M_ω) := by
    intro t ht j
    have heq : pdC j (ω₀_cl t) = fun x => gInv t * pdC j (fun y => ω_raw (t, y)) x :=
      funext (hpdω₀_eq t j)
    rw [heq]
    refine ⟨((hω_memLp t).2.2 j).const_mul (gInv t), ?_⟩
    rw [nsrc_eLpNorm_const_mul, ENNReal.ofReal_mul hC_g]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal (hgInv_bd t ⟨ht.1.le, ht.2⟩))
      (hMω_bd t ht.2 j) bot_le bot_le
  -- `MemLp (f t)` and `xNorm c 9 (f t) ≤ ENNReal.ofReal M_f` for `t ∈ Ioc 0 H`
  have hf_slice_mem_bd : ∀ t ∈ Ioc (0 : ℝ) H,
      MemLp (f t) 2 (B0579.cellMeasure c 9) ∧ xNorm c 9 (f t) ≤ ENNReal.ofReal M_f := by
    intro t ht
    by_cases hle : t ≤ a_zero
    · have hf0 : f t = 0 := funext fun x => hf_zero_aF t (hle.trans ha_zero_lt.le) x
      rw [hf0]
      exact ⟨MemLp.zero, by simp [xNorm]⟩
    · have hv1 : ContDiff ℝ 1 (trainVel tr t) := contDiff_trainVel tr ht.1
      have hv0_m : AEStronglyMeasurable (fun x => (trainVel tr t x 0 : ℂ))
          (volume.restrict (B0579.cell c)) :=
        (Complex.continuous_ofReal.comp ((continuous_apply 0).comp hv1.continuous)).aestronglyMeasurable
      have hv1_m : AEStronglyMeasurable (fun x => (trainVel tr t x 1 : ℂ))
          (volume.restrict (B0579.cell c)) :=
        (Complex.continuous_ofReal.comp ((continuous_apply 1).comp hv1.continuous)).aestronglyMeasurable
      have hE0_m : AEStronglyMeasurable (fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ))
          (volume.restrict (B0579.cell c)) :=
        (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr ht.1.le 0).continuous).aestronglyMeasurable
      have hE1_m : AEStronglyMeasurable (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ))
          (volume.restrict (B0579.cell c)) :=
        (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr ht.1.le 1).continuous).aestronglyMeasurable
      have m1 := nsrc_memLp_xNorm_mul hAm hv0_m (nsrc_trainVel_bdd hbd ht 0) (hpdω₀_lp_bd t ht 0).1
      have m2 := nsrc_memLp_xNorm_mul hAm hv1_m (nsrc_trainVel_bdd hbd ht 1) (hpdω₀_lp_bd t ht 1).1
      have m3 := nsrc_memLp_xNorm_mul (le_max_right C_tr 0) hE0_m
        (nsrc_pdEc_bdd hLad ⟨ht.1.le, ht.2⟩ 0) (hu₀_lp_bd t ht 0).1
      have m4 := nsrc_memLp_xNorm_mul (le_max_right C_tr 0) hE1_m
        (nsrc_pdEc_bdd hLad ⟨ht.1.le, ht.2⟩ 1) (hu₀_lp_bd t ht 1).1
      have hf_eq : f t = -(((fun x => (trainVel tr t x 0 : ℂ) * pdC 0 (ω₀_cl t) x) +
            (fun x => (trainVel tr t x 1 : ℂ) * pdC 1 (ω₀_cl t) x)) +
          ((fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 0) +
            (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 1))) := by
        funext x; simp only [f, hle, ↓reduceIte, Pi.neg_apply, Pi.add_apply]; ring
      refine ⟨?_, ?_⟩
      · rw [hf_eq]
        exact ((m1.1.add m2.1).add (m3.1.add m4.1)).neg
      · unfold xNorm
        rw [hf_eq, eLpNorm_neg]
        have b1 : xNorm c 9 (fun x => (trainVel tr t x 0 : ℂ) * pdC 0 (ω₀_cl t) x) ≤
            ENNReal.ofReal (A_m * (C_g * M_ω)) := by
          rw [ENNReal.ofReal_mul hAm]
          exact m1.2.trans (mul_le_mul_of_nonneg_left (hpdω₀_lp_bd t ht 0).2 bot_le)
        have b2 : xNorm c 9 (fun x => (trainVel tr t x 1 : ℂ) * pdC 1 (ω₀_cl t) x) ≤
            ENNReal.ofReal (A_m * (C_g * M_ω)) := by
          rw [ENNReal.ofReal_mul hAm]
          exact m2.2.trans (mul_le_mul_of_nonneg_left (hpdω₀_lp_bd t ht 1).2 bot_le)
        have b3 : xNorm c 9 (fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 0) ≤
            ENNReal.ofReal (max C_tr 0 * (C_g * M_b)) := by
          rw [ENNReal.ofReal_mul (le_max_right C_tr 0)]
          exact m3.2.trans (mul_le_mul_of_nonneg_left (hu₀_lp_bd t ht 0).2 bot_le)
        have b4 : xNorm c 9 (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 1) ≤
            ENNReal.ofReal (max C_tr 0 * (C_g * M_b)) := by
          rw [ENNReal.ofReal_mul (le_max_right C_tr 0)]
          exact m4.2.trans (mul_le_mul_of_nonneg_left (hu₀_lp_bd t ht 1).2 bot_le)
        calc eLpNorm _ 2 (B0579.cellMeasure c 9)
            ≤ (xNorm c 9 (fun x => (trainVel tr t x 0 : ℂ) * pdC 0 (ω₀_cl t) x) +
                xNorm c 9 (fun x => (trainVel tr t x 1 : ℂ) * pdC 1 (ω₀_cl t) x)) +
              (xNorm c 9 (fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 0) +
                xNorm c 9 (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 1)) :=
              (eLpNorm_add_le (m1.1.1.add m2.1.1) (m3.1.1.add m4.1.1) one_le_two).trans
                (add_le_add (eLpNorm_add_le m1.1.1 m2.1.1 one_le_two)
                  (eLpNorm_add_le m3.1.1 m4.1.1 one_le_two))
          _ ≤ (ENNReal.ofReal (A_m * (C_g * M_ω)) + ENNReal.ofReal (A_m * (C_g * M_ω))) +
              (ENNReal.ofReal (max C_tr 0 * (C_g * M_b)) + ENNReal.ofReal (max C_tr 0 * (C_g * M_b))) :=
              add_le_add (add_le_add b1 b2) (add_le_add b3 b4)
          _ = ENNReal.ofReal M_f := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1; dsimp [M_f]; ring
  -- Helper: `HasWeakCellDerivC` scales under multiplication by a complex constant `k`
  have hwk_const_mul : ∀ {j : Fin 2} {φ' g' : ℝ × ℝ → ℂ} (k : ℂ),
      HasWeakCellDerivC c j φ' g' →
      HasWeakCellDerivC c j (fun x => k * φ' x) (fun x => k * g' x) := by
    intro j φ' g' k hw
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨I1, I2⟩ := hw.1 ψ hψ
      exact ⟨(I1.const_mul k).congr (Eventually.of_forall fun x => by dsimp only; ring),
        (I2.const_mul k).congr (Eventually.of_forall fun x => by dsimp only; ring)⟩
    · have h1 : (fun x => k * φ' x * (B0579.pd j ψ x : ℂ)) =
          fun x => k * (φ' x * (B0579.pd j ψ x : ℂ)) := funext fun _ => by ring
      have h2 : (fun x => k * g' x * (ψ x : ℂ)) =
          fun x => k * (g' x * (ψ x : ℂ)) := funext fun _ => by ring
      rw [h1, h2, integral_const_mul, integral_const_mul, hw.2 ψ hψ]
      ring
  -- Slice clauses on `t ∈ Ioc 0 H`
  have hslice_all : ∀ t ∈ Ioc (0 : ℝ) H,
      (∀ i, MemLp (fun x => b_cl (t, x) i) 2 (volume.restrict (B0579.cell c))) ∧
      (∀ i j, MemLp (fun x => G_cl (t, x) i j) 2 (volume.restrict (B0579.cell c))) ∧
      MemLp (f t) 2 (B0579.cellMeasure c 9) ∧
      HasZeroCirculation c (f t) ∧
      xNorm c 9 (f t) ≤ ENNReal.ofReal M_f ∧
      ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC c j φ (g j)) →
        h1Norm c 9 φ g ≤ 1 →
        ∫ x in B0579.cell c, f t x * φ x =
          coreSrcFun c
            (advStretch (trainVel tr t)
              (fun x => gainConj γ ν b_cl (t, x))
              (fun x => gainConj γ ν G_cl (t, x))) g := by
    intro t ht
    obtain ⟨hb_lp, hG_lp⟩ := hbG_memLp t ht.1
    obtain ⟨hf_lp, hf_bd⟩ := hf_slice_mem_bd t ht
    refine ⟨hb_lp, hG_lp, hf_lp, ?_, hf_bd, ?_⟩
    · by_cases hle : t ≤ a_zero
      · have hf0 : f t = 0 := funext fun x => hf_zero_aF t (hle.trans ha_zero_lt.le) x
        rw [hf0]; exact ⟨integrableOn_zero, by simp⟩
      · refine nsrc_zero_circ (u₀ := u₀_cl t) (ω₀ := ω₀_cl t) (f_t := f t)
            hν0 hAm hbd ht (fun i => (hu₀_lp_bd t ht i).1) ?_ ?_ ?_ hf_lp ?_
        · intro ψ hψ
          have heq : (fun x => u₀_cl t x 0 * (B0579.pd 0 ψ x : ℂ) +
              u₀_cl t x 1 * (B0579.pd 1 ψ x : ℂ)) =
              fun x => gInv t * (b_cl (t, x) 0 * (B0579.pd 0 ψ x : ℂ) +
                b_cl (t, x) 1 * (B0579.pd 1 ψ x : ℂ)) := by
            funext x; dsimp [u₀_cl]; ring
          rw [heq, integral_const_mul, hL.divFree t ht.1 ψ hψ, mul_zero]
        · exact (hω_memLp t).1.const_mul (gInv t)
        · intro j
          have heq : pdC j (ω₀_cl t) = fun x => gInv t * pdC j (fun y => ω_raw (t, y)) x :=
            funext (hpdω₀_eq t j)
          rw [heq]
          exact hwk_const_mul (gInv t) (hω_wk t j)
        · intro x; simp only [f, hle, ↓reduceIte]
    · intro φ g hg hh1
      by_cases hle : t ≤ a_zero
      · have ht_aF : t ≤ aF := hle.trans ha_zero_lt.le
        have hf0 : f t = 0 := funext fun x => hf_zero_aF t ht_aF x
        have hb0 : (fun x => gainConj γ ν b_cl (t, x)) = fun _ _ => 0 := by
          funext x i; simp [gainConj, (hbG_zero t ht_aF).1 x i]
        have hG0 : (fun x => gainConj γ ν G_cl (t, x)) = fun _ _ _ => 0 := by
          funext x i j; simp [gainConj, (hbG_zero t ht_aF).2 x i j]
        rw [hf0, hb0, hG0]
        simp [coreSrcFun, advStretch]
      · have hu_eq : (fun x => gainConj γ ν b_cl (t, x)) = u₀_cl t :=
          funext fun x => (hu₀_eq_gain t x).symm
        rw [hu_eq]
        refine nsrc_pairing_slice (u₀ := u₀_cl t)
          (Gt₀ := fun x => gainConj γ ν G_cl (t, x))
          (ω₀ := ω₀_cl t) (f_t := f t)
          hν0 hAm hbd hLad ht
          (fun i => ((hL.measurable i).comp measurable_prodMk_left).const_mul (gInv t))
          (fun i j => by
            simp only [gainConj, Pi.smul_apply]
            exact ((hL.gradMeasurable i j).comp measurable_prodMk_left).const_smul _)
          (fun i => (hu₀_lp_bd t ht i).1)
          (fun i j => by
            have e : (fun x => gainConj γ ν G_cl (t, x) i j) =
                fun x => gInv t * G_cl (t, x) i j := by
              funext x; simp [gInv, gainConj, Complex.real_smul]
            rw [e]; exact (hG_lp i j).const_mul (gInv t))
          (fun ψ hψ => by
            have heq : (fun x => u₀_cl t x 0 * (B0579.pd 0 ψ x : ℂ) +
                u₀_cl t x 1 * (B0579.pd 1 ψ x : ℂ)) =
                fun x => gInv t * (b_cl (t, x) 0 * (B0579.pd 0 ψ x : ℂ) +
                  b_cl (t, x) 1 * (B0579.pd 1 ψ x : ℂ)) := by
              funext x; dsimp [u₀_cl]; ring
            rw [heq, integral_const_mul, hL.divFree t ht.1 ψ hψ, mul_zero])
          (fun i j => by
            have e : (fun x => gainConj γ ν G_cl (t, x) i j) =
                fun x => gInv t * G_cl (t, x) i j := by
              funext x; simp [gInv, gainConj, Complex.real_smul]
            rw [e]; exact hwk_const_mul (gInv t) (hL.weakGrad t ht.1 i j))
          (by
            have e10 : ∀ x, gainConj γ ν G_cl (t, x) 1 0 = gInv t * G_cl (t, x) 1 0 :=
              fun x => by simp [gInv, gainConj, Complex.real_smul]
            have e01 : ∀ x, gainConj γ ν G_cl (t, x) 0 1 = gInv t * G_cl (t, x) 0 1 :=
              fun x => by simp [gInv, gainConj, Complex.real_smul]
            filter_upwards [hcurl_ae t ht.1] with x hx
            rw [e10 x, e01 x]
            dsimp only [ω₀_cl]
            rw [← hx]; ring)
          ((hω_memLp t).2.1.const_mul (gInv t))
          (fun j => (hpdω₀_lp_bd t ht j).1)
          (fun j => by
            have heq : pdC j (ω₀_cl t) = fun x => gInv t * pdC j (fun y => ω_raw (t, y)) x :=
              funext (hpdω₀_eq t j)
            rw [heq]; exact hwk_const_mul (gInv t) (hω_wk t j))
          hf_lp
          (fun x => by simp only [f, hle, ↓reduceIte])
          hg hh1
  -- Time continuity of `f` in `X_{9,c}` on `t ∈ Ioo 0 H`
  have hf_cont : ∀ t ∈ Ioo (0 : ℝ) H,
      Tendsto (fun t' => xNorm c 9 (f t' - f t)) (𝓝 t) (𝓝 0) := by
    intro t ht
    by_cases hlt_aF : t < aF
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Iio_mem_nhds hlt_aF] with t' ht'
      have hf1 : f t' = 0 := funext (hf_zero_aF t' (le_of_lt ht'))
      have hf2 : f t = 0 := funext (hf_zero_aF t (le_of_lt hlt_aF))
      simp [hf1, hf2, xNorm]
    · have ht_az : t ∈ Ioo a_zero H := ⟨ha_zero_lt.trans_le (not_lt.1 hlt_aF), ht.2⟩
      -- `L²` continuity of `s ↦ pdC j (ω₀_cl s)` and `s ↦ u₀_cl s · i` at `t`
      have hcont_pdω₀ : ∀ j : Fin 2,
          Tendsto (fun s => eLpNorm (pdC j (ω₀_cl s) - pdC j (ω₀_cl t)) 2
            (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0) := by
        intro j
        have h1 : Tendsto (fun s => ENNReal.ofReal C_g *
            eLpNorm (fun x => pdC j (fun y => ω_raw (s, y)) x -
              pdC j (fun y => ω_raw (t, y)) x) 2 (volume.restrict (B0579.cell c)))
            (𝓝 t) (𝓝 0) := by
          simpa using ENNReal.Tendsto.const_mul (hω_cont t j) (Or.inr ENNReal.ofReal_ne_top)
        have h2 : Tendsto (fun s => ENNReal.ofReal ‖gInv s - gInv t‖ *
            ENNReal.ofReal M_ω) (𝓝 t) (𝓝 0) := by
          have hg0 : Tendsto (fun s => ENNReal.ofReal ‖gInv s - gInv t‖) (𝓝 t) (𝓝 0) := by
            have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := by simp
            rw [h0]
            exact (ENNReal.continuous_ofReal.tendsto 0).comp
              (tendsto_iff_norm_sub_tendsto_zero.1 (hgInv_contAt t ht.1))
          simpa using ENNReal.Tendsto.mul_const hg0 (Or.inr ENNReal.ofReal_ne_top)
        have hsum : Tendsto (fun s =>
            ENNReal.ofReal C_g * eLpNorm (fun x => pdC j (fun y => ω_raw (s, y)) x -
              pdC j (fun y => ω_raw (t, y)) x) 2 (volume.restrict (B0579.cell c)) +
            ENNReal.ofReal ‖gInv s - gInv t‖ * ENNReal.ofReal M_ω) (𝓝 t) (𝓝 0) := by
          simpa using h1.add h2
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
          (Eventually.of_forall fun _ => bot_le) ?_
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        have heq : pdC j (ω₀_cl s) - pdC j (ω₀_cl t) =
            (fun x => gInv s * (pdC j (fun y => ω_raw (s, y)) x -
              pdC j (fun y => ω_raw (t, y)) x)) +
            (fun x => (gInv s - gInv t) * pdC j (fun y => ω_raw (t, y)) x) := by
          funext x; simp only [Pi.sub_apply, Pi.add_apply, hpdω₀_eq]; ring
        rw [heq]
        refine (eLpNorm_add_le
          ((((hω_memLp s).2.2 j).sub ((hω_memLp t).2.2 j)).const_mul (gInv s)).1
          (((hω_memLp t).2.2 j).const_mul (gInv s - gInv t)).1 one_le_two).trans ?_
        rw [nsrc_eLpNorm_const_mul, nsrc_eLpNorm_const_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (hgInv_bd s ⟨hs.1.le, hs.2.le⟩)) bot_le)
          (mul_le_mul_of_nonneg_left (hMω_bd t ht.2.le j) bot_le)
      have hcont_u₀ : ∀ i : Fin 2,
          Tendsto (fun s => eLpNorm (fun x => u₀_cl s x i - u₀_cl t x i) 2
            (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0) := by
        intro i
        have h1 : Tendsto (fun s => ENNReal.ofReal C_g *
            eLpNorm (fun x => b_cl (s, x) i - b_cl (t, x) i) 2
              (volume.restrict (B0579.cell c))) (𝓝 t) (𝓝 0) := by
          simpa using ENNReal.Tendsto.const_mul (hb_cont t ht.1 i) (Or.inr ENNReal.ofReal_ne_top)
        have h2 : Tendsto (fun s => ENNReal.ofReal ‖gInv s - gInv t‖ *
            ENNReal.ofReal M_b) (𝓝 t) (𝓝 0) := by
          have hg0 : Tendsto (fun s => ENNReal.ofReal ‖gInv s - gInv t‖) (𝓝 t) (𝓝 0) := by
            have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := by simp
            rw [h0]
            exact (ENNReal.continuous_ofReal.tendsto 0).comp
              (tendsto_iff_norm_sub_tendsto_zero.1 (hgInv_contAt t ht.1))
          simpa using ENNReal.Tendsto.mul_const hg0 (Or.inr ENNReal.ofReal_ne_top)
        have hsum : Tendsto (fun s =>
            ENNReal.ofReal C_g * eLpNorm (fun x => b_cl (s, x) i - b_cl (t, x) i) 2
              (volume.restrict (B0579.cell c)) +
            ENNReal.ofReal ‖gInv s - gInv t‖ * ENNReal.ofReal M_b) (𝓝 t) (𝓝 0) := by
          simpa using h1.add h2
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
          (Eventually.of_forall fun _ => bot_le) ?_
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        have heq : (fun x => u₀_cl s x i - u₀_cl t x i) =
            (fun x => gInv s * (b_cl (s, x) i - b_cl (t, x) i)) +
            (fun x => (gInv s - gInv t) * b_cl (t, x) i) := by
          funext x; dsimp [u₀_cl]; ring
        rw [heq]
        refine (eLpNorm_add_le
          ((((hbG_memLp s hs.1).1 i).sub ((hbG_memLp t ht.1).1 i)).const_mul (gInv s)).1
          (((hbG_memLp t ht.1).1 i).const_mul (gInv s - gInv t)).1 one_le_two).trans ?_
        rw [nsrc_eLpNorm_const_mul, nsrc_eLpNorm_const_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (hgInv_bd s ⟨hs.1.le, hs.2.le⟩)) bot_le)
          (mul_le_mul_of_nonneg_left (hMb_bd t ⟨ht.1, ht.2.le⟩ i) bot_le)
      -- Combine the 4 bilinear pieces via `nsrc_tendsto_xNorm_mul`
      have hterm_v : ∀ j : Fin 2, Tendsto (fun s => xNorm c 9
          (fun x => (trainVel tr s x j : ℂ) * pdC j (ω₀_cl s) x -
            (trainVel tr t x j : ℂ) * pdC j (ω₀_cl t) x)) (𝓝 t) (𝓝 0) := by
        intro j
        refine nsrc_tendsto_xNorm_mul hAm ht_az
          (fun s hs => (Complex.continuous_ofReal.comp
            ((continuous_apply j).comp (contDiff_trainVel tr (ha_zero.trans hs.1)).continuous)).aestronglyMeasurable)
          (fun s hs => nsrc_trainVel_bdd hbd ⟨ha_zero.trans hs.1, hs.2.le⟩ j)
          (fun x _ => nsrc_contAt_trainVel tr ht.1 x j)
          (fun s hs => (hpdω₀_lp_bd s ⟨ha_zero.trans hs.1, hs.2.le⟩ j).1)
          (hcont_pdω₀ j)
      have hterm_E : ∀ i : Fin 2, Tendsto (fun s => xNorm c 9
          (fun x => (B0579.pd i (UnforcedLeray.B0238.Ec tr s) x : ℂ) * u₀_cl s x i -
            (B0579.pd i (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x i)) (𝓝 t) (𝓝 0) := by
        intro i
        refine nsrc_tendsto_xNorm_mul (le_max_right C_tr 0) ht_az
          (fun s hs => (Complex.continuous_ofReal.comp
            (V1.pdE_contDiff tr (ha_zero.trans hs.1).le i).continuous).aestronglyMeasurable)
          (fun s hs => nsrc_pdEc_bdd hLad ⟨(ha_zero.trans hs.1).le, hs.2.le⟩ i)
          (fun x _ => nsrc_contAt_pdEc tr ht.1 x i)
          (fun s hs => (hu₀_lp_bd s ⟨ha_zero.trans hs.1, hs.2.le⟩ i).1)
          (hcont_u₀ i)
      have hsum4 : Tendsto (fun s =>
          (xNorm c 9 (fun x => (trainVel tr s x 0 : ℂ) * pdC 0 (ω₀_cl s) x -
              (trainVel tr t x 0 : ℂ) * pdC 0 (ω₀_cl t) x) +
            xNorm c 9 (fun x => (trainVel tr s x 1 : ℂ) * pdC 1 (ω₀_cl s) x -
              (trainVel tr t x 1 : ℂ) * pdC 1 (ω₀_cl t) x)) +
          (xNorm c 9 (fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) * u₀_cl s x 0 -
              (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 0) +
            xNorm c 9 (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ) * u₀_cl s x 1 -
              (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 1)))
          (𝓝 t) (𝓝 0) := by
        simpa using ((hterm_v 0).add (hterm_v 1)).add ((hterm_E 0).add (hterm_E 1))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum4
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [Ioo_mem_nhds ht_az.1 ht_az.2] with s hs
      have hs0 : 0 < s := ha_zero.trans hs.1
      have hns : ¬ s ≤ a_zero := not_le.2 hs.1
      have hnt : ¬ t ≤ a_zero := not_le.2 ht_az.1
      have heq_f : f s - f t =
          -(((fun x => (trainVel tr s x 0 : ℂ) * pdC 0 (ω₀_cl s) x -
                (trainVel tr t x 0 : ℂ) * pdC 0 (ω₀_cl t) x) +
              (fun x => (trainVel tr s x 1 : ℂ) * pdC 1 (ω₀_cl s) x -
                (trainVel tr t x 1 : ℂ) * pdC 1 (ω₀_cl t) x)) +
            ((fun x => (B0579.pd 0 (UnforcedLeray.B0238.Ec tr s) x : ℂ) * u₀_cl s x 0 -
                (B0579.pd 0 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 0) +
              (fun x => (B0579.pd 1 (UnforcedLeray.B0238.Ec tr s) x : ℂ) * u₀_cl s x 1 -
                (B0579.pd 1 (UnforcedLeray.B0238.Ec tr t) x : ℂ) * u₀_cl t x 1))) := by
        funext x
        simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, f, hns, hnt, ↓reduceIte]
        ring
      have mv : ∀ (r : ℝ), r ∈ Ioc (0 : ℝ) H → ∀ j : Fin 2,
          AEStronglyMeasurable (fun x => (trainVel tr r x j : ℂ) * pdC j (ω₀_cl r) x)
            (B0579.cellMeasure c 9) := fun r hr j =>
        (nsrc_memLp_xNorm_mul hAm
          (Complex.continuous_ofReal.comp
            ((continuous_apply j).comp (contDiff_trainVel tr hr.1).continuous)).aestronglyMeasurable
          (nsrc_trainVel_bdd hbd hr j) (hpdω₀_lp_bd r hr j).1).1.1
      have mE : ∀ (r : ℝ), r ∈ Ioc (0 : ℝ) H → ∀ i : Fin 2,
          AEStronglyMeasurable
            (fun x => (B0579.pd i (UnforcedLeray.B0238.Ec tr r) x : ℂ) * u₀_cl r x i)
            (B0579.cellMeasure c 9) := fun r hr i =>
        (nsrc_memLp_xNorm_mul (le_max_right C_tr 0)
          (Complex.continuous_ofReal.comp (V1.pdE_contDiff tr hr.1.le i).continuous).aestronglyMeasurable
          (nsrc_pdEc_bdd hLad ⟨hr.1.le, hr.2⟩ i) (hu₀_lp_bd r hr i).1).1.1
      have hs_Ioc : s ∈ Ioc (0 : ℝ) H := ⟨hs0, hs.2.le⟩
      have ht_Ioc : t ∈ Ioc (0 : ℝ) H := ⟨ht.1, ht.2.le⟩
      have d0 := (mv s hs_Ioc 0).sub (mv t ht_Ioc 0)
      have d1 := (mv s hs_Ioc 1).sub (mv t ht_Ioc 1)
      have e0 := (mE s hs_Ioc 0).sub (mE t ht_Ioc 0)
      have e1 := (mE s hs_Ioc 1).sub (mE t ht_Ioc 1)
      unfold xNorm
      rw [heq_f, eLpNorm_neg]
      exact (eLpNorm_add_le (d0.add d1) (e0.add e1) one_le_two).trans
        (add_le_add (eLpNorm_add_le d0 d1 one_le_two) (eLpNorm_add_le e0 e1 one_le_two))
  -- A.e. pairing transfer from `(b_cl, G_cl)` to `(b₀, G₀)`
  have hae_pair : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) H →
      ∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
        (∀ j, HasWeakCellDerivC c j φ (g j)) →
        h1Norm c 9 φ g ≤ 1 →
        ∫ x in B0579.cell c, f t x * φ x =
          coreSrcFun c (coreAdvSlice γ tr b₀ G₀ t) g := by
    have hm_bdiff : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) =>
        gainConj γ ν (fun q k => b₀ q k - b_cl q k) p i := by
      intro i
      simp only [gainConj, Pi.smul_apply]
      exact (((Real.measurable_exp.comp ((measurable_const.mul measurable_fst).div
        (measurable_const.add (measurable_const.mul measurable_fst)))).inv).smul
        ((hb0_sol.measurable i).sub (hL.measurable i)))
    have hm_Gdiff : ∀ i j, Measurable fun p : ℝ × (ℝ × ℝ) =>
        gainConj γ ν (fun q k l => G₀ q k l - G_cl q k l) p i j := by
      intro i j
      simp only [gainConj, Pi.smul_apply]
      exact (((Real.measurable_exp.comp ((measurable_const.mul measurable_fst).div
        (measurable_const.add (measurable_const.mul measurable_fst)))).inv).smul
        ((hb0_sol.gradMeasurable i j).sub (hL.gradMeasurable i j)))
    filter_upwards [nsrc_ae_slices_of_calNorm_zero hc hm_bdiff hm_Gdiff hhCal0 htCal0] with t ht_ae ht φ g hg hh1
    rw [(hslice_all t ⟨ht.1, ht.2.le⟩).2.2.2.2.2 φ g hg hh1]
    obtain ⟨hb_ae, hG_ae⟩ := ht_ae ht
    unfold coreSrcFun coreAdvSlice
    refine integral_congr_ae ?_
    filter_upwards [hb_ae, hG_ae] with x hbx hGx
    have hbu : gainConj γ ν b_cl (t, x) = gainConj γ ν b₀ (t, x) := by
      ext i
      have hi := hbx i
      simp only [gainConj, Pi.smul_apply, smul_sub] at hi ⊢
      exact (sub_eq_zero.1 hi).symm
    have hGG : gainConj γ ν G_cl (t, x) = gainConj γ ν G₀ (t, x) := by
      ext i j
      have hij := hGx i j
      simp only [gainConj, Pi.smul_apply, smul_sub] at hij ⊢
      exact (sub_eq_zero.1 hij).symm
    simp only [advStretch, hbu, hGG]
  refine ⟨b_cl, G_cl, f, a_zero, M_f, ha_zero, hM_f, hbcl_sol,
    fun s hs => (hbG_zero s (hs.trans ha_zero_lt.le)).1,
    fun s hs => (hbG_zero s (hs.trans ha_zero_lt.le)).2,
    fun t ht => hf_zero_aF t (ht.trans ha_zero_lt.le),
    hhCal0, htCal0, hslice_all, hf_cont, hae_pair⟩

end UnforcedLeray.Short.IIIa.CoreDuhamelNiceAux

end
