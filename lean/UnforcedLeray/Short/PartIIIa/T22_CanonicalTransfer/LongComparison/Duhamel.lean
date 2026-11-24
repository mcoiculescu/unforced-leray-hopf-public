import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.T20_5_VelNormEqLp
import UnforcedLeray.Short.PartIIIa.T21_2_WeakSmoothing
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV
import UnforcedLeray.Infra.EvolutionContinuity.Volterra

/-!
# Part III-a, task `PartIII-a:T22/2/3`: inhomogeneous Duhamel transfer (`CTDuhamelTransfer`)

Source of record: `the November 2 reference manuscript` (SP), lines 3190-3305
(`eq:ct-long-comparison`, `eq:ct-compact-comparison`).

Proves `UnforcedLeray.Short.IIIa.T22Sub.ctDuhamelTransfer` from `CTCanonicalBranchProps` (`T22/2/1`)
and `CTCanonicalResidual` (`T22/2/2`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa

/-! ## 1. Unconditional train bundles, scaling, Biot-Savart rescaling, and central evenness -/

private theorem trainWeightedJetPoly_uncond : TrainWeightedJetPoly := by
  have hMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv := trainOverlap_unconditional
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails := UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hfl := trainFluctuationDecay_unconditional
  have hme := UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hfl hMP
  have hmeq := trainMeanEquations_unconditional
  exact trainWeightedJetPoly_of (fluctJetWeighted_of hfl)
    (meanJetWeighted_of (meanVecFormula_of hmeq) (meanStreamJetBound_of hme hmeq)) vcWeightedJet

private theorem trainBoundsSmall_uncond : Exist.TrainBoundsSmall :=
  Exist.trainBoundsSmall_of (trainTransverseTailsUniform_of trainTransverseTails_unconditional)

private lemma ae_smul_sqrt_of_ae {a d : ℝ} (ha : 0 < a) {f g : ℝ × ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] g) :
    (fun y => f (Real.sqrt a * y.1, Real.sqrt a * y.2)) =ᵐ[volume.restrict (B0579.cell d)]
      (fun y => g (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  rw [EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell _)] at hfg ⊢
  have hqmp : Measure.QuasiMeasurePreserving (fun y : ℝ × ℝ => Real.sqrt a • y) volume volume :=
    ⟨measurable_const_smul _, Measure.AbsolutelyContinuous.mk fun s _ hs => by
      rw [Measure.map_addHaar_smul volume hR.ne']; simp [hs]⟩
  filter_upwards [hqmp.ae hfg] with y hy hyd
  simpa [T07.sqrt_smul_eq] using hy ((T06.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hyd)

private lemma ae_div_sqrt_of_ae {a d : ℝ} (ha : 0 < a) {W V : ℝ × ℝ → ℂ}
    (hWV : W =ᵐ[volume.restrict (B0579.cell d)] V) :
    (fun x => W (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) =ᵐ[volume.restrict
      (B0579.cell (d * Real.sqrt a))]
      (fun x => V (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by
  have hinv : 0 < a⁻¹ := inv_pos.2 ha
  have hsq : Real.sqrt a⁻¹ = (Real.sqrt a)⁻¹ := Real.sqrt_inv a
  have hd : d = (d * Real.sqrt a) * Real.sqrt a⁻¹ := by
    rw [hsq, mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 ha).ne', mul_one]
  have hWV' : W =ᵐ[volume.restrict (B0579.cell ((d * Real.sqrt a) * Real.sqrt a⁻¹))] V :=
    hd ▸ hWV
  have h := ae_smul_sqrt_of_ae hinv hWV'
  refine h.mono fun x hx => ?_
  simpa [hsq, div_eq_inv_mul] using hx

private lemma jscale_memLp_bound {m a d : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    {W : ℝ × ℝ → ℂ} (hW : MemLp W 2 (B0579.cellMeasure d m)) :
    MemLp (Jscale a W) 2 (B0579.cellMeasure (d * Real.sqrt a) m) ∧
      xNorm (d * Real.sqrt a) m (Jscale a W) ≤
        ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m W := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  set W₀ : ℝ × ℝ → ℂ := hW.1.mk W
  have hWm : Measurable W₀ := hW.1.stronglyMeasurable_mk.measurable
  have hae_cm : W =ᵐ[B0579.cellMeasure d m] W₀ := hW.1.ae_eq_mk
  have hae_vol : W =ᵐ[volume.restrict (B0579.cell d)] W₀ :=
    (B0579.ac_cellMeasure d m).ae_le hae_cm
  have hJae_vol : Jscale a W =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] Jscale a W₀ := by
    filter_upwards [ae_div_sqrt_of_ae ha0 hae_vol] with x hx
    simp [Jscale, hx]
  have hJae_cm : Jscale a W =ᵐ[B0579.cellMeasure (d * Real.sqrt a) m] Jscale a W₀ :=
    (B0579.cellMeasure_ac (d * Real.sqrt a) m).ae_le hJae_vol
  have hsc := scalingJa m hm a d ha hd W₀ hWm
  have hxW : xNorm d m W₀ = xNorm d m W := eLpNorm_congr_ae hae_cm.symm
  have hxJ : xNorm (d * Real.sqrt a) m (Jscale a W) = xNorm (d * Real.sqrt a) m (Jscale a W₀) :=
    eLpNorm_congr_ae hJae_cm
  have hbd : xNorm (d * Real.sqrt a) m (Jscale a W) ≤
      ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m W := by
    rw [hxJ, ← hxW]; exact hsc
  have hJm : AEStronglyMeasurable (Jscale a W) (B0579.cellMeasure (d * Real.sqrt a) m) :=
    (T06.measurable_Jscale a hWm).aestronglyMeasurable.congr hJae_cm.symm
  refine ⟨⟨hJm, lt_of_le_of_lt hbd (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.2)⟩, hbd⟩

private lemma jscaleInv_memLp_bound {m a d : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure (d * Real.sqrt a) m)) :
    MemLp (JscaleInv a f) 2 (B0579.cellMeasure d m) ∧
      xNorm d m (JscaleInv a f) ≤
        ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm (d * Real.sqrt a) m f := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  set f₀ : ℝ × ℝ → ℂ := hf.1.mk f
  have hfm : Measurable f₀ := hf.1.stronglyMeasurable_mk.measurable
  have hae_cm : f =ᵐ[B0579.cellMeasure (d * Real.sqrt a) m] f₀ := hf.1.ae_eq_mk
  have hae_vol : f =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] f₀ :=
    (B0579.ac_cellMeasure (d * Real.sqrt a) m).ae_le hae_cm
  have hJae_vol : JscaleInv a f =ᵐ[volume.restrict (B0579.cell d)] JscaleInv a f₀ := by
    filter_upwards [ae_smul_sqrt_of_ae ha0 hae_vol] with y hy
    simp [JscaleInv, hy]
  have hJae_cm : JscaleInv a f =ᵐ[B0579.cellMeasure d m] JscaleInv a f₀ :=
    (B0579.cellMeasure_ac d m).ae_le hJae_vol
  have hsc := scalingJaInv m hm a d ha hd f₀ hfm
  have hxf : xNorm (d * Real.sqrt a) m f₀ = xNorm (d * Real.sqrt a) m f :=
    eLpNorm_congr_ae hae_cm.symm
  have hxJ : xNorm d m (JscaleInv a f) = xNorm d m (JscaleInv a f₀) :=
    eLpNorm_congr_ae hJae_cm
  have hbd : xNorm d m (JscaleInv a f) ≤
      ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm (d * Real.sqrt a) m f := by
    rw [hxJ, ← hxf]; exact hsc
  have hJ₀m : Measurable (JscaleInv a f₀) := by
    unfold JscaleInv
    exact (hfm.comp ((measurable_fst.const_mul _).prodMk (measurable_snd.const_mul _))).const_mul _
  have hJm : AEStronglyMeasurable (JscaleInv a f) (B0579.cellMeasure d m) :=
    hJ₀m.aestronglyMeasurable.congr hJae_cm.symm
  refine ⟨⟨hJm, lt_of_le_of_lt hbd (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)⟩, hbd⟩

private lemma integral_cell_comp_sqrt_smul {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (f : ℝ × ℝ → ℂ) :
    ∫ y in B0579.cell d, f (Real.sqrt a * y.1, Real.sqrt a * y.2) =
      ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), f x := by
  have h := pairingCoV (d * Real.sqrt a) a (mul_pos hd (Real.sqrt_pos.2 ha)) ha f (fun _ => 1)
  have hdlen : cellLen (d * Real.sqrt a) a = d := by
    unfold cellLen; exact mul_div_cancel_right₀ d (Real.sqrt_pos.2 ha).ne'
  rw [hdlen] at h
  have hL : (∫ y in B0579.cell d, JscaleInv a f y * 1) =
      ((a ^ 2 : ℝ) : ℂ) * ∫ y in B0579.cell d, f (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
    simp only [mul_one, JscaleInv, integral_const_mul]
  have hR : (∫ x in B0579.cell (d * Real.sqrt a), f x * physAdj a (fun _ => 1) x) =
      (a : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), f x := by
    have hp : ∀ x, f x * physAdj a (fun _ => 1) x = (a : ℂ) * f x := fun x => by
      unfold physAdj; ring
    simp only [hp, integral_const_mul]
  rw [hL, hR] at h
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have ha2 : ((a ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_ne_zero 2 ha.ne')
  calc ∫ y in B0579.cell d, f (Real.sqrt a * y.1, Real.sqrt a * y.2)
      = (((a ^ 2 : ℝ) : ℂ))⁻¹ * (((a ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d, f (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
        rw [inv_mul_cancel_left₀ ha2]
    _ = (((a ^ 2 : ℝ) : ℂ))⁻¹ * ((a : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), f x) := by rw [h]
    _ = ((a⁻¹ : ℝ) : ℂ) * ∫ x in B0579.cell (d * Real.sqrt a), f x := by
        push_cast; field_simp

private lemma hasZeroCirc_jscale {m a d : ℝ} (hm : 1 < m) (ha : 1 ≤ a) (hd : 0 < d)
    {W : ℝ × ℝ → ℂ} (hW : MemLp W 2 (B0579.cellMeasure d m)) (hz : HasZeroCirculation d W) :
    HasZeroCirculation (d * Real.sqrt a) (Jscale a W) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hmem := (jscale_memLp_bound (by linarith) ha hd hW).1
  refine ⟨integrableOn_cell_of_X hm hmem, ?_⟩
  have hcov := integral_cell_comp_sqrt_smul ha0 hd (Jscale a W)
  have hpt : (fun y : ℝ × ℝ => Jscale a W (Real.sqrt a * y.1, Real.sqrt a * y.2)) =
      fun y => ((a ^ (-2 : ℝ) : ℝ) : ℂ) * W y := by
    funext y
    simpa [T07.sqrt_smul_eq] using T06.Jscale_smul_sqrt ha0 W y
  rw [hpt, integral_const_mul, hz.2, mul_zero] at hcov
  have hane : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (inv_ne_zero ha0.ne')
  exact (mul_eq_zero.1 hcov.symm).resolve_left hane

private lemma hasZeroCirc_jscaleInv {m a d : ℝ} (hm : 1 < m) (ha : 1 ≤ a) (hd : 0 < d)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure (d * Real.sqrt a) m))
    (hz : HasZeroCirculation (d * Real.sqrt a) f) :
    HasZeroCirculation d (JscaleInv a f) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hmem := (jscaleInv_memLp_bound (by linarith) ha hd hf).1
  refine ⟨integrableOn_cell_of_X hm hmem, ?_⟩
  unfold JscaleInv
  rw [integral_const_mul, integral_cell_comp_sqrt_smul ha0 hd f, hz.2, mul_zero, mul_zero]

private lemma jscale_jscaleInv {a : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) :
    Jscale a (JscaleInv a f) = f := by
  funext x
  unfold Jscale JscaleInv
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hcoord : (Real.sqrt a * (x.1 / Real.sqrt a), Real.sqrt a * (x.2 / Real.sqrt a)) = x := by
    ext <;> simp [mul_div_cancel₀ _ hsq]
  have hpow : (a ^ (-2 : ℝ) : ℝ) * a ^ 2 = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')]
  dsimp only
  rw [hcoord]
  calc ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (((a ^ 2 : ℝ) : ℂ) * f x)
      = (((a ^ (-2 : ℝ) * a ^ 2 : ℝ)) : ℂ) * f x := by push_cast; ring
    _ = f x := by rw [hpow, Complex.ofReal_one, one_mul]

private lemma jscaleInv_jscale {a : ℝ} (ha : 0 < a) (W : ℝ × ℝ → ℂ) :
    JscaleInv a (Jscale a W) = W := by
  funext y
  unfold JscaleInv Jscale
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
    ext <;> simp [mul_div_cancel_left₀ _ hsq]
  have hpow : (a ^ 2 : ℝ) * a ^ (-2 : ℝ) = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne')]
  dsimp only
  rw [hcoord]
  calc ((a ^ 2 : ℝ) : ℂ) * (((a ^ (-2 : ℝ) : ℝ) : ℂ) * W y)
      = (((a ^ 2 * a ^ (-2 : ℝ) : ℝ)) : ℂ) * W y := by push_cast; ring
    _ = W y := by rw [hpow, Complex.ofReal_one, one_mul]

private lemma isCentrallyEven_jscale (a : ℝ) {W : ℝ × ℝ → ℂ} (hW : IsCentrallyEven W) :
    IsCentrallyEven (Jscale a W) := by
  intro x
  unfold Jscale
  have h : ((-x).1 / Real.sqrt a, (-x).2 / Real.sqrt a) =
      -(x.1 / Real.sqrt a, x.2 / Real.sqrt a) := by
    ext <;> simp [neg_div]
  rw [h, hW]

private lemma isCentrallyEven_jscaleInv (a : ℝ) {f : ℝ × ℝ → ℂ} (hf : IsCentrallyEven f) :
    IsCentrallyEven (JscaleInv a f) := by
  intro y
  unfold JscaleInv
  have h : (Real.sqrt a * (-y).1, Real.sqrt a * (-y).2) =
      -(Real.sqrt a * y.1, Real.sqrt a * y.2) := by
    ext <;> simp
  rw [h, hf]

private lemma isCentrallyEven_smul (z : ℂ) {f : ℝ × ℝ → ℂ} (hf : IsCentrallyEven f) :
    IsCentrallyEven (fun x => z * f x) :=
  fun x => by simp [hf x]

/-- Rescaled velocity `U_mov(y) = a^{3/2} u(√a y)`. -/
private def velMov (a : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (y : ℝ × ℝ) (j : Fin 2) : ℂ :=
  ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) j

private lemma isCylTest_div_sqrt {a d : ℝ} (ha : 0 < a) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) :
    B0579.IsCylTest (d * Real.sqrt a) (fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hRne : Real.sqrt a ≠ 0 := hR.ne'
  refine ⟨?_, ?_, ?_⟩
  · exact hψ.smooth.comp ((contDiff_fst.div_const _).prodMk (contDiff_snd.div_const _))
  · intro x
    have h1 : (x.1 + d * Real.sqrt a) / Real.sqrt a = x.1 / Real.sqrt a + d := by
      field_simp
    dsimp only
    rw [h1]
    exact hψ.periodic (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
  · obtain ⟨B, hB⟩ := hψ.band
    refine ⟨max B 0 * Real.sqrt a, fun x hx => ?_⟩
    have hlt : B < |x.2 / Real.sqrt a| := by
      rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left B 0) hR.le) hx
    exact hB _ hlt

private lemma pd_div_sqrt {a : ℝ} (_ha : 0 < a) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun z : ℝ × ℝ => ψ (z.1 / Real.sqrt a, z.2 / Real.sqrt a)) x =
      (Real.sqrt a)⁻¹ * B0579.pd k ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((Real.sqrt a)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((Real.sqrt a)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hL : ∀ z : ℝ × ℝ, L z = (z.1 / Real.sqrt a, z.2 / Real.sqrt a) := fun z => by
    ext <;> simp [L, div_eq_inv_mul]
  have hfun : (fun z : ℝ × ℝ => ψ (z.1 / Real.sqrt a, z.2 / Real.sqrt a)) = ψ ∘ L := by
    funext z; simp [Function.comp, hL z]
  unfold B0579.pd
  have hd : DifferentiableAt ℝ ψ (L x) := (hψ.differentiable (by simp)) (L x)
  have hfd : fderiv ℝ (ψ ∘ L) x = (fderiv ℝ ψ (L x)).comp L :=
    (hd.hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hLk : L (B0579.dir k) = (Real.sqrt a)⁻¹ • B0579.dir k := by
    fin_cases k <;> ext <;> simp [L, B0579.dir]
  rw [hfun, hfd, ContinuousLinearMap.comp_apply, hLk, map_smul, smul_eq_mul, hL x]

private lemma eLpNorm_sq_velMov {a d : ℝ} (ha : 0 < a) {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))))
    (j : Fin 2) :
    MemLp (fun y => velMov a u y j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun y => velMov a u y j) 2 (volume.restrict (B0579.cell d)) =
        ENNReal.ofReal a *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set u₀ : ℝ × ℝ → ℂ := (hu j).1.mk (fun x => u x j)
  have hu₀m : Measurable u₀ := (hu j).1.stronglyMeasurable_mk.measurable
  have hae : (fun x => u x j) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] u₀ :=
    (hu j).1.ae_eq_mk
  have hae_y : (fun y => velMov a u y j) =ᵐ[volume.restrict (B0579.cell d)]
      (fun y => ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u₀ (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
    filter_upwards [ae_smul_sqrt_of_ae ha hae] with y hy
    simp [velMov, hy]
  have hm_y : AEStronglyMeasurable (fun y => velMov a u y j) (volume.restrict (B0579.cell d)) :=
    ((hu₀m.comp ((measurable_fst.const_mul _).prodMk
      (measurable_snd.const_mul _))).const_mul _).aestronglyMeasurable.congr hae_y.symm
  let H : ℝ × ℝ → ℝ≥0∞ := (B0579.cell (d * Real.sqrt a)).indicator (fun x => ‖u₀ x‖ₑ ^ 2)
  have hHm : Measurable H :=
    (hu₀m.enorm.pow_const 2).indicator (B0579.measurableSet_cell _)
  have hcov := T06.lintegral_comp_sqrt_smul ha hHm
  have hpt : ∀ y, ((B0579.cell d).indicator
      (fun y => ‖((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u₀ (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2)) y
      = ENNReal.ofReal (a ^ (3 : ℝ)) * H (Real.sqrt a • y) := by
    intro y
    by_cases hy : y ∈ B0579.cell d
    · have hx : Real.sqrt a • y ∈ B0579.cell (d * Real.sqrt a) :=
        (T06.smul_mem_cell_iff d (Real.sqrt a) hR y).2 hy
      dsimp only [H]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, T07.sqrt_smul_eq, enorm_mul, mul_pow,
        T06.enorm_ofReal_cast (Real.rpow_nonneg ha.le _),
        ← ENNReal.ofReal_pow (Real.rpow_nonneg ha.le _), ← Real.rpow_natCast,
        ← Real.rpow_mul ha.le]
      norm_num
    · have hx : Real.sqrt a • y ∉ B0579.cell (d * Real.sqrt a) :=
        fun h => hy ((T06.smul_mem_cell_iff d (Real.sqrt a) hR y).1 h)
      simp [H, hy, hx]
  have hlint : ∫⁻ y, ‖velMov a u y j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell d)) =
      ENNReal.ofReal (a ^ 2) *
        ∫⁻ x, ‖u x j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell (d * Real.sqrt a))) := by
    have e1 : ∫⁻ y, ‖velMov a u y j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell d)) =
        ∫⁻ y, ‖((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u₀ (Real.sqrt a * y.1, Real.sqrt a * y.2)‖ₑ ^ 2
          ∂(volume.restrict (B0579.cell d)) :=
      lintegral_congr_ae (hae_y.mono fun y hy => by dsimp only at hy ⊢; rw [hy])
    have e2 : ∫⁻ x, ‖u x j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell (d * Real.sqrt a))) =
        ∫⁻ x, ‖u₀ x‖ₑ ^ 2 ∂(volume.restrict (B0579.cell (d * Real.sqrt a))) :=
      lintegral_congr_ae (hae.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
    rw [e1, e2, ← lintegral_indicator (B0579.measurableSet_cell d),
      lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hcov,
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
    have ha3 : a ^ (3 : ℝ) * a⁻¹ = a ^ 2 := by
      have : a ^ (3 : ℝ) = a ^ (3 : ℕ) := Real.rpow_natCast a 3
      rw [this]; field_simp
    rw [ha3, lintegral_indicator (B0579.measurableSet_cell _)]
  have henorm : eLpNorm (fun y => velMov a u y j) 2 (volume.restrict (B0579.cell d)) =
      ENNReal.ofReal a *
        eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
    rw [T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral, hlint,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (sq_nonneg a) (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ha.le]
  refine ⟨⟨hm_y, ?_⟩, henorm⟩
  rw [henorm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu j).2

private lemma isBiotSavart_velMov {a d : ℝ} (ha : 0 < a) (hd : 0 < d) {om : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hbs : IsBiotSavart (d * Real.sqrt a) om u) :
    IsBiotSavart d (JscaleInv a om) (velMov a u) ∧
      velNorm d (velMov a u) = ENNReal.ofReal a * velNorm (d * Real.sqrt a) u := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hRne : Real.sqrt a ≠ 0 := hR.ne'
  have hmem := fun j => (eLpNorm_sq_velMov ha hbs.1 j).1
  have hnrm := fun j => (eLpNorm_sq_velMov ha hbs.1 j).2
  refine ⟨⟨hmem, ?_, ?_⟩, ?_⟩
  · intro ψ hψ
    let ψp : ℝ × ℝ → ℝ := fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hψp : B0579.IsCylTest (d * Real.sqrt a) ψp := isCylTest_div_sqrt ha hψ
    have hdiv := hbs.2.1 ψp hψp
    have hcov := integral_cell_comp_sqrt_smul ha hd
      (fun x => u x 0 * (B0579.pd 0 ψp x : ℂ) + u x 1 * (B0579.pd 1 ψp x : ℂ))
    rw [hdiv, mul_zero] at hcov
    have hpt : (fun y : ℝ × ℝ => velMov a u y 0 * (B0579.pd 0 ψ y : ℂ) +
        velMov a u y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => ((a ^ (3 / 2 : ℝ) * Real.sqrt a : ℝ) : ℂ) *
          (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
              (B0579.pd 0 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) +
            u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
              (B0579.pd 1 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
      funext y
      simp only [velMov, ψp, pd_div_sqrt ha hψ.smooth]
      have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
        ext <;> simp [mul_div_cancel_left₀ _ hRne]
      rw [hcoord]
      push_cast
      field_simp [hRne]
    rw [hpt, integral_const_mul, hcov, mul_zero]
  · intro ψ hψ
    let ψp : ℝ × ℝ → ℝ := fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hψp : B0579.IsCylTest (d * Real.sqrt a) ψp := isCylTest_div_sqrt ha hψ
    have hcurl := hbs.2.2 ψp hψp
    have hcovL := integral_cell_comp_sqrt_smul ha hd (fun x => om x * (ψp x : ℂ))
    have hcovR := integral_cell_comp_sqrt_smul ha hd
      (fun x => u x 0 * (B0579.pd 1 ψp x : ℂ) - u x 1 * (B0579.pd 0 ψp x : ℂ))
    have hL : (∫ y in B0579.cell d, JscaleInv a om y * (ψ y : ℂ)) =
        ((a ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d, om (Real.sqrt a * y.1, Real.sqrt a * y.2) *
            (ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) := by
      have hp : ∀ y : ℝ × ℝ, JscaleInv a om y * (ψ y : ℂ) =
          ((a ^ 2 : ℝ) : ℂ) * (om (Real.sqrt a * y.1, Real.sqrt a * y.2) *
            (ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
        intro y
        unfold JscaleInv
        simp only [ψp]
        have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
          ext <;> simp [mul_div_cancel_left₀ _ hRne]
        rw [hcoord]; ring
      simp only [hp, integral_const_mul]
    have ha32 : a ^ (3 / 2 : ℝ) * Real.sqrt a = a ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]
      norm_num
    have hR' : (∫ y in B0579.cell d,
        (velMov a u y 0 * (B0579.pd 1 ψ y : ℂ) - velMov a u y 1 * (B0579.pd 0 ψ y : ℂ))) =
        ((a ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d,
            (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
                (B0579.pd 1 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) -
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
                (B0579.pd 0 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
      have hp : ∀ y : ℝ × ℝ,
          velMov a u y 0 * (B0579.pd 1 ψ y : ℂ) - velMov a u y 1 * (B0579.pd 0 ψ y : ℂ) =
          ((a ^ 2 : ℝ) : ℂ) *
            (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
                (B0579.pd 1 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) -
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
                (B0579.pd 0 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
        intro y
        rw [← ha32]
        simp only [velMov, ψp, pd_div_sqrt ha hψ.smooth]
        have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
          ext <;> simp [mul_div_cancel_left₀ _ hRne]
        rw [hcoord]
        push_cast
        field_simp [hRne]
      simp only [hp, integral_const_mul]
    rw [hL, hR', hcovL, hcovR, hcurl]
  · unfold velNorm
    have hsum : (∑ j : Fin 2, eLpNorm (fun y => velMov a u y j) 2
          (volume.restrict (B0579.cell d)) ^ 2) =
        ENNReal.ofReal a ^ 2 *
          ∑ j : Fin 2, eLpNorm (fun x => u x j) 2
            (volume.restrict (B0579.cell (d * Real.sqrt a))) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hnrm j, mul_pow]
    rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    congr 1
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num

private lemma kinNorm_eq_of_isBiotSavart {d : ℝ} (hd : 0 < d) {f : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hu : IsBiotSavart d f u) :
    kinNorm d f = velNorm d u := by
  unfold kinNorm
  refine le_antisymm (iInf_le_of_le u (iInf_le _ hu)) ?_
  refine le_iInf fun v => le_iInf fun hv => ?_
  have hae := CTE.isBiotSavart_unique d hd f u v hu hv
  unfold velNorm
  refine le_of_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact eLpNorm_congr_ae (hae.mono fun x hx => by simp [hx])

private lemma isBiotSavart_congr_ae {d : ℝ} {f₁ f₂ : ℝ × ℝ → ℂ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (h1 : IsBiotSavart d f₁ u₁) (hf : f₁ =ᵐ[volume.restrict (B0579.cell d)] f₂)
    (hu : u₁ =ᵐ[volume.restrict (B0579.cell d)] u₂) :
    IsBiotSavart d f₂ u₂ := by
  refine ⟨fun j => (h1.1 j).ae_eq (hu.mono fun x hx => by simp [hx]), ?_, ?_⟩
  · intro ψ hψ
    rw [← h1.2.1 ψ hψ]
    exact integral_congr_ae (hu.mono fun x hx => by simp [hx])
  · intro ψ hψ
    have eL : ∫ x in B0579.cell d, f₂ x * (ψ x : ℂ) = ∫ x in B0579.cell d, f₁ x * (ψ x : ℂ) :=
      integral_congr_ae (hf.symm.mono fun x hx => by simp [hx])
    have eR : ∫ x in B0579.cell d, (u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) =
        ∫ x in B0579.cell d, (u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) :=
      integral_congr_ae (hu.symm.mono fun x hx => by simp [hx])
    rw [eL, eR, h1.2.2 ψ hψ]

private lemma kinNorm_congr_ae {d : ℝ} {f₁ f₂ : ℝ × ℝ → ℂ}
    (hf : f₁ =ᵐ[volume.restrict (B0579.cell d)] f₂) :
    kinNorm d f₁ = kinNorm d f₂ := by
  have hiff : ∀ u, IsBiotSavart d f₁ u ↔ IsBiotSavart d f₂ u := fun u =>
    ⟨fun h => isBiotSavart_congr_ae h hf EventuallyEq.rfl,
      fun h => isBiotSavart_congr_ae h hf.symm EventuallyEq.rfl⟩
  simp only [kinNorm, hiff]

private lemma quadQ_congr_ae {d : ℝ} {f₁ f₂ : ℝ × ℝ → ℂ}
    (hf : f₁ =ᵐ[volume.restrict (B0579.cell d)] f₂) :
    quadQ d f₁ = quadQ d f₂ := by
  unfold quadQ
  congr 1
  exact integral_congr_ae (hf.mono fun x hx => by dsimp only; rw [hx])

private lemma isBiotSavart_smul {d : ℝ} (z : ℂ) {f : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : IsBiotSavart d f u) :
    IsBiotSavart d (fun x => z * f x) (fun x j => z * u x j) := by
  refine ⟨fun j => (hu.1 j).const_mul z, ?_, ?_⟩
  · intro ψ hψ
    have hp : (fun x => z * u x 0 * (B0579.pd 0 ψ x : ℂ) + z * u x 1 * (B0579.pd 1 ψ x : ℂ)) =
        fun x => z * (u x 0 * (B0579.pd 0 ψ x : ℂ) + u x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      funext x; ring
    rw [hp, integral_const_mul, hu.2.1 ψ hψ, mul_zero]
  · intro ψ hψ
    have hp1 : (fun x => z * f x * (ψ x : ℂ)) = fun x => z * (f x * (ψ x : ℂ)) := by
      funext x; ring
    have hp2 : (fun x => z * u x 0 * (B0579.pd 1 ψ x : ℂ) - z * u x 1 * (B0579.pd 0 ψ x : ℂ)) =
        fun x => z * (u x 0 * (B0579.pd 1 ψ x : ℂ) - u x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      funext x; ring
    rw [hp1, hp2, integral_const_mul, integral_const_mul, hu.2.2 ψ hψ]

private lemma velNorm_smul {d : ℝ} (z : ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) :
    velNorm d (fun x j => z * u x j) = ENNReal.ofReal ‖z‖ * velNorm d u := by
  unfold velNorm
  have he : ∀ j : Fin 2, eLpNorm (fun x => z * u x j) 2 (volume.restrict (B0579.cell d)) =
      ENNReal.ofReal ‖z‖ * eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) := by
    intro j
    change eLpNorm (z • fun x => u x j) 2 (volume.restrict (B0579.cell d)) = _
    rw [eLpNorm_const_smul, ofReal_norm]
  have hsum : (∑ j : Fin 2, eLpNorm (fun x => z * u x j) 2 (volume.restrict (B0579.cell d)) ^ 2) =
      ENNReal.ofReal ‖z‖ ^ 2 *
        ∑ j : Fin 2, eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he j, mul_pow]
  rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private lemma isBiotSavart_add {d m : ℝ} (hm : 1 < m) {f₁ f₂ : ℝ × ℝ → ℂ}
    {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure d m)) (hf₂ : MemLp f₂ 2 (B0579.cellMeasure d m))
    (h₁ : IsBiotSavart d f₁ u₁) (h₂ : IsBiotSavart d f₂ u₂) :
    IsBiotSavart d (f₁ + f₂) (u₁ + u₂) := by
  have hneg := isBiotSavart_smul (-1 : ℂ) h₂
  have hsub := ladBSSub m d f₁ (fun x => (-1 : ℂ) * f₂ x) u₁ (fun x j => (-1 : ℂ) * u₂ x j)
    hm hf₁ (hf₂.const_mul (-1 : ℂ)) h₁ hneg
  refine isBiotSavart_congr_ae hsub (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · simp [Pi.sub_apply, Pi.add_apply]
  · funext j; simp [Pi.sub_apply, Pi.add_apply]

private lemma velNorm_add_le {d : ℝ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (h₁ : ∀ j, MemLp (fun x => u₁ x j) 2 (volume.restrict (B0579.cell d)))
    (h₂ : ∀ j, MemLp (fun x => u₂ x j) 2 (volume.restrict (B0579.cell d))) :
    velNorm d (u₁ + u₂) ≤ velNorm d u₁ + velNorm d u₂ := by
  have hm1 : MemLp (fun x => (WithLp.equiv 2 (Fin 2 → ℂ)).symm (u₁ x)) 2 (B0581.cellVol d) :=
    memLp_piLp_iff.2 h₁
  have hm2 : MemLp (fun x => (WithLp.equiv 2 (Fin 2 → ℂ)).symm (u₂ x)) 2 (B0581.cellVol d) :=
    memLp_piLp_iff.2 h₂
  by_cases hd : 0 < d
  · have : Fact (0 < d) := ⟨hd⟩
    let F₁ : Lp B0581.Vel 2 (B0581.cellVol d) := hm1.toLp _
    let F₂ : Lp B0581.Vel 2 (B0581.cellVol d) := hm2.toLp _
    have e1 : velNorm d u₁ = ENNReal.ofReal ‖F₁‖ := by
      rw [← CTE.velNorm_eq_lp d F₁]
      unfold velNorm; congr 1; refine Finset.sum_congr rfl fun j _ => ?_; congr 1
      dsimp only [F₁]
      exact eLpNorm_congr_ae (hm1.coeFn_toLp.symm.mono fun x hx =>
        congrArg (fun v : B0581.Vel => v j) hx)
    have e2 : velNorm d u₂ = ENNReal.ofReal ‖F₂‖ := by
      rw [← CTE.velNorm_eq_lp d F₂]
      unfold velNorm; congr 1; refine Finset.sum_congr rfl fun j _ => ?_; congr 1
      dsimp only [F₂]
      exact eLpNorm_congr_ae (hm2.coeFn_toLp.symm.mono fun x hx =>
        congrArg (fun v : B0581.Vel => v j) hx)
    have e12 : velNorm d (u₁ + u₂) = ENNReal.ofReal ‖F₁ + F₂‖ := by
      rw [← CTE.velNorm_eq_lp d (F₁ + F₂)]
      unfold velNorm; congr 1; refine Finset.sum_congr rfl fun j _ => ?_; congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_add F₁ F₂, hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx h1x h2x
      have hj : ((F₁ + F₂ : Lp B0581.Vel 2 (B0581.cellVol d)) x).ofLp j =
          (F₁ x).ofLp j + (F₂ x).ofLp j :=
        congrArg (fun v : B0581.Vel => v.ofLp j) hx
      have hj1 : (F₁ x).ofLp j = u₁ x j := congrArg (fun v : B0581.Vel => v.ofLp j) h1x
      have hj2 : (F₂ x).ofLp j = u₂ x j := congrArg (fun v : B0581.Vel => v.ofLp j) h2x
      show u₁ x j + u₂ x j = ((F₁ + F₂ : Lp B0581.Vel 2 (B0581.cellVol d)) x).ofLp j
      rw [hj, hj1, hj2]
    rw [e1, e2, e12, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  · have hcell : B0579.cell d = ∅ := by
      ext x; simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, h2⟩; linarith
    simp [velNorm, hcell]

private def symEven (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  (2 : ℂ)⁻¹ * (f x + f (-x))

private lemma isCentrallyEven_symEven (f : ℝ × ℝ → ℂ) : IsCentrallyEven (symEven f) := by
  intro x
  unfold symEven
  rw [neg_neg, add_comm]

private lemma cell_neg_ae_eq (c : ℝ) :
    (Neg.neg ⁻¹' B0579.cell c : Set (ℝ × ℝ)) =ᵐ[volume] B0579.cell c := by
  rw [MeasureTheory.ae_eq_set]
  by_cases hc : 0 < c
  · refine ⟨?_, ?_⟩
    · have hsub : (Neg.neg ⁻¹' B0579.cell c) \ B0579.cell c ⊆ {c / 2} ×ˢ (univ : Set ℝ) := by
        rintro x ⟨h1, h2⟩
        simp only [mem_preimage, B0579.cell, mem_prod, mem_Ico, mem_univ, and_true,
          Prod.fst_neg] at h1 h2
        have hx' : x.1 = c / 2 := by
          by_contra hne
          exact h2 ⟨by linarith, lt_of_le_of_ne (by linarith) hne⟩
        exact ⟨hx', trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
    · have hsub : B0579.cell c \ (Neg.neg ⁻¹' B0579.cell c) ⊆ {-(c / 2)} ×ˢ (univ : Set ℝ) := by
        rintro x ⟨h1, h2⟩
        simp only [mem_preimage, B0579.cell, mem_prod, mem_Ico, mem_univ, and_true,
          Prod.fst_neg] at h1 h2
        have hx' : x.1 = -(c / 2) := by
          by_contra hne
          exact h2 ⟨by linarith, by have := lt_of_le_of_ne h1.1 (Ne.symm hne); linarith⟩
        exact ⟨hx', trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  · have h1 : B0579.cell c = ∅ := by
      ext x; simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, mem_empty_iff_false,
        iff_false]
      rintro ⟨a, b⟩; linarith
    simp [h1]

private lemma restrict_cell_neg_eq (c : ℝ) :
    Measure.map Neg.neg (volume.restrict (B0579.cell c)) = volume.restrict (B0579.cell c) := by
  have hmp : MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_neg volume
  have heq : volume.restrict (Neg.neg ⁻¹' B0579.cell c) = volume.restrict (B0579.cell c) :=
    Measure.restrict_congr_set (cell_neg_ae_eq c)
  calc Measure.map Neg.neg (volume.restrict (B0579.cell c))
      = Measure.map Neg.neg (volume.restrict (Neg.neg ⁻¹' B0579.cell c)) := by rw [heq]
    _ = (Measure.map Neg.neg volume).restrict (B0579.cell c) :=
        ((MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding.restrict_map volume (B0579.cell c)).symm
    _ = volume.restrict (B0579.cell c) := by rw [hmp.map_eq]

private lemma measurePreserving_neg_cell (c : ℝ) :
    MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ)
      (volume.restrict (B0579.cell c)) (volume.restrict (B0579.cell c)) :=
  ⟨measurable_neg, restrict_cell_neg_eq c⟩

private lemma ae_neg_of_ae_cell {c : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => g (-x)) :=
  (measurePreserving_neg_cell c).quasiMeasurePreserving.ae_eq_comp h

private lemma integral_cell_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : ℝ × ℝ → E) :
    ∫ x in B0579.cell c, f (-x) = ∫ x in B0579.cell c, f x :=
  (measurePreserving_neg_cell c).integral_comp (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding f

private lemma symEven_ae_eq {c : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell c)] f) :
    symEven f =ᵐ[volume.restrict (B0579.cell c)] f := by
  filter_upwards [hf] with x hx
  unfold symEven
  rw [hx]
  ring

/-! ## 2. Weak uniqueness on finite age windows `[t₀, S]` without `strongCont` -/

private lemma hasDerivAt_pdCx_of_contDiffOn {t₀ s : ℝ} {G : ℝ × (ℝ × ℝ) → ℂ}
    (hG : ContDiffOn ℝ ∞ G (Ioo t₀ s ×ˢ univ)) {ρ : ℝ} (hρ : ρ ∈ Ioo t₀ s)
    (k : Fin 2) (x : ℝ × ℝ) :
    HasDerivAt (fun r => pdCx k (fun y => G (r, y)) x)
      (pdCx k (fun y => fderiv ℝ G (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ))) x) ρ := by
  let U : Set (ℝ × (ℝ × ℝ)) := Ioo t₀ s ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hGU : ContDiffOn ℝ ∞ (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by simp)
  have hpd_eq : ∀ r ∈ Ioo t₀ s, ∀ y : ℝ × ℝ,
      pdCx k (fun z => G (r, z)) y = fderiv ℝ G (r, y) ((0 : ℝ), B0579.dir k) := by
    intro r hr y
    unfold pdCx
    have hd : DifferentiableAt ℝ G (r, y) :=
      (hG.contDiffAt (hU.mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt (by simp)
    have hl : HasFDerivAt (fun z : ℝ × ℝ => (r, z))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
      (hasFDerivAt_const r y).prodMk (hasFDerivAt_id y)
    have hcomp : HasFDerivAt (fun z => G (r, z)) _ y := hd.hasFDerivAt.comp y hl
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    rfl
  have hsymm : IsSymmSndFDerivAt ℝ G (ρ, x) :=
    (hG.contDiffAt (hU.mem_nhds ⟨hρ, mem_univ _⟩)).isSymmSndFDerivAt (by simp)
  have hdfG : DifferentiableAt ℝ (fderiv ℝ G) (ρ, x) :=
    (hGU.contDiffAt (hU.mem_nhds ⟨hρ, mem_univ _⟩)).differentiableAt (by simp)
  have hspatial : pdCx k (fun y => fderiv ℝ G (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ))) x =
      fderiv ℝ (fderiv ℝ G) (ρ, x) ((0 : ℝ), B0579.dir k) ((1 : ℝ), (0 : ℝ × ℝ)) := by
    unfold pdCx
    have hl : HasFDerivAt (fun y : ℝ × ℝ => (ρ, y))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
      (hasFDerivAt_const ρ x).prodMk (hasFDerivAt_id x)
    let ev1 : (ℝ × (ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))
    have hc : HasFDerivAt (fun y => fderiv ℝ G (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ))) _ x :=
      (ev1.hasFDerivAt.comp (ρ, x) hdfG.hasFDerivAt).comp x hl
    rw [hc.fderiv]
    rfl
  have htime : HasDerivAt (fun r => fderiv ℝ G (r, x) ((0 : ℝ), B0579.dir k))
      (fderiv ℝ (fderiv ℝ G) (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) ((0 : ℝ), B0579.dir k)) ρ := by
    have hl : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
      (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
    let evk : (ℝ × (ℝ × ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)
    exact (evk.hasFDerivAt.comp (ρ, x) hdfG.hasFDerivAt).comp_hasDerivAt ρ hl
  rw [hspatial, ← hsymm ((1 : ℝ), (0 : ℝ × ℝ)) ((0 : ℝ), B0579.dir k)]
  refine htime.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hρ] with r hr
  exact hpd_eq r hr x

private lemma cut_ftc_identities {t₀ s R : ℝ} (hR : 0 < R) {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t₀ s ×ˢ univ))
    {τ r : ℝ} (hτ : τ ∈ Ioo t₀ s) (hr : r ∈ Ioo t₀ s) (hτr : τ ≤ r) (x : ℝ × ℝ) :
    (∫ ρ in τ..r, ((ladCut R x : ℂ) * ladDt φ ρ x) =
        ladCutPhi φ R r x - ladCutPhi φ R τ x) ∧
    (∀ k : Fin 2, ∫ ρ in τ..r, pdCx k (fun y => (ladCut R y : ℂ) * ladDt φ ρ y) x =
        pdCx k (ladCutPhi φ R r) x - pdCx k (ladCutPhi φ R τ) x) ∧
    (∫ ρ in τ..r, ladLapCx (fun y => (ladCut R y : ℂ) * ladDt φ ρ y) x =
        ladLapCx (ladCutPhi φ R r) x - ladLapCx (ladCutPhi φ R τ) x) := by
  let U : Set (ℝ × (ℝ × ℝ)) := Ioo t₀ s ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let Φ : ℝ × (ℝ × ℝ) → ℂ := fun p => φ p.1 p.2
  have hΦ : ContDiffOn ℝ ∞ Φ U := hφ.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hIoo : ∀ ρ ∈ uIcc τ r, ρ ∈ Ioo t₀ s := by
    intro ρ hρ
    rw [uIcc_of_le hτr] at hρ
    exact ⟨lt_of_lt_of_le hτ.1 hρ.1, lt_of_le_of_lt hρ.2 hr.2⟩
  obtain ⟨_, _, hKcut⟩ := ladCutProps
  have hχ : ContDiff ℝ ∞ (ladCut R) := ((hKcut R hR).1 1).smooth
  have hdt_sm : ∀ ρ ∈ Ioo t₀ s, ContDiff ℝ ∞ (ladDt φ ρ) := by
    intro ρ hρ
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU (by simp)
    have h2 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => fderiv ℝ Φ (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ))) :=
      ((ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))).contDiff.comp_contDiffOn h1).comp_contDiff
        (contDiff_const.prodMk contDiff_id) (fun y => ⟨hρ, mem_univ _⟩)
    have heq : ladDt φ ρ = fun y => fderiv ℝ Φ (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ)) :=
      funext fun y => LadPRDerivAux.ladDt_eq_fderiv hφ hρ y
    rwa [heq]
  have hd0 : ∀ ρ ∈ uIcc τ r, HasDerivAt (fun ρ' => φ ρ' x) (ladDt φ ρ x) ρ :=
    fun ρ hρ => LadPRDerivAux.hasDerivAt_phi hφ (hIoo ρ hρ) x
  have hc0 : ContinuousOn (fun ρ => ladDt φ ρ x) (uIcc τ r) :=
    (LadPRDerivAux.continuousOn_ladDt hφ).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
      (fun ρ hρ => ⟨hIoo ρ hρ, mem_univ _⟩)
  have hftc0 : ∫ ρ in τ..r, ladDt φ ρ x = φ r x - φ τ x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd0 hc0.intervalIntegrable
  have hd1 : ∀ (k : Fin 2), ∀ ρ ∈ uIcc τ r,
      HasDerivAt (fun ρ' => pdCx k (φ ρ') x) (pdCx k (ladDt φ ρ) x) ρ := by
    intro k ρ hρ
    have h := hasDerivAt_pdCx_of_contDiffOn hΦ (hIoo ρ hρ) k x
    have heq : ladDt φ ρ = fun y => fderiv ℝ Φ (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ)) :=
      funext fun y => LadPRDerivAux.ladDt_eq_fderiv hφ (hIoo ρ hρ) y
    rwa [heq]
  have hc1 : ∀ k : Fin 2, ContinuousOn (fun ρ => pdCx k (ladDt φ ρ) x) (uIcc τ r) := by
    intro k
    have h1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U := hΦ.fderiv_of_isOpen hU (by simp)
    let G₁ : ℝ × (ℝ × ℝ) → ℂ := fun p => fderiv ℝ Φ p ((1 : ℝ), (0 : ℝ × ℝ))
    have hG₁ : ContDiffOn ℝ ∞ G₁ U :=
      (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))).contDiff.comp_contDiffOn h1
    have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G₁ p ((0 : ℝ), B0579.dir k)) U :=
      ((ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).continuous).comp_continuousOn
        (hG₁.continuousOn_fderiv_of_isOpen hU (by simp))
    refine (h2.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
      (fun ρ hρ => ⟨hIoo ρ hρ, mem_univ _⟩)).congr fun ρ hρ => ?_
    have heq : ladDt φ ρ = fun y => G₁ (ρ, y) :=
      funext fun y => LadPRDerivAux.ladDt_eq_fderiv hφ (hIoo ρ hρ) y
    rw [heq]
    unfold pdCx
    have hd : DifferentiableAt ℝ G₁ (ρ, x) :=
      (hG₁.contDiffAt (hU.mem_nhds ⟨hIoo ρ hρ, mem_univ _⟩)).differentiableAt (by simp)
    have hl : HasFDerivAt (fun z : ℝ × ℝ => (ρ, z))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
      (hasFDerivAt_const ρ x).prodMk (hasFDerivAt_id x)
    have hcomp : HasFDerivAt (fun z => G₁ (ρ, z)) _ x := hd.hasFDerivAt.comp x hl
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    rfl
  have hftc1 : ∀ k : Fin 2, ∫ ρ in τ..r, pdCx k (ladDt φ ρ) x =
      pdCx k (φ r) x - pdCx k (φ τ) x :=
    fun k => intervalIntegral.integral_eq_sub_of_hasDerivAt (hd1 k) (hc1 k).intervalIntegrable
  have hd2 : ∀ (k : Fin 2), ∀ ρ ∈ uIcc τ r,
      HasDerivAt (fun ρ' => pdCx k (pdCx k (φ ρ')) x) (pdCx k (pdCx k (ladDt φ ρ)) x) ρ := by
    intro k ρ hρ
    let Gk : ℝ × (ℝ × ℝ) → ℂ := fun p => fderiv ℝ Φ p ((0 : ℝ), B0579.dir k)
    have hGk : ContDiffOn ℝ ∞ Gk U :=
      (ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).contDiff.comp_contDiffOn
        (hΦ.fderiv_of_isOpen hU (by simp))
    have hstep := hasDerivAt_pdCx_of_contDiffOn hGk (hIoo ρ hρ) k x
    have hGk_eq : ∀ r' ∈ Ioo t₀ s, (fun y => Gk (r', y)) = pdCx k (φ r') := by
      intro r' hr'; funext y; unfold pdCx Gk
      have hd : DifferentiableAt ℝ Φ (r', y) :=
        (hΦ.contDiffAt (hU.mem_nhds ⟨hr', mem_univ _⟩)).differentiableAt (by simp)
      have hl : HasFDerivAt (fun z : ℝ × ℝ => (r', z))
          ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
        (hasFDerivAt_const r' y).prodMk (hasFDerivAt_id y)
      have hcomp : HasFDerivAt (fun z => Φ (r', z)) _ y := hd.hasFDerivAt.comp y hl
      rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
    have hGk_dt : (fun y => fderiv ℝ Gk (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ))) = pdCx k (ladDt φ ρ) := by
      funext y
      have hdf : HasDerivAt (fun r' => Gk (r', y)) (fderiv ℝ Gk (ρ, y) ((1 : ℝ), (0 : ℝ × ℝ))) ρ := by
        have hd : DifferentiableAt ℝ Gk (ρ, y) :=
          (hGk.contDiffAt (hU.mem_nhds ⟨hIoo ρ hρ, mem_univ _⟩)).differentiableAt (by simp)
        have hl : HasDerivAt (fun r' : ℝ => (r', y)) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
          (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ y)
        exact hd.hasFDerivAt.comp_hasDerivAt ρ hl
      have hdf' : HasDerivAt (fun r' => Gk (r', y)) (pdCx k (ladDt φ ρ) y) ρ := by
        have h := hasDerivAt_pdCx_of_contDiffOn hΦ (hIoo ρ hρ) k y
        have heq : ladDt φ ρ = fun z => fderiv ℝ Φ (ρ, z) ((1 : ℝ), (0 : ℝ × ℝ)) :=
          funext fun z => LadPRDerivAux.ladDt_eq_fderiv hφ (hIoo ρ hρ) z
        rw [← heq] at h
        refine h.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioo.mem_nhds (hIoo ρ hρ)] with r' hr'
        exact congrFun (hGk_eq r' hr') y
      exact hdf.unique hdf'
    rw [hGk_dt] at hstep
    refine hstep.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (hIoo ρ hρ)] with r' hr'
    rw [← hGk_eq r' hr']
  have hc2 : ∀ k : Fin 2, ContinuousOn (fun ρ => pdCx k (pdCx k (ladDt φ ρ)) x) (uIcc τ r) := by
    intro k
    let G₁ : ℝ × (ℝ × ℝ) → ℂ := fun p => fderiv ℝ Φ p ((1 : ℝ), (0 : ℝ × ℝ))
    have hG₁ : ContDiffOn ℝ ∞ G₁ U :=
      (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))).contDiff.comp_contDiffOn
        (hΦ.fderiv_of_isOpen hU (by simp))
    let G₂ : ℝ × (ℝ × ℝ) → ℂ := fun p => fderiv ℝ G₁ p ((0 : ℝ), B0579.dir k)
    have hG₂ : ContDiffOn ℝ ∞ G₂ U :=
      (ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).contDiff.comp_contDiffOn
        (hG₁.fderiv_of_isOpen hU (by simp))
    have h3 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G₂ p ((0 : ℝ), B0579.dir k)) U :=
      ((ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).continuous).comp_continuousOn
        (hG₂.continuousOn_fderiv_of_isOpen hU (by simp))
    refine (h3.comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
      (fun ρ hρ => ⟨hIoo ρ hρ, mem_univ _⟩)).congr fun ρ hρ => ?_
    have heq : ladDt φ ρ = fun y => G₁ (ρ, y) :=
      funext fun y => LadPRDerivAux.ladDt_eq_fderiv hφ (hIoo ρ hρ) y
    have heq2 : pdCx k (ladDt φ ρ) = fun y => G₂ (ρ, y) := by
      funext y; rw [heq]; unfold pdCx G₂
      have hd : DifferentiableAt ℝ G₁ (ρ, y) :=
        (hG₁.contDiffAt (hU.mem_nhds ⟨hIoo ρ hρ, mem_univ _⟩)).differentiableAt (by simp)
      have hl : HasFDerivAt (fun z : ℝ × ℝ => (ρ, z))
          ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
        (hasFDerivAt_const ρ y).prodMk (hasFDerivAt_id y)
      have hcomp : HasFDerivAt (fun z => G₁ (ρ, z)) _ y := hd.hasFDerivAt.comp y hl
      rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
    rw [heq2]; unfold pdCx
    have hd : DifferentiableAt ℝ G₂ (ρ, x) :=
      (hG₂.contDiffAt (hU.mem_nhds ⟨hIoo ρ hρ, mem_univ _⟩)).differentiableAt (by simp)
    have hl : HasFDerivAt (fun z : ℝ × ℝ => (ρ, z))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
      (hasFDerivAt_const ρ x).prodMk (hasFDerivAt_id x)
    have hcomp : HasFDerivAt (fun z => G₂ (ρ, z)) _ x := hd.hasFDerivAt.comp x hl
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
  have hftc2 : ∀ k : Fin 2, ∫ ρ in τ..r, pdCx k (pdCx k (ladDt φ ρ)) x =
      pdCx k (pdCx k (φ r)) x - pdCx k (pdCx k (φ τ)) x :=
    fun k => intervalIntegral.integral_eq_sub_of_hasDerivAt (hd2 k) (hc2 k).intervalIntegrable
  refine ⟨?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_const_mul, hftc0]
    unfold ladCutPhi; ring
  · intro k
    have hp : ∀ ρ ∈ uIcc τ r,
        pdCx k (fun y => (ladCut R y : ℂ) * ladDt φ ρ y) x =
          (B0579.pd k (ladCut R) x : ℂ) * ladDt φ ρ x +
            (ladCut R x : ℂ) * pdCx k (ladDt φ ρ) x :=
      fun ρ hρ => RateSplitAux.pdCx_cut_mul hχ (hdt_sm ρ (hIoo ρ hρ)) k x
    rw [intervalIntegral.integral_congr hp,
      intervalIntegral.integral_add (hc0.intervalIntegrable.const_mul _)
        ((hc1 k).intervalIntegrable.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hftc0, hftc1 k]
    have e_r := RateSplitAux.pdCx_cut_mul hχ (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hr) hφ) k x
    have e_τ := RateSplitAux.pdCx_cut_mul hχ (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hτ) hφ) k x
    unfold ladCutPhi; rw [e_r, e_τ]; ring
  · have hp : ∀ ρ ∈ uIcc τ r,
        ladLapCx (fun y => (ladCut R y : ℂ) * ladDt φ ρ y) x =
          (ladCut R x : ℂ) * (pdCx 0 (pdCx 0 (ladDt φ ρ)) x + pdCx 1 (pdCx 1 (ladDt φ ρ)) x) +
            2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (ladDt φ ρ) x +
              (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (ladDt φ ρ) x) +
            (lapP (ladCut R) x : ℂ) * ladDt φ ρ x :=
      fun ρ hρ => RateSplitAux.lap_cut_mul hχ (hdt_sm ρ (hIoo ρ hρ)) x
    have iA : IntervalIntegrable
        (fun ρ => (ladCut R x : ℂ) *
          (pdCx 0 (pdCx 0 (ladDt φ ρ)) x + pdCx 1 (pdCx 1 (ladDt φ ρ)) x)) volume τ r :=
      ((hc2 0).intervalIntegrable.add (hc2 1).intervalIntegrable).const_mul _
    have iB : IntervalIntegrable
        (fun ρ => (2 : ℂ) * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (ladDt φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (ladDt φ ρ) x)) volume τ r :=
      (((hc1 0).intervalIntegrable.const_mul _).add
        ((hc1 1).intervalIntegrable.const_mul _)).const_mul _
    have iC : IntervalIntegrable
        (fun ρ => (lapP (ladCut R) x : ℂ) * ladDt φ ρ x) volume τ r :=
      hc0.intervalIntegrable.const_mul _
    rw [intervalIntegral.integral_congr hp,
      intervalIntegral.integral_add (iA.add iB) iC, intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hc2 0).intervalIntegrable (hc2 1).intervalIntegrable,
      intervalIntegral.integral_add ((hc1 0).intervalIntegrable.const_mul _)
        ((hc1 1).intervalIntegrable.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hftc2 0, hftc2 1, hftc1 0, hftc1 1, hftc0]
    have e_r := RateSplitAux.lap_cut_mul hχ (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hr) hφ) x
    have e_τ := RateSplitAux.lap_cut_mul hχ (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hτ) hφ) x
    unfold ladCutPhi; rw [e_r, e_τ]; unfold ladLapCx; ring

private lemma ae_prod_restrict_mem {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∀ᵐ p ∂(μ.restrict s).prod (ν.restrict t), p.1 ∈ s ∧ p.2 ∈ t :=
  (Measure.ae_prod_mem_iff_ae_ae_mem (hs.prod ht)).2
    ((ae_restrict_mem hs).mono fun _ hx => (ae_restrict_mem ht).mono fun _ hy => ⟨hx, hy⟩)

/-- Carathéodory measurability on a compact square `[t₁, r] ×ˢ [t₁, r]` via finite staircase
approximation in the first variable. -/
private lemma integrable_caratheodory_square {t₁ r : ℝ} (ht₁r : t₁ < r) {K : ℝ → ℝ → ℂ}
    (hmeas : ∀ ρ ∈ Icc t₁ r, AEStronglyMeasurable (K ρ) (volume.restrict (Icc t₁ r)))
    (hcont : ∀ τ ∈ Icc t₁ r, ContinuousOn (fun ρ => K ρ τ) (Icc t₁ r))
    {M : ℝ} (_hM : 0 ≤ M) (hbdd : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₁ r, ‖K ρ τ‖ ≤ M) :
    Integrable (Function.uncurry K)
      ((volume.restrict (Icc t₁ r)).prod (volume.restrict (Icc t₁ r))) := by
  let μI : Measure ℝ := volume.restrict (Icc t₁ r)
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  let a : ℕ → ℕ → ℝ := fun n k => t₁ + (k : ℝ) / ((n + 1 : ℕ) : ℝ) * (r - t₁)
  let slice : ∀ n : ℕ, Fin (n + 1) → Set ℝ := fun n k =>
    if (k : ℕ) = n then Icc (a n k) r else Ico (a n k) (a n (k + 1))
  have ha_mem : ∀ (n : ℕ) (k : Fin (n + 1)), a n k ∈ Icc t₁ r := by
    intro n k
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast k.isLt.le
    have hdiv0 : 0 ≤ (k : ℝ) / ((n + 1 : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg k) hn.le
    have hdiv1 : (k : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hn).2 hle
    exact ⟨by dsimp [a]; nlinarith, by dsimp [a]; nlinarith⟩
  let Fn : ℕ → ℝ × ℝ → ℂ := fun n p =>
    ∑ k : Fin (n + 1), ((slice n k).indicator (fun _ => (1 : ℝ)) p.1 : ℂ) * K (a n k) p.2
  have hFn_meas : ∀ n, AEStronglyMeasurable (Fn n) (μI.prod μI) := by
    intro n
    have hFn_sum : Fn n = ∑ k ∈ (Finset.univ : Finset (Fin (n + 1))), fun p : ℝ × ℝ =>
        ((slice n k).indicator (fun _ => (1 : ℝ)) p.1 : ℂ) * K (a n k) p.2 := by
      ext p; simp [Fn]
    rw [hFn_sum]
    refine Finset.aestronglyMeasurable_sum Finset.univ fun k _ => ?_
    have hms : MeasurableSet (slice n k) := by
      dsimp [slice]; split_ifs <;> [exact measurableSet_Icc; exact measurableSet_Ico]
    have h1 : Measurable (fun p : ℝ × ℝ => ((slice n k).indicator (fun _ => (1 : ℝ)) p.1 : ℂ)) :=
      ((measurable_const : Measurable fun _ : ℝ => ((1 : ℝ) : ℂ)).indicator hms).comp measurable_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => K (a n k) p.2) (μI.prod μI) :=
      (hmeas (a n k) (ha_mem n k)).comp_snd
    exact h1.aestronglyMeasurable.mul h2
  have hae_mem : ∀ᵐ p ∂(μI.prod μI), p.1 ∈ Icc t₁ r ∧ p.2 ∈ Icc t₁ r :=
    ae_prod_restrict_mem measurableSet_Icc measurableSet_Icc
  have htend : ∀ᵐ p ∂(μI.prod μI), Tendsto (fun n => Fn n p) atTop (𝓝 (Function.uncurry K p)) := by
    filter_upwards [hae_mem] with p ⟨hp1, hp2⟩
    have hex : ∀ n : ℕ, ∃ k : Fin (n + 1), p.1 ∈ slice n k ∧
        ∀ j : Fin (n + 1), j ≠ k → p.1 ∉ slice n j := by
      intro n
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      let t_scaled : ℝ := (p.1 - t₁) / (r - t₁) * ((n + 1 : ℕ) : ℝ)
      let m_idx : ℕ := min ⌊t_scaled⌋₊ n
      have hm_lt : m_idx < n + 1 := Nat.lt_succ_of_le (min_le_right _ _)
      refine ⟨⟨m_idx, hm_lt⟩, ?_, ?_⟩
      · have ht0 : 0 ≤ t_scaled := by
          dsimp [t_scaled]
          exact mul_nonneg (div_nonneg (by linarith [hp1.1]) (by linarith)) hn.le
        have hfl_le : (⌊t_scaled⌋₊ : ℝ) ≤ t_scaled := Nat.floor_le ht0
        have hm_le : (m_idx : ℝ) ≤ t_scaled :=
          le_trans (by exact_mod_cast min_le_left ⌊t_scaled⌋₊ n) hfl_le
        have hlow : a n m_idx ≤ p.1 := by
          dsimp [a, t_scaled] at hm_le ⊢
          have hdr : 0 < r - t₁ := by linarith
          have h1 := (le_div_iff₀ hdr).1 ((div_le_iff₀ hn).2 hm_le)
          linarith
        dsimp [slice]
        split_ifs with hmn
        · exact ⟨hlow, hp1.2⟩
        · refine ⟨hlow, ?_⟩
          have hlt_n : ⌊t_scaled⌋₊ < n := by
            by_contra hge
            exact hmn (min_eq_right (not_lt.1 hge))
          have hmeq : m_idx = ⌊t_scaled⌋₊ := min_eq_left hlt_n.le
          have hfl_lt : t_scaled < (m_idx : ℝ) + 1 := by
            rw [hmeq]; exact_mod_cast Nat.lt_floor_add_one t_scaled
          dsimp [a, t_scaled] at hfl_lt ⊢
          have hdr : 0 < r - t₁ := by linarith
          have h2 : (p.1 - t₁) / (r - t₁) < ((m_idx + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
            rw [lt_div_iff₀ hn]; push_cast at hfl_lt ⊢; linarith
          have h3 := (div_lt_iff₀ hdr).1 h2
          linarith
      · intro j hj hmem
        have hmono : ∀ u v : ℕ, u ≤ v → a n u ≤ a n v := by
          intro u v huv; dsimp [a]
          have hn' : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
          have h1 : (u : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ (v : ℝ) / ((n + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast huv) hn'
          nlinarith [mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 ht₁r.le)]
        have h_in_k : a n m_idx ≤ p.1 ∧ (m_idx = n → p.1 ≤ r) ∧ (m_idx ≠ n → p.1 < a n (m_idx + 1)) := by
          have ht0 : 0 ≤ t_scaled :=
            mul_nonneg (div_nonneg (by linarith [hp1.1]) (by linarith)) hn.le
          have hm_le : (m_idx : ℝ) ≤ t_scaled :=
            le_trans (by exact_mod_cast min_le_left ⌊t_scaled⌋₊ n) (Nat.floor_le ht0)
          have hdr : 0 < r - t₁ := by linarith
          have hlow : a n m_idx ≤ p.1 := by
            dsimp [a, t_scaled] at hm_le ⊢
            have h1 := (le_div_iff₀ hdr).1 ((div_le_iff₀ hn).2 hm_le)
            linarith
          refine ⟨hlow, fun _ => hp1.2, fun hmn => ?_⟩
          have hlt_n : ⌊t_scaled⌋₊ < n := by
            by_contra hge; exact hmn (min_eq_right (not_lt.1 hge))
          have hmeq : m_idx = ⌊t_scaled⌋₊ := min_eq_left hlt_n.le
          have hfl_lt : t_scaled < (m_idx : ℝ) + 1 := by
            rw [hmeq]; exact_mod_cast Nat.lt_floor_add_one t_scaled
          dsimp [a, t_scaled] at hfl_lt ⊢
          have h2 : (p.1 - t₁) / (r - t₁) < ((m_idx + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
            rw [lt_div_iff₀ hn]; push_cast at hfl_lt ⊢; linarith
          have h3 := (div_lt_iff₀ hdr).1 h2
          linarith
        rcases lt_trichotomy (j : ℕ) m_idx with hlt | heq | hgt
        · have hjne : (j : ℕ) ≠ n := by omega
          dsimp [slice] at hmem; simp only [hjne, ↓reduceIte] at hmem
          have := hmono (j + 1) m_idx hlt
          linarith [hmem.2, h_in_k.1]
        · exact hj (Fin.ext heq)
        · have hmne : m_idx ≠ n := by have := j.isLt; omega
          have h1 := h_in_k.2.2 hmne
          have h2 := hmono (m_idx + 1) j hgt
          dsimp [slice] at hmem; split_ifs at hmem <;> linarith [hmem.1]
    choose kn hkn_in hkn_out using hex
    have hFn_eq : ∀ n, Fn n p = K (a n (kn n)) p.2 := by
      intro n
      dsimp [Fn]
      rw [Finset.sum_eq_single (kn n)]
      · rw [Set.indicator_of_mem (hkn_in n)]; simp
      · intro j _ hj; rw [Set.indicator_of_notMem (hkn_out n j hj)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hFn_eq]
    have hakn_tend : Tendsto (fun n => a n (kn n)) atTop (𝓝 p.1) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt ((r - t₁) / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hmem := hkn_in n
      have hdist : |a n (kn n) - p.1| ≤ (r - t₁) / ((n + 1 : ℕ) : ℝ) := by
        dsimp [slice] at hmem
        split_ifs at hmem with hk
        · have han : a n n = r - (r - t₁) / ((n + 1 : ℕ) : ℝ) := by
            dsimp [a]; push_cast; field_simp; ring
          rw [hk, han] at hmem ⊢
          rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2]
        · have hstep : a n (kn n + 1) - a n (kn n) = (r - t₁) / ((n + 1 : ℕ) : ℝ) := by
            dsimp [a]; push_cast; field_simp; ring
          rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2, hstep]
      rw [Real.dist_eq]
      refine lt_of_le_of_lt hdist ?_
      rw [div_lt_iff₀ hn1]
      have hN' : r - t₁ < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
      have hle : (N : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
      nlinarith
    exact (hcont p.2 hp2 p.1 hp1).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hakn_tend
        (Eventually.of_forall fun n => ha_mem n (kn n)))
  have haesm : AEStronglyMeasurable (Function.uncurry K) (μI.prod μI) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFn_meas htend
  refine Integrable.of_bound haesm M ?_
  filter_upwards [hae_mem] with p ⟨hp1, hp2⟩
  exact hbdd p.1 hp1 p.2 hp2


/-- Complexified weak identity on sub-intervals `[t₁, ρ] ⊆ [t₁, r] ⊂ (t₀, s)`. -/
private lemma weak_cx_sub_interval {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t₀ S s t₁ r : ℝ} (hsS : s ≤ S) (ht₁ : t₀ < t₁) (ht₁r : t₁ < r) (hrs : r < s)
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hom : ∀ τ ∈ Icc t₀ S, MemLp (om τ) 2 (B0579.cellMeasure c m))
    (hwk : ∀ ψ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc t₀ S,
      IntegrableOn (flowIntegrand tr (om τ) (u τ) τ ψ) (B0579.cell c) ∧
      IntervalIntegrable (fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x)
        volume t₀ τ ∧
      ∫ x in B0579.cell c, om τ x * (ψ x : ℂ) =
        ∫ σ in t₀..τ, ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x)
    (F : ℝ × ℝ → ℂ)
    (hFre : B0579.IsCylTest c (fun x => (F x).re))
    (hFim : B0579.IsCylTest c (fun x => (F x).im))
    {ρ : ℝ} (hρ : ρ ∈ Icc t₁ r) :
    (∀ τ ∈ Icc t₀ S, IntegrableOn (ladFlowCx tr (om τ) (u τ) τ F) (B0579.cell c)) ∧
    IntervalIntegrable (fun τ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x)
      volume t₁ ρ ∧
    (∫ x in B0579.cell c, om ρ x * F x) - (∫ x in B0579.cell c, om t₁ x * F x) =
      ∫ τ in t₁..ρ, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x := by
  have hI_sub_S : Icc t₁ r ⊆ Icc t₀ S := fun σ hσ =>
    ⟨ht₁.le.trans hσ.1, (hσ.2.trans hrs.le).trans hsS⟩
  have hF_eq : F = fun y => (((F y).re : ℝ) : ℂ) + (((F y).im : ℝ) : ℂ) * Complex.I := by
    funext y; exact (Complex.re_add_im (F y)).symm
  have hfl_eq : ∀ τ, ladFlowCx tr (om τ) (u τ) τ F =
      fun x => flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).re) x +
        flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).im) x * Complex.I := by
    intro τ; funext x
    conv_lhs => rw [hF_eq]
    exact LadPRWeakAux.ladFlow_split tr (om τ) (u τ) τ hFre hFim x
  have hint_cell : ∀ τ ∈ Icc t₀ S, IntegrableOn (ladFlowCx tr (om τ) (u τ) τ F) (B0579.cell c) := by
    intro τ hτ; rw [hfl_eq τ]
    exact (hwk _ hFre τ hτ).1.add ((hwk _ hFim τ hτ).1.mul_const Complex.I)
  have hint_int : ∀ τ ∈ Icc t₀ S,
      ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x =
        (∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).re) x) +
          (∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).im) x) *
            Complex.I := by
    intro τ hτ; rw [hfl_eq τ, integral_add (hwk _ hFre τ hτ).1
      ((hwk _ hFim τ hτ).1.mul_const Complex.I), integral_mul_const]
  have hρS : ρ ∈ Icc t₀ S := hI_sub_S hρ
  have ht₁S : t₁ ∈ Icc t₀ S := hI_sub_S ⟨le_rfl, ht₁r.le⟩
  have huIcc_sub : uIcc t₁ ρ ⊆ uIcc t₀ ρ := by
    rw [uIcc_of_le hρ.1, uIcc_of_le (ht₁.le.trans hρ.1)]
    exact Icc_subset_Icc ht₁.le le_rfl
  have hii_re : IntervalIntegrable
      (fun τ => ∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).re) x)
      volume t₁ ρ :=
    (hwk _ hFre ρ hρS).2.1.mono_set huIcc_sub
  have hii_im : IntervalIntegrable
      (fun τ => ∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).im) x)
      volume t₁ ρ :=
    (hwk _ hFim ρ hρS).2.1.mono_set huIcc_sub
  have hii : IntervalIntegrable
      (fun τ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x) volume t₁ ρ := by
    refine (hii_re.add (hii_im.mul_const Complex.I)).congr fun τ hτ => ?_
    rw [uIoc_of_le hρ.1] at hτ
    exact (hint_int τ (hI_sub_S ⟨hτ.1.le, hτ.2.trans hρ.2⟩)).symm
  refine ⟨hint_cell, hii, ?_⟩
  have hpair : ∀ τ ∈ Icc t₀ S,
      ∫ x in B0579.cell c, om τ x * F x =
        (∫ x in B0579.cell c, om τ x * (((F x).re : ℝ) : ℂ)) +
          (∫ x in B0579.cell c, om τ x * (((F x).im : ℝ) : ℂ)) * Complex.I := by
    intro τ hτ
    have hbdd_cyl : ∀ g : ℝ × ℝ → ℝ, B0579.IsCylTest c g →
        IntegrableOn (fun x => om τ x * (g x : ℂ)) (B0579.cell c) := by
      intro g hg
      obtain ⟨Bg, hBg⟩ := hg.band
      exact RateSplitAux.integrableOn_w_mul c m (max Bg 1) (hom τ hτ)
        (Complex.continuous_ofReal.comp hg.continuous) fun x hx => by
          have h0 : 0 < max Bg 1 := lt_of_lt_of_le one_pos (le_max_right Bg 1)
          have : Bg < |x.2| := lt_of_le_of_lt ((le_max_left Bg 1).trans (by linarith)) hx
          simp [hBg x this]
    have ire := hbdd_cyl _ hFre
    have iim := hbdd_cyl _ hFim
    have hp : (fun x => om τ x * F x) =
        fun x => om τ x * (((F x).re : ℝ) : ℂ) + (om τ x * (((F x).im : ℝ) : ℂ)) * Complex.I := by
      funext x; conv_lhs => rw [hF_eq]; ring
    rw [hp, integral_add ire (iim.mul_const Complex.I), integral_mul_const]
  rw [hpair ρ hρS, hpair t₁ ht₁S, (hwk _ hFre ρ hρS).2.2, (hwk _ hFim ρ hρS).2.2,
    (hwk _ hFre t₁ ht₁S).2.2, (hwk _ hFim t₁ ht₁S).2.2]
  have hsub_re := intervalIntegral.integral_add_adjacent_intervals
    (hwk _ hFre t₁ ht₁S).2.1 hii_re
  have hsub_im := intervalIntegral.integral_add_adjacent_intervals
    (hwk _ hFim t₁ ht₁S).2.1 hii_im
  have hcong : ∫ τ in t₁..ρ, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x =
      (∫ τ in t₁..ρ, ∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).re) x) +
        (∫ τ in t₁..ρ, ∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).im) x) *
          Complex.I := by
    have h1 : ∫ τ in t₁..ρ, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x =
        ∫ τ in t₁..ρ, ((∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).re) x) +
          (∫ x in B0579.cell c, flowIntegrand tr (om τ) (u τ) τ (fun y => (F y).im) x) *
            Complex.I) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [uIcc_of_le hρ.1] at hτ
        exact hint_int τ (hI_sub_S ⟨hτ.1, hτ.2.trans hρ.2⟩)
    rw [h1, intervalIntegral.integral_add hii_re (hii_im.mul_const Complex.I),
      intervalIntegral.integral_mul_const]
  rw [hcong]
  linear_combination -hsub_re - Complex.I * hsub_im

/-- Joint continuity on `Icc t₁ r ×ˢ B` of `G`, `pdCx k G`, and `ladLapCx G`. -/
private lemma jet_contOn_compact {t₀ s t₁ r : ℝ} (ht₁ : t₀ < t₁) (hrs : r < s)
    (B : Set (ℝ × ℝ)) {G : ℝ × (ℝ × ℝ) → ℂ}
    (hG : ContDiffOn ℝ ∞ G (Ioo t₀ s ×ˢ univ)) :
    ContinuousOn G (Icc t₁ r ×ˢ B) ∧
    (∀ k : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (fun y => G (p.1, y)) p.2)
      (Icc t₁ r ×ˢ B)) ∧
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladLapCx (fun y => G (p.1, y)) p.2)
      (Icc t₁ r ×ˢ B) := by
  let U : Set (ℝ × (ℝ × ℝ)) := Ioo t₀ s ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hI_sub_Ioo : Icc t₁ r ⊆ Ioo t₀ s := fun ρ hρ => ⟨lt_of_lt_of_le ht₁ hρ.1, lt_of_le_of_lt hρ.2 hrs⟩
  have hsub : Icc t₁ r ×ˢ B ⊆ U := fun p hp => ⟨hI_sub_Ioo hp.1, mem_univ _⟩
  have hcG : ContinuousOn G (Icc t₁ r ×ˢ B) := hG.continuousOn.mono hsub
  have hcpd : ∀ k : Fin 2,
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (fun y => G (p.1, y)) p.2) (Icc t₁ r ×ˢ B) := by
    intro k
    have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ G p ((0 : ℝ), B0579.dir k)) U :=
      ((ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).continuous).comp_continuousOn
        (hG.continuousOn_fderiv_of_isOpen hU (by simp))
    refine (h1.mono hsub).congr fun p hp => ?_
    unfold pdCx
    have hd : DifferentiableAt ℝ G p :=
      (hG.contDiffAt (hU.mem_nhds (hsub hp))).differentiableAt (by simp)
    have hl : HasFDerivAt (fun z : ℝ × ℝ => (p.1, z))
        ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    have hcomp : HasFDerivAt (fun z => G (p.1, z)) _ p.2 := hd.hasFDerivAt.comp p.2 hl
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
  have hclap : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ladLapCx (fun y => G (p.1, y)) p.2)
      (Icc t₁ r ×ˢ B) := by
    have hcp2 : ∀ k : Fin 2,
        ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (pdCx k (fun y => G (p.1, y))) p.2)
          (Icc t₁ r ×ˢ B) := by
      intro k
      let Gk : ℝ × (ℝ × ℝ) → ℂ := fun p => fderiv ℝ G p ((0 : ℝ), B0579.dir k)
      have hGk : ContDiffOn ℝ ∞ Gk U :=
        (ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).contDiff.comp_contDiffOn
          (hG.fderiv_of_isOpen hU (by simp))
      have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Gk p ((0 : ℝ), B0579.dir k)) U :=
        ((ContinuousLinearMap.apply ℝ ℂ ((0 : ℝ), B0579.dir k)).continuous).comp_continuousOn
          (hGk.continuousOn_fderiv_of_isOpen hU (by simp))
      refine (h1.mono hsub).congr fun p hp => ?_
      have heq : pdCx k (fun y => G (p.1, y)) = fun y => Gk (p.1, y) := by
        funext y; unfold pdCx Gk
        have hd : DifferentiableAt ℝ G (p.1, y) :=
          (hG.contDiffAt (hU.mem_nhds (show (p.1, y) ∈ U from
            ⟨hI_sub_Ioo hp.1, mem_univ y⟩))).differentiableAt (by simp)
        have hl : HasFDerivAt (fun z : ℝ × ℝ => (p.1, z))
            ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
          (hasFDerivAt_const p.1 y).prodMk (hasFDerivAt_id y)
        have hcomp : HasFDerivAt (fun z => G (p.1, z)) _ y := hd.hasFDerivAt.comp y hl
        rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
      rw [heq]; unfold pdCx
      have hd : DifferentiableAt ℝ Gk p :=
        (hGk.contDiffAt (hU.mem_nhds (hsub hp))).differentiableAt (by simp)
      have hl : HasFDerivAt (fun z : ℝ × ℝ => (p.1, z))
          ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
        (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
      have hcomp := hd.hasFDerivAt.comp p.2 hl
      change HasFDerivAt (fun z => Gk (p.1, z)) _ p.2 at hcomp
      rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
    exact (hcp2 0).add (hcp2 1)
  exact ⟨hcG, hcpd, hclap⟩

/-- Joint continuity on `Icc t₁ r ×ˢ B` of `tr.v` and `pd j (Ec tr)`. -/
private lemma train_ec_contOn_compact {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t₀ t₁ r : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : t₀ < t₁) (B : Set (ℝ × ℝ)) :
    (∀ j : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j) (Icc t₁ r ×ˢ B)) ∧
    (∀ j : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (UnforcedLeray.B0238.Ec tr p.1) p.2)
      (Icc t₁ r ×ˢ B)) := by
  have htr_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v
  have hsub_tr : Icc t₁ r ×ˢ B ⊆ Ici 0 ×ˢ univ :=
    fun p hp => ⟨ht₀.trans (ht₁.le.trans hp.1.1), mem_univ _⟩
  have hv_cont : ∀ j : Fin 2, ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 j) (Icc t₁ r ×ˢ B) :=
    fun j => ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp_continuousOn
      (htr_sm.continuousOn.mono hsub_tr))
  refine ⟨hv_cont, fun j => ?_⟩
  have hUpos : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hsub_pos : Icc t₁ r ×ˢ B ⊆ Ioi 0 ×ˢ univ :=
    fun p hp => ⟨lt_of_le_of_lt ht₀ (lt_of_lt_of_le ht₁ hp.1.1), mem_univ _⟩
  have htr_pos : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ioi 0 ×ˢ univ) :=
    htr_sm.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  let vi : Fin 2 → ℝ × (ℝ × ℝ) → ℝ := fun i p => tr.v p.1 p.2 i
  have hvi_sm : ∀ i, ContDiffOn ℝ ∞ (vi i) (Ioi 0 ×ˢ univ) := fun i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn htr_pos
  let Dv : Fin 2 → Fin 2 → ℝ × (ℝ × ℝ) → ℝ := fun k i p =>
    fderiv ℝ (vi i) p ((0 : ℝ), B0579.dir k)
  have hDv_sm : ∀ k i, ContDiffOn ℝ ∞ (Dv k i) (Ioi 0 ×ˢ univ) := fun k i =>
    ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), B0579.dir k)).contDiff).comp_contDiffOn
      ((hvi_sm i).fderiv_of_isOpen hUpos (by simp))
  let Ec_p : ℝ × (ℝ × ℝ) → ℝ := fun p => Dv 0 1 p - Dv 1 0 p
  have hEc_sm : ContDiffOn ℝ ∞ Ec_p (Ioi 0 ×ˢ univ) := (hDv_sm 0 1).sub (hDv_sm 1 0)
  have hEc_eq : ∀ τ > 0, ∀ y : ℝ × ℝ, UnforcedLeray.B0238.Ec tr τ y = Ec_p (τ, y) := by
    intro τ hτ0 y
    have hv1 : ContDiff ℝ 1 (tr.v τ) :=
      (UnforcedLeray.B0238.contDiff_Vc tr hτ0.le).of_le (by simp)
    unfold UnforcedLeray.B0238.Ec
    rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 y]
    have hcomp_i : ∀ i k : Fin 2,
        fderiv ℝ (fun w => tr.v τ w i) y (B0579.dir k) = Dv k i (τ, y) := by
      intro i k
      have hd : DifferentiableAt ℝ (vi i) (τ, y) :=
        ((hvi_sm i).contDiffAt (hUpos.mem_nhds (show (τ, y) ∈ Ioi 0 ×ˢ univ from
          ⟨hτ0, mem_univ y⟩))).differentiableAt (by simp)
      have hl : HasFDerivAt (fun z : ℝ × ℝ => (τ, z))
          ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
        (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
      have hcomp := hd.hasFDerivAt.comp y hl
      change HasFDerivAt (fun w => tr.v τ w i) _ y at hcomp
      rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl
    have d0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
    have d1 : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := rfl
    rw [← d0, ← d1, hcomp_i 1 0, hcomp_i 0 1]
  have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Ec_p p ((0 : ℝ), B0579.dir j))
      (Ioi 0 ×ˢ univ) :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), B0579.dir j)).continuous).comp_continuousOn
      (hEc_sm.continuousOn_fderiv_of_isOpen hUpos (by simp))
  refine (h1.mono hsub_pos).congr fun p hp => ?_
  have hτ0 : 0 < p.1 := (hsub_pos hp).1
  have heq : UnforcedLeray.B0238.Ec tr p.1 = fun y => Ec_p (p.1, y) :=
    funext fun y => hEc_eq p.1 hτ0 y
  rw [heq]; unfold B0579.pd
  have hd : DifferentiableAt ℝ Ec_p p :=
    (hEc_sm.contDiffAt (hUpos.mem_nhds (hsub_pos hp))).differentiableAt (by simp)
  have hl : HasFDerivAt (fun z : ℝ × ℝ => (p.1, z))
      ((0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hcomp := hd.hasFDerivAt.comp p.2 hl
  change HasFDerivAt (fun z => Ec_p (p.1, z)) _ p.2 at hcomp
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]; rfl

/-- Carathéodory continuity in `ρ` and uniform bound on `[t₁, r]²` for cell integrals of `ladFlowCx`. -/
private lemma flow_family_caratheodory {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t₀ S s t₁ r R M_om : ℝ} (hc1 : 1 ≤ c) (ht₀ : 0 ≤ t₀) (hsS : s ≤ S)
    (ht₁ : t₀ < t₁) (hrs : r < s) (hM_om : 0 ≤ M_om) (hm : 8 < m)
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hom : ∀ τ ∈ Icc t₀ S, MemLp (om τ) 2 (B0579.cellMeasure c m) ∧
      HasZeroCirculation c (om τ) ∧ (xNorm c m (om τ)).toReal ≤ M_om)
    (hu : ∀ τ ∈ Icc t₀ S, IsBiotSavart c (om τ) (u τ))
    (G : ℝ → ℝ × ℝ → ℂ)
    (hG_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) (Ioo t₀ s ×ˢ univ))
    (hG_supp : ∀ ρ ∈ Icc t₁ r, ∀ x : ℝ × ℝ, 2 * R < |x.2| →
      G ρ x = 0 ∧ pdCx 0 (G ρ) x = 0 ∧ pdCx 1 (G ρ) x = 0 ∧ ladLapCx (G ρ) x = 0)
    (hG_int : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₀ S,
      IntegrableOn (ladFlowCx tr (om τ) (u τ) τ (G ρ)) (B0579.cell c)) :
    (∀ τ ∈ Icc t₁ r, ContinuousOn
      (fun ρ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (G ρ) x) (Icc t₁ r)) ∧
    ∃ M_G ≥ 0, ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₁ r,
      ‖∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (G ρ) x‖ ≤ M_G := by
  have hI_sub_S : Icc t₁ r ⊆ Icc t₀ S := fun σ hσ =>
    ⟨ht₁.le.trans hσ.1, (hσ.2.trans hrs.le).trans hsS⟩
  let B : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hIBc : IsCompact (Icc t₁ r ×ˢ B) := isCompact_Icc.prod hBc
  have hcell_sub : ∀ x ∈ B0579.cell c, |x.2| ≤ 2 * R → x ∈ B :=
    fun x hx h2 => ⟨⟨hx.1.1, hx.1.2.le⟩, abs_le.1 h2⟩
  obtain ⟨C_bs, hC_bs⟩ := ladBSBound m hm
  have hC_bs0 : 0 ≤ max C_bs 0 := le_max_right _ _
  have h_u_nrm : ∀ τ ∈ Icc t₁ r, ∀ j : Fin 2,
      (eLpNorm (fun x => u τ x j) 2 (volume.restrict (B0579.cell c))).toReal ≤
        max C_bs 0 * M_om := by
    intro τ hτ j
    have hτS := hI_sub_S hτ
    have hb := hC_bs c hc1 (om τ) (hom τ hτS).1 (hom τ hτS).2.1 (u τ) (hu τ hτS) j
    have hb' : eLpNorm (fun x => u τ x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (max C_bs 0) * xNorm c m (om τ) :=
      hb.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le)
    have hfin := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := max C_bs 0)) (hom τ hτS).1.2.ne
    have htr := ENNReal.toReal_mono hfin hb'
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_bs0] at htr
    exact htr.trans (mul_le_mul_of_nonneg_left (hom τ hτS).2.2 hC_bs0)
  let JB1 : ℝ × ℝ → ℂ := fun _ => 1
  have hJB1 : MemLp JB1 2 (B0579.cellMeasure c (-m)) := by
    refine ⟨aestronglyMeasurable_const, ?_⟩
    rw [T06.eLpNorm_two_eq_lintegral]
    have hI := CellIntAux.integrable_jb_neg (c := c) (m := m) (by linarith)
    have hlt : ∫⁻ x, ‖JB1 x‖ₑ ^ 2 ∂(B0579.cellMeasure c (-m)) < ⊤ := by
      rw [B0579.cellMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (B0579.measurable_density (-m)).coe_nnreal_ennreal
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
      have heq : ((fun x : ℝ × ℝ => ((B0579.density (-m) x : ℝ≥0) : ℝ≥0∞)) *
          fun x => ‖JB1 x‖ₑ ^ 2) = fun x => ENNReal.ofReal (B0579.jb x ^ (-m)) := by
        funext x; simp [Pi.mul_apply, JB1, T06.density_coe]
      rw [heq]
      exact (hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun x => Real.rpow_nonneg (B0579.jb_pos x).le _)).1 hI.2
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne
  have h_om_L1 : ∀ τ ∈ Icc t₁ r,
      ∫ x in B0579.cell c, ‖om τ x‖ ≤
        M_om * (eLpNorm JB1 2 (B0579.cellMeasure c (-m))).toReal := by
    intro τ hτ
    have hτS := hI_sub_S hτ
    have hcs := RateBoundAux.cs_norm c m (hom τ hτS).1 hJB1
    simp only [JB1, norm_one, mul_one] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right (hom τ hτS).2.2 ENNReal.toReal_nonneg)
  have hB_ind : MemLp (B.indicator (fun _ : ℝ × ℝ => (1 : ℂ))) 2 (volume.restrict (B0579.cell c)) :=
    memLp_indicator_const 2 hBc.measurableSet (1 : ℂ)
      (Or.inr (ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hBc.measure_lt_top)))
  have h_u_L1 : ∀ τ ∈ Icc t₁ r, ∀ j : Fin 2,
      ∫ x in B0579.cell c, B.indicator (fun y => ‖u τ y j‖) x ≤
        max C_bs 0 * M_om *
          (eLpNorm (B.indicator (fun _ : ℝ × ℝ => (1 : ℂ))) 2
            (volume.restrict (B0579.cell c))).toReal := by
    intro τ hτ j
    have hτS := hI_sub_S hτ
    let F_u := ((hu τ hτS).1 j).norm.toLp _
    let F_B := hB_ind.norm.toLp _
    have hcs : ∫ x, F_u x * F_B x ∂(volume.restrict (B0579.cell c)) ≤ ‖F_u‖ * ‖F_B‖ := by
      simpa [MeasureTheory.L2.inner_def, Real.inner_apply, mul_comm] using
        real_inner_le_norm F_u F_B
    have heq : ∫ x in B0579.cell c, B.indicator (fun y => ‖u τ y j‖) x =
        ∫ x, F_u x * F_B x ∂(volume.restrict (B0579.cell c)) := by
      refine integral_congr_ae ?_
      filter_upwards [((hu τ hτS).1 j).norm.coeFn_toLp, hB_ind.norm.coeFn_toLp] with x hux hBx
      rw [hux, hBx]
      by_cases hx : x ∈ B <;> simp [hx]
    rw [heq]
    have hn1 : ‖F_u‖ = (eLpNorm (fun x => u τ x j) 2 (volume.restrict (B0579.cell c))).toReal := by
      rw [Lp.norm_toLp, eLpNorm_norm]
    have hn2 : ‖F_B‖ = (eLpNorm (B.indicator (fun _ : ℝ × ℝ => (1 : ℂ))) 2
        (volume.restrict (B0579.cell c))).toReal := by
      rw [Lp.norm_toLp, eLpNorm_norm]
    rw [hn1, hn2] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right (h_u_nrm τ hτ j) ENNReal.toReal_nonneg)
  have hJG := jet_contOn_compact ht₁ hrs B hG_sm
  obtain ⟨hv_cont, hpdE_cont⟩ := train_ec_contOn_compact tr ht₀ ht₁ B
  let A_om : ℝ → ℝ → ℝ × ℝ → ℂ := fun ρ τ x =>
    (ν : ℂ) * ladLapCx (G ρ) x + ladTransport tr τ (G ρ) x
  have hA_cont : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => A_om q.1.1 q.1.2 q.2)
      ((Icc t₁ r ×ˢ Icc t₁ r) ×ˢ B) := by
    have cL : ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => ladLapCx (G q.1.1) q.2)
        ((Icc t₁ r ×ˢ Icc t₁ r) ×ˢ B) :=
      hJG.2.2.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun q hq => ⟨hq.1.1, hq.2⟩)
    have cp : ∀ k : Fin 2, ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => pdCx k (G q.1.1) q.2)
        ((Icc t₁ r ×ˢ Icc t₁ r) ×ˢ B) :=
      fun k => (hJG.2.1 k).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun q hq => ⟨hq.1.1, hq.2⟩)
    have cv : ∀ k : Fin 2, ContinuousOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (tr.v q.1.2 q.2 k : ℂ))
        ((Icc t₁ r ×ˢ Icc t₁ r) ×ˢ B) :=
      fun k => Complex.continuous_ofReal.comp_continuousOn
        ((hv_cont k).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun q hq => ⟨hq.1.2, hq.2⟩))
    exact (continuousOn_const.mul cL).add (((cv 0).mul (cp 0)).add ((cv 1).mul (cp 1)))
  have hI2Bc : IsCompact ((Icc t₁ r ×ˢ Icc t₁ r) ×ˢ B) := (isCompact_Icc.prod isCompact_Icc).prod hBc
  obtain ⟨MA, hMA⟩ := hI2Bc.exists_bound_of_continuousOn hA_cont
  obtain ⟨MG0, hMG0⟩ := hIBc.exists_bound_of_continuousOn hJG.1
  obtain ⟨ME0, hME0⟩ := hIBc.exists_bound_of_continuousOn (hpdE_cont 0)
  obtain ⟨ME1, hME1⟩ := hIBc.exists_bound_of_continuousOn (hpdE_cont 1)
  let CA : ℝ := |MA|
  let CB : ℝ := (|ME0| + |ME1|) * |MG0|
  have hpt_bd : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₁ r, ∀ x ∈ B0579.cell c,
      ‖ladFlowCx tr (om τ) (u τ) τ (G ρ) x‖ ≤
        CA * ‖om τ x‖ + CB * (B.indicator (fun y => ‖u τ y 0‖) x +
          B.indicator (fun y => ‖u τ y 1‖) x) := by
    intro ρ hρ τ hτ x hx
    by_cases hband : |x.2| ≤ 2 * R
    · have hxB : x ∈ B := hcell_sub x hx hband
      have h1 : ‖A_om ρ τ x‖ ≤ CA := (hMA ((ρ, τ), x) ⟨⟨hρ, hτ⟩, hxB⟩).trans (le_abs_self _)
      have h2 : ‖G ρ x‖ ≤ |MG0| := (hMG0 (ρ, x) ⟨hρ, hxB⟩).trans (le_abs_self _)
      have h30 : ‖(B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ ≤ |ME0| := by
        rw [Complex.norm_real]; exact (hME0 (τ, x) ⟨hτ, hxB⟩).trans (le_abs_self _)
      have h31 : ‖(B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ ≤ |ME1| := by
        rw [Complex.norm_real]; exact (hME1 (τ, x) ⟨hτ, hxB⟩).trans (le_abs_self _)
      rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB]
      unfold ladFlowCx ladForce
      have t1 : ‖om τ x * A_om ρ τ x‖ ≤ CA * ‖om τ x‖ := by
        rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have t2 : ‖(u τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
          u τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)) * G ρ x‖ ≤
          CB * (‖u τ x 0‖ + ‖u τ x 1‖) := by
        rw [norm_mul]
        have s0 : ‖u τ x 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) x : ℂ) +
            u τ x 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) x : ℂ)‖ ≤
            (|ME0| + |ME1|) * (‖u τ x 0‖ + ‖u τ x 1‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          have a0 := mul_le_mul_of_nonneg_left h30 (norm_nonneg (u τ x 0))
          have a1 := mul_le_mul_of_nonneg_left h31 (norm_nonneg (u τ x 1))
          nlinarith [abs_nonneg ME0, abs_nonneg ME1, norm_nonneg (u τ x 0), norm_nonneg (u τ x 1)]
        exact (mul_le_mul s0 h2 (norm_nonneg _) (by positivity)).trans
          (by dsimp [CB]; ring_nf; rfl)
      exact (norm_sub_le _ _).trans (add_le_add t1 t2)
    · have hband' : 2 * R < |x.2| := not_le.1 hband
      obtain ⟨z0, z1, z2, z3⟩ := hG_supp ρ hρ x hband'
      have hz : ladFlowCx tr (om τ) (u τ) τ (G ρ) x = 0 := by
        unfold ladFlowCx ladTransport; simp [z0, z1, z2, z3]
      rw [hz, norm_zero]
      have : 0 ≤ B.indicator (fun y => ‖u τ y 0‖) x :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
      have : 0 ≤ B.indicator (fun y => ‖u τ y 1‖) x :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
      dsimp [CA, CB]; positivity
  refine ⟨?_, ?_⟩
  · intro τ hτ ρ₀ hρ₀
    have hτS := hI_sub_S hτ
    have hmaj : Integrable
        (fun x => CA * ‖om τ x‖ + CB * (B.indicator (fun y => ‖u τ y 0‖) x +
          B.indicator (fun y => ‖u τ y 1‖) x))
        (volume.restrict (B0579.cell c)) := by
      have iom := (integrableOn_cell_of_X (by linarith) (hom τ hτS).1).norm.const_mul CA
      have iu0 : Integrable (B.indicator (fun y => ‖u τ y 0‖)) (volume.restrict (B0579.cell c)) := by
        have := ((hu τ hτS).1 0).norm.integrable_mul hB_ind.norm
        refine this.congr (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ B <;> simp [hx]
      have iu1 : Integrable (B.indicator (fun y => ‖u τ y 1‖)) (volume.restrict (B0579.cell c)) := by
        have := ((hu τ hτS).1 1).norm.integrable_mul hB_ind.norm
        refine this.congr (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ B <;> simp [hx]
      exact iom.add ((iu0.add iu1).const_mul CB)
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hmaj ?_
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact (hG_int ρ hρ τ hτS).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      exact Eventually.of_forall fun x hx => hpt_bd ρ hρ τ hτ x hx
    · rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      refine Eventually.of_forall fun x hx => ?_
      by_cases hband : |x.2| ≤ 2 * R
      · have hxB : x ∈ B := hcell_sub x hx hband
        have hcA : ContinuousWithinAt (fun ρ => A_om ρ τ x) (Icc t₁ r) ρ₀ :=
          (hA_cont.comp ((continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => τ)).prodMk
            (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
            (fun ρ hρ => ⟨⟨hρ, hτ⟩, hxB⟩)) ρ₀ hρ₀
        have hcG : ContinuousWithinAt (fun ρ => G ρ x) (Icc t₁ r) ρ₀ :=
          (hJG.1.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
            (fun ρ hρ => ⟨hρ, hxB⟩)) ρ₀ hρ₀
        exact ((continuousWithinAt_const.mul hcA).sub (continuousWithinAt_const.mul hcG))
      · have hband' : 2 * R < |x.2| := not_le.1 hband
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ρ hρ
        obtain ⟨z0, z1, z2, z3⟩ := hG_supp ρ hρ x hband'
        obtain ⟨w0, w1, w2, w3⟩ := hG_supp ρ₀ hρ₀ x hband'
        unfold ladFlowCx ladTransport; simp [z0, z1, z2, z3, w0, w1, w2, w3]
  · let K_om : ℝ := M_om * (eLpNorm JB1 2 (B0579.cellMeasure c (-m))).toReal
    let K_u : ℝ := max C_bs 0 * M_om *
      (eLpNorm (B.indicator (fun _ : ℝ × ℝ => (1 : ℂ))) 2 (volume.restrict (B0579.cell c))).toReal
    refine ⟨CA * K_om + CB * (2 * K_u), by dsimp [CA, CB, K_om, K_u]; positivity, ?_⟩
    intro ρ hρ τ hτ
    have hτS := hI_sub_S hτ
    have iom := (integrableOn_cell_of_X (by linarith) (hom τ hτS).1).norm
    have iu0 : Integrable (B.indicator (fun y => ‖u τ y 0‖)) (volume.restrict (B0579.cell c)) := by
      have := ((hu τ hτS).1 0).norm.integrable_mul hB_ind.norm
      exact this.congr (Eventually.of_forall fun x => by by_cases hx : x ∈ B <;> simp [hx])
    have iu1 : Integrable (B.indicator (fun y => ‖u τ y 1‖)) (volume.restrict (B0579.cell c)) := by
      have := ((hu τ hτS).1 1).norm.integrable_mul hB_ind.norm
      exact this.congr (Eventually.of_forall fun x => by by_cases hx : x ∈ B <;> simp [hx])
    have ifl := (hG_int ρ hρ τ hτS).norm
    have hmono : ∫ x in B0579.cell c, ‖ladFlowCx tr (om τ) (u τ) τ (G ρ) x‖ ≤
        ∫ x in B0579.cell c, (CA * ‖om τ x‖ +
          CB * (B.indicator (fun y => ‖u τ y 0‖) x + B.indicator (fun y => ‖u τ y 1‖) x)) :=
      setIntegral_mono_on ifl ((iom.const_mul CA).add ((iu0.add iu1).const_mul CB))
        (B0579.measurableSet_cell c) (fun x hx => hpt_bd ρ hρ τ hτ x hx)
    refine (norm_integral_le_integral_norm _).trans (hmono.trans ?_)
    have hsplit_int : ∫ x in B0579.cell c, (CA * ‖om τ x‖ +
        CB * (B.indicator (fun y => ‖u τ y 0‖) x + B.indicator (fun y => ‖u τ y 1‖) x)) =
        CA * (∫ x in B0579.cell c, ‖om τ x‖) +
          CB * ((∫ x in B0579.cell c, B.indicator (fun y => ‖u τ y 0‖) x) +
            ∫ x in B0579.cell c, B.indicator (fun y => ‖u τ y 1‖) x) := by
      have iBsum : Integrable (fun x => B.indicator (fun y => ‖u τ y 0‖) x +
          B.indicator (fun y => ‖u τ y 1‖) x) (volume.restrict (B0579.cell c)) := iu0.add iu1
      rw [integral_add (iom.const_mul CA) (iBsum.const_mul CB),
        integral_const_mul, integral_const_mul, integral_add iu0 iu1]
    rw [hsplit_int]
    have b1 := mul_le_mul_of_nonneg_left (h_om_L1 τ hτ) (abs_nonneg MA)
    have hCB0 : 0 ≤ CB := mul_nonneg (add_nonneg (abs_nonneg ME0) (abs_nonneg ME1)) (abs_nonneg MG0)
    have b2 := mul_le_mul_of_nonneg_left (add_le_add (h_u_L1 τ hτ 0) (h_u_L1 τ hτ 1)) hCB0
    dsimp [CA, K_om, K_u]; linarith

/-- Interval integrability of the diagonal `ρ ↦ K ρ ρ` for a bounded Carathéodory kernel. -/
private lemma diag_flow_intervalIntegrable {t₁ r M_Ψ : ℝ} (ht₁r : t₁ < r)
    (K : ℝ → ℝ → ℂ)
    (hK_ii : ∀ ρ ∈ Icc t₁ r, IntervalIntegrable (fun τ => K ρ τ) volume t₁ r)
    (hK_cont : ∀ τ ∈ Icc t₁ r, ContinuousOn (fun ρ => K ρ τ) (Icc t₁ r))
    (hK_bdd : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₁ r, ‖K ρ τ‖ ≤ M_Ψ) :
    IntervalIntegrable (fun ρ => K ρ ρ) volume t₁ r := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₁r.le]
  let μI : Measure ℝ := volume.restrict (Icc t₁ r)
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  let a : ℕ → ℕ → ℝ := fun n k => t₁ + (k : ℝ) / ((n + 1 : ℕ) : ℝ) * (r - t₁)
  let slice : ∀ n : ℕ, Fin (n + 1) → Set ℝ := fun n k =>
    if (k : ℕ) = n then Icc (a n k) r else Ico (a n k) (a n (k + 1))
  have ha_mem : ∀ (n : ℕ) (k : Fin (n + 1)), a n k ∈ Icc t₁ r := by
    intro n k
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast k.isLt.le
    have hdiv0 : 0 ≤ (k : ℝ) / ((n + 1 : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg k) hn.le
    have hdiv1 : (k : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hn).2 hle
    exact ⟨by dsimp [a]; nlinarith, by dsimp [a]; nlinarith⟩
  let Dn : ℕ → ℝ → ℂ := fun n ρ =>
    ∑ k : Fin (n + 1), ((slice n k).indicator (fun _ => (1 : ℝ)) ρ : ℂ) * K (a n k) ρ
  have hDn_meas : ∀ n, AEStronglyMeasurable (Dn n) μI := by
    intro n
    have hDn_sum : Dn n = ∑ k ∈ (Finset.univ : Finset (Fin (n + 1))),
        fun ρ => ((slice n k).indicator (fun _ => (1 : ℝ)) ρ : ℂ) * K (a n k) ρ := by
      ext ρ; simp [Dn]
    rw [hDn_sum]
    refine Finset.aestronglyMeasurable_sum Finset.univ fun k _ => ?_
    have hms : MeasurableSet (slice n k) := by
      dsimp [slice]; split_ifs <;> [exact measurableSet_Icc; exact measurableSet_Ico]
    have h1 : Measurable (fun ρ : ℝ => ((slice n k).indicator (fun _ => (1 : ℝ)) ρ : ℂ)) :=
      ((measurable_const : Measurable fun _ : ℝ => ((1 : ℝ) : ℂ)).indicator hms)
    have hii := hK_ii (a n k) (ha_mem n k)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₁r.le] at hii
    exact h1.aestronglyMeasurable.mul hii.aestronglyMeasurable
  have htend : ∀ᵐ ρ ∂μI, Tendsto (fun n => Dn n ρ) atTop (𝓝 (K ρ ρ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
    have hex : ∀ n : ℕ, ∃ k : Fin (n + 1), ρ ∈ slice n k ∧
        ∀ j : Fin (n + 1), j ≠ k → ρ ∉ slice n j := by
      intro n
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      let t_sc : ℝ := (ρ - t₁) / (r - t₁) * ((n + 1 : ℕ) : ℝ)
      let m_idx : ℕ := min ⌊t_sc⌋₊ n
      refine ⟨⟨m_idx, Nat.lt_succ_of_le (min_le_right _ _)⟩, ?_, ?_⟩
      · have ht0 : 0 ≤ t_sc := mul_nonneg (div_nonneg (by linarith [hρ.1]) (by linarith)) hn.le
        have hm_le : (m_idx : ℝ) ≤ t_sc :=
          le_trans (by exact_mod_cast min_le_left ⌊t_sc⌋₊ n) (Nat.floor_le ht0)
        have hdr : 0 < r - t₁ := by linarith
        have hlow : a n m_idx ≤ ρ := by
          dsimp [a, t_sc] at hm_le ⊢
          have h1 := (le_div_iff₀ hdr).1 ((div_le_iff₀ hn).2 hm_le); linarith
        dsimp [slice]; split_ifs with hmn
        · exact ⟨hlow, hρ.2⟩
        · refine ⟨hlow, ?_⟩
          have hlt_n : ⌊t_sc⌋₊ < n := by
            by_contra hge; exact hmn (min_eq_right (not_lt.1 hge))
          have hmeq : m_idx = ⌊t_sc⌋₊ := min_eq_left hlt_n.le
          have hfl_lt : t_sc < (m_idx : ℝ) + 1 := by
            rw [hmeq]; exact_mod_cast Nat.lt_floor_add_one t_sc
          dsimp [a, t_sc] at hfl_lt ⊢
          have h2 : (ρ - t₁) / (r - t₁) < ((m_idx + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
            rw [lt_div_iff₀ hn]; push_cast at hfl_lt ⊢; linarith
          have h3 := (div_lt_iff₀ hdr).1 h2; linarith
      · intro j hj hmem
        have hmono : ∀ u v : ℕ, u ≤ v → a n u ≤ a n v := by
          intro u v huv; dsimp [a]
          have hn' : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
          have h1 : (u : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ (v : ℝ) / ((n + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast huv) hn'
          nlinarith [mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 ht₁r.le)]
        have ht0 : 0 ≤ t_sc := mul_nonneg (div_nonneg (by linarith [hρ.1]) (by linarith)) hn.le
        have hm_le : (m_idx : ℝ) ≤ t_sc :=
          le_trans (by exact_mod_cast min_le_left ⌊t_sc⌋₊ n) (Nat.floor_le ht0)
        have hdr : 0 < r - t₁ := by linarith
        have hlow : a n m_idx ≤ ρ := by
          dsimp [a, t_sc] at hm_le ⊢
          have h1 := (le_div_iff₀ hdr).1 ((div_le_iff₀ hn).2 hm_le); linarith
        rcases lt_trichotomy (j : ℕ) m_idx with hlt | heq | hgt
        · have hjne : (j : ℕ) ≠ n := by omega
          dsimp [slice] at hmem; simp only [hjne, ↓reduceIte] at hmem
          have := hmono (j + 1) m_idx hlt; linarith [hmem.2, hlow]
        · exact hj (Fin.ext heq)
        · have hmne : m_idx ≠ n := by have := j.isLt; omega
          have hlt_n : ⌊t_sc⌋₊ < n := by
            by_contra hge; exact hmne (min_eq_right (not_lt.1 hge))
          have hmeq : m_idx = ⌊t_sc⌋₊ := min_eq_left hlt_n.le
          have hfl_lt : t_sc < (m_idx : ℝ) + 1 := by
            rw [hmeq]; exact_mod_cast Nat.lt_floor_add_one t_sc
          have hup : ρ < a n (m_idx + 1) := by
            dsimp [a, t_sc] at hfl_lt ⊢
            have h2 : (ρ - t₁) / (r - t₁) < ((m_idx + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
              rw [lt_div_iff₀ hn]; push_cast at hfl_lt ⊢; linarith
            have h3 := (div_lt_iff₀ hdr).1 h2; linarith
          have h2 := hmono (m_idx + 1) j hgt
          dsimp [slice] at hmem; split_ifs at hmem <;> linarith [hmem.1]
    choose kn hkn_in hkn_out using hex
    have hDn_eq : ∀ n, Dn n ρ = K (a n (kn n)) ρ := by
      intro n; dsimp [Dn]; rw [Finset.sum_eq_single (kn n)]
      · rw [Set.indicator_of_mem (hkn_in n)]; simp
      · intro j _ hj; rw [Set.indicator_of_notMem (hkn_out n j hj)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hDn_eq]
    have hakn_tend : Tendsto (fun n => a n (kn n)) atTop (𝓝 ρ) := by
      rw [Metric.tendsto_atTop]; intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt ((r - t₁) / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hmem := hkn_in n
      have hdist : |a n (kn n) - ρ| ≤ (r - t₁) / ((n + 1 : ℕ) : ℝ) := by
        dsimp [slice] at hmem; split_ifs at hmem with hk
        · have han : a n n = r - (r - t₁) / ((n + 1 : ℕ) : ℝ) := by
            dsimp [a]; push_cast; field_simp; ring
          rw [hk, han] at hmem ⊢; rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2]
        · have hstep : a n (kn n + 1) - a n (kn n) = (r - t₁) / ((n + 1 : ℕ) : ℝ) := by
            dsimp [a]; push_cast; field_simp; ring
          rw [abs_le]; constructor <;> linarith [hmem.1, hmem.2, hstep]
      rw [Real.dist_eq]; refine lt_of_le_of_lt hdist ?_; rw [div_lt_iff₀ hn1]
      have hN' : r - t₁ < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hN
      have hle : (N : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hn
      nlinarith
    exact (hK_cont ρ hρ ρ hρ).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hakn_tend
        (Eventually.of_forall fun n => ha_mem n (kn n)))
  refine Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop hDn_meas htend) M_Ψ ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
  exact hK_bdd ρ hρ ρ hρ

/-- Inner Fubini swap on `[τ, r] × cell c` for `ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ)`. -/
private lemma cut_inner_fubini {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t₀ S s t₁ r R : ℝ} (hc0 : 0 < c) (ht₀ : 0 ≤ t₀) (hsS : s ≤ S)
    (ht₁ : t₀ < t₁) (ht₁r : t₁ < r) (hrs : r < s) (hR : 0 < R) (hm : 8 < m)
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} {φ Ψ Ψ' : ℝ → ℝ × ℝ → ℂ}
    (hΨ_eq : Ψ = ladCutPhi φ R)
    (hΨ'_eq : Ψ' = fun ρ x => (ladCut R x : ℂ) * ladDt φ ρ x)
    (hom : ∀ τ ∈ Icc t₀ S, MemLp (om τ) 2 (B0579.cellMeasure c m))
    (hu : ∀ τ ∈ Icc t₀ S, IsBiotSavart c (om τ) (u τ))
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t₀ s ×ˢ univ))
    (hΨ_supp : ∀ ρ ∈ Icc t₁ r, ∀ x : ℝ × ℝ, 2 * R < |x.2| →
      Ψ ρ x = 0 ∧ pdCx 0 (Ψ ρ) x = 0 ∧ pdCx 1 (Ψ ρ) x = 0 ∧ ladLapCx (Ψ ρ) x = 0)
    (hΨ'_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Ψ' p.1 p.2) (Ioo t₀ s ×ˢ univ))
    (hΨ'_supp : ∀ ρ ∈ Icc t₁ r, ∀ x : ℝ × ℝ, 2 * R < |x.2| →
      Ψ' ρ x = 0 ∧ pdCx 0 (Ψ' ρ) x = 0 ∧ pdCx 1 (Ψ' ρ) x = 0 ∧ ladLapCx (Ψ' ρ) x = 0)
    (hΨ_int : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₀ S,
      IntegrableOn (ladFlowCx tr (om τ) (u τ) τ (Ψ ρ)) (B0579.cell c))
    {τ : ℝ} (hτ : τ ∈ Icc t₁ r) :
    ∫ ρ in τ..r, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x =
      (∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ r) x) -
        (∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ τ) x) := by
  have hI_sub_Ioo : Icc t₁ r ⊆ Ioo t₀ s := fun ρ hρ => ⟨lt_of_lt_of_le ht₁ hρ.1, lt_of_le_of_lt hρ.2 hrs⟩
  have hτS : τ ∈ Icc t₀ S := ⟨ht₁.le.trans hτ.1, (hτ.2.trans hrs.le).trans hsS⟩
  let B : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hIBc : IsCompact (Icc t₁ r ×ˢ B) := isCompact_Icc.prod hBc
  have hcell_sub : ∀ x ∈ B0579.cell c, |x.2| ≤ 2 * R → x ∈ B :=
    fun x hx h2 => ⟨⟨hx.1.1, hx.1.2.le⟩, abs_le.1 h2⟩
  have hB_ind : MemLp (B.indicator (fun _ : ℝ × ℝ => (1 : ℂ))) 2 (volume.restrict (B0579.cell c)) :=
    memLp_indicator_const 2 hBc.measurableSet (1 : ℂ)
      (Or.inr (ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hBc.measure_lt_top)))
  have hJ_Ψ' := jet_contOn_compact ht₁ hrs B hΨ'_sm
  obtain ⟨hv_cont, hpdE_cont⟩ := train_ec_contOn_compact tr ht₀ ht₁ B
  let clB : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ) := fun p =>
    (max t₁ (min r p.1),
      (max (-(c / 2)) (min (c / 2) p.2.1), max (-(2 * R)) (min (2 * R) p.2.2)))
  have hclB_cont : Continuous clB :=
    (continuous_const.max (continuous_const.min continuous_fst)).prodMk
      ((continuous_const.max (continuous_const.min (continuous_fst.comp continuous_snd))).prodMk
        (continuous_const.max (continuous_const.min (continuous_snd.comp continuous_snd))))
  have hclB_mem : ∀ p, clB p ∈ Icc t₁ r ×ˢ B := fun p =>
    ⟨⟨le_max_left _ _, max_le ht₁r.le (min_le_left _ _)⟩,
      ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩,
      ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩
  have hclB_id : ∀ p ∈ Icc t₁ r ×ˢ B, clB p = p := by
    rintro ⟨ρ, x₁, x₂⟩ ⟨hρ, hx₁, hx₂⟩
    dsimp [clB]
    rw [min_eq_right hρ.2, max_eq_right hρ.1,
      min_eq_right hx₁.2, max_eq_right hx₁.1,
      min_eq_right hx₂.2, max_eq_right hx₂.1]
  let μJ : Measure ℝ := volume.restrict (Icc τ r)
  have : IsFiniteMeasure μJ :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  let μC : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  have hind_meas : Measurable (fun p : ℝ × (ℝ × ℝ) => (B.indicator (fun _ => (1 : ℝ)) p.2 : ℂ)) :=
    ((measurable_const : Measurable fun _ : ℝ × ℝ => ((1 : ℝ) : ℂ)).indicator
      hBc.measurableSet).comp measurable_snd
  have cΨ0 : Continuous (fun p : ℝ × (ℝ × ℝ) => Ψ' (clB p).1 (clB p).2) :=
    hJ_Ψ'.1.comp_continuous hclB_cont hclB_mem
  have cΨk : ∀ k : Fin 2, Continuous (fun p : ℝ × (ℝ × ℝ) => pdCx k (Ψ' (clB p).1) (clB p).2) :=
    fun k => (hJ_Ψ'.2.1 k).comp_continuous hclB_cont hclB_mem
  have cΨL : Continuous (fun p : ℝ × (ℝ × ℝ) => ladLapCx (Ψ' (clB p).1) (clB p).2) :=
    hJ_Ψ'.2.2.comp_continuous hclB_cont hclB_mem
  have cvk : ∀ k : Fin 2, Continuous (fun p : ℝ × (ℝ × ℝ) => (tr.v τ (clB p).2 k : ℂ)) :=
    fun k => Complex.continuous_ofReal.comp
      ((hv_cont k).comp_continuous
        ((continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => τ).prodMk
          (continuous_snd.comp hclB_cont))
        (fun p => ⟨hτ, (hclB_mem p).2⟩))
  have cEj : ∀ j : Fin 2,
      Continuous (fun p : ℝ × (ℝ × ℝ) => (B0579.pd j (UnforcedLeray.B0238.Ec tr τ) (clB p).2 : ℂ)) :=
    fun j => Complex.continuous_ofReal.comp
      ((hpdE_cont j).comp_continuous
        ((continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => τ).prodMk
          (continuous_snd.comp hclB_cont))
        (fun p => ⟨hτ, (hclB_mem p).2⟩))
  let F_cl : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    (B.indicator (fun _ => (1 : ℝ)) p.2 : ℂ) *
      (om τ p.2 * ((ν : ℂ) * ladLapCx (Ψ' (clB p).1) (clB p).2 +
          ((tr.v τ (clB p).2 0 : ℂ) * pdCx 0 (Ψ' (clB p).1) (clB p).2 +
            (tr.v τ (clB p).2 1 : ℂ) * pdCx 1 (Ψ' (clB p).1) (clB p).2)) -
        (u τ p.2 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) (clB p).2 : ℂ) +
          u τ p.2 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) (clB p).2 : ℂ)) *
            Ψ' (clB p).1 (clB p).2)
  have hom_m : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => om τ p.2) (μJ.prod μC) :=
    (integrableOn_cell_of_X (by linarith) (hom τ hτS)).aestronglyMeasurable.comp_snd
  have hu_m : ∀ j : Fin 2, AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => u τ p.2 j) (μJ.prod μC) :=
    fun j => ((hu τ hτS).1 j).1.comp_snd
  have huE_m : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) =>
      u τ p.2 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) (clB p).2 : ℂ) +
        u τ p.2 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) (clB p).2 : ℂ)) (μJ.prod μC) :=
    ((hu_m 0).mul (cEj 0).aestronglyMeasurable).add ((hu_m 1).mul (cEj 1).aestronglyMeasurable)
  have hF_cl_m : AEStronglyMeasurable F_cl (μJ.prod μC) := by
    refine hind_meas.aestronglyMeasurable.mul ?_
    refine (hom_m.mul ?_).sub (huE_m.mul cΨ0.aestronglyMeasurable)
    exact (aestronglyMeasurable_const.mul cΨL.aestronglyMeasurable).add
      (((cvk 0).aestronglyMeasurable.mul (cΨk 0).aestronglyMeasurable).add
        ((cvk 1).aestronglyMeasurable.mul (cΨk 1).aestronglyMeasurable))
  have hae_F : (Function.uncurry fun ρ x => ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x) =ᵐ[μJ.prod μC] F_cl := by
    filter_upwards [ae_prod_restrict_mem measurableSet_Icc (B0579.measurableSet_cell c)] with p ⟨hp1, hp2⟩
    have hp1' : p.1 ∈ Icc t₁ r := ⟨hτ.1.trans hp1.1, hp1.2⟩
    dsimp only [Function.uncurry, F_cl]
    by_cases hxB : p.2 ∈ B
    · rw [Set.indicator_of_mem hxB, hclB_id p ⟨hp1', hxB⟩, Complex.ofReal_one, one_mul]; rfl
    · have hb : 2 * R < |p.2.2| := by
        by_contra hle; exact hxB (hcell_sub p.2 hp2 (not_lt.1 hle))
      obtain ⟨z0, z1, z2, z3⟩ := hΨ'_supp p.1 hp1' p.2 hb
      rw [Set.indicator_of_notMem hxB, zero_mul]
      unfold ladFlowCx ladTransport
      rw [z0, z1, z2, z3]; ring
  let A_fn : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    (ν : ℂ) * ladLapCx (Ψ' (clB p).1) (clB p).2 +
      ((tr.v τ (clB p).2 0 : ℂ) * pdCx 0 (Ψ' (clB p).1) (clB p).2 +
        (tr.v τ (clB p).2 1 : ℂ) * pdCx 1 (Ψ' (clB p).1) (clB p).2)
  have hA_cont : Continuous A_fn :=
    (continuous_const.mul cΨL).add (((cvk 0).mul (cΨk 0)).add ((cvk 1).mul (cΨk 1)))
  obtain ⟨MA, hMA⟩ := hIBc.exists_bound_of_continuousOn hA_cont.continuousOn
  obtain ⟨MG0, hMG0⟩ := hIBc.exists_bound_of_continuousOn hJ_Ψ'.1
  obtain ⟨ME0, hME0⟩ := hIBc.exists_bound_of_continuousOn (hpdE_cont 0)
  obtain ⟨ME1, hME1⟩ := hIBc.exists_bound_of_continuousOn (hpdE_cont 1)
  let CA : ℝ := |MA|
  let CB : ℝ := (|ME0| + |ME1|) * |MG0|
  have hmajC : Integrable (fun x => CA * ‖om τ x‖ +
      CB * (B.indicator (fun y => ‖u τ y 0‖) x + B.indicator (fun y => ‖u τ y 1‖) x)) μC := by
    have iom := (integrableOn_cell_of_X (by linarith) (hom τ hτS)).norm.const_mul CA
    have iu0 : Integrable (B.indicator (fun y => ‖u τ y 0‖)) μC :=
      (((hu τ hτS).1 0).norm.integrable_mul hB_ind.norm).congr
        (Eventually.of_forall fun x => by by_cases hx : x ∈ B <;> simp [hx])
    have iu1 : Integrable (B.indicator (fun y => ‖u τ y 1‖)) μC :=
      (((hu τ hτS).1 1).norm.integrable_mul hB_ind.norm).congr
        (Eventually.of_forall fun x => by by_cases hx : x ∈ B <;> simp [hx])
    exact iom.add ((iu0.add iu1).const_mul CB)
  have hprod_int : Integrable (Function.uncurry fun ρ x => ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x)
      (μJ.prod μC) := by
    refine ((integrable_const (1 : ℝ)).mul_prod hmajC).mono' (hF_cl_m.congr hae_F.symm) ?_
    filter_upwards [ae_prod_restrict_mem measurableSet_Icc (B0579.measurableSet_cell c)] with p ⟨hp1, hp2⟩
    have hp1' : p.1 ∈ Icc t₁ r := ⟨hτ.1.trans hp1.1, hp1.2⟩
    simp only [Function.uncurry, one_mul]
    by_cases hb : |p.2.2| ≤ 2 * R
    · have hxB : p.2 ∈ B := hcell_sub p.2 hp2 hb
      have h1 : ‖(ν : ℂ) * ladLapCx (Ψ' p.1) p.2 + ladTransport tr τ (Ψ' p.1) p.2‖ ≤ CA := by
        have := (hMA p ⟨hp1', hxB⟩).trans (le_abs_self _)
        dsimp only [A_fn] at this
        rw [hclB_id p ⟨hp1', hxB⟩] at this
        exact this
      have h2 : ‖Ψ' p.1 p.2‖ ≤ |MG0| := (hMG0 p ⟨hp1', hxB⟩).trans (le_abs_self _)
      have h30 : ‖(B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) p.2 : ℂ)‖ ≤ |ME0| := by
        rw [Complex.norm_real]; exact (hME0 (τ, p.2) ⟨hτ, hxB⟩).trans (le_abs_self _)
      have h31 : ‖(B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) p.2 : ℂ)‖ ≤ |ME1| := by
        rw [Complex.norm_real]; exact (hME1 (τ, p.2) ⟨hτ, hxB⟩).trans (le_abs_self _)
      rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB]
      unfold ladFlowCx ladForce
      have t1 : ‖om τ p.2 * ((ν : ℂ) * ladLapCx (Ψ' p.1) p.2 + ladTransport tr τ (Ψ' p.1) p.2)‖ ≤
          CA * ‖om τ p.2‖ := by
        rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have t2 : ‖(u τ p.2 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) p.2 : ℂ) +
          u τ p.2 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) p.2 : ℂ)) * Ψ' p.1 p.2‖ ≤
          CB * (‖u τ p.2 0‖ + ‖u τ p.2 1‖) := by
        rw [norm_mul]
        have s0 : ‖u τ p.2 0 * (B0579.pd 0 (UnforcedLeray.B0238.Ec tr τ) p.2 : ℂ) +
            u τ p.2 1 * (B0579.pd 1 (UnforcedLeray.B0238.Ec tr τ) p.2 : ℂ)‖ ≤
            (|ME0| + |ME1|) * (‖u τ p.2 0‖ + ‖u τ p.2 1‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          have a0 := mul_le_mul_of_nonneg_left h30 (norm_nonneg (u τ p.2 0))
          have a1 := mul_le_mul_of_nonneg_left h31 (norm_nonneg (u τ p.2 1))
          nlinarith [abs_nonneg ME0, abs_nonneg ME1, norm_nonneg (u τ p.2 0), norm_nonneg (u τ p.2 1)]
        exact (mul_le_mul s0 h2 (norm_nonneg _) (by positivity)).trans (le_of_eq (by dsimp [CB]; ring))
      exact (norm_sub_le _ _).trans (add_le_add t1 t2)
    · have hb' : 2 * R < |p.2.2| := not_le.1 hb
      obtain ⟨z0, z1, z2, z3⟩ := hΨ'_supp p.1 hp1' p.2 hb'
      have hz : ladFlowCx tr (om τ) (u τ) τ (Ψ' p.1) p.2 = 0 := by
        unfold ladFlowCx ladTransport; rw [z0, z1, z2, z3]; ring
      rw [hz, norm_zero]
      have : 0 ≤ B.indicator (fun y => ‖u τ y 0‖) p.2 :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) p.2
      have : 0 ≤ B.indicator (fun y => ‖u τ y 1‖) p.2 :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) p.2
      positivity
  rw [intervalIntegral.integral_of_le hτ.2, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  change ∫ ρ, (∫ x, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x ∂μC) ∂μJ = _
  rw [MeasureTheory.integral_integral_swap hprod_int]
  have hpt : ∀ x ∈ B0579.cell c,
      ∫ ρ, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x ∂μJ =
        ladFlowCx tr (om τ) (u τ) τ (Ψ r) x - ladFlowCx tr (om τ) (u τ) τ (Ψ τ) x := by
    intro x hx
    change ∫ ρ in Icc τ r, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x = _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.2]
    obtain ⟨hftc0, hftc1, hftc2⟩ := cut_ftc_identities hR hφs
      (hI_sub_Ioo hτ) (hI_sub_Ioo ⟨ht₁r.le, le_rfl⟩) hτ.2 x
    rw [← hΨ_eq] at hftc0 hftc1 hftc2
    have hftc0' : ∫ ρ in τ..r, Ψ' ρ x = Ψ r x - Ψ τ x := by rw [hΨ'_eq]; exact hftc0
    have hftc1' : ∀ k : Fin 2, ∫ ρ in τ..r, pdCx k (Ψ' ρ) x = pdCx k (Ψ r) x - pdCx k (Ψ τ) x :=
      fun k => by rw [hΨ'_eq]; exact hftc1 k
    have hftc2' : ∫ ρ in τ..r, ladLapCx (Ψ' ρ) x = ladLapCx (Ψ r) x - ladLapCx (Ψ τ) x := by
      rw [hΨ'_eq]; exact hftc2
    by_cases hb : |x.2| ≤ 2 * R
    · have hxB : x ∈ B := hcell_sub x hx hb
      have hsubJ : uIcc τ r ⊆ Icc t₁ r := by
        rw [uIcc_of_le hτ.2]; exact fun ρ hρ => ⟨hτ.1.trans hρ.1, hρ.2⟩
      have i0 : IntervalIntegrable (fun ρ => Ψ' ρ x) volume τ r :=
        (hJ_Ψ'.1.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
          (fun ρ hρ => ⟨hsubJ hρ, hxB⟩)).intervalIntegrable
      have ik : ∀ k : Fin 2, IntervalIntegrable (fun ρ => pdCx k (Ψ' ρ) x) volume τ r :=
        fun k => ((hJ_Ψ'.2.1 k).comp
          (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
          (fun ρ hρ => ⟨hsubJ hρ, hxB⟩)).intervalIntegrable
      have iL : IntervalIntegrable (fun ρ => ladLapCx (Ψ' ρ) x) volume τ r :=
        (hJ_Ψ'.2.2.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
          (fun ρ hρ => ⟨hsubJ hρ, hxB⟩)).intervalIntegrable
      have itrans : IntervalIntegrable (fun ρ => ladTransport tr τ (Ψ' ρ) x) volume τ r :=
        ((ik 0).const_mul _).add ((ik 1).const_mul _)
      have iA : IntervalIntegrable
          (fun ρ => om τ x * ((ν : ℂ) * ladLapCx (Ψ' ρ) x + ladTransport tr τ (Ψ' ρ) x))
          volume τ r := ((iL.const_mul _).add itrans).const_mul _
      have iB : IntervalIntegrable (fun ρ => ladForce tr (u τ) τ x * Ψ' ρ x) volume τ r :=
        i0.const_mul _
      unfold ladFlowCx
      rw [intervalIntegral.integral_sub iA iB,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (iL.const_mul _) itrans,
        intervalIntegral.integral_const_mul]
      unfold ladTransport
      rw [intervalIntegral.integral_add ((ik 0).const_mul _) ((ik 1).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        hftc2', hftc1' 0, hftc1' 1, hftc0']
      ring
    · have hb' : 2 * R < |x.2| := not_le.1 hb
      have hz' : ∀ ρ ∈ uIcc τ r, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x = 0 := by
        intro ρ hρ
        rw [uIcc_of_le hτ.2] at hρ
        obtain ⟨z0, z1, z2, z3⟩ := hΨ'_supp ρ ⟨hτ.1.trans hρ.1, hρ.2⟩ x hb'
        unfold ladFlowCx ladTransport; rw [z0, z1, z2, z3]; ring
      obtain ⟨r0, r1, r2, r3⟩ := hΨ_supp r ⟨ht₁r.le, le_rfl⟩ x hb'
      obtain ⟨τ0, τ1, τ2, τ3⟩ := hΨ_supp τ hτ x hb'
      rw [intervalIntegral.integral_congr hz', intervalIntegral.integral_zero]
      unfold ladFlowCx ladTransport; rw [r0, r1, r2, r3, τ0, τ1, τ2, τ3]; ring
  have hr_int := hΨ_int r ⟨ht₁r.le, le_rfl⟩ τ hτS
  have hτ_int := hΨ_int τ hτ τ hτS
  have hcongr : ∫ x, (∫ ρ, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x ∂μJ) ∂μC =
      ∫ x, (ladFlowCx tr (om τ) (u τ) τ (Ψ r) x - ladFlowCx tr (om τ) (u τ) τ (Ψ τ) x) ∂μC := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    exact hpt x hx
  rw [hcongr, integral_sub hr_int hτ_int]

/-- Fubini product rule on `[t₁, r] ⊂ (t₀, s)` without strong continuity of `om`. -/
private lemma cut_product_rule_interior {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t₀ S s t₁ r R M_om : ℝ} (hc1 : 1 ≤ c) (ht₀ : 0 ≤ t₀) (hsS : s ≤ S)
    (ht₁ : t₀ < t₁) (ht₁r : t₁ < r) (hrs : r < s) (hR : 0 < R) (hM_om : 0 ≤ M_om)
    (hm : 8 < m) {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hom : ∀ τ ∈ Icc t₀ S, MemLp (om τ) 2 (B0579.cellMeasure c m) ∧
      HasZeroCirculation c (om τ) ∧ (xNorm c m (om τ)).toReal ≤ M_om)
    (hu : ∀ τ ∈ Icc t₀ S, IsBiotSavart c (om τ) (u τ))
    (hwk : ∀ ψ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc t₀ S,
      IntegrableOn (flowIntegrand tr (om τ) (u τ) τ ψ) (B0579.cell c) ∧
      IntervalIntegrable (fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x)
        volume t₀ τ ∧
      ∫ x in B0579.cell c, om τ x * (ψ x : ℂ) =
        ∫ σ in t₀..τ, ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t₀ s ×ˢ univ))
    (hφp : ∀ ρ ∈ Ico t₀ s, ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x) :
    IntervalIntegrable (fun ρ => ladRate tr om u φ R ρ) volume t₁ r ∧
      ladCutPair c R om φ r - ladCutPair c R om φ t₁ = ∫ ρ in t₁..r, ladRate tr om u φ R ρ := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  let U : Set (ℝ × (ℝ × ℝ)) := Ioo t₀ s ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  let Φ : ℝ × (ℝ × ℝ) → ℂ := fun p => φ p.1 p.2
  have hΦ : ContDiffOn ℝ ∞ Φ U := hφs.mono (prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hI_sub_Ioo : Icc t₁ r ⊆ Ioo t₀ s := fun ρ hρ => ⟨lt_of_lt_of_le ht₁ hρ.1, lt_of_le_of_lt hρ.2 hrs⟩
  have hI_sub_S : Icc t₁ r ⊆ Icc t₀ S := fun ρ hρ =>
    ⟨(hI_sub_Ioo hρ).1.le, (hI_sub_Ioo hρ).2.le.trans hsS⟩
  let Ψ : ℝ → ℝ × ℝ → ℂ := ladCutPhi φ R
  let Ψ' : ℝ → ℝ × ℝ → ℂ := fun ρ x => (ladCut R x : ℂ) * ladDt φ ρ x
  have hχ : ContDiff ℝ ∞ (ladCut R) := by
    obtain ⟨_, _, hK⟩ := ladCutProps
    exact ((hK R hR).1 c).smooth
  have hper_cut : ∀ x : ℝ × ℝ, ladCut R (x.1 + c, x.2) = ladCut R x := by
    obtain ⟨_, _, hK⟩ := ladCutProps
    exact ((hK R hR).1 c).periodic
  have hwk_cx : ∀ (F : ℝ × ℝ → ℂ),
      B0579.IsCylTest c (fun x => (F x).re) → B0579.IsCylTest c (fun x => (F x).im) →
      ∀ ρ ∈ Icc t₁ r,
        (∀ τ ∈ Icc t₀ S, IntegrableOn (ladFlowCx tr (om τ) (u τ) τ F) (B0579.cell c)) ∧
        IntervalIntegrable (fun τ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x)
          volume t₁ ρ ∧
        (∫ x in B0579.cell c, om ρ x * F x) - (∫ x in B0579.cell c, om t₁ x * F x) =
          ∫ τ in t₁..ρ, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ F x :=
    fun F hFre hFim _ hρ => weak_cx_sub_interval tr hsS ht₁ ht₁r hrs (fun τ hτ => (hom τ hτ).1)
      hwk F hFre hFim hρ
  have hΨ_test : ∀ ρ ∈ Icc t₁ r,
      B0579.IsCylTest c (fun x => (Ψ ρ x).re) ∧ B0579.IsCylTest c (fun x => (Ψ ρ x).im) :=
    fun ρ hρ => ladPRTest c t₀ s φ hc0 hφs hφp R hR ρ (Ioo_subset_Ico_self (hI_sub_Ioo hρ))
  have hdt_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ladDt φ p.1 p.2) U := by
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ Φ p ((1 : ℝ), (0 : ℝ × ℝ))) U :=
      (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ × ℝ))).contDiff.comp_contDiffOn
        (hΦ.fderiv_of_isOpen hU (by simp))
    exact h1.congr fun p hp => LadPRDerivAux.ladDt_eq_fderiv hφs hp.1 p.2
  have hΨ'_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Ψ' p.1 p.2) U :=
    (((RateSplitAux.contDiff_ofReal hχ).comp contDiff_snd).contDiffOn).mul hdt_sm
  have hdt_slice : ∀ ρ ∈ Icc t₁ r, ContDiff ℝ ∞ (ladDt φ ρ) := by
    intro ρ hρ
    have hρo := hI_sub_Ioo hρ
    have h : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (fun p : ℝ × (ℝ × ℝ) => ladDt φ p.1 p.2) (ρ, x)) univ :=
      hdt_sm.comp (contDiff_prodMk_right ρ).contDiffOn (fun x _ => ⟨hρo, mem_univ x⟩)
    exact contDiffOn_univ.1 h
  have hΨ'_test : ∀ ρ ∈ Icc t₁ r,
      B0579.IsCylTest c (fun x => (Ψ' ρ x).re) ∧ B0579.IsCylTest c (fun x => (Ψ' ρ x).im) := by
    intro ρ hρ
    have hρo := hI_sub_Ioo hρ
    have hsm : ContDiff ℝ ∞ (Ψ' ρ) := (RateSplitAux.contDiff_ofReal hχ).mul (hdt_slice ρ hρ)
    have hpe : ∀ x : ℝ × ℝ, Ψ' ρ (x.1 + c, x.2) = Ψ' ρ x := by
      intro x
      have hd1 := LadPRDerivAux.hasDerivAt_phi hφs hρo (x.1 + c, x.2)
      have hd2 : HasDerivAt (fun r' => φ r' (x.1 + c, x.2)) (ladDt φ ρ x) ρ :=
        (LadPRDerivAux.hasDerivAt_phi hφs hρo x).congr_of_eventuallyEq
          (by filter_upwards [isOpen_Ioo.mem_nhds hρo] with r' hr'
              exact hφp r' (Ioo_subset_Ico_self hr') x)
      simp only [Ψ', hper_cut x, hd1.unique hd2]
    have hb : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Ψ' ρ x = 0 :=
      fun x hx => by simp [Ψ', RateSplitAux.cut_zero hR hx]
    exact LadPRTestAux.isCylTest_re_im hsm hpe (2 * R) hb
  have hΨ_sm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Ψ p.1 p.2) U :=
    (((RateSplitAux.contDiff_ofReal hχ).comp contDiff_snd).contDiffOn).mul hΦ
  have hΨ_supp : ∀ ρ ∈ Icc t₁ r, ∀ x : ℝ × ℝ, 2 * R < |x.2| →
      Ψ ρ x = 0 ∧ pdCx 0 (Ψ ρ) x = 0 ∧ pdCx 1 (Ψ ρ) x = 0 ∧ ladLapCx (Ψ ρ) x = 0 := by
    intro ρ hρ x hx
    have hsm := RateSplitAux.contDiff_slice (Ioo_subset_Ico_self (hI_sub_Ioo hρ)) hφs
    have z0 : Ψ ρ x = 0 := by simp [Ψ, ladCutPhi, RateSplitAux.cut_zero hR hx]
    have zk : ∀ k : Fin 2, pdCx k (Ψ ρ) x = 0 := fun k => by
      change pdCx k (fun y => (ladCut R y : ℂ) * φ ρ y) x = 0
      rw [RateSplitAux.pdCx_cut_mul hχ hsm k x, RateSplitAux.cut_zero hR hx,
        RateSplitAux.pd_cut_zero hR k hx]; simp
    have zL : ladLapCx (Ψ ρ) x = 0 := by
      change ladLapCx (fun y => (ladCut R y : ℂ) * φ ρ y) x = 0
      rw [RateSplitAux.lap_cut_mul hχ hsm x, RateSplitAux.cut_zero hR hx,
        RateSplitAux.pd_cut_zero hR 0 hx, RateSplitAux.pd_cut_zero hR 1 hx,
        RateSplitAux.lapP_cut_zero hR hx]; simp
    exact ⟨z0, zk 0, zk 1, zL⟩
  have hΨ'_supp : ∀ ρ ∈ Icc t₁ r, ∀ x : ℝ × ℝ, 2 * R < |x.2| →
      Ψ' ρ x = 0 ∧ pdCx 0 (Ψ' ρ) x = 0 ∧ pdCx 1 (Ψ' ρ) x = 0 ∧ ladLapCx (Ψ' ρ) x = 0 := by
    intro ρ hρ x hx
    have hsm := hdt_slice ρ hρ
    have z0 : Ψ' ρ x = 0 := by simp [Ψ', RateSplitAux.cut_zero hR hx]
    have zk : ∀ k : Fin 2, pdCx k (Ψ' ρ) x = 0 := fun k => by
      rw [RateSplitAux.pdCx_cut_mul hχ hsm k x, RateSplitAux.cut_zero hR hx,
        RateSplitAux.pd_cut_zero hR k hx]; simp
    have zL : ladLapCx (Ψ' ρ) x = 0 := by
      rw [RateSplitAux.lap_cut_mul hχ hsm x, RateSplitAux.cut_zero hR hx,
        RateSplitAux.pd_cut_zero hR 0 hx, RateSplitAux.pd_cut_zero hR 1 hx,
        RateSplitAux.lapP_cut_zero hR hx]; simp
    exact ⟨z0, zk 0, zk 1, zL⟩
  have hΨ_int : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₀ S,
      IntegrableOn (ladFlowCx tr (om τ) (u τ) τ (Ψ ρ)) (B0579.cell c) :=
    fun ρ hρ => (hwk_cx (Ψ ρ) (hΨ_test ρ hρ).1 (hΨ_test ρ hρ).2 ρ hρ).1
  have hΨ'_int : ∀ ρ ∈ Icc t₁ r, ∀ τ ∈ Icc t₀ S,
      IntegrableOn (ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ)) (B0579.cell c) :=
    fun ρ hρ => (hwk_cx (Ψ' ρ) (hΨ'_test ρ hρ).1 (hΨ'_test ρ hρ).2 ρ hρ).1
  obtain ⟨hΨ_cont, M_Ψ, _hM_Ψ0, hΨ_bdd⟩ :=
    flow_family_caratheodory tr hc1 ht₀ hsS ht₁ hrs hM_om hm hom hu Ψ hΨ_sm hΨ_supp hΨ_int
  obtain ⟨hΨ'_cont, M_Ψ', hM_Ψ'0, hΨ'_bdd⟩ :=
    flow_family_caratheodory tr hc1 ht₀ hsS ht₁ hrs hM_om hm hom hu Ψ' hΨ'_sm hΨ'_supp hΨ'_int
  have hKΨ'_int : Integrable
      (Function.uncurry fun ρ τ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x)
      ((volume.restrict (Icc t₁ r)).prod (volume.restrict (Icc t₁ r))) := by
    refine integrable_caratheodory_square ht₁r ?_ hΨ'_cont hM_Ψ'0 hΨ'_bdd
    intro ρ hρ
    have hii := (hwk_cx (Ψ' ρ) (hΨ'_test ρ hρ).1 (hΨ'_test ρ hρ).2 r ⟨ht₁r.le, le_rfl⟩).2.1
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₁r.le] at hii
    exact hii.aestronglyMeasurable
  have hdiag_ii : IntervalIntegrable
      (fun ρ => ∫ x in B0579.cell c, ladFlowCx tr (om ρ) (u ρ) ρ (Ψ ρ) x) volume t₁ r :=
    diag_flow_intervalIntegrable ht₁r
      (fun ρ τ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ ρ) x)
      (fun ρ hρ => (hwk_cx (Ψ ρ) (hΨ_test ρ hρ).1 (hΨ_test ρ hρ).2 r ⟨ht₁r.le, le_rfl⟩).2.1)
      hΨ_cont hΨ_bdd
  have hdt_pair_eq : ∀ ρ ∈ Icc t₁ r,
      ∫ x in B0579.cell c, om ρ x * Ψ' ρ x =
        (∫ x in B0579.cell c, om t₁ x * Ψ' ρ x) +
          ∫ τ in t₁..ρ, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x :=
    fun ρ hρ => by
      linear_combination (hwk_cx (Ψ' ρ) (hΨ'_test ρ hρ).1 (hΨ'_test ρ hρ).2 ρ hρ).2.2
  let B : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R)
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hIBc : IsCompact (Icc t₁ r ×ˢ B) := isCompact_Icc.prod hBc
  have hcell_sub : ∀ x ∈ B0579.cell c, |x.2| ≤ 2 * R → x ∈ B :=
    fun x hx h2 => ⟨⟨hx.1.1, hx.1.2.le⟩, abs_le.1 h2⟩
  have hJ_Ψ' := jet_contOn_compact ht₁ hrs B hΨ'_sm
  have hfirst_cont : ContinuousOn (fun ρ => ∫ x in B0579.cell c, om t₁ x * Ψ' ρ x) (Icc t₁ r) := by
    obtain ⟨MΨ', hMΨ'⟩ := hIBc.exists_bound_of_continuousOn hJ_Ψ'.1
    have ht₁S : t₁ ∈ Icc t₀ S := hI_sub_S ⟨le_rfl, ht₁r.le⟩
    have hmaj : Integrable (fun x => |MΨ'| * ‖om t₁ x‖) (volume.restrict (B0579.cell c)) :=
      (integrableOn_cell_of_X (by linarith) (hom t₁ ht₁S).1).norm.const_mul |MΨ'|
    intro ρ₀ hρ₀
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hmaj ?_
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hsm : Continuous (Ψ' ρ) :=
        ((RateSplitAux.contDiff_ofReal hχ).mul (hdt_slice ρ hρ)).continuous
      exact (RateSplitAux.integrableOn_w_mul c m R (hom t₁ ht₁S).1 hsm
        (fun x hx => (hΨ'_supp ρ hρ x hx).1)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      refine Eventually.of_forall fun x hx => ?_
      by_cases hb : |x.2| ≤ 2 * R
      · rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right
          ((hMΨ' (ρ, x) ⟨hρ, hcell_sub x hx hb⟩).trans (le_abs_self _)) (norm_nonneg _)
      · have hb' : 2 * R < |x.2| := not_le.1 hb
        rw [(hΨ'_supp ρ hρ x hb').1, mul_zero, norm_zero]; positivity
    · rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
      refine Eventually.of_forall fun x hx => ?_
      by_cases hb : |x.2| ≤ 2 * R
      · exact continuousWithinAt_const.mul
          ((hJ_Ψ'.1.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => x)).continuousOn
            (fun ρ hρ => ⟨hρ, hcell_sub x hx hb⟩)) ρ₀ hρ₀)
      · have hb' : 2 * R < |x.2| := not_le.1 hb
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ρ hρ
        simp [(hΨ'_supp ρ hρ x hb').1, (hΨ'_supp ρ₀ hρ₀ x hb').1]
  have hfirst_fub : ∫ ρ in t₁..r, ∫ x in B0579.cell c, om t₁ x * Ψ' ρ x =
      (∫ x in B0579.cell c, om t₁ x * Ψ r x) - ladCutPair c R om φ t₁ := by
    let clB : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ) := fun p =>
      (max t₁ (min r p.1),
        (max (-(c / 2)) (min (c / 2) p.2.1), max (-(2 * R)) (min (2 * R) p.2.2)))
    have hclB_cont : Continuous clB :=
      (continuous_const.max (continuous_const.min continuous_fst)).prodMk
        ((continuous_const.max (continuous_const.min (continuous_fst.comp continuous_snd))).prodMk
          (continuous_const.max (continuous_const.min (continuous_snd.comp continuous_snd))))
    have hclB_mem : ∀ p, clB p ∈ Icc t₁ r ×ˢ B := fun p =>
      ⟨⟨le_max_left _ _, max_le ht₁r.le (min_le_left _ _)⟩,
        ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩,
        ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩
    have hclB_id : ∀ p ∈ Icc t₁ r ×ˢ B, clB p = p := by
      rintro ⟨ρ, x₁, x₂⟩ ⟨hρ, hx₁, hx₂⟩
      dsimp [clB]
      rw [min_eq_right hρ.2, max_eq_right hρ.1,
        min_eq_right hx₁.2, max_eq_right hx₁.1,
        min_eq_right hx₂.2, max_eq_right hx₂.1]
    let μI : Measure ℝ := volume.restrict (Icc t₁ r)
    have : IsFiniteMeasure μI :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    let μC : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
    obtain ⟨MΨ', hMΨ'⟩ := hIBc.exists_bound_of_continuousOn hJ_Ψ'.1
    have ht₁S : t₁ ∈ Icc t₀ S := hI_sub_S ⟨le_rfl, ht₁r.le⟩
    have hom1_int : Integrable (om t₁) μC :=
      integrableOn_cell_of_X (by linarith) (hom t₁ ht₁S).1
    have hΨ'_cl : Continuous (fun p : ℝ × (ℝ × ℝ) => Ψ' (clB p).1 (clB p).2) :=
      hJ_Ψ'.1.comp_continuous hclB_cont hclB_mem
    have hind_meas : Measurable (fun p : ℝ × (ℝ × ℝ) => (B.indicator (fun _ => (1 : ℝ)) p.2 : ℂ)) :=
      ((measurable_const : Measurable fun _ : ℝ × ℝ => ((1 : ℝ) : ℂ)).indicator
        hBc.measurableSet).comp measurable_snd
    have hae_eq : (Function.uncurry fun ρ x => om t₁ x * Ψ' ρ x) =ᵐ[μI.prod μC]
        fun p => om t₁ p.2 * ((B.indicator (fun _ => (1 : ℝ)) p.2 : ℂ) * Ψ' (clB p).1 (clB p).2) := by
      filter_upwards [ae_prod_restrict_mem measurableSet_Icc (B0579.measurableSet_cell c)] with p ⟨hp1, hp2⟩
      dsimp [Function.uncurry]
      by_cases hxB : p.2 ∈ B
      · rw [Set.indicator_of_mem hxB, hclB_id p ⟨hp1, hxB⟩]; simp
      · have hb : 2 * R < |p.2.2| := by
          by_contra hle; exact hxB (hcell_sub p.2 hp2 (not_lt.1 hle))
        rw [Set.indicator_of_notMem hxB, (hΨ'_supp p.1 hp1 p.2 hb).1]; simp
    have hprod_int : Integrable (Function.uncurry fun ρ x => om t₁ x * Ψ' ρ x) (μI.prod μC) := by
      have hmeas : AEStronglyMeasurable (Function.uncurry fun ρ x => om t₁ x * Ψ' ρ x) (μI.prod μC) :=
        (hom1_int.aestronglyMeasurable.comp_snd.mul
          (hind_meas.aestronglyMeasurable.mul hΨ'_cl.aestronglyMeasurable)).congr hae_eq.symm
      have hdom : Integrable (fun p : ℝ × (ℝ × ℝ) => (1 : ℝ) * (|MΨ'| * ‖om t₁ p.2‖)) (μI.prod μC) :=
        (integrable_const (1 : ℝ)).mul_prod (hom1_int.norm.const_mul |MΨ'|)
      refine hdom.mono' hmeas ?_
      filter_upwards [ae_prod_restrict_mem measurableSet_Icc (B0579.measurableSet_cell c)] with p ⟨hp1, hp2⟩
      simp only [Function.uncurry, one_mul]
      by_cases hb : |p.2.2| ≤ 2 * R
      · rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right
          ((hMΨ' (p.1, p.2) ⟨hp1, hcell_sub p.2 hp2 hb⟩).trans (le_abs_self _)) (norm_nonneg _)
      · have hb' : 2 * R < |p.2.2| := not_le.1 hb
        rw [(hΨ'_supp p.1 hp1 p.2 hb').1, mul_zero, norm_zero]; positivity
    rw [intervalIntegral.integral_of_le ht₁r.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    change ∫ ρ, (∫ x, om t₁ x * Ψ' ρ x ∂μC) ∂μI = _
    rw [MeasureTheory.integral_integral_swap hprod_int]
    have hpt : ∀ x ∈ B0579.cell c,
        ∫ ρ, om t₁ x * Ψ' ρ x ∂μI = om t₁ x * Ψ r x - om t₁ x * Ψ t₁ x := by
      intro x _
      change ∫ ρ in Icc t₁ r, om t₁ x * Ψ' ρ x = _
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht₁r.le,
        intervalIntegral.integral_const_mul,
        (cut_ftc_identities hR hφs (hI_sub_Ioo ⟨le_rfl, ht₁r.le⟩)
          (hI_sub_Ioo ⟨ht₁r.le, le_rfl⟩) ht₁r.le x).1]
      ring
    have hr_int : Integrable (fun x => om t₁ x * Ψ r x) μC := by
      have hr_mem : r ∈ Icc t₁ r := ⟨ht₁r.le, le_rfl⟩
      have hcΨ : Continuous (Ψ r) :=
        ((RateSplitAux.contDiff_ofReal hχ).mul
          (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self (hI_sub_Ioo hr_mem)) hφs)).continuous
      exact RateSplitAux.integrableOn_w_mul c m R (hom t₁ ht₁S).1 hcΨ
        (fun x hx => (hΨ_supp r hr_mem x hx).1)
    have ht₁_int : Integrable (fun x => om t₁ x * Ψ t₁ x) μC := by
      have ht₁_mem : t₁ ∈ Icc t₁ r := ⟨le_rfl, ht₁r.le⟩
      have hcΨ : Continuous (Ψ t₁) :=
        ((RateSplitAux.contDiff_ofReal hχ).mul
          (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self (hI_sub_Ioo ht₁_mem)) hφs)).continuous
      exact RateSplitAux.integrableOn_w_mul c m R (hom t₁ ht₁S).1 hcΨ
        (fun x hx => (hΨ_supp t₁ ht₁_mem x hx).1)
    have hcongr : ∫ x, (∫ ρ, om t₁ x * Ψ' ρ x ∂μI) ∂μC =
        ∫ x, (om t₁ x * Ψ r x - om t₁ x * Ψ t₁ x) ∂μC := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
      exact hpt x hx
    rw [hcongr, integral_sub hr_int ht₁_int]
    rfl
  let K' : ℝ → ℝ → ℂ := fun ρ τ => ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ' ρ) x
  let μI : Measure ℝ := volume.restrict (Icc t₁ r)
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  let Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ≤ p.1}
  have hΔ_ms : MeasurableSet Δ := measurableSet_le measurable_snd measurable_fst
  let KΔ : ℝ → ℝ → ℂ := fun ρ τ => Δ.indicator (Function.uncurry K') (ρ, τ)
  have hK'_tri : Integrable (Function.uncurry KΔ) (μI.prod μI) :=
    hKΨ'_int.indicator hΔ_ms
  have hslice_ρ : ∀ ρ ∈ Icc t₁ r,
      ∫ τ, KΔ ρ τ ∂μI = ∫ τ in t₁..ρ, K' ρ τ := by
    intro ρ hρ
    have heq : (fun τ => KΔ ρ τ) = (Iic ρ).indicator (K' ρ) := by
      funext τ; by_cases h : τ ≤ ρ <;> simp [KΔ, Δ, Function.uncurry, h]
    change ∫ τ in Icc t₁ r, KΔ ρ τ = _
    rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Iic]
    have hinter : Icc t₁ r ∩ Iic ρ = Icc t₁ ρ := by
      ext τ; simp only [mem_inter_iff, mem_Icc, mem_Iic]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2.trans hρ.2⟩, h2⟩⟩
    rw [hinter, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hρ.1]
  have hslice_τ : ∀ τ ∈ Icc t₁ r,
      ∫ ρ, KΔ ρ τ ∂μI = ∫ ρ in τ..r, K' ρ τ := by
    intro τ hτ
    have heq : (fun ρ => KΔ ρ τ) =
        (Ici τ).indicator (fun ρ => K' ρ τ) := by
      funext ρ; by_cases h : τ ≤ ρ <;> simp [KΔ, Δ, Function.uncurry, h]
    change ∫ ρ in Icc t₁ r, KΔ ρ τ = _
    rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hinter : Icc t₁ r ∩ Ici τ = Icc τ r := by
      ext ρ; simp only [mem_inter_iff, mem_Icc, mem_Ici]
      exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨hτ.1.trans h1, h2⟩, h1⟩⟩
    rw [hinter, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hτ.2]
  have hsec_ii : IntervalIntegrable (fun ρ => ∫ τ in t₁..ρ, K' ρ τ) volume t₁ r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₁r.le]
    refine hK'_tri.integral_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
    exact hslice_ρ ρ hρ
  have hsec_fub : ∫ ρ in t₁..r, ∫ τ in t₁..ρ, K' ρ τ =
      ((ladCutPair c R om φ r - ∫ x in B0579.cell c, om t₁ x * Ψ r x) -
        ∫ τ in t₁..r, ∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ τ) x) := by
    rw [intervalIntegral.integral_of_le ht₁r.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hlhs : ∫ ρ in Icc t₁ r, (∫ τ in t₁..ρ, K' ρ τ) =
        ∫ ρ, (∫ τ, KΔ ρ τ ∂μI) ∂μI := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
      exact (hslice_ρ ρ hρ).symm
    rw [hlhs, MeasureTheory.integral_integral_swap hK'_tri]
    have hrhs : ∫ τ, (∫ ρ, KΔ ρ τ ∂μI) ∂μI =
        ∫ τ in Icc t₁ r, ((∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ r) x) -
          (∫ x in B0579.cell c, ladFlowCx tr (om τ) (u τ) τ (Ψ τ) x)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      rw [hslice_τ τ hτ, cut_inner_fubini tr hc0 ht₀ hsS ht₁ ht₁r hrs hR hm
        rfl rfl (fun σ hσ => (hom σ hσ).1) hu hφs hΨ_supp hΨ'_sm hΨ'_supp hΨ_int hτ]
    rw [hrhs, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht₁r.le]
    have hr_ii := (hwk_cx (Ψ r) (hΨ_test r ⟨ht₁r.le, le_rfl⟩).1
      (hΨ_test r ⟨ht₁r.le, le_rfl⟩).2 r ⟨ht₁r.le, le_rfl⟩).2.1
    have hr_wk := (hwk_cx (Ψ r) (hΨ_test r ⟨ht₁r.le, le_rfl⟩).1
      (hΨ_test r ⟨ht₁r.le, le_rfl⟩).2 r ⟨ht₁r.le, le_rfl⟩).2.2
    rw [intervalIntegral.integral_sub hr_ii hdiag_ii, ← hr_wk]
    rfl
  have hdt_ii : IntervalIntegrable (fun ρ => ∫ x in B0579.cell c, om ρ x * Ψ' ρ x) volume t₁ r := by
    refine (hfirst_cont.intervalIntegrable_of_Icc ht₁r.le |>.add hsec_ii).congr fun ρ hρ => ?_
    rw [uIoc_of_le ht₁r.le] at hρ
    exact (hdt_pair_eq ρ ⟨hρ.1.le, hρ.2⟩).symm
  have hrate_ii : IntervalIntegrable (fun ρ => ladRate tr om u φ R ρ) volume t₁ r :=
    hdiag_ii.add hdt_ii
  refine ⟨hrate_ii, ?_⟩
  have hdt_int : ∫ ρ in t₁..r, ∫ x in B0579.cell c, om ρ x * Ψ' ρ x =
      (∫ ρ in t₁..r, ∫ x in B0579.cell c, om t₁ x * Ψ' ρ x) +
        ∫ ρ in t₁..r, ∫ τ in t₁..ρ, K' ρ τ := by
    have hcongr : ∫ ρ in t₁..r, ∫ x in B0579.cell c, om ρ x * Ψ' ρ x =
        ∫ ρ in t₁..r, ((∫ x in B0579.cell c, om t₁ x * Ψ' ρ x) + ∫ τ in t₁..ρ, K' ρ τ) :=
      intervalIntegral.integral_congr fun ρ hρ => by
        rw [uIcc_of_le ht₁r.le] at hρ; exact hdt_pair_eq ρ hρ
    rw [hcongr, intervalIntegral.integral_add (hfirst_cont.intervalIntegrable_of_Icc ht₁r.le) hsec_ii]
  unfold ladRate
  change _ = ∫ ρ in t₁..r,
    ((∫ x in B0579.cell c, ladFlowCx tr (om ρ) (u ρ) ρ (Ψ ρ) x) +
      ∫ x in B0579.cell c, om ρ x * Ψ' ρ x)
  rw [intervalIntegral.integral_add hdiag_ii hdt_ii, hdt_int, hfirst_fub, hsec_fub]
  ring

private lemma pointwise_rate_split_gen {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t₀ S s : ℝ} (_hc : 0 < c) (ht₀ : 0 ≤ t₀) (hsS : s ≤ S)
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hom : ∀ ρ ∈ Icc t₀ S, MemLp (om ρ) 2 (B0579.cellMeasure c m))
    (hu : ∀ ρ ∈ Icc t₀ S, ∀ j : Fin 2, MemLp (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)))
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t₀ s ×ˢ univ))
    {R : ℝ} (hR : 0 < R) {ρ : ℝ} (hρ : ρ ∈ Ioo t₀ s) :
    ladRate tr om u φ R ρ =
      (∫ x in B0579.cell c, om ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
        (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) +
          ladComm tr om φ R ρ := by
  have hρ0 : 0 ≤ ρ := ht₀.trans hρ.1.le
  have hρS : ρ ∈ Icc t₀ S := ⟨hρ.1.le, hρ.2.le.trans hsS⟩
  have hφs : ContDiff ℝ ∞ (φ ρ) := RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hρ) hφ
  have hdt : Continuous (ladDt φ ρ) := RateSplitAux.continuous_dt hρ hφ
  obtain ⟨_, _, hKcut⟩ := ladCutProps
  have hχ : ContDiff ℝ ∞ (ladCut R) := ((hKcut R hR).1 c).smooth
  have hχC : Continuous (fun x => (ladCut R x : ℂ)) := (RateSplitAux.contDiff_ofReal hχ).continuous
  have hφC : Continuous (φ ρ) := hφs.continuous
  have hpd : ∀ k : Fin 2, Continuous (fun x => (B0579.pd k (ladCut R) x : ℂ)) := fun k =>
    (RateSplitAux.contDiff_ofReal (ForceMemXAux.contDiff_pd hχ k)).continuous
  have hpdφ : ∀ k : Fin 2, Continuous (pdCx k (φ ρ)) :=
    fun k => (RateSplitAux.contDiff_pdCx hφs k).continuous
  have hlapφ : Continuous (ladLapCx (φ ρ)) := by
    unfold ladLapCx
    exact (RateSplitAux.contDiff_pdCx (RateSplitAux.contDiff_pdCx hφs 0) 0).continuous.add
      (RateSplitAux.contDiff_pdCx (RateSplitAux.contDiff_pdCx hφs 1) 1).continuous
  have hv : ∀ j : Fin 2, Continuous (fun x => (tr.v ρ x j : ℂ)) := fun j =>
    (RateSplitAux.contDiff_ofReal (RateSplitAux.continuous_v tr hρ0 j)).continuous
  have hlapP : Continuous (fun x => (lapP (ladCut R) x : ℂ)) := by
    unfold lapP
    have h0 := ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 0) 0
    have h1 := ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 1) 1
    exact (RateSplitAux.contDiff_ofReal (h0.add h1)).continuous
  have hchiC : Continuous (ladChi tr φ ρ) := by
    unfold ladChi ladTransport
    exact (hdt.add (continuous_const.mul hlapφ)).add
      (((hv 0).mul (hpdφ 0)).add ((hv 1).mul (hpdφ 1)))
  have hE : ∀ k : Fin 2, Continuous (fun x => (B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) :=
    fun k => (RateSplitAux.contDiff_ofReal
      (ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_Ec tr hρ0) k)).continuous
  have hwm := hom ρ hρS
  have hum := hu ρ hρS
  have hz1 : ∀ x : ℝ × ℝ, 2 * R < |x.2| → ladCut R x = 0 :=
    fun _ hx => RateSplitAux.cut_zero hR hx
  set Cp : ℝ × ℝ → ℂ := fun x => (ladCut R x : ℂ) * ladChi tr φ ρ x with hCp
  set Bp : ℝ × ℝ → ℂ := fun x => (ladCut R x : ℂ) * ladDt φ ρ x with hBp
  set Ep : ℝ × ℝ → ℂ := fun x =>
    (ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
      ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
        φ ρ x with hEp
  have hCc : Continuous Cp := hχC.mul hchiC
  have hBc : Continuous Bp := hχC.mul hdt
  have hEc : Continuous Ep := by
    simp only [hEp]
    refine (continuous_const.mul ?_).add ?_
    · refine (continuous_const.mul (((hpd 0).mul (hpdφ 0)).add ((hpd 1).mul (hpdφ 1)))).add
        (hlapP.mul hφC)
    · have : Continuous (fun x => ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
          tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ)) := by
        push_cast
        exact ((hv 0).mul (hpd 0)).add ((hv 1).mul (hpd 1))
      exact this.mul hφC
  have hCs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Cp x = 0 := fun x hx => by simp [hCp, hz1 x hx]
  have hBs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Bp x = 0 := fun x hx => by simp [hBp, hz1 x hx]
  have hEs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Ep x = 0 := fun x hx => by
    simp [hEp, RateSplitAux.pd_cut_zero hR 0 hx,
      RateSplitAux.pd_cut_zero hR 1 hx, RateSplitAux.lapP_cut_zero hR hx]
  have iC := RateSplitAux.integrableOn_w_mul c m R hwm hCc hCs
  have iB := RateSplitAux.integrableOn_w_mul c m R hwm hBc hBs
  have iE := RateSplitAux.integrableOn_w_mul c m R hwm hEc hEs
  have hDj : ∀ j : Fin 2, IntegrableOn (fun x => u ρ x j *
      ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) * ladCutPhi φ R ρ x)) (B0579.cell c) := by
    intro j
    have hg : Continuous (fun x => (B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) *
        ladCutPhi φ R ρ x) := (hE j).mul (hχC.mul hφC)
    have hgs : MemLp (fun x => (B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) *
        ladCutPhi φ R ρ x) 2 (volume.restrict (B0579.cell c)) :=
      RateSplitAux.memLp_supp c R hg (fun x hx => by simp [ladCutPhi, hz1 x hx])
    exact (hum j).integrable_mul hgs
  have iD : IntegrableOn (fun x => ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) (B0579.cell c) := by
    have := (hDj 0).add (hDj 1)
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [ladForce, Pi.add_apply]; ring
  have hpt : ∀ x : ℝ × ℝ,
      ladFlowCx tr (om ρ) (u ρ) ρ (ladCutPhi φ R ρ) x +
        om ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x) =
        om ρ x * Cp x - ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x + om ρ x * Ep x := by
    intro x
    have h := RateSplitAux.pointwise_split tr hχ hφs ρ (om ρ x) (u ρ x) x
      (ladDt φ ρ x) (ladChi tr φ ρ x) rfl
    unfold ladFlowCx
    have e : ladCutPhi φ R ρ = fun y => (ladCut R y : ℂ) * φ ρ y := rfl
    rw [e]
    simp only [hCp, hEp]
    linear_combination h
  have iFl : IntegrableOn (fun x => ladFlowCx tr (om ρ) (u ρ) ρ (ladCutPhi φ R ρ) x)
      (B0579.cell c) := by
    have := ((iC.sub iD).add iE).sub iB
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    have := hpt x
    simp only [Pi.add_apply, Pi.sub_apply]
    linear_combination -this
  unfold ladRate ladComm
  rw [← integral_add iFl iB]
  have heq : (fun x => ladFlowCx tr (om ρ) (u ρ) ρ (ladCutPhi φ R ρ) x +
      om ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x)) =
      fun x => (om ρ x * Cp x - ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) + om ρ x * Ep x :=
    funext hpt
  rw [heq]
  have h1 := integral_add (μ := volume.restrict (B0579.cell c))
    (f := fun x => om ρ x * Cp x - ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
    (g := fun x => om ρ x * Ep x) (iC.sub iD) iE
  have h2 := integral_sub (μ := volume.restrict (B0579.cell c))
    (f := fun x => om ρ x * Cp x)
    (g := fun x => ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) iC iD
  rw [h1, h2]

private lemma pointwise_transp_gen {ν c m : ℝ} (hm : 8 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {t₀ s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {om_ρ : ℝ × ℝ → ℂ} {u_ρ : ℝ × ℝ → Fin 2 → ℂ} {ρ : ℝ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (ht₀ : 0 ≤ t₀) (hts : t₀ < s)
    (hB : ∀ S' : ℝ, 0 ≤ S' → ∃ C : ℝ, LadTrainBdd tr m S' C)
    (hφ : IsAdjointFlow ν c m tr t₀ s g φ) (hρ : ρ ∈ Ioo t₀ s)
    (hmem : MemLp om_ρ 2 (B0579.cellMeasure c m)) (hz : HasZeroCirculation c om_ρ)
    (hbs : IsBiotSavart c om_ρ u_ρ) :
    ∫ x in B0579.cell c, om_ρ x * ladChi tr φ ρ x =
      ∫ x in B0579.cell c, ladForce tr u_ρ ρ x * φ ρ x := by
  obtain ⟨a, b, ua, ub, hT, hX, hV⟩ := ladTranspApprox m hm c om_ρ u_ρ hc1 hmem hz hbs
  obtain ⟨M, hM⟩ := ladChiBound m hm ν c tr t₀ s g φ hν hc1 ht₀ hts hB hφ
  refine ladTranspLimitM m hm ν c tr t₀ s g φ om_ρ u_ρ ρ hν hc1 ht₀ hts hB hφ hρ hmem hbs
    (hM ρ hρ).1 a b ua ub
    (fun n => ⟨(hT n).1, (hT n).2.1⟩)
    (fun n j => ⟨aesm_of_kernel (hT n).2.2.1 j, aesm_of_kernel (hT n).2.2.2 j⟩) ?_ ?_ hX hV
  · intro n
    exact ladAdjPointwise m ν c tr t₀ s g φ hν (by linarith) ht₀ hts hB hφ ρ hρ (a n) (ua n)
      (hT n).1 (hT n).2.2.1
  · intro n
    exact ladAdjPointwise m ν c tr t₀ s g φ hν (by linarith) ht₀ hts hB hφ ρ hρ (b n) (ub n)
      (hT n).2.1 (hT n).2.2.2

private lemma pointwise_rate_tendsto_zero {ν c m : ℝ} (hm : 8 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {t₀ S s : ℝ} {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (ht₀ : 0 ≤ t₀) (hts : t₀ < s) (hsS : s ≤ S)
    (hB : ∀ S' : ℝ, 0 ≤ S' → ∃ C : ℝ, LadTrainBdd tr m S' C)
    (hφ : IsAdjointFlow ν c m tr t₀ s g φ)
    (hom : ∀ ρ ∈ Icc t₀ S, MemLp (om ρ) 2 (B0579.cellMeasure c m) ∧ HasZeroCirculation c (om ρ))
    (hu : ∀ ρ ∈ Icc t₀ S, IsBiotSavart c (om ρ) (u ρ))
    {ρ : ℝ} (hρ : ρ ∈ Ioo t₀ s) :
    Tendsto (fun R : ℝ => ladRate tr om u φ R ρ) atTop (𝓝 0) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hρ0 : 0 ≤ ρ := ht₀.trans hρ.1.le
  have hρS : ρ ∈ Icc t₀ S := ⟨hρ.1.le, hρ.2.le.trans hsS⟩
  obtain ⟨M, hM⟩ := ladChiBound m hm ν c tr t₀ s g φ hν hc1 ht₀ hts hB hφ
  obtain ⟨C0, hC0b⟩ := hB s (ht₀.trans hts.le)
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c := ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans ((hC0b t₀ ⟨ht₀, hts.le⟩ _ hx0).1 0)
  have hwm := (hom ρ hρS).1
  have hφm := hφ.memX ρ ⟨hρ.1.le, hρ.2.le⟩
  have hFm : MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) :=
    (ladForceMemX m ν c tr s C0 ρ hC0b ⟨hρ0, hρ.2.le⟩ (u ρ) (hu ρ hρS).1).1
  have hA := ladCutLimit c m (om ρ) (ladChi tr φ ρ) hwm (hM ρ hρ).1
  have hBl := ladCutLimit c m (ladForce tr (u ρ) ρ) (φ ρ) hFm hφm
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  have hCm : Tendsto (fun R : ℝ => ladComm tr om φ R ρ) atTop (𝓝 0) := by
    have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C0 :=
      fun x hx j => (hC0b ρ ⟨hρ0, hρ.2.le⟩ x hx).1 j
    have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hwm hφm
    have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ ⟨hρ.1.le, hρ.2⟩ 0)
    have i3 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ ⟨hρ.1.le, hρ.2⟩ 1)
    have hI := (i1.add i2).add i3
    have hbd := RateBoundAux.comm_bound tr om φ ρ K C0 hK0 hC00
      (fun R hR x j => (hK R hR).2.2.2.2.1 x j)
      (fun R hR x => (hK R hR).2.2.2.2.2 x) hv hI
    set Q : ℝ := ∫ x in B0579.cell c,
      (‖om ρ x‖ * ‖φ ρ x‖ + ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖)
    have hlim0 : Tendsto (fun R : ℝ => (3 * |ν| * K + 2 * C0 * K) * R⁻¹ * Q) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.const_mul (3 * |ν| * K + 2 * C0 * K)).mul_const Q
      simpa using this
    refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hbd R hR
  have hsum := (hA.sub hBl).add hCm
  have htr := pointwise_transp_gen hm tr hν hc1 ht₀ hts hB hφ hρ hwm (hom ρ hρS).2 (hu ρ hρS)
  rw [htr, sub_self, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (pointwise_rate_split_gen tr hc0 ht₀ hsS (fun σ hσ => (hom σ hσ).1)
    (fun σ hσ j => (hu σ hσ).1 j) hφ.jointSmooth hR hρ).symm

private lemma interior_rate_dom {ν c m : ℝ} (hm : 8 < m)
    (tr : UnforcedLeray.B0140.TrainSol ν c) {t₀ S s t₁ r M_om : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hν : 0 < ν) (hc1 : 1 ≤ c) (ht₀ : 0 ≤ t₀) (ht₁ : t₀ < t₁) (ht₁r : t₁ < r)
    (hrs : r < s) (hsS : s ≤ S) (hM_om : 0 ≤ M_om)
    (hB : ∀ S' : ℝ, 0 ≤ S' → ∃ C : ℝ, LadTrainBdd tr m S' C)
    (hφ : IsAdjointFlow ν c m tr t₀ s g φ)
    (hom : ∀ ρ ∈ Icc t₀ S, MemLp (om ρ) 2 (B0579.cellMeasure c m) ∧
      HasZeroCirculation c (om ρ) ∧ (xNorm c m (om ρ)).toReal ≤ M_om)
    (hu : ∀ ρ ∈ Icc t₀ S, IsBiotSavart c (om ρ) (u ρ)) :
    ∃ D : ℝ → ℝ, IntervalIntegrable D volume t₁ r ∧
      ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t₁ r, ‖ladRate tr om u φ R ρ‖ ≤ D ρ := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hts : t₀ < s := (ht₁.trans ht₁r).trans hrs
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  obtain ⟨C0, hC0b⟩ := hB s (ht₀.trans hts.le)
  have hx0 : ((0 : ℝ), (0 : ℝ)) ∈ B0579.cell c := ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans ((hC0b t₀ ⟨ht₀, hts.le⟩ _ hx0).1 0)
  have hφc : ContinuousOn (fun ρ => (xNorm c (-m) (φ ρ)).toReal) (Icc t₀ s) :=
    RateBoundAux.contOn_norm φ (fun ρ h => hφ.memX ρ h) (fun ρ h => hφ.strongCont ρ h)
  obtain ⟨Bφ, hB0, hBφ⟩ := RateBoundAux.bdd_of_cont hφc
  obtain ⟨M, hM⟩ := ladChiBound m hm ν c tr t₀ s g φ hν hc1 ht₀ hts hB hφ
  obtain ⟨C_bs, hC_bs⟩ := ladBSBound m hm
  have hU : ∀ ρ ∈ Icc t₁ r, ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (max C_bs 0) * ENNReal.ofReal M_om := by
    intro ρ hρ j
    have hρS : ρ ∈ Icc t₀ S := ⟨ht₁.le.trans hρ.1, (hρ.2.trans hrs.le).trans hsS⟩
    have h1 := hC_bs c hc1 (om ρ) (hom ρ hρS).1 (hom ρ hρS).2.1 (u ρ) (hu ρ hρS) j
    have h2 : xNorm c m (om ρ) ≤ ENNReal.ofReal M_om :=
      RateBoundAux.ofReal_toReal_le (hom ρ hρS).1.eLpNorm_ne_top hM_om (hom ρ hρS).2.2
    exact h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) h2)
  set Fe : ℝ≥0∞ := ENNReal.ofReal C0 *
    (ENNReal.ofReal (max C_bs 0) * ENNReal.ofReal M_om +
      ENNReal.ofReal (max C_bs 0) * ENNReal.ofReal M_om)
  have hFe : Fe ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C0))
      (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) <;>
      exact ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := max C_bs 0))
        (ENNReal.ofReal_ne_top (r := M_om))
  have hFe0 : 0 ≤ Fe.toReal := ENNReal.toReal_nonneg
  have hforce : ∀ ρ ∈ Icc t₁ r, MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ Fe.toReal := by
    intro ρ hρ
    have hρS : ρ ∈ Icc t₀ S := ⟨ht₁.le.trans hρ.1, (hρ.2.trans hrs.le).trans hsS⟩
    obtain ⟨h1, h2⟩ := ladForceMemX m ν c tr s C0 ρ hC0b
      ⟨ht₀.trans (ht₁.le.trans hρ.1), hρ.2.trans hrs.le⟩ (u ρ) (hu ρ hρS).1
    exact ⟨h1, ENNReal.toReal_mono hFe
      (h2.trans (mul_le_mul' le_rfl (add_le_add (hU ρ hρ 0) (hU ρ hρ 1))))⟩
  have hK2 : 0 ≤ 3 * |ν| * K + 2 * C0 * K := by positivity
  have hr_mem : r ∈ Ico t₀ s := ⟨(ht₁.trans ht₁r).le, hrs⟩
  have hsub_uIcc : uIcc t₁ r ⊆ uIcc t₀ r := by
    rw [uIcc_of_le ht₁r.le, uIcc_of_le (ht₁.trans ht₁r).le]
    exact Icc_subset_Icc_left ht₁.le
  have h0 := (ladAdjGradInt m hm ν c tr t₀ s g φ hν hc1 ht₀ hts hB hφ r hr_mem 0).mono_set hsub_uIcc
  have h1 := (ladAdjGradInt m hm ν c tr t₀ s g φ hν hc1 ht₀ hts hB hφ r hr_mem 1).mono_set hsub_uIcc
  refine ⟨fun ρ => (M_om * |M| + Fe.toReal * Bφ + (3 * |ν| * K + 2 * C0 * K) * (M_om * Bφ)) +
    (3 * |ν| * K + 2 * C0 * K) * M_om *
      ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
        (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal),
    intervalIntegrable_const.add ((h0.add h1).const_mul _), ?_⟩
  intro R hR ρ hρ
  have hρs : ρ ∈ Ioo t₀ s := ⟨ht₁.trans hρ.1, hρ.2.trans hrs⟩
  have hρI : ρ ∈ Icc t₁ r := ⟨hρ.1.le, hρ.2.le⟩
  have hρ_ts : ρ ∈ Icc t₀ s := ⟨hρs.1.le, hρs.2.le⟩
  have hρK : ρ ∈ Ico t₀ s := ⟨hρs.1.le, hρs.2⟩
  have hρS : ρ ∈ Icc t₀ S := ⟨hρs.1.le, hρs.2.le.trans hsS⟩
  have hR0 : 0 < R := by linarith
  have hq : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hq1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  beta_reduce
  rw [pointwise_rate_split_gen tr hc0 ht₀ hsS (fun σ hσ => (hom σ hσ).1)
    (fun σ hσ j => (hu σ hσ).1 j) hφ.jointSmooth hR0 hρs]
  obtain ⟨hχm, hχn⟩ := hM ρ hρs
  have hχ' : (xNorm c (-m) (ladChi tr φ ρ)).toReal ≤ |M| :=
    ENNReal.toReal_le_of_le_ofReal (abs_nonneg M)
      (hχn.trans (ENNReal.ofReal_le_ofReal (le_abs_self M)))
  have hcut := hK R hR0
  have hcont : Continuous (ladCut R) := (hcut.1 c).continuous
  have hcb : ∀ x, |ladCut R x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hcut.2.1 x).1]; exact (hcut.2.1 x).2
  have hwm := (hom ρ hρS).1
  have hφm := hφ.memX ρ hρ_ts
  have ea : ‖∫ x in B0579.cell c, om ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)‖ ≤ M_om * |M| :=
    (RateBoundAux.cs_cut c m hcont hcb hwm hχm).trans
      (mul_le_mul (hom ρ hρS).2.2 hχ' ENNReal.toReal_nonneg hM_om)
  have eb : ‖∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x‖ ≤ Fe.toReal * Bφ :=
    (RateBoundAux.cs_cut c m hcont hcb (hforce ρ hρI).1 hφm).trans
      (mul_le_mul (hforce ρ hρI).2 (hBφ ρ hρ_ts) ENNReal.toReal_nonneg hFe0)
  have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C0 :=
    fun x hx j => (hC0b ρ ⟨ht₀.trans hρs.1.le, hρs.2.le⟩ x hx).1 j
  have i1 := CommVanishAux.integrableOn_cell_norm_mul c m hwm hφm
  have i2 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 0)
  have i3 := CommVanishAux.integrableOn_cell_norm_mul c m hwm (hφ.memH1 ρ hρK 1)
  have hI := (i1.add i2).add i3
  have ec := RateBoundAux.comm_bound tr om φ ρ K C0 hK0 hC00
    (fun R hR x j => (hK R hR).2.2.2.2.1 x j)
    (fun R hR x => (hK R hR).2.2.2.2.2 x) hv hI R hR
  have hint : ∫ x in B0579.cell c, (‖om ρ x‖ * ‖φ ρ x‖ + ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) =
      (∫ x in B0579.cell c, ‖om ρ x‖ * ‖φ ρ x‖) +
        (∫ x in B0579.cell c, ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖) +
        ∫ x in B0579.cell c, ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖ := by
    rw [integral_add (f := fun x => ‖om ρ x‖ * ‖φ ρ x‖ + ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖)
      (g := fun x => ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) (i1.add i2) i3, integral_add i1 i2]
  have c1 := (RateBoundAux.cs_norm c m hwm hφm).trans
    (mul_le_mul (hom ρ hρS).2.2 (hBφ ρ hρ_ts) ENNReal.toReal_nonneg hM_om)
  have c2 := (RateBoundAux.cs_norm c m hwm (hφ.memH1 ρ hρK 0)).trans
    (mul_le_mul_of_nonneg_right (hom ρ hρS).2.2 ENNReal.toReal_nonneg)
  have c3 := (RateBoundAux.cs_norm c m hwm (hφ.memH1 ρ hρK 1)).trans
    (mul_le_mul_of_nonneg_right (hom ρ hρS).2.2 ENNReal.toReal_nonneg)
  have hIle : (∫ x in B0579.cell c, (‖om ρ x‖ * ‖φ ρ x‖ + ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖)) ≤ M_om * Bφ +
      M_om * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
        (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal) := by
    rw [hint, mul_add]
    have c2' : (∫ x in B0579.cell c, ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖) ≤
        M_om * (eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal := c2
    have c3' : (∫ x in B0579.cell c, ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) ≤
        M_om * (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal := c3
    linarith
  have hI0 : 0 ≤ ∫ x in B0579.cell c, (‖om ρ x‖ * ‖φ ρ x‖ + ‖om ρ x‖ * ‖pdCx 0 (φ ρ) x‖ +
      ‖om ρ x‖ * ‖pdCx 1 (φ ρ) x‖) := integral_nonneg fun x => by positivity
  have ec' : ‖ladComm tr om φ R ρ‖ ≤ (3 * |ν| * K + 2 * C0 * K) *
      (M_om * Bφ + M_om * ((eLpNorm (pdCx 0 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal +
        (eLpNorm (pdCx 1 (φ ρ)) 2 (B0579.cellMeasure c (-m))).toReal)) := by
    refine ec.trans ?_
    calc _ ≤ (3 * |ν| * K + 2 * C0 * K) * 1 * _ := by gcongr
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hIle hK2
  have hsub := norm_add_le ((∫ x in B0579.cell c, om ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
    ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) (ladComm tr om φ R ρ)
  have hsub2 := norm_sub_le (∫ x in B0579.cell c, om ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x))
    (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
  nlinarith [hsub, hsub2, ea, eb, ec']

private lemma tendsto_cutPhi_xNorm_nat {c m t₀ s r₁ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hr₁ : r₁ ∈ Ioo t₀ s)
    (hφs : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t₀ s ×ˢ univ))
    (hφm : MemLp (φ r₁) 2 (B0579.cellMeasure c (-m))) :
    Tendsto (fun n : ℕ => (xNorm c (-m) (ladCutPhi φ ((n : ℝ) + 1) r₁ - φ r₁)).toReal)
      atTop (𝓝 0) := by
  let μ : Measure (ℝ × ℝ) := B0579.cellMeasure c (-m)
  have hφ_cont : Continuous (φ r₁) :=
    (RateSplitAux.contDiff_slice (Ioo_subset_Ico_self hr₁) hφs).continuous
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n x =>
    ‖ladCutPhi φ ((n : ℝ) + 1) r₁ x - φ r₁ x‖ₑ ^ 2
  let bnd : ℝ × ℝ → ℝ≥0∞ := fun x => ‖φ r₁ x‖ₑ ^ 2
  have hFm : ∀ n, Measurable (F n) := fun n => by
    have hc : Continuous (fun x => ladCutPhi φ ((n : ℝ) + 1) r₁ x - φ r₁ x) :=
      ((Complex.continuous_ofReal.comp (CutLimitAux.continuous_cut _)).mul hφ_cont).sub hφ_cont
    exact hc.measurable.enorm.pow_const 2
  have h_bnd : ∀ n, F n ≤ᵐ[μ] bnd := fun n => Eventually.of_forall fun x => by
    dsimp only [F, bnd, ladCutPhi]
    have heq : (ladCut ((n : ℝ) + 1) x : ℂ) * φ r₁ x - φ r₁ x =
        ((ladCut ((n : ℝ) + 1) x - 1 : ℝ) : ℂ) * φ r₁ x := by push_cast; ring
    have hle1 : ‖((ladCut ((n : ℝ) + 1) x - 1 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h0 := CutLimitAux.nonneg ((n : ℝ) + 1) x
      have h1 := CutLimitAux.le_one ((n : ℝ) + 1) x
      exact ⟨by linarith, by linarith⟩
    have hnrm : ‖(ladCut ((n : ℝ) + 1) x : ℂ) * φ r₁ x - φ r₁ x‖ ≤ ‖φ r₁ x‖ := by
      rw [heq, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hle1
    have henorm : ‖(ladCut ((n : ℝ) + 1) x : ℂ) * φ r₁ x - φ r₁ x‖ₑ ≤ ‖φ r₁ x‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hnrm
    exact pow_le_pow_left' henorm 2
  have h_fin : ∫⁻ x, bnd x ∂μ ≠ ⊤ := by
    have hx : (∫⁻ x, bnd x ∂μ) ^ (1 / 2 : ℝ) = xNorm c (-m) (φ r₁) := by
      unfold xNorm
      rw [T06.eLpNorm_two_eq_lintegral]
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hx
    exact hφm.eLpNorm_ne_top hx.symm
  have h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (0 : ℝ≥0∞)) :=
    Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|x.2|⌉₊] with n hn
      have hle : |x.2| + 1 ≤ (n : ℝ) + 1 := by
        have hceil : |x.2| ≤ (⌈|x.2|⌉₊ : ℝ) := Nat.le_ceil _
        have hnat : (⌈|x.2|⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      dsimp only [F, ladCutPhi]
      rw [CutLimitAux.eq_one hle]
      simp
  have ht_lint := tendsto_lintegral_of_dominated_convergence bnd hFm h_bnd h_fin h_lim
  rw [lintegral_zero] at ht_lint
  have ht_rpow : Tendsto (fun n : ℕ => xNorm c (-m) (ladCutPhi φ ((n : ℝ) + 1) r₁ - φ r₁))
      atTop (𝓝 0) := by
    have hcont_rpow := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hcont_rpow
    refine (hcont_rpow.comp ht_lint).congr fun n => ?_
    dsimp only [Function.comp_apply]
    unfold xNorm
    rw [T06.eLpNorm_two_eq_lintegral]
    rfl
  have ht_real := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht_rpow
  rw [ENNReal.toReal_zero] at ht_real
  exact ht_real

/-- Continuity of `ladPair c om φ` on `Icc t₀ s` without strong continuity of `om`, using density
of `Ioo t₀ s` and continuity of the primitive of the frozen cut-test weak equation. -/
private lemma ladPair_contOn_Icc {ν c m : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {t₀ S s M_om : ℝ}
    {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hc0 : 0 < c) (hts : t₀ < s) (hsS : s ≤ S) (hM_om : 0 ≤ M_om)
    (hφ : IsAdjointFlow ν c m tr t₀ s g φ)
    (hom : ∀ τ ∈ Icc t₀ S, MemLp (om τ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (om τ)).toReal ≤ M_om)
    (hwk : ∀ ψ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc t₀ S,
      IntervalIntegrable (fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x)
        volume t₀ τ ∧
        ∫ x in B0579.cell c, om τ x * (ψ x : ℂ) =
          ∫ σ in t₀..τ, ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x) :
    ContinuousOn (ladPair c om φ) (Icc t₀ s) := by
  intro s₀ hs₀
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  let B : ℝ := M_om + 1
  have hB_pos : 0 < B := by dsimp [B]; linarith
  have hη_pos : 0 < ε / (8 * B) := by positivity
  have hφ_lim : Tendsto (fun τ => (xNorm c (-m) (φ τ - φ s₀)).toReal) (𝓝[Icc t₀ s] s₀) (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hφ.strongCont s₀ hs₀)
    rw [ENNReal.toReal_zero] at ht
    exact ht
  have hev1 : ∀ᶠ τ in 𝓝[Icc t₀ s] s₀, (xNorm c (-m) (φ τ - φ s₀)).toReal < ε / (8 * B) :=
    hφ_lim.eventually (gt_mem_nhds hη_pos)
  rw [eventually_nhdsWithin_iff] at hev1
  have hs₀_cl : s₀ ∈ closure (Ioo t₀ s) := by rwa [closure_Ioo hts.ne]
  obtain ⟨r₁, hr₁_mem⟩ : (Ioo t₀ s ∩ {τ | τ ∈ Icc t₀ s →
      (xNorm c (-m) (φ τ - φ s₀)).toReal < ε / (8 * B)}).Nonempty := by
    have hmem : {τ | τ ∈ Icc t₀ s → (xNorm c (-m) (φ τ - φ s₀)).toReal < ε / (8 * B)} ∈ 𝓝 s₀ :=
      hev1
    obtain ⟨r₁, hr₁U, hr₁I⟩ := mem_closure_iff_nhds.1 hs₀_cl _ hmem
    exact ⟨r₁, hr₁I, hr₁U⟩
  have hr₁ : r₁ ∈ Ioo t₀ s := hr₁_mem.1
  have hr₁_close : (xNorm c (-m) (φ r₁ - φ s₀)).toReal < ε / (8 * B) :=
    hr₁_mem.2 ⟨hr₁.1.le, hr₁.2.le⟩
  have ht_cut := tendsto_cutPhi_xNorm_nat hr₁ hφ.jointSmooth (hφ.memX r₁ ⟨hr₁.1.le, hr₁.2.le⟩)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (ht_cut.eventually (gt_mem_nhds hη_pos))
  let R : ℝ := (n₀ : ℝ) + 1
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hR_close : (xNorm c (-m) (ladCutPhi φ R r₁ - φ r₁)).toReal < ε / (8 * B) := hn₀ n₀ le_rfl
  let F : ℝ × ℝ → ℂ := ladCutPhi φ R r₁
  have hF_close : (xNorm c (-m) (F - φ r₁)).toReal < ε / (8 * B) := hR_close
  have hF_mem : MemLp F 2 (B0579.cellMeasure c (-m)) :=
    LadPRPairAux.memLp_cutPhi hR0 hφ.jointSmooth ⟨hr₁.1.le, hr₁.2⟩ (-m)
  have hF_test := ladPRTest c t₀ s φ hc0 hφ.jointSmooth hφ.periodic R hR0 r₁ ⟨hr₁.1.le, hr₁.2⟩
  have hF_pair_cont : ContinuousOn (fun τ => ∫ x in B0579.cell c, om τ x * F x) (Icc t₀ s) := by
    let kre : ℝ → ℂ := fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ (fun y => (F y).re) x
    let kim : ℝ → ℂ := fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ (fun y => (F y).im) x
    have hs_mem : s ∈ Icc t₀ S := ⟨hts.le, hsS⟩
    have hire : IntervalIntegrable kre volume t₀ s := (hwk _ hF_test.1 s hs_mem).1
    have hiim : IntervalIntegrable kim volume t₀ s := (hwk _ hF_test.2 s hs_mem).1
    have hcre : ContinuousOn (fun τ => ∫ σ in t₀..τ, kre σ) (Icc t₀ s) := by
      have hc := intervalIntegral.continuousOn_primitive_interval' hire left_mem_uIcc
      rwa [uIcc_of_le hts.le] at hc
    have hcim : ContinuousOn (fun τ => ∫ σ in t₀..τ, kim σ) (Icc t₀ s) := by
      have hc := intervalIntegral.continuousOn_primitive_interval' hiim left_mem_uIcc
      rwa [uIcc_of_le hts.le] at hc
    refine (hcre.add ((continuousOn_const (c := Complex.I)).mul hcim)).congr fun τ hτ => ?_
    have hτS : τ ∈ Icc t₀ S := ⟨hτ.1, hτ.2.trans hsS⟩
    have i_re := Exist.lfc_integrableOn_cplx_test (hom τ hτS).1 hF_test.1
    have i_im := Exist.lfc_integrableOn_cplx_test (hom τ hτS).1 hF_test.2
    have hsplit : (fun x => om τ x * F x) =
        fun x => om τ x * ((F x).re : ℂ) + Complex.I * (om τ x * ((F x).im : ℂ)) := by
      funext x
      conv_lhs => rw [← Complex.re_add_im (F x)]
      ring
    rw [hsplit, integral_add i_re (i_im.const_mul Complex.I), integral_const_mul,
      (hwk _ hF_test.1 τ hτS).2, (hwk _ hF_test.2 τ hτS).2]; rfl
  have happrox : ∀ τ ∈ Icc t₀ s,
      ‖ladPair c om φ τ - ∫ x in B0579.cell c, om τ x * F x‖ ≤
        M_om * (xNorm c (-m) (φ τ - F)).toReal := by
    intro τ hτ
    have hτS : τ ∈ Icc t₀ S := ⟨hτ.1, hτ.2.trans hsS⟩
    have hwm := (hom τ hτS).1
    have hφm := hφ.memX τ hτ
    have i1 := (PairContAux.holder hwm hφm).1
    have i2 := (PairContAux.holder hwm hF_mem).1
    have hH := PairContAux.holder hwm (hφm.sub hF_mem)
    have heq : ladPair c om φ τ - (∫ x in B0579.cell c, om τ x * F x) =
        ∫ x in B0579.cell c, om τ x * (φ τ x - F x) := by
      unfold ladPair
      rw [← integral_sub i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun x => (mul_sub _ _ _).symm)
    rw [heq]
    exact hH.2.trans (mul_le_mul_of_nonneg_right (hom τ hτS).2 ENNReal.toReal_nonneg)
  have hs₀F_lt : (xNorm c (-m) (φ s₀ - F)).toReal < 2 * (ε / (8 * B)) := by
    have hms₀ := hφ.memX s₀ hs₀
    have hmr₁ := hφ.memX r₁ ⟨hr₁.1.le, hr₁.2.le⟩
    have heq : φ s₀ - F = (φ s₀ - φ r₁) + (φ r₁ - F) := by abel
    have htri : xNorm c (-m) (φ s₀ - F) ≤ xNorm c (-m) (φ s₀ - φ r₁) + xNorm c (-m) (φ r₁ - F) := by
      rw [heq]
      exact eLpNorm_add_le (hms₀.sub hmr₁).1 (hmr₁.sub hF_mem).1 one_le_two
    have hc1 : xNorm c (-m) (φ s₀ - φ r₁) = xNorm c (-m) (φ r₁ - φ s₀) :=
      eLpNorm_sub_comm _ _ _ _
    have hc2 : xNorm c (-m) (φ r₁ - F) = xNorm c (-m) (F - φ r₁) :=
      eLpNorm_sub_comm _ _ _ _
    rw [hc1, hc2] at htri
    have hf1 : xNorm c (-m) (φ r₁ - φ s₀) ≠ ⊤ := (hmr₁.sub hms₀).eLpNorm_ne_top
    have hf2 : xNorm c (-m) (F - φ r₁) ≠ ⊤ := (hF_mem.sub hmr₁).eLpNorm_ne_top
    have htr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf1, hf2⟩) htri
    rw [ENNReal.toReal_add hf1 hf2] at htr
    linarith
  have hev_F : ∀ᶠ τ in 𝓝[Icc t₀ s] s₀,
      dist (∫ x in B0579.cell c, om τ x * F x) (∫ x in B0579.cell c, om s₀ x * F x) < ε / 4 :=
    Metric.tendsto_nhds.1 (hF_pair_cont s₀ hs₀) (ε / 4) (by positivity)
  have hev_φ : ∀ᶠ τ in 𝓝[Icc t₀ s] s₀, (xNorm c (-m) (φ τ - φ s₀)).toReal < ε / (8 * B) :=
    hφ_lim.eventually (gt_mem_nhds hη_pos)
  filter_upwards [self_mem_nhdsWithin, hev_F, hev_φ] with τ hτ hF_diff hφ_diff
  rw [dist_eq_norm] at hF_diff ⊢
  have hτF_lt : (xNorm c (-m) (φ τ - F)).toReal < 3 * (ε / (8 * B)) := by
    have hmτ := hφ.memX τ hτ
    have hms₀ := hφ.memX s₀ hs₀
    have heq : φ τ - F = (φ τ - φ s₀) + (φ s₀ - F) := by abel
    have htri : xNorm c (-m) (φ τ - F) ≤ xNorm c (-m) (φ τ - φ s₀) + xNorm c (-m) (φ s₀ - F) := by
      rw [heq]
      exact eLpNorm_add_le (hmτ.sub hms₀).1 (hms₀.sub hF_mem).1 one_le_two
    have hf1 : xNorm c (-m) (φ τ - φ s₀) ≠ ⊤ := (hmτ.sub hms₀).eLpNorm_ne_top
    have hf2 : xNorm c (-m) (φ s₀ - F) ≠ ⊤ := (hms₀.sub hF_mem).eLpNorm_ne_top
    have htr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf1, hf2⟩) htri
    rw [ENNReal.toReal_add hf1 hf2] at htr
    linarith
  have b_τ : ‖ladPair c om φ τ - ∫ x in B0579.cell c, om τ x * F x‖ ≤
      B * (3 * (ε / (8 * B))) := by
    have h1 := happrox τ hτ
    have h2 : M_om * (xNorm c (-m) (φ τ - F)).toReal ≤ B * (3 * (ε / (8 * B))) := by
      have hMB : M_om ≤ B := by dsimp [B]; linarith
      exact mul_le_mul hMB hτF_lt.le ENNReal.toReal_nonneg hB_pos.le
    exact h1.trans h2
  have b_s₀ : ‖ladPair c om φ s₀ - ∫ x in B0579.cell c, om s₀ x * F x‖ ≤
      B * (2 * (ε / (8 * B))) := by
    have h1 := happrox s₀ hs₀
    have h2 : M_om * (xNorm c (-m) (φ s₀ - F)).toReal ≤ B * (2 * (ε / (8 * B))) := by
      have hMB : M_om ≤ B := by dsimp [B]; linarith
      exact mul_le_mul hMB hs₀F_lt.le ENNReal.toReal_nonneg hB_pos.le
    exact h1.trans h2
  have hsplit : ladPair c om φ τ - ladPair c om φ s₀ =
      (ladPair c om φ τ - ∫ x in B0579.cell c, om τ x * F x) +
        ((∫ x in B0579.cell c, om τ x * F x) - (∫ x in B0579.cell c, om s₀ x * F x)) -
        (ladPair c om φ s₀ - ∫ x in B0579.cell c, om s₀ x * F x) := by abel
  rw [hsplit]
  have n1 := norm_sub_le
    ((ladPair c om φ τ - ∫ x in B0579.cell c, om τ x * F x) +
      ((∫ x in B0579.cell c, om τ x * F x) - (∫ x in B0579.cell c, om s₀ x * F x)))
    (ladPair c om φ s₀ - ∫ x in B0579.cell c, om s₀ x * F x)
  have n2 := norm_add_le
    (ladPair c om φ τ - ∫ x in B0579.cell c, om τ x * F x)
    ((∫ x in B0579.cell c, om τ x * F x) - (∫ x in B0579.cell c, om s₀ x * F x))
  have hsimp3 : B * (3 * (ε / (8 * B))) = 3 * ε / 8 := by field_simp
  have hsimp2 : B * (2 * (ε / (8 * B))) = 2 * ε / 8 := by field_simp
  rw [hsimp3] at b_τ
  rw [hsimp2] at b_s₀
  linarith

/-- Small-viscosity threshold for weak uniqueness (combining `ladTrainBddAll` and `adjointExists`). -/
private def nuUniq (m : ℝ) (hm : 8 < m) : ℝ :=
  min 1 (min (ladTrainBddAll m trainWeightedJetPoly_uncond).choose
    (adjointExists m hm trainWeightedJetPoly_uncond).choose)

private lemma nuUniq_pos (m : ℝ) (hm : 8 < m) : 0 < nuUniq m hm := by
  unfold nuUniq
  exact lt_min one_pos (lt_min (ladTrainBddAll m trainWeightedJetPoly_uncond).choose_spec.1
    (adjointExists m hm trainWeightedJetPoly_uncond).choose_spec.1)

private lemma nuUniq_le_one (m : ℝ) (hm : 8 < m) : nuUniq m hm ≤ 1 :=
  min_le_left _ _

/-- **Weak uniqueness on finite age windows `[t₀, S]` without strong continuity.**
Any uniformly `X_{m,c}`-bounded zero-circulation weak solution `(om, u)` starting from `0` at `t₀`
vanishes a.e. on the cell at every `s ∈ [t₀, S]`. -/
private theorem weak_flow_unique_zero {m : ℝ} (hm : 8 < m) {ν : ℝ}
    (hν : ν ∈ Ioc 0 (nuUniq m hm))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₀ S M_om : ℝ} (ht₀ : 0 ≤ t₀) (hM_om : 0 ≤ M_om)
    {om : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hom0 : om t₀ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] 0)
    (hom : ∀ τ ∈ Icc t₀ S, MemLp (om τ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (om τ) ∧
      (xNorm (ν ^ (-2 : ℝ)) m (om τ)).toReal ≤ M_om)
    (hu : ∀ τ ∈ Icc t₀ S, IsBiotSavart (ν ^ (-2 : ℝ)) (om τ) (u τ))
    (hwk : ∀ ψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → ∀ τ ∈ Icc t₀ S,
      IntegrableOn (flowIntegrand tr (om τ) (u τ) τ ψ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntervalIntegrable (fun σ => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        flowIntegrand tr (om σ) (u σ) σ ψ x) volume t₀ τ ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), om τ x * (ψ x : ℂ) =
        ∫ σ in t₀..τ, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          flowIntegrand tr (om σ) (u σ) σ ψ x) :
    ∀ s ∈ Icc t₀ S, om s =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] 0 := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (nuUniq_le_one m hm)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hν_tb : ν ∈ Ioc 0 (ladTrainBddAll m trainWeightedJetPoly_uncond).choose :=
    ⟨hν0, hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hν_adj : ν ∈ Ioc 0 (adjointExists m hm trainWeightedJetPoly_uncond).choose :=
    ⟨hν0, hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hB : ∀ S' : ℝ, 0 ≤ S' → ∃ C : ℝ, LadTrainBdd tr m S' C :=
    (ladTrainBddAll m trainWeightedJetPoly_uncond).choose_spec.2 ν hν_tb tr hbuc
  have hAdj := (adjointExists m hm trainWeightedJetPoly_uncond).choose_spec.2 ν hν_adj tr hbuc
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hts
  · exact hom0
  have hadj_zero : ∀ g : ℝ × ℝ → ℂ, ∀ φ : ℝ → ℝ × ℝ → ℂ,
      IsAdjointFlow ν c m tr t₀ s g φ →
        ∫ x in B0579.cell c, om s x * g x = 0 := by
    intro g φ hφ
    have hstep : ∀ t₁ r, t₀ < t₁ → t₁ < r → r < s →
        ladPair c om φ r = ladPair c om φ t₁ := by
      intro t₁ r ht₁ ht₁r hrs
      obtain ⟨D, hD, hDb⟩ := interior_rate_dom hm tr hν0 hc1 ht₀ ht₁ ht₁r hrs hs.2 hM_om hB hφ hom hu
      have hprod : ∀ R : ℝ, 0 < R →
          IntervalIntegrable (fun ρ => ladRate tr om u φ R ρ) volume t₁ r ∧
            ladCutPair c R om φ r - ladCutPair c R om φ t₁ =
              ∫ ρ in t₁..r, ladRate tr om u φ R ρ :=
        fun R hR => cut_product_rule_interior tr hc1 ht₀ hs.2 ht₁ ht₁r hrs hR hM_om hm hom hu
          hwk hφ.jointSmooth hφ.periodic
      have hI : Ι t₁ r = Ioc t₁ r := Set.uIoc_of_le ht₁r.le
      have hlimInt : Tendsto (fun R : ℝ => ∫ ρ in t₁..r, ladRate tr om u φ R ρ) atTop (𝓝 0) := by
        have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
          (μ := volume) (l := atTop) (f := fun _ => (0 : ℂ))
          (F := fun R ρ => ladRate tr om u φ R ρ) D ?_ ?_ hD ?_
        · simpa using key
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
          exact (intervalIntegrable_iff.mp (hprod R hR).1).aestronglyMeasurable
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
          filter_upwards [lad_ae_ne r] with ρ hρr hρI
          rw [hI] at hρI
          exact hDb R hR ρ ⟨hρI.1, lt_of_le_of_ne hρI.2 hρr⟩
        · filter_upwards [lad_ae_ne r] with ρ hρr hρI
          rw [hI] at hρI
          exact pointwise_rate_tendsto_zero hm tr hν0 hc1 ht₀ hts hs.2 hB hφ
            (fun σ hσ => ⟨(hom σ hσ).1, (hom σ hσ).2.1⟩) hu
            ⟨ht₁.trans hρI.1, (lt_of_le_of_ne hρI.2 hρr).trans hrs⟩
      have hrS : r ∈ Icc t₀ S := ⟨(ht₁.trans ht₁r).le, hrs.le.trans hs.2⟩
      have ht₁S : t₁ ∈ Icc t₀ S := ⟨ht₁.le, (ht₁r.trans hrs).le.trans hs.2⟩
      have hcutr := ladCutLimit c m (om r) (φ r) (hom r hrS).1
        (hφ.memX r ⟨(ht₁.trans ht₁r).le, hrs.le⟩)
      have hcutt := ladCutLimit c m (om t₁) (φ t₁) (hom t₁ ht₁S).1
        (hφ.memX t₁ ⟨ht₁.le, (ht₁r.trans hrs).le⟩)
      have hdiff : Tendsto (fun R : ℝ => ladCutPair c R om φ r - ladCutPair c R om φ t₁)
          atTop (𝓝 0) := by
        refine hlimInt.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
        exact ((hprod R hR).2).symm
      exact sub_eq_zero.mp (tendsto_nhds_unique (hcutr.sub hcutt) hdiff)
    let mid : ℝ := (t₀ + s) / 2
    have hmid : mid ∈ Ioo t₀ s := ⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩
    have hconst_Ioo : EqOn (ladPair c om φ) (fun _ => ladPair c om φ mid) (Ioo t₀ s) := by
      intro r hr
      rcases lt_trichotomy r mid with hlt | rfl | hgt
      · exact (hstep r mid hr.1 hlt hmid.2).symm
      · rfl
      · exact hstep mid r hmid.1 hgt hr.2
    have hcont := ladPair_contOn_Icc tr hc0 hts hs.2 hM_om hφ
      (fun τ hτ => ⟨(hom τ hτ).1, (hom τ hτ).2.2⟩)
      (fun ψ hψ τ hτ => ⟨(hwk ψ hψ τ hτ).2.1, (hwk ψ hψ τ hτ).2.2⟩)
    have hEq_Icc : EqOn (ladPair c om φ) (fun _ => ladPair c om φ mid) (Icc t₀ s) := by
      refine hconst_Ioo.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self ?_
      rw [closure_Ioo hts.ne]
    have hst₀ : ladPair c om φ s = ladPair c om φ t₀ :=
      (hEq_Icc ⟨hts.le, le_rfl⟩).trans (hEq_Icc ⟨le_rfl, hts.le⟩).symm
    have ht₀_zero : ladPair c om φ t₀ = 0 := by
      unfold ladPair
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hom0] with x hx
      change om t₀ x * φ t₀ x = 0
      rw [hx, Pi.zero_apply, zero_mul]
    have hs_eq : ∫ x in B0579.cell c, om s x * g x = ladPair c om φ s := by
      unfold ladPair
      refine integral_congr_ae ?_
      filter_upwards [hφ.terminal] with x hx
      rw [hx]
    rw [hs_eq, hst₀, ht₀_zero]
  have hs0 : 0 ≤ s := ht₀.trans hts.le
  have ha1 : 1 ≤ clockA ν s := by unfold clockA; nlinarith
  have ha0 : 0 < clockA ν s := lt_of_lt_of_le one_pos ha1
  have hsq : 0 < Real.sqrt (clockA ν s) := Real.sqrt_pos.2 ha0
  let d_s : ℝ := cellLen c (clockA ν s)
  have hd : 0 < d_s := div_pos hc0 hsq
  have hdc : d_s * Real.sqrt (clockA ν s) = c := div_mul_cancel₀ _ hsq.ne'
  have hw_s : MemLp (om s) 2 (B0579.cellMeasure c m) := (hom s hs).1
  have hFm : Measurable (hw_s.1.mk (om s)) := hw_s.1.stronglyMeasurable_mk.measurable
  have hae_cm : om s =ᵐ[B0579.cellMeasure c m] hw_s.1.mk (om s) := hw_s.1.ae_eq_mk
  have hvol : om s =ᵐ[volume.restrict (B0579.cell c)] hw_s.1.mk (om s) :=
    (B0579.ac_cellMeasure c m).ae_le hae_cm
  have hWV : JscaleInv (clockA ν s) (om s) =ᵐ[volume.restrict (B0579.cell d_s)]
      JscaleInv (clockA ν s) (hw_s.1.mk (om s)) :=
    (jscaleInv_ae_volume ha0 hd hdc hvol.symm).symm
  have hFin : xNorm c m (hw_s.1.mk (om s)) ≠ ⊤ := by
    rw [show xNorm c m (hw_s.1.mk (om s)) = xNorm c m (om s) from eLpNorm_congr_ae hae_cm.symm]
    exact hw_s.2.ne
  have hdual := XND.dual_core (measurable_jscaleInv _ hFm) hWV
    (XND.xNorm_fin_of_scale ha1 hd hdc hFin)
  have hpair_zero : ∀ (G : ℝ × ℝ → ℂ), MemLp G 2 (B0579.cellMeasure d_s (-m)) →
      ∫ y in B0579.cell d_s, JscaleInv (clockA ν s) (om s) y * G y = 0 := by
    intro G hG
    obtain ⟨φ, hφ⟩ := hAdj t₀ s ht₀ hts G hG
    rw [pairingCoV c (clockA ν s) hc0 ha0 (om s) G]
    exact hadj_zero _ φ hφ
  have hsup_zero : (⨆ (G : ℝ × ℝ → ℂ) (_ : MemLp G 2 (B0579.cellMeasure d_s (-m)))
      (_ : xNorm d_s (-m) G ≤ 1),
      ENNReal.ofReal ‖∫ y in B0579.cell d_s, JscaleInv (clockA ν s) (om s) y * G y‖) ≤ 0 := by
    refine iSup_le fun G => iSup_le fun hG => iSup_le fun _ => ?_
    rw [hpair_zero G hG, norm_zero, ENNReal.ofReal_zero]
  have hx_zero : xNorm d_s m (JscaleInv (clockA ν s) (om s)) = 0 :=
    le_antisymm (hdual.trans hsup_zero) zero_le
  have hJ_meas : AEStronglyMeasurable (JscaleInv (clockA ν s) (om s))
      (B0579.cellMeasure d_s m) :=
    (measurable_jscaleInv _ hFm).aestronglyMeasurable.congr
      ((B0579.cellMeasure_ac d_s m).ae_le hWV.symm)
  have hJ_ae0_cm : JscaleInv (clockA ν s) (om s) =ᵐ[B0579.cellMeasure d_s m] 0 :=
    (eLpNorm_eq_zero_iff hJ_meas (by norm_num)).1 hx_zero
  have hJ_ae0_vol : JscaleInv (clockA ν s) (om s) =ᵐ[volume.restrict (B0579.cell d_s)] 0 :=
    (B0579.ac_cellMeasure d_s m).ae_le hJ_ae0_cm
  have hdiv := ae_div_sqrt_of_ae ha0 hJ_ae0_vol
  rw [hdc] at hdiv
  filter_upwards [hdiv] with x hx
  dsimp only [JscaleInv, Pi.zero_apply] at hx
  have hcoord : (Real.sqrt (clockA ν s) * (x.1 / Real.sqrt (clockA ν s)),
      Real.sqrt (clockA ν s) * (x.2 / Real.sqrt (clockA ν s))) = x := by
    ext <;> simp [mul_div_cancel₀ _ hsq.ne']
  rw [hcoord] at hx
  have ha2_ne : ((clockA ν s ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (pow_ne_zero 2 ha0.ne')
  exact (mul_eq_zero.1 hx).resolve_left ha2_ne

/-- Two `IsLinearisedFlow` solutions with a.e.-equal `X_{m,c}` zero-circulation initial data agree
a.e. on the cell at every age `s ≥ t₀`. -/
private theorem isLinearisedFlow_unique_ae {m : ℝ} (hm : 8 < m) {ν : ℝ}
    (hν : ν ∈ Ioc 0 (nuUniq m hm))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {f₁ f₂ : ℝ × ℝ → ℂ}
    (_hf₁ : MemLp f₁ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hz₁ : HasZeroCirculation (ν ^ (-2 : ℝ)) f₁)
    (hf_eq : f₁ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] f₂)
    {w₁ w₂ : ℝ → ℝ × ℝ → ℂ} {u₁ u₂ : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw₁ : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₀ f₁ w₁ u₁)
    (hw₂ : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₀ f₂ w₂ u₂) :
    ∀ s, t₀ ≤ s → w₁ s =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] w₂ s := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (nuUniq_le_one m hm)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hz₂ : HasZeroCirculation c f₂ :=
    ⟨hz₁.1.congr_fun_ae hf_eq, (integral_congr_ae hf_eq).symm.trans hz₁.2⟩
  intro s hs
  let om : ℝ → ℝ × ℝ → ℂ := fun τ x => w₁ τ x - w₂ τ x
  let u : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun τ x j => u₁ τ x j - u₂ τ x j
  have hom_mem : ∀ τ, t₀ ≤ τ → MemLp (om τ) 2 (B0579.cellMeasure c m) :=
    fun τ hτ => (hw₁.memX τ hτ).sub (hw₂.memX τ hτ)
  have hom_sc : ∀ τ, t₀ ≤ τ → Tendsto (fun τ' => xNorm c m (om τ' - om τ)) (𝓝[Ici t₀] τ) (𝓝 0) := by
    intro τ hτ
    have hsum := (hw₁.strongCont τ hτ).add (hw₂.strongCont τ hτ)
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with τ' hτ'
    have heq : om τ' - om τ = (w₁ τ' - w₁ τ) - (w₂ τ' - w₂ τ) := by
      ext x; simp [om]; ring
    rw [heq]
    exact eLpNorm_sub_le ((hw₁.memX τ' hτ').sub (hw₁.memX τ hτ)).1
      ((hw₂.memX τ' hτ').sub (hw₂.memX τ hτ)).1 one_le_two
  have hcont_norm : ContinuousOn (fun τ => (xNorm c m (om τ)).toReal) (Icc t₀ s) :=
    (RateBoundAux.contOn_norm om (fun τ h => hom_mem τ h) (fun τ h => hom_sc τ h)).mono
      Icc_subset_Ici_self
  obtain ⟨M_om, hM_om, hM_bd⟩ := RateBoundAux.bdd_of_cont hcont_norm
  have hom0 : om t₀ =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    filter_upwards [hw₁.initial, hw₂.initial, hf_eq] with x h1 h2 h12
    simp [om, h1, h2, h12]
  have hom_props : ∀ τ ∈ Icc t₀ s,
      MemLp (om τ) 2 (B0579.cellMeasure c m) ∧ HasZeroCirculation c (om τ) ∧
        (xNorm c m (om τ)).toReal ≤ M_om := by
    intro τ hτ
    have z1 := ladFlowZeroCirc m (by linarith) ν c tr t₀ f₁ w₁ u₁ hc1 hz₁ hw₁ τ hτ.1
    have z2 := ladFlowZeroCirc m (by linarith) ν c tr t₀ f₂ w₂ u₂ hc1 hz₂ hw₂ τ hτ.1
    refine ⟨hom_mem τ hτ.1, ⟨z1.1.sub z2.1, ?_⟩, hM_bd τ hτ⟩
    change ∫ x in B0579.cell c, (w₁ τ x - w₂ τ x) = 0
    rw [integral_sub z1.1 z2.1, z1.2, z2.2, sub_self]
  have hu_bs : ∀ τ ∈ Icc t₀ s, IsBiotSavart c (om τ) (u τ) := by
    intro τ hτ
    have b1 := hw₁.biotSavart τ hτ.1
    have b2 := hw₂.biotSavart τ hτ.1
    refine ⟨fun j => (b1.1 j).sub (b2.1 j), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have i1 : Integrable (fun x => u₁ τ x 0 * (B0579.pd 0 ψ x : ℂ) +
          u₁ τ x 1 * (B0579.pd 1 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (Exist.lfc_integrableOn_vol_test (b1.1 0) (hψ.pd 0)).add
          (Exist.lfc_integrableOn_vol_test (b1.1 1) (hψ.pd 1))
      have i2 : Integrable (fun x => u₂ τ x 0 * (B0579.pd 0 ψ x : ℂ) +
          u₂ τ x 1 * (B0579.pd 1 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (Exist.lfc_integrableOn_vol_test (b2.1 0) (hψ.pd 0)).add
          (Exist.lfc_integrableOn_vol_test (b2.1 1) (hψ.pd 1))
      have heq : (fun x => u τ x 0 * (B0579.pd 0 ψ x : ℂ) + u τ x 1 * (B0579.pd 1 ψ x : ℂ)) =
          fun x => (u₁ τ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ τ x 1 * (B0579.pd 1 ψ x : ℂ)) -
            (u₂ τ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ τ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
        funext x; simp [u]; ring
      rw [heq, integral_sub i1 i2, b1.2.1 ψ hψ, b2.2.1 ψ hψ, sub_self]
    · have iw1 := Exist.lfc_integrableOn_cplx_test (hw₁.memX τ hτ.1) hψ
      have iw2 := Exist.lfc_integrableOn_cplx_test (hw₂.memX τ hτ.1) hψ
      have iu1 : Integrable (fun x => u₁ τ x 0 * (B0579.pd 1 ψ x : ℂ) -
          u₁ τ x 1 * (B0579.pd 0 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (Exist.lfc_integrableOn_vol_test (b1.1 0) (hψ.pd 1)).sub
          (Exist.lfc_integrableOn_vol_test (b1.1 1) (hψ.pd 0))
      have iu2 : Integrable (fun x => u₂ τ x 0 * (B0579.pd 1 ψ x : ℂ) -
          u₂ τ x 1 * (B0579.pd 0 ψ x : ℂ)) (volume.restrict (B0579.cell c)) :=
        (Exist.lfc_integrableOn_vol_test (b2.1 0) (hψ.pd 1)).sub
          (Exist.lfc_integrableOn_vol_test (b2.1 1) (hψ.pd 0))
      have hl : (fun x => om τ x * (ψ x : ℂ)) =
          fun x => w₁ τ x * (ψ x : ℂ) - w₂ τ x * (ψ x : ℂ) := by
        funext x; simp [om]; ring
      have hr : (fun x => u τ x 0 * (B0579.pd 1 ψ x : ℂ) - u τ x 1 * (B0579.pd 0 ψ x : ℂ)) =
          fun x => (u₁ τ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ τ x 1 * (B0579.pd 0 ψ x : ℂ)) -
            (u₂ τ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ τ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
        funext x; simp [u]; ring
      rw [hl, hr, integral_sub iw1 iw2, integral_sub iu1 iu2, b1.2.2 ψ hψ, b2.2.2 ψ hψ]
  have hwk_om : ∀ ψ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc t₀ s,
      IntegrableOn (flowIntegrand tr (om τ) (u τ) τ ψ) (B0579.cell c) ∧
      IntervalIntegrable (fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x)
        volume t₀ τ ∧
      ∫ x in B0579.cell c, om τ x * (ψ x : ℂ) =
        ∫ σ in t₀..τ, ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x := by
    intro ψ hψ τ hτ
    have hfl_sub : ∀ σ, flowIntegrand tr (om σ) (u σ) σ ψ =
        fun x => flowIntegrand tr (w₁ σ) (u₁ σ) σ ψ x - flowIntegrand tr (w₂ σ) (u₂ σ) σ ψ x := by
      intro σ; funext x; unfold flowIntegrand; simp [om, u]; ring
    have hint_τ : IntegrableOn (flowIntegrand tr (om τ) (u τ) τ ψ) (B0579.cell c) := by
      rw [hfl_sub τ]
      exact (hw₁.integrable ψ hψ τ hτ.1).sub (hw₂.integrable ψ hψ τ hτ.1)
    have hcell_sub : ∀ σ, t₀ ≤ σ →
        ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x =
          (∫ x in B0579.cell c, flowIntegrand tr (w₁ σ) (u₁ σ) σ ψ x) -
            ∫ x in B0579.cell c, flowIntegrand tr (w₂ σ) (u₂ σ) σ ψ x := by
      intro σ hσ
      rw [hfl_sub σ]
      exact integral_sub (hw₁.integrable ψ hψ σ hσ) (hw₂.integrable ψ hψ σ hσ)
    have hii : IntervalIntegrable
        (fun σ => ∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x) volume t₀ τ := by
      refine ((hw₁.timeIntegrable ψ hψ τ hτ.1).sub (hw₂.timeIntegrable ψ hψ τ hτ.1)).congr
        fun σ hσ => ?_
      rw [uIoc_of_le hτ.1] at hσ
      exact (hcell_sub σ hσ.1.le).symm
    refine ⟨hint_τ, hii, ?_⟩
    have iw1 := Exist.lfc_integrableOn_cplx_test (hw₁.memX τ hτ.1) hψ
    have iw2 := Exist.lfc_integrableOn_cplx_test (hw₂.memX τ hτ.1) hψ
    have if_eq : ∫ x in B0579.cell c, f₁ x * (ψ x : ℂ) = ∫ x in B0579.cell c, f₂ x * (ψ x : ℂ) :=
      integral_congr_ae (hf_eq.mono fun x hx => by dsimp only; rw [hx])
    have hl : (fun x => om τ x * (ψ x : ℂ)) =
        fun x => w₁ τ x * (ψ x : ℂ) - w₂ τ x * (ψ x : ℂ) := by
      funext x; simp [om]; ring
    have hr_int : ∫ σ in t₀..τ, (∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x) =
        (∫ σ in t₀..τ, ∫ x in B0579.cell c, flowIntegrand tr (w₁ σ) (u₁ σ) σ ψ x) -
          ∫ σ in t₀..τ, ∫ x in B0579.cell c, flowIntegrand tr (w₂ σ) (u₂ σ) σ ψ x := by
      have hcgr : ∫ σ in t₀..τ, (∫ x in B0579.cell c, flowIntegrand tr (om σ) (u σ) σ ψ x) =
          ∫ σ in t₀..τ, ((∫ x in B0579.cell c, flowIntegrand tr (w₁ σ) (u₁ σ) σ ψ x) -
            ∫ x in B0579.cell c, flowIntegrand tr (w₂ σ) (u₂ σ) σ ψ x) :=
        intervalIntegral.integral_congr fun σ hσ => by
          rw [uIcc_of_le hτ.1] at hσ; exact hcell_sub σ hσ.1
      rw [hcgr, intervalIntegral.integral_sub (hw₁.timeIntegrable ψ hψ τ hτ.1)
        (hw₂.timeIntegrable ψ hψ τ hτ.1)]
    rw [hl, integral_sub iw1 iw2, hw₁.weak ψ hψ τ hτ.1, hw₂.weak ψ hψ τ hτ.1, if_eq, hr_int]
    ring
  have hzero := weak_flow_unique_zero hm hν tr hbuc ht₀ hM_om hom0 hom_props hu_bs hwk_om s
    ⟨hs, le_rfl⟩
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.1 hx

private lemma pd_comp_neg {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => F (-y)) x = -B0579.pd k F (-x) := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := -ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have hfun : (fun y : ℝ × ℝ => F (-y)) = F ∘ L := rfl
  unfold B0579.pd
  have hfd : fderiv ℝ (F ∘ L) x = (fderiv ℝ F (-x)).comp L :=
    ((hF (-x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  rw [hfun, hfd, ContinuousLinearMap.comp_apply]
  simp [L]

private lemma pd_neg {G : ℝ × ℝ → ℝ} (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => -G y) x = -B0579.pd k G x := by
  unfold B0579.pd
  change (fderiv ℝ (-G) x) (B0579.dir k) = -(fderiv ℝ G x) (B0579.dir k)
  rw [fderiv_neg]
  rfl

private lemma isCylTest_neg {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun x => ψ (-x)) := by
  refine ⟨hψ.smooth.comp contDiff_neg, fun x => ?_, ?_⟩
  · have hp := hψ.periodic (-x.1 - c, -x.2)
    dsimp only at hp
    have h1 : -((x.1 + c, x.2) : ℝ × ℝ) = (-x.1 - c, -x.2) := by
      ext
      · simp; ring
      · simp
    have h2 : (-x.1 - c + c, -x.2) = -x := by ext <;> simp
    rw [h1, ← hp, h2]
  · obtain ⟨B, hB⟩ := hψ.band
    refine ⟨B, fun x hx => hB (-x) ?_⟩
    simpa using hx

private lemma eLpNorm_comp_neg_cellMeasure (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    xNorm c m (fun x => F (-x)) = xNorm c m F := by
  unfold xNorm
  rw [PairContAux.eLpNorm_cellMeasure_cx, PairContAux.eLpNorm_cellMeasure_cx,
    T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral]
  congr 1
  have hjb : ∀ x : ℝ × ℝ, B0579.jb (-x) = B0579.jb x := fun x => by
    simp [B0579.jb]
  have hfn : (fun x : ℝ × ℝ => ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F (-x)‖ₑ ^ 2) =
      (fun y : ℝ × ℝ => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2) ∘ Neg.neg := by
    funext x; simp [Function.comp, hjb x]
  rw [hfn]
  exact (measurePreserving_neg_cell c).lintegral_comp_emb
    (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding
    (fun y => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2)

private lemma memLp_comp_neg_cellMeasure {c m : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => F (-x)) 2 (B0579.cellMeasure c m) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_vol : F =ᵐ[volume.restrict (B0579.cell c)] F₀ :=
    (B0579.ac_cellMeasure c m).ae_le hF.1.ae_eq_mk
  have hae_neg : (fun x => F (-x)) =ᵐ[B0579.cellMeasure c m] (fun x => F₀ (-x)) :=
    (B0579.cellMeasure_ac c m).ae_le (ae_neg_of_ae_cell hae_vol)
  have hm : AEStronglyMeasurable (fun x => F (-x)) (B0579.cellMeasure c m) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  change xNorm c m (fun x => F (-x)) < ⊤
  rw [eLpNorm_comp_neg_cellMeasure]
  exact hF.2

private lemma memLp_comp_neg_vol {c : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun x => F (-x)) 2 (volume.restrict (B0579.cell c)) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_neg : (fun x => F (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => F₀ (-x)) :=
    ae_neg_of_ae_cell hF.1.ae_eq_mk
  have hm : AEStronglyMeasurable (fun x => F (-x)) (volume.restrict (B0579.cell c)) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  rw [T06.eLpNorm_two_eq_lintegral]
  have hlint : ∫⁻ x, ‖F (-x)‖ₑ ^ 2 ∂(volume.restrict (B0579.cell c)) =
      ∫⁻ y, ‖F y‖ₑ ^ 2 ∂(volume.restrict (B0579.cell c)) :=
    (measurePreserving_neg_cell c).lintegral_comp_emb
      (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding (fun y => ‖F y‖ₑ ^ 2)
  rw [hlint, ← T06.eLpNorm_two_eq_lintegral]
  exact hF.2

/-- Propagation of central evenness (`f (-x) =ᵐ f x`) under `IsLinearisedFlow`. -/
private theorem isLinearisedFlow_even_ae {m : ℝ} (hm : 8 < m) {ν : ℝ}
    (hν : ν ∈ Ioc 0 (nuUniq m hm))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hz : HasZeroCirculation (ν ^ (-2 : ℝ)) f)
    (hf_even : (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₀ f w u) :
    ∀ s, t₀ ≤ s → (fun x => w s (-x)) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] w s := by
  let c : ℝ := ν ^ (-2 : ℝ)
  let w' : ℝ → ℝ × ℝ → ℂ := fun τ x => w τ (-x)
  let u' : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun τ x j => -u τ (-x) j
  have hlap_neg : ∀ (ψ : ℝ × ℝ → ℝ) (_ : ContDiff ℝ ∞ ψ) (x : ℝ × ℝ),
      lapP (fun y => ψ (-y)) x = lapP ψ (-x) := by
    intro ψ hψ x
    unfold lapP
    have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have hpd0 : Differentiable ℝ (B0579.pd 0 ψ) :=
      (ForceMemXAux.contDiff_pd hψ 0).differentiable (by simp)
    have hpd1 : Differentiable ℝ (B0579.pd 1 ψ) :=
      (ForceMemXAux.contDiff_pd hψ 1).differentiable (by simp)
    have e0 : B0579.pd 0 (fun y => ψ (-y)) = fun y => -B0579.pd 0 ψ (-y) :=
      funext (pd_comp_neg hdψ 0)
    have e1 : B0579.pd 1 (fun y => ψ (-y)) = fun y => -B0579.pd 1 ψ (-y) :=
      funext (pd_comp_neg hdψ 1)
    have d0 : B0579.pd 0 (fun y => -B0579.pd 0 ψ (-y)) x = B0579.pd 0 (B0579.pd 0 ψ) (-x) := by
      rw [pd_neg, pd_comp_neg hpd0 0 x, neg_neg]
    have d1 : B0579.pd 1 (fun y => -B0579.pd 1 ψ (-y)) x = B0579.pd 1 (B0579.pd 1 ψ) (-x) := by
      rw [pd_neg, pd_comp_neg hpd1 1 x, neg_neg]
    rw [e0, e1, d0, d1]
  have hpdE_odd : ∀ r : ℝ, 0 ≤ r → ∀ (j : Fin 2) (x : ℝ × ℝ),
      B0579.pd j (UnforcedLeray.B0238.Ec tr r) (-x) =
        -B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by
    intro r hr j x
    have hdE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr r) :=
      (ForceMemXAux.contDiff_Ec tr hr).differentiable (by simp)
    have heven : (fun y => UnforcedLeray.B0238.Ec tr r (-y)) = UnforcedLeray.B0238.Ec tr r :=
      funext (UnforcedLeray.B0238.Ec_even tr hr)
    have h1 := pd_comp_neg hdE j x
    rw [heven] at h1
    linarith
  have hfl_eq : ∀ (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) (r : ℝ), t₀ ≤ r → ∀ x : ℝ × ℝ,
      flowIntegrand tr (w' r) (u' r) r ψ x =
        flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) := by
    intro ψ hψ r hr x
    have hr0 : 0 ≤ r := ht₀.trans hr
    have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
    have p0 := pd_comp_neg hdψ 0 (-x)
    have p1 := pd_comp_neg hdψ 1 (-x)
    have pl := hlap_neg ψ hψ.smooth (-x)
    rw [neg_neg] at p0 p1 pl
    have hv_odd : ∀ j : Fin 2, tr.v r (-x) j = -tr.v r x j := fun j => by
      have h := congrArg (fun v : UnforcedLeray.Train.Vec => v j) (tr.isTrain.odd r hr0 x)
      simpa using h
    have eE0 := hpdE_odd r hr0 0 x
    have eE1 := hpdE_odd r hr0 1 x
    unfold flowIntegrand
    dsimp only [w', u']
    rw [p0, p1, pl, hv_odd 0, hv_odd 1, eE0, eE1, neg_neg]
    push_cast
    ring
  have hw' : IsLinearisedFlow ν c m tr t₀ f w' u' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (ae_neg_of_ae_cell hw.initial).trans hf_even
    · exact fun s hs => memLp_comp_neg_cellMeasure (hw.memX s hs)
    · intro s hs
      refine (hw.strongCont s hs).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s' _
      have heq : w' s' - w' s = fun x => (w s' - w s) (-x) := rfl
      rw [heq, eLpNorm_comp_neg_cellMeasure]
    · intro s hs
      have hbs := hw.biotSavart s hs
      refine ⟨fun j => (memLp_comp_neg_vol (hbs.1 j)).neg, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
      · have hψn := isCylTest_neg hψ
        have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
        have hpt : (fun x => u' s x 0 * (B0579.pd 0 ψ x : ℂ) + u' s x 1 * (B0579.pd 1 ψ x : ℂ)) =
            fun x => u s (-x) 0 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) +
              u s (-x) 1 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) := by
          funext x
          have p0 := pd_comp_neg hdψ 0 (-x)
          have p1 := pd_comp_neg hdψ 1 (-x)
          rw [neg_neg] at p0 p1
          dsimp only [u']
          rw [p0, p1]
          push_cast; ring
        rw [hpt, integral_cell_neg c (fun y => u s y 0 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ) +
          u s y 1 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ))]
        exact hbs.2.1 _ hψn
      · have hψn := isCylTest_neg hψ
        have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
        have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
            ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
          have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
              fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by
            funext x; simp [w']
          rw [hp]
          exact integral_cell_neg c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
        have hr : (fun x => u' s x 0 * (B0579.pd 1 ψ x : ℂ) - u' s x 1 * (B0579.pd 0 ψ x : ℂ)) =
            fun x => u s (-x) 0 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) -
              u s (-x) 1 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) := by
          funext x
          have p0 := pd_comp_neg hdψ 0 (-x)
          have p1 := pd_comp_neg hdψ 1 (-x)
          rw [neg_neg] at p0 p1
          dsimp only [u']
          rw [p0, p1]
          push_cast; ring
        rw [hl, hr, integral_cell_neg c (fun y => u s y 0 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ) -
          u s y 1 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ))]
        exact hbs.2.2 _ hψn
    · intro ψ hψ r hr
      have hψn := isCylTest_neg hψ
      have hInt : Integrable (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))
          (volume.restrict (B0579.cell c)) := hw.integrable _ hψn r hr
      exact ((measurePreserving_neg_cell c).integrable_comp_of_integrable hInt).congr
        (Eventually.of_forall fun x => (hfl_eq ψ hψ r hr x).symm)
    · intro ψ hψ s hs
      have hψn := isCylTest_neg hψ
      refine (hw.timeIntegrable _ hψn s hs).congr fun r hr => ?_
      rw [uIoc_of_le hs] at hr
      have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
          fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
        funext (hfl_eq ψ hψ r hr.1.le)
      rw [heq_r, integral_cell_neg c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
    · intro ψ hψ s hs
      have hψn := isCylTest_neg hψ
      have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
          ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
        have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
            fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp [w']
        rw [hp]
        exact integral_cell_neg c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
      have hf_int : ∫ x in B0579.cell c, f x * (ψ x : ℂ) =
          ∫ y in B0579.cell c, f y * ((fun z => ψ (-z)) y : ℂ) := by
        have hp : ∫ y in B0579.cell c, f (-y) * (ψ y : ℂ) =
            ∫ y in B0579.cell c, f y * ((fun z => ψ (-z)) y : ℂ) := by
          have hp2 : (fun y : ℝ × ℝ => f (-y) * (ψ y : ℂ)) =
              fun y => f (-y) * ((fun z => ψ (-z)) (-y) : ℂ) := by funext y; simp
          rw [hp2]
          exact integral_cell_neg c (fun y => f y * ((fun z => ψ (-z)) y : ℂ))
        rw [← hp]
        exact integral_congr_ae (hf_even.symm.mono fun y hy => by dsimp only at hy ⊢; rw [hy])
      have hr_int : ∫ r in t₀..s, (∫ x in B0579.cell c, flowIntegrand tr (w' r) (u' r) r ψ x) =
          ∫ r in t₀..s, (∫ y in B0579.cell c,
            flowIntegrand tr (w r) (u r) r (fun z => ψ (-z)) y) :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hs] at hr
          have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
              fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
            funext (hfl_eq ψ hψ r hr.1)
          rw [heq_r, integral_cell_neg c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
      rw [hl, hf_int, hr_int, hw.weak _ hψn s hs]
  exact isLinearisedFlow_unique_ae hm hν tr hbuc ht₀ hf hz (EventuallyEq.refl _ _) hw' hw

/-! ## 3. Inhomogeneous Volterra / Duhamel representation on finite age windows `[t₀, S]` -/

private lemma isLinearisedFlow_congr_initial_ae {ν c m t₀ : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f f' : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t₀ f w u)
    (hf : f =ᵐ[volume.restrict (B0579.cell c)] f') :
    IsLinearisedFlow ν c m tr t₀ f' w u where
  initial := hw.initial.trans hf
  memX := hw.memX
  strongCont := hw.strongCont
  biotSavart := hw.biotSavart
  integrable := hw.integrable
  timeIntegrable := hw.timeIntegrable
  weak φ hφ s hs := by
    rw [hw.weak φ hφ s hs]
    congr 1
    exact integral_congr_ae (hf.symm.mono fun x hx => by dsimp only; rw [hx])

private lemma isLinearisedFlow_zero_of_ae {ν c m t₀ : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    (hf : f =ᵐ[volume.restrict (B0579.cell c)] 0) :
    IsLinearisedFlow ν c m tr t₀ f (fun _ _ => 0) (fun _ _ _ => 0) where
  initial := hf.symm
  memX _ _ := MemLp.zero
  strongCont _ _ := by
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun _ => ?_)
    have h0 : ((fun _ : ℝ × ℝ => (0 : ℂ)) - fun _ => (0 : ℂ)) = 0 := by ext; simp
    rw [h0]
    simp [xNorm]
  biotSavart _ _ := ⟨fun _ => MemLp.zero, fun _ _ => by simp, fun _ _ => by simp⟩
  integrable _ _ _ _ := by unfold flowIntegrand; simp
  timeIntegrable _ _ _ _ := by unfold flowIntegrand; simp
  weak φ _ s _ := by
    have hz : ∫ x in B0579.cell c, f x * (φ x : ℂ) = 0 :=
      integral_eq_zero_of_ae (hf.mono fun x hx => by
        dsimp only [Pi.zero_apply] at hx ⊢
        rw [hx, zero_mul])
    rw [hz]
    unfold flowIntegrand
    simp

private lemma isLinearisedFlow_smul {ν c m t₀ : ℝ} (α : ℂ)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t₀ f w u) :
    IsLinearisedFlow ν c m tr t₀ (fun x => α * f x) (fun s x => α * w s x)
      (fun s x j => α * u s x j) where
  initial := hw.initial.mono fun x hx => by dsimp only; rw [hx]
  memX s hs := (hw.memX s hs).const_mul α
  strongCont s hs := by
    have hlim := ENNReal.Tendsto.const_mul (a := ‖α‖ₑ) (hw.strongCont s hs)
      (Or.inr ENNReal.coe_ne_top)
    rw [mul_zero] at hlim
    refine hlim.congr' (Eventually.of_forall fun s' => ?_)
    have heq : ((fun x => α * w s' x) - fun x => α * w s x) = α • (w s' - w s) := by
      ext x; simp [mul_sub]
    dsimp only
    unfold xNorm
    rw [heq, eLpNorm_const_smul]
  biotSavart s hs := isBiotSavart_smul α (hw.biotSavart s hs)
  integrable φ hφ r hr := by
    have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
        fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq]
    exact (hw.integrable φ hφ r hr).const_mul α
  timeIntegrable φ hφ s hs := by
    refine ((hw.timeIntegrable φ hφ s hs).const_mul α).congr fun r _ => ?_
    have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
        fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq, integral_const_mul]
  weak φ hφ s hs := by
    have hl : (fun x => α * w s x * (φ x : ℂ)) = fun x => α * (w s x * (φ x : ℂ)) := by
      funext x; ring
    have hf_eq : (fun x => α * f x * (φ x : ℂ)) = fun x => α * (f x * (φ x : ℂ)) := by
      funext x; ring
    have hr_eq : (∫ r in t₀..s, ∫ x in B0579.cell c,
        flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ x) =
        α * ∫ r in t₀..s, ∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r φ x := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
          fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
        funext x; unfold flowIntegrand; ring
      rw [heq, integral_const_mul]
    rw [hl, hf_eq, integral_const_mul, integral_const_mul, hr_eq, hw.weak φ hφ s hs, mul_add]

private lemma xNorm_cplx_vortFn {c m : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    xNorm c m (Exist.cplx (Exist.vortFn hm1 v)) = ENNReal.ofReal ‖v‖ := by
  let z0 : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
    (c := c) (m := m) hm1 := 0
  have hz0 : Exist.cplx (Exist.vortFn hm1 z0) =ᵐ[B0579.cellMeasure c m] 0 := by
    filter_upwards [Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m)] with x hx
    simpa [z0, Exist.cplx, Exist.vortFn] using hx
  have heq : Exist.cplx (Exist.vortFn hm1 v) =ᵐ[B0579.cellMeasure c m]
      Exist.cplx (Exist.vortFn hm1 v) - Exist.cplx (Exist.vortFn hm1 z0) := by
    filter_upwards [hz0] with x hx
    dsimp only [Pi.sub_apply, Pi.zero_apply] at hx ⊢
    rw [hx, sub_zero]
  calc xNorm c m (Exist.cplx (Exist.vortFn hm1 v))
      = xNorm c m (Exist.cplx (Exist.vortFn hm1 v) - Exist.cplx (Exist.vortFn hm1 z0)) :=
        eLpNorm_congr_ae heq
    _ = ENNReal.ofReal ‖v - z0‖ := Exist.stc_xNorm_cplx_sub hm1 v z0
    _ = ENNReal.ofReal ‖v‖ := by simp [z0]

private lemma vortFn_zero_ae {c m : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m) :
    Exist.vortFn hm1
      (0 : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1)
      =ᵐ[volume.restrict (B0579.cell c)] 0 := by
  filter_upwards [(B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m))]
    with x hx
  simpa [Exist.vortFn] using hx

/-- Global `IsLinearisedFlow` on `[τ, ∞)` generated by `Exist.horizonEvolution` from a real state
`u₀ : ActualVorticity hm1`. -/
private lemma horizon_real_flow {ν c m : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (hReg : Exist.Regime ν c m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (Pn : ∀ n : ℕ, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPathOn
      (c := c) (m := m) (ν := ν) hm1 tr (Nat.cast_nonneg n))
    (H : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatStripSupplier
      (c := c) (m := m) hm1)
    (hH : Exist.ScaledHeatWeak hm1 ν H) {τ : ℝ} (hτ : 0 ≤ τ)
    (u₀ : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    IsLinearisedFlow ν c m tr τ (Exist.cplx (Exist.vortFn hm1 u₀))
      (fun r => Exist.cplx (Exist.vortFn hm1 (Exist.horizonEvolution hm1 Pn H r τ u₀)))
      (fun r => Exist.stripVel hm1 (Exist.horizonEvolution hm1 Pn H r τ u₀)) := by
  have hS : ∀ n : ℕ, Exist.StripWeakLpOn hm1 tr (Pn n) H := fun n =>
    Exist.stripWeakAssemblyOnFromParts Exist.biotSavartFieldAll Exist.fluxIdentityOnAll
      Exist.mildIntegratedOnAll Exist.stripContinuityOnAll ν c m hm1 tr n (Nat.cast_nonneg n)
      (Pn n) H hReg hH
  have hUnit : ∀ a : ℝ, 0 ≤ a →
      ∀ v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1,
        Exist.IsLinFlowOn ν c m tr a (a + 1) (Exist.cplx (Exist.vortFn hm1 v))
          (fun r => Exist.cplx (Exist.vortFn hm1 (Exist.horizonEvolution hm1 Pn H r a v)))
          (fun r => Exist.stripVel hm1 (Exist.horizonEvolution hm1 Pn H r a v)) := by
    intro a ha v
    have hn : a + 1 ≤ ((⌈a + 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h0 := hS ⌈a + 1⌉₊ a ha hn v
    refine Exist.flowCongrAE ν c m tr a (a + 1) _ _ _ _ _ _ (by linarith) h0
      EventuallyEq.rfl ?_ ?_
    · intro s hs
      refine EventuallyEq.of_eq ?_
      have heq := congrArg (fun L => L v)
        (Exist.horizonEvolution_eq hm1 Exist.horizonLocality Pn H ha hs.1 (hs.2.trans hn))
      rw [heq]
    · intro s hs
      refine EventuallyEq.of_eq ?_
      have heq := congrArg (fun L => L v)
        (Exist.horizonEvolution_eq hm1 Exist.horizonLocality Pn H ha hs.1 (hs.2.trans hn))
      rw [heq]
  refine Exist.flowGlobal ν c m tr τ _ _ _ ?_
  intro N
  induction N with
  | zero =>
    have hj : τ + ((0 + 1 : ℕ) : ℝ) = τ + 1 := by push_cast; ring
    rw [hj]
    exact hUnit τ hτ u₀
  | succ N ih =>
    let a : ℝ := τ + ((N + 1 : ℕ) : ℝ)
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have hta : τ ≤ a := by dsimp [a]; linarith [show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity]
    let v := Exist.horizonEvolution hm1 Pn H a τ u₀
    have hs := hUnit a ha0 v
    have hs' : Exist.IsLinFlowOn ν c m tr a (a + 1)
        (Exist.cplx (Exist.vortFn hm1 v))
        (fun r => Exist.cplx (Exist.vortFn hm1 (Exist.horizonEvolution hm1 Pn H r τ u₀)))
        (fun r => Exist.stripVel hm1 (Exist.horizonEvolution hm1 Pn H r τ u₀)) := by
      refine Exist.flowCongrAE ν c m tr a (a + 1) _ _ _ _ _ _ (by linarith) hs
        EventuallyEq.rfl ?_ ?_
      · intro s hs1
        refine EventuallyEq.of_eq ?_
        rw [show v = Exist.horizonEvolution hm1 Pn H a τ u₀ from rfl,
          Exist.horizonEvolution_comp hm1 Exist.horizonLocality Pn H hτ hta hs1.1 u₀]
      · intro s hs1
        refine EventuallyEq.of_eq ?_
        rw [show v = Exist.horizonEvolution hm1 Pn H a τ u₀ from rfl,
          Exist.horizonEvolution_comp hm1 Exist.horizonLocality Pn H hτ hta hs1.1 u₀]
    have hj : τ + ((N + 1 + 1 : ℕ) : ℝ) = a + 1 := by dsimp [a]; push_cast; ring
    rw [hj]
    exact Exist.flowAppend ν c m tr τ a (a + 1) _ _ _ hta (by linarith) ih hs'

/-- Fubini swap on the compact triangle `{t₀ ≤ τ ≤ r ≤ s}` for a continuous real kernel. -/
private lemma triangle_fubini_real {t₀ s : ℝ} (hts : t₀ ≤ s) (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ s}) :
    IntervalIntegrable (fun r => ∫ τ in t₀..r, f (r, τ)) volume t₀ s ∧
      IntervalIntegrable (fun τ => ∫ r in τ..s, f (r, τ)) volume t₀ s ∧
      (∫ τ in t₀..s, ∫ r in τ..s, f (r, τ)) = ∫ r in t₀..s, ∫ τ in t₀..r, f (r, τ) := by
  let T_set : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ≤ p.1}
  let Q : Set (ℝ × ℝ) := Icc t₀ s ×ˢ Icc t₀ s
  let W_s : Set (ℝ × ℝ) := {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ s}
  have hT_meas : MeasurableSet T_set := (isClosed_le continuous_snd continuous_fst).measurableSet
  have hW_eq : T_set ∩ Q = W_s := by
    ext ⟨r, τ⟩
    simp only [T_set, Q, W_s, mem_inter_iff, mem_ofPred, mem_prod, mem_Icc]
    constructor
    · rintro ⟨h1, ⟨_, h3⟩, ⟨h4, _⟩⟩; exact ⟨h4, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, ⟨h1.trans h2, h3⟩, ⟨h1, h2.trans h3⟩⟩
  have hW_comp : IsCompact W_s := by
    rw [← hW_eq]
    exact (isCompact_Icc.prod isCompact_Icc).inter_left (isClosed_le continuous_snd continuous_fst)
  have hf_W : Integrable f ((volume : Measure (ℝ × ℝ)).restrict W_s) :=
    hf.integrableOn_compact hW_comp
  let μI : Measure ℝ := volume.restrict (Icc t₀ s)
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hμ_prod : μI.prod μI = (volume : Measure (ℝ × ℝ)).restrict Q :=
    Measure.prod_restrict (Icc t₀ s) (Icc t₀ s)
  have hf_ind : Integrable (T_set.indicator f) (μI.prod μI) := by
    rw [hμ_prod, integrable_indicator_iff hT_meas]
    change Integrable f (((volume : Measure (ℝ × ℝ)).restrict Q).restrict T_set)
    rw [Measure.restrict_restrict hT_meas, hW_eq]
    exact hf_W
  have hslice_r : ∀ r ∈ Icc t₀ s,
      ∫ τ, T_set.indicator f (r, τ) ∂μI = ∫ τ in t₀..r, f (r, τ) := by
    intro r hr
    have hind : (fun τ => T_set.indicator f (r, τ)) = (Iic r).indicator (fun τ => f (r, τ)) := by
      funext τ; by_cases h : τ ≤ r <;> simp [T_set, h]
    have hinter : Icc t₀ s ∩ Iic r = Icc t₀ r := by
      ext τ; simp only [mem_inter_iff, mem_Icc, mem_Iic]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2.trans hr.2⟩, h2⟩⟩
    change ∫ τ in Icc t₀ s, T_set.indicator f (r, τ) = _
    rw [hind, setIntegral_indicator measurableSet_Iic, hinter,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.1]
  have hslice_τ : ∀ τ ∈ Icc t₀ s,
      ∫ r, T_set.indicator f (r, τ) ∂μI = ∫ r in τ..s, f (r, τ) := by
    intro τ hτ
    have hind : (fun r => T_set.indicator f (r, τ)) = (Ici τ).indicator (fun r => f (r, τ)) := by
      funext r; by_cases h : τ ≤ r <;> simp [T_set, h]
    have hinter : Icc t₀ s ∩ Ici τ = Icc τ s := by
      ext r; simp only [mem_inter_iff, mem_Icc, mem_Ici]
      exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨h3, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨hτ.1.trans h1, h2⟩, h1⟩⟩
    change ∫ r in Icc t₀ s, T_set.indicator f (r, τ) = _
    rw [hind, setIntegral_indicator measurableSet_Ici, hinter,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.2]
  have hii_r : IntervalIntegrable (fun r => ∫ τ in t₀..r, f (r, τ)) volume t₀ s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hts]
    exact hf_ind.integral_prod_left.congr
      ((ae_restrict_mem measurableSet_Icc).mono fun r hr => hslice_r r hr)
  have hii_τ : IntervalIntegrable (fun τ => ∫ r in τ..s, f (r, τ)) volume t₀ s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hts]
    exact hf_ind.integral_prod_right.congr
      ((ae_restrict_mem measurableSet_Icc).mono fun τ hτ => hslice_τ τ hτ)
  refine ⟨hii_r, hii_τ, ?_⟩
  have h1 : ∫ τ in t₀..s, (∫ r in τ..s, f (r, τ)) = ∫ τ, (∫ r, T_set.indicator f (r, τ) ∂μI) ∂μI := by
    rw [intervalIntegral.integral_of_le hts, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc fun τ hτ => (hslice_τ τ hτ).symm
  have h2 : ∫ r in t₀..s, (∫ τ in t₀..r, f (r, τ)) = ∫ r, (∫ τ, T_set.indicator f (r, τ) ∂μI) ∂μI := by
    rw [intervalIntegral.integral_of_le hts, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => (hslice_r r hr).symm
  rw [h1, h2]
  exact (MeasureTheory.integral_integral_swap
    (f := fun r τ => T_set.indicator f (r, τ)) hf_ind).symm

private lemma setIntegral_sub_sub_sub {s : Set (ℝ × ℝ)} {f₁ f₂ f₃ f₄ : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn f₁ s) (h₂ : IntegrableOn f₂ s)
    (h₃ : IntegrableOn f₃ s) (h₄ : IntegrableOn f₄ s) :
    (∫ x in s, ((f₁ x - f₂ x) - (f₃ x - f₄ x))) =
      ((∫ x in s, f₁ x) - (∫ x in s, f₂ x)) - ((∫ x in s, f₃ x) - (∫ x in s, f₄ x)) := by
  have h12 : IntegrableOn (fun x => f₁ x - f₂ x) s := h₁.sub h₂
  have h34 : IntegrableOn (fun x => f₃ x - f₄ x) s := h₃.sub h₄
  rw [integral_sub h12 h34, integral_sub h₁ h₂, integral_sub h₃ h₄]

private lemma continuousOn_slice_of_joint {X : Type*} [TopologicalSpace X] {t₀ S r : ℝ}
    {G : ℝ × ℝ → X}
    (hG : ContinuousOn G {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S})
    (hr : r ≤ S) :
    ContinuousOn (fun τ => G (r, τ)) (Icc t₀ r) :=
  hG.comp (continuousOn_const.prodMk continuousOn_id) fun _ hτ => ⟨hτ.1, hτ.2, hr⟩

private lemma continuousOn_norm_clm_clock {X Y : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (s : ℝ)
    {t₀ S a b : ℝ} {G : ℝ × ℝ → X} {φ : ℝ → ℝ}
    (hG : ContinuousOn G {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S})
    (hφ : ContinuousOn φ (Icc a b))
    (hm : ∀ u ∈ Icc a b, t₀ ≤ φ u ∧ φ u ≤ s ∧ s ≤ S) :
    ContinuousOn (fun u => ‖L (G (s, φ u))‖) (Icc a b) :=
  (continuous_norm.comp L.continuous).comp_continuousOn
    (hG.comp (continuousOn_const.prodMk hφ) fun u hu => hm u hu)

/-- Joint continuity, uniform state-norm bound, and weak forced identity on `[t₀, S]` for the
Bochner Duhamel integral `Y s = ∫ τ in t₀..s, D.evolution s τ (F τ)` of a continuous real source
`F : ℝ → ActualVorticity hm1`. -/
private lemma inhom_real_volterra_weak {ν c m t₀ S : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (hReg : Exist.Regime ν c m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (N₀ : ℕ) (ht₀ : 0 ≤ t₀) (htS : t₀ ≤ S) (hSN : S ≤ (N₀ : ℝ))
    (Pn : ∀ n : ℕ, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPathOn
      (c := c) (m := m) (ν := ν) hm1 tr (Nat.cast_nonneg n))
    (H : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatStripSupplier
      (c := c) (m := m) hm1)
    (hH : Exist.ScaledHeatWeak hm1 ν H)
    {F : ℝ → UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1}
    (hF : ContinuousOn F (Icc t₀ S))
    {D : UnforcedLeray.Infra.VolterraEvolution.VolterraData ℝ
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1)
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualFlux (c := c) (m := m))}
    (hD : D = Exist.horizonData hm1 (Pn N₀) H)
    {Y : ℝ → UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1}
    (hY : ∀ s, Y s = ∫ τ in t₀..s, D.evolution s τ (F τ)) :
    ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (F p.2))
        {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S} ∧
      (∃ M_Y : ℝ, 0 ≤ M_Y ∧ ∀ s ∈ Icc t₀ S, ‖Y s‖ ≤ M_Y) ∧
      (∀ φ, B0579.IsCylTest c φ → ∀ s ∈ Icc t₀ S,
        IntegrableOn (flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y s)))
          (Exist.stripVel hm1 (Y s)) s φ) (B0579.cell c) ∧
        IntervalIntegrable (fun r => ∫ x in B0579.cell c,
          flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y r)))
            (Exist.stripVel hm1 (Y r)) r φ x) volume t₀ s ∧
        ∫ x in B0579.cell c, Exist.cplx (Exist.vortFn hm1 (Y s)) x * (φ x : ℂ) =
          ∫ r in t₀..s,
            ((∫ x in B0579.cell c, Exist.cplx (Exist.vortFn hm1 (F r)) x * (φ x : ℂ)) +
              ∫ x in B0579.cell c, flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y r)))
                (Exist.stripVel hm1 (Y r)) r φ x)) := by
  have : CompleteSpace (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1) :=
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualVorticityCompleteSpace
      (c := c) (m := m) hm1
  let W : Set (ℝ × ℝ) := {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S}
  have hFE : (UnforcedLeray.Infra.EvolutionContinuity.ForwardEvolution D.evolution) := by
    rw [hD]
    exact UnforcedLeray.Infra.EvolutionContinuity.forwardEvolution_volterra
      (Exist.horizonData_compatible hm1 (Pn N₀) H) H.S₀_zero
  have hJoint : ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (F p.2)) W :=
    hFE.continuousOn_apply (fun _ hp => hp.2.1)
      (hF.comp continuous_snd.continuousOn fun _ hp => ⟨hp.1, hp.2.1.trans hp.2.2⟩)
  have hW_eq : {p : ℝ × ℝ | p.2 ≤ p.1} ∩ (Icc t₀ S ×ˢ Icc t₀ S) = W := by
    ext ⟨r, τ⟩
    simp only [W, mem_inter_iff, mem_ofPred, mem_prod, mem_Icc]
    constructor
    · rintro ⟨h1, ⟨_, h3⟩, ⟨h4, _⟩⟩; exact ⟨h4, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, ⟨h1.trans h2, h3⟩, ⟨h1, h2.trans h3⟩⟩
  have hW_comp : IsCompact W := by
    rw [← hW_eq]
    exact (isCompact_Icc.prod isCompact_Icc).inter_left (isClosed_le continuous_snd continuous_fst)
  obtain ⟨K_E, hKE⟩ := hW_comp.exists_bound_of_continuousOn hJoint
  have hM_bd : ∃ M_Y : ℝ, 0 ≤ M_Y ∧ ∀ s ∈ Icc t₀ S, ‖Y s‖ ≤ M_Y := by
    refine ⟨max K_E 0 * (S - t₀), mul_nonneg (le_max_right _ _) (sub_nonneg.2 htS), fun s hs => ?_⟩
    have hn : ‖Y s‖ ≤ max K_E 0 * |s - t₀| := by
      rw [hY s]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
      rw [Set.uIoc_of_le hs.1] at hτ
      exact (hKE (s, τ) ⟨hτ.1.le, hτ.2, hs.2⟩).trans (le_max_left _ _)
    rw [abs_of_nonneg (sub_nonneg.2 hs.1)] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 t₀) (le_max_right _ _))
  refine ⟨hJoint, hM_bd, fun φ hφ s hs => ?_⟩
  let Lφ : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1 →L[ℝ] ℝ :=
    (Exist.stcPairL φ hφ.continuous hφ.band).comp (Submodule.subtypeL _)
  obtain ⟨hLc, hLb⟩ := Exist.stc_lapP_cyl hφ
  have hpc0 := (hφ.pd 0).continuous
  have hpb0 := (hφ.pd 0).band
  have hpc1 := (hφ.pd 1).continuous
  have hpb1 := (hφ.pd 1).band
  let LΔ : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1 →L[ℝ] ℝ :=
    (Exist.stcPairL (lapP φ) hLc hLb).comp (Submodule.subtypeL _)
  let Lflux : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualFlux (c := c) (m := m) →L[ℝ] ℝ :=
    (Exist.stcPairL (B0579.pd 0 φ) hpc0 hpb0).comp (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)) +
      (Exist.stcPairL (B0579.pd 1 φ) hpc1 hpb1).comp (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2))
  let B_op := fun r =>
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualTrainFluxBOn hm1 (Pn N₀) r
  let ΛCLM : ℝ → UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1 →L[ℝ] ℝ := fun r => ν • LΔ + Lflux.comp (B_op r)
  have hLφ_eq : ∀ u : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1,
      ∫ x in B0579.cell c, Exist.cplx (Exist.vortFn hm1 u) x * (φ x : ℂ) = ((Lφ u : ℝ) : ℂ) := by
    intro u
    have hpt : ∀ x, Exist.cplx (Exist.vortFn hm1 u) x * (φ x : ℂ) =
        ((Exist.vortFn hm1 u x * φ x : ℝ) : ℂ) := fun x => by simp [Exist.cplx]
    simp only [hpt, integral_complex_ofReal]
    congr 1
    exact (Exist.stc_pairL_apply φ hφ.continuous hφ.band u.1).symm
  have hΛ_eq : ∀ r ∈ Icc (0 : ℝ) (N₀ : ℝ),
      ∀ u : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1,
        IntegrableOn (flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 u)) (Exist.stripVel hm1 u) r φ)
          (B0579.cell c) ∧
        ∫ x in B0579.cell c,
            flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 u)) (Exist.stripVel hm1 u) r φ x =
          ((ΛCLM r u : ℝ) : ℂ) := by
    intro r hr0 u
    have hI := (Exist.fluxIdentityOnAll ν c m hm1 tr N₀ (Nat.cast_nonneg N₀) (Pn N₀) hReg) r hr0 u φ hφ
    refine ⟨hI.1, ?_⟩
    have i0 : IntegrableOn (fun x => Exist.fluxFn (B_op r u) 0 x * B0579.pd 0 φ x) (B0579.cell c) := by
      obtain ⟨R0, hR0⟩ := hpb0
      exact Exist.L2Aux.integrableOn_band_mul _ hpc0 hR0
    have i1 : IntegrableOn (fun x => Exist.fluxFn (B_op r u) 1 x * B0579.pd 1 φ x) (B0579.cell c) := by
      obtain ⟨R1, hR1⟩ := hpb1
      exact Exist.L2Aux.integrableOn_band_mul _ hpc1 hR1
    have eL : (∫ x in B0579.cell c, Exist.vortFn hm1 u x * lapP φ x) = LΔ u :=
      (Exist.stc_pairL_apply _ hLc hLb u.1).symm
    have e0 : (∫ x in B0579.cell c, Exist.fluxFn (B_op r u) 0 x * B0579.pd 0 φ x) =
        Exist.stcPairL (B0579.pd 0 φ) hpc0 hpb0 (B_op r u 0) :=
      (Exist.stc_pairL_apply _ hpc0 hpb0 (B_op r u 0)).symm
    have e1 : (∫ x in B0579.cell c, Exist.fluxFn (B_op r u) 1 x * B0579.pd 1 φ x) =
        Exist.stcPairL (B0579.pd 1 φ) hpc1 hpb1 (B_op r u 1) :=
      (Exist.stc_pairL_apply _ hpc1 hpb1 (B_op r u 1)).symm
    rw [hI.2]
    congr 1
    rw [eL, integral_add i0 i1, e0, e1]
    rfl
  have hsN : s ∈ Icc (0 : ℝ) (N₀ : ℝ) := ⟨ht₀.trans hs.1, hs.2.trans hSN⟩
  have hint_s : IntegrableOn (flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y s)))
      (Exist.stripVel hm1 (Y s)) s φ) (B0579.cell c) := (hΛ_eq s hsN (Y s)).1
  let W_s : Set (ℝ × ℝ) := {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ s}
  let g_ker : ℝ × ℝ → ℝ := fun p => ΛCLM p.1 (D.evolution p.1 p.2 (F p.2))
  have hΛ_bd : ∃ C_Λ : ℝ, ∀ r : ℝ, ‖ΛCLM r‖ ≤ C_Λ := by
    let K_B := (Pn N₀).Cv + (Pn N₀).CE * (c / (2 * Real.pi) + 2)
    have hK_B0 : 0 ≤ K_B := by
      have hc0 : 0 ≤ c := hReg.pos_c.le
      have hCv := (Pn N₀).hCv
      have hCE := (Pn N₀).hCE
      dsimp [K_B]; positivity
    refine ⟨|ν| * ‖LΔ‖ + ‖Lflux‖ * K_B, fun r => ?_⟩
    have hbB : ‖B_op r‖ ≤ K_B :=
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_actualTrainFluxBOn_le hm1 (Pn N₀) r
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    change ‖ν * LΔ u + Lflux (B_op r u)‖ ≤ _
    calc ‖ν * LΔ u + Lflux (B_op r u)‖
        ≤ ‖ν * LΔ u‖ + ‖Lflux (B_op r u)‖ := norm_add_le _ _
      _ ≤ |ν| * (‖LΔ‖ * ‖u‖) + ‖Lflux‖ * (K_B * ‖u‖) := by
          rw [norm_mul, Real.norm_eq_abs]
          refine add_le_add (mul_le_mul_of_nonneg_left (LΔ.le_opNorm u) (abs_nonneg ν)) ?_
          exact (Lflux.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left
              (((B_op r).le_opNorm u).trans (mul_le_mul_of_nonneg_right hbB (norm_nonneg u)))
              (norm_nonneg Lflux))
      _ = (|ν| * ‖LΔ‖ + ‖Lflux‖ * K_B) * ‖u‖ := by ring
  obtain ⟨C_Λ, hC_Λ⟩ := hΛ_bd
  have hg_cont : ContinuousOn g_ker W_s := by
    intro p₀ hp₀
    refine UnforcedLeray.Infra.EvolutionContinuity.continuousWithinAt_clm_apply
      (K := fun p : ℝ × ℝ => ΛCLM p.1) ?_ ⟨C_Λ, Eventually.of_forall fun p => hC_Λ p.1⟩ ?_
    · intro e
      have hc : Continuous (fun p : ℝ × ℝ => ΛCLM p.1 e) :=
        continuous_const.add (Lflux.continuous.comp
          ((UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.continuous_actualTrainFluxBOn_apply
            hm1 (Pn N₀) e).comp continuous_fst))
      exact hc.continuousWithinAt
    · exact (hJoint.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hs.2⟩) p₀ hp₀
  obtain ⟨hii_r, hii_τ, hswap⟩ := triangle_fubini_real hs.1 g_ker hg_cont
  have hslice_int : ∀ r ∈ Icc t₀ S,
      IntervalIntegrable (fun τ => D.evolution r τ (F τ)) volume t₀ r := by
    intro r hr
    exact (continuousOn_slice_of_joint hJoint hr.2).intervalIntegrable_of_Icc hr.1
  have hΛ_Y : ∀ r ∈ Icc t₀ s, ΛCLM r (Y r) = ∫ τ in t₀..r, g_ker (r, τ) := by
    intro r hr
    rw [hY r]
    exact ((ΛCLM r).intervalIntegral_comp_comm (hslice_int r ⟨hr.1, hr.2.trans hs.2⟩)).symm
  have hii_fl : IntervalIntegrable (fun r => ∫ x in B0579.cell c,
      flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y r))) (Exist.stripVel hm1 (Y r)) r φ x)
      volume t₀ s := by
    refine (intervalIntegrable_congr fun r hr => ?_).1
      ⟨Complex.ofRealCLM.integrable_comp hii_r.1, Complex.ofRealCLM.integrable_comp hii_r.2⟩
    rw [uIoc_of_le hs.1] at hr
    have hr_s : r ∈ Icc t₀ s := ⟨hr.1.le, hr.2⟩
    have hrN : r ∈ Icc (0 : ℝ) (N₀ : ℝ) := ⟨ht₀.trans hr_s.1, hr_s.2.trans (hs.2.trans hSN)⟩
    change ((∫ τ in t₀..r, g_ker (r, τ) : ℝ) : ℂ) = _
    rw [← hΛ_Y r hr_s, (hΛ_eq r hrN (Y r)).2]
  refine ⟨hint_s, hii_fl, ?_⟩
  have hLφ_Y : Lφ (Y s) = ∫ τ in t₀..s, Lφ (D.evolution s τ (F τ)) := by
    rw [hY s]
    exact (Lφ.intervalIntegral_comp_comm (hslice_int s hs)).symm
  have hweak_τ : ∀ τ ∈ Icc t₀ s,
      Lφ (D.evolution s τ (F τ)) = Lφ (F τ) + ∫ r in τ..s, g_ker (r, τ) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := ht₀.trans hτ.1
    have hfl_τ := horizon_real_flow hm1 hReg tr Pn H hH hτ0 (F τ)
    have hwk := hfl_τ.weak φ hφ s hτ.2
    have hev_s : Exist.horizonEvolution hm1 Pn H s τ (F τ) = D.evolution s τ (F τ) := by
      rw [hD]
      exact congrArg (fun L => L (F τ))
        (Exist.horizonEvolution_eq hm1 Exist.horizonLocality Pn H hτ0 hτ.2 (hs.2.trans hSN))
    rw [hev_s, hLφ_eq, hLφ_eq] at hwk
    have hrhs : (∫ r in τ..s, ∫ x in B0579.cell c,
        flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Exist.horizonEvolution hm1 Pn H r τ (F τ))))
          (Exist.stripVel hm1 (Exist.horizonEvolution hm1 Pn H r τ (F τ))) r φ x) =
        ((∫ r in τ..s, g_ker (r, τ) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hτ.2] at hr
      have hrN : r ∈ Icc (0 : ℝ) (N₀ : ℝ) :=
        ⟨hτ0.trans hr.1, hr.2.trans (hs.2.trans hSN)⟩
      have hev_r : Exist.horizonEvolution hm1 Pn H r τ (F τ) = D.evolution r τ (F τ) := by
        rw [hD]
        exact congrArg (fun L => L (F τ))
          (Exist.horizonEvolution_eq hm1 Exist.horizonLocality Pn H hτ0 hr.1
            (hr.2.trans (hs.2.trans hSN)))
      rw [hev_r, (hΛ_eq r hrN (D.evolution r τ (F τ))).2]
    rw [hrhs, ← Complex.ofReal_add] at hwk
    exact Complex.ofReal_injective hwk
  have hii_LφF : IntervalIntegrable (fun r => Lφ (F r)) volume t₀ s :=
    (Lφ.continuous.comp_continuousOn (hF.mono (Icc_subset_Icc_right hs.2))).intervalIntegrable_of_Icc hs.1
  have hreal_id : Lφ (Y s) = ∫ r in t₀..s, (Lφ (F r) + ΛCLM r (Y r)) := by
    have hc1 : ∫ τ in t₀..s, Lφ (D.evolution s τ (F τ)) =
        ∫ τ in t₀..s, (Lφ (F τ) + ∫ r in τ..s, g_ker (r, τ)) :=
      intervalIntegral.integral_congr fun τ hτ => by
        rw [uIcc_of_le hs.1] at hτ; exact hweak_τ τ hτ
    have hc2 : ∫ r in t₀..s, (∫ τ in t₀..r, g_ker (r, τ)) = ∫ r in t₀..s, ΛCLM r (Y r) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs.1] at hr; exact (hΛ_Y r hr).symm
    have hii_ΛY : IntervalIntegrable (fun r => ΛCLM r (Y r)) volume t₀ s :=
      hii_r.congr fun r hr => by
        rw [uIoc_of_le hs.1] at hr; exact (hΛ_Y r ⟨hr.1.le, hr.2⟩).symm
    rw [hLφ_Y, hc1, intervalIntegral.integral_add hii_LφF hii_τ, hswap, hc2,
      ← intervalIntegral.integral_add hii_LφF hii_ΛY]
  rw [hLφ_eq (Y s), hreal_id, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  have hrN : r ∈ Icc (0 : ℝ) (N₀ : ℝ) := ⟨ht₀.trans hr.1, hr.2.trans (hs.2.trans hSN)⟩
  rw [Complex.ofReal_add, ← hLφ_eq (F r), ← (hΛ_eq r hrN (Y r)).2]

/-- Lift a continuous zero-circulation complex residual path `f_res` on `[t₀, S]` to continuous
real and imaginary paths `F_re, F_im : ℝ → ActualVorticity hm1`. -/
private lemma lift_fres_contOn {c m t₀ S : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    {f_res : ℝ → ℝ × ℝ → ℂ}
    (hf_mem : ∀ s ∈ Icc t₀ S, MemLp (f_res s) 2 (B0579.cellMeasure c m))
    (hf_zc : ∀ s ∈ Icc t₀ S, HasZeroCirculation c (f_res s))
    (hf_cont : ∀ s ∈ Icc t₀ S,
      Tendsto (fun s' => xNorm c m (f_res s' - f_res s)) (𝓝[Icc t₀ S] s) (𝓝 0)) :
    ∃ F_re F_im : ℝ →
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1,
      ContinuousOn F_re (Icc t₀ S) ∧
      ContinuousOn F_im (Icc t₀ S) ∧
      (∀ s ∈ Icc t₀ S,
        f_res s =ᵐ[volume.restrict (B0579.cell c)]
          (fun x => Exist.cplx (Exist.vortFn hm1 (F_re s)) x +
            Complex.I * Exist.cplx (Exist.vortFn hm1 (F_im s)) x) ∧
        Exist.vortFn hm1 (F_re s) =ᵐ[volume.restrict (B0579.cell c)] (fun x => (f_res s x).re) ∧
        Exist.vortFn hm1 (F_im s) =ᵐ[volume.restrict (B0579.cell c)] (fun x => (f_res s x).im)) := by
  classical
  have hrep : ∀ s : ℝ, s ∈ Icc t₀ S →
      ∃ wr wi : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1,
        f_res s =ᵐ[volume.restrict (B0579.cell c)]
          fun x => Exist.cplx (Exist.vortFn hm1 wr) x + Complex.I * Exist.cplx (Exist.vortFn hm1 wi) x :=
    fun s hs => Exist.actualRepresentation c m hm1 (f_res s) ⟨hf_mem s hs, hf_zc s hs⟩
  choose! F_re F_im hF_ae using hrep
  have hparts : ∀ s ∈ Icc t₀ S,
      Exist.vortFn hm1 (F_re s) =ᵐ[volume.restrict (B0579.cell c)] (fun x => (f_res s x).re) ∧
      Exist.vortFn hm1 (F_im s) =ᵐ[volume.restrict (B0579.cell c)] (fun x => (f_res s x).im) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · filter_upwards [hF_ae s hs] with x hx
      have := congrArg Complex.re hx
      simpa [Exist.cplx] using this.symm
    · filter_upwards [hF_ae s hs] with x hx
      have := congrArg Complex.im hx
      simpa [Exist.cplx] using this.symm
  have hre_le : ∀ s ∈ Icc t₀ S, ∀ s' ∈ Icc t₀ S,
      ‖F_re s' - F_re s‖ ≤ (xNorm c m (f_res s' - f_res s)).toReal := by
    intro s hs s' hs'
    have a1 := (B0579.cellMeasure_ac c m).ae_le (hparts s' hs').1
    have a2 := (B0579.cellMeasure_ac c m).ae_le (hparts s hs).1
    have hle_enn : ENNReal.ofReal ‖F_re s' - F_re s‖ ≤ xNorm c m (f_res s' - f_res s) := by
      rw [← Exist.stc_xNorm_cplx_sub hm1 (F_re s') (F_re s)]
      unfold xNorm
      refine eLpNorm_mono_ae ?_
      filter_upwards [a1, a2] with x hx1 hx2
      dsimp only [Pi.sub_apply, Exist.cplx] at hx1 hx2 ⊢
      rw [hx1, hx2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hfin : xNorm c m (f_res s' - f_res s) ≠ ⊤ :=
      ((hf_mem s' hs').sub (hf_mem s hs)).eLpNorm_ne_top
    have htr := ENNReal.toReal_mono hfin hle_enn
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at htr
  have him_le : ∀ s ∈ Icc t₀ S, ∀ s' ∈ Icc t₀ S,
      ‖F_im s' - F_im s‖ ≤ (xNorm c m (f_res s' - f_res s)).toReal := by
    intro s hs s' hs'
    have a1 := (B0579.cellMeasure_ac c m).ae_le (hparts s' hs').2
    have a2 := (B0579.cellMeasure_ac c m).ae_le (hparts s hs).2
    have hle_enn : ENNReal.ofReal ‖F_im s' - F_im s‖ ≤ xNorm c m (f_res s' - f_res s) := by
      rw [← Exist.stc_xNorm_cplx_sub hm1 (F_im s') (F_im s)]
      unfold xNorm
      refine eLpNorm_mono_ae ?_
      filter_upwards [a1, a2] with x hx1 hx2
      dsimp only [Pi.sub_apply, Exist.cplx] at hx1 hx2 ⊢
      rw [hx1, hx2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    have hfin : xNorm c m (f_res s' - f_res s) ≠ ⊤ :=
      ((hf_mem s' hs').sub (hf_mem s hs)).eLpNorm_ne_top
    have htr := ENNReal.toReal_mono hfin hle_enn
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at htr
  have hre_cont : ContinuousOn F_re (Icc t₀ S) := by
    intro s hs
    have hlim0 : Tendsto (fun s' => (xNorm c m (f_res s' - f_res s)).toReal) (𝓝[Icc t₀ S] s) (𝓝 0) := by
      rw [← ENNReal.toReal_zero]
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hf_cont s hs)
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim0
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    exact hre_le s hs s' hs'
  have him_cont : ContinuousOn F_im (Icc t₀ S) := by
    intro s hs
    have hlim0 : Tendsto (fun s' => (xNorm c m (f_res s' - f_res s)).toReal) (𝓝[Icc t₀ S] s) (𝓝 0) := by
      rw [← ENNReal.toReal_zero]
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hf_cont s hs)
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim0
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    exact him_le s hs s' hs'
  exact ⟨F_re, F_im, hre_cont, him_cont, fun s hs => ⟨hF_ae s hs, hparts s hs⟩⟩

/-- **Inhomogeneous Duhamel decomposition on `[t₀, S]`.**
If `(w, u)` is a linearised flow from `0` (with zero-circulation `X_{m,c}` datum `w₀`),
`w_can` satisfies the forced weak linearised equation on `[t₀, S]` with forcing `+f_res` and has
bounded `X_{m,c}` norm and zero circulation on `[t₀, S]`, and `(w_hom, u_hom)` is any homogeneous
`IsLinearisedFlow` from `w t₀ - w_can t₀` at `t₀`, then for every `s ∈ [t₀, S]`,
`w s - w_can s =ᵐ w_hom s - w_inhom s` on `cell c`, where
`w_inhom s = cplx (vortFn hm1 (Y_re s)) + I * cplx (vortFn hm1 (Y_im s))`. -/
private lemma inhom_duhamel_eq_ae {m ν t₀ S M_can : ℝ} (hm : 8 < m) (hm1 : 1 ≤ m)
    [Fact (0 < ν ^ (-2 : ℝ))]
    (hν : ν ∈ Ioc 0 (nuUniq m hm))
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (N₀ : ℕ) (ht₀ : 0 ≤ t₀) (htS : t₀ ≤ S) (hSN : S ≤ (N₀ : ℝ)) (hM_can : 0 ≤ M_can)
    (Pn : ∀ n : ℕ, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPathOn
      (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr (Nat.cast_nonneg n))
    (H : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatStripSupplier
      (c := ν ^ (-2 : ℝ)) (m := m) hm1)
    (hH : Exist.ScaledHeatWeak hm1 ν H)
    {w₀ : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw₀_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) w₀)
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 w₀ w u)
    {w_can : ℝ → ℝ × ℝ → ℂ} {u_can : ℝ → ℝ × ℝ → Fin 2 → ℂ} {f_res : ℝ → ℝ × ℝ → ℂ}
    (hcan_mem : ∀ s ∈ Icc t₀ S, MemLp (w_can s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (w_can s) ∧
      (xNorm (ν ^ (-2 : ℝ)) m (w_can s)).toReal ≤ M_can)
    (hcan_bs : ∀ s ∈ Icc t₀ S, IsBiotSavart (ν ^ (-2 : ℝ)) (w_can s) (u_can s))
    (hcan_wk : ∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc t₀ S,
      IntegrableOn (flowIntegrand tr (w_can s) (u_can s) s φ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntervalIntegrable (fun τ =>
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume t₀ s ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can s x * (φ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can t₀ x * (φ x : ℂ)) +
        ∫ τ in t₀..s,
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
            (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))))
    {F_re F_im : ℝ → UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := ν ^ (-2 : ℝ)) (m := m) hm1}
    (hFre_cont : ContinuousOn F_re (Icc t₀ S))
    (hFim_cont : ContinuousOn F_im (Icc t₀ S))
    (hF_ae : ∀ s ∈ Icc t₀ S,
      f_res s =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
        fun x => Exist.cplx (Exist.vortFn hm1 (F_re s)) x +
          Complex.I * Exist.cplx (Exist.vortFn hm1 (F_im s)) x)
    {w_hom : ℝ → ℝ × ℝ → ℂ} {u_hom : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw_hom : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₀ (fun x => w t₀ x - w_can t₀ x) w_hom u_hom)
    {D : UnforcedLeray.Infra.VolterraEvolution.VolterraData ℝ
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1)
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualFlux (c := ν ^ (-2 : ℝ)) (m := m))}
    (hD : D = Exist.horizonData hm1 (Pn N₀) H)
    {Y_re Y_im : ℝ → UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := ν ^ (-2 : ℝ)) (m := m) hm1}
    (hYre : ∀ s, Y_re s = ∫ τ in t₀..s, D.evolution s τ (F_re τ))
    (hYim : ∀ s, Y_im s = ∫ τ in t₀..s, D.evolution s τ (F_im τ)) :
    ∀ s ∈ Icc t₀ S,
      (fun x => w s x - w_can s x) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
        fun x => w_hom s x - (Exist.cplx (Exist.vortFn hm1 (Y_re s)) x +
          Complex.I * Exist.cplx (Exist.vortFn hm1 (Y_im s)) x) := by
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (nuUniq_le_one m hm)
  have hc1 : 1 ≤ ν ^ (-2 : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
  have hReg : Exist.Regime ν (ν ^ (-2 : ℝ)) m := ⟨hν0, hν1, rfl, hm⟩
  obtain ⟨_, ⟨M_re, hM_re0, hM_re⟩, hwk_re⟩ :=
    inhom_real_volterra_weak hm1 hReg tr N₀ ht₀ htS hSN Pn H hH hFre_cont hD hYre
  obtain ⟨_, ⟨M_im, hM_im0, hM_im⟩, hwk_im⟩ :=
    inhom_real_volterra_weak hm1 hReg tr N₀ ht₀ htS hSN Pn H hH hFim_cont hD hYim
  let w_inh : ℝ → ℝ × ℝ → ℂ := fun s x =>
    Exist.cplx (Exist.vortFn hm1 (Y_re s)) x +
      Complex.I * Exist.cplx (Exist.vortFn hm1 (Y_im s)) x
  let u_inh : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun s x j =>
    Exist.stripVel hm1 (Y_re s) x j + Complex.I * Exist.stripVel hm1 (Y_im s) x j
  have hc_w : ContinuousOn (fun s => (xNorm (ν ^ (-2 : ℝ)) m (w s)).toReal) (Icc t₀ S) :=
    (RateBoundAux.contOn_norm w (fun s hs => hw.memX s hs)
      (fun s hs => hw.strongCont s hs)).mono fun s hs => ht₀.trans hs.1
  obtain ⟨M_w, hM_w0, hM_w⟩ := RateBoundAux.bdd_of_cont hc_w
  have hc_hom : ContinuousOn (fun s => (xNorm (ν ^ (-2 : ℝ)) m (w_hom s)).toReal) (Icc t₀ S) :=
    (RateBoundAux.contOn_norm w_hom (fun s hs => hw_hom.memX s hs)
      (fun s hs => hw_hom.strongCont s hs)).mono Icc_subset_Ici_self
  obtain ⟨M_hom, hM_hom0, hM_hom⟩ := RateBoundAux.bdd_of_cont hc_hom
  let om : ℝ → ℝ × ℝ → ℂ := fun s x => (w s x - w_can s x) - (w_hom s x - w_inh s x)
  let u_om : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun s x j =>
    (u s x j - u_can s x j) - (u_hom s x j - u_inh s x j)
  have hom0 : om t₀ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] 0 := by
    have hYre0 : Y_re t₀ = 0 := by rw [hYre t₀, intervalIntegral.integral_same]
    have hYim0 : Y_im t₀ = 0 := by rw [hYim t₀, intervalIntegral.integral_same]
    have hinh0 : w_inh t₀ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] 0 := by
      dsimp only [w_inh]
      rw [hYre0, hYim0]
      filter_upwards [vortFn_zero_ae (c := ν ^ (-2 : ℝ)) (m := m) hm1] with x hx
      simp [Exist.cplx, hx]
    filter_upwards [hw_hom.initial, hinh0] with x h1 h2
    dsimp only [om, Pi.zero_apply] at h1 h2 ⊢
    rw [h1, h2]
    ring
  have hzc_init_hom : HasZeroCirculation (ν ^ (-2 : ℝ)) (fun x => w t₀ x - w_can t₀ x) := by
    have zw := ladFlowZeroCirc m (by linarith) ν (ν ^ (-2 : ℝ)) tr 0 w₀ w u hc1 hw₀_zc hw t₀ ht₀
    have zc := (hcan_mem t₀ ⟨le_rfl, htS⟩).2.1
    exact ⟨zw.1.sub zc.1, by rw [integral_sub zw.1 zc.1, zw.2, zc.2, sub_self]⟩
  let M_tot : ℝ := M_w + M_can + M_hom + (M_re + M_im)
  have hM_tot0 : 0 ≤ M_tot := by dsimp [M_tot]; positivity
  have hom_props : ∀ s ∈ Icc t₀ S,
      MemLp (om s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (om s) ∧
      (xNorm (ν ^ (-2 : ℝ)) m (om s)).toReal ≤ M_tot := by
    intro s hs
    have hs0 : 0 ≤ s := ht₀.trans hs.1
    have mw := hw.memX s hs0
    have mcan := (hcan_mem s hs).1
    have mhom := hw_hom.memX s hs.1
    have ginh : Exist.GoodC (ν ^ (-2 : ℝ)) m (w_inh s) :=
      Exist.goodCStable.2 (ν ^ (-2 : ℝ)) m _ _
        (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_re s))
        (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_im s))
    have minh := ginh.1
    have mom : MemLp (om s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
      (mw.sub mcan).sub (mhom.sub minh)
    have zw := ladFlowZeroCirc m (by linarith) ν (ν ^ (-2 : ℝ)) tr 0 w₀ w u hc1 hw₀_zc hw s hs0
    have zcan := (hcan_mem s hs).2.1
    have zhom := ladFlowZeroCirc m (by linarith) ν (ν ^ (-2 : ℝ)) tr t₀ _ w_hom u_hom hc1
      hzc_init_hom hw_hom s hs.1
    have zinh := ginh.2
    have zom : HasZeroCirculation (ν ^ (-2 : ℝ)) (om s) := by
      refine ⟨(zw.1.sub zcan.1).sub (zhom.1.sub zinh.1), ?_⟩
      change ∫ x in B0579.cell (ν ^ (-2 : ℝ)), ((w s x - w_can s x) - (w_hom s x - w_inh s x)) = 0
      rw [setIntegral_sub_sub_sub zw.1 zcan.1 zhom.1 zinh.1, zw.2, zcan.2, zhom.2, zinh.2]
      ring
    have hx_inh : xNorm (ν ^ (-2 : ℝ)) m (w_inh s) ≤ ENNReal.ofReal (M_re + M_im) := by
      have mr := (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_re s)).1
      have mi := ((Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_im s)).1).const_mul Complex.I
      have htri : xNorm (ν ^ (-2 : ℝ)) m (w_inh s) ≤
          xNorm (ν ^ (-2 : ℝ)) m (Exist.cplx (Exist.vortFn hm1 (Y_re s))) +
            xNorm (ν ^ (-2 : ℝ)) m (fun x => Complex.I * Exist.cplx (Exist.vortFn hm1 (Y_im s)) x) :=
        eLpNorm_add_le mr.1 mi.1 one_le_two
      have him_nrm : xNorm (ν ^ (-2 : ℝ)) m
            (fun x => Complex.I * Exist.cplx (Exist.vortFn hm1 (Y_im s)) x) =
          xNorm (ν ^ (-2 : ℝ)) m (Exist.cplx (Exist.vortFn hm1 (Y_im s))) := by
        unfold xNorm
        refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
        simp
      rw [him_nrm, xNorm_cplx_vortFn hm1, xNorm_cplx_vortFn hm1,
        ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] at htri
      exact htri.trans (ENNReal.ofReal_le_ofReal (add_le_add (hM_re s hs) (hM_im s hs)))
    have htri1 : xNorm (ν ^ (-2 : ℝ)) m (om s) ≤
        xNorm (ν ^ (-2 : ℝ)) m (w s - w_can s) + xNorm (ν ^ (-2 : ℝ)) m (w_hom s - w_inh s) :=
      eLpNorm_sub_le (mw.sub mcan).1 (mhom.sub minh).1 one_le_two
    have htri2 : xNorm (ν ^ (-2 : ℝ)) m (w s - w_can s) ≤
        xNorm (ν ^ (-2 : ℝ)) m (w s) + xNorm (ν ^ (-2 : ℝ)) m (w_can s) :=
      eLpNorm_sub_le mw.1 mcan.1 one_le_two
    have htri3 : xNorm (ν ^ (-2 : ℝ)) m (w_hom s - w_inh s) ≤
        xNorm (ν ^ (-2 : ℝ)) m (w_hom s) + xNorm (ν ^ (-2 : ℝ)) m (w_inh s) :=
      eLpNorm_sub_le mhom.1 minh.1 one_le_two
    have hall : xNorm (ν ^ (-2 : ℝ)) m (om s) ≤
        (xNorm (ν ^ (-2 : ℝ)) m (w s) + xNorm (ν ^ (-2 : ℝ)) m (w_can s)) +
          (xNorm (ν ^ (-2 : ℝ)) m (w_hom s) + ENNReal.ofReal (M_re + M_im)) :=
      htri1.trans (add_le_add htri2 (htri3.trans (add_le_add le_rfl hx_inh)))
    have nw : xNorm (ν ^ (-2 : ℝ)) m (w s) ≠ ⊤ := mw.eLpNorm_ne_top
    have ncan : xNorm (ν ^ (-2 : ℝ)) m (w_can s) ≠ ⊤ := mcan.eLpNorm_ne_top
    have nhom : xNorm (ν ^ (-2 : ℝ)) m (w_hom s) ≠ ⊤ := mhom.eLpNorm_ne_top
    have hf_sum : (xNorm (ν ^ (-2 : ℝ)) m (w s) + xNorm (ν ^ (-2 : ℝ)) m (w_can s)) +
        (xNorm (ν ^ (-2 : ℝ)) m (w_hom s) + ENNReal.ofReal (M_re + M_im)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨nw, ncan⟩,
        ENNReal.add_ne_top.2 ⟨nhom, ENNReal.ofReal_ne_top⟩⟩
    have htr := ENNReal.toReal_mono hf_sum hall
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨nw, ncan⟩)
        (ENNReal.add_ne_top.2 ⟨nhom, ENNReal.ofReal_ne_top⟩),
      ENNReal.toReal_add nw ncan,
      ENNReal.toReal_add nhom ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (add_nonneg hM_re0 hM_im0)] at htr
    refine ⟨mom, zom, htr.trans ?_⟩
    have b1 := hM_w s hs
    have b2 := (hcan_mem s hs).2.2
    have b3 := hM_hom s hs
    dsimp [M_tot]
    linarith
  have hu_bs : ∀ s ∈ Icc t₀ S, IsBiotSavart (ν ^ (-2 : ℝ)) (om s) (u_om s) := by
    intro s hs
    have hm_gt1 : 1 < m := by linarith
    have hs0 : 0 ≤ s := ht₀.trans hs.1
    have mw := hw.memX s hs0
    have mcan := ((hcan_mem s hs).1).const_mul (-1 : ℂ)
    have mhom := hw_hom.memX s hs.1
    have mre := (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_re s)).1
    have mim := ((Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_im s)).1).const_mul Complex.I
    have minh : MemLp (w_inh s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := mre.add mim
    have b_w := hw.biotSavart s hs0
    have b_can := isBiotSavart_smul (-1 : ℂ) (hcan_bs s hs)
    have b_hom := hw_hom.biotSavart s hs.1
    have b_inh : IsBiotSavart (ν ^ (-2 : ℝ)) (w_inh s) (u_inh s) :=
      isBiotSavart_add hm_gt1 mre mim (Exist.biotSavartFieldAll (ν ^ (-2 : ℝ)) m hm1 (Y_re s))
        (isBiotSavart_smul Complex.I (Exist.biotSavartFieldAll (ν ^ (-2 : ℝ)) m hm1 (Y_im s)))
    have b1 := isBiotSavart_add hm_gt1 mw mcan b_w b_can
    have b2 := isBiotSavart_smul (-1 : ℂ)
      (isBiotSavart_add hm_gt1 mhom (minh.const_mul (-1 : ℂ)) b_hom
        (isBiotSavart_smul (-1 : ℂ) b_inh))
    refine isBiotSavart_congr_ae (isBiotSavart_add hm_gt1 (mw.add mcan)
      ((mhom.add (minh.const_mul (-1 : ℂ))).const_mul (-1 : ℂ)) b1 b2) ?_ ?_
    · refine Eventually.of_forall fun x => ?_
      dsimp only [Pi.add_apply, om, w_inh]
      ring
    · refine Eventually.of_forall fun x => ?_
      funext j
      dsimp only [Pi.add_apply, u_om, u_inh]
      ring
  have hwk_om : ∀ ψ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ → ∀ s ∈ Icc t₀ S,
      IntegrableOn (flowIntegrand tr (om s) (u_om s) s ψ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntervalIntegrable (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
        flowIntegrand tr (om r) (u_om r) r ψ x) volume t₀ s ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), om s x * (ψ x : ℂ) =
        ∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (om r) (u_om r) r ψ x := by
    intro ψ hψ s hs
    have hfl_eq : ∀ r, flowIntegrand tr (om r) (u_om r) r ψ = fun x =>
        (flowIntegrand tr (w r) (u r) r ψ x - flowIntegrand tr (w_can r) (u_can r) r ψ x) -
          (flowIntegrand tr (w_hom r) (u_hom r) r ψ x -
            (flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y_re r)))
                (Exist.stripVel hm1 (Y_re r)) r ψ x +
              Complex.I * flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y_im r)))
                (Exist.stripVel hm1 (Y_im r)) r ψ x)) := by
      intro r; funext x; unfold flowIntegrand; dsimp only [om, u_om, w_inh, u_inh]; ring
    have hint_s : IntegrableOn (flowIntegrand tr (om s) (u_om s) s ψ)
        (B0579.cell (ν ^ (-2 : ℝ))) := by
      rw [hfl_eq s]
      exact ((hw.integrable ψ hψ s (ht₀.trans hs.1)).sub (hcan_wk ψ hψ s hs).1).sub
        ((hw_hom.integrable ψ hψ s hs.1).sub
          ((hwk_re ψ hψ s hs).1.add ((hwk_im ψ hψ s hs).1.const_mul Complex.I)))
    let Lψ : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1 →L[ℝ] ℝ :=
      (Exist.stcPairL ψ hψ.continuous hψ.band).comp (Submodule.subtypeL _)
    have hF_pair : ∀ r ∈ Icc t₀ S,
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res r x * (ψ x : ℂ) =
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), Exist.cplx (Exist.vortFn hm1 (F_re r)) x * (ψ x : ℂ)) +
            Complex.I * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
              Exist.cplx (Exist.vortFn hm1 (F_im r)) x * (ψ x : ℂ) := by
      intro r hr
      have ire := Exist.lfc_integrableOn_cplx_test
        (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (F_re r)).1 hψ
      have iim := Exist.lfc_integrableOn_cplx_test
        (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (F_im r)).1 hψ
      have hae : (fun x => f_res r x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
          fun x => Exist.cplx (Exist.vortFn hm1 (F_re r)) x * (ψ x : ℂ) +
            Complex.I * (Exist.cplx (Exist.vortFn hm1 (F_im r)) x * (ψ x : ℂ)) := by
        filter_upwards [hF_ae r hr] with x hx
        rw [hx]
        ring
      rw [integral_congr_ae hae, integral_add ire (iim.const_mul Complex.I), integral_const_mul]
    have hLψ_eq : ∀ v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1,
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), Exist.cplx (Exist.vortFn hm1 v) x * (ψ x : ℂ) =
          ((Lψ v : ℝ) : ℂ) := by
      intro v
      have hpt : ∀ x, Exist.cplx (Exist.vortFn hm1 v) x * (ψ x : ℂ) =
          ((Exist.vortFn hm1 v x * ψ x : ℝ) : ℂ) := fun x => by simp [Exist.cplx]
      simp only [hpt, integral_complex_ofReal]
      congr 1
      exact (Exist.stc_pairL_apply ψ hψ.continuous hψ.band v.1).symm
    have hii_Fre : IntervalIntegrable
        (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          Exist.cplx (Exist.vortFn hm1 (F_re r)) x * (ψ x : ℂ)) volume t₀ s := by
      have hc : ContinuousOn (fun r => ((Lψ (F_re r) : ℝ) : ℂ)) (Icc t₀ s) :=
        Complex.continuous_ofReal.comp_continuousOn
          (Lψ.continuous.comp_continuousOn (hFre_cont.mono (Icc_subset_Icc_right hs.2)))
      exact (hc.intervalIntegrable_of_Icc hs.1).congr fun r _ => (hLψ_eq (F_re r)).symm
    have hii_Fim : IntervalIntegrable
        (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          Exist.cplx (Exist.vortFn hm1 (F_im r)) x * (ψ x : ℂ)) volume t₀ s := by
      have hc : ContinuousOn (fun r => ((Lψ (F_im r) : ℝ) : ℂ)) (Icc t₀ s) :=
        Complex.continuous_ofReal.comp_continuousOn
          (Lψ.continuous.comp_continuousOn (hFim_cont.mono (Icc_subset_Icc_right hs.2)))
      exact (hc.intervalIntegrable_of_Icc hs.1).congr fun r _ => (hLψ_eq (F_im r)).symm
    have hii_fres : IntervalIntegrable
        (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res r x * (ψ x : ℂ)) volume t₀ s := by
      refine (hii_Fre.add (hii_Fim.const_mul Complex.I)).congr fun r hr => ?_
      rw [uIoc_of_le hs.1] at hr
      exact (hF_pair r ⟨hr.1.le, hr.2.trans hs.2⟩).symm
    have hii_can_sum := (hcan_wk ψ hψ s hs).2.1
    have hii_can : IntervalIntegrable
        (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_can r) (u_can r) r ψ x)
        volume t₀ s :=
      (hii_can_sum.sub hii_fres).congr fun _ _ => add_sub_cancel_right _ _
    have hii_w : IntervalIntegrable
        (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w r) (u r) r ψ x)
        volume t₀ s :=
      (hw.timeIntegrable ψ hψ s (ht₀.trans hs.1)).mono_set
        (by rw [uIcc_of_le hs.1, uIcc_of_le (ht₀.trans hs.1)]; exact Icc_subset_Icc_left ht₀)
    have hii_hom := hw_hom.timeIntegrable ψ hψ s hs.1
    have hii_re := (hwk_re ψ hψ s hs).2.1
    have hii_im := (hwk_im ψ hψ s hs).2.1
    have hcell_om : ∀ r ∈ Icc t₀ S,
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (om r) (u_om r) r ψ x =
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w r) (u r) r ψ x) -
            (∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_can r) (u_can r) r ψ x)) -
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_hom r) (u_hom r) r ψ x) -
            ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y_re r)))
                (Exist.stripVel hm1 (Y_re r)) r ψ x) +
              Complex.I * ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
                (Exist.cplx (Exist.vortFn hm1 (Y_im r))) (Exist.stripVel hm1 (Y_im r)) r ψ x)) := by
      intro r hr
      have iw := hw.integrable ψ hψ r (ht₀.trans hr.1)
      have ic := (hcan_wk ψ hψ r hr).1
      have ih := hw_hom.integrable ψ hψ r hr.1
      have ir := (hwk_re ψ hψ r hr).1
      have ii := (hwk_im ψ hψ r hr).1
      have iri : IntegrableOn (fun x =>
          flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y_re r))) (Exist.stripVel hm1 (Y_re r)) r ψ x +
            Complex.I * flowIntegrand tr (Exist.cplx (Exist.vortFn hm1 (Y_im r)))
              (Exist.stripVel hm1 (Y_im r)) r ψ x) (B0579.cell (ν ^ (-2 : ℝ))) :=
        ir.add (ii.const_mul Complex.I)
      rw [hfl_eq r, setIntegral_sub_sub_sub iw ic ih iri,
        integral_add ir (ii.const_mul Complex.I), integral_const_mul]
    have hii_om : IntervalIntegrable
        (fun r => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (om r) (u_om r) r ψ x)
        volume t₀ s := by
      refine ((hii_w.sub hii_can).sub (hii_hom.sub (hii_re.add (hii_im.const_mul Complex.I)))).congr
        fun r hr => ?_
      rw [uIoc_of_le hs.1] at hr
      exact (hcell_om r ⟨hr.1.le, hr.2.trans hs.2⟩).symm
    refine ⟨hint_s, hii_om, ?_⟩
    have hw_s := hw.weak ψ hψ s (ht₀.trans hs.1)
    have hw_t₀ := hw.weak ψ hψ t₀ ht₀
    have hadj_w := intervalIntegral.integral_add_adjacent_intervals
      (hw.timeIntegrable ψ hψ t₀ ht₀) hii_w
    have hw_diff : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * (ψ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t₀ x * (ψ x : ℂ)) +
          ∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w r) (u r) r ψ x := by
      rw [hw_s, hw_t₀, ← hadj_w]
      ring
    have hcan_diff : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can s x * (ψ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can t₀ x * (ψ x : ℂ)) +
          (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (w_can r) (u_can r) r ψ x) +
          (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res r x * (ψ x : ℂ)) := by
      rw [(hcan_wk ψ hψ s hs).2.2, intervalIntegral.integral_add hii_can hii_fres]
      ring
    have i_wt₀ := Exist.lfc_integrableOn_cplx_test (hw.memX t₀ ht₀) hψ
    have i_ct₀ := Exist.lfc_integrableOn_cplx_test (hcan_mem t₀ ⟨le_rfl, htS⟩).1 hψ
    have hhom_diff : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_hom s x * (ψ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t₀ x * (ψ x : ℂ)) -
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can t₀ x * (ψ x : ℂ)) +
          ∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (w_hom r) (u_hom r) r ψ x := by
      have hinit_sub : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w t₀ x - w_can t₀ x) * (ψ x : ℂ) =
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w t₀ x * (ψ x : ℂ)) -
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can t₀ x * (ψ x : ℂ) := by
        have heq : (fun x => (w t₀ x - w_can t₀ x) * (ψ x : ℂ)) =
            fun x => w t₀ x * (ψ x : ℂ) - w_can t₀ x * (ψ x : ℂ) := by
          funext x; ring
        rw [heq, integral_sub i_wt₀ i_ct₀]
      rw [hw_hom.weak ψ hψ s hs.1, hinit_sub]
    have i_yre := Exist.lfc_integrableOn_cplx_test
      (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_re s)).1 hψ
    have i_yim := Exist.lfc_integrableOn_cplx_test
      (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_im s)).1 hψ
    have hinh_diff : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_inh s x * (ψ x : ℂ) =
        (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res r x * (ψ x : ℂ)) +
          ((∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
              (Exist.cplx (Exist.vortFn hm1 (Y_re r))) (Exist.stripVel hm1 (Y_re r)) r ψ x) +
            Complex.I * ∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
              (Exist.cplx (Exist.vortFn hm1 (Y_im r))) (Exist.stripVel hm1 (Y_im r)) r ψ x) := by
      have hl : (fun x => w_inh s x * (ψ x : ℂ)) =
          fun x => Exist.cplx (Exist.vortFn hm1 (Y_re s)) x * (ψ x : ℂ) +
            Complex.I * (Exist.cplx (Exist.vortFn hm1 (Y_im s)) x * (ψ x : ℂ)) := by
        funext x; dsimp [w_inh]; ring
      have hf_split : (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res r x * (ψ x : ℂ)) =
          (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            Exist.cplx (Exist.vortFn hm1 (F_re r)) x * (ψ x : ℂ)) +
            Complex.I * ∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
              Exist.cplx (Exist.vortFn hm1 (F_im r)) x * (ψ x : ℂ) := by
        have hcgr : (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res r x * (ψ x : ℂ)) =
            ∫ r in t₀..s, ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                Exist.cplx (Exist.vortFn hm1 (F_re r)) x * (ψ x : ℂ)) +
              Complex.I * ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                Exist.cplx (Exist.vortFn hm1 (F_im r)) x * (ψ x : ℂ)) :=
          intervalIntegral.integral_congr fun r hr => by
            rw [uIcc_of_le hs.1] at hr; exact hF_pair r ⟨hr.1, hr.2.trans hs.2⟩
        rw [hcgr, intervalIntegral.integral_add hii_Fre (hii_Fim.const_mul Complex.I),
          intervalIntegral.integral_const_mul]
      rw [hl, integral_add i_yre (i_yim.const_mul Complex.I), integral_const_mul,
        (hwk_re ψ hψ s hs).2.2, (hwk_im ψ hψ s hs).2.2,
        intervalIntegral.integral_add hii_Fre hii_re,
        intervalIntegral.integral_add hii_Fim hii_im, hf_split]
      ring
    have i_ws := Exist.lfc_integrableOn_cplx_test (hw.memX s (ht₀.trans hs.1)) hψ
    have i_cs := Exist.lfc_integrableOn_cplx_test (hcan_mem s hs).1 hψ
    have i_hs := Exist.lfc_integrableOn_cplx_test (hw_hom.memX s hs.1) hψ
    have i_is : IntegrableOn (fun x => w_inh s x * (ψ x : ℂ)) (B0579.cell (ν ^ (-2 : ℝ))) :=
      Exist.lfc_integrableOn_cplx_test
        (Exist.goodCStable.2 (ν ^ (-2 : ℝ)) m _ _
          (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_re s))
          (Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (Y_im s))).1 hψ
    have hl_om : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), om s x * (ψ x : ℂ) =
        ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), w s x * (ψ x : ℂ)) -
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can s x * (ψ x : ℂ))) -
        ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_hom s x * (ψ x : ℂ)) -
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_inh s x * (ψ x : ℂ))) := by
      have heq : (fun x => om s x * (ψ x : ℂ)) =
          fun x => (w s x * (ψ x : ℂ) - w_can s x * (ψ x : ℂ)) -
            (w_hom s x * (ψ x : ℂ) - w_inh s x * (ψ x : ℂ)) := by
        funext x; dsimp [om]; ring
      rw [heq, setIntegral_sub_sub_sub i_ws i_cs i_hs i_is]
    have hr_om : (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          flowIntegrand tr (om r) (u_om r) r ψ x) =
        ((∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w r) (u r) r ψ x) -
          (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (w_can r) (u_can r) r ψ x)) -
        ((∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (w_hom r) (u_hom r) r ψ x) -
          ((∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
              (Exist.cplx (Exist.vortFn hm1 (Y_re r))) (Exist.stripVel hm1 (Y_re r)) r ψ x) +
            Complex.I * ∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
              (Exist.cplx (Exist.vortFn hm1 (Y_im r))) (Exist.stripVel hm1 (Y_im r)) r ψ x)) := by
      have hcgr : (∫ r in t₀..s, ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (om r) (u_om r) r ψ x) =
          ∫ r in t₀..s,
            (((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w r) (u r) r ψ x) -
              (∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_can r) (u_can r) r ψ x)) -
            ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr (w_hom r) (u_hom r) r ψ x) -
              ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
                  (Exist.cplx (Exist.vortFn hm1 (Y_re r))) (Exist.stripVel hm1 (Y_re r)) r ψ x) +
                Complex.I * ∫ x in B0579.cell (ν ^ (-2 : ℝ)), flowIntegrand tr
                  (Exist.cplx (Exist.vortFn hm1 (Y_im r))) (Exist.stripVel hm1 (Y_im r)) r ψ x))) :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hs.1] at hr; exact hcell_om r ⟨hr.1, hr.2.trans hs.2⟩
      rw [hcgr, intervalIntegral.integral_sub (hii_w.sub hii_can)
          (hii_hom.sub (hii_re.add (hii_im.const_mul Complex.I))),
        intervalIntegral.integral_sub hii_w hii_can,
        intervalIntegral.integral_sub hii_hom (hii_re.add (hii_im.const_mul Complex.I)),
        intervalIntegral.integral_add hii_re (hii_im.const_mul Complex.I),
        intervalIntegral.integral_const_mul]
    rw [hl_om, hr_om, hw_diff, hcan_diff, hhom_diff, hinh_diff]
    ring
  intro s hs
  have hzero := weak_flow_unique_zero hm hν tr hbuc ht₀ hM_tot0 hom0 hom_props hu_bs hwk_om s hs
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.1 hx

/-! ## 4. Inhomogeneous Duhamel transfer (`CTDuhamelTransfer`) -/

/-! ### 4.1 Clock change of variables and residual integral bounds -/

private lemma clockAge_eq_sub_inv {ν u : ℝ} (hν : 0 < ν) (hu : 0 < u) :
    clockAge ν u = (ν ^ 2)⁻¹ * u⁻¹ - ν⁻¹ := by
  unfold clockAge
  have hν_ne : ν ≠ 0 := hν.ne'
  have hu_ne : u ≠ 0 := hu.ne'
  field_simp

private lemma clockAge_anti {ν θ₁ θ₂ : ℝ} (hν : 0 < ν) (hθ₁ : 0 < θ₁) (h12 : θ₁ ≤ θ₂) :
    clockAge ν θ₂ ≤ clockAge ν θ₁ := by
  have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ h12
  rw [clockAge_eq_sub_inv hν hθ₂, clockAge_eq_sub_inv hν hθ₁]
  refine sub_le_sub_right ?_ _
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hθ₁ h12) (by positivity)

private lemma hasDerivAt_clockAge {ν u : ℝ} (hν : 0 < ν) (hu : 0 < u) :
    HasDerivAt (clockAge ν) (-(clockA ν (clockAge ν u)) ^ 2) u := by
  have hd : HasDerivAt (fun x : ℝ => (ν ^ 2)⁻¹ * x⁻¹ - ν⁻¹)
      ((ν ^ 2)⁻¹ * (-(u ^ 2)⁻¹) - 0) u :=
    ((hasDerivAt_inv hu.ne').const_mul (ν ^ 2)⁻¹).sub (hasDerivAt_const u ν⁻¹)
  have hval : (ν ^ 2)⁻¹ * (-(u ^ 2)⁻¹) - 0 = -(clockA ν (clockAge ν u)) ^ 2 := by
    rw [clockA_clockAge hν hu]
    have hν_ne : ν ≠ 0 := hν.ne'
    have hu_ne : u ≠ 0 := hu.ne'
    field_simp
    ring
  rw [hval] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
  exact clockAge_eq_sub_inv hν hx

private lemma one_le_clockA {ν s : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) : 1 ≤ clockA ν s := by
  unfold clockA
  exact le_add_of_nonneg_right (mul_nonneg hν hs)

private lemma continuousOn_clockAge {ν θ₁ θ₂ : ℝ} (hν : 0 < ν) (hθ₁ : 0 < θ₁) :
    ContinuousOn (clockAge ν) (Icc θ₁ θ₂) :=
  fun _ hu => (hasDerivAt_clockAge hν (lt_of_lt_of_le hθ₁ hu.1)).continuousAt.continuousWithinAt

private lemma integral_clockAge_cov {ν θ₁ θ₂ : ℝ} (hν : 0 < ν) (hθ₁ : 0 < θ₁) (h12 : θ₁ ≤ θ₂)
    (g : ℝ → ℝ) :
    ∫ τ in clockAge ν θ₂..clockAge ν θ₁, g τ =
      ∫ u in θ₁..θ₂, g (clockAge ν u) * (clockA ν (clockAge ν u)) ^ 2 := by
  have hc : ContinuousOn (clockAge ν) (uIcc θ₁ θ₂) := by
    rw [uIcc_of_le h12]
    exact continuousOn_clockAge hν hθ₁
  have hd : ∀ u ∈ Ioo (min θ₁ θ₂) (max θ₁ θ₂),
      HasDerivAt (clockAge ν) (-(clockA ν (clockAge ν u)) ^ 2) u := by
    rw [min_eq_left h12, max_eq_right h12]
    exact fun u hu => hasDerivAt_clockAge hν (hθ₁.trans hu.1)
  have hnp : ∀ u ∈ Ioo (min θ₁ θ₂) (max θ₁ θ₂), -(clockA ν (clockAge ν u)) ^ 2 ≤ 0 :=
    fun u _ => neg_nonpos.2 (sq_nonneg _)
  have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos hc hd hnp (g := g)
  have hneg : (∫ u in θ₁..θ₂, (g ∘ clockAge ν) u * -(clockA ν (clockAge ν u)) ^ 2) =
      -(∫ u in θ₁..θ₂, g (clockAge ν u) * (clockA ν (clockAge ν u)) ^ 2) := by
    have heq : (fun u => (g ∘ clockAge ν) u * -(clockA ν (clockAge ν u)) ^ 2) =
        fun u => -(g (clockAge ν u) * (clockA ν (clockAge ν u)) ^ 2) := by
      funext u; simp [Function.comp]
    rw [heq, intervalIntegral.integral_neg]
  rw [hneg] at hcov
  rw [intervalIntegral.integral_symm (clockAge ν θ₁) (clockAge ν θ₂), ← hcov, neg_neg]

private def resTerm (ν a₀ u : ℝ) : ℝ :=
  (ν ^ 3) ^ 2 * u ^ (-2 : ℝ) + ν ^ 3 * Real.exp (-a₀ * u / ν ^ 3)

private lemma continuousOn_resTerm {ν a₀ θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) :
    ContinuousOn (resTerm ν a₀) (Icc θ₁ θ₂) := by
  unfold resTerm
  have c1 : ContinuousOn (fun u : ℝ => (ν ^ 3) ^ 2 * u ^ (-2 : ℝ)) (Icc θ₁ θ₂) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun u hu =>
      Or.inl (lt_of_lt_of_le hθ₁ hu.1).ne')
  have c2 : ContinuousOn (fun u : ℝ => ν ^ 3 * Real.exp (-a₀ * u / ν ^ 3)) (Icc θ₁ θ₂) :=
    (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const _))).continuousOn
  exact c1.add c2

private lemma integral_resTerm_le {ν a₀ θ₁ θ₂ : ℝ} (hν : 0 < ν) (ha₀ : 0 < a₀)
    (hθ₁ : 0 < θ₁) (h12 : θ₁ ≤ θ₂) :
    ∫ u in θ₁..θ₂, resTerm ν a₀ u ≤
      (ν ^ 3) ^ 2 / θ₁ + (ν ^ 6 / a₀) * Real.exp (-a₀ * θ₁ / ν ^ 3) := by
  have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ h12
  have hν_ne : ν ≠ 0 := hν.ne'
  have ha₀_ne : a₀ ≠ 0 := ha₀.ne'
  let f₁ : ℝ → ℝ := fun u => (ν ^ 3) ^ 2 * u ^ (-2 : ℝ)
  let F₁ : ℝ → ℝ := fun u => -((ν ^ 3) ^ 2) * u⁻¹
  have hd₁ : ∀ u ∈ uIcc θ₁ θ₂, HasDerivAt F₁ (f₁ u) u := by
    intro u hu
    rw [uIcc_of_le h12] at hu
    have hu0 : 0 < u := lt_of_lt_of_le hθ₁ hu.1
    have h0 : HasDerivAt F₁ (-((ν ^ 3) ^ 2) * -(u ^ 2)⁻¹) u :=
      (hasDerivAt_inv hu0.ne').const_mul (-((ν ^ 3) ^ 2))
    have h1 : -((ν ^ 3) ^ 2) * -(u ^ 2)⁻¹ = f₁ u := by
      dsimp only [f₁]
      rw [Real.rpow_neg hu0.le, Real.rpow_two]
      ring
    rwa [h1] at h0
  have hc₁ : ContinuousOn f₁ (uIcc θ₁ θ₂) := by
    rw [uIcc_of_le h12]
    exact continuousOn_const.mul (continuousOn_id.rpow_const fun u hu =>
      Or.inl (lt_of_lt_of_le hθ₁ hu.1).ne')
  have hi₁ : ∫ u in θ₁..θ₂, f₁ u = F₁ θ₂ - F₁ θ₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd₁ hc₁.intervalIntegrable
  let f₂ : ℝ → ℝ := fun u => ν ^ 3 * Real.exp (-a₀ * u / ν ^ 3)
  let F₂ : ℝ → ℝ := fun u => -(ν ^ 6 / a₀) * Real.exp (-a₀ * u / ν ^ 3)
  have hd₂ : ∀ u ∈ uIcc θ₁ θ₂, HasDerivAt F₂ (f₂ u) u := by
    intro u _
    have hlin : HasDerivAt (fun x : ℝ => -a₀ * x / ν ^ 3) (-a₀ / ν ^ 3) u := by
      simpa using ((hasDerivAt_id u).const_mul (-a₀)).div_const (ν ^ 3)
    have h0 : HasDerivAt F₂ (-(ν ^ 6 / a₀) * (Real.exp (-a₀ * u / ν ^ 3) * (-a₀ / ν ^ 3))) u :=
      hlin.exp.const_mul (-(ν ^ 6 / a₀))
    have h1 : -(ν ^ 6 / a₀) * (Real.exp (-a₀ * u / ν ^ 3) * (-a₀ / ν ^ 3)) = f₂ u := by
      dsimp only [f₂]
      field_simp
    rwa [h1] at h0
  have hc₂ : ContinuousOn f₂ (uIcc θ₁ θ₂) :=
    (continuous_const.mul
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const _))).continuousOn
  have hi₂ : ∫ u in θ₁..θ₂, f₂ u = F₂ θ₂ - F₂ θ₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd₂ hc₂.intervalIntegrable
  have hsplit : ∫ u in θ₁..θ₂, resTerm ν a₀ u = (∫ u in θ₁..θ₂, f₁ u) + ∫ u in θ₁..θ₂, f₂ u :=
    intervalIntegral.integral_add hc₁.intervalIntegrable hc₂.intervalIntegrable
  rw [hsplit, hi₁, hi₂]
  have hb₁ : F₁ θ₂ - F₁ θ₁ ≤ (ν ^ 3) ^ 2 / θ₁ := by
    dsimp only [F₁]
    have hnn : 0 ≤ (ν ^ 3) ^ 2 * θ₂⁻¹ := by positivity
    rw [div_eq_mul_inv]
    linarith
  have hb₂ : F₂ θ₂ - F₂ θ₁ ≤ (ν ^ 6 / a₀) * Real.exp (-a₀ * θ₁ / ν ^ 3) := by
    dsimp only [F₂]
    have hnn : 0 ≤ (ν ^ 6 / a₀) * Real.exp (-a₀ * θ₂ / ν ^ 3) := by positivity
    linarith
  exact add_le_add hb₁ hb₂

/-! ### 4.2 Continuous linear maps on `ActualVorticity` for `xNorm`, `kinNorm`, and `quadQ` -/

private def scaleReal (a : ℝ) (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  a ^ 2 * g (Real.sqrt a * y.1, Real.sqrt a * y.2)

private lemma cplx_scaleReal_eq (a : ℝ) (g : ℝ × ℝ → ℝ) :
    Exist.cplx (scaleReal a g) = JscaleInv a (Exist.cplx g) := by
  funext y
  simp [Exist.cplx, scaleReal, JscaleInv]

private lemma memLp_congr_cellMeasure {α : Type*} [NormedAddCommGroup α] {c₁ c₂ m : ℝ}
    (hc : c₁ = c₂) {g : ℝ × ℝ → α} (hg : MemLp g 2 (B0579.cellMeasure c₁ m)) :
    MemLp g 2 (B0579.cellMeasure c₂ m) :=
  hc ▸ hg

private lemma ae_cell_congr {c₁ c₂ : ℝ} (hc : c₁ = c₂) {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ x ∂volume.restrict (B0579.cell c₁), P x) :
    ∀ᵐ x ∂volume.restrict (B0579.cell c₂), P x :=
  hc ▸ h

private lemma isBiotSavart_congr_c {c₁ c₂ : ℝ} (hc : c₁ = c₂)
    {w : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ} (h : IsBiotSavart c₁ w u) :
    IsBiotSavart c₂ w u :=
  hc ▸ h

private lemma hasZeroCirc_congr_c {c₁ c₂ : ℝ} (hc : c₁ = c₂)
    {g : ℝ × ℝ → ℂ} (h : HasZeroCirculation c₁ g) :
    HasZeroCirculation c₂ g :=
  hc ▸ h

private lemma memLp_cplx_of_X {c m : ℝ} (f : B0579.X c m) :
    MemLp (Exist.cplx f) 2 (B0579.cellMeasure c m) ∧
      xNorm c m (Exist.cplx f) = ENNReal.ofReal ‖f‖ := by
  have hm : MemLp (Exist.cplx f) 2 (B0579.cellMeasure c m) := (Lp.memLp f).ofReal
  have hn : xNorm c m (Exist.cplx f) = eLpNorm (f : B0579.Plane → ℝ) 2 (B0579.cellMeasure c m) := by
    unfold xNorm
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    simp [Exist.cplx]
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  exact ⟨hm, hn⟩

private lemma scaleReal_memLp {c m a d : ℝ} (hm0 : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    (hdc : d * Real.sqrt a = c) (f : B0579.X c m) :
    MemLp (scaleReal a f) 2 (B0579.cellMeasure d m) := by
  have hf := memLp_congr_cellMeasure hdc.symm (memLp_cplx_of_X f).1
  have hJ := (jscaleInv_memLp_bound hm0 ha hd hf).1
  rw [← cplx_scaleReal_eq] at hJ
  simpa [Exist.cplx] using hJ.re

private lemma scaleReal_toLp_norm {c m a d : ℝ} (hm0 : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
    (hdc : d * Real.sqrt a = c) (f : B0579.X c m) :
    ENNReal.ofReal ‖(scaleReal_memLp hm0 ha hd hdc f).toLp (scaleReal a f)‖ =
        xNorm d m (JscaleInv a (Exist.cplx f)) ∧
      ‖(scaleReal_memLp hm0 ha hd hdc f).toLp (scaleReal a f)‖ ≤ a ^ (3 / 2 : ℝ) * ‖f‖ := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  obtain ⟨hf_mem, hf_nrm⟩ := memLp_cplx_of_X f
  have hf_mem' : MemLp (Exist.cplx f) 2 (B0579.cellMeasure (d * Real.sqrt a) m) :=
    memLp_congr_cellMeasure hdc.symm hf_mem
  have hJ_bd := (jscaleInv_memLp_bound hm0 ha hd hf_mem').2
  rw [hdc, hf_nrm] at hJ_bd
  have heq_nrm : eLpNorm (scaleReal a f) 2 (B0579.cellMeasure d m) =
      xNorm d m (JscaleInv a (Exist.cplx f)) := by
    unfold xNorm
    rw [← cplx_scaleReal_eq]
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun y => ?_)
    simp [Exist.cplx]
  have h1 : ENNReal.ofReal ‖(scaleReal_memLp hm0 ha hd hdc f).toLp (scaleReal a f)‖ =
      xNorm d m (JscaleInv a (Exist.cplx f)) := by
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal (scaleReal_memLp hm0 ha hd hdc f).eLpNorm_ne_top,
      heq_nrm]
  refine ⟨h1, ?_⟩
  have h2 : ENNReal.ofReal ‖(scaleReal_memLp hm0 ha hd hdc f).toLp (scaleReal a f)‖ ≤
      ENNReal.ofReal (a ^ (3 / 2 : ℝ) * ‖f‖) := by
    rw [h1, ENNReal.ofReal_mul (Real.rpow_nonneg ha0.le _)]
    exact hJ_bd
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg ha0.le _) (norm_nonneg f))).1 h2

private def jscaleInvActualCLM {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m) (ha : 1 ≤ a)
    (hd : 0 < d) (hdc : d * Real.sqrt a = c) :
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1 →L[ℝ] B0579.X d m := by
  have hm0 : 0 ≤ m := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  let L : B0579.X c m →ₗ[ℝ] B0579.X d m := {
    toFun := fun f => (scaleReal_memLp hm0 ha hd hdc f).toLp (scaleReal a f)
    map_add' := fun f g => by
      have hae_c : Exist.cplx ((f + g : B0579.X c m)) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))]
          fun x => Exist.cplx f x + Exist.cplx g x := by
        have h0 := ae_cell_congr hdc.symm ((B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_add f g))
        filter_upwards [h0] with x hx
        dsimp only [Exist.cplx]
        rw [hx, Pi.add_apply, Complex.ofReal_add]
      have hae_d : scaleReal a ((f + g : B0579.X c m)) =ᵐ[B0579.cellMeasure d m]
          scaleReal a f + scaleReal a g := by
        refine (B0579.cellMeasure_ac d m).ae_le ?_
        filter_upwards [ae_smul_sqrt_of_ae ha0 hae_c] with y hy
        have := congrArg Complex.re hy
        dsimp only [Exist.cplx, Pi.add_apply] at this
        simp only [Complex.ofReal_re, Complex.add_re] at this
        dsimp only [scaleReal, Pi.add_apply]
        rw [this]
        ring
      rw [MemLp.toLp_congr (scaleReal_memLp hm0 ha hd hdc (f + g))
        ((scaleReal_memLp hm0 ha hd hdc f).add (scaleReal_memLp hm0 ha hd hdc g)) hae_d]
      exact MemLp.toLp_add (scaleReal_memLp hm0 ha hd hdc f) (scaleReal_memLp hm0 ha hd hdc g)
    map_smul' := fun α f => by
      have hae_c : Exist.cplx ((α • f : B0579.X c m)) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))]
          fun x => (α : ℂ) * Exist.cplx f x := by
        have h0 := ae_cell_congr hdc.symm ((B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_smul α f))
        filter_upwards [h0] with x hx
        simp [Exist.cplx, hx]
      have hae_d : scaleReal a ((α • f : B0579.X c m)) =ᵐ[B0579.cellMeasure d m]
          α • scaleReal a f := by
        refine (B0579.cellMeasure_ac d m).ae_le ?_
        filter_upwards [ae_smul_sqrt_of_ae ha0 hae_c] with y hy
        have := congrArg Complex.re hy
        dsimp only [Exist.cplx] at this
        rw [← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re] at this
        dsimp only [scaleReal, Pi.smul_apply, smul_eq_mul]
        rw [this]
        ring
      rw [RingHom.id_apply, MemLp.toLp_congr (scaleReal_memLp hm0 ha hd hdc (α • f))
        ((scaleReal_memLp hm0 ha hd hdc f).const_smul α) hae_d]
      exact MemLp.toLp_const_smul α (scaleReal_memLp hm0 ha hd hdc f)
  }
  exact (L.mkContinuous (a ^ (3 / 2 : ℝ))
    (fun f => (scaleReal_toLp_norm hm0 ha hd hdc f).2)).comp (Submodule.subtypeL _)

private lemma ofReal_norm_jscaleInvActualCLM {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (ha : 1 ≤ a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    ENNReal.ofReal ‖jscaleInvActualCLM hm1 ha hd hdc v‖ =
      xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) :=
  (scaleReal_toLp_norm (by linarith) ha hd hdc v.1).1

private lemma velNorm_stripVel_eq {c m : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    velNorm c (Exist.stripVel hm1 v) =
      ENNReal.ofReal
        ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v‖ := by
  let F : Lp UnforcedLeray.Train.Vec 2 (B0581.cellVol c) :=
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v
  have hF_meas : AEStronglyMeasurable (F : B0579.Plane → UnforcedLeray.Train.Vec) (B0581.cellVol c) :=
    Lp.aestronglyMeasurable F
  have hcoord : ∀ j : Fin 2,
      AEMeasurable (fun x => ‖Exist.stripVel hm1 v x j‖ₑ ^ 2) (B0581.cellVol c) := by
    intro j
    have h1 : AEStronglyMeasurable (fun x => (F : B0579.Plane → UnforcedLeray.Train.Vec) x j)
        (B0581.cellVol c) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp_aestronglyMeasurable hF_meas
    have h2 : (fun x => ‖Exist.stripVel hm1 v x j‖ₑ ^ 2) =
        fun x => ‖(F : B0579.Plane → UnforcedLeray.Train.Vec) x j‖ₑ ^ 2 := by
      funext x
      change ‖((F x j : ℝ) : ℂ)‖ₑ ^ 2 = ‖F x j‖ₑ ^ 2
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
    rw [h2]
    exact h1.enorm.pow_const 2
  have heucl : ∀ u : UnforcedLeray.Train.Vec, ∑ j : Fin 2, ‖u j‖ₑ ^ 2 = ‖u‖ₑ ^ 2 := by
    intro u
    have h : ‖u‖₊ ^ 2 = ∑ j : Fin 2, ‖u j‖₊ ^ 2 := by
      rw [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt]
    simp only [enorm_eq_nnnorm]
    rw [← ENNReal.coe_pow, h, ENNReal.ofNNReal_finsetSum]
    simp only [ENNReal.coe_pow]
  have hcomp : ∀ j : Fin 2,
      eLpNorm (fun x => Exist.stripVel hm1 v x j) 2 (B0581.cellVol c) ^ 2 =
        ∫⁻ x, ‖Exist.stripVel hm1 v x j‖ₑ ^ 2 ∂(B0581.cellVol c) := by
    intro j
    rw [T06.eLpNorm_two_eq_lintegral, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsum : ∑ j : Fin 2, eLpNorm (fun x => Exist.stripVel hm1 v x j) 2 (B0581.cellVol c) ^ 2 =
      ∫⁻ x, ‖(F : B0579.Plane → UnforcedLeray.Train.Vec) x‖ₑ ^ 2 ∂(B0581.cellVol c) := by
    calc ∑ j : Fin 2, eLpNorm (fun x => Exist.stripVel hm1 v x j) 2 (B0581.cellVol c) ^ 2
        = ∑ j : Fin 2, ∫⁻ x, ‖Exist.stripVel hm1 v x j‖ₑ ^ 2 ∂(B0581.cellVol c) :=
          Finset.sum_congr rfl fun j _ => hcomp j
      _ = ∫⁻ x, ∑ j : Fin 2, ‖Exist.stripVel hm1 v x j‖ₑ ^ 2 ∂(B0581.cellVol c) :=
          (lintegral_finsetSum' _ fun j _ => hcoord j).symm
      _ = ∫⁻ x, ‖(F : B0579.Plane → UnforcedLeray.Train.Vec) x‖ₑ ^ 2 ∂(B0581.cellVol c) := by
          refine lintegral_congr fun x => ?_
          have hpt : ∀ j : Fin 2, ‖Exist.stripVel hm1 v x j‖ₑ ^ 2 = ‖F x j‖ₑ ^ 2 := fun j => by
            change ‖((F x j : ℝ) : ℂ)‖ₑ ^ 2 = ‖F x j‖ₑ ^ 2
            rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
          simp only [hpt, heucl (F x)]
  have hFV : eLpNorm (F : B0579.Plane → UnforcedLeray.Train.Vec) 2 (B0581.cellVol c) =
      (∫⁻ x, ‖(F : B0579.Plane → UnforcedLeray.Train.Vec) x‖ₑ ^ 2 ∂(B0581.cellVol c)) ^
        (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num [ENNReal.rpow_two]
  unfold velNorm
  change (∑ j : Fin 2, eLpNorm (fun x => Exist.stripVel hm1 v x j) 2 (B0581.cellVol c) ^ 2) ^
      (1 / 2 : ℝ) = ENNReal.ofReal ‖F‖
  rw [hsum, ← hFV, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]

private lemma kinNorm_jscaleInv_vortFn_eq {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (ha : 0 < a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    kinNorm d (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) =
      ENNReal.ofReal (a *
        ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v‖) := by
  have hbs_c : IsBiotSavart c (Exist.cplx (Exist.vortFn hm1 v)) (Exist.stripVel hm1 v) :=
    Exist.biotSavartFieldAll c m hm1 v
  have hbs_c' : IsBiotSavart (d * Real.sqrt a) (Exist.cplx (Exist.vortFn hm1 v))
      (Exist.stripVel hm1 v) := isBiotSavart_congr_c hdc.symm hbs_c
  obtain ⟨hbs_d, hvel⟩ := isBiotSavart_velMov ha hd hbs_c'
  rw [kinNorm_eq_of_isBiotSavart hd hbs_d, hvel, hdc, velNorm_stripVel_eq hm1 v,
    ENNReal.ofReal_mul ha.le]

private lemma quadQ_jscaleInv_eq {a d c : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hdc : d * Real.sqrt a = c) (g : ℝ × ℝ → ℂ) :
    quadQ d (JscaleInv a g) = quadQ c g := by
  unfold quadQ
  have hsq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hpt : (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * JscaleInv a g y) =
      fun y => (a : ℂ) * ((((Real.sqrt a * y.2) ^ 2 : ℝ) : ℂ) *
        g (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
    funext y
    unfold JscaleInv
    have hy : y.2 ^ 2 * a ^ 2 = a * (Real.sqrt a * y.2) ^ 2 := by
      calc y.2 ^ 2 * a ^ 2 = a * ((Real.sqrt a) ^ 2 * y.2 ^ 2) := by rw [hsq]; ring
        _ = a * (Real.sqrt a * y.2) ^ 2 := by ring
    calc ((y.2 ^ 2 : ℝ) : ℂ) * (((a ^ 2 : ℝ) : ℂ) * g (Real.sqrt a * y.1, Real.sqrt a * y.2))
        = (((y.2 ^ 2 * a ^ 2 : ℝ)) : ℂ) * g (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
          push_cast; ring
      _ = (a : ℂ) * ((((Real.sqrt a * y.2) ^ 2 : ℝ) : ℂ) *
            g (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
          rw [hy]; push_cast; ring
  have hcov := integral_cell_comp_sqrt_smul ha hd (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * g x)
  rw [hdc] at hcov
  rw [hpt, integral_const_mul]
  change -((2 / Real.pi : ℝ) : ℂ) *
      ((a : ℂ) * ∫ y in B0579.cell d,
        (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * g x) (Real.sqrt a * y.1, Real.sqrt a * y.2)) = _
  rw [hcov, ← mul_assoc _ ((a⁻¹ : ℝ) : ℂ)]
  have ha_inv : (a : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 ha.ne')]
  rw [ha_inv, one_mul]

private lemma memLp_eta_sq_neg (c m : ℝ) (hm3 : 3 < m) :
    MemLp (fun x : ℝ × ℝ => x.2 ^ 2) 2 (B0579.cellMeasure c (-m)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ × ℝ => x.2 ^ 2) (B0579.cellMeasure c (-m)) :=
    (measurable_snd.pow_const 2).aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq hmeas, B0579.integrable_cellMeasure_iff]
  have hdom : IntegrableOn (fun x : ℝ × ℝ => (1 + ‖x‖ ^ 2) ^ (2 - m)) (B0579.cell c) :=
    (CTE.QuadQBoundProof.integrable_moment m hm3).integrableOn
  refine hdom.mono'
    (((B0579.measurable_density (-m)).coe_nnreal_real.mul
      ((measurable_snd.pow_const 2).pow_const 2)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hjb : 0 < B0579.jb x := B0579.jb_pos x
  rw [NNReal.smul_def, smul_eq_mul, B0579.coe_density, Real.rpow_neg hjb.le,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 (Real.rpow_nonneg hjb.le m)) (sq_nonneg _))]
  exact CTE.QuadQBoundProof.inv_mul_sq_le m hm3 x

private def quadRealCLM (c m : ℝ) [Fact (0 < c)] (hm1 : 1 ≤ m) (hm3 : 3 < m) :
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1 →L[ℝ] ℝ :=
  (-(2 / Real.pi)) •
    (innerSL ℝ (B0579.mulW c (-m) m
      ((memLp_eta_sq_neg c m hm3).toLp (fun x => x.2 ^ 2)))).comp (Submodule.subtypeL _)

private lemma quadQ_jscaleInv_vortFn_eq {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (hm3 : 3 < m) (ha : 0 < a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    quadQ d (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) =
      ((quadRealCLM c m hm1 hm3 v : ℝ) : ℂ) := by
  rw [quadQ_jscaleInv_eq ha hd hdc]
  let ηLp : B0579.X c (-m) := (memLp_eta_sq_neg c m hm3).toLp (fun x => x.2 ^ 2)
  have hη_ae : (ηLp : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] fun x => x.2 ^ 2 :=
    (B0579.ac_cellMeasure c (-m)).ae_le ((memLp_eta_sq_neg c m hm3).coeFn_toLp)
  have hpair : inner ℝ (B0579.mulW c (-m) m ηLp) v.1 =
      ∫ x in B0579.cell c, x.2 ^ 2 * Exist.vortFn hm1 v x := by
    rw [B0579.inner_mulW_neg c m v.1 ηLp]
    refine integral_congr_ae (hη_ae.mono fun x hx => ?_)
    dsimp only [Exist.vortFn] at hx ⊢
    rw [hx, mul_comm]
  have hreal : quadRealCLM c m hm1 hm3 v =
      -(2 / Real.pi) * ∫ x in B0579.cell c, x.2 ^ 2 * Exist.vortFn hm1 v x := by
    change -(2 / Real.pi) * inner ℝ (B0579.mulW c (-m) m ηLp) v.1 = _
    rw [hpair]
  unfold quadQ
  have hpt : (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * Exist.cplx (Exist.vortFn hm1 v) x) =
      fun x => ((x.2 ^ 2 * Exist.vortFn hm1 v x : ℝ) : ℂ) := by
    funext x; simp [Exist.cplx]
  rw [hpt, integral_complex_ofReal, hreal]
  push_cast
  ring

private lemma norm_quadQ_jscaleInv_vortFn_eq {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (hm3 : 3 < m) (ha : 0 < a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1) :
    ‖quadQ d (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v)))‖ = ‖quadRealCLM c m hm1 hm3 v‖ := by
  rw [quadQ_jscaleInv_vortFn_eq hm1 hm3 ha hd hdc v, Complex.norm_real]

/-! ### 4.3 Heat-column norm, symmetry, and canonical-column window helpers -/

private lemma heatColumn_sub_canonicalPeriodized_eq (P : PlanarData) {ν θ : ℝ}
    (hν : 0 < ν) (hθ : 0 < θ) (w : ℝ → ℝ × ℝ → ℂ) :
    heatColumn P ν w θ - canonicalPeriodized P ν θ =
      fun y => (P.gaugeFactor ν)⁻¹ *
        JscaleInv (ν * θ)⁻¹
          (fun x => w (clockAge ν θ) x - canonicalPhysColumn P ν (clockAge ν θ) x) y := by
  rw [← heatColumn_canonicalPhysColumn_eq P hν hθ]
  funext y
  simp only [Pi.sub_apply, heatColumn, JscaleInv]
  ring

private lemma xNorm_jscaleInv_vortFn_le_of_re {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (ha : 0 < a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1)
    {g : ℝ × ℝ → ℂ} (hre : Exist.vortFn hm1 v =ᵐ[volume.restrict (B0579.cell c)] fun x => (g x).re) :
    xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) ≤ xNorm d m (JscaleInv a g) := by
  have hcplx : Exist.cplx (Exist.vortFn hm1 v) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))]
      fun x => ((g x).re : ℂ) := by
    have h0 : Exist.vortFn hm1 v =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))]
        fun x => (g x).re := ae_cell_congr hdc.symm hre
    exact h0.mono fun x hx => by simp [Exist.cplx, hx]
  have hJ : JscaleInv a (Exist.cplx (Exist.vortFn hm1 v)) =ᵐ[B0579.cellMeasure d m]
      JscaleInv a (fun x => ((g x).re : ℂ)) :=
    (B0579.cellMeasure_ac d m).ae_le (jscaleInv_ae_volume ha hd rfl hcplx)
  rw [show xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) =
      xNorm d m (JscaleInv a (fun x => ((g x).re : ℂ))) from eLpNorm_congr_ae hJ]
  unfold xNorm
  refine eLpNorm_mono_ae (Eventually.of_forall fun y => ?_)
  dsimp only [JscaleInv]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)

private lemma xNorm_jscaleInv_vortFn_le_of_im {c m a d : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (ha : 0 < a) (hd : 0 < d) (hdc : d * Real.sqrt a = c)
    (v : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity (c := c) (m := m) hm1)
    {g : ℝ × ℝ → ℂ} (him : Exist.vortFn hm1 v =ᵐ[volume.restrict (B0579.cell c)] fun x => (g x).im) :
    xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) ≤ xNorm d m (JscaleInv a g) := by
  have hcplx : Exist.cplx (Exist.vortFn hm1 v) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))]
      fun x => ((g x).im : ℂ) := by
    have h0 : Exist.vortFn hm1 v =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))]
        fun x => (g x).im := ae_cell_congr hdc.symm him
    exact h0.mono fun x hx => by simp [Exist.cplx, hx]
  have hJ : JscaleInv a (Exist.cplx (Exist.vortFn hm1 v)) =ᵐ[B0579.cellMeasure d m]
      JscaleInv a (fun x => ((g x).im : ℂ)) :=
    (B0579.cellMeasure_ac d m).ae_le (jscaleInv_ae_volume ha hd rfl hcplx)
  rw [show xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v))) =
      xNorm d m (JscaleInv a (fun x => ((g x).im : ℂ))) from eLpNorm_congr_ae hJ]
  unfold xNorm
  refine eLpNorm_mono_ae (Eventually.of_forall fun y => ?_)
  dsimp only [JscaleInv]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg _)

private lemma symEven_jscaleInv_props {c d m a : ℝ} (hm : 1 < m) (ha : 1 ≤ a) (hd : 0 < d)
    (hdc : d * Real.sqrt a = c) {g : ℝ × ℝ → ℂ} {u_g : ℝ × ℝ → Fin 2 → ℂ}
    (hg_mem : MemLp g 2 (B0579.cellMeasure c m))
    (hg_zc : HasZeroCirculation c g)
    (hg_bs : IsBiotSavart c g u_g)
    (hg_even : (fun x => g (-x)) =ᵐ[volume.restrict (B0579.cell c)] g) :
    let h := symEven (JscaleInv a g)
    MemLp h 2 (B0579.cellMeasure d m) ∧
      HasZeroCirculation d h ∧
      IsCentrallyEven h ∧
      IsBiotSavart d h (velMov a u_g) ∧
      xNorm d m h = xNorm d m (JscaleInv a g) ∧
      Jscale a h =ᵐ[volume.restrict (B0579.cell c)] g := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hg_mem' : MemLp g 2 (B0579.cellMeasure (d * Real.sqrt a) m) :=
    memLp_congr_cellMeasure hdc.symm hg_mem
  have hg_zc' : HasZeroCirculation (d * Real.sqrt a) g := hasZeroCirc_congr_c hdc.symm hg_zc
  have hg_bs' : IsBiotSavart (d * Real.sqrt a) g u_g := isBiotSavart_congr_c hdc.symm hg_bs
  have hg_even' : (fun x => g (-x)) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] g :=
    ae_cell_congr hdc.symm hg_even
  have hJ_even : (fun y => JscaleInv a g (-y)) =ᵐ[volume.restrict (B0579.cell d)] JscaleInv a g := by
    have h0 := jscaleInv_ae_volume ha0 hd rfl hg_even'
    refine h0.mono fun y hy => ?_
    have hcoord : (Real.sqrt a * (-y).1, Real.sqrt a * (-y).2) =
        -(Real.sqrt a * y.1, Real.sqrt a * y.2) := by ext <;> simp
    simpa [JscaleInv, hcoord] using hy
  have hae_vol : symEven (JscaleInv a g) =ᵐ[volume.restrict (B0579.cell d)] JscaleInv a g :=
    symEven_ae_eq hJ_even
  have hae_cm : symEven (JscaleInv a g) =ᵐ[B0579.cellMeasure d m] JscaleInv a g :=
    (B0579.cellMeasure_ac d m).ae_le hae_vol
  have hJ_mem := (jscaleInv_memLp_bound (by linarith) ha hd hg_mem').1
  have hJ_zc := hasZeroCirc_jscaleInv hm ha hd hg_mem' hg_zc'
  have hJ_bs := (isBiotSavart_velMov ha0 hd hg_bs').1
  refine ⟨hJ_mem.ae_eq hae_cm.symm, ?_, isCentrallyEven_symEven _, ?_,
    eLpNorm_congr_ae hae_cm, ?_⟩
  · exact ⟨hJ_zc.1.congr_fun_ae hae_vol.symm, (integral_congr_ae hae_vol).trans hJ_zc.2⟩
  · exact isBiotSavart_congr_ae hJ_bs hae_vol.symm EventuallyEq.rfl
  · have hdiv := ae_div_sqrt_of_ae ha0 hae_vol
    rw [hdc] at hdiv
    have hj := jscale_jscaleInv ha0 g
    filter_upwards [hdiv] with x hx
    have hjx := congrFun hj x
    dsimp only [Jscale] at hx hjx ⊢
    rwa [hx]

private lemma integrableOn_eta_sq_mul {d m : ℝ} (hm3 : 3 < m) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure d m)) :
    IntegrableOn (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * f y) (B0579.cell d) := by
  let ηLp : B0579.X d (-m) := (memLp_eta_sq_neg d m hm3).toLp (fun y => y.2 ^ 2)
  have hη_ae : (ηLp : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell d)] fun y => y.2 ^ 2 :=
    (B0579.ac_cellMeasure d (-m)).ae_le ((memLp_eta_sq_neg d m hm3).coeFn_toLp)
  have hre : MemLp (fun y => (f y).re) 2 (B0579.cellMeasure d m) := hf.re
  have him : MemLp (fun y => (f y).im) 2 (B0579.cellMeasure d m) := hf.im
  have ire0 := B0579.integrableOn_mul_neg d m (hre.toLp _) ηLp
  have iim0 := B0579.integrableOn_mul_neg d m (him.toLp _) ηLp
  have ire : IntegrableOn (fun y : ℝ × ℝ => y.2 ^ 2 * (f y).re) (B0579.cell d) := by
    refine ire0.congr_fun_ae ?_
    filter_upwards [(B0579.ac_cellMeasure d m).ae_le hre.coeFn_toLp, hη_ae] with y h1 h2
    rw [h1, h2, mul_comm]
  have iim : IntegrableOn (fun y : ℝ × ℝ => y.2 ^ 2 * (f y).im) (B0579.cell d) := by
    refine iim0.congr_fun_ae ?_
    filter_upwards [(B0579.ac_cellMeasure d m).ae_le him.coeFn_toLp, hη_ae] with y h1 h2
    rw [h1, h2, mul_comm]
  have heq : (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * f y) =
      fun y => ((y.2 ^ 2 * (f y).re : ℝ) : ℂ) + Complex.I * ((y.2 ^ 2 * (f y).im : ℝ) : ℂ) := by
    funext y
    have hf_eq : f y = (f y).re + Complex.I * (f y).im := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hf_eq]
    push_cast
    ring
  rw [heq]
  exact (Complex.ofRealCLM.integrable_comp ire).add
    ((Complex.ofRealCLM.integrable_comp iim).const_mul Complex.I)

private lemma xNorm_heatDiff_inhom_le {c d m a : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m)
    (ha : 1 ≤ a) (hd : 0 < d) (hdc : d * Real.sqrt a = c) (α : ℂ)
    {diff : ℝ × ℝ → ℂ}
    (v_re v_im : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1)
    (hae : diff =ᵐ[volume.restrict (B0579.cell c)]
      fun x => -(Exist.cplx (Exist.vortFn hm1 v_re) x +
        Complex.I * Exist.cplx (Exist.vortFn hm1 v_im) x)) :
    xNorm d m (fun y => α * JscaleInv a diff y) ≤
      ENNReal.ofReal ‖α‖ *
        (ENNReal.ofReal ‖jscaleInvActualCLM hm1 ha hd hdc v_re‖ +
          ENNReal.ofReal ‖jscaleInvActualCLM hm1 ha hd hdc v_im‖) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hJ_ae : (fun y => α * JscaleInv a diff y) =ᵐ[B0579.cellMeasure d m]
      fun y => (-α) * (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) y +
        Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) y) := by
    refine (B0579.cellMeasure_ac d m).ae_le ?_
    have hae' : diff =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] _ :=
      ae_cell_congr hdc.symm hae
    filter_upwards [jscaleInv_ae_volume ha0 hd rfl hae'] with y hy
    rw [hy]
    unfold JscaleInv
    ring
  rw [show xNorm d m (fun y => α * JscaleInv a diff y) =
      xNorm d m (fun y => (-α) * (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) y +
        Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) y)) from eLpNorm_congr_ae hJ_ae]
  have hm_re := (jscaleInv_memLp_bound (by linarith) ha hd
    (memLp_congr_cellMeasure hdc.symm (Exist.goodCStable.1 c m hm1 v_re).1)).1
  have hm_im := (jscaleInv_memLp_bound (by linarith) ha hd
    (memLp_congr_cellMeasure hdc.symm (Exist.goodCStable.1 c m hm1 v_im).1)).1
  have hsmul : xNorm d m (fun y => (-α) * (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) y +
        Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) y)) =
      ENNReal.ofReal ‖α‖ *
        xNorm d m (fun y => JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) y +
          Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) y) := by
    unfold xNorm
    change eLpNorm ((-α) • fun y => JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) y +
        Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) y) 2 (B0579.cellMeasure d m) = _
    rw [eLpNorm_const_smul, ← ofReal_norm, norm_neg]
  have htri : xNorm d m (fun y => JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) y +
        Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) y) ≤
      xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re))) +
        xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im))) := by
    have h1 := eLpNorm_add_le hm_re.1 (hm_im.const_mul Complex.I).1 one_le_two
    have him_eq : eLpNorm (fun x => Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) x)
        2 (B0579.cellMeasure d m) =
        xNorm d m (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im))) := by
      change eLpNorm (Complex.I • JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)))
        2 (B0579.cellMeasure d m) = _
      rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one, one_mul]
      rfl
    change eLpNorm (JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re)) +
        fun x => Complex.I * JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im)) x)
        2 (B0579.cellMeasure d m) ≤ _
    rw [← him_eq]
    exact h1
  rw [hsmul, ofReal_norm_jscaleInvActualCLM, ofReal_norm_jscaleInvActualCLM]
  exact mul_le_mul_of_nonneg_left htri zero_le

private lemma kinNorm_heatDiff_inhom_le {c d m a : ℝ} [Fact (0 < c)] (hm : 1 < m) (hm1 : 1 ≤ m)
    (ha : 1 ≤ a) (hd : 0 < d) (hdc : d * Real.sqrt a = c) (α : ℂ)
    {diff w_hom_s : ℝ × ℝ → ℂ} {u_hom_s : ℝ × ℝ → Fin 2 → ℂ}
    (hhom_mem : MemLp w_hom_s 2 (B0579.cellMeasure c m))
    (hhom_bs : IsBiotSavart c w_hom_s u_hom_s)
    (v_re v_im : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1)
    (hae : diff =ᵐ[volume.restrict (B0579.cell c)]
      fun x => w_hom_s x - (Exist.cplx (Exist.vortFn hm1 v_re) x +
        Complex.I * Exist.cplx (Exist.vortFn hm1 v_im) x)) :
    kinNorm d (fun y => α * JscaleInv a diff y) ≤
      ENNReal.ofReal ‖α‖ *
        (kinNorm d (JscaleInv a w_hom_s) +
          ENNReal.ofReal (a *
            ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v_re‖) +
          ENNReal.ofReal (a *
            ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v_im‖)) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  let f₁ := JscaleInv a w_hom_s
  let f₂ := JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re))
  let f₃ := JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im))
  let u₁ := velMov a u_hom_s
  let u₂ := velMov a (Exist.stripVel hm1 v_re)
  let u₃ := velMov a (Exist.stripVel hm1 v_im)
  have m₁ : MemLp f₁ 2 (B0579.cellMeasure d m) :=
    (jscaleInv_memLp_bound (by linarith) ha hd (memLp_congr_cellMeasure hdc.symm hhom_mem)).1
  have m₂ : MemLp f₂ 2 (B0579.cellMeasure d m) :=
    (jscaleInv_memLp_bound (by linarith) ha hd
      (memLp_congr_cellMeasure hdc.symm (Exist.goodCStable.1 c m hm1 v_re).1)).1
  have m₃ : MemLp f₃ 2 (B0579.cellMeasure d m) :=
    (jscaleInv_memLp_bound (by linarith) ha hd
      (memLp_congr_cellMeasure hdc.symm (Exist.goodCStable.1 c m hm1 v_im).1)).1
  have b₁ : IsBiotSavart d f₁ u₁ :=
    (isBiotSavart_velMov ha0 hd (isBiotSavart_congr_c hdc.symm hhom_bs)).1
  have b₂ : IsBiotSavart d f₂ u₂ :=
    (isBiotSavart_velMov ha0 hd
      (isBiotSavart_congr_c hdc.symm (Exist.biotSavartFieldAll c m hm1 v_re))).1
  have b₃ : IsBiotSavart d f₃ u₃ :=
    (isBiotSavart_velMov ha0 hd
      (isBiotSavart_congr_c hdc.symm (Exist.biotSavartFieldAll c m hm1 v_im))).1
  have b₃I : IsBiotSavart d (fun y => Complex.I * f₃ y) (fun y j => Complex.I * u₃ y j) :=
    isBiotSavart_smul Complex.I b₃
  have b₂₃ : IsBiotSavart d (f₂ + fun y => Complex.I * f₃ y) (u₂ + fun y j => Complex.I * u₃ y j) :=
    isBiotSavart_add hm m₂ (m₃.const_mul Complex.I) b₂ b₃I
  have b₂₃n : IsBiotSavart d (fun y => (-1 : ℂ) * (f₂ y + Complex.I * f₃ y))
      (fun y j => (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j)) :=
    isBiotSavart_smul (-1 : ℂ) b₂₃
  have b_tot0 : IsBiotSavart d (f₁ + fun y => (-1 : ℂ) * (f₂ y + Complex.I * f₃ y))
      (u₁ + fun y j => (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j)) :=
    isBiotSavart_add hm m₁ ((m₂.add (m₃.const_mul Complex.I)).const_mul (-1 : ℂ)) b₁ b₂₃n
  have b_tot : IsBiotSavart d (fun y => α * (f₁ y + (-1 : ℂ) * (f₂ y + Complex.I * f₃ y)))
      (fun y j => α * (u₁ y j + (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j))) :=
    isBiotSavart_smul α b_tot0
  have hae_d : (fun y => α * JscaleInv a diff y) =ᵐ[volume.restrict (B0579.cell d)]
      fun y => α * (f₁ y + (-1 : ℂ) * (f₂ y + Complex.I * f₃ y)) := by
    have hae' : diff =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] _ :=
      ae_cell_congr hdc.symm hae
    filter_upwards [jscaleInv_ae_volume ha0 hd rfl hae'] with y hy
    dsimp only [f₁, f₂, f₃] at hy ⊢
    rw [hy]
    unfold JscaleInv
    ring
  rw [kinNorm_congr_ae hae_d, kinNorm_eq_of_isBiotSavart hd b_tot, velNorm_smul]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have v1 : velNorm d (u₁ + fun y j => (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j)) ≤
      velNorm d u₁ + velNorm d (fun y j => (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j)) :=
    velNorm_add_le b₁.1 b₂₃n.1
  have v2 : velNorm d (fun y j => (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j)) =
      velNorm d (u₂ + fun y j => Complex.I * u₃ y j) := by
    rw [velNorm_smul]; simp; rfl
  have v3 : velNorm d (u₂ + fun y j => Complex.I * u₃ y j) ≤
      velNorm d u₂ + velNorm d (fun y j => Complex.I * u₃ y j) :=
    velNorm_add_le b₂.1 b₃I.1
  have v4 : velNorm d (fun y j => Complex.I * u₃ y j) = velNorm d u₃ := by
    rw [velNorm_smul]; simp
  have hk1 : velNorm d u₁ = kinNorm d f₁ := (kinNorm_eq_of_isBiotSavart hd b₁).symm
  have hk2 : velNorm d u₂ =
      ENNReal.ofReal (a *
        ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v_re‖) := by
    rw [← kinNorm_eq_of_isBiotSavart hd b₂]
    exact kinNorm_jscaleInv_vortFn_eq hm1 ha0 hd hdc v_re
  have hk3 : velNorm d u₃ =
      ENNReal.ofReal (a *
        ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v_im‖) := by
    rw [← kinNorm_eq_of_isBiotSavart hd b₃]
    exact kinNorm_jscaleInv_vortFn_eq hm1 ha0 hd hdc v_im
  calc velNorm d (u₁ + fun y j => (-1 : ℂ) * (u₂ y j + Complex.I * u₃ y j))
      ≤ velNorm d u₁ + (velNorm d u₂ + velNorm d u₃) := by
        rw [v2] at v1; rw [v4] at v3; exact v1.trans (add_le_add le_rfl v3)
    _ = kinNorm d f₁ +
          ENNReal.ofReal (a *
            ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v_re‖) +
          ENNReal.ofReal (a *
            ‖UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM hm1 v_im‖) := by
        rw [hk1, hk2, hk3]
        exact (add_assoc _ _ _).symm

private lemma quadQ_heatDiff_inhom_le {c d m a : ℝ} [Fact (0 < c)] (hm1 : 1 ≤ m) (hm3 : 3 < m)
    (ha : 1 ≤ a) (hd : 0 < d) (hdc : d * Real.sqrt a = c) (α : ℂ)
    {diff w_hom_s : ℝ × ℝ → ℂ}
    (hhom_mem : MemLp w_hom_s 2 (B0579.cellMeasure c m))
    (v_re v_im : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := c) (m := m) hm1)
    (hae : diff =ᵐ[volume.restrict (B0579.cell c)]
      fun x => w_hom_s x - (Exist.cplx (Exist.vortFn hm1 v_re) x +
        Complex.I * Exist.cplx (Exist.vortFn hm1 v_im) x)) :
    ‖quadQ d (fun y => α * JscaleInv a diff y)‖ ≤
      ‖α‖ * (‖quadQ d (JscaleInv a w_hom_s)‖ +
        ‖quadRealCLM c m hm1 hm3 v_re‖ + ‖quadRealCLM c m hm1 hm3 v_im‖) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  let f₁ := JscaleInv a w_hom_s
  let f₂ := JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_re))
  let f₃ := JscaleInv a (Exist.cplx (Exist.vortFn hm1 v_im))
  have hae_d : (fun y => α * JscaleInv a diff y) =ᵐ[volume.restrict (B0579.cell d)]
      fun y => α * (f₁ y - (f₂ y + Complex.I * f₃ y)) := by
    have hae' : diff =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] _ :=
      ae_cell_congr hdc.symm hae
    filter_upwards [jscaleInv_ae_volume ha0 hd rfl hae'] with y hy
    dsimp only [f₁, f₂, f₃] at hy ⊢
    rw [hy]
    unfold JscaleInv
    ring
  rw [quadQ_congr_ae hae_d]
  have i₁ := integrableOn_eta_sq_mul hm3
    (jscaleInv_memLp_bound (by linarith) ha hd (memLp_congr_cellMeasure hdc.symm hhom_mem)).1
  have i₂ := integrableOn_eta_sq_mul hm3
    (jscaleInv_memLp_bound (by linarith) ha hd
      (memLp_congr_cellMeasure hdc.symm (Exist.goodCStable.1 c m hm1 v_re).1)).1
  have i₃ := integrableOn_eta_sq_mul hm3
    (jscaleInv_memLp_bound (by linarith) ha hd
      (memLp_congr_cellMeasure hdc.symm (Exist.goodCStable.1 c m hm1 v_im).1)).1
  have hlin : quadQ d (fun y => α * (f₁ y - (f₂ y + Complex.I * f₃ y))) =
      α * (quadQ d f₁ - (quadQ d f₂ + Complex.I * quadQ d f₃)) := by
    unfold quadQ
    have hpt : (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * (α * (f₁ y - (f₂ y + Complex.I * f₃ y)))) =
        fun y => α * (((y.2 ^ 2 : ℝ) : ℂ) * f₁ y -
          (((y.2 ^ 2 : ℝ) : ℂ) * f₂ y + Complex.I * (((y.2 ^ 2 : ℝ) : ℂ) * f₃ y))) := by
      funext y; ring
    have i₂₃ : IntegrableOn (fun y : ℝ × ℝ => ((y.2 ^ 2 : ℝ) : ℂ) * f₂ y +
        Complex.I * (((y.2 ^ 2 : ℝ) : ℂ) * f₃ y)) (B0579.cell d) :=
      i₂.add (i₃.const_mul Complex.I)
    rw [hpt, integral_const_mul, integral_sub i₁ i₂₃,
      integral_add i₂ (i₃.const_mul Complex.I), integral_const_mul]
    ring
  rw [hlin, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg α)
  have n1 := norm_sub_le (quadQ d f₁) (quadQ d f₂ + Complex.I * quadQ d f₃)
  have n2 := norm_add_le (quadQ d f₂) (Complex.I * quadQ d f₃)
  rw [norm_mul, Complex.norm_I, one_mul,
    norm_quadQ_jscaleInv_vortFn_eq hm1 hm3 ha0 hd hdc v_re,
    norm_quadQ_jscaleInv_vortFn_eq hm1 hm3 ha0 hd hdc v_im] at n2
  linarith

private lemma canonicalPhysColumn_window_props (hBranch : CTCanonicalBranchProps)
    (P : PlanarData) (hP : IsPlanarReference P) {m ν θ₀ : ℝ} (hm : 8 < m)
    (hν : ν ∈ Ioc (0 : ℝ) 1) (hθ₀ : 0 < θ₀) (hθν : θ₀ ≤ ν⁻¹) (hν3 : ν ^ 3 ≤ θ₀) :
    ∃ M_can : ℝ, 0 ≤ M_can ∧ ∀ s ∈ Icc (0 : ℝ) (clockAge ν θ₀),
      MemLp (canonicalPhysColumn P ν s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) ∧
      IsCentrallyEven (canonicalPhysColumn P ν s) ∧
      (xNorm (ν ^ (-2 : ℝ)) m (canonicalPhysColumn P ν s)).toReal ≤ M_can := by
  have hν0 : 0 < ν := hν.1
  obtain ⟨C_ν, hC_ν, hbd_ν⟩ := (hBranch P hP m hm).2.2.2 ν⁻¹ (inv_pos.2 hν0)
  let S := clockAge ν θ₀
  have hS0 : 0 ≤ S := clockAge_nonneg hν0 hθ₀ hθν
  have haS1 : 1 ≤ clockA ν S := by unfold clockA; nlinarith
  let M_can : ℝ := ‖P.gaugeFactor ν‖ * (clockA ν S) ^ ((m - 3) / 2) * C_ν
  have hM_can0 : 0 ≤ M_can := by
    dsimp [M_can]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)) hC_ν.le
  refine ⟨M_can, hM_can0, fun s hs => ?_⟩
  have ha1 : 1 ≤ clockA ν s := by unfold clockA; nlinarith [hs.1]
  have ha0 : 0 < clockA ν s := lt_of_lt_of_le one_pos ha1
  have ha_le : clockA ν s ≤ clockA ν S := by unfold clockA; nlinarith [hs.2]
  let θ_s := clockTheta ν s
  have hθ_s_inv : θ_s ≤ ν⁻¹ := by
    unfold θ_s clockTheta
    have hmul : ν ≤ ν * clockA ν s := le_mul_of_one_le_right hν0.le ha1
    exact inv_anti₀ hν0 hmul
  have hθ₀_le : θ₀ ≤ θ_s := by
    have hAS : clockA ν S = (ν * θ₀)⁻¹ := clockA_clockAge hν0 hθ₀
    unfold θ_s clockTheta
    have hmul : ν * clockA ν s ≤ ν * (ν * θ₀)⁻¹ := by
      rw [← hAS]; exact mul_le_mul_of_nonneg_left ha_le hν0.le
    have hinv : (ν * (ν * θ₀)⁻¹)⁻¹ ≤ (ν * clockA ν s)⁻¹ := inv_anti₀ (by positivity) hmul
    have hsimp : (ν * (ν * θ₀)⁻¹)⁻¹ = θ₀ := by
      have h1 : ν ≠ 0 := hν0.ne'
      have h2 : θ₀ ≠ 0 := hθ₀.ne'
      field_simp
    rwa [hsimp] at hinv
  have hθ_s_pos : 0 < θ_s := lt_of_lt_of_le hθ₀ hθ₀_le
  have hd1 : 1 ≤ dOfTheta ν θ_s := one_le_dOfTheta hν0 (hν3.trans hθ₀_le)
  have hd0 : 0 < dOfTheta ν θ_s := lt_of_lt_of_le one_pos hd1
  have hdc : dOfTheta ν θ_s * Real.sqrt (clockA ν s) = ν ^ (-2 : ℝ) := by
    rw [dOfTheta_eq_cellLen hν0 ha0]
    unfold cellLen
    exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha0).ne'
  obtain ⟨hV_mem, hV_zc, hV_ev, -⟩ := (hBranch P hP m hm).2.1 ν θ_s hν0 hθ_s_pos hd1
  have hV_bd : xNorm (dOfTheta ν θ_s) m (canonicalPeriodized P ν θ_s) ≤ ENNReal.ofReal C_ν :=
    hbd_ν ν hν θ_s ⟨hθ_s_pos, hθ_s_inv⟩ hd1
  obtain ⟨hJ_mem, hJ_bd⟩ := jscale_memLp_bound (by linarith) ha1 hd0 hV_mem
  have hJ_zc := hasZeroCirc_jscale (by linarith) ha1 hd0 hV_mem hV_zc
  rw [hdc] at hJ_mem hJ_bd hJ_zc
  have hcan_mem : MemLp (canonicalPhysColumn P ν s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    hJ_mem.const_mul (P.gaugeFactor ν)
  have hcan_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) :=
    ⟨hJ_zc.1.const_mul (P.gaugeFactor ν), by
      unfold canonicalPhysColumn; rw [integral_const_mul, hJ_zc.2, mul_zero]⟩
  have hcan_ev : IsCentrallyEven (canonicalPhysColumn P ν s) :=
    isCentrallyEven_smul (P.gaugeFactor ν) (isCentrallyEven_jscale (clockA ν s) hV_ev)
  refine ⟨hcan_mem, hcan_zc, hcan_ev, ?_⟩
  have hnrm : xNorm (ν ^ (-2 : ℝ)) m (canonicalPhysColumn P ν s) ≤ ENNReal.ofReal M_can := by
    have hsm : xNorm (ν ^ (-2 : ℝ)) m (canonicalPhysColumn P ν s) =
        ENNReal.ofReal ‖P.gaugeFactor ν‖ *
          xNorm (ν ^ (-2 : ℝ)) m (Jscale (clockA ν s) (canonicalPeriodized P ν θ_s)) := by
      unfold xNorm canonicalPhysColumn
      change eLpNorm (P.gaugeFactor ν • Jscale (clockA ν s) (canonicalPeriodized P ν θ_s)) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) = _
      rw [eLpNorm_const_smul, ofReal_norm]
    have hrpow : (clockA ν s) ^ ((m - 3) / 2) ≤ (clockA ν S) ^ ((m - 3) / 2) :=
      Real.rpow_le_rpow ha0.le ha_le (by linarith)
    calc xNorm (ν ^ (-2 : ℝ)) m (canonicalPhysColumn P ν s)
        ≤ ENNReal.ofReal ‖P.gaugeFactor ν‖ *
            (ENNReal.ofReal ((clockA ν s) ^ ((m - 3) / 2)) * ENNReal.ofReal C_ν) := by
          rw [hsm]
          exact mul_le_mul_of_nonneg_left
            (hJ_bd.trans (mul_le_mul_of_nonneg_left hV_bd zero_le)) zero_le
      _ ≤ ENNReal.ofReal ‖P.gaugeFactor ν‖ *
            (ENNReal.ofReal ((clockA ν S) ^ ((m - 3) / 2)) * ENNReal.ofReal C_ν) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hrpow) zero_le) zero_le
      _ = ENNReal.ofReal M_can := by
          dsimp only [M_can]
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _),
            ← ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnrm
  rwa [ENNReal.toReal_ofReal hM_can0] at htr

private lemma exists_horizon_suppliers {m ν : ℝ} (hm : 8 < m) (hm1 : 1 ≤ m)
    [Fact (0 < ν ^ (-2 : ℝ))]
    (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (hB : Exist.FiniteHorizonTrainBounds tr m) :
    ∃ (_Pn : ∀ n : ℕ, UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPathOn
        (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr (Nat.cast_nonneg n))
      (H : UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatStripSupplier
        (c := ν ^ (-2 : ℝ)) (m := m) hm1),
      Exist.ScaledHeatWeak hm1 ν H := by
  have hReg : Exist.Regime ν (ν ^ (-2 : ℝ)) m := ⟨hν0, hν1, rfl, hm⟩
  have hP : ∀ n : ℕ, Nonempty
      (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualTrainFluxPathOn
        (c := ν ^ (-2 : ℝ)) (m := m) (ν := ν) hm1 tr (Nat.cast_nonneg n)) :=
    fun n => Exist.fluxPathExistsAll ν (ν ^ (-2 : ℝ)) m hm1 tr hReg hB n (Nat.cast_nonneg n)
  obtain ⟨H, hH⟩ := Exist.scaleSupplier ν (ν ^ (-2 : ℝ)) m hReg.one_le_c hm1 hν0 hν1
    (Exist.unitHeatWeakActual (ν ^ (-2 : ℝ)) m hReg.one_le_c hm1)
  exact ⟨fun n => Classical.choice (hP n), H, hH⟩

/-! ### 4.4 Main proofs of `CTLongComparison`, `CTCompactComparison`, and `ctDuhamelTransfer` -/

private theorem ctLongComparison_of (hBranch : CTCanonicalBranchProps)
    (hRes : CTCanonicalResidual) : CTLongComparison := by
  intro P hP m hm
  have hm1 : 1 ≤ m := by linarith
  obtain ⟨ν_tb, hν_tb_pos, hTB⟩ := trainBoundsSmall_uncond m hm
  obtain ⟨b₀_res, _, hRes_b⟩ := hRes P hP m hm
  obtain ⟨b₀_fc, hFC_b⟩ := fullClockLongForward P hP m hm
  refine ⟨max 1 (max b₀_res b₀_fc), fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hb
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hb_res : b₀_res ≤ b := (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  have hb_fc : b₀_fc ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  obtain ⟨C_res, a₀, ν_res, hC_res, ha₀, hν_res, hRes_long⟩ := (hRes_b b hb_res).1
  obtain ⟨C_fc, ν_fc, hν_fc, hFC⟩ := hFC_b b hb_fc
  let C_fc' : ℝ := max C_fc 0
  have hC_fc'0 : 0 ≤ C_fc' := le_max_right _ _
  let K_a : ℝ := max 1 a₀⁻¹
  have hK_a0 : 0 ≤ K_a := le_trans zero_le_one (le_max_left _ _)
  let C_out : ℝ := 2 * C_fc' * C_res * K_a
  let ν₀ : ℝ := min (nuUniq m hm) (min ν_tb (min ν_res (min ν_fc (2 * b)⁻¹)))
  have hν₀_pos : 0 < ν₀ :=
    lt_min (nuUniq_pos m hm)
      (lt_min hν_tb_pos (lt_min hν_res (lt_min hν_fc (inv_pos.2 (by positivity)))))
  refine ⟨C_out, a₀, ν₀, ha₀, hν₀_pos, fun ν hν tr hbuc => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_u : ν ∈ Ioc 0 (nuUniq m hm) := ⟨hν0, hν.2.trans (min_le_left _ _)⟩
  have hν1 : ν ≤ 1 := hν_u.2.trans (nuUniq_le_one m hm)
  have hν_tb_le : ν ≤ ν_tb := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_res_le : ν ≤ ν_res :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_fc_le : ν ≤ ν_fc :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hν_2b : ν ≤ (2 * b)⁻¹ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hb_inv : b ≤ ν⁻¹ :=
    (le_inv_comm₀ hν0 hb0).1 (hν_2b.trans (inv_anti₀ hb0 (by linarith)))
  have hν3_b : ν ^ 3 ≤ b := (pow_le_one₀ hν0.le hν1).trans hb1
  have hReg : Exist.Regime ν (ν ^ (-2 : ℝ)) m := ⟨hν0, hν1, rfl, hm⟩
  have : Fact (0 < ν ^ (-2 : ℝ)) := ⟨hReg.pos_c⟩
  have : CompleteSpace (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := ν ^ (-2 : ℝ)) (m := m) hm1) :=
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualVorticityCompleteSpace
      (c := ν ^ (-2 : ℝ)) (m := m) hm1
  obtain ⟨hprep_mem, hprep_zc, _⟩ := (hBranch P hP m hm).1 ν ⟨hν0, hν1⟩
  obtain ⟨hFE, hFC_est⟩ := hFC ν ⟨hν0, hν_fc_le⟩ tr hbuc
  refine ⟨hFE 0 le_rfl (preparedDatum P ν) hprep_mem hprep_zc, fun w u hw θ hθb hθν => ?_⟩
  have hθ0 : 0 < θ := lt_of_lt_of_le hb0 hθb
  let S : ℝ := coreEnd ν b
  have hS_eq : clockAge ν b = S := clockAge_eq_coreEnd hν0 hb0
  have hS0 : 0 ≤ S := by rw [← hS_eq]; exact clockAge_nonneg hν0 hb0 hb_inv
  let N₀ : ℕ := ⌈S⌉₊
  have hSN : S ≤ (N₀ : ℝ) := Nat.le_ceil S
  obtain ⟨Pn, H, hH⟩ := exists_horizon_suppliers hm hm1 hν0 hν1 tr (hTB ν hν0 hν_tb_le tr hbuc)
  obtain ⟨M_can, hM_can0, hcan_win0⟩ :=
    canonicalPhysColumn_window_props hBranch P hP hm ⟨hν0, hν1⟩ hb0 hb_inv hν3_b
  have hcan_win : ∀ s' ∈ Icc (0 : ℝ) S,
      MemLp (canonicalPhysColumn P ν s') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s') ∧
      (xNorm (ν ^ (-2 : ℝ)) m (canonicalPhysColumn P ν s')).toReal ≤ M_can := by
    intro s' hs'
    have h0 := hcan_win0 s' (by rwa [hS_eq])
    exact ⟨h0.1, h0.2.1, h0.2.2.2⟩
  obtain ⟨u_can, f_res, hf_props, hcan_wk0, hf_bd⟩ := hRes_long ν ⟨hν0, hν_res_le⟩ tr hbuc
  have hcan0_eq : canonicalPhysColumn P ν 0 = preparedDatum P ν :=
    canonicalPhysColumn_zero_eq_preparedDatum P hν0
  have hcan_wk : ∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s' ∈ Icc (0 : ℝ) S,
      IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν s') (u_can s') s' φ)
        (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntervalIntegrable (fun τ =>
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume 0 s' ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν s' x * (φ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν 0 x * (φ x : ℂ)) +
        ∫ τ in (0 : ℝ)..s',
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) := by
    intro φ hφ s' hs'
    rw [hcan0_eq]
    exact hcan_wk0 φ hφ s' hs'
  obtain ⟨F_re, F_im, hFre_cont, hFim_cont, hF_lift⟩ :=
    lift_fres_contOn (c := ν ^ (-2 : ℝ)) (m := m) hm1
      (fun s' hs' => (hf_props s' hs').2.1)
      (fun s' hs' => (hf_props s' hs').2.2.1)
      (fun s' hs' => (hf_props s' hs').2.2.2.2)
  obtain ⟨D, hD⟩ : ∃ D, D = Exist.horizonData hm1 (Pn N₀) H := ⟨_, rfl⟩
  obtain ⟨Y_re, hYre⟩ : ∃ Y : ℝ →
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1,
      ∀ s', Y s' = ∫ τ in (0 : ℝ)..s', D.evolution s' τ (F_re τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Y_im, hYim⟩ : ∃ Y : ℝ →
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1,
      ∀ s', Y s' = ∫ τ in (0 : ℝ)..s', D.evolution s' τ (F_im τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨hJoint_re, _, _⟩ :=
    inhom_real_volterra_weak hm1 hReg tr N₀ le_rfl hS0 hSN Pn H hH hFre_cont hD hYre
  obtain ⟨hJoint_im, _, _⟩ :=
    inhom_real_volterra_weak hm1 hReg tr N₀ le_rfl hS0 hSN Pn H hH hFim_cont hD hYim
  have hinit0 : (fun x => w 0 x - canonicalPhysColumn P ν 0 x) =ᵐ[volume.restrict
      (B0579.cell (ν ^ (-2 : ℝ)))] 0 := by
    rw [hcan0_eq]
    filter_upwards [hw.initial] with x hx
    simp [hx]
  have hw_hom0 := isLinearisedFlow_zero_of_ae (ν := ν) (c := ν ^ (-2 : ℝ)) (m := m)
    (t₀ := 0) (tr := tr) hinit0
  have hduh := inhom_duhamel_eq_ae hm hm1 hν_u tr hbuc N₀ le_rfl hS0 hSN hM_can0 Pn H hH
    hprep_zc hw hcan_win (fun s' hs' => (hf_props s' hs').1) hcan_wk hFre_cont hFim_cont
    (fun s' hs' => (hF_lift s' hs').1) hw_hom0 hD hYre hYim
  let s : ℝ := clockAge ν θ
  have hs0 : 0 ≤ s := clockAge_nonneg hν0 hθ0 hθν
  have hsS : s ≤ S := by rw [← hS_eq]; exact clockAge_anti hν0 hb0 hθb
  let a_s : ℝ := (ν * θ)⁻¹
  have ha_s_eq : clockA ν s = a_s := clockA_clockAge hν0 hθ0
  have ha_s1 : 1 ≤ a_s := by
    rw [← ha_s_eq]; exact one_le_clockA hν0.le hs0
  have ha_s0 : 0 < a_s := lt_of_lt_of_le one_pos ha_s1
  let d_s : ℝ := dOfTheta ν θ
  have hd_s1 : 1 ≤ d_s := one_le_dOfTheta hν0 (hν3_b.trans hθb)
  have hd_s0 : 0 < d_s := lt_of_lt_of_le one_pos hd_s1
  have hdc_s : d_s * Real.sqrt a_s = ν ^ (-2 : ℝ) := by
    have h1 := dOfTheta_eq_cellLen (s := s) hν0 (by rw [ha_s_eq]; exact ha_s0)
    rw [clockTheta_clockAge hν0 hθ0, ha_s_eq] at h1
    change d_s = cellLen (ν ^ (-2 : ℝ)) a_s at h1
    rw [h1]; unfold cellLen; exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha_s0).ne'
  have hgf_pos : 0 < ‖P.gaugeFactor ν‖ := norm_pos_iff.2 (gaugeFactor_ne_zero P hν0)
  let w_θ : ℝ := Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re
  have hw_θ_pos : 0 < w_θ := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hθ0 _)
  obtain ⟨J_θ, hJ_θ⟩ : ∃ J,
      J = jscaleInvActualCLM (c := ν ^ (-2 : ℝ)) (m := m) hm1 ha_s1 hd_s0 hdc_s := ⟨_, rfl⟩
  have h_part : ∀ (F Y : ℝ →
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
          (c := ν ^ (-2 : ℝ)) (m := m) hm1),
      ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (F p.2))
        {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S} →
      (∀ s', Y s' = ∫ τ in (0 : ℝ)..s', D.evolution s' τ (F τ)) →
      (∀ τ ∈ Icc (0 : ℝ) S, ∀ a' d' : ℝ, 0 < a' → 0 < d' →
        d' * Real.sqrt a' = ν ^ (-2 : ℝ) →
          xNorm d' m (JscaleInv a' (Exist.cplx (Exist.vortFn hm1 (F τ)))) ≤
            xNorm d' m (JscaleInv a' (f_res τ))) →
      w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y s)‖) ≤
        C_fc' * C_res * K_a * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3)) := by
    intro F Y hJoint hY hF_nrm
    have hslice_cont : ContinuousOn (fun τ => D.evolution s τ (F τ)) (Icc 0 s) :=
      continuousOn_slice_of_joint hJoint hsS
    have hcomm : J_θ (Y s) = ∫ τ in (0 : ℝ)..s, J_θ (D.evolution s τ (F τ)) := by
      rw [hY s]
      exact (J_θ.intervalIntegral_comp_comm
        (hslice_cont.intervalIntegrable_of_Icc (μ := volume) hs0)).symm
    have hnrm_int : ‖J_θ (Y s)‖ ≤ ∫ τ in (0 : ℝ)..s, ‖J_θ (D.evolution s τ (F τ))‖ := by
      rw [hcomm]
      exact intervalIntegral.norm_integral_le_integral_norm hs0
    have hcov : ∫ τ in (0 : ℝ)..s, ‖J_θ (D.evolution s τ (F τ))‖ =
        ∫ u in θ..ν⁻¹, ‖J_θ (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
          (clockA ν (clockAge ν u)) ^ 2 := by
      have h0 := integral_clockAge_cov hν0 hθ0 hθν (fun τ => ‖J_θ (D.evolution s τ (F τ))‖)
      rwa [clockAge_inv hν0] at h0
    let lhs_u : ℝ → ℝ := fun u =>
      w_θ * ‖P.gaugeFactor ν‖⁻¹ *
        (‖J_θ (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ * (clockA ν (clockAge ν u)) ^ 2)
    have hmaps : ∀ u ∈ Icc θ ν⁻¹, 0 ≤ clockAge ν u ∧ clockAge ν u ≤ s ∧ s ≤ S :=
      fun u hu => ⟨clockAge_nonneg hν0 (lt_of_lt_of_le hθ0 hu.1) hu.2,
        clockAge_anti hν0 hθ0 hu.1, hsS⟩
    have hc_clockA2 : ContinuousOn (fun u => (clockA ν (clockAge ν u)) ^ 2) (Icc θ ν⁻¹) := by
      unfold clockA
      exact ((continuousOn_const.add (continuousOn_const.mul
        (continuousOn_clockAge hν0 hθ0))).pow 2)
    have hlhs_cont : ContinuousOn lhs_u (Icc θ ν⁻¹) :=
      continuousOn_const.mul ((continuousOn_norm_clm_clock J_θ s hJoint
        (continuousOn_clockAge hν0 hθ0) hmaps).mul hc_clockA2)
    have hrhs_cont : ContinuousOn (fun u => C_fc' * C_res * resTerm ν a₀ u) (Icc θ ν⁻¹) :=
      continuousOn_const.mul (continuousOn_resTerm hθ0)
    have hpt : ∀ u ∈ Icc θ ν⁻¹, lhs_u u ≤ C_fc' * C_res * resTerm ν a₀ u := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hθ0 hu.1
      have hub : b ≤ u := hθb.trans hu.1
      let τ := clockAge ν u
      have hτ0 : 0 ≤ τ := clockAge_nonneg hν0 hu0 hu.2
      have hτs : τ ≤ s := clockAge_anti hν0 hθ0 hu.1
      have hτS : τ ≤ S := hτs.trans hsS
      have hev_eq : Exist.horizonEvolution hm1 Pn H s τ (F τ) = D.evolution s τ (F τ) := by
        rw [hD]
        exact congrArg (fun L => L (F τ))
          (Exist.horizonEvolution_eq hm1 Exist.horizonLocality Pn H hτ0 hτs (hsS.trans hSN))
      have hfl_τ := horizon_real_flow hm1 hReg tr Pn H hH hτ0 (F τ)
      obtain ⟨hFτ_mem, hFτ_zc⟩ := Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (F τ)
      have hθ_s_b : b ≤ clockTheta ν s := by rw [clockTheta_clockAge hν0 hθ0]; exact hθb
      have hfc_u := hFC_est τ s hτ0 hτs hθ_s_b _ hFτ_mem hFτ_zc _ _ hfl_τ
      have hd_s_eq : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) = d_s := by
        rw [← dOfTheta_eq_cellLen hν0 (by rw [ha_s_eq]; exact ha_s0),
          clockTheta_clockAge hν0 hθ0]
      have ha_τ_eq : clockA ν τ = (ν * u)⁻¹ := clockA_clockAge hν0 hu0
      have ha_τ0 : 0 < clockA ν τ := by rw [ha_τ_eq]; positivity
      have hd_u_eq : cellLen (ν ^ (-2 : ℝ)) (clockA ν τ) = dOfTheta ν u := by
        rw [← dOfTheta_eq_cellLen hν0 ha_τ0, clockTheta_clockAge hν0 hu0]
      have hd_u0 : 0 < dOfTheta ν u := lt_of_lt_of_le one_pos (one_le_dOfTheta hν0 (hν3_b.trans hub))
      have hdc_u : dOfTheta ν u * Real.sqrt (clockA ν τ) = ν ^ (-2 : ℝ) := by
        rw [← hd_u_eq]; unfold cellLen; exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha_τ0).ne'
      rw [hev_eq, hd_s_eq, ha_s_eq, hd_u_eq, clockTheta_clockAge hν0 hu0,
        clockTheta_clockAge hν0 hθ0,
        ← ofReal_norm_jscaleInvActualCLM hm1 ha_s1 hd_s0 hdc_s (D.evolution s τ (F τ)),
        ← hJ_θ] at hfc_u
      have hfc_u' : ENNReal.ofReal ‖J_θ (D.evolution s τ (F τ))‖ ≤
          ENNReal.ofReal (C_fc' * Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re) *
            xNorm (dOfTheta ν u) m (JscaleInv (clockA ν τ) (f_res τ)) := by
        refine hfc_u.trans (mul_le_mul ?_ (hF_nrm τ ⟨hτ0, hτS⟩ (clockA ν τ) (dOfTheta ν u)
          ha_τ0 hd_u0 hdc_u) zero_le zero_le)
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C_fc 0) (Real.exp_nonneg _))
          (Real.rpow_nonneg (div_nonneg hu0.le hθ0.le) _)
      let mult : ℝ := w_θ * ‖P.gaugeFactor ν‖⁻¹ * (clockA ν τ) ^ 2
      have hmult0 : 0 ≤ mult := by dsimp [mult]; positivity
      have hmul_enn := mul_le_mul_of_nonneg_left hfc_u' (zero_le : 0 ≤ ENNReal.ofReal mult)
      have hlhs_enn : ENNReal.ofReal mult * ENNReal.ofReal ‖J_θ (D.evolution s τ (F τ))‖ =
          ENNReal.ofReal (lhs_u u) := by
        rw [← ENNReal.ofReal_mul hmult0]
        dsimp only [mult, lhs_u, τ]
        congr 1; ring
      have hexp_id : w_θ * (Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re) =
          Real.exp (P.eigenvalue.re * u) * u ^ P.kappa.re := by
        dsimp only [w_θ]
        have he1 : Real.exp (P.eigenvalue.re * θ) * Real.exp (P.eigenvalue.re * (u - θ)) =
            Real.exp (P.eigenvalue.re * u) := by
          rw [← Real.exp_add]; congr 1; ring
        have he2 : θ ^ P.kappa.re * (u / θ) ^ P.kappa.re = u ^ P.kappa.re := by
          rw [← Real.mul_rpow hθ0.le (div_nonneg hu0.le hθ0.le), mul_div_cancel₀ u hθ0.ne']
        calc Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re *
              (Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re)
            = (Real.exp (P.eigenvalue.re * θ) * Real.exp (P.eigenvalue.re * (u - θ))) *
                (θ ^ P.kappa.re * (u / θ) ^ P.kappa.re) := by ring
          _ = Real.exp (P.eigenvalue.re * u) * u ^ P.kappa.re := by rw [he1, he2]
      have hrhs_alg : mult * (C_fc' * Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re) =
          C_fc' * (Real.exp (P.eigenvalue.re * u) * u ^ P.kappa.re *
            (clockA ν τ) ^ 2 / ‖P.gaugeFactor ν‖) := by
        have h1 : mult * (C_fc' * Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re) =
            C_fc' * (w_θ * (Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re)) *
              (clockA ν τ) ^ 2 * ‖P.gaugeFactor ν‖⁻¹ := by
          dsimp only [mult]; ring
        rw [h1, hexp_id, div_eq_mul_inv _ ‖P.gaugeFactor ν‖]
        ring
      have hrhs_enn : ENNReal.ofReal mult *
          (ENNReal.ofReal (C_fc' * Real.exp (P.eigenvalue.re * (u - θ)) * (u / θ) ^ P.kappa.re) *
            xNorm (dOfTheta ν u) m (JscaleInv (clockA ν τ) (f_res τ))) ≤
          ENNReal.ofReal (C_fc' * C_res * resTerm ν a₀ u) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hmult0, hrhs_alg,
          ENNReal.ofReal_mul hC_fc'0, mul_assoc]
        have hres_u := hf_bd u ⟨hub, hu.2⟩
        change _ ≤ ENNReal.ofReal (C_res * resTerm ν a₀ u) at hres_u
        refine (mul_le_mul_of_nonneg_left hres_u zero_le).trans ?_
        exact le_of_eq (by rw [← ENNReal.ofReal_mul hC_fc'0]; congr 1; ring)
      rw [hlhs_enn] at hmul_enn
      have hres0 : 0 ≤ resTerm ν a₀ u := by
        unfold resTerm
        exact add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hu0.le _)) (by positivity)
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hmul_enn.trans hrhs_enn)
    have hint_mono := intervalIntegral.integral_mono_on hθν
      (hlhs_cont.intervalIntegrable_of_Icc (μ := volume) hθν)
      (hrhs_cont.intervalIntegrable_of_Icc (μ := volume) hθν) hpt
    have hlhs_pull : ∫ u in θ..ν⁻¹, lhs_u u =
        w_θ * ‖P.gaugeFactor ν‖⁻¹ *
          ∫ u in θ..ν⁻¹, ‖J_θ (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
            (clockA ν (clockAge ν u)) ^ 2 := by
      dsimp only [lhs_u]
      exact intervalIntegral.integral_const_mul _ _
    have hrhs_pull : ∫ u in θ..ν⁻¹, C_fc' * C_res * resTerm ν a₀ u =
        C_fc' * C_res * ∫ u in θ..ν⁻¹, resTerm ν a₀ u :=
      intervalIntegral.integral_const_mul _ _
    rw [hlhs_pull, hrhs_pull] at hint_mono
    have hstep1 : w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y s)‖) ≤
        C_fc' * C_res * ((ν ^ 3) ^ 2 / θ + (ν ^ 6 / a₀) * Real.exp (-a₀ * θ / ν ^ 3)) := by
      calc w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y s)‖)
          = (w_θ * ‖P.gaugeFactor ν‖⁻¹) * ‖J_θ (Y s)‖ := by ring
        _ ≤ (w_θ * ‖P.gaugeFactor ν‖⁻¹) *
              ∫ u in θ..ν⁻¹, ‖J_θ (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
                (clockA ν (clockAge ν u)) ^ 2 := by
            rw [← hcov]
            exact mul_le_mul_of_nonneg_left hnrm_int (by positivity)
        _ ≤ C_fc' * C_res * ∫ u in θ..ν⁻¹, resTerm ν a₀ u := hint_mono
        _ ≤ C_fc' * C_res * ((ν ^ 3) ^ 2 / θ + (ν ^ 6 / a₀) * Real.exp (-a₀ * θ / ν ^ 3)) :=
            mul_le_mul_of_nonneg_left (integral_resTerm_le hν0 ha₀ hθ0 hθν) (by positivity)
    have hstep2 : (ν ^ 3) ^ 2 / θ + (ν ^ 6 / a₀) * Real.exp (-a₀ * θ / ν ^ 3) ≤
        K_a * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3)) := by
      have hν6 : ν ^ 6 ≤ 1 := pow_le_one₀ hν0.le hν1
      have hexp_le : (ν ^ 6 / a₀) * Real.exp (-a₀ * θ / ν ^ 3) ≤
          K_a * Real.exp (-a₀ * θ / ν ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        calc ν ^ 6 / a₀ ≤ 1 / a₀ := div_le_div_of_nonneg_right hν6 ha₀.le
          _ = a₀⁻¹ := one_div a₀
          _ ≤ K_a := le_max_right 1 a₀⁻¹
      have hsq_le : (ν ^ 3) ^ 2 / θ ≤ K_a * ((ν ^ 3) ^ 2 / θ) := by
        have h1K : 1 ≤ K_a := le_max_left 1 a₀⁻¹
        exact le_mul_of_one_le_left (by positivity) h1K
      have hν_nonneg : 0 ≤ K_a * ν := mul_nonneg hK_a0 hν0.le
      linarith only [hexp_le, hsq_le, hν_nonneg]
    calc w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y s)‖)
        ≤ C_fc' * C_res * (K_a * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3))) :=
          hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by positivity))
      _ = C_fc' * C_res * K_a * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3)) := by ring
  have h_re := h_part F_re Y_re hJoint_re hYre fun τ hτ a' d' ha' hd' hdc' =>
    xNorm_jscaleInv_vortFn_le_of_re hm1 ha' hd' hdc' (F_re τ) (hF_lift τ hτ).2.1
  have h_im := h_part F_im Y_im hJoint_im hYim fun τ hτ a' d' ha' hd' hdc' =>
    xNorm_jscaleInv_vortFn_le_of_im hm1 ha' hd' hdc' (F_im τ) (hF_lift τ hτ).2.2
  have hae_s : (fun x => w s x - canonicalPhysColumn P ν s x) =ᵐ[volume.restrict
      (B0579.cell (ν ^ (-2 : ℝ)))]
      fun x => -(Exist.cplx (Exist.vortFn hm1 (Y_re s)) x +
        Complex.I * Exist.cplx (Exist.vortFn hm1 (Y_im s)) x) := by
    filter_upwards [hduh s ⟨hs0, hsS⟩] with x hx
    simpa using hx
  have hx_diff := xNorm_heatDiff_inhom_le hm1 ha_s1 hd_s0 hdc_s (P.gaugeFactor ν)⁻¹
    (Y_re s) (Y_im s) hae_s
  rw [heatColumn_sub_canonicalPeriodized_eq P hν0 hθ0 w]
  change ENNReal.ofReal w_θ * xNorm d_s m _ ≤ _
  rw [norm_inv, ← hJ_θ] at hx_diff
  calc ENNReal.ofReal w_θ *
        xNorm d_s m (fun y => (P.gaugeFactor ν)⁻¹ *
          JscaleInv a_s (fun x => w s x - canonicalPhysColumn P ν s x) y)
      ≤ ENNReal.ofReal w_θ *
          (ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ *
            (ENNReal.ofReal ‖J_θ (Y_re s)‖ + ENNReal.ofReal ‖J_θ (Y_im s)‖)) :=
        mul_le_mul_of_nonneg_left hx_diff zero_le
    _ = ENNReal.ofReal (w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y_re s)‖) +
          w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y_im s)‖)) := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ← ENNReal.ofReal_mul (inv_nonneg.2 hgf_pos.le),
          ← ENNReal.ofReal_mul hw_θ_pos.le]
        congr 1; ring
    _ ≤ ENNReal.ofReal (C_out * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y_re s)‖) +
              w_θ * (‖P.gaugeFactor ν‖⁻¹ * ‖J_θ (Y_im s)‖)
            ≤ C_fc' * C_res * K_a * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3)) +
                C_fc' * C_res * K_a * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3)) :=
              add_le_add h_re h_im
          _ = C_out * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₀ * θ / ν ^ 3)) := by
              dsimp only [C_out]; ring

private theorem ctCompactComparison_of (hBranch : CTCanonicalBranchProps)
    (hRes : CTCanonicalResidual) (hLong : CTLongComparison)
    (hEmb : CTEmbeddings) (hKin : CTKineticImpulse) (hMom : CTPartialMoment) :
    CTCompactComparison := by
  intro P hP m hm
  have hm1 : 1 ≤ m := by linarith
  have hm_gt1 : 1 < m := by linarith
  have hm3 : 3 < m := by linarith
  obtain ⟨ν_tb, hν_tb_pos, hTB⟩ := trainBoundsSmall_uncond m hm
  obtain ⟨C_emb, hEmb_d⟩ := hEmb m hm
  let C_emb' : ℝ := max C_emb 0
  have hC_emb'0 : 0 ≤ C_emb' := le_max_right _ _
  obtain ⟨b₀_res, _, hRes_b⟩ := hRes P hP m hm
  obtain ⟨b₀_long, hLong_b⟩ := hLong P hP m hm
  obtain ⟨b₀_kin, hKin_b⟩ := hKin P hP m hm
  obtain ⟨b₀_mom, hMom_b⟩ := hMom P hP m hm
  obtain ⟨b₀_fc, hFC_b⟩ := fullClockLongForward P hP m hm
  refine ⟨max 1 (max b₀_res (max b₀_long (max b₀_kin (max b₀_mom b₀_fc)))),
    fun b hb r hr hrb ε hε => ?_⟩
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hb
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hb_r1 := (le_max_right _ _).trans hb
  have hb_res : b₀_res ≤ b := (le_max_left _ _).trans hb_r1
  have hb_r2 := (le_max_right _ _).trans hb_r1
  have hb_long : b₀_long ≤ b := (le_max_left _ _).trans hb_r2
  have hb_r3 := (le_max_right _ _).trans hb_r2
  have hb_kin : b₀_kin ≤ b := (le_max_left _ _).trans hb_r3
  have hb_r4 := (le_max_right _ _).trans hb_r3
  have hb_mom : b₀_mom ≤ b := (le_max_left _ _).trans hb_r4
  have hb_fc : b₀_fc ≤ b := (le_max_right _ _).trans hb_r4
  obtain ⟨C_long, a₁, ν_long, ha₁, hν_long, hLong_est⟩ := hLong_b b hb_long
  obtain ⟨C_kin, ν_kin, hν_kin, hKin_est⟩ := hKin_b b hb_kin
  obtain ⟨C_mom, ν_mom, hν_mom, hMom_est⟩ := hMom_b b hb_mom
  obtain ⟨_, ν_fc, hν_fc, hFC_est⟩ := hFC_b b hb_fc
  obtain ⟨C_r, a₀, ν_r, hC_r, ha₀, hν_r, hRes_comp⟩ := (hRes_b b hb_res).2 r hr hrb
  let C_long' : ℝ := max C_long 0
  let C_kin' : ℝ := max C_kin 0
  let C_mom' : ℝ := max C_mom 0
  have hC_long'0 : 0 ≤ C_long' := le_max_right _ _
  have hC_kin'0 : 0 ≤ C_kin' := le_max_right _ _
  have hC_mom'0 : 0 ≤ C_mom' := le_max_right _ _
  let w_b : ℝ := Real.exp (P.eigenvalue.re * b) * b ^ P.kappa.re
  have hw_b_pos : 0 < w_b := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hb0 _)
  have hlog_br : 0 ≤ Real.log (b / r) := Real.log_nonneg ((one_le_div hr).2 hrb)
  let M_fac : ℝ := max (C_kin' * (b / r)) (1 + C_mom' * b * Real.log (b / r))
  have hM_fac0 : 0 ≤ M_fac := le_trans (by positivity) (le_max_left _ _)
  let K_hom : ℝ := M_fac * C_emb' * w_b⁻¹ * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹)
  let K_inh : ℝ := 2 * M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹)
  let K_tot : ℝ := K_hom + K_inh
  have hK_hom0 : 0 ≤ K_hom := by
    dsimp [K_hom]
    positivity
  have hK_inh0 : 0 ≤ K_inh := by
    dsimp [K_inh]
    positivity
  have hK_tot0 : 0 ≤ K_tot := add_nonneg hK_hom0 hK_inh0
  let ν_base : ℝ := min (nuUniq m hm) (min ν_tb (min ν_long (min ν_kin
    (min ν_mom (min ν_fc (min ν_r (min (2 * b)⁻¹ (min 1 r))))))))
  have hν_base_pos : 0 < ν_base :=
    lt_min (nuUniq_pos m hm) (lt_min hν_tb_pos (lt_min hν_long (lt_min hν_kin
      (lt_min hν_mom (lt_min hν_fc (lt_min hν_r
        (lt_min (inv_pos.2 (by positivity)) (lt_min one_pos hr))))))))
  let ν_final : ℝ := min ν_base (ε / (K_tot + 1))
  have hν_final_pos : 0 < ν_final := lt_min hν_base_pos (div_pos hε (by positivity))
  have hnhds : Ioo 0 ν_final ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨Iio ν_final, Iio_mem_nhds hν_final_pos, fun x hx => ⟨hx.2, hx.1⟩⟩
  refine Filter.eventually_of_mem hnhds fun ν hν_fin tr hbuc w u hw θ hθ => ?_
  have hν0 : 0 < ν := hν_fin.1
  have hν_lt_fin : ν < ν_final := hν_fin.2
  have hν_le_base : ν ≤ ν_base := hν_lt_fin.le.trans (min_le_left _ _)
  have hν_lt_eps : ν < ε / (K_tot + 1) := hν_lt_fin.trans_le (min_le_right _ _)
  have hν_u : ν ∈ Ioc 0 (nuUniq m hm) := ⟨hν0, hν_le_base.trans (min_le_left _ _)⟩
  have hν1 : ν ≤ 1 := hν_u.2.trans (nuUniq_le_one m hm)
  have hν_r1 := hν_le_base.trans (min_le_right _ _)
  have hν_tb_le : ν ≤ ν_tb := hν_r1.trans (min_le_left _ _)
  have hν_r2 := hν_r1.trans (min_le_right _ _)
  have hν_long_le : ν ≤ ν_long := hν_r2.trans (min_le_left _ _)
  have hν_r3 := hν_r2.trans (min_le_right _ _)
  have hν_kin_le : ν ≤ ν_kin := hν_r3.trans (min_le_left _ _)
  have hν_r4 := hν_r3.trans (min_le_right _ _)
  have hν_mom_le : ν ≤ ν_mom := hν_r4.trans (min_le_left _ _)
  have hν_r5 := hν_r4.trans (min_le_right _ _)
  have hν_fc_le : ν ≤ ν_fc := hν_r5.trans (min_le_left _ _)
  have hν_r6 := hν_r5.trans (min_le_right _ _)
  have hν_r_le : ν ≤ ν_r := hν_r6.trans (min_le_left _ _)
  have hν_r7 := hν_r6.trans (min_le_right _ _)
  have hν_2b : ν ≤ (2 * b)⁻¹ := hν_r7.trans (min_le_left _ _)
  have hν_le_r : ν ≤ r := (hν_r7.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hb_inv : b ≤ ν⁻¹ :=
    (le_inv_comm₀ hν0 hb0).1 (hν_2b.trans (inv_anti₀ hb0 (by linarith)))
  have hr_inv : r ≤ ν⁻¹ := hrb.trans hb_inv
  have hν3_le_ν : ν ^ 3 ≤ ν := by
    have h2 : ν ^ 2 ≤ 1 := pow_le_one₀ hν0.le hν1
    nlinarith only [hν0, h2]
  have hν6_le_ν : ν ^ 6 ≤ ν := by
    have h5 : ν ^ 5 ≤ 1 := pow_le_one₀ hν0.le hν1
    nlinarith only [hν0, h5]
  have hν3_r : ν ^ 3 ≤ r := hν3_le_ν.trans hν_le_r
  have hReg : Exist.Regime ν (ν ^ (-2 : ℝ)) m := ⟨hν0, hν1, rfl, hm⟩
  have : Fact (0 < ν ^ (-2 : ℝ)) := ⟨hReg.pos_c⟩
  have : CompleteSpace (UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
      (c := ν ^ (-2 : ℝ)) (m := m) hm1) :=
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualVorticityCompleteSpace
      (c := ν ^ (-2 : ℝ)) (m := m) hm1
  obtain ⟨hprep_mem, hprep_zc, hprep_ev⟩ := (hBranch P hP m hm).1 ν ⟨hν0, hν1⟩
  have hFE := (hFC_est ν ⟨hν0, hν_fc_le⟩ tr hbuc).1
  let t₀ : ℝ := coreEnd ν b
  have ht₀_eq : clockAge ν b = t₀ := clockAge_eq_coreEnd hν0 hb0
  have ht₀0 : 0 ≤ t₀ := by rw [← ht₀_eq]; exact clockAge_nonneg hν0 hb0 hb_inv
  let S : ℝ := clockAge ν r
  have htS : t₀ ≤ S := by rw [← ht₀_eq]; exact clockAge_anti hν0 hr hrb
  let N₀ : ℕ := ⌈S⌉₊
  have hSN : S ≤ (N₀ : ℝ) := Nat.le_ceil S
  obtain ⟨Pn, H, hH⟩ := exists_horizon_suppliers hm hm1 hν0 hν1 tr (hTB ν hν0 hν_tb_le tr hbuc)
  obtain ⟨M_can, hM_can0, hcan_win0⟩ :=
    canonicalPhysColumn_window_props hBranch P hP hm ⟨hν0, hν1⟩ hr hr_inv hν3_r
  have hcan_win : ∀ s' ∈ Icc t₀ S,
      MemLp (canonicalPhysColumn P ν s') 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s') ∧
      (xNorm (ν ^ (-2 : ℝ)) m (canonicalPhysColumn P ν s')).toReal ≤ M_can := by
    intro s' hs'
    have h0 := hcan_win0 s' ⟨ht₀0.trans hs'.1, hs'.2⟩
    exact ⟨h0.1, h0.2.1, h0.2.2.2⟩
  obtain ⟨u_can, f_res, hf_props, hcan_wk, hf_bd⟩ := hRes_comp ν ⟨hν0, hν_r_le⟩ tr hbuc
  -- Construct homogeneous flow at t₀ = clockAge ν b from symEven-regularized heat datum h_b
  let a_b : ℝ := (ν * b)⁻¹
  have ha_b_eq : clockA ν t₀ = a_b := by rw [← ht₀_eq]; exact clockA_clockAge hν0 hb0
  have ha_b1 : 1 ≤ a_b := by rw [← ha_b_eq]; exact one_le_clockA hν0.le ht₀0
  have ha_b0 : 0 < a_b := lt_of_lt_of_le one_pos ha_b1
  let d_b : ℝ := dOfTheta ν b
  have hd_b1 : 1 ≤ d_b := one_le_dOfTheta hν0 (hν3_r.trans hrb)
  have hd_b0 : 0 < d_b := lt_of_lt_of_le one_pos hd_b1
  have hdc_b : d_b * Real.sqrt a_b = ν ^ (-2 : ℝ) := by
    have h1 := dOfTheta_eq_cellLen (s := t₀) hν0 (by rw [ha_b_eq]; exact ha_b0)
    rw [ha_b_eq, ← ht₀_eq, clockTheta_clockAge hν0 hb0] at h1
    change d_b = cellLen (ν ^ (-2 : ℝ)) a_b at h1
    rw [h1]; unfold cellLen; exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha_b0).ne'
  let g₀ : ℝ × ℝ → ℂ := fun x => w t₀ x - canonicalPhysColumn P ν t₀ x
  let u_g₀ : ℝ × ℝ → Fin 2 → ℂ := fun x j => u t₀ x j - u_can t₀ x j
  have hg₀_mem : MemLp g₀ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    (hw.memX t₀ ht₀0).sub (hcan_win0 t₀ ⟨ht₀0, htS⟩).1
  have hg₀_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) g₀ := by
    have zw := ladFlowZeroCirc m hm_gt1 ν (ν ^ (-2 : ℝ)) tr 0 (preparedDatum P ν) w u
      hReg.one_le_c hprep_zc hw t₀ ht₀0
    have zc := (hcan_win0 t₀ ⟨ht₀0, htS⟩).2.1
    exact ⟨zw.1.sub zc.1, by
      change ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w t₀ x - canonicalPhysColumn P ν t₀ x) = 0
      rw [integral_sub zw.1 zc.1, zw.2, zc.2, sub_self]⟩
  have hg₀_bs : IsBiotSavart (ν ^ (-2 : ℝ)) g₀ u_g₀ :=
    ladBSSub m (ν ^ (-2 : ℝ)) (w t₀) (canonicalPhysColumn P ν t₀) (u t₀) (u_can t₀) hm_gt1
      (hw.memX t₀ ht₀0) (hcan_win0 t₀ ⟨ht₀0, htS⟩).1 (hw.biotSavart t₀ ht₀0)
      (hf_props t₀ ⟨le_rfl, htS⟩).1
  have hg₀_ev : (fun x => g₀ (-x)) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] g₀ := by
    have hw_ev := isLinearisedFlow_even_ae hm hν_u tr hbuc le_rfl hprep_mem hprep_zc
      (Eventually.of_forall hprep_ev) hw t₀ ht₀0
    have hcan_ev := (hcan_win0 t₀ ⟨ht₀0, htS⟩).2.2.1
    filter_upwards [hw_ev] with x hx
    dsimp only [g₀] at hx ⊢
    rw [hx, hcan_ev x]
  obtain ⟨hhb_mem, hhb_zc, hhb_ev, hhb_bs, hhb_nrm, hJb_ae⟩ :=
    symEven_jscaleInv_props hm_gt1 ha_b1 hd_b0 hdc_b hg₀_mem hg₀_zc hg₀_bs hg₀_ev
  let h_b : ℝ × ℝ → ℂ := symEven (JscaleInv a_b g₀)
  have hJb_mem : MemLp (Jscale a_b h_b) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
    memLp_congr_cellMeasure hdc_b (jscale_memLp_bound (by linarith) ha_b1 hd_b0 hhb_mem).1
  have hJb_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) (Jscale a_b h_b) :=
    hasZeroCirc_congr_c hdc_b (hasZeroCirc_jscale hm_gt1 ha_b1 hd_b0 hhb_mem hhb_zc)
  obtain ⟨w_hom, u_hom, hw_hom_hb⟩ := hFE t₀ ht₀0 (Jscale a_b h_b) hJb_mem hJb_zc
  have hw_hom : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₀ g₀ w_hom u_hom :=
    isLinearisedFlow_congr_initial_ae hw_hom_hb hJb_ae
  -- Lift residual f_res and apply inhomogeneous Duhamel identity on [t₀, S]
  obtain ⟨F_re, F_im, hFre_cont, hFim_cont, hF_lift⟩ :=
    lift_fres_contOn (c := ν ^ (-2 : ℝ)) (m := m) hm1
      (fun s' hs' => (hf_props s' hs').2.1)
      (fun s' hs' => (hf_props s' hs').2.2.1)
      (fun s' hs' => (hf_props s' hs').2.2.2.2)
  obtain ⟨D, hD⟩ : ∃ D, D = Exist.horizonData hm1 (Pn N₀) H := ⟨_, rfl⟩
  obtain ⟨Y_re, hYre⟩ : ∃ Y : ℝ →
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1,
      ∀ s', Y s' = ∫ τ in t₀..s', D.evolution s' τ (F_re τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Y_im, hYim⟩ : ∃ Y : ℝ →
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
        (c := ν ^ (-2 : ℝ)) (m := m) hm1,
      ∀ s', Y s' = ∫ τ in t₀..s', D.evolution s' τ (F_im τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨hJoint_re, _, _⟩ :=
    inhom_real_volterra_weak hm1 hReg tr N₀ ht₀0 htS hSN Pn H hH hFre_cont hD hYre
  obtain ⟨hJoint_im, _, _⟩ :=
    inhom_real_volterra_weak hm1 hReg tr N₀ ht₀0 htS hSN Pn H hH hFim_cont hD hYim
  have hduh := inhom_duhamel_eq_ae hm hm1 hν_u tr hbuc N₀ ht₀0 htS hSN hM_can0 Pn H hH
    hprep_zc hw hcan_win (fun s' hs' => (hf_props s' hs').1) hcan_wk hFre_cont hFim_cont
    (fun s' hs' => (hF_lift s' hs').1) hw_hom hD hYre hYim
  -- Evaluate at θ ∈ Icc r b (s = clockAge ν θ ∈ Icc t₀ S)
  have hθr : r ≤ θ := hθ.1
  have hθb : θ ≤ b := hθ.2
  have hθ0 : 0 < θ := lt_of_lt_of_le hr hθr
  let s : ℝ := clockAge ν θ
  have hts : t₀ ≤ s := by rw [← ht₀_eq]; exact clockAge_anti hν0 hθ0 hθb
  have hsS : s ≤ S := clockAge_anti hν0 hr hθr
  let a_s : ℝ := (ν * θ)⁻¹
  have ha_s_eq : clockA ν s = a_s := clockA_clockAge hν0 hθ0
  have ha_s1 : 1 ≤ a_s := by
    rw [← ha_s_eq]; exact one_le_clockA hν0.le (ht₀0.trans hts)
  have ha_s0 : 0 < a_s := lt_of_lt_of_le one_pos ha_s1
  let d_s : ℝ := dOfTheta ν θ
  have hd_s1 : 1 ≤ d_s := one_le_dOfTheta hν0 (hν3_r.trans hθr)
  have hd_s0 : 0 < d_s := lt_of_lt_of_le one_pos hd_s1
  have hdc_s : d_s * Real.sqrt a_s = ν ^ (-2 : ℝ) := by
    have h1 := dOfTheta_eq_cellLen (s := s) hν0 (by rw [ha_s_eq]; exact ha_s0)
    rw [clockTheta_clockAge hν0 hθ0, ha_s_eq] at h1
    change d_s = cellLen (ν ^ (-2 : ℝ)) a_s at h1
    rw [h1]; unfold cellLen; exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha_s0).ne'
  have hgf_pos : 0 < ‖P.gaugeFactor ν‖ := norm_pos_iff.2 (gaugeFactor_ne_zero P hν0)
  -- Part A: Homogeneous bounds at θ from h_b via CTEmbeddings, CTKineticImpulse, CTPartialMoment, hLong
  let Zh_hom : ℝ × ℝ → ℂ := JscaleInv a_s (w_hom s)
  have hEvol_hom : HeatEvolvesTo ν m tr b θ h_b Zh_hom := by
    refine ⟨w_hom, u_hom, ?_, rfl⟩
    rw [ht₀_eq]; exact hw_hom_hb
  have hemb_hb : ENNReal.ofReal ‖quadQ d_b h_b‖ + kinNorm d_b h_b ≤
      ENNReal.ofReal C_emb' * xNorm d_b m h_b := by
    rw [kinNorm_eq_of_isBiotSavart hd_b0 hhb_bs]
    exact (hEmb_d d_b hd_b1 h_b hhb_mem hhb_zc hhb_ev (velMov a_b u_g₀) hhb_bs).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C_emb 0)) zero_le)
  have hhb_kin_le : kinNorm d_b h_b ≤ ENNReal.ofReal C_emb' * xNorm d_b m h_b :=
    le_add_self.trans hemb_hb
  have hhb_quad_le : ENNReal.ofReal ‖quadQ d_b h_b‖ ≤ ENNReal.ofReal C_emb' * xNorm d_b m h_b :=
    le_self_add.trans hemb_hb
  have hlong_at_b := (hLong_est ν ⟨hν0, hν_long_le⟩ tr hbuc).2 w u hw b le_rfl hb_inv
  have hgf_xnorm_hb : ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * xNorm d_b m h_b =
      xNorm d_b m (heatColumn P ν w b - canonicalPeriodized P ν b) := by
    change ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * xNorm d_b m (symEven (JscaleInv a_b g₀)) = _
    rw [hhb_nrm, heatColumn_sub_canonicalPeriodized_eq P hν0 hb0 w]
    unfold xNorm
    have hpt : (fun y => (P.gaugeFactor ν)⁻¹ *
          JscaleInv (ν * b)⁻¹ (fun x => w (clockAge ν b) x - canonicalPhysColumn P ν (clockAge ν b) x) y) =
        (P.gaugeFactor ν)⁻¹ • JscaleInv a_b g₀ := by
      funext y; simp [ht₀_eq, a_b, g₀]
    rw [hpt, eLpNorm_const_smul, ← ofReal_norm, norm_inv]
  have hxnorm_b_le : xNorm d_b m (heatColumn P ν w b - canonicalPeriodized P ν b) ≤
      ENNReal.ofReal (w_b⁻¹ * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν) := by
    have h1 := mul_le_mul_of_nonneg_left hlong_at_b (zero_le : 0 ≤ ENNReal.ofReal w_b⁻¹)
    have hlhs : ENNReal.ofReal w_b⁻¹ *
        (ENNReal.ofReal w_b * xNorm d_b m (heatColumn P ν w b - canonicalPeriodized P ν b)) =
        xNorm d_b m (heatColumn P ν w b - canonicalPeriodized P ν b) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hw_b_pos.le),
        inv_mul_cancel₀ hw_b_pos.ne', ENNReal.ofReal_one, one_mul]
    rw [hlhs] at h1
    refine h1.trans ?_
    have hexp_b : Real.exp (-a₁ * b / ν ^ 3) ≤ (a₁ * b)⁻¹ * ν := by
      let z : ℝ := a₁ * b / ν ^ 3
      have hz : 0 < z := by dsimp [z]; positivity
      have hexp_z : z ≤ Real.exp z := by linarith only [Real.add_one_le_exp z]
      have hneg_z : Real.exp (-z) ≤ z⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ hz hexp_z
      have hz_inv : z⁻¹ = (a₁ * b)⁻¹ * ν ^ 3 := by
        dsimp only [z]
        have ha₁_ne : a₁ ≠ 0 := ha₁.ne'
        have hb_ne : b ≠ 0 := hb0.ne'
        have hν_ne : ν ≠ 0 := hν0.ne'
        field_simp
      calc Real.exp (-a₁ * b / ν ^ 3)
          = Real.exp (-z) := by congr 1; dsimp [z]; ring
        _ ≤ z⁻¹ := hneg_z
        _ = (a₁ * b)⁻¹ * ν ^ 3 := hz_inv
        _ ≤ (a₁ * b)⁻¹ * ν := mul_le_mul_of_nonneg_left hν3_le_ν (by positivity)
    have hsq_b : (ν ^ 3) ^ 2 / b ≤ b⁻¹ * ν := by
      have hpow : (ν ^ 3) ^ 2 = ν ^ 6 := by ring
      rw [hpow, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hν6_le_ν (by positivity)
    have hcl_le : C_long ≤ C_long' := le_max_left _ _
    have hsum_pos : 0 ≤ ν + (ν ^ 3) ^ 2 / b + Real.exp (-a₁ * b / ν ^ 3) := by positivity
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hw_b_pos.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc w_b⁻¹ * (C_long * (ν + (ν ^ 3) ^ 2 / b + Real.exp (-a₁ * b / ν ^ 3)))
        ≤ w_b⁻¹ * (C_long' * (ν + b⁻¹ * ν + (a₁ * b)⁻¹ * ν)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hw_b_pos.le)
          exact (mul_le_mul_of_nonneg_right hcl_le hsum_pos).trans
            (mul_le_mul_of_nonneg_left (by linarith only [hsq_b, hexp_b]) hC_long'0)
      _ = w_b⁻¹ * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν := by ring
  have hhom_kin_bd : ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * kinNorm d_s Zh_hom ≤
      ENNReal.ofReal (K_hom * ν) := by
    have hk0 := hKin_est ν ⟨hν0, hν_kin_le⟩ tr hbuc b θ hθ0 hθb le_rfl h_b Zh_hom
      hhb_mem hhb_zc hhb_ev hEvol_hom
    have hfac : ENNReal.ofReal (C_kin * (b / θ)) ≤ ENNReal.ofReal M_fac := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hdiv : b / θ ≤ b / r := div_le_div_of_nonneg_left hb0.le hr hθr
      have h1 : C_kin * (b / θ) ≤ C_kin' * (b / r) :=
        (mul_le_mul_of_nonneg_right (le_max_left C_kin 0) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hdiv hC_kin'0)
      exact h1.trans (le_max_left _ _)
    calc ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * kinNorm d_s Zh_hom
        ≤ ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ *
            (ENNReal.ofReal M_fac * (ENNReal.ofReal C_emb' * xNorm d_b m h_b)) :=
          mul_le_mul_of_nonneg_left (hk0.trans (mul_le_mul hfac hhb_kin_le zero_le zero_le))
            zero_le
      _ = ENNReal.ofReal (M_fac * C_emb') *
            (ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * xNorm d_b m h_b) := by
          rw [ENNReal.ofReal_mul hM_fac0, ← mul_assoc (ENNReal.ofReal M_fac)]
          exact mul_left_comm _ _ _
      _ ≤ ENNReal.ofReal (M_fac * C_emb') *
            ENNReal.ofReal (w_b⁻¹ * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν) := by
          rw [hgf_xnorm_hb]
          exact mul_le_mul_of_nonneg_left hxnorm_b_le zero_le
      _ = ENNReal.ofReal (K_hom * ν) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; dsimp [K_hom]; ring
  have hhom_quad_bd : ‖P.gaugeFactor ν‖⁻¹ * ‖quadQ d_s Zh_hom‖ ≤ K_hom * ν := by
    have hq0 := hMom_est ν ⟨hν0, hν_mom_le⟩ tr hbuc b θ hθ0 hθb le_rfl h_b Zh_hom
      hhb_mem hhb_zc hhb_ev hEvol_hom
    have hlog_bθ0 : 0 ≤ Real.log (b / θ) := Real.log_nonneg ((one_le_div hθ0).2 hθb)
    have hlog_le : Real.log (b / θ) ≤ Real.log (b / r) :=
      Real.log_le_log (div_pos hb0 hθ0) (div_le_div_of_nonneg_left hb0.le hr hθr)
    have hcm : ENNReal.ofReal (C_mom * b * Real.log (b / θ)) ≤
        ENNReal.ofReal (C_mom' * b * Real.log (b / r)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : C_mom * b * Real.log (b / θ) ≤ C_mom' * b * Real.log (b / θ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C_mom 0) hb0.le) hlog_bθ0
      exact h1.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))
    have hq1 : ENNReal.ofReal ‖quadQ d_s Zh_hom‖ ≤
        ENNReal.ofReal M_fac * (ENNReal.ofReal C_emb' * xNorm d_b m h_b) := by
      calc ENNReal.ofReal ‖quadQ d_s Zh_hom‖
          ≤ ENNReal.ofReal C_emb' * xNorm d_b m h_b +
              ENNReal.ofReal (C_mom' * b * Real.log (b / r)) *
                (ENNReal.ofReal C_emb' * xNorm d_b m h_b) :=
            hq0.trans (add_le_add hhb_quad_le (mul_le_mul hcm hhb_kin_le zero_le zero_le))
        _ = ENNReal.ofReal (1 + C_mom' * b * Real.log (b / r)) *
              (ENNReal.ofReal C_emb' * xNorm d_b m h_b) := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              add_mul, one_mul]
        _ ≤ ENNReal.ofReal M_fac * (ENNReal.ofReal C_emb' * xNorm d_b m h_b) :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) zero_le
    have hq_enn : ENNReal.ofReal (‖P.gaugeFactor ν‖⁻¹ * ‖quadQ d_s Zh_hom‖) ≤
        ENNReal.ofReal (K_hom * ν) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.2 hgf_pos.le)]
      calc ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * ENNReal.ofReal ‖quadQ d_s Zh_hom‖
          ≤ ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ *
              (ENNReal.ofReal M_fac * (ENNReal.ofReal C_emb' * xNorm d_b m h_b)) :=
            mul_le_mul_of_nonneg_left hq1 zero_le
        _ = ENNReal.ofReal (M_fac * C_emb') *
              (ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * xNorm d_b m h_b) := by
            rw [ENNReal.ofReal_mul hM_fac0, ← mul_assoc (ENNReal.ofReal M_fac)]
            exact mul_left_comm _ _ _
        _ ≤ ENNReal.ofReal (M_fac * C_emb') *
              ENNReal.ofReal (w_b⁻¹ * C_long' * (1 + b⁻¹ + (a₁ * b)⁻¹) * ν) := by
            rw [hgf_xnorm_hb]
            exact mul_le_mul_of_nonneg_left hxnorm_b_le zero_le
        _ = ENNReal.ofReal (K_hom * ν) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1; dsimp [K_hom]; ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hq_enn
  -- Part B: Inhomogeneous bounds for Y_re and Y_im via CLM commutation + impulse estimates
  obtain ⟨K_BS, hK_BS⟩ : ∃ K,
      K = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavartKernelCLM
        (c := ν ^ (-2 : ℝ)) (m := m) hm1 := ⟨_, rfl⟩
  obtain ⟨Q_CLM, hQ_CLM⟩ : ∃ Q, Q = quadRealCLM (ν ^ (-2 : ℝ)) m hm1 hm3 := ⟨_, rfl⟩
  have h_slice : ∀ (F Y : ℝ →
        UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.ActualVorticity
          (c := ν ^ (-2 : ℝ)) (m := m) hm1),
      ContinuousOn (fun p : ℝ × ℝ => D.evolution p.1 p.2 (F p.2))
        {p : ℝ × ℝ | t₀ ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S} →
      (∀ s', Y s' = ∫ τ in t₀..s', D.evolution s' τ (F τ)) →
      (∀ τ ∈ Icc t₀ S, ∀ a' d' : ℝ, 0 < a' → 0 < d' →
        d' * Real.sqrt a' = ν ^ (-2 : ℝ) →
          xNorm d' m (JscaleInv a' (Exist.cplx (Exist.vortFn hm1 (F τ)))) ≤
            xNorm d' m (JscaleInv a' (f_res τ))) →
      (∀ τ ∈ Icc t₀ S,
        (fun x => Exist.cplx (Exist.vortFn hm1 (F τ)) (-x)) =ᵐ[volume.restrict
          (B0579.cell (ν ^ (-2 : ℝ)))] Exist.cplx (Exist.vortFn hm1 (F τ))) →
      ‖P.gaugeFactor ν‖⁻¹ * (a_s * ‖K_BS (Y s)‖) ≤
          M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹) * ν ∧
        ‖P.gaugeFactor ν‖⁻¹ * ‖Q_CLM (Y s)‖ ≤
          M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹) * ν := by
    intro F Y hJoint hY hF_nrm hF_ev
    have hslice_cont : ContinuousOn (fun τ => D.evolution s τ (F τ)) (Icc t₀ s) :=
      continuousOn_slice_of_joint hJoint hsS
    have hmaps : ∀ u ∈ Icc θ b, t₀ ≤ clockAge ν u ∧ clockAge ν u ≤ s ∧ s ≤ S := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hθ0 hu.1
      refine ⟨?_, clockAge_anti hν0 hθ0 hu.1, hsS⟩
      rw [← ht₀_eq]
      exact clockAge_anti hν0 hu0 hu.2
    have hcov_kin : ∫ τ in t₀..s, ‖K_BS (D.evolution s τ (F τ))‖ =
        ∫ u in θ..b, ‖K_BS (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
          (clockA ν (clockAge ν u)) ^ 2 := by
      rw [← ht₀_eq]
      exact integral_clockAge_cov hν0 hθ0 hθb (fun τ => ‖K_BS (D.evolution s τ (F τ))‖)
    have hcov_quad : ∫ τ in t₀..s, ‖Q_CLM (D.evolution s τ (F τ))‖ =
        ∫ u in θ..b, ‖Q_CLM (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
          (clockA ν (clockAge ν u)) ^ 2 := by
      rw [← ht₀_eq]
      exact integral_clockAge_cov hν0 hθ0 hθb (fun τ => ‖Q_CLM (D.evolution s τ (F τ))‖)
    let lhs_k : ℝ → ℝ := fun u =>
      ‖P.gaugeFactor ν‖⁻¹ * a_s *
        (‖K_BS (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ * (clockA ν (clockAge ν u)) ^ 2)
    let lhs_q : ℝ → ℝ := fun u =>
      ‖P.gaugeFactor ν‖⁻¹ *
        (‖Q_CLM (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ * (clockA ν (clockAge ν u)) ^ 2)
    have hc_clockA2 : ContinuousOn (fun u => (clockA ν (clockAge ν u)) ^ 2) (Icc θ b) := by
      unfold clockA
      exact ((continuousOn_const.add (continuousOn_const.mul
        (continuousOn_clockAge hν0 hθ0))).pow 2)
    have hlhs_k_cont : ContinuousOn lhs_k (Icc θ b) :=
      continuousOn_const.mul ((continuousOn_norm_clm_clock K_BS s hJoint
        (continuousOn_clockAge hν0 hθ0) hmaps).mul hc_clockA2)
    have hlhs_q_cont : ContinuousOn lhs_q (Icc θ b) :=
      continuousOn_const.mul ((continuousOn_norm_clm_clock Q_CLM s hJoint
        (continuousOn_clockAge hν0 hθ0) hmaps).mul hc_clockA2)
    have hrhs_cont : ContinuousOn (fun u => M_fac * C_emb' * C_r * resTerm ν a₀ u) (Icc θ b) :=
      continuousOn_const.mul (continuousOn_resTerm hθ0)
    have hpt : ∀ u ∈ Icc θ b,
        lhs_k u ≤ M_fac * C_emb' * C_r * resTerm ν a₀ u ∧
        lhs_q u ≤ M_fac * C_emb' * C_r * resTerm ν a₀ u := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hθ0 hu.1
      have hur : r ≤ u := hθr.trans hu.1
      let τ : ℝ := clockAge ν u
      have hτ_t₀ : t₀ ≤ τ := by rw [← ht₀_eq]; exact clockAge_anti hν0 hu0 hu.2
      have hτs : τ ≤ s := clockAge_anti hν0 hθ0 hu.1
      have hτS : τ ≤ S := hτs.trans hsS
      have hτ0 : 0 ≤ τ := ht₀0.trans hτ_t₀
      let a_u : ℝ := (ν * u)⁻¹
      have ha_u_eq : clockA ν τ = a_u := clockA_clockAge hν0 hu0
      have ha_u1 : 1 ≤ a_u := by rw [← ha_u_eq]; exact one_le_clockA hν0.le hτ0
      have ha_u0 : 0 < a_u := lt_of_lt_of_le one_pos ha_u1
      let d_u : ℝ := dOfTheta ν u
      have hd_u1 : 1 ≤ d_u := one_le_dOfTheta hν0 (hν3_r.trans hur)
      have hd_u0 : 0 < d_u := lt_of_lt_of_le one_pos hd_u1
      have hdc_u : d_u * Real.sqrt a_u = ν ^ (-2 : ℝ) := by
        have h1 := dOfTheta_eq_cellLen (s := τ) hν0 (by rw [ha_u_eq]; exact ha_u0)
        rw [clockTheta_clockAge hν0 hu0, ha_u_eq] at h1
        change d_u = cellLen (ν ^ (-2 : ℝ)) a_u at h1
        rw [h1]; unfold cellLen; exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha_u0).ne'
      obtain ⟨hF_mem, hF_zc⟩ := Exist.goodCStable.1 (ν ^ (-2 : ℝ)) m hm1 (F τ)
      have hF_bs := Exist.biotSavartFieldAll (ν ^ (-2 : ℝ)) m hm1 (F τ)
      obtain ⟨hhu_mem, hhu_zc, hhu_ev, hhu_bs, hhu_nrm, hJu_ae⟩ :=
        symEven_jscaleInv_props hm_gt1 ha_u1 hd_u0 hdc_u hF_mem hF_zc hF_bs (hF_ev τ ⟨hτ_t₀, hτS⟩)
      let h_u : ℝ × ℝ → ℂ := symEven (JscaleInv a_u (Exist.cplx (Exist.vortFn hm1 (F τ))))
      have hev_eq : Exist.horizonEvolution hm1 Pn H s τ (F τ) = D.evolution s τ (F τ) := by
        rw [hD]
        exact congrArg (fun L => L (F τ))
          (Exist.horizonEvolution_eq hm1 Exist.horizonLocality Pn H hτ0 hτs (hsS.trans hSN))
      let Zh_u : ℝ × ℝ → ℂ :=
        JscaleInv a_s (Exist.cplx (Exist.vortFn hm1 (D.evolution s τ (F τ))))
      have hEvol_u : HeatEvolvesTo ν m tr u θ h_u Zh_u := by
        refine ⟨fun r' => Exist.cplx (Exist.vortFn hm1 (Exist.horizonEvolution hm1 Pn H r' τ (F τ))),
          fun r' => Exist.stripVel hm1 (Exist.horizonEvolution hm1 Pn H r' τ (F τ)), ?_, ?_⟩
        · exact isLinearisedFlow_congr_initial_ae (horizon_real_flow hm1 hReg tr Pn H hH hτ0 (F τ))
            hJu_ae.symm
        · change JscaleInv a_s (Exist.cplx (Exist.vortFn hm1 (D.evolution s τ (F τ)))) =
            JscaleInv a_s (Exist.cplx (Exist.vortFn hm1 (Exist.horizonEvolution hm1 Pn H s τ (F τ))))
          rw [hev_eq]
      have hemb_hu : ENNReal.ofReal ‖quadQ d_u h_u‖ + kinNorm d_u h_u ≤
          ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ)) := by
        rw [kinNorm_eq_of_isBiotSavart hd_u0 hhu_bs]
        have h0 := (hEmb_d d_u hd_u1 h_u hhu_mem hhu_zc hhu_ev _ hhu_bs).trans
          (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C_emb 0)) zero_le)
        change _ ≤ ENNReal.ofReal C_emb' * xNorm d_u m h_u at h0
        rw [hhu_nrm] at h0
        exact h0.trans (mul_le_mul_of_nonneg_left
          (hF_nrm τ ⟨hτ_t₀, hτS⟩ a_u d_u ha_u0 hd_u0 hdc_u) zero_le)
      have hhu_kin_le : kinNorm d_u h_u ≤
          ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ)) :=
        le_add_self.trans hemb_hu
      have hhu_quad_le : ENNReal.ofReal ‖quadQ d_u h_u‖ ≤
          ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ)) :=
        le_self_add.trans hemb_hu
      have hk_u0 := hKin_est ν ⟨hν0, hν_kin_le⟩ tr hbuc u θ hθ0 hu.1 hu.2 h_u Zh_u
        hhu_mem hhu_zc hhu_ev hEvol_u
      have hq_u0 := hMom_est ν ⟨hν0, hν_mom_le⟩ tr hbuc u θ hθ0 hu.1 hu.2 h_u Zh_u
        hhu_mem hhu_zc hhu_ev hEvol_u
      have hfac_k : ENNReal.ofReal (C_kin * (u / θ)) ≤ ENNReal.ofReal M_fac := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hdiv : u / θ ≤ b / r :=
          (div_le_div_of_nonneg_right hu.2 hθ0.le).trans
            (div_le_div_of_nonneg_left hb0.le hr hθr)
        have h1 : C_kin * (u / θ) ≤ C_kin' * (b / r) :=
          (mul_le_mul_of_nonneg_right (le_max_left C_kin 0) (by positivity)).trans
            (mul_le_mul_of_nonneg_left hdiv hC_kin'0)
        exact h1.trans (le_max_left _ _)
      have hk_u1 : ENNReal.ofReal (a_s * ‖K_BS (D.evolution s τ (F τ))‖) ≤
          ENNReal.ofReal (M_fac * C_emb') * xNorm d_u m (JscaleInv a_u (f_res τ)) := by
        rw [hK_BS, ← kinNorm_jscaleInv_vortFn_eq hm1 ha_s0 hd_s0 hdc_s (D.evolution s τ (F τ)),
          ENNReal.ofReal_mul hM_fac0, mul_assoc]
        exact hk_u0.trans (mul_le_mul hfac_k hhu_kin_le zero_le zero_le)
      have hlog_uθ0 : 0 ≤ Real.log (u / θ) := Real.log_nonneg ((one_le_div hθ0).2 hu.1)
      have hlog_u_le : Real.log (u / θ) ≤ Real.log (b / r) := by
        refine Real.log_le_log (div_pos hu0 hθ0) ?_
        exact (div_le_div_of_nonneg_right hu.2 hθ0.le).trans
          (div_le_div_of_nonneg_left hb0.le hr hθr)
      have hcm_u : ENNReal.ofReal (C_mom * u * Real.log (u / θ)) ≤
          ENNReal.ofReal (C_mom' * b * Real.log (b / r)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : C_mom * u * Real.log (u / θ) ≤ C_mom' * b * Real.log (u / θ) :=
          mul_le_mul_of_nonneg_right
            ((mul_le_mul_of_nonneg_right (le_max_left C_mom 0) hu0.le).trans
              (mul_le_mul_of_nonneg_left hu.2 hC_mom'0)) hlog_uθ0
        exact h1.trans (mul_le_mul_of_nonneg_left hlog_u_le (by positivity))
      have hq_u1 : ENNReal.ofReal ‖Q_CLM (D.evolution s τ (F τ))‖ ≤
          ENNReal.ofReal (M_fac * C_emb') * xNorm d_u m (JscaleInv a_u (f_res τ)) := by
        rw [hQ_CLM, ← norm_quadQ_jscaleInv_vortFn_eq hm1 hm3 ha_s0 hd_s0 hdc_s (D.evolution s τ (F τ)),
          ENNReal.ofReal_mul hM_fac0, mul_assoc]
        calc ENNReal.ofReal ‖quadQ d_s Zh_u‖
            ≤ ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ)) +
                ENNReal.ofReal (C_mom' * b * Real.log (b / r)) *
                  (ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ))) :=
              hq_u0.trans (add_le_add hhu_quad_le (mul_le_mul hcm_u hhu_kin_le zero_le zero_le))
          _ = ENNReal.ofReal (1 + C_mom' * b * Real.log (b / r)) *
                (ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ))) := by
              rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
                add_mul, one_mul]
          _ ≤ ENNReal.ofReal M_fac *
                (ENNReal.ofReal C_emb' * xNorm d_u m (JscaleInv a_u (f_res τ))) :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right _ _)) zero_le
      let mult : ℝ := a_u ^ 2 / ‖P.gaugeFactor ν‖
      have hmult0 : 0 ≤ mult := by dsimp [mult]; positivity
      have hres_u : ENNReal.ofReal mult * xNorm d_u m (JscaleInv a_u (f_res τ)) ≤
          ENNReal.ofReal (C_r * resTerm ν a₀ u) := by
        have h0 := hf_bd u ⟨hur, hu.2⟩
        rw [ha_u_eq] at h0
        exact h0
      have hres0 : 0 ≤ resTerm ν a₀ u := by
        unfold resTerm
        exact add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hu0.le _)) (by positivity)
      have hk_enn : ENNReal.ofReal (lhs_k u) ≤
          ENNReal.ofReal (M_fac * C_emb' * C_r * resTerm ν a₀ u) := by
        have hl : ENNReal.ofReal (lhs_k u) =
            ENNReal.ofReal mult * ENNReal.ofReal (a_s * ‖K_BS (D.evolution s τ (F τ))‖) := by
          rw [← ENNReal.ofReal_mul hmult0]
          congr 1
          dsimp only [lhs_k, mult, τ]
          rw [ha_u_eq, div_eq_mul_inv (a_u ^ 2)]
          ring
        rw [hl]
        calc ENNReal.ofReal mult * ENNReal.ofReal (a_s * ‖K_BS (D.evolution s τ (F τ))‖)
            ≤ ENNReal.ofReal mult *
                (ENNReal.ofReal (M_fac * C_emb') * xNorm d_u m (JscaleInv a_u (f_res τ))) :=
              mul_le_mul_of_nonneg_left hk_u1 zero_le
          _ = ENNReal.ofReal (M_fac * C_emb') *
                (ENNReal.ofReal mult * xNorm d_u m (JscaleInv a_u (f_res τ))) :=
              mul_left_comm _ _ _
          _ ≤ ENNReal.ofReal (M_fac * C_emb') * ENNReal.ofReal (C_r * resTerm ν a₀ u) :=
              mul_le_mul_of_nonneg_left hres_u zero_le
          _ = ENNReal.ofReal (M_fac * C_emb' * C_r * resTerm ν a₀ u) := by
              rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      have hq_enn : ENNReal.ofReal (lhs_q u) ≤
          ENNReal.ofReal (M_fac * C_emb' * C_r * resTerm ν a₀ u) := by
        have hl : ENNReal.ofReal (lhs_q u) =
            ENNReal.ofReal mult * ENNReal.ofReal ‖Q_CLM (D.evolution s τ (F τ))‖ := by
          rw [← ENNReal.ofReal_mul hmult0]
          congr 1
          dsimp only [lhs_q, mult, τ]
          rw [ha_u_eq, div_eq_mul_inv (a_u ^ 2)]
          ring
        rw [hl]
        calc ENNReal.ofReal mult * ENNReal.ofReal ‖Q_CLM (D.evolution s τ (F τ))‖
            ≤ ENNReal.ofReal mult *
                (ENNReal.ofReal (M_fac * C_emb') * xNorm d_u m (JscaleInv a_u (f_res τ))) :=
              mul_le_mul_of_nonneg_left hq_u1 zero_le
          _ = ENNReal.ofReal (M_fac * C_emb') *
                (ENNReal.ofReal mult * xNorm d_u m (JscaleInv a_u (f_res τ))) :=
              mul_left_comm _ _ _
          _ ≤ ENNReal.ofReal (M_fac * C_emb') * ENNReal.ofReal (C_r * resTerm ν a₀ u) :=
              mul_le_mul_of_nonneg_left hres_u zero_le
          _ = ENNReal.ofReal (M_fac * C_emb' * C_r * resTerm ν a₀ u) := by
              rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      exact ⟨(ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hk_enn,
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hq_enn⟩
    have hres_int_bd : ∫ u in θ..b, resTerm ν a₀ u ≤ (r⁻¹ + a₀⁻¹) * ν := by
      have h0 := integral_resTerm_le hν0 ha₀ hθ0 hθb
      have h1 : (ν ^ 3) ^ 2 / θ ≤ r⁻¹ * ν := by
        have hpow : (ν ^ 3) ^ 2 = ν ^ 6 := by ring
        rw [hpow, div_eq_inv_mul]
        exact (mul_le_mul_of_nonneg_right (inv_anti₀ hr hθr) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hν6_le_ν (by positivity))
      have h2 : (ν ^ 6 / a₀) * Real.exp (-a₀ * θ / ν ^ 3) ≤ a₀⁻¹ * ν := by
        have hexp1 : Real.exp (-a₀ * θ / ν ^ 3) ≤ 1 :=
          Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha₀.le) hθ0.le) (by positivity))
        calc (ν ^ 6 / a₀) * Real.exp (-a₀ * θ / ν ^ 3)
            ≤ (ν ^ 6 / a₀) * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
          _ = a₀⁻¹ * ν ^ 6 := by rw [mul_one, div_eq_inv_mul]
          _ ≤ a₀⁻¹ * ν := mul_le_mul_of_nonneg_left hν6_le_ν (by positivity)
      linarith only [h0, h1, h2]
    have hk_comm : K_BS (Y s) = ∫ τ in t₀..s, K_BS (D.evolution s τ (F τ)) := by
      rw [hY s]
      exact (K_BS.intervalIntegral_comp_comm
        (hslice_cont.intervalIntegrable_of_Icc (μ := volume) hts)).symm
    have hq_comm : Q_CLM (Y s) = ∫ τ in t₀..s, Q_CLM (D.evolution s τ (F τ)) := by
      rw [hY s]
      exact (Q_CLM.intervalIntegral_comp_comm
        (hslice_cont.intervalIntegrable_of_Icc (μ := volume) hts)).symm
    have hk_int := intervalIntegral.integral_mono_on hθb
      (hlhs_k_cont.intervalIntegrable_of_Icc (μ := volume) hθb)
      (hrhs_cont.intervalIntegrable_of_Icc (μ := volume) hθb)
      (fun u hu => (hpt u hu).1)
    have hq_int := intervalIntegral.integral_mono_on hθb
      (hlhs_q_cont.intervalIntegrable_of_Icc (μ := volume) hθb)
      (hrhs_cont.intervalIntegrable_of_Icc (μ := volume) hθb)
      (fun u hu => (hpt u hu).2)
    have hk_pull : ∫ u in θ..b, lhs_k u =
        (‖P.gaugeFactor ν‖⁻¹ * a_s) *
          ∫ u in θ..b, ‖K_BS (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
            (clockA ν (clockAge ν u)) ^ 2 := by
      dsimp only [lhs_k]
      exact intervalIntegral.integral_const_mul _ _
    have hq_pull : ∫ u in θ..b, lhs_q u =
        ‖P.gaugeFactor ν‖⁻¹ *
          ∫ u in θ..b, ‖Q_CLM (D.evolution s (clockAge ν u) (F (clockAge ν u)))‖ *
            (clockA ν (clockAge ν u)) ^ 2 := by
      dsimp only [lhs_q]
      exact intervalIntegral.integral_const_mul _ _
    have hr_pull : ∫ u in θ..b, M_fac * C_emb' * C_r * resTerm ν a₀ u =
        M_fac * C_emb' * C_r * ∫ u in θ..b, resTerm ν a₀ u :=
      intervalIntegral.integral_const_mul _ _
    rw [hk_pull, hr_pull] at hk_int
    rw [hq_pull, hr_pull] at hq_int
    refine ⟨?_, ?_⟩
    · calc ‖P.gaugeFactor ν‖⁻¹ * (a_s * ‖K_BS (Y s)‖)
          ≤ (‖P.gaugeFactor ν‖⁻¹ * a_s) * ∫ τ in t₀..s, ‖K_BS (D.evolution s τ (F τ))‖ := by
            rw [← mul_assoc, hk_comm]
            exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hts)
              (by positivity)
        _ ≤ M_fac * C_emb' * C_r * ∫ u in θ..b, resTerm ν a₀ u := by
            rw [hcov_kin]; exact hk_int
        _ ≤ M_fac * C_emb' * C_r * ((r⁻¹ + a₀⁻¹) * ν) :=
            mul_le_mul_of_nonneg_left hres_int_bd (by positivity)
        _ = M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹) * ν := by ring
    · calc ‖P.gaugeFactor ν‖⁻¹ * ‖Q_CLM (Y s)‖
          ≤ ‖P.gaugeFactor ν‖⁻¹ * ∫ τ in t₀..s, ‖Q_CLM (D.evolution s τ (F τ))‖ := by
            rw [hq_comm]
            exact mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hts)
              (by positivity)
        _ ≤ M_fac * C_emb' * C_r * ∫ u in θ..b, resTerm ν a₀ u := by
            rw [hcov_quad]; exact hq_int
        _ ≤ M_fac * C_emb' * C_r * ((r⁻¹ + a₀⁻¹) * ν) :=
            mul_le_mul_of_nonneg_left hres_int_bd (by positivity)
        _ = M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹) * ν := by ring
  have hFre_ev : ∀ τ ∈ Icc t₀ S,
      (fun x => Exist.cplx (Exist.vortFn hm1 (F_re τ)) (-x)) =ᵐ[volume.restrict
        (B0579.cell (ν ^ (-2 : ℝ)))] Exist.cplx (Exist.vortFn hm1 (F_re τ)) := by
    intro τ hτ
    have hre : Exist.cplx (Exist.vortFn hm1 (F_re τ)) =ᵐ[volume.restrict
        (B0579.cell (ν ^ (-2 : ℝ)))] fun x => ((f_res τ x).re : ℂ) :=
      ((hF_lift τ hτ).2.1).mono fun x hx => by simp [Exist.cplx, hx]
    have hev := (hf_props τ hτ).2.2.2.1
    filter_upwards [ae_neg_of_ae_cell hre, hre] with x hx1 hx2
    change Exist.cplx (Exist.vortFn hm1 (F_re τ)) (-x) = ((f_res τ (-x)).re : ℂ) at hx1
    change Exist.cplx (Exist.vortFn hm1 (F_re τ)) x = ((f_res τ x).re : ℂ) at hx2
    rw [hx1, hx2, hev x]
  have hFim_ev : ∀ τ ∈ Icc t₀ S,
      (fun x => Exist.cplx (Exist.vortFn hm1 (F_im τ)) (-x)) =ᵐ[volume.restrict
        (B0579.cell (ν ^ (-2 : ℝ)))] Exist.cplx (Exist.vortFn hm1 (F_im τ)) := by
    intro τ hτ
    have him : Exist.cplx (Exist.vortFn hm1 (F_im τ)) =ᵐ[volume.restrict
        (B0579.cell (ν ^ (-2 : ℝ)))] fun x => ((f_res τ x).im : ℂ) :=
      ((hF_lift τ hτ).2.2).mono fun x hx => by simp [Exist.cplx, hx]
    have hev := (hf_props τ hτ).2.2.2.1
    filter_upwards [ae_neg_of_ae_cell him, him] with x hx1 hx2
    change Exist.cplx (Exist.vortFn hm1 (F_im τ)) (-x) = ((f_res τ (-x)).im : ℂ) at hx1
    change Exist.cplx (Exist.vortFn hm1 (F_im τ)) x = ((f_res τ x).im : ℂ) at hx2
    rw [hx1, hx2, hev x]
  obtain ⟨hk_re, hq_re⟩ := h_slice F_re Y_re hJoint_re hYre
    (fun τ hτ a' d' ha' hd' hdc' =>
      xNorm_jscaleInv_vortFn_le_of_re hm1 ha' hd' hdc' (F_re τ) (hF_lift τ hτ).2.1) hFre_ev
  obtain ⟨hk_im, hq_im⟩ := h_slice F_im Y_im hJoint_im hYim
    (fun τ hτ a' d' ha' hd' hdc' =>
      xNorm_jscaleInv_vortFn_le_of_im hm1 ha' hd' hdc' (F_im τ) (hF_lift τ hτ).2.2) hFim_ev
  have hKtot_eps : K_tot * ν ≤ ε := by
    have h1 : K_tot * ν ≤ (K_tot + 1) * ν :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hν0.le
    have h2 : (K_tot + 1) * ν < (K_tot + 1) * (ε / (K_tot + 1)) :=
      mul_lt_mul_of_pos_left hν_lt_eps (by positivity)
    have h3 : (K_tot + 1) * (ε / (K_tot + 1)) = ε :=
      mul_div_cancel₀ ε (by positivity)
    linarith only [h1, h2, h3]
  have hae_s := hduh s ⟨hts, hsS⟩
  rw [heatColumn_sub_canonicalPeriodized_eq P hν0 hθ0 w]
  refine ⟨?_, ?_⟩
  · have hkin_tri := kinNorm_heatDiff_inhom_le hm_gt1 hm1 ha_s1 hd_s0 hdc_s (P.gaugeFactor ν)⁻¹
      (hw_hom.memX s hts) (hw_hom.biotSavart s hts) (Y_re s) (Y_im s) hae_s
    rw [norm_inv, ← hK_BS] at hkin_tri
    change kinNorm d_s _ ≤ ENNReal.ofReal ε
    calc kinNorm d_s (fun y => (P.gaugeFactor ν)⁻¹ *
          JscaleInv a_s (fun x => w s x - canonicalPhysColumn P ν s x) y)
        ≤ ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ *
            (kinNorm d_s Zh_hom + ENNReal.ofReal (a_s * ‖K_BS (Y_re s)‖) +
              ENNReal.ofReal (a_s * ‖K_BS (Y_im s)‖)) := hkin_tri
      _ = ENNReal.ofReal ‖P.gaugeFactor ν‖⁻¹ * kinNorm d_s Zh_hom +
            ENNReal.ofReal (‖P.gaugeFactor ν‖⁻¹ * (a_s * ‖K_BS (Y_re s)‖)) +
            ENNReal.ofReal (‖P.gaugeFactor ν‖⁻¹ * (a_s * ‖K_BS (Y_im s)‖)) := by
          rw [mul_add, mul_add, ← ENNReal.ofReal_mul (inv_nonneg.2 hgf_pos.le),
            ← ENNReal.ofReal_mul (inv_nonneg.2 hgf_pos.le)]
      _ ≤ ENNReal.ofReal (K_hom * ν) +
            ENNReal.ofReal (M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹) * ν) +
            ENNReal.ofReal (M_fac * C_emb' * C_r * (r⁻¹ + a₀⁻¹) * ν) :=
          add_le_add (add_le_add hhom_kin_bd (ENNReal.ofReal_le_ofReal hk_re))
            (ENNReal.ofReal_le_ofReal hk_im)
      _ = ENNReal.ofReal (K_tot * ν) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hK_hom0 hν0.le) (by positivity),
            ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hK_hom0 hν0.le) (by positivity))
              (by positivity)]
          congr 1; dsimp [K_tot, K_inh]; ring
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hKtot_eps
  · have hquad_tri := quadQ_heatDiff_inhom_le hm1 hm3 ha_s1 hd_s0 hdc_s (P.gaugeFactor ν)⁻¹
      (hw_hom.memX s hts) (Y_re s) (Y_im s) hae_s
    rw [norm_inv, ← hQ_CLM] at hquad_tri
    change ENNReal.ofReal ‖quadQ d_s _‖ ≤ ENNReal.ofReal ε
    refine ENNReal.ofReal_le_ofReal ?_
    have hdist : ‖P.gaugeFactor ν‖⁻¹ *
        (‖quadQ d_s Zh_hom‖ + ‖Q_CLM (Y_re s)‖ + ‖Q_CLM (Y_im s)‖) =
        ‖P.gaugeFactor ν‖⁻¹ * ‖quadQ d_s Zh_hom‖ +
          ‖P.gaugeFactor ν‖⁻¹ * ‖Q_CLM (Y_re s)‖ +
          ‖P.gaugeFactor ν‖⁻¹ * ‖Q_CLM (Y_im s)‖ := by ring
    rw [hdist] at hquad_tri
    have hsum : ‖P.gaugeFactor ν‖⁻¹ * ‖quadQ d_s Zh_hom‖ +
          ‖P.gaugeFactor ν‖⁻¹ * ‖Q_CLM (Y_re s)‖ +
          ‖P.gaugeFactor ν‖⁻¹ * ‖Q_CLM (Y_im s)‖ ≤ K_tot * ν := by
      dsimp only [K_tot, K_inh]
      linarith only [hhom_quad_bd, hq_re, hq_im]
    exact hquad_tri.trans (hsum.trans hKtot_eps)

/-- Inhomogeneous Duhamel transfer (`PartIII-a:T22/2/3`, SP 3190-3305): proves both
`CTLongComparison` (`b ≤ θ ≤ ν⁻¹`) and conditional `CTCompactComparison` (`r ≤ θ ≤ b`). -/
theorem ctDuhamelTransfer (hBranch : UnforcedLeray.Short.IIIa.T22Sub.CTCanonicalBranchProps)
    (hRes : UnforcedLeray.Short.IIIa.T22Sub.CTCanonicalResidual) :
    UnforcedLeray.Short.IIIa.T22Sub.CTDuhamelTransfer :=
  ⟨ctLongComparison_of hBranch hRes,
    ctCompactComparison_of hBranch hRes (ctLongComparison_of hBranch hRes)⟩

end UnforcedLeray.Short.IIIa.T22Sub

