import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.T20_CTEmbeddings
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.AbsoluteStress.Impulse
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV

/-!
# Part III-a, `PartIII-a:T22/6`: Absolute stress bound (`eq:ct-absolute-stress`)

Source of record: `the November 2 reference manuscript` (SP), lines 3345-3379.

Establishes `UnforcedLeray.Short.IIIa.CTAbsoluteStress` for `k ≤ 1` by splitting
`Ioi (onsetAge ν)` at `s_b = clockAge ν b = coreEnd ν b` for a fixed large clock `b`:
1. On `Ioc (onsetAge ν) s_b` (`b ≤ θ < θ_o(ν)`), `ctLongComparison`,
   `T22Sub.ctCanonicalBranchProps`, and `ctEmbeddings` (applied to the centrally-even
   representative of `heatColumn P ν w θ`, justified via reflection symmetry and
   `fullClockLongForward` uniqueness at zero datum) yield exponential decay of the physical
   perturbation velocity `velNorm c (u s)`, which combines with pre-overlap `TrainL2Decay`
   and exact derivative integration of `exp (-(γ/2) * clockTheta ν s)`.
2. On `Ioi s_b` (`0 < θ < b`), restarting `IsLinearisedFlow` at `s_b` and rescaling by
   `(P.gaugeFactor ν)⁻¹` reduces directly to `T22Sub.ctAbsoluteImpulse` at `r = b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-! ## 1. Pointwise Frobenius, Cauchy-Schwarz, and gauge-scaling properties of `sAbs` -/

private lemma sAbs_smul {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (α : ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) :
    sAbs tr μ (fun x j => α * u x j) s = ENNReal.ofReal ‖α‖ * sAbs tr μ u s := by
  unfold sAbs
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2,
        ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * (α * u x j)) +
            ((s : ℂ) ^ (-μ) * (α * u x i)) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2) =
      ‖α‖ ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
        ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
            ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpt : ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * (α * u x j)) +
          ((s : ℂ) ^ (-μ) * (α * u x i)) * ((tr.v s x j : ℝ) : ℂ) =
        α * (((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
          ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)) := by
      ring
    rw [hpt, norm_mul, mul_pow]
  rw [hsum, Real.sqrt_mul (sq_nonneg ‖α‖), Real.sqrt_sq (norm_nonneg α),
    ENNReal.ofReal_mul (norm_nonneg α)]
  exact (mul_left_comm _ _ _).symm

private lemma frobenius_sym_le_abs (v : UnforcedLeray.Train.Vec) (z : ℂ) (u : Fin 2 → ℂ) :
    Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
      ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2) ≤
      2 * ‖z‖ * ‖v‖ * Real.sqrt (∑ j : Fin 2, ‖u j‖ ^ 2) := by
  have hterm : ∀ i j : Fin 2,
      ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2 ≤
        2 * (‖z‖ ^ 2 * ((v i) ^ 2 * ‖u j‖ ^ 2 + ‖u i‖ ^ 2 * (v j) ^ 2)) := by
    intro i j
    set X : ℝ := |v i| * (‖z‖ * ‖u j‖)
    set Y : ℝ := (‖z‖ * ‖u i‖) * |v j|
    have htri : ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ≤ X + Y := by
      calc ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖
          ≤ ‖((v i : ℝ) : ℂ) * (z * u j)‖ + ‖(z * u i) * ((v j : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = X + Y := by simp only [X, Y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsq1 : ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2 ≤ (X + Y) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hsq2 : (X + Y) ^ 2 ≤ 2 * (X ^ 2 + Y ^ 2) := by nlinarith [sq_nonneg (X - Y)]
    have hXY : X ^ 2 + Y ^ 2 = ‖z‖ ^ 2 * ((v i) ^ 2 * ‖u j‖ ^ 2 + ‖u i‖ ^ 2 * (v j) ^ 2) := by
      dsimp only [X, Y]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    linarith
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2,
      ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2 ≤
      4 * ‖z‖ ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2) := by
    simp only [Fin.sum_univ_two]
    have h00 := hterm 0 0; have h01 := hterm 0 1
    have h10 := hterm 1 0; have h11 := hterm 1 1
    linarith
  have hv_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hnn : 0 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by positivity
    rw [Real.sq_sqrt hnn, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  set R : ℝ := 2 * ‖z‖ * ‖v‖ * Real.sqrt (∑ j : Fin 2, ‖u j‖ ^ 2)
  have hR_nn : 0 ≤ R := by dsimp [R]; positivity
  have hR_sq : R ^ 2 = 4 * ‖z‖ ^ 2 * ((v 0) ^ 2 + (v 1) ^ 2) * (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2) := by
    dsimp only [R]
    have hu_nn : 0 ≤ ∑ j : Fin 2, ‖u j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hu_nn, hv_sq, Fin.sum_univ_two]
    ring
  calc Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
        ‖((v i : ℝ) : ℂ) * (z * u j) + (z * u i) * ((v j : ℝ) : ℂ)‖ ^ 2)
      ≤ Real.sqrt (R ^ 2) := by rw [hR_sq]; exact Real.sqrt_le_sqrt hsum
    _ = R := Real.sqrt_sq hR_nn

private lemma cyl_cellμ_eq_restrict_cell_abs (c : ℝ) :
    UnforcedLeray.Cyl.cellμ c = volume.restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell B0579.cell
  rw [neg_div]

private lemma continuous_train_vel_abs {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {s : ℝ} (hs : 0 ≤ s) :
    Continuous (tr.v s) :=
  tr.isTrain.smooth_v.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨hs, trivial⟩)

private lemma sAbs_le_cellL2_mul_velNorm_abs {ν : ℝ} (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) {s : ℝ} (hs : 0 < s)
    (hu : ∀ j : Fin 2, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (ν ^ (-2 : ℝ))))) :
    sAbs tr μ u s ≤
      ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) *
        UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) *
        velNorm (ν ^ (-2 : ℝ)) u := by
  let c : ℝ := ν ^ (-2 : ℝ)
  let μ_c : Measure (ℝ × ℝ) := volume.restrict (B0579.cell c)
  have hc_inv : c⁻¹ = ν ^ 2 := by
    dsimp [c]; rw [Real.rpow_neg hν.le, Real.rpow_two, inv_inv]
  have hcpow : ‖(s : ℂ) ^ (-μ)‖ = s ^ (-μ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hs, Complex.neg_re]
  set F : ℝ × ℝ → ℝ≥0∞ := fun x => ‖tr.v s x‖ₑ
  set G : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2))
  have hF_aem : AEMeasurable F μ_c :=
    ((continuous_train_vel_abs tr hs.le).measurable.enorm).aemeasurable
  have hG_aem : AEMeasurable G μ_c := by
    have hsum_aem : AEMeasurable (fun x => ∑ j : Fin 2, ‖u x j‖ ^ 2) μ_c :=
      Finset.aemeasurable_sum Finset.univ fun j _ => ((hu j).1.norm.aemeasurable.pow_const 2)
    exact (Real.continuous_sqrt.measurable.comp_aemeasurable hsum_aem).ennreal_ofReal
  have hpt : ∀ x : ℝ × ℝ,
      ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
          ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
              ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2)) ≤
        ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * (F x * G x) := by
    intro x
    have hfrob := frobenius_sym_le_abs (tr.v s x) ((s : ℂ) ^ (-μ)) (u x)
    rw [hcpow] at hfrob
    rw [hc_inv]
    have h1 := ENNReal.ofReal_le_ofReal hfrob
    calc ENNReal.ofReal (ν ^ 2) *
          ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
            ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
                ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2))
        ≤ ENNReal.ofReal (ν ^ 2) *
            ENNReal.ofReal (2 * s ^ (-μ.re) * ‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 bot_le
      _ = ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * (F x * G x) := by
          have hv_nn : 0 ≤ ‖tr.v s x‖ := norm_nonneg _
          dsimp only [F, G]
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ν ^ 2),
            show ν ^ 2 * (2 * s ^ (-μ.re) * ‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) =
              (2 * ν ^ 2 * s ^ (-μ.re)) * (‖tr.v s x‖ * Real.sqrt (∑ j : Fin 2, ‖u x j‖ ^ 2)) by ring,
            ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ν ^ 2 * s ^ (-μ.re)),
            ENNReal.ofReal_mul hv_nn, ofReal_norm]
  have hFG_le : ∫⁻ x, F x * G x ∂μ_c ≤
      UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c u := by
    have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ_c Real.HolderConjugate.two_two hF_aem hG_aem
    have hF_lp : (∫⁻ x, F x ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) =
        UnforcedLeray.Train.cellL2 c (tr.v s) := by
      unfold UnforcedLeray.Train.cellL2
      rw [cyl_cellμ_eq_restrict_cell_abs,
        eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      simp [F, μ_c]
    have hG_lp : (∫⁻ x, G x ^ (2 : ℝ) ∂μ_c) ^ (1 / (2 : ℝ)) = velNorm c u := by
      have hG_sq : ∀ x : ℝ × ℝ, G x ^ (2 : ℝ) = ∑ j : Fin 2, ‖u x j‖ₑ ^ 2 := by
        intro x
        set S : ℝ := ∑ j : Fin 2, ‖u x j‖ ^ 2
        have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
        dsimp only [G]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg S) 2, Real.sq_sqrt hS_nn]
        dsimp only [S]
        rw [Fin.sum_univ_two, Fin.sum_univ_two,
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _) 2, ENNReal.ofReal_pow (norm_nonneg _) 2,
          ofReal_norm, ofReal_norm]
      rw [lintegral_congr hG_sq,
        lintegral_finsetSum' Finset.univ (fun j _ => ((hu j).1.enorm.pow_const 2))]
      unfold velNorm
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [T07.eLpNorm_two_eq_lintegral, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
    simpa only [Pi.mul_apply, hF_lp, hG_lp] using hhold
  unfold sAbs
  calc ∫⁻ x, ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
          ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
              ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2)) ∂μ_c
      ≤ ∫⁻ x, ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * (F x * G x) ∂μ_c := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) * ∫⁻ x, F x * G x ∂μ_c :=
        lintegral_const_mul'' _ (hF_aem.mul hG_aem)
    _ ≤ ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) *
          (UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c u) :=
        mul_le_mul_of_nonneg_left hFG_le bot_le
    _ = ENNReal.ofReal (2 * ν ^ 2 * s ^ (-μ.re)) *
          UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c u := (mul_assoc _ _ _).symm

/-! ## 2. Rescaling (`Jscale` / `JscaleInv`), Biot-Savart rescaling, and `symEven` -/

private lemma ae_smul_sqrt_of_ae_abs {a d : ℝ} (ha : 0 < a) {f g : ℝ × ℝ → ℂ}
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

private lemma ae_div_sqrt_of_ae_abs {a d : ℝ} (ha : 0 < a) {W V : ℝ × ℝ → ℂ}
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
  have h := ae_smul_sqrt_of_ae_abs hinv hWV'
  refine h.mono fun x hx => ?_
  simpa [hsq, div_eq_inv_mul] using hx

private lemma jscaleInv_memLp_bound_abs {m a d : ℝ} (hm : 0 ≤ m) (ha : 1 ≤ a) (hd : 0 < d)
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
    filter_upwards [ae_smul_sqrt_of_ae_abs ha0 hae_vol] with y hy
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

private lemma integral_cell_comp_sqrt_smul_abs {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
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

private lemma hasZeroCirc_jscaleInv_abs {m a d : ℝ} (hm : 1 < m) (ha : 1 ≤ a) (hd : 0 < d)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (B0579.cellMeasure (d * Real.sqrt a) m))
    (hz : HasZeroCirculation (d * Real.sqrt a) f) :
    HasZeroCirculation d (JscaleInv a f) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hmem := (jscaleInv_memLp_bound_abs (by linarith) ha hd hf).1
  refine ⟨integrableOn_cell_of_X hm hmem, ?_⟩
  unfold JscaleInv
  rw [integral_const_mul, integral_cell_comp_sqrt_smul_abs ha0 hd f, hz.2, mul_zero, mul_zero]

private lemma jscale_jscaleInv_abs {a : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) :
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

private def velMovAbs (a : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (y : ℝ × ℝ) (j : Fin 2) : ℂ :=
  ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u (Real.sqrt a * y.1, Real.sqrt a * y.2) j

private lemma isCylTest_div_sqrt_abs {a d : ℝ} (ha : 0 < a) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) :
    B0579.IsCylTest (d * Real.sqrt a) (fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hRne : Real.sqrt a ≠ 0 := hR.ne'
  refine ⟨?_, ?_, ?_⟩
  · exact hψ.smooth.comp ((contDiff_fst.div_const _).prodMk (contDiff_snd.div_const _))
  · intro x
    have h1 : (x.1 + d * Real.sqrt a) / Real.sqrt a = x.1 / Real.sqrt a + d := by field_simp
    dsimp only; rw [h1]
    exact hψ.periodic (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
  · obtain ⟨B, hB⟩ := hψ.band
    refine ⟨max B 0 * Real.sqrt a, fun x hx => ?_⟩
    have hlt : B < |x.2 / Real.sqrt a| := by
      rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left B 0) hR.le) hx
    exact hB _ hlt

private lemma pd_div_sqrt_abs {a : ℝ} (_ha : 0 < a) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
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

private lemma eLpNorm_sq_velMov_abs {a d : ℝ} (ha : 0 < a) {u : ℝ × ℝ → Fin 2 → ℂ}
    (hu : ∀ j, MemLp (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))))
    (j : Fin 2) :
    MemLp (fun y => velMovAbs a u y j) 2 (volume.restrict (B0579.cell d)) ∧
      eLpNorm (fun y => velMovAbs a u y j) 2 (volume.restrict (B0579.cell d)) =
        ENNReal.ofReal a *
          eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell (d * Real.sqrt a))) := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set u₀ : ℝ × ℝ → ℂ := (hu j).1.mk (fun x => u x j)
  have hu₀m : Measurable u₀ := (hu j).1.stronglyMeasurable_mk.measurable
  have hae : (fun x => u x j) =ᵐ[volume.restrict (B0579.cell (d * Real.sqrt a))] u₀ :=
    (hu j).1.ae_eq_mk
  have hae_y : (fun y => velMovAbs a u y j) =ᵐ[volume.restrict (B0579.cell d)]
      (fun y => ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u₀ (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
    filter_upwards [ae_smul_sqrt_of_ae_abs ha hae] with y hy
    simp [velMovAbs, hy]
  have hm_y : AEStronglyMeasurable (fun y => velMovAbs a u y j) (volume.restrict (B0579.cell d)) :=
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
  have hlint : ∫⁻ y, ‖velMovAbs a u y j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell d)) =
      ENNReal.ofReal (a ^ 2) *
        ∫⁻ x, ‖u x j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell (d * Real.sqrt a))) := by
    have e1 : ∫⁻ y, ‖velMovAbs a u y j‖ₑ ^ 2 ∂(volume.restrict (B0579.cell d)) =
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
  have henorm : eLpNorm (fun y => velMovAbs a u y j) 2 (volume.restrict (B0579.cell d)) =
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

private lemma isBiotSavart_velMov_abs {a d : ℝ} (ha : 0 < a) (hd : 0 < d) {om : ℝ × ℝ → ℂ}
    {u : ℝ × ℝ → Fin 2 → ℂ} (hbs : IsBiotSavart (d * Real.sqrt a) om u) :
    IsBiotSavart d (JscaleInv a om) (velMovAbs a u) ∧
      velNorm d (velMovAbs a u) = ENNReal.ofReal a * velNorm (d * Real.sqrt a) u := by
  have hR : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hRne : Real.sqrt a ≠ 0 := hR.ne'
  have hmem := fun j => (eLpNorm_sq_velMov_abs ha hbs.1 j).1
  have hnrm := fun j => (eLpNorm_sq_velMov_abs ha hbs.1 j).2
  refine ⟨⟨hmem, ?_, ?_⟩, ?_⟩
  · intro ψ hψ
    let ψp : ℝ × ℝ → ℝ := fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hψp : B0579.IsCylTest (d * Real.sqrt a) ψp := isCylTest_div_sqrt_abs ha hψ
    have hdiv := hbs.2.1 ψp hψp
    have hcov := integral_cell_comp_sqrt_smul_abs ha hd
      (fun x => u x 0 * (B0579.pd 0 ψp x : ℂ) + u x 1 * (B0579.pd 1 ψp x : ℂ))
    rw [hdiv, mul_zero] at hcov
    have hpt : (fun y : ℝ × ℝ => velMovAbs a u y 0 * (B0579.pd 0 ψ y : ℂ) +
        velMovAbs a u y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => ((a ^ (3 / 2 : ℝ) * Real.sqrt a : ℝ) : ℂ) *
          (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
              (B0579.pd 0 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) +
            u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
              (B0579.pd 1 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
      funext y
      simp only [velMovAbs, ψp, pd_div_sqrt_abs ha hψ.smooth]
      have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
        ext <;> simp [mul_div_cancel_left₀ _ hRne]
      rw [hcoord]; push_cast; field_simp [hRne]
    rw [hpt, integral_const_mul, hcov, mul_zero]
  · intro ψ hψ
    let ψp : ℝ × ℝ → ℝ := fun x => ψ (x.1 / Real.sqrt a, x.2 / Real.sqrt a)
    have hψp : B0579.IsCylTest (d * Real.sqrt a) ψp := isCylTest_div_sqrt_abs ha hψ
    have hcurl := hbs.2.2 ψp hψp
    have hcovL := integral_cell_comp_sqrt_smul_abs ha hd (fun x => om x * (ψp x : ℂ))
    have hcovR := integral_cell_comp_sqrt_smul_abs ha hd
      (fun x => u x 0 * (B0579.pd 1 ψp x : ℂ) - u x 1 * (B0579.pd 0 ψp x : ℂ))
    have hL : (∫ y in B0579.cell d, JscaleInv a om y * (ψ y : ℂ)) =
        ((a ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d, om (Real.sqrt a * y.1, Real.sqrt a * y.2) *
            (ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) := by
      have hp : ∀ y : ℝ × ℝ, JscaleInv a om y * (ψ y : ℂ) =
          ((a ^ 2 : ℝ) : ℂ) * (om (Real.sqrt a * y.1, Real.sqrt a * y.2) *
            (ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
        intro y; unfold JscaleInv; simp only [ψp]
        have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
          ext <;> simp [mul_div_cancel_left₀ _ hRne]
        rw [hcoord]; ring
      simp only [hp, integral_const_mul]
    have ha32 : a ^ (3 / 2 : ℝ) * Real.sqrt a = a ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]; norm_num
    have hR' : (∫ y in B0579.cell d,
        (velMovAbs a u y 0 * (B0579.pd 1 ψ y : ℂ) - velMovAbs a u y 1 * (B0579.pd 0 ψ y : ℂ))) =
        ((a ^ 2 : ℝ) : ℂ) *
          ∫ y in B0579.cell d,
            (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
                (B0579.pd 1 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) -
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
                (B0579.pd 0 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
      have hp : ∀ y : ℝ × ℝ,
          velMovAbs a u y 0 * (B0579.pd 1 ψ y : ℂ) - velMovAbs a u y 1 * (B0579.pd 0 ψ y : ℂ) =
          ((a ^ 2 : ℝ) : ℂ) *
            (u (Real.sqrt a * y.1, Real.sqrt a * y.2) 0 *
                (B0579.pd 1 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ) -
              u (Real.sqrt a * y.1, Real.sqrt a * y.2) 1 *
                (B0579.pd 0 ψp (Real.sqrt a * y.1, Real.sqrt a * y.2) : ℂ)) := by
        intro y
        rw [← ha32]
        simp only [velMovAbs, ψp, pd_div_sqrt_abs ha hψ.smooth]
        have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
          ext <;> simp [mul_div_cancel_left₀ _ hRne]
        rw [hcoord]; push_cast; field_simp [hRne]
      simp only [hp, integral_const_mul]
    rw [hL, hR', hcovL, hcovR, hcurl]
  · unfold velNorm
    have hsum : (∑ j : Fin 2, eLpNorm (fun y => velMovAbs a u y j) 2
          (volume.restrict (B0579.cell d)) ^ 2) =
        ENNReal.ofReal a ^ 2 *
          ∑ j : Fin 2, eLpNorm (fun x => u x j) 2
            (volume.restrict (B0579.cell (d * Real.sqrt a))) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hnrm j, mul_pow]
    rw [hsum, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    congr 1
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

private lemma isBiotSavart_smul_abs {d : ℝ} (z : ℂ) {f : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
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

private lemma velNorm_smul_abs {d : ℝ} (z : ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) :
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
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

private lemma isBiotSavart_congr_ae_abs {d : ℝ} {f₁ f₂ : ℝ × ℝ → ℂ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
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

private def symEvenAbs (f : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  (2 : ℂ)⁻¹ * (f x + f (-x))

private lemma isCentrallyEven_symEven_abs (f : ℝ × ℝ → ℂ) : IsCentrallyEven (symEvenAbs f) := by
  intro x; unfold symEvenAbs; rw [neg_neg, add_comm]

private lemma cell_neg_ae_eq_abs (c : ℝ) :
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

private lemma measurePreserving_neg_cell_abs (c : ℝ) :
    MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ)
      (volume.restrict (B0579.cell c)) (volume.restrict (B0579.cell c)) := by
  refine ⟨measurable_neg, ?_⟩
  have hmp : MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_neg volume
  have heq : volume.restrict (Neg.neg ⁻¹' B0579.cell c) = volume.restrict (B0579.cell c) :=
    Measure.restrict_congr_set (cell_neg_ae_eq_abs c)
  calc Measure.map Neg.neg (volume.restrict (B0579.cell c))
      = Measure.map Neg.neg (volume.restrict (Neg.neg ⁻¹' B0579.cell c)) := by rw [heq]
    _ = (Measure.map Neg.neg volume).restrict (B0579.cell c) :=
        ((MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding.restrict_map volume (B0579.cell c)).symm
    _ = volume.restrict (B0579.cell c) := by rw [hmp.map_eq]

private lemma ae_neg_of_ae_cell_abs {c : ℝ} {f g : ℝ × ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) :
    (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => g (-x)) :=
  (measurePreserving_neg_cell_abs c).quasiMeasurePreserving.ae_eq_comp h

private lemma integral_cell_neg_abs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : ℝ × ℝ → E) :
    ∫ x in B0579.cell c, f (-x) = ∫ x in B0579.cell c, f x :=
  (measurePreserving_neg_cell_abs c).integral_comp
    (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding f

private lemma symEven_ae_eq_abs {c : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : (fun x => f (-x)) =ᵐ[volume.restrict (B0579.cell c)] f) :
    symEvenAbs f =ᵐ[volume.restrict (B0579.cell c)] f := by
  filter_upwards [hf] with x hx
  unfold symEvenAbs; rw [hx]; ring

/-! ## 3. `IsLinearisedFlow` scaling, subtraction, reflection, and core central evenness -/

private lemma isLinearisedFlow_congr_initial_ae_abs {ν c m t₀ : ℝ}
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

private lemma isLinearisedFlow_smul_abs {ν c m t₀ : ℝ} (α : ℂ)
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
    dsimp only; unfold xNorm; rw [heq, eLpNorm_const_smul]
  biotSavart s hs := isBiotSavart_smul_abs α (hw.biotSavart s hs)
  integrable φ hφ r hr := by
    have heq : flowIntegrand tr (fun x => α * w r x) (fun x j => α * u r x j) r φ =
        fun x => α * flowIntegrand tr (w r) (u r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq]; exact (hw.integrable φ hφ r hr).const_mul α
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

private lemma isLinearisedFlow_sub_m_abs {ν c m : ℝ} (hm : 1 < m)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {t : ℝ}
    {f₁ f₂ : ℝ × ℝ → ℂ} {w₁ w₂ : ℝ → ℝ × ℝ → ℂ} {u₁ u₂ : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hf₁ : MemLp f₁ 2 (B0579.cellMeasure c m))
    (hf₂ : MemLp f₂ 2 (B0579.cellMeasure c m))
    (hw₁ : IsLinearisedFlow ν c m tr t f₁ w₁ u₁)
    (hw₂ : IsLinearisedFlow ν c m tr t f₂ w₂ u₂) :
    IsLinearisedFlow ν c m tr t (fun x => f₁ x - f₂ x)
      (fun s x => w₁ s x - w₂ s x) (fun s x j => u₁ s x j - u₂ s x j) where
  initial := hw₁.initial.sub hw₂.initial
  memX s hs := (hw₁.memX s hs).sub (hw₂.memX s hs)
  strongCont s hs := by
    have hlim : Tendsto (fun s' => xNorm c m (w₁ s' - w₁ s) + xNorm c m (w₂ s' - w₂ s))
        (𝓝[Ici t] s) (𝓝 0) := by
      simpa using (hw₁.strongCont s hs).add (hw₂.strongCont s hs)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    have heq : ((fun x => w₁ s' x - w₂ s' x) - (fun x => w₁ s x - w₂ s x)) =
        (w₁ s' - w₁ s) - (w₂ s' - w₂ s) := by
      funext x; simp only [Pi.sub_apply]; ring
    unfold xNorm; rw [heq]
    exact eLpNorm_sub_le ((hw₁.memX s' hs').1.sub (hw₁.memX s hs).1)
      ((hw₂.memX s' hs').1.sub (hw₂.memX s hs).1) one_le_two
  biotSavart s hs :=
    ladBSSub m c (w₁ s) (w₂ s) (u₁ s) (u₂ s) hm
      (hw₁.memX s hs) (hw₂.memX s hs) (hw₁.biotSavart s hs) (hw₂.biotSavart s hs)
  integrable φ hφ r hr := by
    have heq : flowIntegrand tr (fun x => w₁ r x - w₂ r x) (fun x j => u₁ r x j - u₂ r x j) r φ =
        fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x - flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
      funext x; unfold flowIntegrand; ring
    rw [heq]; exact (hw₁.integrable φ hφ r hr).sub (hw₂.integrable φ hφ r hr)
  timeIntegrable φ hφ s hs := by
    have hsub := (hw₁.timeIntegrable φ hφ s hs).sub (hw₂.timeIntegrable φ hφ s hs)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs] at hsub ⊢
    refine hsub.congr_fun (fun r hr => ?_) measurableSet_Ioc
    have heq : flowIntegrand tr (fun x => w₁ r x - w₂ r x) (fun x j => u₁ r x j - u₂ r x j) r φ =
        fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x - flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
      funext x; unfold flowIntegrand; ring
    simp only [heq]
    exact (integral_sub (hw₁.integrable φ hφ r hr.1.le) (hw₂.integrable φ hφ r hr.1.le)).symm
  weak φ hφ s hs := by
    have Iw₁ : IntegrableOn (fun x => w₁ s x * (φ x : ℂ)) (B0579.cell c) :=
      CutLimitAux.integrable_complex (hw₁.memX s hs) (hφ.memLp (-m)).ofReal
    have Iw₂ : IntegrableOn (fun x => w₂ s x * (φ x : ℂ)) (B0579.cell c) :=
      CutLimitAux.integrable_complex (hw₂.memX s hs) (hφ.memLp (-m)).ofReal
    have If₁ : IntegrableOn (fun x => f₁ x * (φ x : ℂ)) (B0579.cell c) :=
      CutLimitAux.integrable_complex hf₁ (hφ.memLp (-m)).ofReal
    have If₂ : IntegrableOn (fun x => f₂ x * (φ x : ℂ)) (B0579.cell c) :=
      CutLimitAux.integrable_complex hf₂ (hφ.memLp (-m)).ofReal
    have heqL : (fun x => (w₁ s x - w₂ s x) * (φ x : ℂ)) =
        fun x => w₁ s x * (φ x : ℂ) - w₂ s x * (φ x : ℂ) := by funext x; ring
    have heqf : (fun x => (f₁ x - f₂ x) * (φ x : ℂ)) =
        fun x => f₁ x * (φ x : ℂ) - f₂ x * (φ x : ℂ) := by funext x; ring
    have hcongr : ∀ r ∈ uIoc t s,
        (∫ x in B0579.cell c, flowIntegrand tr (fun x => w₁ r x - w₂ r x)
          (fun x j => u₁ r x j - u₂ r x j) r φ x) =
        (∫ x in B0579.cell c, flowIntegrand tr (w₁ r) (u₁ r) r φ x) -
          (∫ x in B0579.cell c, flowIntegrand tr (w₂ r) (u₂ r) r φ x) := by
      intro r hr
      rw [uIoc_of_le hs] at hr
      have heq : flowIntegrand tr (fun x => w₁ r x - w₂ r x)
          (fun x j => u₁ r x j - u₂ r x j) r φ =
          fun x => flowIntegrand tr (w₁ r) (u₁ r) r φ x - flowIntegrand tr (w₂ r) (u₂ r) r φ x := by
        funext x; unfold flowIntegrand; ring
      rw [heq, integral_sub (hw₁.integrable φ hφ r hr.1.le) (hw₂.integrable φ hφ r hr.1.le)]
    rw [heqL, integral_sub Iw₁ Iw₂, hw₁.weak φ hφ s hs, hw₂.weak φ hφ s hs,
      heqf, integral_sub If₁ If₂,
      intervalIntegral.integral_congr_ae (ae_of_all _ hcongr),
      intervalIntegral.integral_sub (hw₁.timeIntegrable φ hφ s hs) (hw₂.timeIntegrable φ hφ s hs)]
    ring

private lemma pd_comp_neg_abs {F : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => F (-y)) x = -B0579.pd k F (-x) := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ := -ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have hfun : (fun y : ℝ × ℝ => F (-y)) = F ∘ L := rfl
  unfold B0579.pd
  have hfd : fderiv ℝ (F ∘ L) x = (fderiv ℝ F (-x)).comp L :=
    ((hF (-x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  rw [hfun, hfd, ContinuousLinearMap.comp_apply]
  simp [L]

private lemma pd_neg_abs {G : ℝ × ℝ → ℝ} (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => -G y) x = -B0579.pd k G x := by
  unfold B0579.pd
  change (fderiv ℝ (-G) x) (B0579.dir k) = -(fderiv ℝ G x) (B0579.dir k)
  rw [fderiv_neg]; rfl

private lemma isCylTest_neg_abs {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
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

private lemma eLpNorm_comp_neg_cellMeasure_abs (c m : ℝ) (F : ℝ × ℝ → ℂ) :
    xNorm c m (fun x => F (-x)) = xNorm c m F := by
  unfold xNorm
  rw [PairContAux.eLpNorm_cellMeasure_cx, PairContAux.eLpNorm_cellMeasure_cx,
    T06.eLpNorm_two_eq_lintegral, T06.eLpNorm_two_eq_lintegral]
  congr 1
  have hjb : ∀ x : ℝ × ℝ, B0579.jb (-x) = B0579.jb x := fun x => by simp [B0579.jb]
  have hfn : (fun x : ℝ × ℝ => ‖((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * F (-x)‖ₑ ^ 2) =
      (fun y : ℝ × ℝ => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2) ∘ Neg.neg := by
    funext x; simp [Function.comp, hjb x]
  rw [hfn]
  exact (measurePreserving_neg_cell_abs c).lintegral_comp_emb
    (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding
    (fun y => ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * F y‖ₑ ^ 2)

private lemma memLp_comp_neg_cellMeasure_abs {c m : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (B0579.cellMeasure c m)) :
    MemLp (fun x => F (-x)) 2 (B0579.cellMeasure c m) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_vol : F =ᵐ[volume.restrict (B0579.cell c)] F₀ :=
    (B0579.ac_cellMeasure c m).ae_le hF.1.ae_eq_mk
  have hae_neg : (fun x => F (-x)) =ᵐ[B0579.cellMeasure c m] (fun x => F₀ (-x)) :=
    (B0579.cellMeasure_ac c m).ae_le (ae_neg_of_ae_cell_abs hae_vol)
  have hm : AEStronglyMeasurable (fun x => F (-x)) (B0579.cellMeasure c m) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  change xNorm c m (fun x => F (-x)) < ⊤
  rw [eLpNorm_comp_neg_cellMeasure_abs]
  exact hF.2

private lemma memLp_comp_neg_vol_abs {c : ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (B0579.cell c))) :
    MemLp (fun x => F (-x)) 2 (volume.restrict (B0579.cell c)) := by
  set F₀ : ℝ × ℝ → ℂ := hF.1.mk F
  have hF₀m : Measurable F₀ := hF.1.stronglyMeasurable_mk.measurable
  have hae_neg : (fun x => F (-x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => F₀ (-x)) :=
    ae_neg_of_ae_cell_abs hF.1.ae_eq_mk
  have hm : AEStronglyMeasurable (fun x => F (-x)) (volume.restrict (B0579.cell c)) :=
    (hF₀m.comp measurable_neg).aestronglyMeasurable.congr hae_neg.symm
  refine ⟨hm, ?_⟩
  rw [T06.eLpNorm_two_eq_lintegral]
  have hlint : ∫⁻ x, ‖F (-x)‖ₑ ^ 2 ∂(volume.restrict (B0579.cell c)) =
      ∫⁻ y, ‖F y‖ₑ ^ 2 ∂(volume.restrict (B0579.cell c)) :=
    (measurePreserving_neg_cell_abs c).lintegral_comp_emb
      (MeasurableEquiv.neg (ℝ × ℝ)).measurableEmbedding (fun y => ‖F y‖ₑ ^ 2)
  rw [hlint, ← T06.eLpNorm_two_eq_lintegral]
  exact hF.2

private lemma isLinearisedFlow_reflect_abs {ν c m : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) {f : ℝ × ℝ → ℂ}
    (hf_even : IsCentrallyEven f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr 0 f w u) :
    IsLinearisedFlow ν c m tr 0 f (fun τ x => w τ (-x)) (fun τ x j => -u τ (-x) j) := by
  let w' : ℝ → ℝ × ℝ → ℂ := fun τ x => w τ (-x)
  let u' : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun τ x j => -u τ (-x) j
  have hlap_neg : ∀ (ψ : ℝ × ℝ → ℝ) (_ : ContDiff ℝ ∞ ψ) (x : ℝ × ℝ),
      lapP (fun y => ψ (-y)) x = lapP ψ (-x) := by
    intro ψ hψ x; unfold lapP
    have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have hpd0 : Differentiable ℝ (B0579.pd 0 ψ) :=
      (ForceMemXAux.contDiff_pd hψ 0).differentiable (by simp)
    have hpd1 : Differentiable ℝ (B0579.pd 1 ψ) :=
      (ForceMemXAux.contDiff_pd hψ 1).differentiable (by simp)
    have e0 : B0579.pd 0 (fun y => ψ (-y)) = fun y => -B0579.pd 0 ψ (-y) :=
      funext (pd_comp_neg_abs hdψ 0)
    have e1 : B0579.pd 1 (fun y => ψ (-y)) = fun y => -B0579.pd 1 ψ (-y) :=
      funext (pd_comp_neg_abs hdψ 1)
    have d0 : B0579.pd 0 (fun y => -B0579.pd 0 ψ (-y)) x = B0579.pd 0 (B0579.pd 0 ψ) (-x) := by
      rw [pd_neg_abs, pd_comp_neg_abs hpd0 0 x, neg_neg]
    have d1 : B0579.pd 1 (fun y => -B0579.pd 1 ψ (-y)) x = B0579.pd 1 (B0579.pd 1 ψ) (-x) := by
      rw [pd_neg_abs, pd_comp_neg_abs hpd1 1 x, neg_neg]
    rw [e0, e1, d0, d1]
  have hpdE_odd : ∀ r : ℝ, 0 ≤ r → ∀ (j : Fin 2) (x : ℝ × ℝ),
      B0579.pd j (UnforcedLeray.B0238.Ec tr r) (-x) =
        -B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by
    intro r hr j x
    have hdE : Differentiable ℝ (UnforcedLeray.B0238.Ec tr r) :=
      (ForceMemXAux.contDiff_Ec tr hr).differentiable (by simp)
    have heven : (fun y => UnforcedLeray.B0238.Ec tr r (-y)) = UnforcedLeray.B0238.Ec tr r :=
      funext (UnforcedLeray.B0238.Ec_even tr hr)
    have h1 := pd_comp_neg_abs hdE j x
    rw [heven] at h1; linarith
  have hfl_eq : ∀ (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) (r : ℝ), 0 ≤ r → ∀ x : ℝ × ℝ,
      flowIntegrand tr (w' r) (u' r) r ψ x =
        flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) := by
    intro ψ hψ r hr0 x
    have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
    have p0 := pd_comp_neg_abs hdψ 0 (-x)
    have p1 := pd_comp_neg_abs hdψ 1 (-x)
    have pl := hlap_neg ψ hψ.smooth (-x)
    rw [neg_neg] at p0 p1 pl
    have hv_odd : ∀ j : Fin 2, tr.v r (-x) j = -tr.v r x j := fun j => by
      have h := congrArg (fun v : UnforcedLeray.Train.Vec => v j) (tr.isTrain.odd r hr0 x)
      simpa using h
    have eE0 := hpdE_odd r hr0 0 x
    have eE1 := hpdE_odd r hr0 1 x
    unfold flowIntegrand; dsimp only [w', u']
    rw [p0, p1, pl, hv_odd 0, hv_odd 1, eE0, eE1, neg_neg]
    push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ae_neg_of_ae_cell_abs hw.initial).trans (Eventually.of_forall hf_even)
  · exact fun s hs => memLp_comp_neg_cellMeasure_abs (hw.memX s hs)
  · intro s hs
    refine (hw.strongCont s hs).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' _
    have heq : w' s' - w' s = fun x => (w s' - w s) (-x) := rfl
    rw [heq, eLpNorm_comp_neg_cellMeasure_abs]
  · intro s hs
    have hbs := hw.biotSavart s hs
    refine ⟨fun j => (memLp_comp_neg_vol_abs (hbs.1 j)).neg, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hψn := isCylTest_neg_abs hψ
      have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
      have hpt : (fun x => u' s x 0 * (B0579.pd 0 ψ x : ℂ) + u' s x 1 * (B0579.pd 1 ψ x : ℂ)) =
          fun x => u s (-x) 0 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) +
            u s (-x) 1 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) := by
        funext x
        have p0 := pd_comp_neg_abs hdψ 0 (-x); have p1 := pd_comp_neg_abs hdψ 1 (-x)
        rw [neg_neg] at p0 p1; dsimp only [u']; rw [p0, p1]; push_cast; ring
      rw [hpt, integral_cell_neg_abs c (fun y => u s y 0 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ) +
        u s y 1 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ))]
      exact hbs.2.1 _ hψn
    · have hψn := isCylTest_neg_abs hψ
      have hdψ : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
      have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
          ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
        have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
            fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp [w']
        rw [hp]; exact integral_cell_neg_abs c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
      have hr : (fun x => u' s x 0 * (B0579.pd 1 ψ x : ℂ) - u' s x 1 * (B0579.pd 0 ψ x : ℂ)) =
          fun x => u s (-x) 0 * (B0579.pd 1 (fun y => ψ (-y)) (-x) : ℂ) -
            u s (-x) 1 * (B0579.pd 0 (fun y => ψ (-y)) (-x) : ℂ) := by
        funext x
        have p0 := pd_comp_neg_abs hdψ 0 (-x); have p1 := pd_comp_neg_abs hdψ 1 (-x)
        rw [neg_neg] at p0 p1; dsimp only [u']; rw [p0, p1]; push_cast; ring
      rw [hl, hr, integral_cell_neg_abs c (fun y => u s y 0 * (B0579.pd 1 (fun z => ψ (-z)) y : ℂ) -
        u s y 1 * (B0579.pd 0 (fun z => ψ (-z)) y : ℂ))]
      exact hbs.2.2 _ hψn
  · intro ψ hψ r hr
    have hψn := isCylTest_neg_abs hψ
    have hInt : Integrable (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))
        (volume.restrict (B0579.cell c)) := hw.integrable _ hψn r hr
    exact ((measurePreserving_neg_cell_abs c).integrable_comp_of_integrable hInt).congr
      (Eventually.of_forall fun x => (hfl_eq ψ hψ r hr x).symm)
  · intro ψ hψ s hs
    have hψn := isCylTest_neg_abs hψ
    refine (hw.timeIntegrable _ hψn s hs).congr fun r hr => ?_
    rw [uIoc_of_le hs] at hr
    have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
        fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
      funext (hfl_eq ψ hψ r hr.1.le)
    rw [heq_r, integral_cell_neg_abs c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
  · intro ψ hψ s hs
    have hψn := isCylTest_neg_abs hψ
    have hl : ∫ x in B0579.cell c, w' s x * (ψ x : ℂ) =
        ∫ y in B0579.cell c, w s y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun x : ℝ × ℝ => w' s x * (ψ x : ℂ)) =
          fun x => w s (-x) * ((fun z => ψ (-z)) (-x) : ℂ) := by funext x; simp [w']
      rw [hp]; exact integral_cell_neg_abs c (fun y => w s y * ((fun z => ψ (-z)) y : ℂ))
    have hf_int : ∫ x in B0579.cell c, f x * (ψ x : ℂ) =
        ∫ y in B0579.cell c, f y * ((fun z => ψ (-z)) y : ℂ) := by
      have hp : (fun y : ℝ × ℝ => f y * (ψ y : ℂ)) =
          fun y => f (-y) * ((fun z => ψ (-z)) (-y) : ℂ) := by
        funext y; simp [hf_even y]
      rw [hp]; exact integral_cell_neg_abs c (fun y => f y * ((fun z => ψ (-z)) y : ℂ))
    have hr_int : ∫ r in (0 : ℝ)..s, (∫ x in B0579.cell c, flowIntegrand tr (w' r) (u' r) r ψ x) =
        ∫ r in (0 : ℝ)..s, (∫ y in B0579.cell c,
          flowIntegrand tr (w r) (u r) r (fun z => ψ (-z)) y) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs] at hr
        have heq_r : flowIntegrand tr (w' r) (u' r) r ψ =
            fun x => flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)) (-x) :=
          funext (hfl_eq ψ hψ r hr.1)
        rw [heq_r, integral_cell_neg_abs c (flowIntegrand tr (w r) (u r) r (fun y => ψ (-y)))]
    rw [hl, hf_int, hr_int, hw.weak _ hψn s hs]

/-- Using `FullClockLongForward` at `t = 0` with datum `0`, central evenness of the initial datum
propagates a.e. on `B0579.cell (ν⁻²)` to every age `s ≥ 0` in the core `b ≤ clockTheta ν s`. -/
private lemma flow_even_ae_of_longForward {P : PlanarData} {ν m b C_fc : ℝ}
    (hν : 0 < ν) (hm : 1 < m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} (hf_mem : MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hf_even : IsCentrallyEven f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f w u)
    {s : ℝ} (hs : 0 ≤ s) (_hbs : b ≤ clockTheta ν s)
    (hfc : ∀ f₀ : ℝ × ℝ → ℂ, MemLp f₀ 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
      HasZeroCirculation (ν ^ (-2 : ℝ)) f₀ →
      ∀ w₀ u₀, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f₀ w₀ u₀ →
        xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) m (JscaleInv (clockA ν s) (w₀ s)) ≤
          ENNReal.ofReal (C_fc * Real.exp (P.eigenvalue.re * (clockTheta ν 0 - clockTheta ν s)) *
              (clockTheta ν 0 / clockTheta ν s) ^ P.kappa.re) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν 0)) m (JscaleInv (clockA ν 0) f₀)) :
    (fun x => w s (-x)) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] w s := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν _
  have hw_ref := isLinearisedFlow_reflect_abs tr hf_even hw
  have hw_sub := isLinearisedFlow_sub_m_abs hm hf_mem hf_mem hw hw_ref
  have hf_zero : (fun x : ℝ × ℝ => f x - f x) = fun _ => 0 := by funext x; simp
  rw [hf_zero] at hw_sub
  have hzc0 : HasZeroCirculation c (fun _ : ℝ × ℝ => (0 : ℂ)) :=
    ⟨integrableOn_zero, by simp⟩
  have hbd := hfc (fun _ => 0) MemLp.zero hzc0 _ _ hw_sub
  have hJ0 : JscaleInv (clockA ν 0) (fun _ : ℝ × ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext y; simp [JscaleInv]
  rw [hJ0, show xNorm (cellLen c (clockA ν 0)) m (fun _ : ℝ × ℝ => (0 : ℂ)) = 0 by simp [xNorm],
    mul_zero] at hbd
  set a_s : ℝ := clockA ν s
  have ha_s1 : 1 ≤ a_s := by unfold a_s clockA; nlinarith
  have ha_s0 : 0 < a_s := lt_of_lt_of_le one_pos ha_s1
  set d_s : ℝ := cellLen c a_s
  have hd_s0 : 0 < d_s := by unfold d_s cellLen; exact div_pos hc_pos (Real.sqrt_pos.2 ha_s0)
  have hdc : d_s * Real.sqrt a_s = c := by
    unfold d_s cellLen; exact div_mul_cancel₀ c (Real.sqrt_pos.2 ha_s0).ne'
  have hdiff_mem : MemLp (fun x => w s x - w s (-x)) 2 (B0579.cellMeasure (d_s * Real.sqrt a_s) m) := by
    rw [hdc]; exact hw_sub.memX s hs
  have hJ_mem := (jscaleInv_memLp_bound_abs (by linarith) ha_s1 hd_s0 hdiff_mem).1
  have hx0 : eLpNorm (JscaleInv a_s (fun x => w s x - w s (-x))) 2 (B0579.cellMeasure d_s m) = 0 :=
    le_zero_iff.1 hbd
  have hae_cm : JscaleInv a_s (fun x => w s x - w s (-x)) =ᵐ[B0579.cellMeasure d_s m] 0 :=
    (eLpNorm_eq_zero_iff hJ_mem.1 two_ne_zero).1 hx0
  have hae_vol_d : JscaleInv a_s (fun x => w s x - w s (-x)) =ᵐ[volume.restrict (B0579.cell d_s)] 0 :=
    (B0579.ac_cellMeasure d_s m).ae_le hae_cm
  have hae_div := ae_div_sqrt_of_ae_abs ha_s0 hae_vol_d
  rw [hdc] at hae_div
  have hsq_ne : Real.sqrt a_s ≠ 0 := (Real.sqrt_pos.2 ha_s0).ne'
  have ha2_ne : ((a_s ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_ne_zero 2 ha_s0.ne')
  filter_upwards [hae_div] with x hx
  have hcoord : (Real.sqrt a_s * (x.1 / Real.sqrt a_s), Real.sqrt a_s * (x.2 / Real.sqrt a_s)) = x := by
    ext <;> simp [mul_div_cancel₀ _ hsq_ne]
  have hneg_coord : -(Real.sqrt a_s * (x.1 / Real.sqrt a_s), Real.sqrt a_s * (x.2 / Real.sqrt a_s)) =
      -x := by rw [hcoord]
  dsimp only [JscaleInv, Pi.zero_apply] at hx
  rw [hcoord] at hx
  have hsub0 : w s x - w s (-x) = 0 := (mul_eq_zero.1 hx).resolve_left ha2_ne
  exact (sub_eq_zero.1 hsub0).symm

/-! ## 4. Core heat-column regularity, `kinNorm`, and physical velocity bound on `[b, ν⁻¹]` -/

private lemma dOfTheta_mul_sqrt_inv_abs {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    dOfTheta ν θ * Real.sqrt ((ν * θ)⁻¹) = ν ^ (-2 : ℝ) := by
  unfold dOfTheta
  have hc_pos : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
    rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]; ring
  rw [← Real.sqrt_mul (by positivity : 0 ≤ θ / ν ^ 3)]
  have hprod : θ / ν ^ 3 * (ν * θ)⁻¹ = (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hc_sq]; have := hν.ne'; have := hθ.ne'; field_simp
  rw [hprod, Real.sqrt_sq hc_pos.le]

private lemma core_heatDatum_and_vel_bound
    {P : PlanarData} {ν m b θ C_emb C_br C_long a₁ : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hm : 8 < m) (hb1 : 1 ≤ b) (hθb : b ≤ θ) (hθν : θ ≤ ν⁻¹)
    (hν3 : ν ^ 3 ≤ b)
    (_hC_emb : 0 < C_emb) (hC_br : 0 < C_br) (hC_long : 0 < C_long) (ha₁ : 0 < a₁)
    (hEmb : ∀ d : ℝ, 1 ≤ d → ∀ f : ℝ × ℝ → ℂ,
      MemLp f 2 (B0579.cellMeasure d m) → HasZeroCirculation d f → IsCentrallyEven f →
        ∀ u, IsBiotSavart d f u →
          ENNReal.ofReal ‖quadQ d f‖ + velNorm d u ≤ ENNReal.ofReal C_emb * xNorm d m f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw_mem : MemLp (w (clockAge ν θ)) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
    (hw_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) (w (clockAge ν θ)))
    (hw_bs : IsBiotSavart (ν ^ (-2 : ℝ)) (w (clockAge ν θ)) (u (clockAge ν θ)))
    (hw_ev : (fun x => w (clockAge ν θ) (-x)) =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
      w (clockAge ν θ))
    (hVd_mem : MemLp (canonicalPeriodized P ν θ) 2 (B0579.cellMeasure (dOfTheta ν θ) m))
    (hBr_bd : ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
        xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) ≤ ENNReal.ofReal C_br)
    (hLong_bd : ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
        xNorm (dOfTheta ν θ) m (heatColumn P ν w θ - canonicalPeriodized P ν θ) ≤
        ENNReal.ofReal (C_long * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3)))) :
    let d_θ := dOfTheta ν θ
    let h_θ := symEvenAbs (heatColumn P ν w θ)
    MemLp h_θ 2 (B0579.cellMeasure d_θ m) ∧
      HasZeroCirculation d_θ h_θ ∧
      IsCentrallyEven h_θ ∧
      (Jscale (ν * θ)⁻¹ h_θ =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
        fun x => (P.gaugeFactor ν)⁻¹ * w (clockAge ν θ) x) ∧
      kinNorm d_θ h_θ ≤
        ENNReal.ofReal (C_emb * (C_br + 3 * C_long) *
          Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) ∧
      velNorm (ν ^ (-2 : ℝ)) (u (clockAge ν θ)) ≤
        ENNReal.ofReal (C_emb * (C_br + 3 * C_long) * ‖P.gaugeFactor ν‖ * ν * θ *
          Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) := by
  dsimp only
  have hθ1 : 1 ≤ θ := hb1.trans hθb
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
  set c : ℝ := ν ^ (-2 : ℝ)
  set a : ℝ := (ν * θ)⁻¹
  have ha1 : 1 ≤ a := by
    dsimp [a]
    have hmul : ν * θ ≤ 1 := by
      calc ν * θ ≤ ν * ν⁻¹ := mul_le_mul_of_nonneg_left hθν hν.le
        _ = 1 := mul_inv_cancel₀ hν.ne'
    exact (one_le_inv₀ (mul_pos hν hθ0)).2 hmul
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
  set d_θ : ℝ := dOfTheta ν θ
  have hd_θ1 : 1 ≤ d_θ := T22Sub.one_le_dOfTheta hν (hν3.trans hθb)
  have hd_θ0 : 0 < d_θ := lt_of_lt_of_le one_pos hd_θ1
  have hdc : d_θ * Real.sqrt a = c := dOfTheta_mul_sqrt_inv_abs hν hθ0
  set α : ℂ := (P.gaugeFactor ν)⁻¹
  have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν
  have hα_pos : 0 < ‖α‖ := norm_pos_iff.2 (inv_ne_zero hgf_ne)
  -- Regularity and symmetry of Z_θ = heatColumn P ν w θ and h_θ = symEvenAbs Z_θ
  set s_θ : ℝ := clockAge ν θ
  have hw_mem' : MemLp (w s_θ) 2 (B0579.cellMeasure (d_θ * Real.sqrt a) m) := hdc.symm ▸ hw_mem
  have hw_zc' : HasZeroCirculation (d_θ * Real.sqrt a) (w s_θ) := hdc.symm ▸ hw_zc
  have hw_bs' : IsBiotSavart (d_θ * Real.sqrt a) (w s_θ) (u s_θ) := hdc.symm ▸ hw_bs
  have hJ_mem := (jscaleInv_memLp_bound_abs (by linarith) ha1 hd_θ0 hw_mem').1
  have hZ_mem : MemLp (heatColumn P ν w θ) 2 (B0579.cellMeasure d_θ m) :=
    hJ_mem.const_mul α
  have hJ_zc := hasZeroCirc_jscaleInv_abs (by linarith) ha1 hd_θ0 hw_mem' hw_zc'
  have hZ_zc : HasZeroCirculation d_θ (heatColumn P ν w θ) := by
    refine ⟨hJ_zc.1.const_mul α, ?_⟩
    change ∫ y in B0579.cell d_θ, α * JscaleInv a (w s_θ) y = 0
    rw [integral_const_mul, hJ_zc.2, mul_zero]
  obtain ⟨hJ_bs, hvel_mov⟩ := isBiotSavart_velMov_abs ha0 hd_θ0 hw_bs'
  set u_Z : ℝ × ℝ → Fin 2 → ℂ := fun y j => α * velMovAbs a (u s_θ) y j
  have hZ_bs : IsBiotSavart d_θ (heatColumn P ν w θ) u_Z :=
    isBiotSavart_smul_abs α hJ_bs
  have hZ_ev : (fun y => heatColumn P ν w θ (-y)) =ᵐ[volume.restrict (B0579.cell d_θ)]
      heatColumn P ν w θ := by
    have hw_ev' : (fun x => w s_θ (-x)) =ᵐ[volume.restrict (B0579.cell (d_θ * Real.sqrt a))]
        w s_θ := hdc.symm ▸ hw_ev
    have h0 := ae_smul_sqrt_of_ae_abs ha0 hw_ev'
    refine h0.mono fun y hy => ?_
    have hcoord : (Real.sqrt a * (-y).1, Real.sqrt a * (-y).2) =
        -(Real.sqrt a * y.1, Real.sqrt a * y.2) := by ext <;> simp
    change α * JscaleInv a (w s_θ) (-y) = α * JscaleInv a (w s_θ) y
    have hy' : JscaleInv a (w s_θ) (-y) = JscaleInv a (w s_θ) y := by
      dsimp only [JscaleInv] at hy ⊢
      rw [hcoord, hy]
    rw [hy']
  set h_θ : ℝ × ℝ → ℂ := symEvenAbs (heatColumn P ν w θ)
  have hae_vol : h_θ =ᵐ[volume.restrict (B0579.cell d_θ)] heatColumn P ν w θ :=
    symEven_ae_eq_abs hZ_ev
  have hae_cm : h_θ =ᵐ[B0579.cellMeasure d_θ m] heatColumn P ν w θ :=
    (B0579.cellMeasure_ac d_θ m).ae_le hae_vol
  have hh_mem : MemLp h_θ 2 (B0579.cellMeasure d_θ m) := hZ_mem.ae_eq hae_cm.symm
  have hh_zc : HasZeroCirculation d_θ h_θ :=
    ⟨hZ_zc.1.congr_fun_ae hae_vol.symm, (integral_congr_ae hae_vol).trans hZ_zc.2⟩
  have hh_ev : IsCentrallyEven h_θ := isCentrallyEven_symEven_abs _
  have hh_bs : IsBiotSavart d_θ h_θ u_Z :=
    isBiotSavart_congr_ae_abs hZ_bs hae_vol.symm EventuallyEq.rfl
  have hJ_ae : Jscale a h_θ =ᵐ[volume.restrict (B0579.cell c)] fun x => α * w s_θ x := by
    have hdiv := ae_div_sqrt_of_ae_abs ha0 hae_vol
    rw [hdc] at hdiv
    have hj := jscale_jscaleInv_abs ha0 (w s_θ)
    filter_upwards [hdiv] with x hx
    have hjx := congrFun hj x
    dsimp only [Jscale, heatColumn] at hx hjx ⊢
    change ((a ^ (-2 : ℝ) : ℝ) : ℂ) * h_θ (x.1 / Real.sqrt a, x.2 / Real.sqrt a) = α * w s_θ x
    rw [hx]
    calc ((a ^ (-2 : ℝ) : ℝ) : ℂ) * (α * JscaleInv a (w s_θ) (x.1 / Real.sqrt a, x.2 / Real.sqrt a))
        = α * (((a ^ (-2 : ℝ) : ℝ) : ℂ) *
            JscaleInv a (w s_θ) (x.1 / Real.sqrt a, x.2 / Real.sqrt a)) := by ring
      _ = α * w s_θ x := by rw [hjx]
  -- Bound xNorm d_θ m (heatColumn P ν w θ) via triangle inequality + ctLongComparison + BranchProps
  set W_θ : ℝ := Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re
  have hW_pos : 0 < W_θ := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hθ0 _)
  have hWinv_eq : W_θ⁻¹ = Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re) := by
    dsimp [W_θ]
    rw [mul_inv, ← Real.exp_neg, neg_mul, ← Real.rpow_neg hθ0.le]
  have herr_le3 : ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3) ≤ 3 := by
    have hν6 : (ν ^ 3) ^ 2 / θ ≤ 1 := by
      have h1 : (ν ^ 3) ^ 2 ≤ 1 := by
        have : ν ^ 3 ≤ 1 := pow_le_one₀ hν.le hν1
        exact pow_le_one₀ (by positivity) this
      exact (div_le_one hθ0).2 (h1.trans hθ1)
    have hexp1 : Real.exp (-a₁ * θ / ν ^ 3) ≤ 1 :=
      Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha₁.le) hθ0.le) (by positivity))
    linarith
  have hLong_3 : ENNReal.ofReal W_θ *
      xNorm d_θ m (heatColumn P ν w θ - canonicalPeriodized P ν θ) ≤
      ENNReal.ofReal (3 * C_long) := by
    refine hLong_bd.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have hxZ_tri : xNorm d_θ m (heatColumn P ν w θ) ≤
      xNorm d_θ m (heatColumn P ν w θ - canonicalPeriodized P ν θ) +
        xNorm d_θ m (canonicalPeriodized P ν θ) := by
    have hdiff_mem : MemLp (heatColumn P ν w θ - canonicalPeriodized P ν θ) 2
        (B0579.cellMeasure d_θ m) := hZ_mem.sub hVd_mem
    have heq : heatColumn P ν w θ =
        (heatColumn P ν w θ - canonicalPeriodized P ν θ) + canonicalPeriodized P ν θ := by
      funext y; simp
    unfold xNorm
    conv_lhs => rw [heq]
    exact eLpNorm_add_le hdiff_mem.1 hVd_mem.1 one_le_two
  have hWZ_bd : ENNReal.ofReal W_θ * xNorm d_θ m (heatColumn P ν w θ) ≤
      ENNReal.ofReal (C_br + 3 * C_long) := by
    calc ENNReal.ofReal W_θ * xNorm d_θ m (heatColumn P ν w θ)
        ≤ ENNReal.ofReal W_θ *
            (xNorm d_θ m (heatColumn P ν w θ - canonicalPeriodized P ν θ) +
              xNorm d_θ m (canonicalPeriodized P ν θ)) :=
          mul_le_mul_of_nonneg_left hxZ_tri bot_le
      _ = ENNReal.ofReal W_θ * xNorm d_θ m (heatColumn P ν w θ - canonicalPeriodized P ν θ) +
            ENNReal.ofReal W_θ * xNorm d_θ m (canonicalPeriodized P ν θ) := mul_add _ _ _
      _ ≤ ENNReal.ofReal (3 * C_long) + ENNReal.ofReal C_br := add_le_add hLong_3 hBr_bd
      _ = ENNReal.ofReal (C_br + 3 * C_long) := by
          rw [← ENNReal.ofReal_add (by positivity) hC_br.le]; congr 1; ring
  have hx_hθ : xNorm d_θ m h_θ ≤
      ENNReal.ofReal ((C_br + 3 * C_long) *
        Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) := by
    have hx_eq : xNorm d_θ m h_θ = xNorm d_θ m (heatColumn P ν w θ) :=
      eLpNorm_congr_ae hae_cm
    rw [hx_eq]
    have hscaled := mul_le_mul_of_nonneg_left hWZ_bd (bot_le : 0 ≤ ENNReal.ofReal W_θ⁻¹)
    have hlhs : ENNReal.ofReal W_θ⁻¹ * (ENNReal.ofReal W_θ * xNorm d_θ m (heatColumn P ν w θ)) =
        xNorm d_θ m (heatColumn P ν w θ) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hW_pos.le),
        inv_mul_cancel₀ hW_pos.ne', ENNReal.ofReal_one, one_mul]
    rw [hlhs, ← ENNReal.ofReal_mul (inv_nonneg.2 hW_pos.le), hWinv_eq] at hscaled
    refine hscaled.trans (le_of_eq ?_)
    congr 1; ring
  -- Apply CTEmbeddings to (d_θ, h_θ, u_Z)
  have huZ_bd : velNorm d_θ u_Z ≤
      ENNReal.ofReal (C_emb * (C_br + 3 * C_long) *
        Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) := by
    have hemb := (le_add_self.trans (hEmb d_θ hd_θ1 h_θ hh_mem hh_zc hh_ev u_Z hh_bs)).trans
      (mul_le_mul_of_nonneg_left hx_hθ bot_le)
    rwa [← ENNReal.ofReal_mul (by positivity),
      show C_emb * ((C_br + 3 * C_long) * Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) =
        C_emb * (C_br + 3 * C_long) * Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re) by
        ring] at hemb
  have hkin_bd : kinNorm d_θ h_θ ≤
      ENNReal.ofReal (C_emb * (C_br + 3 * C_long) *
        Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) :=
    (iInf₂_le u_Z hh_bs).trans huZ_bd
  -- Rescale velNorm d_θ u_Z back to velNorm c (u s_θ)
  have huZ_eq : velNorm d_θ u_Z =
      ENNReal.ofReal (‖P.gaugeFactor ν‖⁻¹ * (ν * θ)⁻¹) * velNorm c (u s_θ) := by
    dsimp only [u_Z, α]
    rw [velNorm_smul_abs, norm_inv, hvel_mov, hdc, ← mul_assoc,
      ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _))]
  have hvel_c : velNorm c (u s_θ) ≤
      ENNReal.ofReal (C_emb * (C_br + 3 * C_long) * ‖P.gaugeFactor ν‖ * ν * θ *
        Real.exp (-P.eigenvalue.re * θ) * θ ^ (-P.kappa.re)) := by
    set S_fac : ℝ := ‖P.gaugeFactor ν‖ * (ν * θ)
    have hS_pos : 0 < S_fac := mul_pos (norm_pos_iff.2 hgf_ne) (mul_pos hν hθ0)
    have h1 := mul_le_mul_of_nonneg_left (huZ_eq ▸ huZ_bd) (bot_le : 0 ≤ ENNReal.ofReal S_fac)
    have hlhs : ENNReal.ofReal S_fac *
        (ENNReal.ofReal (‖P.gaugeFactor ν‖⁻¹ * (ν * θ)⁻¹) * velNorm c (u s_θ)) =
        velNorm c (u s_θ) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hS_pos.le]
      have hmul1 : S_fac * (‖P.gaugeFactor ν‖⁻¹ * (ν * θ)⁻¹) = 1 := by
        dsimp [S_fac]
        have := (norm_pos_iff.2 hgf_ne).ne'; have := hν.ne'; have := hθ0.ne'
        field_simp
      rw [hmul1, ENNReal.ofReal_one, one_mul]
    rw [hlhs, ← ENNReal.ofReal_mul hS_pos.le] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1; dsimp [S_fac]; ring
  exact ⟨hh_mem, hh_zc, hh_ev, hJ_ae, hkin_bd, hvel_c⟩

/-! ## 5. Onset-to-core clock bounds and exact exponential integral on `Ioc (onsetAge ν) s_b` -/

private lemma onset_and_core_clock_props {b ν : ℝ} (hb1 : 1 ≤ b) (hν : 0 < ν)
    (hν_qtr : ν ≤ 1 / 4) (hν_9b2 : ν ≤ (9 * b ^ 2)⁻¹) :
    0 < onsetAge ν ∧
      onsetAge ν < clockAge ν b ∧
      clockAge ν b ≤ UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) ∧
      ∀ s ∈ Ioc (onsetAge ν) (clockAge ν b),
        0 < s ∧
        b ≤ clockTheta ν s ∧
        clockTheta ν s ≤ ν⁻¹ ∧
        (2 * ν ^ 2 * clockTheta ν s)⁻¹ ≤ s ∧
        (UnforcedLeray.Train.width ν s)⁻¹ = ν * clockTheta ν s := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  have huo_pos : 0 < onsetAge ν := Real.rpow_pos_of_pos hν _
  -- Show onsetAge ν < clockAge ν b
  have hsqrt_le : ν ^ (1 / 2 : ℝ) ≤ (3 * b)⁻¹ := by
    have h9 : (9 * b ^ 2)⁻¹ = ((3 * b)⁻¹) ^ (2 : ℝ) := by
      rw [Real.rpow_two, inv_pow]; ring
    calc ν ^ (1 / 2 : ℝ)
        ≤ ((9 * b ^ 2)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hν.le hν_9b2 (by norm_num)
      _ = (((3 * b)⁻¹) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [h9]
      _ = (3 * b)⁻¹ := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (3 * b)⁻¹)]
          norm_num
  have hνb_le : ν * b ≤ 1 / 9 := by
    calc ν * b ≤ (9 * b ^ 2)⁻¹ * b := mul_le_mul_of_nonneg_right hν_9b2 hb0.le
      _ = (9 * b)⁻¹ := by field_simp
      _ ≤ 1 / 9 := by
          rw [inv_eq_one_div]
          exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  have huo_lt : onsetAge ν < clockAge ν b := by
    unfold onsetAge clockAge
    rw [lt_div_iff₀ (by positivity)]
    have hprod : ν ^ (-3 / 2 : ℝ) * (ν ^ 2 * b) = b * ν ^ (1 / 2 : ℝ) := by
      have h2 : (ν ^ 2 : ℝ) = ν ^ (2 : ℝ) := (Real.rpow_two ν).symm
      calc ν ^ (-3 / 2 : ℝ) * (ν ^ 2 * b)
          = b * (ν ^ (-3 / 2 : ℝ) * ν ^ (2 : ℝ)) := by rw [h2]; ring
        _ = b * ν ^ (1 / 2 : ℝ) := by
            congr 1; rw [← Real.rpow_add hν]; norm_num
    have hle3 : b * ν ^ (1 / 2 : ℝ) ≤ 1 / 3 := by
      calc b * ν ^ (1 / 2 : ℝ) ≤ b * (3 * b)⁻¹ := mul_le_mul_of_nonneg_left hsqrt_le hb0.le
        _ = 1 / 3 := by field_simp
    linarith
  -- Show clockAge ν b ≤ overlapAge ν (ν ^ (-2 : ℝ))
  have hsb_le_sc : clockAge ν b ≤ UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) := by
    have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
      rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]; ring
    have hsc_eq : UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) = (1 - ν ^ 4) / ν ^ 5 := by
      unfold UnforcedLeray.B0146.overlapAge; rw [hc_sq]; have := hν.ne'; field_simp
    rw [hsc_eq]; unfold clockAge
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hν3_lt : ν ^ 3 ≤ b := by
      have : ν ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hν.le hν_qtr 3
      linarith
    have hmul : ν ^ 5 ≤ ν ^ 2 * b := by
      calc ν ^ 5 = ν ^ 2 * ν ^ 3 := by ring
        _ ≤ ν ^ 2 * b := mul_le_mul_of_nonneg_left hν3_lt (sq_nonneg ν)
    nlinarith [pow_nonneg hν.le 6]
  refine ⟨huo_pos, huo_lt, hsb_le_sc, fun s hs => ?_⟩
  have hs0 : 0 < s := huo_pos.trans hs.1
  have ha_s1 : 1 ≤ clockA ν s := by unfold clockA; nlinarith
  have ha_s0 : 0 < clockA ν s := lt_of_lt_of_le one_pos ha_s1
  have hb_le_θ : b ≤ clockTheta ν s := by
    have ha_le : clockA ν s ≤ clockA ν (clockAge ν b) := by
      unfold clockA; nlinarith [hs.2]
    rw [T22Sub.clockA_clockAge hν hb0] at ha_le
    have hmul : ν * clockA ν s ≤ b⁻¹ := by
      calc ν * clockA ν s ≤ ν * (ν * b)⁻¹ := mul_le_mul_of_nonneg_left ha_le hν.le
        _ = b⁻¹ := by field_simp [hν.ne', hb0.ne']
    unfold clockTheta
    have hinv := inv_anti₀ (mul_pos hν ha_s0) hmul
    rwa [inv_inv] at hinv
  have hθ_le_inv : clockTheta ν s ≤ ν⁻¹ := by
    unfold clockTheta
    exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha_s1)
  have hνs_ge1 : 1 ≤ ν * s := by
    have h1 : 1 ≤ ν ^ (-1 / 2 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
    have h2 : ν ^ (-1 / 2 : ℝ) = ν * onsetAge ν := by
      unfold onsetAge
      calc ν ^ (-1 / 2 : ℝ) = ν ^ ((1 : ℝ) + (-3 / 2 : ℝ)) := by norm_num
        _ = ν ^ (1 : ℝ) * ν ^ (-3 / 2 : ℝ) := Real.rpow_add hν 1 (-3 / 2)
        _ = ν * ν ^ (-3 / 2 : ℝ) := by rw [Real.rpow_one]
    calc (1 : ℝ) ≤ ν ^ (-1 / 2 : ℝ) := h1
      _ = ν * onsetAge ν := h2
      _ ≤ ν * s := mul_le_mul_of_nonneg_left hs.1.le hν.le
  have hs_lower : (2 * ν ^ 2 * clockTheta ν s)⁻¹ ≤ s := by
    have heq : (2 * ν ^ 2 * clockTheta ν s)⁻¹ = (1 + ν * s) / (2 * ν) := by
      unfold clockTheta clockA
      have := hν.ne'; have := ha_s0.ne'
      field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    linarith
  have hwidth_eq : (UnforcedLeray.Train.width ν s)⁻¹ = ν * clockTheta ν s := by
    unfold UnforcedLeray.Train.width clockTheta clockA
    have := hν.ne'; have := ha_s0.ne'
    field_simp
  exact ⟨hs0, hb_le_θ, hθ_le_inv, hs_lower, hwidth_eq⟩

private lemma rpow_mul_exp_le_half_exp {γ θ q : ℝ} (hγ : 0 < γ) (hθ1 : 1 ≤ θ)
    (M : ℕ) (hq : q ≤ (M : ℝ)) :
    θ ^ q * Real.exp (-γ * θ) ≤
      ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp (-(γ / 2) * θ) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
  have hpow_le : θ ^ q ≤ θ ^ M := by
    rw [← Real.rpow_natCast θ M]
    exact Real.rpow_le_rpow_of_exponent_le hθ1 hq
  have hfac := Real.pow_div_factorial_le_exp ((γ / 2) * θ) (by positivity) M
  have hθM : θ ^ M ≤ ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp ((γ / 2) * θ) := by
    have h1 : ((γ / 2) * θ) ^ M ≤ (M.factorial : ℝ) * Real.exp ((γ / 2) * θ) := by
      have hpos_f : (0 : ℝ) < (M.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos M)
      rw [div_le_iff₀ hpos_f] at hfac
      linarith
    have hid : θ ^ M = (2 / γ) ^ M * ((γ / 2) * θ) ^ M := by
      rw [← mul_pow]
      congr 1; field_simp [hγ.ne']
    rw [hid]
    calc (2 / γ) ^ M * ((γ / 2) * θ) ^ M
        ≤ (2 / γ) ^ M * ((M.factorial : ℝ) * Real.exp ((γ / 2) * θ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp ((γ / 2) * θ) := by ring
  calc θ ^ q * Real.exp (-γ * θ)
      ≤ θ ^ M * Real.exp (-γ * θ) := mul_le_mul_of_nonneg_right hpow_le (Real.exp_nonneg _)
    _ ≤ (((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp ((γ / 2) * θ)) * Real.exp (-γ * θ) :=
        mul_le_mul_of_nonneg_right hθM (Real.exp_nonneg _)
    _ = ((M.factorial : ℝ) * (2 / γ) ^ M) * (Real.exp ((γ / 2) * θ) * Real.exp (-γ * θ)) := by
        ring
    _ = ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp (-(γ / 2) * θ) := by
        rw [← Real.exp_add]; congr 2; ring

private lemma lintegral_Ioc_exp_clockTheta_le {γ ν t₁ t₂ : ℝ}
    (hγ : 0 < γ) (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (ht12 : t₁ ≤ t₂) :
    ∫⁻ s in Ioc t₁ t₂,
        ENNReal.ofReal (Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2)) ≤
      ENNReal.ofReal (2 / γ) := by
  let g : ℝ → ℝ := fun s => Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2)
  let Φ : ℝ → ℝ := fun s => (2 / γ) * Real.exp (-(γ / 2) * clockTheta ν s)
  have hθ_cont : ContinuousOn (clockTheta ν) (Icc t₁ t₂) := by
    unfold clockTheta clockA
    refine ContinuousOn.inv₀
      (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))) ?_
    intro s hs
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    exact (mul_pos hν (by positivity : 0 < 1 + ν * s)).ne'
  have hg_cont : ContinuousOn g (Icc t₁ t₂) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hθ_cont)).mul
      (continuousOn_const.mul (hθ_cont.pow 2))
  have hderiv : ∀ s ∈ Icc t₁ t₂, HasDerivAt Φ (g s) s := by
    intro s hs
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have hden_pos : 0 < ν + ν ^ 2 * s := by positivity
    have h_lin : HasDerivAt (fun r : ℝ => ν + ν ^ 2 * r) (ν ^ 2) s := by
      simpa using (hasDerivAt_id s).const_mul (ν ^ 2) |>.const_add ν
    have h_inv := h_lin.inv hden_pos.ne'
    have hθ_eq : clockTheta ν = fun r : ℝ => (ν + ν ^ 2 * r)⁻¹ := by
      funext r; unfold clockTheta clockA; congr 1; ring
    have hθ_deriv : HasDerivAt (clockTheta ν) (-(ν ^ 2 * (clockTheta ν s) ^ 2)) s := by
      rw [hθ_eq]
      refine h_inv.congr_deriv ?_
      rw [neg_div, div_eq_mul_inv, inv_pow]
    have hexp_deriv := ((hθ_deriv.const_mul (-(γ / 2))).exp).const_mul (2 / γ)
    refine hexp_deriv.congr_deriv ?_
    dsimp only [g]
    have hγ_ne : γ ≠ 0 := hγ.ne'
    field_simp [hγ_ne]
  have hg_iiv : IntervalIntegrable g volume t₁ t₂ :=
    hg_cont.intervalIntegrable_of_Icc ht12
  have hg_intOn : IntegrableOn g (Ioc t₁ t₂) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht12).1 hg_iiv
  have hg_nn : 0 ≤ᵐ[volume.restrict (Ioc t₁ t₂)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s _
    dsimp [g]; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_intOn hg_nn,
    ← intervalIntegral.integral_of_le ht12,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hderiv s (uIcc_of_le ht12 ▸ hs))
      hg_iiv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hΦ_t1_nn : 0 ≤ Φ t₁ := by dsimp [Φ]; positivity
  have hθ_t2_nn : 0 ≤ clockTheta ν t₂ := by
    unfold clockTheta clockA
    have : 0 ≤ t₂ := ht₁.trans ht12
    positivity
  have hexp_le1 : Real.exp (-(γ / 2) * clockTheta ν t₂) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) hθ_t2_nn)
  have hΦ_t2_le : Φ t₂ ≤ 2 / γ := by
    dsimp [Φ]
    calc (2 / γ) * Real.exp (-(γ / 2) * clockTheta ν t₂)
        ≤ (2 / γ) * 1 := mul_le_mul_of_nonneg_left hexp_le1 (by positivity)
      _ = 2 / γ := mul_one _
  linarith

/-! ## 6. Main proof (`eq:ct-absolute-stress`, SP 3345-3379) -/

/-- Absolute stress bound (`eq:ct-absolute-stress`, SP 3345-3379) for `k ≤ 1`. -/
theorem ctAbsoluteStress : UnforcedLeray.Short.IIIa.CTAbsoluteStress := by
  intro P hP m hm K hK k hk
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  set γ : ℝ := P.eigenvalue.re
  set κ_re : ℝ := P.kappa.re
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hEmb : ∀ d : ℝ, 1 ≤ d → ∀ f : ℝ × ℝ → ℂ,
      MemLp f 2 (B0579.cellMeasure d m) → HasZeroCirculation d f → IsCentrallyEven f →
        ∀ u, IsBiotSavart d f u →
          ENNReal.ofReal ‖quadQ d f‖ + velNorm d u ≤ ENNReal.ofReal C_emb * xNorm d m f := by
    intro d hd f hf hz hev u hu
    exact (hEmb0 d hd f hf hz hev u hu).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) bot_le)
  have hBranch := T22Sub.ctCanonicalBranchProps P hP m hm
  obtain ⟨b₀_br, _, hBr_all⟩ := hBranch.2.2.1
  obtain ⟨b₀_long, hLong_all⟩ := ctLongComparison P hP m hm
  obtain ⟨b₀_fc, hFC_all⟩ := fullClockLongForward P hP m hm
  obtain ⟨b₀_imp, hImp_all⟩ := T22Sub.ctAbsoluteImpulse P hP m hm K hK k hk
  obtain ⟨C_tr, ν_tr, hC_tr, hν_tr, htr_l2⟩ :=
    T22Sub.trainL2Decay_unconditional 2 (by norm_num : (1 / 2 : ℝ) < 2)
  set b : ℝ := max 1 (max b₀_br (max b₀_long (max b₀_fc b₀_imp)))
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hb_br : b₀_br ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hb_long : b₀_long ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hb_fc : b₀_fc ≤ b :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hb_imp : b₀_imp ≤ b :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  obtain ⟨C_br, hC_br, hBr_est⟩ := hBr_all b hb_br
  obtain ⟨C_long0, a₁, ν_long, ha₁, hν_long, hLong_est⟩ := hLong_all b hb_long
  set C_long : ℝ := max C_long0 1
  have hC_long : 0 < C_long := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨C_fc, ν_fc, hν_fc, hFC_est⟩ := hFC_all b hb_fc
  obtain ⟨C_imp0, ν_imp, hν_imp, hImp_est⟩ := hImp_all b hb_imp
  set C_imp : ℝ := max C_imp0 1
  have hC_imp : 0 < C_imp := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- Derived constants independent of ν and μ
  set C_Z : ℝ := C_emb * (C_br + 3 * C_long)
  have hC_Z : 0 < C_Z := by dsimp [C_Z]; positivity
  set M_pow : ℕ := ⌈3 - κ_re⌉₊
  set M_exp : ℝ := (M_pow.factorial : ℝ) * (2 / γ) ^ M_pow
  have hM_exp : 0 < M_exp := by
    dsimp [M_exp]
    exact mul_pos (Nat.cast_pos.2 (Nat.factorial_pos M_pow)) (pow_pos (div_pos two_pos hγ) M_pow)
  set C_part1 : ℝ := 16 * C_tr * C_Z * M_exp * (2 / γ)
  have hC_part1 : 0 < C_part1 := by dsimp [C_part1]; positivity
  set K_b : ℝ := C_Z * Real.exp (-γ * b) * b ^ (-κ_re)
  have hK_b : 0 < K_b := mul_pos (mul_pos hC_Z (Real.exp_pos _)) (Real.rpow_pos_of_pos hb0 _)
  set C_part2 : ℝ := C_imp * b ^ (4 : ℝ) * K_b
  have hC_part2 : 0 < C_part2 := by
    dsimp [C_part2]; exact mul_pos (mul_pos hC_imp (Real.rpow_pos_of_pos hb0 _)) hK_b
  set C : ℝ := C_part1 + C_part2
  set ν₀ : ℝ := min ν_long (min ν_fc (min ν_imp (min ν_tr (min (1 / 4) ((9 * b ^ 2)⁻¹)))))
  have hν₀ : 0 < ν₀ :=
    lt_min hν_long (lt_min hν_fc (lt_min hν_imp
      (lt_min hν_tr (lt_min (by norm_num) (inv_pos.2 (by positivity))))))
  refine ⟨C, ν₀, hν₀, fun ν hν tr htr w u hw μ hμ => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_long_le : ν ≤ ν_long := hν.2.trans (min_le_left _ _)
  have hν_fc_le : ν ≤ ν_fc := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_imp_le : ν ≤ ν_imp :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_tr_le : ν ≤ ν_tr :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hν_qtr : ν ≤ 1 / 4 :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hν_9b2 : ν ≤ (9 * b ^ 2)⁻¹ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  have hν3_le_b : ν ^ 3 ≤ b := by
    have : ν ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hν_pos.le hν_qtr 3
    linarith
  have hb_le_inv : b ≤ ν⁻¹ := by
    have hνb : ν * b ≤ 1 := by
      calc ν * b ≤ (9 * b ^ 2)⁻¹ * b := mul_le_mul_of_nonneg_right hν_9b2 hb0.le
        _ = (9 * b)⁻¹ := by field_simp
        _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    calc b = ν⁻¹ * (ν * b) := by field_simp [hν_pos.ne']
      _ ≤ ν⁻¹ * 1 := mul_le_mul_of_nonneg_left hνb (inv_nonneg.2 hν_pos.le)
      _ = ν⁻¹ := mul_one _
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  obtain ⟨hprep_mem, hprep_zc, hprep_ev⟩ := hBranch.1 ν ⟨hν_pos, hν1⟩
  obtain ⟨hσ_pos, hσ_lt⟩ := hK.2 μ hμ
  set σ : ℝ := μ.re
  set p_k : ℝ := σ + 3 / 2 + (k : ℝ) / 2
  have hk_nn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk_le1 : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  have hp_gt : 3 / 2 < p_k := by dsimp [p_k]; linarith
  have hp_lt : p_k < 9 / 4 := by dsimp [p_k]; linarith
  have hscaleA_nn : 0 ≤ scaleA P ν μ := by
    unfold scaleA; positivity
  have hscaleA_eq : ‖P.gaugeFactor ν‖ * ν ^ (2 + 2 * p_k) = scaleA P ν μ * ν ^ k := by
    unfold scaleA
    have hdiv : ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ) = ν ^ (5 + 2 * σ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hν_pos.le, neg_neg, ← Real.rpow_add hν_pos]
      congr 1; ring
    have hcomb : ν ^ (5 + 2 * σ) * (ν ^ k : ℝ) = ν ^ (2 + 2 * p_k) := by
      rw [← Real.rpow_natCast ν k, ← Real.rpow_add hν_pos]
      congr 1; dsimp [p_k]; ring
    calc ‖P.gaugeFactor ν‖ * ν ^ (2 + 2 * p_k)
        = ‖P.gaugeFactor ν‖ * (ν ^ (5 + 2 * σ) * ν ^ k) := by rw [hcomb]
      _ = ‖P.gaugeFactor ν‖ * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k := by rw [hdiv]; ring
      _ = ‖P.gaugeFactor ν‖ * ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ) * ν ^ k := by ring
  -- Helper applying core_heatDatum_and_vel_bound for any θ ∈ [b, ν⁻¹]
  have hcore_at : ∀ θ : ℝ, b ≤ θ → θ ≤ ν⁻¹ →
      MemLp (symEvenAbs (heatColumn P ν w θ)) 2 (B0579.cellMeasure (dOfTheta ν θ) m) ∧
      HasZeroCirculation (dOfTheta ν θ) (symEvenAbs (heatColumn P ν w θ)) ∧
      IsCentrallyEven (symEvenAbs (heatColumn P ν w θ)) ∧
      (Jscale (ν * θ)⁻¹ (symEvenAbs (heatColumn P ν w θ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun x => (P.gaugeFactor ν)⁻¹ * w (clockAge ν θ) x) ∧
      kinNorm (dOfTheta ν θ) (symEvenAbs (heatColumn P ν w θ)) ≤
        ENNReal.ofReal (C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re)) ∧
      velNorm c (u (clockAge ν θ)) ≤
        ENNReal.ofReal (C_Z * ‖P.gaugeFactor ν‖ * ν * θ * Real.exp (-γ * θ) * θ ^ (-κ_re)) := by
    intro θ hθb hθν
    have hθ0 : 0 < θ := lt_of_lt_of_le hb0 hθb
    have hs_θ0 : 0 ≤ clockAge ν θ := T22Sub.clockAge_nonneg hν_pos hθ0 hθν
    have hbs_θ : b ≤ clockTheta ν (clockAge ν θ) := by
      rw [T22Sub.clockTheta_clockAge hν_pos hθ0]; exact hθb
    have hw_zc_θ : HasZeroCirculation c (w (clockAge ν θ)) :=
      zeroCirculationPreserved ν c m hc_pos (by linarith) tr 0
        (preparedDatum P ν) w u hw hprep_zc (clockAge ν θ) hs_θ0
    have hw_ev_θ : (fun x => w (clockAge ν θ) (-x)) =ᵐ[volume.restrict (B0579.cell c)]
        w (clockAge ν θ) :=
      flow_even_ae_of_longForward hν_pos (by linarith) hprep_mem hprep_ev hw hs_θ0 hbs_θ
        (fun f₀ hf₀ hzc₀ w₀ u₀ hw₀ =>
          (hFC_est ν ⟨hν_pos, hν_fc_le⟩ tr htr).2 0 (clockAge ν θ) le_rfl hs_θ0 hbs_θ
            f₀ hf₀ hzc₀ w₀ u₀ hw₀)
    have hd_θ1 : 1 ≤ dOfTheta ν θ := T22Sub.one_le_dOfTheta hν_pos (hν3_le_b.trans hθb)
    have hVd_mem := (hBranch.2.1 ν θ hν_pos hθ0 hd_θ1).1
    have hBr_θ := hBr_est ν ⟨hν_pos, hν1⟩ θ hθb hd_θ1
    have hLong_θ0 := (hLong_est ν ⟨hν_pos, hν_long_le⟩ tr htr).2 w u hw θ hθb hθν
    have hLong_θ : ENNReal.ofReal (Real.exp (γ * θ) * θ ^ κ_re) *
        xNorm (dOfTheta ν θ) m (heatColumn P ν w θ - canonicalPeriodized P ν θ) ≤
        ENNReal.ofReal (C_long * (ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3))) := by
      refine hLong_θ0.trans (ENNReal.ofReal_le_ofReal ?_)
      have hsum_nn : 0 ≤ ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3) := by positivity
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hsum_nn
    exact core_heatDatum_and_vel_bound hν_pos hν1 hm hb1 hθb hθν hν3_le_b
      hC_emb hC_br hC_long ha₁ hEmb
      (hw.memX _ hs_θ0) hw_zc_θ (hw.biotSavart _ hs_θ0) hw_ev_θ hVd_mem hBr_θ hLong_θ
  -- Split Ioi (onsetAge ν) at s_b = clockAge ν b
  set s_b : ℝ := clockAge ν b
  obtain ⟨huo_pos, huo_lt_sb, hsb_le_sc, hclock_Ioc⟩ :=
    onset_and_core_clock_props hb1 hν_pos hν_qtr hν_9b2
  set F_int : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u s) s
  have hcov : Ioi (onsetAge ν) ⊆ Ioc (onsetAge ν) s_b ∪ Ioi s_b := fun s hs =>
    if hsb : s ≤ s_b then Or.inl ⟨hs, hsb⟩ else Or.inr (not_le.1 hsb)
  have hsplit : ∫⁻ s in Ioi (onsetAge ν), F_int s ≤
      (∫⁻ s in Ioc (onsetAge ν) s_b, F_int s) + (∫⁻ s in Ioi s_b, F_int s) :=
    (lintegral_mono_set hcov).trans (lintegral_union_le _ _ _)
  -- Part 1: Bound on Ioc (onsetAge ν) s_b
  have hI1 : ∫⁻ s in Ioc (onsetAge ν) s_b, F_int s ≤
      ENNReal.ofReal (C_part1 * scaleA P ν μ * ν ^ k) := by
    set K₁ : ℝ := 16 * C_tr * C_Z * M_exp * scaleA P ν μ * ν ^ k
    have hK₁_nn : 0 ≤ K₁ := by dsimp [K₁]; positivity
    have hpt1 : ∀ s ∈ Ioc (onsetAge ν) s_b,
        F_int s ≤ ENNReal.ofReal K₁ *
          ENNReal.ofReal (Real.exp (-(γ / 2) * clockTheta ν s) *
            (ν ^ 2 * (clockTheta ν s) ^ 2)) := by
      intro s hs
      obtain ⟨hs_pos, hb_le_θ, hθ_le_inv, hs_lower, hwidth_eq⟩ := hclock_Ioc s hs
      set θ : ℝ := clockTheta ν s
      have hθ1 : 1 ≤ θ := hb1.trans hb_le_θ
      have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
      have ha_s : 0 < clockA ν s := by unfold clockA; positivity
      have hs_eq : clockAge ν θ = s := T22Sub.clockAge_clockTheta hν_pos ha_s
      have hvel_s : velNorm c (u s) ≤
          ENNReal.ofReal (C_Z * ‖P.gaugeFactor ν‖ * ν * θ * Real.exp (-γ * θ) * θ ^ (-κ_re)) := by
        have h := (hcore_at θ hb_le_θ hθ_le_inv).2.2.2.2.2
        rwa [hs_eq] at h
      have hsc_s : s ≤ UnforcedLeray.B0146.overlapAge ν c := hs.2.trans hsb_le_sc
      have hl2_s : UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal (C_tr * ν * θ) := by
        have h := (htr_l2 ν hν_pos hν_tr_le tr htr s hs_pos.le).1 hsc_s
        rw [hwidth_eq, ← mul_assoc] at h
        exact h
      have hs_abs := sAbs_le_cellL2_mul_velNorm_abs hν_pos tr μ (u s) hs_pos
        (hw.biotSavart s hs_pos.le).1
      -- Bound s ^ (-p_k) ≤ 8 * ν ^ (2 * p_k) * θ ^ p_k
      have hp_pos : 0 < p_k := by linarith
      have hp_le3 : p_k ≤ 3 := by linarith
      have hs_pow_bd : s ^ (-3 / 2 - (k : ℝ) / 2) * (2 * ν ^ 2 * s ^ (-σ)) ≤
          16 * ν ^ (2 + 2 * p_k) * θ ^ p_k := by
        have hs_comb : s ^ (-3 / 2 - (k : ℝ) / 2) * s ^ (-σ) = (s⁻¹) ^ p_k := by
          rw [← Real.rpow_add hs_pos, Real.inv_rpow hs_pos.le, ← Real.rpow_neg hs_pos.le]
          congr 1; dsimp [p_k]; ring
        have hsinv_le : s⁻¹ ≤ 2 * ν ^ 2 * θ := by
          have h := inv_anti₀ (by positivity : 0 < (2 * ν ^ 2 * θ)⁻¹) hs_lower
          rwa [inv_inv] at h
        have hsinv_pow : (s⁻¹) ^ p_k ≤ 8 * ν ^ (2 * p_k) * θ ^ p_k := by
          calc (s⁻¹) ^ p_k
              ≤ (2 * ν ^ 2 * θ) ^ p_k :=
                Real.rpow_le_rpow (inv_nonneg.2 hs_pos.le) hsinv_le hp_pos.le
            _ = 2 ^ p_k * (ν ^ 2) ^ p_k * θ ^ p_k := by
                rw [Real.mul_rpow (by positivity) hθ0.le, Real.mul_rpow (by norm_num) (sq_nonneg ν)]
            _ ≤ 8 * (ν ^ 2) ^ p_k * θ ^ p_k := by
                have h2 : (2 : ℝ) ^ p_k ≤ 8 := by
                  calc (2 : ℝ) ^ p_k ≤ (2 : ℝ) ^ (3 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp_le3
                    _ = 8 := by norm_num
                gcongr
            _ = 8 * ν ^ (2 * p_k) * θ ^ p_k := by
                congr 2; rw [← Real.rpow_natCast ν 2, ← Real.rpow_mul hν_pos.le]; push_cast; rfl
        have hν_comb : ν ^ 2 * ν ^ (2 * p_k) = ν ^ (2 + 2 * p_k) := by
          rw [← Real.rpow_natCast ν 2, ← Real.rpow_add hν_pos]; push_cast; rfl
        calc s ^ (-3 / 2 - (k : ℝ) / 2) * (2 * ν ^ 2 * s ^ (-σ))
            = 2 * ν ^ 2 * (s ^ (-3 / 2 - (k : ℝ) / 2) * s ^ (-σ)) := by ring
          _ = 2 * ν ^ 2 * (s⁻¹) ^ p_k := by rw [hs_comb]
          _ ≤ 2 * ν ^ 2 * (8 * ν ^ (2 * p_k) * θ ^ p_k) :=
              mul_le_mul_of_nonneg_left hsinv_pow (by positivity)
          _ = 16 * (ν ^ 2 * ν ^ (2 * p_k)) * θ ^ p_k := by ring
          _ = 16 * ν ^ (2 + 2 * p_k) * θ ^ p_k := by rw [hν_comb]
      have hθ_exp_bd : θ ^ p_k * θ ^ (-κ_re) * Real.exp (-γ * θ) ≤
          M_exp * Real.exp (-(γ / 2) * θ) := by
        have hθ_comb : θ ^ p_k * θ ^ (-κ_re) = θ ^ (p_k - κ_re) := by
          rw [← Real.rpow_add hθ0, ← sub_eq_add_neg]
        have hq_le : p_k - κ_re ≤ (M_pow : ℝ) :=
          (by linarith : p_k - κ_re ≤ 3 - κ_re).trans (Nat.le_ceil _)
        rw [hθ_comb]
        exact rpow_mul_exp_le_half_exp hγ hθ1 M_pow hq_le
      calc F_int s
          ≤ ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
              (ENNReal.ofReal (2 * ν ^ 2 * s ^ (-σ)) *
                UnforcedLeray.Train.cellL2 c (tr.v s) * velNorm c (u s)) :=
            mul_le_mul_of_nonneg_left hs_abs bot_le
        _ ≤ ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) *
              (ENNReal.ofReal (2 * ν ^ 2 * s ^ (-σ)) *
                ENNReal.ofReal (C_tr * ν * θ) *
                ENNReal.ofReal (C_Z * ‖P.gaugeFactor ν‖ * ν * θ *
                  Real.exp (-γ * θ) * θ ^ (-κ_re))) := by
            gcongr
        _ = ENNReal.ofReal ((s ^ (-3 / 2 - (k : ℝ) / 2) * (2 * ν ^ 2 * s ^ (-σ))) *
              (C_tr * ν * θ) *
              (C_Z * ‖P.gaugeFactor ν‖ * ν * θ * Real.exp (-γ * θ) * θ ^ (-κ_re))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (K₁ * (Real.exp (-(γ / 2) * θ) * (ν ^ 2 * θ ^ 2))) := by
            apply ENNReal.ofReal_le_ofReal
            calc (s ^ (-3 / 2 - (k : ℝ) / 2) * (2 * ν ^ 2 * s ^ (-σ))) *
                  (C_tr * ν * θ) *
                  (C_Z * ‖P.gaugeFactor ν‖ * ν * θ * Real.exp (-γ * θ) * θ ^ (-κ_re))
                ≤ (16 * ν ^ (2 + 2 * p_k) * θ ^ p_k) *
                    (C_tr * ν * θ) *
                    (C_Z * ‖P.gaugeFactor ν‖ * ν * θ * Real.exp (-γ * θ) * θ ^ (-κ_re)) := by
                  gcongr
              _ = 16 * C_tr * C_Z * (‖P.gaugeFactor ν‖ * ν ^ (2 + 2 * p_k)) *
                    (θ ^ p_k * θ ^ (-κ_re) * Real.exp (-γ * θ)) * (ν ^ 2 * θ ^ 2) := by ring
              _ = 16 * C_tr * C_Z * (scaleA P ν μ * ν ^ k) *
                    (θ ^ p_k * θ ^ (-κ_re) * Real.exp (-γ * θ)) * (ν ^ 2 * θ ^ 2) := by
                  rw [hscaleA_eq]
              _ ≤ 16 * C_tr * C_Z * (scaleA P ν μ * ν ^ k) *
                    (M_exp * Real.exp (-(γ / 2) * θ)) * (ν ^ 2 * θ ^ 2) := by
                  gcongr
              _ = K₁ * (Real.exp (-(γ / 2) * θ) * (ν ^ 2 * θ ^ 2)) := by dsimp [K₁]; ring
        _ = ENNReal.ofReal K₁ *
              ENNReal.ofReal (Real.exp (-(γ / 2) * θ) * (ν ^ 2 * θ ^ 2)) :=
            ENNReal.ofReal_mul hK₁_nn
    calc ∫⁻ s in Ioc (onsetAge ν) s_b, F_int s
        ≤ ∫⁻ s in Ioc (onsetAge ν) s_b,
            ENNReal.ofReal K₁ *
              ENNReal.ofReal (Real.exp (-(γ / 2) * clockTheta ν s) *
                (ν ^ 2 * (clockTheta ν s) ^ 2)) :=
          setLIntegral_mono' measurableSet_Ioc hpt1
      _ = ENNReal.ofReal K₁ *
            ∫⁻ s in Ioc (onsetAge ν) s_b,
              ENNReal.ofReal (Real.exp (-(γ / 2) * clockTheta ν s) *
                (ν ^ 2 * (clockTheta ν s) ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K₁ * ENNReal.ofReal (2 / γ) :=
          mul_le_mul_of_nonneg_left
            (lintegral_Ioc_exp_clockTheta_le hγ hν_pos huo_pos.le huo_lt_sb.le) bot_le
      _ = ENNReal.ofReal (C_part1 * scaleA P ν μ * ν ^ k) := by
          rw [← ENNReal.ofReal_mul hK₁_nn]
          congr 1; dsimp [K₁, C_part1]; ring
  -- Part 2: Bound on Ioi s_b via restart + gauge rescaling + ctAbsoluteImpulse at r = b
  have hI2 : ∫⁻ s in Ioi s_b, F_int s ≤
      ENNReal.ofReal (C_part2 * scaleA P ν μ * ν ^ k) := by
    obtain ⟨hhb_mem, hhb_zc, hhb_ev, hJb_ae, hhb_kin, _⟩ := hcore_at b le_rfl hb_le_inv
    set h_b : ℝ × ℝ → ℂ := symEvenAbs (heatColumn P ν w b)
    have hs_b0 : 0 ≤ s_b := T22Sub.clockAge_nonneg hν_pos hb0 hb_le_inv
    set w_sc : ℝ → ℝ × ℝ → ℂ := fun s x => (P.gaugeFactor ν)⁻¹ * w s x
    set u_sc : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun s x j => (P.gaugeFactor ν)⁻¹ * u s x j
    have hw_sc : IsLinearisedFlow ν c m tr s_b (Jscale (ν * b)⁻¹ h_b) w_sc u_sc :=
      isLinearisedFlow_congr_initial_ae_abs
        (isLinearisedFlow_smul_abs (P.gaugeFactor ν)⁻¹ (hw.restart hs_b0))
        hJb_ae.symm
    have himp := hImp_est ν ⟨hν_pos, hν_imp_le⟩ tr htr b hb0 le_rfl
      h_b hhb_mem hhb_zc hhb_ev w_sc u_sc hw_sc μ hμ
    have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν_pos
    have hu_eq : ∀ s : ℝ, u s = fun x j => P.gaugeFactor ν * u_sc s x j := by
      intro s; funext x j; dsimp [u_sc]
      rw [← mul_assoc, mul_inv_cancel₀ hgf_ne, one_mul]
    have hpt_gf : ∀ s : ℝ, F_int s =
        ENNReal.ofReal ‖P.gaugeFactor ν‖ *
          (ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u_sc s) s) := by
      intro s
      dsimp only [F_int]
      conv_lhs => rw [hu_eq s, sAbs_smul]
      exact mul_left_comm _ _ _
    have hmax1 : max 1 ((ν ^ 3 / b) ^ (1 / 4 : ℝ)) = 1 := by
      apply max_eq_left
      have hdiv1 : ν ^ 3 / b ≤ 1 := (div_le_one hb0).2 hν3_le_b
      calc (ν ^ 3 / b) ^ (1 / 4 : ℝ)
          ≤ (1 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hdiv1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hb_pow_le : b ^ (σ + 5 / 2 + (k : ℝ) / 2) ≤ b ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have hfac_le : ENNReal.ofReal (C_imp0 * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k *
          b ^ (σ + 5 / 2 + (k : ℝ) / 2) * max 1 ((ν ^ 3 / b) ^ (1 / 4 : ℝ))) ≤
        ENNReal.ofReal (C_imp * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * b ^ (4 : ℝ)) := by
      rw [hmax1, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : C_imp0 ≤ C_imp := le_max_left _ _
      have hbase_nn : 0 ≤ (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k := by positivity
      calc C_imp0 * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * b ^ (σ + 5 / 2 + (k : ℝ) / 2)
          = C_imp0 * ((ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k) *
              b ^ (σ + 5 / 2 + (k : ℝ) / 2) := by ring
        _ ≤ C_imp * ((ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k) * b ^ (4 : ℝ) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hbase_nn) hb_pow_le
              (Real.rpow_nonneg hb0.le _) (by positivity)
        _ = C_imp * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * b ^ (4 : ℝ) := by ring
    calc ∫⁻ s in Ioi s_b, F_int s
        = ∫⁻ s in Ioi s_b, ENNReal.ofReal ‖P.gaugeFactor ν‖ *
            (ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u_sc s) s) :=
          lintegral_congr hpt_gf
      _ = ENNReal.ofReal ‖P.gaugeFactor ν‖ *
            ∫⁻ s in Ioi s_b, ENNReal.ofReal (s ^ (-3 / 2 - (k : ℝ) / 2)) * sAbs tr μ (u_sc s) s :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ‖P.gaugeFactor ν‖ *
            (ENNReal.ofReal (C_imp * (ν ^ (3 + 2 * σ) / ν ^ (-2 : ℝ)) * ν ^ k * b ^ (4 : ℝ)) *
              ENNReal.ofReal K_b) :=
          mul_le_mul_of_nonneg_left (himp.trans (mul_le_mul hfac_le hhb_kin bot_le bot_le)) bot_le
      _ = ENNReal.ofReal (C_part2 * scaleA P ν μ * ν ^ k) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (norm_nonneg _)]
          congr 1
          unfold scaleA
          dsimp [C_part2]
          ring
  -- Sum Part 1 and Part 2
  calc ∫⁻ s in Ioi (onsetAge ν), F_int s
      ≤ (∫⁻ s in Ioc (onsetAge ν) s_b, F_int s) + (∫⁻ s in Ioi s_b, F_int s) := hsplit
    _ ≤ ENNReal.ofReal (C_part1 * scaleA P ν μ * ν ^ k) +
          ENNReal.ofReal (C_part2 * scaleA P ν μ * ν ^ k) := add_le_add hI1 hI2
    _ = ENNReal.ofReal (C * scaleA P ν μ * ν ^ k) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; dsimp [C]; ring

end UnforcedLeray.Short.IIIa
