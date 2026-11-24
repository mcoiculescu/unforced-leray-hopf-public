import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.SepComm.Defs
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2/1/2`: Order-0 difference bound `YBWidth.sepCommMainDiff0`

Source `the November 2 reference manuscript`
lines 5415-5427, SP 3735-3766. Proves `YBWidth.SepCommMainDiff0` on the transition annulus
`ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` by comparing `sepW` and `sepVmu0` at kernel derivative
order `j = 1` via `YBWidth.sepKernelDiffIter 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIIa

namespace YBWidth

open YBComm PhasePrim

private theorem scale_iter1 (i j : Fin 3) (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) (u : Space) :
    iteratedFDeriv ℝ 1 (fun x => IIIa.heatLerayK t i j x) (ε⁻¹ • u) =
      ε ^ 4 • iteratedFDeriv ℝ 1 (fun x => IIIa.heatLerayK (t * ε ^ 2) i j x) u := by
  have hK1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun x => IIIa.heatLerayK 1 i j x) :=
    (IIIa.heatLerayKSmoothAll 1 one_pos i j).of_le (by norm_cast)
  have hs : 0 < t * ε ^ 2 := by positivity
  rw [IIIa.l2_iteratedFDeriv_scale i j 1 t ht _ hK1,
    IIIa.l2_iteratedFDeriv_scale i j 1 (t * ε ^ 2) hs u hK1, smul_smul]
  have hsq : Real.sqrt (t * ε ^ 2) = Real.sqrt t * ε := by
    rw [Real.sqrt_mul ht.le, Real.sqrt_sq hε.le]
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have harg : ((Real.sqrt t)⁻¹ * ε⁻¹) • u = (Real.sqrt (t * ε ^ 2))⁻¹ • u := by
    rw [hsq, mul_inv]
  rw [harg]
  have h1 : ((ε : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) = (ε ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    have : (((2 : ℕ) : ℝ) * (-(3 / 2 : ℝ))) = -((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg hε.le, Real.rpow_natCast]
  have hcoef : t ^ (-(3 / 2 : ℝ)) * (Real.sqrt t)⁻¹ ^ 1 =
      ε ^ 4 * ((t * ε ^ 2) ^ (-(3 / 2 : ℝ)) * (Real.sqrt (t * ε ^ 2))⁻¹ ^ 1) := by
    rw [pow_one, pow_one, hsq, mul_inv, Real.mul_rpow ht.le (sq_nonneg ε), h1]
    field_simp
  rw [hcoef, smul_smul]

private theorem fderiv_heatLerayK_scale (i j : Fin 3) (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (u : Space) (k : Fin 3) :
    fderiv ℝ (fun x => IIIa.heatLerayK t i j x) (ε⁻¹ • u) (coordinateVector k) =
      ε ^ 4 * fderiv ℝ (fun x => IIIa.heatLerayK (t * ε ^ 2) i j x) u (coordinateVector k) := by
  have h := congrArg (fun M => M ![coordinateVector k]) (scale_iter1 i j t ε ht hε u)
  simpa [iteratedFDeriv_one_apply] using h

/-- The rescaled order-0 integrand of `sepW` on `(λ, w)`-space. -/
private def mpHW0 (ν ε : ℝ) (μ : ℂ) (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (xo : Space)
    (i : Fin 3) (p : ℝ × ((ℝ × ℝ) × ℝ)) : ℂ :=
  -2 * ((p.1 : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
    ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2) * ε ^ 2) i j x)
      (xo - p.1 • (!₂[p.2.1.1, p.2.1.2, ε * p.2.2] : Space)) (coordinateVector k) : ℝ) : ℂ) *
        ((G p.2.1 p.2.2 j k : ℝ) : ℂ))

private theorem mpHW0_scale (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) (μ : ℂ)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (xo : Space) (i : Fin 3) (l : ℝ)
    (hl : l ∈ Ioo (0 : ℝ) 1) (z : Space) :
    IIIa.sepDiffF ν μ (IIIa.thinSource ε (IIIa.meanLift G)) τ (l, z) (ε⁻¹ • xo) i =
      (ε : ℂ) ^ 4 * mpHW0 ν ε μ G xo i (l, ((ε * z 0, ε * z 1), z 2)) := by
  have ht : 0 < ν * (1 - l ^ 2) := mul_pos hν (by nlinarith [hl.1, hl.2])
  have harg : ε⁻¹ • xo - l • z = ε⁻¹ • (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)) := by
    ext n
    fin_cases n <;> simp <;> field_simp
  unfold IIIa.sepDiffF mpHW0
  simp only
  rw [harg]
  have hsrc : ∀ j k : Fin 3,
      IIIa.thinSource ε (IIIa.meanLift G) (τ + 2 * Real.log l) z j k =
        G (ε * z 0, ε * z 1) (z 2) j k := fun _ _ => rfl
  have key : ∀ (j k : Fin 3),
      (fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
        (ε⁻¹ • (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space))) (coordinateVector k) : ℝ) =
      ε ^ 4 * fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x)
        (xo - l • (!₂[ε * z 0, ε * z 1, ε * z 2] : Space)) (coordinateVector k) :=
    fun j k => fderiv_heatLerayK_scale i j _ ε ht hε _ k
  simp only [hsrc, key, Complex.ofReal_mul, Complex.ofReal_pow]
  have hs : ∀ (a : ℂ) (f : Fin 3 → Fin 3 → ℂ), ∑ j : Fin 3, ∑ k : Fin 3, a * f j k =
      a * ∑ j : Fin 3, ∑ k : Fin 3, f j k := by
    intro a f; simp [Finset.mul_sum]
  simp only [mul_assoc, hs]
  ring

private theorem mp_W0_eval (ν c ε ρo ρi : ℝ) (μ : ℂ) (hν : 0 < ν) (hc : 0 < c)
    (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) (i : Fin 3) :
    IIIa.sepW ν μ (IIIa.thinSource ε (IIIa.meanLift G)) (ε⁻¹ • xo) τ i =
      (ε : ℂ) ^ 2 * ∫ p, mpHW0 ν ε μ G xo i p ∂IIIa.mpRho2 ∧
    Integrable (mpHW0 ν ε μ G xo i) IIIa.mpRho2 := by
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  have hsrc : IIIa.IsSepSource (2 * ε * c) (ρo / ε) T :=
    IIIa.t17s_isSepSource ε c ρo hε hc _ (fun i' j' =>
      (hGm i' j').comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop))
      (fun _ _ _ => rfl) (fun x' Y q h => hGs x' Y h)
  have hD : 0 < ρi / ε - ρo / ε := by
    have : 0 < ρi - ρo := by linarith
    rw [← sub_div]; positivity
  have hy : ρi / ε ≤ Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) := by
    have h2 : Real.sqrt ((ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2) =
        ε⁻¹ * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
      have : (ε⁻¹ • xo) 0 ^ 2 + (ε⁻¹ • xo) 1 ^ 2 = (ε⁻¹) ^ 2 * (xo 0 ^ 2 + xo 1 ^ 2) := by
        simp only [PiLp.smul_apply, smul_eq_mul]; ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hε.le)]
    rw [h2, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hfinN : ∫⁻ w : (ℝ × ℝ) × ℝ, ENNReal.ofReal (IIIa.tensorNorm (G w.1 w.2)) < ⊤ :=
    hint.lintegral_lt_top
  have hfin : IIIa.sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (IIIa.srcNorm T) τ (ε⁻¹ • xo) < ⊤ := by
    refine IIIa.t17s_sepDom_lt_top (2 * μ.re + 2) (by linarith) _ hD _ τ _ ?_
    simp_rw [show T = IIIa.thinSource ε (IIIa.meanLift G) from rfl,
      IIIa.mp_src_lintegral ε hε G hGm]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
      mul_one]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hfinN
  obtain ⟨hev, _⟩ := IIIa.t17s_local IIIa.sepKernelBounds ν hν μ (ρo / ε) (ρi / ε) (2 * ε * c)
    (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) T hsrc τ (ε⁻¹ • xo) hy hfin
  obtain ⟨hFint, hWeq⟩ := hev.self_of_nhds
  have hFi : Integrable (fun p => IIIa.sepDiffF ν μ T τ p (ε⁻¹ • xo) i) IIIa.sepDiffRho :=
    (integrable_pi_iff.mp hFint) i
  have h1 : IIIa.sepW ν μ T (ε⁻¹ • xo) τ i =
      ∫ p, IIIa.sepDiffF ν μ T τ p (ε⁻¹ • xo) i ∂IIIa.sepDiffRho := by
    rw [hWeq, eval_integral (integrable_pi_iff.mp hFint) i]
  have h2 : ∀ᵐ p ∂IIIa.sepDiffRho,
      IIIa.sepDiffF ν μ T τ p (ε⁻¹ • xo) i =
        (ε : ℂ) ^ 4 * mpHW0 ν ε μ G xo i (Prod.map (id : ℝ → ℝ) (IIIa.mpPsi ε hε) p) := by
    filter_upwards [IIIa.sepDiffRho_ae_mem] with p hp
    exact mpHW0_scale ν ε hν hε μ G τ xo i p.1 hp p.2
  have hc2 : ENNReal.ofReal (ε⁻¹) ^ 2 ≠ 0 := by
    have : ENNReal.ofReal ε⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hε)).ne'
    exact pow_ne_zero _ this
  have hc2' : ENNReal.ofReal (ε⁻¹) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hε4 : (ε : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hε.ne')
  have hmapint : Integrable (mpHW0 ν ε μ G xo i) IIIa.mpRho2 := by
    have h3 : Integrable (fun p => mpHW0 ν ε μ G xo i (Prod.map (id : ℝ → ℝ) (IIIa.mpPsi ε hε) p))
        IIIa.sepDiffRho := by
      have := hFi.const_mul ((ε : ℂ) ^ 4)⁻¹
      refine this.congr ?_
      filter_upwards [h2] with p hp
      rw [hp, ← mul_assoc, inv_mul_cancel₀ hε4, one_mul]
    have h4 := (IIIa.mp_Psi_embedding ε hε).integrable_map_iff
      (g := mpHW0 ν ε μ G xo i) (μ := IIIa.sepDiffRho) |>.2 h3
    rw [IIIa.mp_Psi_map ε hε, integrable_smul_measure hc2 hc2'] at h4
    exact h4
  refine ⟨?_, hmapint⟩
  rw [h1, integral_congr_ae h2, integral_const_mul]
  have h5 := (IIIa.mp_Psi_embedding ε hε).integral_map (μ := IIIa.sepDiffRho) (mpHW0 ν ε μ G xo i)
  rw [IIIa.mp_Psi_map ε hε, integral_smul_measure] at h5
  have h6 : (ENNReal.ofReal (ε⁻¹) ^ 2).toReal = (ε⁻¹) ^ 2 := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.2 hε.le)]
  rw [h6] at h5
  have h7 : ∫ p, mpHW0 ν ε μ G xo i (Prod.map (id : ℝ → ℝ) (IIIa.mpPsi ε hε) p) ∂IIIa.sepDiffRho =
      ((ε⁻¹ : ℝ) : ℂ) ^ 2 * ∫ p, mpHW0 ν ε μ G xo i p ∂IIIa.mpRho2 := by
    rw [← h5, Complex.real_smul]
    push_cast
    ring
  rw [h7]
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  push_cast
  field_simp

private theorem mp_diff0_pointwise :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ε : ℝ) (μ : ℂ) (ρo ρi : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
      -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (i : Fin 3)
        (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 →
        ‖mpHW0 ν ε μ G xo i p - IIIa.mpVF μ G p xo i‖ ≤
          C * ε * (1 + |p.2.2|) * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ)) *
            IIIa.tensorNorm (G p.2.1 p.2.2) := by
  obtain ⟨Ck, hCk0, hCk⟩ := sepKernelDiffIter 1
  refine ⟨18 * Ck, by positivity, ?_⟩
  intro ν ε μ ρo ρi hν hν1 hε hε1 hμ hρo hρ G hGs xo hxo i p hp
  obtain ⟨l, w⟩ := p
  simp only at hp
  have hD : 0 < ρi - ρo := by linarith
  have hD6 : 0 ≤ (ρi - ρo) ^ (-6 : ℝ) := Real.rpow_nonneg hD.le _
  have hD5 : 0 ≤ (ρi - ρo) ^ (-5 : ℝ) := Real.rpow_nonneg hD.le _
  by_cases hw : Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) ≤ ρo
  · have hs : 0 < ν * (1 - l ^ 2) * ε ^ 2 :=
      mul_pos (mul_pos hν (by nlinarith [hp.1, hp.2])) (by positivity)
    have hgap := IIIa.mp_gap ρo ρi xo xo hxo l hp w hw
    simp only [sub_self, norm_zero, sub_zero] at hgap
    set u0 : Space := xo - l • IIIa.mpV3 w with hu0
    set u : Space := xo - l • (!₂[w.1.1, w.1.2, ε * w.2] : Space) with hu
    have hu0c : u 0 = u0 0 := by simp [hu, hu0, IIIa.mpV3]
    have hu1c : u 1 = u0 1 := by simp [hu, hu0, IIIa.mpV3]
    have hnorm : ‖u - u0‖ ≤ ε * |w.2| := by
      have : u - u0 = (-(l * (ε * w.2))) • coordinateVector 2 := by
        ext n
        fin_cases n <;> simp [hu, hu0, IIIa.mpV3, coordinateVector]
      rw [this, norm_smul, IIIa.mp_norm_e, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
        abs_of_pos hp.1, abs_of_pos hε]
      calc l * (ε * |w.2|) ≤ 1 * (ε * |w.2|) := by gcongr; exact hp.2.le
        _ = ε * |w.2| := one_mul _
    have hsle : ν * (1 - l ^ 2) * ε ^ 2 ≤ ε := by
      have h1 : ν * (1 - l ^ 2) ≤ 1 := by nlinarith [hp.1, hp.2]
      have h2 : ε ^ 2 ≤ ε := by nlinarith
      calc ν * (1 - l ^ 2) * ε ^ 2 ≤ 1 * ε ^ 2 := by gcongr
        _ ≤ ε := by linarith
    have hdiff : mpHW0 ν ε μ G xo i (l, w) - IIIa.mpVF μ G (l, w) xo i =
        -2 * ((l : ℂ) ^ (2 * μ + 2) * ∑ j : Fin 3, ∑ k : Fin 3,
          ((((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u
                (coordinateVector k) -
              fderiv ℝ (fun x => IIIa.heatLerayK0 i j x) u0
                (coordinateVector k)) : ℝ) : ℂ) *
            ((G w.1 w.2 j k : ℝ) : ℂ))) := by
      unfold mpHW0 IIIa.mpVF
      simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hdiff]
    have hb : ∀ j k : Fin 3,
        ‖((((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u
              (coordinateVector k) -
            fderiv ℝ (fun x => IIIa.heatLerayK0 i j x) u0
              (coordinateVector k)) : ℝ) : ℂ) *
          ((G w.1 w.2 j k : ℝ) : ℂ))‖ ≤
        (Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) *
          IIIa.tensorNorm (G w.1 w.2) := by
      intro j k
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      set M1 := iteratedFDeriv ℝ 1 (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u
      set M0 := iteratedFDeriv ℝ 1 (fun x => IIIa.heatLerayK0 i j x) u0
      have hM : fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2) * ε ^ 2) i j x) u
            (coordinateVector k) -
          fderiv ℝ (fun x => IIIa.heatLerayK0 i j x) u0 (coordinateVector k) =
          (M1 - M0) ![coordinateVector k] := by
        simp [M1, M0, iteratedFDeriv_one_apply]
      have h1 : |(M1 - M0) ![coordinateVector k]| ≤ ‖M1 - M0‖ := by
        have h := (M1 - M0).le_opNorm ![coordinateVector k]
        rw [Fin.prod_univ_one] at h
        simp only [Matrix.cons_val_zero, IIIa.mp_norm_e, mul_one] at h
        simpa using h
      have h2 := hCk i j (ν * (1 - l ^ 2) * ε ^ 2) hs u0 u (ρi - ρo) hD hgap hu0c hu1c
      have he6 : (-5 - ((1 : ℕ) : ℝ)) = (-6 : ℝ) := by norm_num
      have he5 : (-4 - ((1 : ℕ) : ℝ)) = (-5 : ℝ) := by norm_num
      rw [he6, he5] at h2
      have h3 : ‖M1 - M0‖ ≤
          Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ)) := by
        refine h2.trans ?_
        have hsum : ν * (1 - l ^ 2) * ε ^ 2 + ‖u - u0‖ ≤ ε + ε * |w.2| := add_le_add hsle hnorm
        have hDD : 0 ≤ (ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ) := add_nonneg hD6 hD5
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCk0) hDD
      rw [hM]
      exact mul_le_mul (h1.trans h3) (IIIa.mp_entry_le _ j k) (abs_nonneg _) (by positivity)
    have hs9 := IIIa.mp_sum9 _ _ hb
    have hw1 := IIIa.mp_norm_cpow_le μ hμ l hp
    rw [norm_mul, norm_mul]
    have hn2 : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [hn2]
    calc 2 * (‖(l : ℂ) ^ (2 * μ + 2)‖ * ‖∑ j : Fin 3, ∑ k : Fin 3, _‖)
        ≤ 2 * (1 * (9 * ((Ck * (ε + ε * |w.2|) * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) *
            IIIa.tensorNorm (G w.1 w.2)))) := by gcongr
      _ = _ := by ring
  · have hw' : ρo < Real.sqrt (w.1.1 ^ 2 + w.1.2 ^ 2) := lt_of_not_ge hw
    have h0 : G w.1 w.2 = 0 := hGs _ _ hw'
    have : mpHW0 ν ε μ G xo i (l, w) - IIIa.mpVF μ G (l, w) xo i = 0 := by
      simp [mpHW0, IIIa.mpVF, h0]
    rw [this, norm_zero]
    have : 0 ≤ IIIa.tensorNorm (G w.1 w.2) := Real.sqrt_nonneg _
    positivity

private theorem sepW_sub_sepVmu0_le (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hdiff : ∀ (ν ε : ℝ) (μ : ℂ) (ρo ρi : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 →
      -(1 / 4) < μ.re → 0 ≤ ρo → ρo < ρi →
      ∀ (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ),
        (∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
      ∀ (xo : Space), ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (i : Fin 3)
        (p : ℝ × ((ℝ × ℝ) × ℝ)), p.1 ∈ Ioo (0 : ℝ) 1 →
        ‖mpHW0 ν ε μ G xo i p - IIIa.mpVF μ G p xo i‖ ≤
          C0 * ε * (1 + |p.2.2|) * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ)) *
            IIIa.tensorNorm (G p.2.1 p.2.2))
    (ν c ε ρo ρi : ℝ) (μ : ℂ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρo : 0 ≤ ρo) (hρ : ρo < ρi) (hμ : -(1 / 4) < μ.re)
    (G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j)
    (hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0)
    (hwint : Integrable (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)) volume)
    (hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume)
    (xo : Space) (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    ‖IIIa.sepW ν μ (IIIa.thinSource ε (IIIa.meanLift G)) (ε⁻¹ • xo) τ -
        (ε ^ 2 : ℝ) • IIIa.sepVmu0 μ G xo‖ ≤
      C0 * ε ^ 3 * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ)) *
        ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2) := by
  have hD : 0 < ρi - ρo := by linarith
  have hD1pos : 0 < (ρi - ρo) / 2 := by linarith
  have hD6 : 0 ≤ (ρi - ρo) ^ (-6 : ℝ) := Real.rpow_nonneg hD.le _
  have hD5 : 0 ≤ (ρi - ρo) ^ (-5 : ℝ) := Real.rpow_nonneg hD.le _
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2) with hNr
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  obtain ⟨hWe, hWi⟩ := mp_W0_eval ν c ε ρo ρi μ hν hc hε hρo hρ hμ G hGm hGs hint xo hxo τ i
  obtain ⟨_, hi0, _⟩ := IIIa.mp_V_diff IIIa.sepKernelBounds μ hμ ρo ρi hρo hρ G hGm hGs hint xo hxo i
  have hVi : Integrable (fun p => IIIa.mpVF μ G p xo i) IIIa.mpRho2 :=
    hi0 xo (Metric.mem_ball_self hD1pos)
  have hVe : IIIa.sepVmu0 μ G xo i = ∫ p, IIIa.mpVF μ G p xo i ∂IIIa.mpRho2 :=
    IIIa.mp_V_link μ G xo i hVi
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [hWe, hVe, Complex.real_smul]
  push_cast
  rw [← mul_sub, ← integral_sub hWi hVi, norm_mul]
  have hB : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
      (C0 * ε * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) *
        ((1 + |p.2.2|) * IIIa.tensorNorm (G p.2.1 p.2.2))) IIIa.mpRho2 := by
    have h := (integrable_const (1 : ℝ) (μ := volume.restrict (Ioo (0 : ℝ) 1))).mul_prod hwint
    exact (h.congr (Eventually.of_forall fun p => by simp)).const_mul _
  have hnorm : ‖∫ p, (mpHW0 ν ε μ G xo i p - IIIa.mpVF μ G p xo i) ∂IIIa.mpRho2‖ ≤
      ∫ p, (C0 * ε * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) *
        ((1 + |p.2.2|) * IIIa.tensorNorm (G p.2.1 p.2.2)) ∂IIIa.mpRho2 := by
    refine norm_integral_le_of_norm_le hB ?_
    filter_upwards [IIIa.mpRho2_ae_mem] with p hp
    have := hdiff ν ε μ ρo ρi hν hν1 hε hε1 hμ hρo hρ G hGs xo hxo i p hp
    calc _ ≤ _ := this
      _ = _ := by ring
  have hI : ∫ p, (C0 * ε * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) *
      ((1 + |p.2.2|) * IIIa.tensorNorm (G p.2.1 p.2.2)) ∂IIIa.mpRho2 =
      (C0 * ε * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) * Nr := by
    rw [integral_const_mul]
    congr 1
    have := integral_prod_mul (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (ν := (volume : Measure ((ℝ × ℝ) × ℝ)))
      (fun _ => (1 : ℝ)) (fun w : (ℝ × ℝ) × ℝ => (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2))
    simp only [one_mul, integral_const, smul_eq_mul] at this
    unfold IIIa.mpRho2
    rw [hNr]
    simpa using this
  have hpow : ‖(ε : ℂ) ^ 2‖ = ε ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le]
  rw [hpow]
  calc ε ^ 2 * ‖∫ p, (mpHW0 ν ε μ G xo i p - IIIa.mpVF μ G p xo i) ∂IIIa.mpRho2‖
      ≤ ε ^ 2 * ((C0 * ε * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) * Nr) := by
        rw [← hI]; gcongr
    _ = _ := by ring

private theorem annulus_gap_rpow_le (ν c r : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c)
    (hr1 : Real.sqrt ν ≤ r) (hr2 : r ≤ Real.sqrt (5 * ν / 4)) :
    r⁻¹ * ((Real.sqrt ν - Real.sqrt (5 * ν / 6)) ^ (-6 : ℝ) +
        (Real.sqrt ν - Real.sqrt (5 * ν / 6)) ^ (-5 : ℝ)) ≤
      2 * 32 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 7 * r ^ (-5 : ℝ) := by
  set D := Real.sqrt ν - Real.sqrt (5 * ν / 6)
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hr0 : 0 < r := lt_of_lt_of_le hsν hr1
  have hg := PhasePrim.gap_le ν hν
  have hD : 0 < D := by linarith
  have hν_le_sν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have hM1 : 1 ≤ 1 + ν⁻¹ + c := by
    have : 0 < ν⁻¹ := inv_pos.2 hν
    linarith
  have hM0 : 0 ≤ 1 + ν⁻¹ + c := by linarith
  have hDinv : D⁻¹ ≤ 12 * (1 + ν⁻¹ + c) := by
    have h1 : D⁻¹ ≤ 12 * (Real.sqrt ν)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀' hD]
      have : D * (12 * (Real.sqrt ν)⁻¹) = 12 * D / Real.sqrt ν := by ring
      rw [this, one_le_div hsν]
      linarith
    have h2 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hν_le_sν
    linarith
  have hrinv : r⁻¹ ≤ 1 + ν⁻¹ + c := by
    have h1 : r⁻¹ ≤ (Real.sqrt ν)⁻¹ := inv_anti₀ hsν hr1
    have h2 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hν_le_sν
    linarith
  have hr_le_2 : r ≤ 2 := by
    refine hr2.trans ?_
    have : 5 * ν / 4 ≤ 4 := by linarith
    calc Real.sqrt (5 * ν / 4) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt this
      _ = 2 := by norm_num
  have hr5_bound : 1 ≤ 32 * r ^ (-5 : ℝ) := by
    have e5 : r ^ (-5 : ℝ) = (r ^ 5)⁻¹ := by
      rw [Real.rpow_neg hr0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e5, ← div_eq_mul_inv, one_le_div (pow_pos hr0 5)]
    calc r ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ hr0.le hr_le_2 5
      _ = 32 := by norm_num
  have e6 : D ^ (-6 : ℝ) = (D⁻¹) ^ 6 := by
    rw [Real.rpow_neg hD.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have e5 : D ^ (-5 : ℝ) = (D⁻¹) ^ 5 := by
    rw [Real.rpow_neg hD.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  rw [e6, e5]
  have hp6 : (D⁻¹) ^ 6 ≤ (12 * (1 + ν⁻¹ + c)) ^ 6 :=
    pow_le_pow_left₀ (inv_nonneg.2 hD.le) hDinv 6
  have hp5 : (D⁻¹) ^ 5 ≤ (12 * (1 + ν⁻¹ + c)) ^ 6 := by
    calc (D⁻¹) ^ 5 ≤ (12 * (1 + ν⁻¹ + c)) ^ 5 :=
          pow_le_pow_left₀ (inv_nonneg.2 hD.le) hDinv 5
      _ ≤ (12 * (1 + ν⁻¹ + c)) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hsum : (D⁻¹) ^ 6 + (D⁻¹) ^ 5 ≤ 2 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 6 := by
    have : (12 * (1 + ν⁻¹ + c)) ^ 6 = 12 ^ 6 * (1 + ν⁻¹ + c) ^ 6 := by ring
    linarith
  have hmul : r⁻¹ * ((D⁻¹) ^ 6 + (D⁻¹) ^ 5) ≤ 2 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 7 := by
    calc r⁻¹ * ((D⁻¹) ^ 6 + (D⁻¹) ^ 5)
        ≤ (1 + ν⁻¹ + c) * (2 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 6) :=
          mul_le_mul hrinv hsum (by positivity) hM0
      _ = 2 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 7 := by ring
  calc r⁻¹ * ((D⁻¹) ^ 6 + (D⁻¹) ^ 5)
      = (r⁻¹ * ((D⁻¹) ^ 6 + (D⁻¹) ^ 5)) * 1 := by ring
    _ ≤ (2 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 7) * (32 * r ^ (-5 : ℝ)) :=
        mul_le_mul hmul hr5_bound zero_le_one (by positivity)
    _ = 2 * 32 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 7 * r ^ (-5 : ℝ) := by ring

/-- **Proof of `YBWidth.SepCommMainDiff0`** (`PartIII-b:C/rep/8/1/1/2/5/2/1/2`). -/
theorem sepCommMainDiff0 : YBWidth.SepCommMainDiff0 := by
  obtain ⟨C0, hC0, hdiff⟩ := mp_diff0_pointwise
  refine ⟨4 * C0 * (2 * 32 * 12 ^ 6), 7, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 G hGm hGs hwint τ xo hxo hle
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hρi_xo : ρi ≤ r := Real.sqrt_le_sqrt hxo
  have hr_le : r ≤ Real.sqrt (5 * ν / 4) := Real.sqrt_le_sqrt hle
  have hr : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hρi_xo
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hmeas : Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2) := by
    unfold IIIa.tensorNorm
    exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => (hGm i j).pow_const 2)
  have hint : Integrable (fun w : (ℝ × ℝ) × ℝ => IIIa.tensorNorm (G w.1 w.2)) volume := by
    refine Integrable.mono' hwint hmeas.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (tn_nonneg _)]
    exact le_mul_of_one_le_left (tn_nonneg _) (by linarith [abs_nonneg w.2])
  set T := IIIa.thinSource ε (IIIa.meanLift G)
  set A0 := IIIa.sepW ν (μ : ℂ) T (ε⁻¹ • xo) τ
  set A1 := IIIa.sepW ν ((μ : ℂ) + 1) T (ε⁻¹ • xo) τ
  set B0 := (ε ^ 2 : ℝ) • IIIa.sepVmu0 (μ : ℂ) G xo
  set B1 := (ε ^ 2 : ℝ) • IIIa.sepVmu0 ((μ : ℂ) + 1) G xo
  have hsrc : srcX0 ν μ T τ (ε⁻¹ • xo) = PhasePrim.reMap (A0 - A1) := rfl
  have hnewt : newtonX0 ε μ G τ (ε⁻¹ • xo) = PhasePrim.reMap (B0 - B1) := by
    unfold newtonX0 B0 B1
    rw [smul_inv_smul₀ hε.ne', ← map_smul, smul_sub]
  rw [hsrc, hnewt, ← map_sub]
  have h_re : ‖PhasePrim.reMap (A0 - A1 - (B0 - B1))‖ ≤ 2 * (‖A0 - B0‖ + ‖A1 - B1‖) := by
    have e : A0 - A1 - (B0 - B1) = (A0 - B0) - (A1 - B1) := by abel
    rw [e]
    calc ‖PhasePrim.reMap ((A0 - B0) - (A1 - B1))‖
        ≤ ‖PhasePrim.reMap‖ * ‖(A0 - B0) - (A1 - B1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * (‖A0 - B0‖ + ‖A1 - B1‖) :=
          mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
  set Nr : ℝ := ∫ w : (ℝ × ℝ) × ℝ, (1 + |w.2|) * IIIa.tensorNorm (G w.1 w.2)
  have hNr0 : 0 ≤ Nr := integral_nonneg fun w => mul_nonneg (by positivity) (tn_nonneg _)
  have hB0 := sepW_sub_sepVmu0_le C0 hC0 hdiff ν c ε ρo ρi (μ : ℂ)
    hν hν1 hc hε hε1 hρo hρ hreμ G hGm hGs hwint hint xo hρi_xo τ
  have hB1 := sepW_sub_sepVmu0_le C0 hC0 hdiff ν c ε ρo ρi ((μ : ℂ) + 1)
    hν hν1 hc hε hε1 hρo hρ hreμ1 G hGm hGs hwint hint xo hρi_xo τ
  have hsum : ‖PhasePrim.reMap (A0 - A1 - (B0 - B1))‖ ≤
      4 * C0 * ε ^ 3 * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ)) * Nr := by
    linarith
  have hgap_pow := annulus_gap_rpow_le ν c r hν hν1 hc hρi_xo hr_le
  calc ε * r⁻¹ * ‖PhasePrim.reMap (A0 - A1 - (B0 - B1))‖
      ≤ ε * r⁻¹ * (4 * C0 * ε ^ 3 * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ)) * Nr) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * C0 * (r⁻¹ * ((ρi - ρo) ^ (-6 : ℝ) + (ρi - ρo) ^ (-5 : ℝ))) * ε ^ 4 * Nr := by ring
    _ ≤ 4 * C0 * (2 * 32 * 12 ^ 6 * (1 + ν⁻¹ + c) ^ 7 * r ^ (-5 : ℝ)) * ε ^ 4 * Nr := by
        gcongr
    _ = 4 * C0 * (2 * 32 * 12 ^ 6) * (1 + ν⁻¹ + c) ^ 7 * ε ^ 4 * r ^ (-5 : ℝ) * Nr := by ring

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
