import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G1_1_2
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts

/-!


Source of record: `the November 2 reference manuscript`, lines 4366-4396
(finite-band retained block estimates: "Divide the two amplitudes by `F_±(s,t)` ... Insert this
estimate in the amplitude equation. Its deviation from the initial amplitude is bounded by ...")
and lines 2991-3000 (`prop:short-full-clock`: direct errors `δ_*(θ)`, amplitude/complement
couplings `C(θ⁻¹ + δ_*)`, division of each amplitude by `e^{λ_i(r₀-θ)}(r₀/θ)^{κ_i}`).

Proof of `ActualAmpIntegralBound D`:
1. `Fpm_eq_clockNC`: on `s, t ≥ 0`, `F_j(s,t) = clockNC P ν t s (pmIdx j)` (the exponential
   `e^{λ_j(z_s-z_t)}(a_s/a_t)^{κ_j}` is the complex normaliser of Part III-a, since
   `z_s - z_t = θ_t - θ_s` and `a_s/a_t = θ_t/θ_s`); hence (`ampN_actualPk_eq_normAmpl`) on the
   band `[0, 2/ν]` the normalised amplitude `ampN j` is the Part III-a `normAmpl (pmIdx j)`.
2. The weak FTC of the amplitude equation (`amplWeakFTC`, source 2898-2918, 2998-3000) writes
   `normAmpl s - normAmpl t` as `∫_{(t,s]} a⁻² N_C⁻¹ (amplitude residual)`.
3. The residual splits (`amplResidual_eq_sum_add`) into the direct frame error (`amplDirectError`,
   `≤ C₁ν³/θ`) and the complement coupling (`amplComplCoupling`, `≤ C₂θ⁻¹ ‖compl‖`); on the band
   `θ⁻¹ ≤ 3ν`, `a⁻² ≤ 1` and `‖compl‖ ≤ 3^{3/2} ‖P_c 𝒰 x‖` (`compl_le_norm_Pc_actualPk`), which
   gives the pointwise bound `integrand_le` and then the integral bound.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF FlatSettingInst

/-! ## 1. The amplitudes `F_±` are the Part III-a complex normalisers -/

/-- Polar form of `e^{lΔ} ρ^k` for `ρ > 0`, with the modulus and phase written as `A`, `B`, `φ`. -/
theorem exp_mul_cpow_eq_polar (l k : ℂ) (Δ ρ A B φ : ℝ) (hρ : 0 < ρ) (hA : A = l.re)
    (hB : B = k.re) (hφ : φ = l.im * Δ + k.im * Real.log ρ) :
    Complex.exp (l * (Δ : ℂ)) * ((ρ : ℝ) : ℂ) ^ k =
      ((Real.exp (A * Δ) * ρ ^ B : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
  subst hA hB hφ
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne'),
    ← Complex.ofReal_log hρ.le, Real.rpow_def_of_pos hρ, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_exp]
  simp only [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- For `0 < ν`, `0 ≤ s`, `0 ≤ t`: `F_j(s,t) = clockNC P ν t s (pmIdx j)` (source 4368-4372,
2998-3000). -/
theorem Fpm_eq_clockNC (P : UnforcedLeray.Blueprint.Planar.PlanarData) (j : Bool)
    {ν s t : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Fpm j P.eigenvalue P.kappa ν s t = IIIa.clockNC P ν t s (pmIdx j) := by
  have has : 0 < aOf ν s := aOf_pos_of_nonneg ν s hν hs
  have hat : 0 < aOf ν t := aOf_pos_of_nonneg ν t hν ht
  have hρ : 0 < aOf ν s / aOf ν t := div_pos has hat
  have hνne : ν ≠ 0 := hν.ne'
  have hasne : 1 + ν * s ≠ 0 := has.ne'
  have hatne : 1 + ν * t ≠ 0 := hat.ne'
  have hz : IIIa.clockTheta ν t - IIIa.clockTheta ν s = zOf ν s - zOf ν t := by
    unfold IIIa.clockTheta zOf aOf IIIa.clockA
    field_simp
    ring
  have hθ : IIIa.clockTheta ν t / IIIa.clockTheta ν s = aOf ν s / aOf ν t := by
    unfold IIIa.clockTheta aOf IIIa.clockA
    field_simp
  unfold IIIa.clockNC IIIa.clockN IIIa.clockPhaseIm
  rw [hz, hθ]
  cases j
  · rw [fpm_false_eq, show pmIdx false = 1 from rfl]
    exact exp_mul_cpow_eq_polar _ _ _ _ _ _ _ hρ (by simp) (by simp)
      (by rw [if_neg (by decide)]; simp; ring)
  · rw [fpm_true_eq, show pmIdx true = 0 from rfl]
    exact exp_mul_cpow_eq_polar _ _ _ _ _ _ _ hρ rfl rfl
      (by rw [if_pos rfl, one_mul])

/-- On the band `[0, 2/ν]`, the normalised amplitude `ampN j` of `actualPk FI` is the Part III-a
normalised amplitude `normAmpl (pmIdx j)` of the periodized frame. -/
theorem ampN_actualPk_eq_normAmpl {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : 0 ≤ t) (x : Xmc (cOf ν) m) (j : Bool)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (2 / ν)) :
    ampN (actualPk FI) P.eigenvalue P.kappa ν t x j r =
      IIIa.normAmpl (IIIa.periodizedFrame κ ν m b K hν hPF) P t
        (fun q => xFn (FI.ev.U q t x)) r (pmIdx j) := by
  unfold ampN IIIa.normAmpl
  rw [ell_actualPk_eq_ampl hν hPF FI t x j hr, Fpm_eq_clockNC P j hν hr.1 ht, div_eq_inv_mul]

/-! ## 2. Pointwise bound on the integrand of the amplitude equation -/

/-- **Pointwise bound** (source 2991-2997, 4366-4382): at an age `r ∈ [t, 2/ν]`, the normalised
age-rate residual of mode `i` is bounded by `3C₁ν⁴(|A₊|+|A₋|) + 3·3^{3/2}C₂ν R`. -/
theorem integrand_le {κ : IIIa.PlanarFrameKernels} {ν m b K C₁ C₂ : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    (tr' : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : 0 ≤ t) (x : Xmc (cOf ν) m)
    {r : ℝ} (htr : t ≤ r) (hr : r ≤ 2 / ν) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hdecomp : ∀ i : Fin 2,
      IIIa.movH0 κ tr' r i (IIIa.movingW ν (fun q => xFn (FI.ev.U q t x)) r) =
        (∑ j : Fin 2, IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF)
            (fun q => xFn (FI.ev.U q t x)) r j *
          IIIa.movH0 κ tr' r i ((IIIa.periodizedFrame κ ν m b K hν hPF).E r j)) +
        IIIa.movH0 κ tr' r i (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun q => xFn (FI.ev.U q t x)) r))
    (hdir : ∀ j : Fin 2, (∑ i : Fin 2, ‖IIIa.amplDirectMat κ P
        (IIIa.periodizedFrame κ ν m b K hν hPF) tr' r i j‖) ≤ C₁ * ν ^ 3 / IIIa.clockTheta ν r)
    (hcompl : (∑ i : Fin 2, ENNReal.ofReal ‖IIIa.movH0 κ tr' r i
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) (fun q => xFn (FI.ev.U q t x)) r)‖) ≤
      ENNReal.ofReal (C₂ * (1 / IIIa.clockTheta ν r)) *
        IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
          (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) (fun q => xFn (FI.ev.U q t x)) r))
    (i : Fin 2) :
    ‖(((IIIa.clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((IIIa.clockNC P ν t r i)⁻¹ * IIIa.amplResidual κ P
          (IIIa.periodizedFrame κ ν m b K hν hPF) tr' (fun q => xFn (FI.ev.U q t x)) r i)‖ ≤
      3 * C₁ * ν ^ 4 * (‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
          ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖) +
        3 * C₂ * (3 : ℝ) ^ ((3 : ℝ) / 2) * ν *
          cmpN (actualPk FI) P.eigenvalue P.kappa ν t x r := by
  set F := IIIa.periodizedFrame κ ν m b K hν hPF with hFdef
  set w : ℝ → ℝ × ℝ → ℂ := fun q => xFn (FI.ev.U q t x) with hwdef
  have hr0 : 0 ≤ r := ht.trans htr
  have hrI : r ∈ Icc (0 : ℝ) (2 / ν) := ⟨hr0, hr⟩
  obtain ⟨hθ1, hθ3, -⟩ := clockTheta_inv_bounds hν hrI
  have hθpos : 0 < IIIa.clockTheta ν r := inv_pos.mp (lt_of_lt_of_le hν hθ1)
  have hN : 0 < IIIa.clockN P ν t r := IIIa.clockN_pos P hν ht hr0
  have ha1 : 1 ≤ IIIa.clockA ν r := by
    unfold IIIa.clockA
    nlinarith [mul_nonneg hν.le hr0]
  have ha2 : (IIIa.clockA ν r) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by norm_num)
  have ha2' : 0 ≤ (IIIa.clockA ν r) ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hA : ∀ jj : Bool, ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x jj r‖ =
      ‖IIIa.ampl F w r (pmIdx jj)‖ / IIIa.clockN P ν t r := by
    intro jj
    rw [ampN_actualPk_eq_normAmpl P hν hPF FI ht x jj hrI]
    exact IIIa.FrameAmplSub.norm_normAmpl F P hν ht hr0 w (pmIdx jj)
  have hR : cmpN (actualPk FI) P.eigenvalue P.kappa ν t x r =
      ‖Pc (actualPk FI) r ((actualPk FI).Uev r t x)‖ / IIIa.clockN P ν t r := by
    unfold cmpN
    rw [norm_Fpm_eq_clockN P true hν hr0 ht]
  have hres := IIIa.FrameAmplSub.amplResidual_eq_sum_add κ P F tr' w r i (hdecomp i)
  have hD : ∀ jj : Fin 2, ‖IIIa.amplDirectMat κ P F tr' r i jj‖ ≤
      C₁ * ν ^ 3 / IIIa.clockTheta ν r := by
    intro jj
    refine le_trans ?_ (hdir jj)
    exact Finset.single_le_sum (f := fun i' => ‖IIIa.amplDirectMat κ P F tr' r i' jj‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  set R := ‖Pc (actualPk FI) r ((actualPk FI).Uev r t x)‖ with hRdef
  set c32 : ℝ := (3 : ℝ) ^ ((3 : ℝ) / 2) with hc32
  have hc32pos : 0 ≤ c32 := by positivity
  have hM : ‖IIIa.movH0 κ tr' r i (IIIa.compl F w r)‖ ≤
      C₂ * (1 / IIIa.clockTheta ν r) * (c32 * R) := by
    have h1 : ENNReal.ofReal ‖IIIa.movH0 κ tr' r i (IIIa.compl F w r)‖ ≤
        ∑ i' : Fin 2, ENNReal.ofReal ‖IIIa.movH0 κ tr' r i' (IIIa.compl F w r)‖ :=
      Finset.single_le_sum (f := fun i' => ENNReal.ofReal ‖IIIa.movH0 κ tr' r i' (IIIa.compl F w r)‖)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    have hPc := compl_le_norm_Pc_actualPk hm hν hPF FI t x hrI
    have h2 := h1.trans (hcompl.trans (mul_le_mul_of_nonneg_left hPc zero_le))
    have hγ : 0 ≤ C₂ * (1 / IIIa.clockTheta ν r) :=
      mul_nonneg hC₂ (le_of_lt (one_div_pos.mpr hθpos))
    have h3 : ENNReal.ofReal (C₂ * (1 / IIIa.clockTheta ν r)) *
        (ENNReal.ofReal c32 * ENNReal.ofReal R) =
        ENNReal.ofReal (C₂ * (1 / IIIa.clockTheta ν r) * (c32 * R)) := by
      rw [ENNReal.ofReal_mul hγ, ENNReal.ofReal_mul hc32pos]
    rw [h3, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hγ (mul_nonneg hc32pos (norm_nonneg _)))]
      at h2
    exact h2
  have hδ : C₁ * ν ^ 3 / IIIa.clockTheta ν r ≤ 3 * C₁ * ν ^ 4 := by
    rw [div_eq_mul_inv]
    calc C₁ * ν ^ 3 * (IIIa.clockTheta ν r)⁻¹ ≤ C₁ * ν ^ 3 * (3 * ν) :=
          mul_le_mul_of_nonneg_left hθ3 (mul_nonneg hC₁ (pow_nonneg hν.le 3))
      _ = 3 * C₁ * ν ^ 4 := by ring
  have hγ' : C₂ * (1 / IIIa.clockTheta ν r) * (c32 * R) ≤ 3 * C₂ * c32 * ν * R := by
    rw [one_div]
    calc C₂ * (IIIa.clockTheta ν r)⁻¹ * (c32 * R) ≤ C₂ * (3 * ν) * (c32 * R) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ3 hC₂)
            (mul_nonneg hc32pos (norm_nonneg _))
      _ = 3 * C₂ * c32 * ν * R := by ring
  set A0 := ‖IIIa.ampl F w r 0‖ with hA0
  set A1 := ‖IIIa.ampl F w r 1‖ with hA1
  have hres_le : ‖IIIa.amplResidual κ P F tr' w r i‖ ≤
      (A0 + A1) * (3 * C₁ * ν ^ 4) + 3 * C₂ * c32 * ν * R := by
    rw [hres, Fin.sum_univ_two]
    calc ‖IIIa.ampl F w r 0 * IIIa.amplDirectMat κ P F tr' r i 0 +
          IIIa.ampl F w r 1 * IIIa.amplDirectMat κ P F tr' r i 1 +
          IIIa.movH0 κ tr' r i (IIIa.compl F w r)‖
        ≤ ‖IIIa.ampl F w r 0 * IIIa.amplDirectMat κ P F tr' r i 0‖ +
          ‖IIIa.ampl F w r 1 * IIIa.amplDirectMat κ P F tr' r i 1‖ +
          ‖IIIa.movH0 κ tr' r i (IIIa.compl F w r)‖ := norm_add₃_le
      _ = A0 * ‖IIIa.amplDirectMat κ P F tr' r i 0‖ +
          A1 * ‖IIIa.amplDirectMat κ P F tr' r i 1‖ +
          ‖IIIa.movH0 κ tr' r i (IIIa.compl F w r)‖ := by rw [norm_mul, norm_mul]
      _ ≤ A0 * (3 * C₁ * ν ^ 4) + A1 * (3 * C₁ * ν ^ 4) + 3 * C₂ * c32 * ν * R := by
          refine add_le_add (add_le_add ?_ ?_) (hM.trans hγ')
          · exact mul_le_mul_of_nonneg_left ((hD 0).trans hδ) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left ((hD 1).trans hδ) (norm_nonneg _)
      _ = (A0 + A1) * (3 * C₁ * ν ^ 4) + 3 * C₂ * c32 * ν * R := by ring
  rw [hA true, hA false, hR, show pmIdx true = 0 from rfl, show pmIdx false = 1 from rfl,
    norm_mul, norm_mul, IIIa.FrameAmplSub.norm_clockNC_inv P hν ht hr0 i,
    Complex.norm_of_nonneg ha2']
  have hNinv : 0 ≤ (IIIa.clockN P ν t r)⁻¹ := inv_nonneg.mpr hN.le
  have hprod : 0 ≤ (IIIa.clockN P ν t r)⁻¹ * ‖IIIa.amplResidual κ P F tr' w r i‖ :=
    mul_nonneg hNinv (norm_nonneg _)
  calc (IIIa.clockA ν r) ^ (-2 : ℝ) *
        ((IIIa.clockN P ν t r)⁻¹ * ‖IIIa.amplResidual κ P F tr' w r i‖)
      ≤ 1 * ((IIIa.clockN P ν t r)⁻¹ * ‖IIIa.amplResidual κ P F tr' w r i‖) :=
        mul_le_mul_of_nonneg_right ha2 hprod
    _ ≤ (IIIa.clockN P ν t r)⁻¹ * ((A0 + A1) * (3 * C₁ * ν ^ 4) + 3 * C₂ * c32 * ν * R) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hres_le hNinv
    _ = 3 * C₁ * ν ^ 4 * (A0 / IIIa.clockN P ν t r + A1 / IIIa.clockN P ν t r) +
        3 * C₂ * c32 * ν * (R / IIIa.clockN P ν t r) := by ring

/-! ## 3. The integral bound at one level -/

/-- **The amplitude integral inequality at one level** (source 4366-4396): from the weak FTC of
the amplitude equation, the decomposition of the residual, the direct-error and the coupling
bounds on `(t, s]`. -/
theorem ampDiff_le {κ : IIIa.PlanarFrameKernels} {ν m b K C₁ C₂ C : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (P : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    (tr' : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {t : ℝ} (ht : 0 ≤ t) (x : Xmc (cOf ν) m)
    {s : ℝ} (hts : t ≤ s) (hs : s ≤ 2 / ν) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC1 : 3 * C₁ ≤ C) (hC2 : 3 * C₂ * (3 : ℝ) ^ ((3 : ℝ) / 2) ≤ C)
    (hftc : ∀ i : Fin 2,
      IIIa.normAmpl (IIIa.periodizedFrame κ ν m b K hν hPF) P t
          (fun q => xFn (FI.ev.U q t x)) s i -
        IIIa.normAmpl (IIIa.periodizedFrame κ ν m b K hν hPF) P t
          (fun q => xFn (FI.ev.U q t x)) t i =
      ∫ r in Ioc t s, (((IIIa.clockA ν r) ^ (-2 : ℝ) : ℝ) : ℂ) *
        ((IIIa.clockNC P ν t r i)⁻¹ * IIIa.amplResidual κ P
          (IIIa.periodizedFrame κ ν m b K hν hPF) tr' (fun q => xFn (FI.ev.U q t x)) r i))
    (hdecomp : ∀ r ∈ Ioc t s, ∀ i : Fin 2,
      IIIa.movH0 κ tr' r i (IIIa.movingW ν (fun q => xFn (FI.ev.U q t x)) r) =
        (∑ j : Fin 2, IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF)
            (fun q => xFn (FI.ev.U q t x)) r j *
          IIIa.movH0 κ tr' r i ((IIIa.periodizedFrame κ ν m b K hν hPF).E r j)) +
        IIIa.movH0 κ tr' r i (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF)
          (fun q => xFn (FI.ev.U q t x)) r))
    (hdir : ∀ r ∈ Ioc t s, ∀ j : Fin 2, (∑ i : Fin 2, ‖IIIa.amplDirectMat κ P
        (IIIa.periodizedFrame κ ν m b K hν hPF) tr' r i j‖) ≤ C₁ * ν ^ 3 / IIIa.clockTheta ν r)
    (hcompl : ∀ r ∈ Ioc t s, (∑ i : Fin 2, ENNReal.ofReal ‖IIIa.movH0 κ tr' r i
        (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) (fun q => xFn (FI.ev.U q t x)) r)‖) ≤
      ENNReal.ofReal (C₂ * (1 / IIIa.clockTheta ν r)) *
        IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) (IIIa.clockA ν r)) m
          (IIIa.compl (IIIa.periodizedFrame κ ν m b K hν hPF) (fun q => xFn (FI.ev.U q t x)) r))
    (j : Bool) :
    ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x j s -
        ampN (actualPk FI) P.eigenvalue P.kappa ν t x j t‖ ≤
      ∫ r in t..s, (C * ν ^ 4 *
          (‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
            ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖) +
        C * (ν + ν ^ 4) * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x r) := by
  have hsI : s ∈ Icc (0 : ℝ) (2 / ν) := ⟨ht.trans hts, hs⟩
  have htI : t ∈ Icc (0 : ℝ) (2 / ν) := ⟨ht, hts.trans hs⟩
  rw [ampN_actualPk_eq_normAmpl P hν hPF FI ht x j hsI,
    ampN_actualPk_eq_normAmpl P hν hPF FI ht x j htI, hftc (pmIdx j),
    intervalIntegral.integral_of_le hts]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hcA : ∀ jj : Bool, ContinuousOn
      (fun r => ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x jj r‖) (Icc t s) := fun jj =>
    (continuousOn_ampN_actualPk FI P.eigenvalue P.kappa hν ht x jj).norm
  have hcR : ContinuousOn (cmpN (actualPk FI) P.eigenvalue P.kappa ν t x) (Icc t s) :=
    continuousOn_cmpN_actualPk FI P.eigenvalue P.kappa hν ht x
  have hcont : ContinuousOn (fun r => C * ν ^ 4 *
        (‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
          ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖) +
      C * (ν + ν ^ 4) * cmpN (actualPk FI) P.eigenvalue P.kappa ν t x r) (Icc t s) :=
    (continuousOn_const.mul ((hcA true).add (hcA false))).add (continuousOn_const.mul hcR)
  have hint := (hcont.intervalIntegrable_of_Icc (μ := volume) hts).1
  refine integral_mono_of_nonneg (ae_of_all _ fun r => norm_nonneg _) hint ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun r hr => ?_
  have hle := integrand_le hm P hν hPF tr' FI ht x hr.1.le (hr.2.trans hs) hC₁ hC₂
    (hdecomp r hr) (hdir r hr) (hcompl r hr) (pmIdx j)
  refine hle.trans ?_
  have hS : 0 ≤ ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x true r‖ +
      ‖ampN (actualPk FI) P.eigenvalue P.kappa ν t x false r‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hZ : 0 ≤ cmpN (actualPk FI) P.eigenvalue P.kappa ν t x r := by
    unfold cmpN
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hν4 : 0 ≤ ν ^ 4 := pow_nonneg hν.le 4
  have hCnn : 0 ≤ C := le_trans (mul_nonneg (by norm_num) hC₁) hC1
  refine add_le_add ?_ ?_
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hν4) hS
  · refine mul_le_mul_of_nonneg_right ?_ hZ
    calc 3 * C₂ * (3 : ℝ) ^ ((3 : ℝ) / 2) * ν ≤ C * ν :=
          mul_le_mul_of_nonneg_right hC2 hν.le
      _ ≤ C * (ν + ν ^ 4) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hν4) hCnn

/-! ## 4. Assembly -/

/-- Transport of a train along an equality of cell lengths, with its BUC class and its linearised
flows. -/
theorem exists_train_cast {ν c c' : ℝ} (m : ℝ) (hc : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c', UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧
      ∀ (t : ℝ) (f : ℝ × ℝ → ℂ) (w : ℝ → ℝ × ℝ → ℂ) (u : ℝ → ℝ × ℝ → Fin 2 → ℂ),
        IIIa.IsLinearisedFlow ν c m tr t f w u → IIIa.IsLinearisedFlow ν c' m tr' t f w u := by
  subst hc
  exact ⟨tr, hbuc, fun _ _ _ _ h => h⟩

/-- **(Leaf 2) Finite-band amplitude integral inequality on `actualPk FI`** (source lines
4366-4396 and 2991-3000 `prop:short-full-clock`). -/
theorem actualAmpIntegralBound (D : SeqData) :
    UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.ActualAmpIntegralBound D := by
  intro dm dp hD κ hκ m hfact hm
  have hseed : IIIa.IsSeedKernels κ := hκ.1
  obtain ⟨K, bPF, hPFall⟩ := IIIa.perFrameFactsAll κ hseed m hm
  obtain ⟨bW, hbW1, hW⟩ := amplWeakFTC κ hseed D.Pl hD.planar m hm K
  obtain ⟨C₁, bD, hC₁, -, hDE⟩ := amplDirectError κ hseed D.Pl hD.planar m hm K
  obtain ⟨C₂, bC, hC₂, -, hCC⟩ := amplComplCoupling κ hseed m hm K
  set b : ℝ := max bPF (max bW (max bD bC)) with hbdef
  have hbPF : bPF ≤ b := le_max_left _ _
  have hbW : bW ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hbD : bD ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hbC : bC ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hb0 : 0 < b := lt_of_lt_of_le one_pos (hbW1.trans hbW)
  obtain ⟨ν₁, hν₁, hPF'⟩ := hPFall b hbPF
  obtain ⟨ν₂, hν₂, hW'⟩ := hW b hbW
  obtain ⟨ν₃, hν₃, hDE'⟩ := hDE b hbD
  obtain ⟨ν₄, hν₄, hCC'⟩ := hCC b hbC
  have hlim := retNu_tendsto D.σ₀ hD.omega_ne
  have hlt : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, nu D n < ε := fun ε hε =>
    hlim.eventually_lt tendsto_const_nhds hε
  have hb3 : 0 < 1 / (3 * b) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hlt ν₁ hν₁).and ((hlt ν₂ hν₂).and ((hlt ν₃ hν₃).and ((hlt ν₄ hν₄).and (hlt _ hb3)))))
  set C : ℝ := 3 * C₁ + 3 * C₂ * (3 : ℝ) ^ ((3 : ℝ) / 2) + 1 with hCdef
  have hc32 : 0 ≤ 3 * C₂ * (3 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have hC : 0 < C := by positivity
  refine ⟨C, N, hC, ?_⟩
  intro n hn FI t ht x j s hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN n hn
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hν1 : nu D n ∈ Ioc 0 ν₁ := ⟨hν, h1.le⟩
  have hν2 : nu D n ∈ Ioc 0 ν₂ := ⟨hν, h2.le⟩
  have hν3 : nu D n ∈ Ioc 0 ν₃ := ⟨hν, h3.le⟩
  have hν4 : nu D n ∈ Ioc 0 ν₄ := ⟨hν, h4.le⟩
  have hbν : b ≤ 1 / (3 * nu D n) := by
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * b)).1 h5.le
    nlinarith
  have hbθ : ∀ r ∈ Icc (0 : ℝ) (2 / nu D n), b ≤ IIIa.clockTheta (nu D n) r := fun r hr =>
    hbν.trans (clockTheta_inv_bounds hν hr).2.2
  have hPF : IIIa.PerFrameFacts κ (nu D n) m b K := hPF' (nu D n) hν1
  obtain ⟨tr', hbuc', hcast⟩ :=
    exists_train_cast m (cOf_eq_rpow hν) (D.train n) (D.train_buc n)
  obtain ⟨u, hu⟩ := FI.ev.flow t ht.1 x
  have hflow := hcast t _ _ u hu
  have hzero : IIIa.HasZeroCirculation (nu D n ^ (-2 : ℝ)) (xFn x) := by
    rw [← cOf_eq_rpow hν]
    exact xFn_zeroCirc x
  have hts : t ≤ s := hs.1
  have hbs : b ≤ IIIa.clockTheta (nu D n) s := hbθ s ⟨ht.1.trans hts, hs.2⟩
  obtain ⟨-, hftc, hdec⟩ := hW' (nu D n) hν2 hPF tr' hbuc' t s ht.1 hts hbs (xFn x)
    (fun q => xFn (FI.ev.U q t x)) u hflow hzero
  have hcpl := hCC' (nu D n) hν4 hPF tr' hbuc' t s ht.1 hts hbs (xFn x)
    (fun q => xFn (FI.ev.U q t x)) u hflow hzero
  refine ampDiff_le hm D.Pl hν hPF tr' FI ht.1 x hts hs.2 hC₁ hC₂
    (by linarith) (by linarith) hftc hdec ?_ hcpl j
  intro r hr jj
  exact hDE' (nu D n) hν3 hPF tr' hbuc' r (ht.1.trans hr.1.le)
    (hbθ r ⟨ht.1.trans hr.1.le, hr.2.trans hs.2⟩) jj

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

end
