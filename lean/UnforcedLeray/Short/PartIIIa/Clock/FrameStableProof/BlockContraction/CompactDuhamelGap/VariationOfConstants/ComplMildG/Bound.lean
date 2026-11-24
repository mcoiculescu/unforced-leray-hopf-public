import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildG.KerDecay
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CurlBound

/-!
# Uniform `X_{m,d(r)}` bound of the mode residuals on a block (SP 2905, 2914-2925)

On a block `[t₁, t₂]` with `θ ≥ 1` and `d(r) ≥ 1`, the residual
`Ψ_j(r) = θ(r)⁻¹ P_{d(r)}(D e_j) + L_{ν,c}(r) E_j - λ_j E_j` is bounded in `X_{m,d(r)}` uniformly
in `r` and `j`, for every `ν > 0` and every BUC train: the oscillator part and the transport,
eigenvalue parts are Gaussian on the cell, the train coefficients are bounded on the block
(BUC class), and the kernel velocity `K_d E_j` decays exponentially in `|y₂|`
(`kerVelCx_perE_decay`), uniformly for `d` in a bounded range.  The weight `⟨y⟩^{2m}` is absorbed
by `xNorm_le_of_jb_pow`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace ComplMildGAux

open EulerErrorSub OscillatorForceSub

/-- `(1 + t)^k e^{-βt} ≤ k! β^{-k} e^β` for `t ≥ 0`. -/
theorem one_add_pow_mul_exp_neg_le (k : ℕ) {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ k * Real.exp (-(β * t)) ≤ (k.factorial : ℝ) / β ^ k * Real.exp β := by
  have h := Real.pow_div_factorial_le_exp (x := β * (1 + t)) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hb : 0 < β ^ k := by positivity
  rw [div_le_iff₀ hf, mul_pow] at h
  have hexp : Real.exp (β * (1 + t)) = Real.exp β * Real.exp (β * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at h
  have key : (1 + t) ^ k * β ^ k ≤ (k.factorial : ℝ) * Real.exp β * Real.exp (β * t) := by
    nlinarith [h]
  have hE : Real.exp (β * t) * Real.exp (-(β * t)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [div_mul_eq_mul_div, le_div_iff₀ hb]
  calc (1 + t) ^ k * Real.exp (-(β * t)) * β ^ k
      = ((1 + t) ^ k * β ^ k) * Real.exp (-(β * t)) := by ring
    _ ≤ ((k.factorial : ℝ) * Real.exp β * Real.exp (β * t)) * Real.exp (-(β * t)) := by
        gcongr
    _ = (k.factorial : ℝ) * Real.exp β := by
        rw [mul_assoc ((k.factorial : ℝ) * Real.exp β), hE, mul_one]

/-- The weight `⟨y⟩^{2k}` times the cell Gaussian is bounded. -/
theorem jb_pow_mul_gauss_le (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ × ℝ,
    B0579.jb x ^ k * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) ≤ C := by
  refine ⟨(k.factorial : ℝ) / (1 / 16 : ℝ) ^ k * Real.exp (1 / 16), by positivity, fun x => ?_⟩
  have h := one_add_pow_mul_exp_neg_le k (β := 1 / 16) (by norm_num)
    (t := x.1 ^ 2 + x.2 ^ 2) (by positivity)
  have hjb : B0579.jb x = 1 + (x.1 ^ 2 + x.2 ^ 2) := by unfold B0579.jb; ring
  have hexp : -(x.1 ^ 2 + x.2 ^ 2) / 16 = -(1 / 16 * (x.1 ^ 2 + x.2 ^ 2)) := by ring
  rw [hjb, hexp]
  exact h

/-- The weight `⟨y⟩^{2k}` times the kernel velocity of `E_j` is bounded on the cell, uniformly
for `1 ≤ d ≤ D`. -/
theorem jb_pow_mul_kerVel_le {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (k : ℕ) {D : ℝ}
    (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d → d ≤ D → ∀ (j k' : Fin 2), ∀ x ∈ B0579.cell d,
      B0579.jb x ^ k * ‖kerVelCx d (perE κ d j) x k'‖ ≤ C := by
  obtain ⟨Q, hQ0, hQ⟩ := kerVelCx_perE_decay hκ
  obtain ⟨C_vel, hCv0, hCv⟩ := kerVelCx_perE_bound hκ
  have hD0 : 0 < D := by linarith
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = min (1 / 64) (Real.pi / D) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; exact lt_min (by norm_num) (by positivity)
  have hβ1 : β ≤ 1 / 64 := by rw [hβ]; exact min_le_left _ _
  have hβ2 : β ≤ Real.pi / D := by rw [hβ]; exact min_le_right _ _
  refine ⟨(5 + D ^ 2) ^ k * C_vel + (1 + D ^ 2) ^ k * (2 * Q) *
      (((2 * k).factorial : ℝ) / β ^ (2 * k) * Real.exp β), by positivity,
    fun d hd1 hdD j k' x hx => ?_⟩
  have hd0 : 0 < d := by linarith
  have hx1 : x.1 ^ 2 ≤ D ^ 2 := by
    simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true] at hx
    have : |x.1| ≤ D := by rw [abs_le]; constructor <;> linarith
    calc x.1 ^ 2 = |x.1| ^ 2 := (sq_abs _).symm
      _ ≤ D ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hjb0 : 0 ≤ B0579.jb x := by unfold B0579.jb; positivity
  have hs0 : 0 ≤ |x.2| := abs_nonneg _
  by_cases hx2 : |x.2| ≤ 2
  · have hjb : B0579.jb x ≤ 5 + D ^ 2 := by
      unfold B0579.jb
      have h4 : x.2 ^ 2 ≤ 4 := by nlinarith [sq_abs x.2]
      linarith
    have h1 : B0579.jb x ^ k * ‖kerVelCx d (perE κ d j) x k'‖ ≤ (5 + D ^ 2) ^ k * C_vel :=
      mul_le_mul (pow_le_pow_left₀ hjb0 hjb k) (hCv d hd1 j k' x) (norm_nonneg _)
        (by positivity)
    exact h1.trans (le_add_of_nonneg_right (by positivity))
  · have hy : 2 < |x.2| := lt_of_not_ge hx2
    have hK := hQ d hd1 j k' x hy
    have he1 : Real.exp (-(|x.2| / 2) / 32) ≤ Real.exp (-(β * |x.2|)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hβ1 hs0])
    have hπd : β ≤ Real.pi / d := hβ2.trans (div_le_div_of_nonneg_left Real.pi_pos.le hd0 hdD)
    have he2 : Real.exp (-(2 * Real.pi / d) * (|x.2| / 2)) ≤ Real.exp (-(β * |x.2|)) := by
      apply Real.exp_le_exp.mpr
      have : -(2 * Real.pi / d) * (|x.2| / 2) = -(Real.pi / d * |x.2|) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hπd hs0]
    have hK' : ‖kerVelCx d (perE κ d j) x k'‖ ≤ 2 * Q * Real.exp (-(β * |x.2|)) := by
      calc ‖kerVelCx d (perE κ d j) x k'‖
          ≤ Q * (Real.exp (-(|x.2| / 2) / 32) +
              Real.exp (-(2 * Real.pi / d) * (|x.2| / 2))) := hK
        _ ≤ Q * (Real.exp (-(β * |x.2|)) + Real.exp (-(β * |x.2|))) := by gcongr
        _ = 2 * Q * Real.exp (-(β * |x.2|)) := by ring
    have hjb : B0579.jb x ≤ (1 + D ^ 2) * (1 + |x.2|) ^ 2 := by
      unfold B0579.jb
      nlinarith [sq_abs x.2, sq_nonneg D, mul_nonneg (sq_nonneg D) hs0,
        mul_nonneg (sq_nonneg D) (sq_nonneg x.2)]
    have hpoly := one_add_pow_mul_exp_neg_le (2 * k) hβ0 hs0
    calc B0579.jb x ^ k * ‖kerVelCx d (perE κ d j) x k'‖
        ≤ ((1 + D ^ 2) * (1 + |x.2|) ^ 2) ^ k * (2 * Q * Real.exp (-(β * |x.2|))) :=
          mul_le_mul (pow_le_pow_left₀ hjb0 hjb k) hK' (norm_nonneg _) (by positivity)
      _ = (1 + D ^ 2) ^ k * (2 * Q) * ((1 + |x.2|) ^ (2 * k) * Real.exp (-(β * |x.2|))) := by
          rw [mul_pow, ← pow_mul, mul_comm 2 k]
          ring
      _ ≤ (1 + D ^ 2) ^ k * (2 * Q) * (((2 * k).factorial : ℝ) / β ^ (2 * k) * Real.exp β) := by
          gcongr
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- The rescaled BUC train coefficients are bounded on a block `[0, t₂]`. -/
theorem train_block_bounds {ν c : ℝ} (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t₂ : ℝ} (ht₂ : 0 ≤ t₂) :
    ∃ C_V C_G : ℝ, 0 ≤ C_V ∧ 0 ≤ C_G ∧ ∀ r ∈ Icc (0 : ℝ) t₂, ∀ (y : ℝ × ℝ) (k : Fin 2),
      |movingTrainV tr r y k| ≤ C_V ∧ |movingTrainGradE tr r y k| ≤ C_G := by
  obtain ⟨M₀, hM₀⟩ := htr.sup_bound ht₂
  obtain ⟨M₂, hM₂⟩ := htr.deriv_bound ht₂ 2
  obtain ⟨C₁, hC₁0, hC₁⟩ := UnforcedLeray.Short.PartI.curlJetBound_proof 1
  have hA2 : 1 ≤ clockA ν t₂ := one_le_clockA hν.le ht₂
  have hp3 : 0 ≤ clockA ν t₂ ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hp5 : 0 ≤ clockA ν t₂ ^ ((5 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  refine ⟨clockA ν t₂ ^ (3 / 2 : ℝ) * |M₀|, clockA ν t₂ ^ ((5 : ℝ) / 2) * (C₁ * |M₂|),
    mul_nonneg hp3 (abs_nonneg _), mul_nonneg hp5 (mul_nonneg hC₁0 (abs_nonneg _)),
    fun r hr y k => ⟨?_, ?_⟩⟩
  · have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr.1
    have haA : clockA ν r ≤ clockA ν t₂ := clockA_mono hν.le hr.2
    unfold movingTrainV
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hv : |tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) k| ≤ |M₀| := by
      have h1 := PiLp.norm_apply_le
        (tr.v r (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)) k
      rw [Real.norm_eq_abs] at h1
      exact h1.trans ((hM₀ r hr _).trans (le_abs_self _))
    exact mul_le_mul (Real.rpow_le_rpow (by linarith) haA (by norm_num)) hv (abs_nonneg _) hp3
  · have hr0 : 0 ≤ r := hr.1
    have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr0
    have haA : clockA ν r ≤ clockA ν t₂ := clockA_mono hν.le hr.2
    unfold movingTrainGradE
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hsmooth : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr0
    have hpd : ∀ z : ℝ × ℝ, |B0579.pd k (UnforcedLeray.B0238.Ec tr r) z| ≤ C₁ * |M₂| := by
      intro z
      unfold B0579.pd
      have hdir : ‖B0579.dir k‖ ≤ 1 := by
        fin_cases k <;> simp [B0579.dir, Prod.norm_def]
      have h1 : |fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z (B0579.dir k)| ≤
          ‖fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z‖ := by
        have := (fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z).le_opNorm (B0579.dir k)
        rw [Real.norm_eq_abs] at this
        calc _ ≤ _ := this
          _ ≤ ‖fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z‖ * 1 := by gcongr
          _ = _ := mul_one _
      have h2 : ‖fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z‖ =
          ‖iteratedFDeriv ℝ 1 (UnforcedLeray.Cyl.curl (tr.v r)) z‖ := by
        rw [norm_iteratedFDeriv_one]
        rfl
      have h3 := hC₁ (tr.v r) hsmooth z
      have h4 : ‖iteratedFDeriv ℝ 2 (tr.v r) z‖ ≤ M₂ := hM₂ r hr z
      calc |fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z (B0579.dir k)|
          ≤ ‖fderiv ℝ (UnforcedLeray.B0238.Ec tr r) z‖ := h1
        _ = ‖iteratedFDeriv ℝ 1 (UnforcedLeray.Cyl.curl (tr.v r)) z‖ := h2
        _ ≤ C₁ * ‖iteratedFDeriv ℝ (1 + 1) (tr.v r) z‖ := h3
        _ ≤ C₁ * |M₂| := by
          gcongr
          exact h4.trans (le_abs_self _)
    exact mul_le_mul (Real.rpow_le_rpow (by linarith) haA (by norm_num)) (hpd _) (abs_nonneg _)
      hp5

/-- Norm bound for the linearised Euler eigenmode defect expression. -/
theorem norm_eulerCombo_le (V0 V1 G0 G1 : ℝ) (p0 p1 K0 K1 l E : ℂ) {CV CG : ℝ}
    (hV0 : |V0| ≤ CV) (hV1 : |V1| ≤ CV) (hG0 : |G0| ≤ CG) (hG1 : |G1| ≤ CG) :
    ‖-((V0 : ℂ) * p0 + (V1 : ℂ) * p1) - (K0 * (G0 : ℂ) + K1 * (G1 : ℂ)) - l * E‖ ≤
      CV * ‖p0‖ + CV * ‖p1‖ + CG * ‖K0‖ + CG * ‖K1‖ + ‖l‖ * ‖E‖ := by
  have e1 : ‖(V0 : ℂ) * p0‖ ≤ CV * ‖p0‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; gcongr
  have e2 : ‖(V1 : ℂ) * p1‖ ≤ CV * ‖p1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; gcongr
  have e3 : ‖K0 * (G0 : ℂ)‖ ≤ CG * ‖K0‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]; gcongr
  have e4 : ‖K1 * (G1 : ℂ)‖ ≤ CG * ‖K1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]; gcongr
  have e5 : ‖l * E‖ = ‖l‖ * ‖E‖ := norm_mul _ _
  have a1 := norm_sub_le (-((V0 : ℂ) * p0 + (V1 : ℂ) * p1) - (K0 * (G0 : ℂ) + K1 * (G1 : ℂ)))
    (l * E)
  have a2 := norm_sub_le (-((V0 : ℂ) * p0 + (V1 : ℂ) * p1)) (K0 * (G0 : ℂ) + K1 * (G1 : ℂ))
  have a3 := norm_add_le ((V0 : ℂ) * p0) ((V1 : ℂ) * p1)
  have a4 := norm_add_le (K0 * (G0 : ℂ)) (K1 * (G1 : ℂ))
  rw [norm_neg] at a2
  linarith

/-- **Pointwise weighted bound of the mode residuals on a block.** -/
theorem psi_block_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν : ℝ} (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hθ : ∀ r ∈ Icc t₁ t₂, 1 ≤ clockTheta ν r) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      ∀ x ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        B0579.jb x ^ k * ‖movOscRes κ ν r j x + movEulerRes κ P tr r j x‖ ≤ M := by
  obtain ⟨-, C_D0, hCD0_pos, hCD0⟩ := movD_seed_decay hκ 0
  obtain ⟨-, C_D1, hCD1_pos, hCD1⟩ := movD_seed_decay hκ 1
  obtain ⟨M0, hM0_pos, hM0⟩ := perSum_pointwise_of_gauss hCD0_pos hCD0
  obtain ⟨M1, hM1_pos, hM1⟩ := perSum_pointwise_of_gauss hCD1_pos hCD1
  obtain ⟨M_E, hME0, hME⟩ := perE_and_pdCx_gauss_bounds hκ
  obtain ⟨C_V, C_G, hCV0, hCG0, hTr⟩ := train_block_bounds hν tr htr (ht₁.trans h12)
  obtain ⟨C_g, hCg0, hCg⟩ := jb_pow_mul_gauss_le k
  obtain ⟨C_K, hCK0, hCK⟩ := jb_pow_mul_kerVel_le hκ k (le_max_left 1 (ν ^ (-2 : ℝ)))
  set Λ : ℝ := ‖modeEigen P 0‖ + ‖modeEigen P 1‖ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛj : ∀ j : Fin 2, ‖modeEigen P j‖ ≤ Λ := by
    intro j
    fin_cases j
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  refine ⟨(max M0 M1 + (2 * C_V + Λ) * M_E) * C_g + 2 * C_G * C_K, by positivity,
    fun r hr j x hx => ?_⟩
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have hrI : r ∈ Icc (0 : ℝ) t₂ := ⟨hr0, hr.2⟩
  have hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := hd1 r hr
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr0
  have hdD : cellLen (ν ^ (-2 : ℝ)) (clockA ν r) ≤ max 1 (ν ^ (-2 : ℝ)) := by
    have hs : 1 ≤ Real.sqrt (clockA ν r) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt ha1
    unfold cellLen
    exact (div_le_self (Real.rpow_pos_of_pos hν _).le hs).trans (le_max_right _ _)
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  set g := Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) with hg
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hjb0 : 0 ≤ B0579.jb x := by unfold B0579.jb; positivity
  have hθpos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one (hθ r hr)
  -- oscillator part
  have hosc : ‖movOscRes κ ν r j x‖ ≤ max M0 M1 * g := by
    rw [movOscRes_eq_perSum_movD hκ hν hr0 j x, norm_mul, norm_inv,
      Complex.norm_of_nonneg hθpos.le]
    have hper : ‖perSum d (movD (κ.e j)) x‖ ≤ max M0 M1 * g := by
      fin_cases j
      · exact (hM0 d hd x hx).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      · exact (hM1 d hd x hx).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
    have hinv : (clockTheta ν r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hθ r hr)
    calc (clockTheta ν r)⁻¹ * ‖perSum d (movD (κ.e j)) x‖ ≤ 1 * (max M0 M1 * g) :=
          mul_le_mul hinv hper (norm_nonneg _) zero_le_one
      _ = max M0 M1 * g := one_mul _
  -- Euler part
  obtain ⟨hEcell, -, hpdcell⟩ := hME d hd j
  have heul : ‖movEulerRes κ P tr r j x‖ ≤
      (2 * C_V + Λ) * M_E * g + C_G * (‖kerVelCx d (perE κ d j) x 0‖ +
        ‖kerVelCx d (perE κ d j) x 1‖) := by
    have h := norm_eulerCombo_le (movingTrainV tr r x 0) (movingTrainV tr r x 1)
      (movingTrainGradE tr r x 0) (movingTrainGradE tr r x 1) (pdCx 0 (perE κ d j) x)
      (pdCx 1 (perE κ d j) x) (kerVelCx d (perE κ d j) x 0) (kerVelCx d (perE κ d j) x 1)
      (modeEigen P j) (perE κ d j x) (hTr r hrI x 0).1 (hTr r hrI x 1).1 (hTr r hrI x 0).2
      (hTr r hrI x 1).2
    have hmov : movEulerRes κ P tr r j x =
        -(((movingTrainV tr r x 0 : ℝ) : ℂ) * pdCx 0 (perE κ d j) x +
            ((movingTrainV tr r x 1 : ℝ) : ℂ) * pdCx 1 (perE κ d j) x) -
          (kerVelCx d (perE κ d j) x 0 * ((movingTrainGradE tr r x 0 : ℝ) : ℂ) +
            kerVelCx d (perE κ d j) x 1 * ((movingTrainGradE tr r x 1 : ℝ) : ℂ)) -
          modeEigen P j * perE κ d j x := rfl
    rw [hmov]
    refine h.trans ?_
    have hp0 := hpdcell 0 x hx
    have hp1 := hpdcell 1 x hx
    have hE := hEcell x hx
    have hl := hΛj j
    have t1 : C_V * ‖pdCx 0 (perE κ d j) x‖ ≤ C_V * (M_E * g) :=
      mul_le_mul_of_nonneg_left hp0 hCV0
    have t2 : C_V * ‖pdCx 1 (perE κ d j) x‖ ≤ C_V * (M_E * g) :=
      mul_le_mul_of_nonneg_left hp1 hCV0
    have t3 : ‖modeEigen P j‖ * ‖perE κ d j x‖ ≤ Λ * (M_E * g) :=
      mul_le_mul hl hE (norm_nonneg _) hΛ0
    nlinarith [t1, t2, t3]
  -- combine
  have hK0 := hCK d hd hdD j 0 x hx
  have hK1 := hCK d hd hdD j 1 x hx
  have hgC : B0579.jb x ^ k * g ≤ C_g := hCg x
  have hjbk : 0 ≤ B0579.jb x ^ k := pow_nonneg hjb0 k
  calc B0579.jb x ^ k * ‖movOscRes κ ν r j x + movEulerRes κ P tr r j x‖
      ≤ B0579.jb x ^ k * (max M0 M1 * g + ((2 * C_V + Λ) * M_E * g +
          C_G * (‖kerVelCx d (perE κ d j) x 0‖ + ‖kerVelCx d (perE κ d j) x 1‖))) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hosc heul)) hjbk
    _ = (max M0 M1 + (2 * C_V + Λ) * M_E) * (B0579.jb x ^ k * g) +
          C_G * (B0579.jb x ^ k * ‖kerVelCx d (perE κ d j) x 0‖ +
            B0579.jb x ^ k * ‖kerVelCx d (perE κ d j) x 1‖) := by ring
    _ ≤ (max M0 M1 + (2 * C_V + Λ) * M_E) * C_g + C_G * (C_K + C_K) := by
        gcongr
    _ = (max M0 M1 + (2 * C_V + Λ) * M_E) * C_g + 2 * C_G * C_K := by ring

/-- **Uniform `X_{m,d(r)}` bound of the mode residuals on a block.** -/
theorem psi_block_xNorm {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) (P : PlanarData)
    {ν : ℝ} (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hθ : ∀ r ∈ Icc t₁ t₂, 1 ≤ clockTheta ν r) {m : ℝ} (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc t₁ t₂, ∀ j : Fin 2,
      xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
        (fun y => movOscRes κ ν r j y + movEulerRes κ P tr r j y) ≤ ENNReal.ofReal C := by
  have h := xNorm_le_of_jb_pow (m := m) hm
  dsimp only at h
  obtain ⟨K_p, hKp0, hKp⟩ := h
  obtain ⟨M, hM0, hM⟩ := psi_block_bound hκ P hν tr htr ht₁ h12 hd1 hθ (Nat.ceil m + 2)
  exact ⟨M * K_p, by positivity, fun r hr j => hKp _ M _ hM0 (fun x hx => hM r hr j x hx)⟩

end ComplMildGAux

end UnforcedLeray.Short.IIIa
