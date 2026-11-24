import UnforcedLeray.Short.PartIIa.Sub.F03_1

/-!
# Part II-a, task `PartII-a:F03/1/6`: the local identity at the pulled-back test

Source of record: `the November 2 reference manuscript`, lines 1431-1434 (cutoff
`χ`, `θ = e^t`, the window identity). Old manuscript: `paper/main.tex` lines 7479-7510.
Statement: `WindowTestIdentity` (`Short/PartII-a/Sub/F03_1.lean`), proved here unchanged.

Proof. The test `Ξ(t, x) = χ(t) φ(e^t, x)` is `B0424.timeTest χ φ`, and `Ψ = phaseTest τ₀ Ξ e_c`.
`LocalIdentity` at `Ψ` reads `∫ (μΨ + L₀ᵗΨ)·W = ∫ Ψ·Fr`. By `L0T_phaseTest`, `tD_timeTest` and
`sLap_timeTest`, the field `μΨ + L₀ᵗΨ` equals `(μ a₁ - a₂ + a₃) e_c`, where `a_k = phaseScal τ₀ Ξ_k`,
`Ξ₁ = timeTest χ φ`, `Ξ₂ = timeTest χ' φ`, `Ξ₃ = timeTest χ ψ` and `ψ(θ, x) = θ ζ(θ, x)` with
`ζ = -∂_t φ - ν Δφ`. Each integral `∫ a_k W_c` is shifted to `τ = τ₀ + t` by `integral_shift`.
Helpers carry the prefix `wti`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.B0411 UnforcedLeray.Parabolic

/-! ### Helpers -/

/-- The unit vector `e_c` of `ℂ³`. -/
abbrev wtiE (c : Fin 3) : CVec3 := EuclideanSpace.single c (1 : ℂ)

/-- `ζ(X) = -∂_t φ(X) - ν Δφ(X)`. -/
def wtiZeta (ν : ℝ) (φ : PS 3 → ℝ) : PS 3 → ℝ := fun X => -tD φ X - ν * sLap φ X

/-- `ψ(θ, x) = θ ζ(θ, x)`. -/
def wtiPsi (ν : ℝ) (φ : PS 3 → ℝ) : PS 3 → ℝ := fun X => X.1 * wtiZeta ν φ X

/-- The scalar profile `phaseScal τ₀ Ξ` paired with the `c`-component of `V`. -/
def wtiF (τ₀ : ℝ) (Ξ : ℝ × Space → ℝ) (V : ℝ × Space → CVec3) (c : Fin 3) (p : ℝ × Space) : ℂ :=
  (B0424.phaseScal τ₀ Ξ p : ℂ) * V p c

theorem wti_exists_bound {Ξ : ℝ × Space → ℝ} (hΞc : HasCompactSupport Ξ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t y, R < |t| ∨ R < ‖y‖ → Ξ (t, y) = 0 := by
  obtain ⟨M, hM⟩ := hΞc.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  refine ⟨max M 0, le_max_right _ _, fun t y h => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have h1 := hM hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : |t| ≤ ‖((t, y) : ℝ × Space)‖ := by
    simpa [Real.norm_eq_abs] using norm_fst_le ((t, y) : ℝ × Space)
  have h3 : ‖y‖ ≤ ‖((t, y) : ℝ × Space)‖ := norm_snd_le ((t, y) : ℝ × Space)
  rcases h with h | h <;> linarith [le_max_left M 0]

theorem wti_phaseTest_cs (τ₀ : ℝ) {Ξ : ℝ × Space → ℝ} (hΞ : ContDiff ℝ ∞ Ξ)
    (hΞc : HasCompactSupport Ξ) (e : CVec3) :
    ContDiff ℝ ∞ (B0424.phaseTest τ₀ Ξ e) ∧ HasCompactSupport (B0424.phaseTest τ₀ Ξ e) := by
  obtain ⟨R, hR0, hR⟩ := wti_exists_bound hΞc
  have hT : TimeSupp (-R) R Ξ := by
    intro τ y hτ
    apply hR
    left
    by_contra h
    push_neg at h
    exact hτ (abs_le.mp h)
  have hS : ∀ t y, R < ‖y‖ → Ξ (t, y) = 0 := fun t y hy => hR t y (Or.inr hy)
  obtain ⟨hTS, hSS⟩ := B0424.phaseTest_supp hR0 hT hS τ₀ e
  refine ⟨(B0424.contDiff_phaseScal τ₀ hΞ).smul contDiff_const, ?_⟩
  refine HasCompactSupport.intro
    (K := Icc (τ₀ - R) (τ₀ + R) ×ˢ Metric.closedBall (0 : Space) (R * Real.exp (R / 2)))
    ((isCompact_Icc).prod (isCompact_closedBall _ _)) fun p hp => ?_
  by_cases h1 : p.1 ∈ Icc (τ₀ - R) (τ₀ + R)
  · have h2 : p.2 ∉ Metric.closedBall (0 : Space) (R * Real.exp (R / 2)) :=
      fun h2 => hp (mk_mem_prod h1 h2)
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h2
    exact hSS p.1 p.2 h2
  · exact hTS p.1 p.2 h1

theorem wti_dotL_single (c : Fin 3) (r : ℂ) (w : CVec3) :
    dotL (r • wtiE c) w = r * w c := by
  rw [dotL_apply, Finset.sum_eq_single c]
  · simp [wtiE, EuclideanSpace.single_apply]
  · intro b _ hb
    simp [wtiE, EuclideanSpace.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem wti_dotL_real (c : Fin 3) (x : ℝ) (w : CVec3) :
    dotL ((x : ℝ) • wtiE c) w = (x : ℂ) * w c := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), wti_dotL_single]
  rfl

theorem wti_dotL_phaseTest (τ₀ : ℝ) (Ξ : ℝ × Space → ℝ) (c : Fin 3) (w : CVec3) (p : ℝ × Space) :
    dotL (B0424.phaseTest τ₀ Ξ (wtiE c) p) w = (B0424.phaseScal τ₀ Ξ p : ℂ) * w c :=
  wti_dotL_real c _ w

theorem wti_integrable {V : ℝ × Space → CVec3}
    (hV : ∀ G : ℝ × Space → CVec3, Continuous G → HasCompactSupport G →
      Integrable (fun p => dotL (G p) (V p)) volume)
    (τ₀ : ℝ) (c : Fin 3) {Ξ : ℝ × Space → ℝ} (hΞ : ContDiff ℝ ∞ Ξ)
    (hΞc : HasCompactSupport Ξ) :
    Integrable (wtiF τ₀ Ξ V c) volume := by
  obtain ⟨hs, hc⟩ := wti_phaseTest_cs τ₀ hΞ hΞc (wtiE c)
  refine (hV (B0424.phaseTest τ₀ Ξ (wtiE c)) hs.continuous hc).congr
    (Eventually.of_forall fun p => ?_)
  exact wti_dotL_phaseTest τ₀ Ξ c (V p) p

theorem wti_shift_int (τ₀ : ℝ) {k : ℝ × Space → ℂ} (hk : Integrable k volume) :
    Integrable (fun p : ℝ × Space => k (τ₀ + p.1, p.2)) volume :=
  (B0424.integrable_shift_iff τ₀ k).mpr hk

theorem wti_phaseScal_shift (τ₀ t : ℝ) (y : Space) (g : ℝ → ℝ) (ψ : ℝ × Space → ℝ) :
    B0424.phaseScal τ₀ (B0424.timeTest g ψ) (τ₀ + t, y)
      = Real.exp t * (g t * ψ (Real.exp t, Real.exp (t / 2) • y)) := by
  simp [B0424.phaseScal_apply, B0424.timeTest_apply]

theorem wti_real_smul (x : ℝ) (e : CVec3) : x • e = (x : ℂ) • e := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The field `μΨ + L₀ᵗΨ` for `Ψ = phaseTest τ₀ (timeTest χ φ) e_c` is `(μ a₁ - a₂ + a₃) e_c`. -/
theorem wti_L0_decomp (ν : ℝ) (μ : ℂ) {χ : ℝ → ℝ} (hχs : ContDiff ℝ ∞ χ) {φ : PS 3 → ℝ}
    (hφs : ContDiff ℝ ∞ φ) (hΞ : ContDiff ℝ ∞ (B0424.timeTest χ φ : ℝ × Space → ℝ))
    (τ₀ : ℝ) (c : Fin 3) (p : ℝ × Space) :
    (μ • B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c)
        + B0411.L0T ν (B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c))) p
      = (μ * (B0424.phaseScal τ₀ (B0424.timeTest χ φ) p : ℂ)
          - (B0424.phaseScal τ₀ (B0424.timeTest (deriv χ) φ) p : ℂ)
          + (B0424.phaseScal τ₀ (B0424.timeTest χ (wtiPsi ν φ)) p : ℂ)) • wtiE c := by
  have hL := congrFun (B0424.L0T_phaseTest τ₀ hΞ ν (wtiE c)) p
  have hs : Real.exp (p.1 - τ₀) * (-tD (B0424.timeTest χ φ : PS 3 → ℝ)
        (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2)
      - ν * Real.exp (p.1 - τ₀) * sLap (B0424.timeTest χ φ : PS 3 → ℝ)
        (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2))
      = -(B0424.phaseScal τ₀ (B0424.timeTest (deriv χ) φ) p)
        + B0424.phaseScal τ₀ (B0424.timeTest χ (wtiPsi ν φ)) p := by
    simp only [B0424.phaseScal_apply, B0424.timeTest_apply, B0424.tD_timeTest hχs hφs,
      B0424.sLap_timeTest hχs hφs, wtiPsi, wtiZeta]
    ring
  rw [Pi.add_apply, Pi.smul_apply, hL]
  simp only [B0424.phaseTest]
  rw [hs, wti_real_smul, wti_real_smul, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

theorem wti_zeta_isSTTest (ν : ℝ) {φ : PS 3 → ℝ} (hφ : IsSTTest φ) :
    IsSTTest (wtiZeta ν φ) := by
  have hsL : IsSTTest (sLap φ) := by
    have h : sLap φ = sD2 0 0 φ + sD2 1 1 φ + sD2 2 2 φ := by
      funext X
      simp [sLap, Fin.sum_univ_three]
    rw [h]
    exact ((hφ.sD2 0 0).add (hφ.sD2 1 1)).add (hφ.sD2 2 2)
  have hT : IsSTTest (tD φ) := hφ.dirD tdir
  have h2 : wtiZeta ν φ = (-1 : ℝ) • tD φ + (-ν) • sLap φ := by
    funext X
    simp only [wtiZeta, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h2]
  exact (hT.smul (-1)).add (hsL.smul (-ν))

theorem wti_psi_isSTTest (ν : ℝ) {φ : PS 3 → ℝ} (hφ : IsSTTest φ) :
    IsSTTest (wtiPsi ν φ) := by
  have hζ := wti_zeta_isSTTest ν hφ
  refine ⟨?_, ?_⟩
  · exact contDiff_fst.mul hζ.1
  · exact HasCompactSupport.mul_left (f := fun X : PS 3 => X.1) hζ.2

/-! ### The local identity at the pulled-back test -/

/-- **Task `PartII-a:F03/1/6`**: the local identity at the pulled-back test `Ξ(t,x) = χ(t)φ(e^t,x)`
(tex 1431-1434; `Sub/F03_1.lean`). -/
theorem windowTestIdentity : WindowTestIdentity := by
  intro ν μ W Fr hW hFr hI χ hχ τ₀ c φ hφ
  have hχs : ContDiff ℝ ∞ χ := hχ.smooth
  have hχ' : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχs).2
  have hχ'c : HasCompactSupport (deriv χ) := hχ.compact.deriv
  have hφs : ContDiff ℝ ∞ φ := hφ.1
  have hΞ1 := B0424.isSTTest_timeTest hχs hχ.compact hφ
  have hΞ2 := B0424.isSTTest_timeTest hχ' hχ'c hφ
  have hΞ3 := B0424.isSTTest_timeTest hχs hχ.compact (wti_psi_isSTTest ν hφ)
  have hΨ := wti_phaseTest_cs τ₀ hΞ1.1 hΞ1.2 (wtiE c)
  have hI' := hI _ hΨ.1 hΨ.2
  have hF1 := wti_integrable hW τ₀ c hΞ1.1 hΞ1.2
  have hF2 := wti_integrable hW τ₀ c hΞ2.1 hΞ2.2
  have hF3 := wti_integrable hW τ₀ c hΞ3.1 hΞ3.2
  have hFR := wti_integrable hFr τ₀ c hΞ1.1 hΞ1.2
  -- the left side of the local identity
  have hLHS : ∫ p : ℝ × Space, dotL ((μ • B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c)
        + B0411.L0T ν (B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c))) p) (W p)
      = μ * (∫ p, wtiF τ₀ (B0424.timeTest χ φ) W c p)
        - (∫ p, wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c p)
        + ∫ p, wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c p := by
    have hfun : (fun p : ℝ × Space => dotL ((μ • B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c)
          + B0411.L0T ν (B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c))) p) (W p))
        = fun p => μ * wtiF τ₀ (B0424.timeTest χ φ) W c p
          - wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c p
          + wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c p := by
      funext p
      rw [wti_L0_decomp ν μ hχs hφs hΞ1.1 τ₀ c p, wti_dotL_single]
      simp only [wtiF]
      ring
    have hA : Integrable (fun p : ℝ × Space => μ * wtiF τ₀ (B0424.timeTest χ φ) W c p
        - wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c p) volume := (hF1.const_mul μ).sub hF2
    have hA' : Integrable (fun p : ℝ × Space => μ * wtiF τ₀ (B0424.timeTest χ φ) W c p) volume :=
      hF1.const_mul μ
    rw [hfun, integral_add hA hF3, integral_sub hA' hF2, integral_const_mul]
  -- the right side of the local identity
  have hRHS : ∫ p : ℝ × Space, dotL (B0424.phaseTest τ₀ (B0424.timeTest χ φ) (wtiE c) p) (Fr p)
      = ∫ p, wtiF τ₀ (B0424.timeTest χ φ) Fr c p :=
    integral_congr_ae (Eventually.of_forall fun p => wti_dotL_phaseTest τ₀ _ c (Fr p) p)
  -- translation `τ = τ₀ + t`
  have hK1e : ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ φ) W c (τ₀ + p.1, p.2)
      = ∫ p, wtiF τ₀ (B0424.timeTest χ φ) W c p :=
    B0424.integral_shift τ₀ (wtiF τ₀ (B0424.timeTest χ φ) W c)
  have hK2e : ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c (τ₀ + p.1, p.2)
      = ∫ p, wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c p :=
    B0424.integral_shift τ₀ (wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c)
  have hK3e : ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c (τ₀ + p.1, p.2)
      = ∫ p, wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c p :=
    B0424.integral_shift τ₀ (wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c)
  have hKRe : ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ φ) Fr c (τ₀ + p.1, p.2)
      = ∫ p, wtiF τ₀ (B0424.timeTest χ φ) Fr c p :=
    B0424.integral_shift τ₀ (wtiF τ₀ (B0424.timeTest χ φ) Fr c)
  have hK1i := wti_shift_int τ₀ hF1
  have hK2i := wti_shift_int τ₀ hF2
  have hK3i := wti_shift_int τ₀ hF3
  have hKRi := wti_shift_int τ₀ hFR
  have hK1μ : Integrable (fun p : ℝ × Space => μ * wtiF τ₀ (B0424.timeTest χ φ) W c (τ₀ + p.1, p.2))
      volume := hK1i.const_mul μ
  have hB : Integrable (fun p : ℝ × Space =>
      wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c (τ₀ + p.1, p.2)
        - μ * wtiF τ₀ (B0424.timeTest χ φ) W c (τ₀ + p.1, p.2)) volume := hK2i.sub hK1μ
  -- the local identity after translation
  have hfinal : μ * (∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ φ) W c (τ₀ + p.1, p.2))
      - (∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c (τ₀ + p.1, p.2))
      + (∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c (τ₀ + p.1, p.2))
      = ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ φ) Fr c (τ₀ + p.1, p.2) := by
    rw [hK1e, hK2e, hK3e, hKRe]
    linear_combination hI' + hRHS - hLHS
  -- the pointwise identities
  have hRpt : ∀ p : ℝ × Space,
      ((Real.exp p.1 : ℝ) : ℂ) * ((((deriv χ p.1 : ℝ) : ℂ) - μ * (χ p.1 : ℂ)) * W (τ₀ + p.1, p.2) c
        + (χ p.1 : ℂ) * Fr (τ₀ + p.1, p.2) c) * (φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℂ)
      = wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c (τ₀ + p.1, p.2)
        - μ * wtiF τ₀ (B0424.timeTest χ φ) W c (τ₀ + p.1, p.2)
        + wtiF τ₀ (B0424.timeTest χ φ) Fr c (τ₀ + p.1, p.2) := by
    intro p
    simp only [wtiF, wti_phaseScal_shift]
    push_cast
    ring
  have hL3 : ∀ p : ℝ × Space,
      ((Real.exp (2 * p.1) * χ p.1 : ℝ) : ℂ) * W (τ₀ + p.1, p.2) c
        * ((-tD φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2)
            - ν * sLap φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℝ) : ℂ)
      = wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c (τ₀ + p.1, p.2) := by
    intro p
    simp only [wtiF, wti_phaseScal_shift, wtiPsi, wtiZeta]
    rw [show Real.exp (2 * p.1) = Real.exp p.1 * Real.exp p.1 by rw [two_mul, Real.exp_add]]
    push_cast
    ring
  have hLt : ∫ p : ℝ × Space, ((Real.exp (2 * p.1) * χ p.1 : ℝ) : ℂ) * W (τ₀ + p.1, p.2) c
        * ((-tD φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2)
            - ν * sLap φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℝ) : ℂ)
      = ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ (wtiPsi ν φ)) W c (τ₀ + p.1, p.2) :=
    integral_congr_ae (Eventually.of_forall hL3)
  have hRsplit : ∫ p : ℝ × Space, ((Real.exp p.1 : ℝ) : ℂ)
        * ((((deriv χ p.1 : ℝ) : ℂ) - μ * (χ p.1 : ℂ)) * W (τ₀ + p.1, p.2) c
          + (χ p.1 : ℂ) * Fr (τ₀ + p.1, p.2) c) * (φ (Real.exp p.1, Real.exp (p.1 / 2) • p.2) : ℂ)
      = (∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest (deriv χ) φ) W c (τ₀ + p.1, p.2))
        - μ * (∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ φ) W c (τ₀ + p.1, p.2))
        + ∫ p : ℝ × Space, wtiF τ₀ (B0424.timeTest χ φ) Fr c (τ₀ + p.1, p.2) := by
    rw [integral_congr_ae (Eventually.of_forall hRpt), integral_add hB hKRi,
      integral_sub hK2i hK1μ, integral_const_mul]
  linear_combination hLt - hRsplit + hfinal

end UnforcedLeray.Short.PartIIa
