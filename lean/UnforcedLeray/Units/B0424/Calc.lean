import UnforcedLeray.Lib.PhaseTrace
import UnforcedLeray.Units.B0005.Bridge.Weak
import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0423

/-!
# B0424, part 2: the chain rule for the tests of the fixed-window estimate

Blueprint unit B0424 (`eq:free-stress-13`, `-14`, `-15`), `paper/main.tex` lines 7479–7517.
"Direct differentiation gives (13)" (tex 7491) and the time change gives (14) (tex 7495–7499):
in distributions, these are identities for transformed tests. This file computes the
transformed tests.

* `cmb c m b Ψ (τ, y) = c(τ) Ψ(m(τ), b(τ) y)`, with its spatial (`fderiv_cmb_space`) and time
  (`fderiv_cmb_time`) directional derivatives.
* **The phase test of (13)** (`phaseTest τ₀ Ξ e`): for a test `Ξ(t, x)` on `ℝ × ℝ³`,
  `G(τ, y) = e^t Ξ(t, e^{t/2} y) e`, `t = τ - τ₀`. It is a smooth test with bounded support
  (`isPhaseTest_phaseTest`, `timeSupp_phaseTest`), and the transpose of `L₀` falls on the
  transpose of `∂_t - νe^tΔ_x` (`L0T_phaseTest`):
  `L₀ᵗ G(τ, y) = e^t (-∂_tΞ - νe^tΔ_xΞ)(t, e^{t/2} y) e`.
* `L0T_perT`: `L₀ᵗ` commutes with periodization in the phase.

Status: infrastructure for `Units/B0424.lean`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0424

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Parabolic

/-! ### Functions of the form `c(τ) Ψ(m(τ), b(τ) y)` -/

/-- `cmb c m b Ψ (τ, y) = c(τ) Ψ(m(τ), b(τ) y)`. -/
def cmb (c m b : ℝ → ℝ) (Ψ : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  c p.1 * Ψ (m p.1, b p.1 • p.2)

theorem sdir_eq (j : Fin 3) : (sdir j : PS 3) = ((0 : ℝ), coordinateVector j) := rfl

/-- The spatial directional derivative of `c(τ) Ψ(m(τ), b(τ) y)`. -/
theorem fderiv_cmb_space {Ψ : ℝ × Space → ℝ} {c m b : ℝ → ℝ} {p : ℝ × Space}
    (hf : DifferentiableAt ℝ (cmb c m b Ψ) p) (hΨ : DifferentiableAt ℝ Ψ (m p.1, b p.1 • p.2))
    (v : Space) :
    fderiv ℝ (cmb c m b Ψ) p (0, v) =
      c p.1 * (b p.1 * fderiv ℝ Ψ (m p.1, b p.1 • p.2) (0, v)) := by
  refine fderiv_apply_of_hasDerivAt hf ?_
  have hγ : HasDerivAt (fun s : ℝ => ((m p.1, b p.1 • (p.2 + s • v)) : ℝ × Space))
      ((0 : ℝ), b p.1 • v) 0 := by
    refine (hasDerivAt_const (0 : ℝ) (m p.1)).prodMk ?_
    exact ((((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add p.2).const_smul (b p.1)).congr_deriv
      (by simp)
  have h := hΨ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have h2 := h.const_mul (c p.1)
  have e1 : (fun s : ℝ => cmb c m b Ψ (p + s • ((0 : ℝ), v))) =
      fun s => c p.1 * (Ψ ∘ fun s : ℝ => ((m p.1, b p.1 • (p.2 + s • v)) : ℝ × Space)) s := by
    funext s; simp [cmb]
  rw [e1]
  refine h2.congr_deriv ?_
  rw [show ((0 : ℝ), b p.1 • v) = b p.1 • ((0 : ℝ), v) by simp, map_smul, smul_eq_mul]

/-- The time directional derivative of `c(τ) Ψ(m(τ), b(τ) y)`. -/
theorem fderiv_cmb_time {Ψ : ℝ × Space → ℝ} {c m b : ℝ → ℝ} {c' m' b' : ℝ} {p : ℝ × Space}
    (hf : DifferentiableAt ℝ (cmb c m b Ψ) p) (hΨ : DifferentiableAt ℝ Ψ (m p.1, b p.1 • p.2))
    (hc : HasDerivAt c c' p.1) (hm : HasDerivAt m m' p.1) (hb : HasDerivAt b b' p.1) :
    fderiv ℝ (cmb c m b Ψ) p (1, 0) =
      c' * Ψ (m p.1, b p.1 • p.2) + c p.1 * fderiv ℝ Ψ (m p.1, b p.1 • p.2) (m', b' • p.2) := by
  refine fderiv_apply_of_hasDerivAt hf ?_
  have hc0 : HasDerivAt (fun s => c (p.1 + s)) c' 0 :=
    HasDerivAt.comp_const_add p.1 0 (by rw [add_zero]; exact hc)
  have hm0 : HasDerivAt (fun s => m (p.1 + s)) m' 0 :=
    HasDerivAt.comp_const_add p.1 0 (by rw [add_zero]; exact hm)
  have hb0 : HasDerivAt (fun s => b (p.1 + s)) b' 0 :=
    HasDerivAt.comp_const_add p.1 0 (by rw [add_zero]; exact hb)
  have hγ : HasDerivAt (fun s : ℝ => ((m (p.1 + s), b (p.1 + s) • p.2) : ℝ × Space))
      (m', b' • p.2) 0 := hm0.prodMk (hb0.smul_const p.2)
  have h := hΨ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have h2 := hc0.mul h
  have e1 : (fun s : ℝ => cmb c m b Ψ (p + s • ((1 : ℝ), (0 : Space)))) =
      fun s => c (p.1 + s) *
        (Ψ ∘ fun s : ℝ => ((m (p.1 + s), b (p.1 + s) • p.2) : ℝ × Space)) s := by
    funext s; simp [cmb]
  rw [e1]
  refine h2.congr_deriv ?_
  simp

theorem contDiff_cmb {Ψ : ℝ × Space → ℝ} {c m b : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hc : ContDiff ℝ ∞ c) (hm : ContDiff ℝ ∞ m) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (cmb c m b Ψ) := by
  unfold cmb
  exact (hc.comp contDiff_fst).mul
    (hΨ.comp ((hm.comp contDiff_fst).prodMk ((hb.comp contDiff_fst).smul contDiff_snd)))

/-- The spatial derivative of `cmb` as a function: `∂_j (c Ψ(m, b y)) = c b (∂_jΨ)(m, b y)`. -/
theorem sD_cmb {Ψ : ℝ × Space → ℝ} {c m b : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hc : ContDiff ℝ ∞ c) (hm : ContDiff ℝ ∞ m) (hb : ContDiff ℝ ∞ b) (j : Fin 3) :
    sD j (cmb c m b Ψ : PS 3 → ℝ) = cmb (fun τ => c τ * b τ) m b (sD j Ψ) := by
  funext p
  have hd := ((contDiff_cmb hΨ hc hm hb).differentiable (by simp)) p
  show fderiv ℝ (cmb c m b Ψ) p ((0 : ℝ), coordinateVector j) = _
  rw [fderiv_cmb_space hd ((hΨ.differentiable (by simp)) _)]
  simp only [cmb]
  rw [← mul_assoc]
  rfl

/-- The spatial Laplacian of `cmb`: `Δ (c Ψ(m, b y)) = c b² (ΔΨ)(m, b y)`. -/
theorem sLap_cmb {Ψ : ℝ × Space → ℝ} {c m b : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hc : ContDiff ℝ ∞ c) (hm : ContDiff ℝ ∞ m) (hb : ContDiff ℝ ∞ b) (p : ℝ × Space) :
    sLap (cmb c m b Ψ : PS 3 → ℝ) p = c p.1 * b p.1 ^ 2 * sLap Ψ (m p.1, b p.1 • p.2) := by
  simp only [sLap]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show sD j (sD j (cmb c m b Ψ : PS 3 → ℝ)) p = _
  rw [sD_cmb hΨ hc hm hb, sD_cmb (isSTTest_sD_contDiff hΨ j) (hc.mul hb) hm hb]
  simp only [cmb]
  ring
where
  isSTTest_sD_contDiff {Ψ : ℝ × Space → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (j : Fin 3) :
      ContDiff ℝ ∞ (sD j (Ψ : PS 3 → ℝ)) :=
    (hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ### Vector tests `s(p) e` and the scalar transpose of `L₀` -/

/-- The scalar form of `L₀ᵗ = -∂_τ + ½ y·∇ + 3/2 - νΔ - ½` (tex 7318–7319). -/
def L0S (ν : ℝ) (s : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  -tD (s : PS 3 → ℝ) p + (1 / 2 : ℝ) * ∑ j : Fin 3, p.2 j * sD j (s : PS 3 → ℝ) p + s p -
    ν * sLap (s : PS 3 → ℝ) p

theorem fderiv_smul_e {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (e : CVec3) (p v : ℝ × Space) :
    fderiv ℝ (fun p => s p • e) p v = fderiv ℝ s p v • e := by
  rw [fderiv_smul_const ((hs.differentiable (by simp)) p) e,
    ContinuousLinearMap.smulRight_apply]

theorem contDiff_sD {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (j : Fin 3) :
    ContDiff ℝ ∞ (sD j (s : PS 3 → ℝ)) :=
  (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dy_smul_e {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (e : CVec3) (j : Fin 3) :
    dy j (fun p => s p • e) = fun p => sD j (s : PS 3 → ℝ) p • e := by
  funext p
  simp only [dy]
  rw [fderiv_smul_e hs]
  rfl

theorem lapT_smul_e {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (e : CVec3) (p : ℝ × Space) :
    lapT (fun p => s p • e) p = sLap (s : PS 3 → ℝ) p • e := by
  simp only [lapT]
  simp_rw [dy_smul_e hs, dy_smul_e (contDiff_sD hs _)]
  rw [sLap, Finset.sum_smul]

/-- `L₀ᵗ (s e) = (L₀ᵗ s) e` for a smooth scalar `s`. -/
theorem L0T_smul_e {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (ν : ℝ) (e : CVec3) :
    B0411.L0T ν (fun p => s p • e) = fun p => L0S ν s p • e := by
  funext p
  have hdt : dτ (fun p => s p • e) p = tD (s : PS 3 → ℝ) p • e := by
    simp only [dτ]; rw [fderiv_smul_e hs]; rfl
  have hrad : radialT (fun p => s p • e) p =
      (∑ j : Fin 3, p.2 j * sD j (s : PS 3 → ℝ) p) • e := by
    simp only [radialT]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dy_smul_e hs, smul_smul]
  simp only [B0411.L0T, nuLapT, driftT, Pi.sub_apply, Pi.smul_apply, hdt, hrad, lapT_smul_e hs,
    L0S, smul_smul]
  module

theorem sum_mul_fderiv_coord (L : ℝ × Space →L[ℝ] ℝ) (y : Space) :
    ∑ j : Fin 3, y j * L ((0 : ℝ), coordinateVector j) = L ((0 : ℝ), y) := by
  have h : ((0 : ℝ), y) = ∑ j : Fin 3, y j • ((0 : ℝ), coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_mk, smul_zero, Finset.sum_const_zero]
    · simp only [Prod.snd_sum, Prod.smul_mk]
      exact (sum_smul_coordinateVector y).symm
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul]

/-! ### The phase test of `eq:free-stress-13` -/

/-- The scalar profile `e^t Ξ(t, e^{t/2} y)`, `t = τ - τ₀`. -/
def phaseScal (τ₀ : ℝ) (Ξ : ℝ × Space → ℝ) : ℝ × Space → ℝ :=
  cmb (fun τ => Real.exp (τ - τ₀)) (fun τ => τ - τ₀) (fun τ => Real.exp ((τ - τ₀) / 2)) Ξ

/-- **The phase test of (13)** (tex 7485–7491): `G(τ, y) = e^t Ξ(t, e^{t/2} y) e`,
`t = τ - τ₀`, the pullback of a test `Ξ(t, x)` along `x = e^{t/2} y`, weighted by `e^t`. -/
def phaseTest (τ₀ : ℝ) (Ξ : ℝ × Space → ℝ) (e : CVec3) : ℝ × Space → CVec3 :=
  fun p => phaseScal τ₀ Ξ p • e

theorem phaseScal_apply (τ₀ : ℝ) (Ξ : ℝ × Space → ℝ) (p : ℝ × Space) :
    phaseScal τ₀ Ξ p =
      Real.exp (p.1 - τ₀) * Ξ (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) := rfl

theorem contDiff_phaseScal (τ₀ : ℝ) {Ξ : ℝ × Space → ℝ} (hΞ : ContDiff ℝ ∞ Ξ) :
    ContDiff ℝ ∞ (phaseScal τ₀ Ξ) :=
  contDiff_cmb hΞ (Real.contDiff_exp.comp (contDiff_id.sub contDiff_const))
    (contDiff_id.sub contDiff_const)
    (Real.contDiff_exp.comp ((contDiff_id.sub contDiff_const).div_const 2))

/-- **`L₀ᵗ` of the phase test** (tex 7491, in distributions):
`L₀ᵗ G(τ, y) = e^t (-∂_tΞ - νe^tΔ_xΞ)(t, e^{t/2} y) e`, `t = τ - τ₀`. -/
theorem L0S_phaseScal (τ₀ : ℝ) {Ξ : ℝ × Space → ℝ} (hΞ : ContDiff ℝ ∞ Ξ) (ν : ℝ)
    (p : ℝ × Space) :
    L0S ν (phaseScal τ₀ Ξ) p =
      Real.exp (p.1 - τ₀) * (-tD (Ξ : PS 3 → ℝ) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) -
        ν * Real.exp (p.1 - τ₀) *
          sLap (Ξ : PS 3 → ℝ) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2)) := by
  have hc : ContDiff ℝ ∞ (fun τ : ℝ => Real.exp (τ - τ₀)) :=
    Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)
  have hm : ContDiff ℝ ∞ (fun τ : ℝ => τ - τ₀) := contDiff_id.sub contDiff_const
  have hb : ContDiff ℝ ∞ (fun τ : ℝ => Real.exp ((τ - τ₀) / 2)) :=
    Real.contDiff_exp.comp ((contDiff_id.sub contDiff_const).div_const 2)
  have hd := ((contDiff_phaseScal τ₀ hΞ).differentiable (by simp)) p
  have hΞd := (hΞ.differentiable (by simp)) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2)
  -- time derivative
  have hct : HasDerivAt (fun τ : ℝ => Real.exp (τ - τ₀)) (Real.exp (p.1 - τ₀)) p.1 := by
    simpa using ((hasDerivAt_id' p.1).sub_const τ₀).exp
  have hmt : HasDerivAt (fun τ : ℝ => τ - τ₀) 1 p.1 := (hasDerivAt_id' p.1).sub_const τ₀
  have hbt : HasDerivAt (fun τ : ℝ => Real.exp ((τ - τ₀) / 2))
      (Real.exp ((p.1 - τ₀) / 2) * (1 / 2)) p.1 :=
    (((hasDerivAt_id' p.1).sub_const τ₀).div_const 2).exp
  have ht : tD (phaseScal τ₀ Ξ : PS 3 → ℝ) p =
      Real.exp (p.1 - τ₀) * Ξ (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) +
        Real.exp (p.1 - τ₀) * (tD (Ξ : PS 3 → ℝ) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) +
          Real.exp ((p.1 - τ₀) / 2) * (1 / 2) *
            fderiv ℝ Ξ (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) ((0 : ℝ), p.2)) := by
    show fderiv ℝ (phaseScal τ₀ Ξ) p ((1 : ℝ), (0 : Space)) = _
    rw [phaseScal, fderiv_cmb_time hd hΞd hct hmt hbt]
    congr 2
    rw [show ((1 : ℝ), (Real.exp ((p.1 - τ₀) / 2) * (1 / 2)) • p.2) =
        ((1 : ℝ), (0 : Space)) + (Real.exp ((p.1 - τ₀) / 2) * (1 / 2)) • ((0 : ℝ), p.2) by
      ext <;> simp, map_add, map_smul, smul_eq_mul]
    rfl
  have hs : ∀ j : Fin 3, sD j (phaseScal τ₀ Ξ : PS 3 → ℝ) p =
      Real.exp (p.1 - τ₀) * (Real.exp ((p.1 - τ₀) / 2) *
        fderiv ℝ Ξ (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) ((0 : ℝ), coordinateVector j)) :=
    fun j => fderiv_cmb_space hd hΞd _
  have hrad : ∑ j : Fin 3, p.2 j * sD j (phaseScal τ₀ Ξ : PS 3 → ℝ) p =
      Real.exp (p.1 - τ₀) * (Real.exp ((p.1 - τ₀) / 2) *
        fderiv ℝ Ξ (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) ((0 : ℝ), p.2)) := by
    simp_rw [hs]
    rw [← sum_mul_fderiv_coord, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hl : sLap (phaseScal τ₀ Ξ : PS 3 → ℝ) p =
      Real.exp (p.1 - τ₀) * Real.exp ((p.1 - τ₀) / 2) ^ 2 *
        sLap (Ξ : PS 3 → ℝ) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) :=
    sLap_cmb hΞ hc hm hb p
  have hsq : Real.exp ((p.1 - τ₀) / 2) ^ 2 = Real.exp (p.1 - τ₀) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [L0S, ht, hrad, hl, hsq, phaseScal_apply]
  ring

theorem L0T_phaseTest (τ₀ : ℝ) {Ξ : ℝ × Space → ℝ} (hΞ : ContDiff ℝ ∞ Ξ) (ν : ℝ) (e : CVec3) :
    B0411.L0T ν (phaseTest τ₀ Ξ e) = fun p =>
      (Real.exp (p.1 - τ₀) * (-tD (Ξ : PS 3 → ℝ) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2) -
        ν * Real.exp (p.1 - τ₀) *
          sLap (Ξ : PS 3 → ℝ) (p.1 - τ₀, Real.exp ((p.1 - τ₀) / 2) • p.2))) • e := by
  show B0411.L0T ν (fun p => phaseScal τ₀ Ξ p • e) = _
  rw [L0T_smul_e (contDiff_phaseScal τ₀ hΞ)]
  funext p
  rw [L0S_phaseScal τ₀ hΞ]

/-- The phase test vanishes outside the phase window `[τ₀ - R, τ₀ + R]` and for
`|y| > R e^{R/2}` when `Ξ` vanishes outside `[-R, R] × B_R`. -/
theorem phaseTest_supp {Ξ : ℝ × Space → ℝ} {R : ℝ} (hR : 0 ≤ R) (hT : TimeSupp (-R) R Ξ)
    (hS : ∀ t y, R < ‖y‖ → Ξ (t, y) = 0) (τ₀ : ℝ) (e : CVec3) :
    TimeSupp (τ₀ - R) (τ₀ + R) (phaseTest τ₀ Ξ e) ∧
      ∀ τ y, R * Real.exp (R / 2) < ‖y‖ → phaseTest τ₀ Ξ e (τ, y) = 0 := by
  constructor
  · intro τ y hτ
    have : τ - τ₀ ∉ Icc (-R) R := by
      intro h; exact hτ ⟨by linarith [h.1], by linarith [h.2]⟩
    simp [phaseTest, phaseScal_apply, hT _ _ this]
  · intro τ y hy
    by_cases ht : τ - τ₀ ∈ Icc (-R) R
    · have h1 : Real.exp (-R / 2) ≤ Real.exp ((τ - τ₀) / 2) :=
        Real.exp_le_exp.2 (by linarith [ht.1])
      have h2 : R < ‖Real.exp ((τ - τ₀) / 2) • y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h3 : R < Real.exp (-R / 2) * ‖y‖ := by
          have h4 : R * Real.exp (R / 2) * Real.exp (-R / 2) = R := by
            rw [mul_assoc, ← Real.exp_add, show R / 2 + -R / 2 = 0 by ring, Real.exp_zero,
              mul_one]
          calc R = R * Real.exp (R / 2) * Real.exp (-R / 2) := h4.symm
            _ < ‖y‖ * Real.exp (-R / 2) :=
              mul_lt_mul_of_pos_right hy (Real.exp_pos _)
            _ = Real.exp (-R / 2) * ‖y‖ := mul_comm _ _
        exact h3.trans_le (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
      simp [phaseTest, phaseScal_apply, hS _ _ h2]
    · simp [phaseTest, phaseScal_apply, hT _ _ ht]

theorem isPhaseTest_phaseTest {Ξ : ℝ × Space → ℝ} (hΞ : ContDiff ℝ ∞ Ξ) {R : ℝ} (hR : 0 ≤ R)
    (hT : TimeSupp (-R) R Ξ) (hS : ∀ t y, R < ‖y‖ → Ξ (t, y) = 0) (τ₀ : ℝ) (e : CVec3) :
    IsPhaseTest 0 (phaseTest τ₀ Ξ e) where
  smooth := (contDiff_phaseScal τ₀ hΞ).smul contDiff_const
  periodic τ y := by simp
  bounded_support := ⟨_, (phaseTest_supp hR hT hS τ₀ e).2⟩

/-! ### `L₀ᵗ` commutes with periodization -/

theorem timeSupp_L0T {G : ℝ × Space → CVec3} {A B : ℝ} (hG : TimeSupp A B G) (ν : ℝ) :
    TimeSupp A B (B0411.L0T ν G) := by
  intro τ y hτ
  simp only [B0411.L0T, nuLapT, Pi.sub_apply, Pi.smul_apply, timeSupp_driftT hG τ y hτ,
    B0005.timeSupp_lapT hG τ y hτ, hG τ y hτ, smul_zero, sub_zero]

theorem L0T_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → CVec3} {A B : ℝ} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) (ν : ℝ) : B0411.L0T ν (perT P G) = perT P (B0411.L0T ν G) := by
  have hdr := driftT_perT hP hG hGs
  have hla := B0005.lapT_perT hP hG hGs
  funext p₀
  have hidx : ∀ {H : ℝ × Space → CVec3}, TimeSupp A B H → perT P H p₀ =
      ∑ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1), H (p₀.1 + k * P, p₀.2) := fun hH =>
    perT_eq_sum hH _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)
  have e1 : B0411.L0T ν (perT P G) p₀ =
      driftT (perT P G) p₀ - ν • lapT (perT P G) p₀ - (1 / 2 : ℝ) • perT P G p₀ := rfl
  rw [e1, hdr, hla, hidx (timeSupp_driftT hG), hidx (B0005.timeSupp_lapT hG), hidx hG,
    hidx (timeSupp_L0T hG ν), Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  rfl

end UnforcedLeray.B0424
