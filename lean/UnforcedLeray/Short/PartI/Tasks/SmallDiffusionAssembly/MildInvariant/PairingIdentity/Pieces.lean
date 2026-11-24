import UnforcedLeray.Short.PartI.Sub.PartI_C05_4
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.EllL0
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.ExpDPairing
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.PairingIdentity.Fubini

/-!
# Helpers for `PartI:C05/4/3` (the mild pairing identity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartI.PairingPieces

open UnforcedLeray

/-- Joint continuity of `(a, x) ↦ e^{aD} x`. -/
theorem expD_joint_cont : Continuous fun p : ℝ × B0010.XG => B0123.expD p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨b, y⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : ℝ × B0010.XG => ‖p.2 - y‖) (𝓝 (b, y)) (𝓝 0) := by
    have hc : Continuous fun p : ℝ × B0010.XG => ‖p.2 - y‖ := by fun_prop
    simpa using hc.tendsto (b, y)
  have h2 : Tendsto (fun p : ℝ × B0010.XG => ‖B0123.expD p.1 y - B0123.expD b y‖) (𝓝 (b, y))
      (𝓝 0) := by
    have hc : Continuous fun p : ℝ × B0010.XG => B0123.expD p.1 y :=
      (Cons.G3b.continuous_expD_apply y).comp continuous_fst
    exact tendsto_iff_norm_sub_tendsto_zero.1 (hc.tendsto (b, y))
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) h3
  show ‖B0123.expD p.1 p.2 - B0123.expD b y‖ ≤
    ‖p.2 - y‖ + ‖B0123.expD p.1 y - B0123.expD b y‖
  have hsplit : B0123.expD p.1 p.2 - B0123.expD b y =
      B0123.expD p.1 (p.2 - y) + (B0123.expD p.1 y - B0123.expD b y) := by
    rw [map_sub]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact ((B0123.expD p.1).le_opNorm (p.2 - y)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (B0123.norm_expD_le p.1))

/-- Joint continuity of the clock `(r, τ) ↦ ∫_r^τ β`. -/
theorem clock_joint_cont {β : ℝ → ℝ} (hβm : Measurable β) (hβ01 : ∀ τ, 0 ≤ β τ ∧ β τ ≤ 1) :
    Continuous fun p : ℝ × ℝ => ∫ u in p.1..p.2, β u := by
  have hint : ∀ a b : ℝ, IntervalIntegrable β volume a b :=
    fun a b => ExpDPairingHelp.beta_intervalIntegrable hβm hβ01 a b
  have hP : Continuous fun y : ℝ => ∫ u in (0 : ℝ)..y, β u :=
    intervalIntegral.continuous_primitive (fun a b => hint a b) 0
  have heq : (fun p : ℝ × ℝ => ∫ u in p.1..p.2, β u) =
      fun p : ℝ × ℝ => (∫ u in (0 : ℝ)..p.2, β u) - ∫ u in (0 : ℝ)..p.1, β u := by
    funext p
    exact (intervalIntegral.integral_interval_sub_left (hint 0 p.2) (hint 0 p.1)).symm
  rw [heq]
  exact (hP.comp continuous_snd).sub (hP.comp continuous_fst)

/-- The operator `G_r` of the mild equation at clock value `b` (the integrand of the Duhamel
formula, with the clock value `b = β r` and the state `y = U(r,s)x`). -/
def pairOp (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ) (κ : ℂ)
    (Rf : B0010.XG →L[ℂ] B0010.XG) (b : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
    ((b : ℂ) * κ) • (1 : B0010.XG →L[ℂ] B0010.XG) + (b : ℂ) • Rf

theorem pairOp_clm_cont (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ) (κ : ℂ)
    (Rf : B0010.XG →L[ℂ] B0010.XG) :
    Continuous fun p : ℝ × B0010.XG => pairOp lam q l κ Rf p.1 p.2 := by
  have hT : Continuous fun b : ℝ => pairOp lam q l κ Rf b := by
    unfold pairOp
    fun_prop
  exact (hT.comp continuous_fst).clm_apply continuous_snd

/-- The double-integral integrand `β(τ) ⟨Dq†, e^{B(r,τ)D} z_r⟩`. -/
def pairG (qd : B0010.XG) (hqd : qd ∈ B0094.D.domain) (β : ℝ → ℝ)
    (z : ℝ → B0010.XG) (r τ : ℝ) : ℂ :=
  (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (B0123.expD (∫ u in r..τ, β u) (z r))

/-- `ℓ` applied to the operator `G_r`: `ℓ(G_r y) = -ℓ y - β ⟨Dq†, y⟩`. -/
theorem pairOp_ell {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ} (hI : IsSeedXG lam q l)
    (hq : q ∈ B0094.D.domain) (qd : B0010.XG) (hqd : qd ∈ B0094.D.domain) (b : ℝ)
    (y : B0010.XG) :
    l (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) b y) =
      -(l y) - (b : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) y := by
  have hL0 : l (Planar.L0 y) = lam * l y := mildEllL0 lam q l hI y
  simp only [pairOp, seedRf, seedKappa, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, innerSL_apply_apply,
    map_add, map_sub, map_neg, map_smul, smul_eq_mul, hL0, hI.ell_q, mul_one]
  ring

/-- Interchange of a second-slot interval integral with the inner product. -/
theorem inner_integral_right' (z : B0010.XG) {f : ℝ → B0010.XG} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    inner ℂ z (∫ r in a..b, f r) = ∫ r in a..b, inner ℂ z (f r) := by
  have := (innerSL ℂ z).intervalIntegral_comp_comm hf
  simpa only [innerSL_apply_apply] using this.symm

end UnforcedLeray.Short.PartI.PairingPieces
