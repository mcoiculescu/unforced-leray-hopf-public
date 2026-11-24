import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Cons.L2.BackgroundConcrete.Spaces
import UnforcedLeray.Units.B0412

/-!
# `FreeGraphHessian`: the Cartesian Hessian on the body graph, and `GEHess` from it

Task `PartIII-b:C/ward/12/3/1/2/2/org`.  Source of record
`the November 2 reference manuscript`,
lines 1356-1366 (`bg:common-body-graph`), 1377-1424 (`free:heat-estimate`, `‖νD²u‖_r`, no
viscosity loss), 1426-1442 (window reduction; "the same reasoning applies to any distributional
`Y_r` solution"), used at 2531 (`D²w ∈ Y_p`).

* `FreeGraphHessian`: for `1 < r < 3`, `a_r = Re μ + γ_r > 0`, `ν > 0`, `0 < P ≤ 1`, every
  `w ∈ D_r` with gradient `g` (`HasGrad`) has `∂_k g_j = h_{jk} ∈ Y_r` and
  `ν ∑_{j,k} ‖h_{jk}‖ ≤ C_r [1 + (1+|μ|)/a_r] ‖(μ+L)w‖` (the Hessian companion of
  `bg:body-graph`, `PartIIa.CommonBodyGraphBound`).
* `freeGraphHessian_of`: from `BodyHessianBound` (`Hess/Defs.lean`) with the resolvent bound
  `‖w‖ ≤ ‖(μ+L)w‖/a_r` (`bodyResolvent_exists`, `bodyResolvent_solves`, `bodyOp_uniqueness`);
  `h_{jk} = ν⁻¹ a_{jk}` where `ν∂_j∂_kw = a_{jk}`, since `⟪-∂_kΦ, g_j⟫ = ⟪∂_j∂_kΦ, w⟫`.
* `gEHess_of_freeGraphHessian`: `w = wOf z ∈ X_{q₀} ⊆ D_{q₀}` (`cw_mem_X`, `X_le_D`), `μ = 0`
  (`γ_{q₀} > 0`), `ν₀ = dm³/12` (`bgCorr_period_le_one`), and the `g` of `GEData` is the
  gradient.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **The Cartesian Hessian on the body graph** (source 1356-1366, 1377-1442, used at 2531):
for `1 < r < 3`, `Re μ + γ_r > 0`, `ν > 0`, `0 < P ≤ 1`, every `w ∈ D_r` with distributional
gradient `g` has `∂_k g_j = h_{jk}` in `Y_r` and
`ν ∑_{j,k} ‖h_{jk}‖_{Y_r} ≤ C_r [1 + (1+|μ|)/a_r] ‖(μ+L)w‖_{Y_r}`, `C_r` independent of
`P, ν, μ`. -/
def FreeGraphHessian : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ,
      0 < μ.re + UnforcedLeray.Short.PartIIa.gammaR r →
      ∀ (w : UnforcedLeray.B0411.D P ν r) (g : Fin 3 → Yq P r),
        UnforcedLeray.Short.PartIIa.HasGrad (w : Yq P r) g →
        ∃ h : Fin 3 → Fin 3 → Yq P r, (∀ j k, HasPhaseOp (fun Φ => -dy k Φ) (g j) (h j k)) ∧
          ν * ∑ j, ∑ k, ‖h j k‖ ≤
            C * (1 + (1 + ‖μ‖) / (μ.re + UnforcedLeray.Short.PartIIa.gammaR r)) *
              ‖UnforcedLeray.Short.PartIIa.bodyOp P ν r μ w‖

/-- `-∂_j(-∂_kΦ) = ∂_j∂_kΦ`. -/
theorem neg_dy_neg_dy (j k : Fin 3) (Φ : ℝ × Space → CVec3) :
    -dy j (-dy k Φ) = dy j (dy k Φ) := by
  rw [dy_neg, neg_neg]

/-- From `ν∂_j∂_kw = a` and `∂_jw = g_j`: `∂_k g_j = ν⁻¹ a`. -/
theorem hasPhaseOp_grad_of_hess {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] {ν : ℝ}
    (hν : 0 < ν) {w gj a : Yq P r} {j k : Fin 3}
    (hg : HasPhaseOp (fun Φ => -dy j Φ) w gj) (ha : HasPhaseOp (nuHessT ν j k) w a) :
    HasPhaseOp (fun Φ => -dy k Φ) gj (((ν : ℂ)⁻¹) • a) := by
  intro Φ hΦ
  have hk : IsPhaseTest P (-dy k Φ) := (hΦ.dy k).neg
  have hjk : IsPhaseTest P (dy j (dy k Φ)) := (hΦ.dy k).dy j
  have e1 : phasePair P r (-dy j (-dy k Φ)) w = phasePair P r (-dy k Φ) gj := hg (-dy k Φ) hk
  rw [neg_dy_neg_dy] at e1
  have e2 := ha Φ hΦ
  rw [nuHessT, phasePair_real_smul hjk] at e2
  show phasePair P r (-dy k Φ) gj = phasePair P r Φ (((ν : ℂ)⁻¹) • a)
  rw [← e1, map_smul, smul_eq_mul, ← e2, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hν.ne'), one_mul]

/-- `FreeGraphHessian` from the quantitative body Hessian bound. -/
theorem freeGraphHessian_of (hb : BodyHessianBound) : FreeGraphHessian := by
  intro r _ h1 h3
  obtain ⟨C, hC0, hC⟩ := hb r h1 (ne_top_of_lt h3)
  refine ⟨9 * C, by positivity, ?_⟩
  intro P _ hP ν hν μ hμ w g hg
  set a : ℝ := μ.re + UnforcedLeray.Short.PartIIa.gammaR r with ha
  set f : Yq P r := UnforcedLeray.Short.PartIIa.bodyOp P ν r μ w with hf
  have hw : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w : Yq P r) f :=
    UnforcedLeray.Short.PartIIa.hasPhaseOp_body_of_D w
  -- `‖w‖ ≤ ‖f‖ / a` from the resolvent and uniqueness (as in `commonBodyGraphBound_of`)
  obtain ⟨Rm, hRm, hRf⟩ := UnforcedLeray.Short.PartIIa.bodyResolvent_exists r h1 h3 P ν hν μ hμ
  have hsol := UnforcedLeray.Short.PartIIa.bodyResolvent_solves r h1 h3 P ν hν μ hμ Rm hRf f
  have hz : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) ((w : Yq P r) - Rm f) 0 := by
    intro Φ hΦ
    rw [map_sub, hw Φ hΦ, hsol Φ hΦ, sub_self, map_zero]
  have hwR : (w : Yq P r) = Rm f :=
    sub_eq_zero.1 (UnforcedLeray.Short.PartIIa.bodyOp_uniqueness r h1 h3 P ν hν μ hμ _ hz)
  have hwn : ‖(w : Yq P r)‖ ≤ a⁻¹ * ‖f‖ := by
    rw [hwR]; exact (Rm.le_opNorm f).trans (mul_le_mul_of_nonneg_right hRm (norm_nonneg _))
  have ha0 : 0 < a := hμ
  have hS : ‖f‖ + (1 + ‖μ‖) * ‖(w : Yq P r)‖ ≤ (1 + (1 + ‖μ‖) / a) * ‖f‖ := by
    have h1' : (1 + ‖μ‖) * ‖(w : Yq P r)‖ ≤ (1 + ‖μ‖) * (a⁻¹ * ‖f‖) :=
      mul_le_mul_of_nonneg_left hwn (by positivity)
    have e : (1 + ‖μ‖) * (a⁻¹ * ‖f‖) = (1 + ‖μ‖) / a * ‖f‖ := by
      rw [div_eq_mul_inv]; ring
    rw [add_mul, one_mul]
    linarith
  choose A hA hAn using fun j k => hC P hP ν hν μ f (w : Yq P r) hw j k
  refine ⟨fun j k => ((ν : ℂ)⁻¹) • A j k, fun j k => hasPhaseOp_grad_of_hess hν (hg j) (hA j k),
    ?_⟩
  have hterm : ∀ j k, ν * ‖((ν : ℂ)⁻¹) • A j k‖ ≤ C * ((1 + (1 + ‖μ‖) / a) * ‖f‖) := by
    intro j k
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν, ← mul_assoc,
      mul_inv_cancel₀ hν.ne', one_mul]
    exact (hAn j k).trans (mul_le_mul_of_nonneg_left hS hC0)
  calc ν * ∑ j, ∑ k, ‖((ν : ℂ)⁻¹) • A j k‖
      = ∑ j, ∑ k, ν * ‖((ν : ℂ)⁻¹) • A j k‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
    _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, C * ((1 + (1 + ‖μ‖) / a) * ‖f‖) := by
        exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
    _ = 9 * C * (1 + (1 + ‖μ‖) / a) * ‖f‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **`GEHess` from `FreeGraphHessian`** (source 2531): `w = wOf z ∈ X_{q₀} ⊆ D_{q₀}`, `μ = 0`,
`ν₀ = dm³/12` (so `P ≤ 1`), and `g` is the distributional gradient of `w` (`GEData`). -/
theorem gEHess_of_freeGraphHessian (h : FreeGraphHessian) : GEHess := by
  intro lam q hq dm dp hdm
  refine ⟨dm ^ 3 / 12, by positivity, ?_⟩
  intro p d hreg hν hmode z g hd
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hν
  have hw : p.wOf z ∈ UnforcedLeray.B0412.X p.period p.ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.Cons.C03.Concrete.cw_mem_X z
  have hD : p.wOf z ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E :=
    UnforcedLeray.B0412.X_le_D hw
  obtain ⟨C, -, hB⟩ := h UnforcedLeray.B0412.q0E q0E_gt_one q0E_lt_three
  obtain ⟨hh, hhd, -⟩ := hB p.period hP1 p.ν p.ν_pos 0 (by simpa using gammaR_q0E_pos)
    ⟨p.wOf z, hD⟩ g hd.2
  exact ⟨hh, hhd⟩

end UnforcedLeray.Short.PartIIIb.Concrete
