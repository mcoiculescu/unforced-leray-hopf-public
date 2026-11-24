import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.FarDomChart
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `farOutPointwise` (source 3631-3647 with `p = 22/19`, `b = 22/3`, `j = 0`; 3611-3621; 3905-3912).

Apply `IIIa.sepYoungPointwise_of` to the masked source of `sepWfar`, a separated source with
`rOut = R e^{-δ/2}/√s`, `rIn = R/√s`, `P = 2c/R`; the receiver power is `D^{-79/22}`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem farOutPointwise : FarOutPointwise := by
  intro σ₁ σ₂ hσ
  have hKc : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc σ₁ σ₂) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hKre : ∀ μ ∈ (fun x : ℝ => (x : ℂ)) '' Icc σ₁ σ₂, -(1 / 4) < μ.re := by
    rintro μ ⟨x, hx, rfl⟩
    rw [Complex.ofReal_re]
    linarith [hx.1]
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ (fun x : ℝ => (x : ℂ)) '' Icc σ₁ σ₂,
      δ ≤ 2 * μ.re + 3 / (22 / 19 : ℝ) := by
    refine ⟨2 * σ₁ + 57 / 22, by linarith, ?_⟩
    rintro μ ⟨x, hx, rfl⟩
    rw [Complex.ofReal_re]
    have hx1 := hx.1
    norm_num
    linarith
  obtain ⟨C, hC, hY⟩ := UnforcedLeray.Short.IIIa.sepYoungPointwise_of
    UnforcedLeray.Short.IIIa.sepWDominated UnforcedLeray.Short.IIIa.sepKernelBounds
    UnforcedLeray.Short.IIIa.sepDomPointwise _ hKc hKre 0 (22 / 19) (22 / 3)
    (by norm_num) (by norm_num) (by norm_num) hδ
  refine ⟨C, hC, ?_⟩
  intro ν μ R c δ hν hμ hR hc hδ0 f hf p hp0
  have hfm : Measurable f := hf
  have hsqrt_pos : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp0
  have hsqrtS : 0 < Real.sqrt p.1 := hsqrt_pos
  have he1 : Real.exp (-(δ / 2)) < 1 := by
    have := Real.exp_lt_exp.mpr (show -(δ / 2) < 0 by linarith)
    simpa using this
  have he0 : 0 < Real.exp (-(δ / 2)) := Real.exp_pos _
  have hrOut0 : 0 ≤ R * Real.exp (-(δ / 2)) / Real.sqrt p.1 := by positivity
  have hrlt : R * Real.exp (-(δ / 2)) / Real.sqrt p.1 < R / Real.sqrt p.1 := by
    apply div_lt_div_of_pos_right _ hsqrt_pos
    nlinarith
  have hrIn_rOut : R / Real.sqrt p.1 - R * Real.exp (-(δ / 2)) / Real.sqrt p.1 =
      (1 - Real.exp (-(δ / 2))) * R / Real.sqrt p.1 := by ring
  have hy0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := by
    simp [NearInst.chartY]
  have hy1 : (NearInst.chartY R p) 1 = 0 := by
    simp [NearInst.chartY]
  have hyle : R / Real.sqrt p.1 ≤
      Real.sqrt ((NearInst.chartY R p) 0 ^ 2 + (NearInst.chartY R p) 1 ^ 2) := by
    rw [hy0, hy1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    rw [Real.sqrt_sq (by positivity)]
  have hsep := fd_isSepSource R c δ p.1 hR hc f hfm hp0
  have hexp : (-4 - ((0 : ℕ) : ℝ) + 3 / (22 / 3 : ℝ)) = -(79 / 22 : ℝ) := by norm_num
  have hmemK : (μ : ℂ) ∈ (fun x : ℝ => (x : ℂ)) '' Icc σ₁ σ₂ := ⟨μ, hμ, rfl⟩
  have hY' := hY ν hν (μ : ℂ) hmemK (R * Real.exp (-(δ / 2)) / Real.sqrt p.1) (R / Real.sqrt p.1)
    (2 * c / R) hrOut0 hrlt (by positivity) _ hsep (NearInst.chartY R p) hyle
  rw [hexp, hrIn_rOut] at hY'
  have hWeq : ∀ τ : ℝ, ‖NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c f)
        (NearInst.chartY R p) τ‖ₑ = UnforcedLeray.Short.IIIa.wDerivNorm ν (μ : ℂ)
          (fun τ' z => if Real.exp δ * p.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
            NearInst.cartLift R c f τ' z else 0) 0 τ (NearInst.chartY R p) := by
    intro τ
    unfold UnforcedLeray.Short.IIIa.wDerivNorm
    rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]
    rfl
  have hfar : farPt R c ν μ δ f p = UnforcedLeray.Short.IIIa.ltauAt (2 * c / R)
      (fun τ => UnforcedLeray.Short.IIIa.wDerivNorm ν (μ : ℂ)
          (fun τ' z => if Real.exp δ * p.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
            NearInst.cartLift R c f τ' z else 0) 0 τ (NearInst.chartY R p)) := by
    unfold farPt
    congr 1
    funext τ
    exact hWeq τ
  rw [hfar]
  have hmask := UnforcedLeray.Short.IIIa.ltauLq_mono (2 * c / R) (22 / 19) (by norm_num)
    (fun τ z => fd_srcNorm_mask_le R c p.1 δ f τ z)
  exact le_trans hY' (mul_le_mul_of_nonneg_left hmask zero_le)

end UnforcedLeray.Short.PartIIIb.Concrete
