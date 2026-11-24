import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_ax
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Fderiv
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Lap
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphStateSymmetry
import UnforcedLeray.Short.PartIIb.Compose

/-!
# The exact background and the lifted pressure are axisymmetric without swirl (`pres/3/2/2`)

Source `the November 2 reference manuscript`:
121-124, 2031, 2522-2523 (reality, no-swirl symmetry and periodicity of the background), 1217
(`p_lift = s p_cyl` depends on `y` only through `(ϱ, y₃)`), 4139-4141 (`D₀U + U·∇U + ∇p = 0`).

* `pf2b_axiU`: for large `n`, `U(τ) = V(τ) + r_b(τ)` is pointwise axisymmetric without swirl
  (`IsBallSplit`: `V = U_raw + Σ α_i inlet_i`, `r_b = corr z`; `raw`, `inlet` are ring lifts,
  `corr` by `Params.corr_isAxisymmetricNoSwirl`, `period ≤ 1` from the regime);
* `pf2b_liftP_invariant`: `p_lift ∘ g = p_lift` for every isometry `g` fixing `e₃`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem pf2b_axi_congr {f f' : SpatialField} (hf : IsAxisymmetricNoSwirl f)
    (h : ∀ y : Space, y ∉ axis → f y = f' y) : IsAxisymmetricNoSwirl f' := by
  refine UnforcedLeray.Cons.C03.isAxisymmetricNoSwirl_congr_ae' hf ?_
  filter_upwards [ae_not_mem_axis] with y hy
  exact h y hy

theorem pf2b_period_tendsto (dm : ℝ) (hdm : 0 < dm) :
    Tendsto (fun ν : ℝ => |(2 : ℝ)| * (ν ^ 2)⁻¹ * Real.exp (-dm / ν)) (𝓝[>] 0) (𝓝 0) := by
  have hx : Tendsto (fun ν : ℝ => ν⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hG : Tendsto (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-dm * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hdm
  have h := (hG.comp hx).const_mul |(2 : ℝ)|
  rw [mul_zero] at h
  refine h.congr fun ν => ?_
  simp only [Function.comp]
  rw [Real.rpow_two, inv_pow, div_eq_mul_inv (-dm) ν]
  ring

/-- **Large `n`: `P = 2εc ≤ 1`** (regime window `d ≥ d₋ > 0`). -/
theorem pf2b_period_le_one (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, ((D.level n).params D.Pl).period ≤ 1 := by
  have h1 : ∀ᶠ n : ℕ in atTop, |(2 : ℝ)| * (retNu D.Pl D.σ₀ n ^ 2)⁻¹ *
      Real.exp (-dm / retNu D.Pl D.σ₀ n) < 1 := by
    have hT : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨retNu_tendsto D.σ₀ hst.omega_ne,
        Eventually.of_forall fun n => retNu_pos D.Pl D.σ₀ n⟩
    exact ((pf2b_period_tendsto dm hst.dm_pos).comp hT).eventually (gt_mem_nhds one_pos)
  filter_upwards [hst.actual, h1] with n hn hsmall
  exact UnforcedLeray.Short.IIb.period_le_one_of hn.regime hsmall

theorem pf2b_axi_bgField (p : UnforcedLeray.Cons.C03.Concrete.Params) (hP1 : p.period ≤ 1)
    (z : p.Z) (τ : ℝ) :
    IsAxisymmetricNoSwirl (p.raw τ + ∑ i : Fin 2, p.coord z i • p.inlet i τ + p.corr z τ) := by
  have hraw : IsAxisymmetricNoSwirl (p.raw τ) :=
    pf2b_axi_congr (isAxisymmetricNoSwirl_Nv _ _ τ)
      (fun y hy => (p.raw_eq_off_axis τ y hy).symm)
  have hin : ∀ i : Fin 2, IsAxisymmetricNoSwirl (p.coord z i • p.inlet i τ) := fun i =>
    UnforcedLeray.Cons.C03.isAxisymmetricNoSwirl_const_smul
      (isAxisymmetricNoSwirl_Nv p.R (p.inletProfile i) τ) _
  have hcorr : IsAxisymmetricNoSwirl (p.corr z τ) :=
    UnforcedLeray.Cons.C03.Concrete.Params.corr_isAxisymmetricNoSwirl p hP1 z τ
  refine UnforcedLeray.Cons.C03.isAxisymmetricNoSwirl_add' ?_ hcorr
  refine UnforcedLeray.Cons.C03.isAxisymmetricNoSwirl_add' hraw ?_
  rw [Fin.sum_univ_two]
  exact UnforcedLeray.Cons.C03.isAxisymmetricNoSwirl_add' (hin 0) (hin 1)

/-- **`U(τ)` is axisymmetric without swirl, pointwise** (source 121-124, 2031, 2522-2523). -/
theorem pf2b_axiU (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ) := by
  filter_upwards [hst.actual, pf2b_period_le_one D hst] with n hn hP1 τ
  obtain ⟨z, -, hV, hrb, -⟩ := hn.ball
  have hsum := pf2b_axi_bgField ((D.level n).params D.Pl) hP1 z τ
  have hU : (D.level n).U τ = ((D.level n).params D.Pl).raw τ +
      ∑ i : Fin 2, ((D.level n).params D.Pl).coord z i • ((D.level n).params D.Pl).inlet i τ +
      ((D.level n).params D.Pl).corr z τ := by
    funext y
    show D.V n τ y + D.rb n τ y = _
    rw [hV τ y, hrb]
    simp [Pi.add_apply]
  have hc : Continuous ((D.level n).U τ) :=
    hn.profile.smoothU.continuous.comp (Continuous.prodMk_right (Y := Space) τ)
  rw [hU] at hc ⊢
  exact axiNoSwirlPt_of_ae hc hsum

end UnforcedLeray.Short.PartIIIb.Concrete
