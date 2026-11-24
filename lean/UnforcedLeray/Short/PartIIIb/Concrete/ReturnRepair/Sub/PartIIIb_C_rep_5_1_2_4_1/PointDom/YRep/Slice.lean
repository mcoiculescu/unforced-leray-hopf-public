import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.FinR
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.FullMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.X0Rep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.OutPrimRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.KerBounds

/-!
# The slice identity `wardX = ∫ fullKer` at a receiver off the old disk
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_tensorNorm_meas (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable fun e : ℝ × Space => IIIa.tensorNorm (oldPhys R c g e.1 e.2) := by
  unfold IIIa.tensorNorm
  refine Real.continuous_sqrt.measurable.comp ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (yr_meas_oldPhys_entry R c g hg i j).pow_const 2

lemma yr_xpart_int (ν μ R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) (hν : 0 < ν)
    (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (τ' : ℝ) (x : Space)
    (hsupp : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < ϱ x)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ' then ENNReal.ofReal (pdLam (τ' - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤) :
    Integrable fun e : ℝ × Space => if e.1 < τ' then
      xKer ν μ (τ' - e.1) (x - pdLam (τ' - e.1) • e.2) (oldPhys R c g e.1 e.2) else 0 := by
  obtain ⟨CK, hCK0, hK⟩ := pdKerBounds
  have hS : MeasurableSet {e : ℝ × Space | e.1 < τ'} :=
    measurableSet_lt measurable_fst measurable_const
  have hm := yr_xKer_meas ν μ {e : ℝ × Space | e.1 < τ'} hS (fun e => τ' - e.1)
    (measurable_const.sub measurable_fst) (fun e => x - pdLam (τ' - e.1) • e.2)
    (by
      have hlam : Measurable fun e : ℝ × Space => pdLam (τ' - e.1) := by unfold pdLam; fun_prop
      exact measurable_const.sub (hlam.smul measurable_snd))
    (fun e => oldPhys R c g e.1 e.2) (fun i j => yr_meas_oldPhys_entry R c g hg i j)
    (fun e he hW => yr_zero_of_eq (sub_pos.2 he) (sub_eq_zero.mp hW) _ (hsupp _ _))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∀ e : ℝ × Space, ‖(if e.1 < τ' then
      xKer ν μ (τ' - e.1) (x - pdLam (τ' - e.1) • e.2) (oldPhys R c g e.1 e.2) else 0 : Space)‖ₑ ≤
      ENNReal.ofReal CK * ((if e.1 < τ' then ENNReal.ofReal (pdLam (τ' - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
    intro e
    by_cases h : e.1 < τ'
    · rw [if_pos h, if_pos h]
      by_cases hM : oldPhys R c g e.1 e.2 = 0
      · rw [hM, yr_xKer_zero]; simp
      · have hw : x - pdLam (τ' - e.1) • e.2 ≠ 0 := fun hw =>
          hM (yr_zero_of_eq (sub_pos.2 h) (sub_eq_zero.mp hw) _ (fun _ => hsupp _ _ hM))
        have hb := ((hK ν μ (τ' - e.1) hν hμ0 hμ1 (sub_pos.2 h) (oldPhys R c g e.1 e.2)).2.2
          _ hw).1
        rw [← ofReal_norm_eq_enorm]
        unfold IIIa.srcNorm
        have hp : 0 ≤ pdLam (τ' - e.1) ^ (2 * μ + 3) * (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹ :=
          mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) (by positivity)
        rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hCK0]
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ ≤ _ := hb
          _ = _ := by ring
    · rw [if_neg h]; simp
  calc _ ≤ ∫⁻ e : ℝ × Space, ENNReal.ofReal CK * ((if e.1 < τ' then
        ENNReal.ofReal (pdLam (τ' - e.1) ^ (2 * μ + 3) *
        (‖x - pdLam (τ' - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm (oldPhys R c g) e.1 e.2) := lintegral_mono hle
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

lemma yr_spart_int (ν μ R c τ r y3 : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hg : Measurable g)
    (hr : 0 < r) (hsupp : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < r)
    (hfin : ∫⁻ ρ in Ioi r, ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
        (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤) :
    Integrable fun e : ℝ × Space => if e.1 < τ then
      sKer ν μ (τ - e.1) r y3 e.2 (oldPhys R c g e.1 e.2) else 0 := by
  obtain ⟨C, hC0, hC⟩ := gm_bound
  have hF_int := pdOR_F_int ν μ R c τ r y3 g hν hg hr hsupp hfin ⟨C, hC0, hC⟩
  have hsP : ∀ ρ : ℝ, r < ρ → ∀ σ z, oldPhys R c g σ z ≠ 0 →
      ϱ z < ϱ (!₂[ρ, 0, y3] : Space) := by
    intro ρ hρr σ z hz
    rw [pdOR_varrho (hr.trans hρr).le]
    exact lt_trans (hsupp σ z hz) hρr
  have hC' : ∀ e : ℝ × Space,
      ∫ ρ in Ioi r, ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e =
        -(if e.1 < τ then sKer ν μ (τ - e.1) r y3 e.2 (oldPhys R c g e.1 e.2) else 0) := by
    intro e
    by_cases h : e.1 < τ
    · rw [if_pos h, sKer, neg_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      have hx := xKerGm_eq ν μ τ (!₂[ρ, 0, y3] : Space) (oldPhys R c g)
        (hsP ρ (Set.mem_Ioi.mp hρ)) e
      rw [if_pos h] at hx
      show ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e =
        ρ * xKer ν μ (τ - e.1) ((!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2)
          (oldPhys R c g e.1 e.2) 2
      rw [hx]
    · simp [xKerGm, h]
  have := hF_int.integral_prod_right.neg
  refine this.congr (Filter.Eventually.of_forall fun e => ?_)
  show -(∫ ρ in Ioi r, ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e) = _
  rw [hC', neg_neg]

lemma yr_slice (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hR : 0 < R)
    (hc : 0 < c) (hμ0 : -(1 / 4) < μ) (hμ1 : μ ≤ 1) (hg : Measurable g)
    {ρ₀ r₁ Y τ ε : ℝ} (hρ0 : 0 ≤ ρ₀) (hρ : ρ₀ < r₁)
    (hsupp0 : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z ≤ ρ₀) (hε1 : ε ≤ 1)
    (hfin : ∫⁻ e : ℝ × Space, (if e.1 < τ + ε then ENNReal.ofReal (srcWeight μ (τ - e.1) e.2)
      else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤)
    (τ' : ℝ) (hτ' : |τ' - τ| < ε) (x : Space) (hx : r₁ < ϱ x) (hxY : ‖x‖ < Y) :
    wardX ν μ R c χy g τ' x = ∫ e : ℝ × Space, if e.1 < τ' then
      fullKer ν μ R χy (τ' - e.1) x e.2 (oldPhys R c g e.1 e.2) else 0 := by
  have hsupp : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < ϱ x :=
    fun σ z h => lt_of_le_of_lt (hsupp0 σ z h) (hρ.trans hx)
  have hxpos : 0 < ϱ x := by linarith [hρ0]
  have h2 := yr_N2 μ R c g hμ0 hμ1 hρ hsupp0 hε1 hfin τ' hτ' x hx hxY
  have hy3 : |x 2| < Y := by
    refine lt_of_le_of_lt ?_ hxY
    have := PiLp.norm_apply_le x 2
    simpa [Real.norm_eq_abs] using this
  have h3 := yr_N3 μ R c g hg hμ0 hμ1 hρ0 hρ hsupp0 hε1 hfin τ' hτ' (x 2) (ϱ x) hy3 hx.le
  have hX0 := pdX0Rep ν μ R c g hν hR hc hμ0 hμ1 hg τ' x hsupp h2
  have hO := pdOutPrimRep ν μ R c g hν hR hc hμ0 hμ1 hg τ' (ϱ x) (x 2) hxpos hsupp h3
  have hAint := yr_xpart_int ν μ R c g hg hν hμ0 hμ1 τ' x hsupp h2
  have hSint := yr_spart_int ν μ R c τ' (ϱ x) (x 2) g hν hg hxpos hsupp h3
  set A : ℝ × Space → Space := fun e => if e.1 < τ' then
      xKer ν μ (τ' - e.1) (x - pdLam (τ' - e.1) • e.2) (oldPhys R c g e.1 e.2) else 0 with hA
  set S : ℝ × Space → ℝ := fun e => if e.1 < τ' then
      sKer ν μ (τ' - e.1) (ϱ x) (x 2) e.2 (oldPhys R c g e.1 e.2) else 0 with hS
  set cf : ℝ := deriv χy (ν * age R x) * (-2 * ν * R ^ 2 / ϱ x ^ 3) / ϱ x with hcf
  have hFeq : (fun e : ℝ × Space => if e.1 < τ' then
      fullKer ν μ R χy (τ' - e.1) x e.2 (oldPhys R c g e.1 e.2) else 0) =
      fun e => χy (ν * age R x) • A e + (cf * S e) • (coordinateVector 2 : Space) := by
    funext e
    by_cases h : e.1 < τ'
    · simp [hA, hS, hcf, h, fullKer]
    · simp [hA, hS, h]
  rw [hFeq, integral_add (f := fun e => χy (ν * age R x) • A e) (g := fun e => (cf * S e) • (coordinateVector 2 : Space)) (hAint.smul (χy (ν * age R x))) ((hSint.const_mul cf).smul_const (coordinateVector 2 : Space)), integral_smul,
    integral_smul_const, integral_const_mul]
  unfold wardX wardStreamCut
  rw [hX0, hO]


end UnforcedLeray.Short.PartIIIb.Concrete

end
