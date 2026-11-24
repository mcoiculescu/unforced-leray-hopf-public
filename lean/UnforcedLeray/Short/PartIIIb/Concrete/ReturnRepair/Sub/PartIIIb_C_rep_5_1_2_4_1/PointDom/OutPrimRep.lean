import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.X0Rep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Sub.PartIIIb_C_rep_5_1_2_4_1_2_7_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `pdOutPrimRep` (`PartIII-b:C/rep/5/1/2/4/1/2/8`)

Source `the November 2 reference manuscript` 4178-4186 (the outward primitive
converges; `outPrim` of `wardX0` in phase-lag form).

Proof outline.  `outPrim Z τ r y3 = -∫_{ρ>r} ρ (Z τ (ρ,0,y3)) 2`.  For `ρ > r` the point
`P = !₂[ρ,0,y3]` has `ϱ P = ρ > r > ϱ z` on the old support, so `PDX0Rep` applies at `P` for
almost every `ρ` (finiteness of the `ρ`-integrated majorant gives the pointwise finiteness a.e.).
Taking component `2` commutes with the Bochner integral (`ContinuousLinearMap.integral_comp_comm`),
the `ρ`-integral and the `(e)`-integral are swapped by `integral_integral_swap`, justified by the
joint integrability bound `xKer_ite_enorm_le`, and the inner `ρ`-integral is `-sKer`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The receiver `!₂[ρ, 0, y₃]` depends measurably on `ρ`. -/
lemma pdOR_P_meas (y3 : ℝ) : Measurable (fun ρ : ℝ => (!₂[ρ, 0, y3] : Space)) := by
  exact measurable_toLp_three.comp (by fun_prop)

/-- `ϱ !₂[ρ, 0, y₃] = ρ` for `ρ ≥ 0`. -/
lemma pdOR_varrho {ρ : ℝ} (hρ : 0 ≤ ρ) (y3 : ℝ) : ϱ (!₂[ρ, 0, y3] : Space) = ρ := by
  unfold ϱ
  simp [Real.sqrt_sq hρ]

/-- Joint measurability of the phase-lag `xKer` component, with receiver `!₂[ρ, 0, y₃]`. -/
lemma pdOR_xKerGm_joint (ν μ τ y3 : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hTm : ∀ i j : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 i j) (i : Fin 3) :
    Measurable (fun p : ℝ × (ℝ × Space) => xKerGm ν μ T τ (!₂[p.1, 0, y3] : Space) i p.2) := by
  have hlam : Measurable fun p : ℝ × (ℝ × Space) => pdLam (τ - p.2.1) := by
    unfold pdLam; fun_prop
  have hτ1 : Measurable fun p : ℝ × (ℝ × Space) => ν * (1 - pdLam (τ - p.2.1) ^ 2) :=
    measurable_const.mul (measurable_const.sub (hlam.pow_const 2))
  have hPm : Measurable fun p : ℝ × (ℝ × Space) => (!₂[p.1, 0, y3] : Space) :=
    (pdOR_P_meas y3).comp measurable_fst
  have hx1 : Measurable fun p : ℝ × (ℝ × Space) =>
      (!₂[p.1, 0, y3] : Space) - pdLam (τ - p.2.1) • p.2.2 :=
    hPm.sub (hlam.smul (measurable_snd.comp measurable_snd))
  unfold xKerGm
  refine Measurable.ite (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
    ?_ measurable_const
  refine Measurable.mul (Measurable.neg ((hlam.pow_const _).sub (hlam.pow_const _))) ?_
  refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
  exact ((T8_1.measurable_Gm k i j).comp (hτ1.prodMk hx1)).mul
    ((hTm j k).comp measurable_snd)

/-- The measurable integrand of the hypothesis of `PDOutPrimRep`, jointly in `(ρ, e)`. -/
lemma pdOR_F0_meas (μ τ R c y3 : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable (fun p : ℝ × (ℝ × Space) =>
      (if p.2.1 < τ then ENNReal.ofReal (p.1 * pdLam (τ - p.2.1) ^ (2 * μ + 3) *
          (‖(!₂[p.1, 0, y3] : Space) - pdLam (τ - p.2.1) • p.2.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm (oldPhys R c g) p.2.1 p.2.2) := by
  have hlam : Measurable fun p : ℝ × (ℝ × Space) => pdLam (τ - p.2.1) := by
    unfold pdLam; fun_prop
  have hPm : Measurable fun p : ℝ × (ℝ × Space) => (!₂[p.1, 0, y3] : Space) :=
    (pdOR_P_meas y3).comp measurable_fst
  have hS : Measurable (fun e : ℝ × Space => IIIa.srcNorm (oldPhys R c g) e.1 e.2) := by
    unfold IIIa.srcNorm IIIa.tensorNorm
    refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    exact (T8_1.measurable_oldPhys_entry R c g hg i j).pow_const 2
  refine Measurable.mul ?_ (hS.comp measurable_snd)
  refine Measurable.ite (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const) ?_
    measurable_const
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.mul (Measurable.mul measurable_fst (hlam.pow_const _)) ?_
  exact ((hPm.sub (hlam.smul (measurable_snd.comp measurable_snd))).norm.pow_const 4).inv

/-- Factoring `ρ` out of the majorant integrand (`ρ ≥ 0`). -/
lemma pdOR_key (μ τ ρ y3 : ℝ) (hρ : 0 ≤ ρ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (e : ℝ × Space) :
    (if e.1 < τ then ENNReal.ofReal (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) *
        (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm T e.1 e.2 =
    ENNReal.ofReal ρ * ((if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
        (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
      IIIa.srcNorm T e.1 e.2) := by
  by_cases h : e.1 < τ
  · rw [if_pos h, if_pos h, mul_assoc ρ, ENNReal.ofReal_mul hρ]
    ring
  · rw [if_neg h, if_neg h]
    simp

/-- Pointwise majorant of the `ρ`-weighted component of the phase-lag `xKer` integrand. -/
lemma pdOR_enorm_le (ν μ τ y3 C : ℝ) (hν : 0 < ν) (hC0 : 0 ≤ C)
    (hC : ∀ t, 0 < t → ∀ w : Space, w ≠ 0 → ∀ i j k : Fin 3,
      |T8_1.Gm k i j (t, w)| ≤ C * (‖w‖ ^ 4)⁻¹)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hsupp : ∀ σ z, T σ z ≠ 0 → ϱ z < ρ) (e : ℝ × Space) :
    ‖ρ * xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) 2 e‖ₑ ≤ ENNReal.ofReal (27 * C) *
      ((if e.1 < τ then ENNReal.ofReal (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) *
          (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
        IIIa.srcNorm T e.1 e.2) := by
  have hϱ : ϱ (!₂[ρ, 0, y3] : Space) = ρ := pdOR_varrho hρ.le y3
  have hsupp' : ∀ σ z, T σ z ≠ 0 → ϱ z < ϱ (!₂[ρ, 0, y3] : Space) :=
    fun σ z hz => by rw [hϱ]; exact hsupp σ z hz
  have hv := xKer_ite_enorm_le hC0 hC ν μ τ T (!₂[ρ, 0, y3] : Space) hν hsupp' e
  have hcoord : ‖xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) 2 e‖ₑ ≤
      ‖(if e.1 < τ then xKer ν μ (τ - e.1) ((!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2)
        (T e.1 e.2) else 0)‖ₑ := by
    rw [xKerGm_eq ν μ τ _ T hsupp' e, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) i e) : Space) 2)
  have h1 : ‖ρ * xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) 2 e‖ₑ =
      ENNReal.ofReal ρ * ‖xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) 2 e‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, norm_mul, Real.norm_of_nonneg hρ.le,
      ENNReal.ofReal_mul hρ.le]
  calc ‖ρ * xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) 2 e‖ₑ
      = ENNReal.ofReal ρ * ‖xKerGm ν μ T τ (!₂[ρ, 0, y3] : Space) 2 e‖ₑ := h1
    _ ≤ ENNReal.ofReal ρ * ‖(if e.1 < τ then xKer ν μ (τ - e.1)
          ((!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2) (T e.1 e.2) else 0)‖ₑ :=
        by gcongr
    _ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal (27 * C) *
          ((if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
          (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
            IIIa.srcNorm T e.1 e.2)) := by gcongr
    _ = ENNReal.ofReal (27 * C) * (ENNReal.ofReal ρ * ((if e.1 < τ then
          ENNReal.ofReal (pdLam (τ - e.1) ^ (2 * μ + 3) *
            (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
            IIIa.srcNorm T e.1 e.2)) := by ring
    _ = ENNReal.ofReal (27 * C) * ((if e.1 < τ then
          ENNReal.ofReal (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) *
            (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹) else 0) *
            IIIa.srcNorm T e.1 e.2) := by
        rw [pdOR_key μ τ ρ y3 hρ.le T e]

/-- Joint integrability of the `ρ`-weighted phase-lag integrand over `(r, ∞) × (ℝ × Space)`. -/
lemma pdOR_F_int (ν μ R c τ r y3 : ℝ) (g : Chart → Ten3) (hν : 0 < ν) (hg : Measurable g)
    (hr : 0 < r) (hsupp : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < r)
    (hfin : ∫⁻ ρ in Ioi r, ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
        (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤)
    (obtain_C : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → ∀ w : Space, w ≠ 0 → ∀ i j k : Fin 3,
      |T8_1.Gm k i j (t, w)| ≤ C * (‖w‖ ^ 4)⁻¹) :
    Integrable (Function.uncurry fun (ρ : ℝ) (e : ℝ × Space) =>
      ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e)
      ((volume.restrict (Ioi r)).prod volume) := by
  obtain ⟨C, hC0, hC⟩ := obtain_C
  have hTm : ∀ i j : Fin 3, Measurable fun s : ℝ × Space => oldPhys R c g s.1 s.2 i j :=
    fun i j => T8_1.measurable_oldPhys_entry R c g hg i j
  have hmeas : Measurable (Function.uncurry fun (ρ : ℝ) (e : ℝ × Space) =>
      ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e) :=
    measurable_fst.mul (pdOR_xKerGm_joint ν μ τ y3 (oldPhys R c g) hTm 2)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeas.enorm.aemeasurable]
  have hb : ∀ᵐ ρ ∂(volume.restrict (Ioi r)),
      ∫⁻ e : ℝ × Space, ‖Function.uncurry (fun (ρ : ℝ) (e : ℝ × Space) =>
          ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e) (ρ, e)‖ₑ ≤
        ENNReal.ofReal (27 * C) * ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
          (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
          else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    have hρr : r < ρ := Set.mem_Ioi.mp hρ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun e => ?_
    exact pdOR_enorm_le ν μ τ y3 C hν hC0 hC (oldPhys R c g) ρ (hr.trans hρr)
      (fun σ z hz => lt_trans (hsupp σ z hz) hρr) e
  refine lt_of_le_of_lt (lintegral_mono_ae hb) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- **The outward primitive in phase-lag form** (source 4178-4186): `PDOutPrimRep`. -/
theorem pdOutPrimRep : PDOutPrimRep := by
  intro ν μ R c g hν hR hc hμ0 hμ1 hg τ r y3 hr hsupp hfin
  obtain ⟨C, hC0, hC⟩ := gm_bound
  have hF0 := pdOR_F0_meas μ τ R c y3 g hg
  have hHm := Measurable.lintegral_prod_right' (ν := (volume : Measure (ℝ × Space))) hF0
  have hGae : ∀ᵐ ρ ∂(volume.restrict (Ioi r)),
      ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
        (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ := by
    filter_upwards [ae_lt_top hHm hfin.ne, ae_restrict_mem measurableSet_Ioi] with ρ hH hρ
    have hρr : r < ρ := Set.mem_Ioi.mp hρ
    have hρpos : 0 < ρ := hr.trans hρr
    have hid : ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
          (ρ * pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
          else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 =
        ENNReal.ofReal ρ * ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
          (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
          else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun e => pdOR_key μ τ ρ y3 hρpos.le (oldPhys R c g) e
    have hH' := hH
    rw [hid] at hH'
    exact ENNReal.lt_top_of_mul_ne_top_right hH'.ne (ENNReal.ofReal_pos.2 hρpos).ne'
  have hsP : ∀ ρ : ℝ, r < ρ → ∀ σ z, oldPhys R c g σ z ≠ 0 →
      ϱ z < ϱ (!₂[ρ, 0, y3] : Space) := by
    intro ρ hρr σ z hz
    rw [pdOR_varrho (hr.trans hρr).le]
    exact lt_trans (hsupp σ z hz) hρr
  have hcomp : ∀ ρ : ℝ, r < ρ →
      ∫⁻ e : ℝ × Space, (if e.1 < τ then ENNReal.ofReal
        (pdLam (τ - e.1) ^ (2 * μ + 3) * (‖(!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2‖ ^ 4)⁻¹)
        else 0) * IIIa.srcNorm (oldPhys R c g) e.1 e.2 < ⊤ →
      (wardX0 ν μ R c g τ (!₂[ρ, 0, y3] : Space)) 2 =
        ∫ e : ℝ × Space, xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e := by
    intro ρ hρr hG
    rw [pdX0Rep ν μ R c g hν hR hc hμ0 hμ1 hg τ _ (hsP ρ hρr) hG]
    have hint := (pdX0RepIntegrable ν μ R c g hν hR hc hμ0 hμ1 hg τ _ (hsP ρ hρr) hG).2
    have hl := ContinuousLinearMap.integral_comp_comm
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) hint
    simp only [EuclideanSpace.proj, PiLp.proj_apply] at hl
    rw [← hl]
    refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
    show (if e.1 < τ then xKer ν μ (τ - e.1) ((!₂[ρ, 0, y3] : Space) - pdLam (τ - e.1) • e.2)
        (oldPhys R c g e.1 e.2) else 0) 2 = _
    rw [xKerGm_eq ν μ τ _ (oldPhys R c g) (hsP ρ hρr) e]
  have hA : ∫ ρ in Ioi r, ρ * (wardX0 ν μ R c g τ (!₂[ρ, 0, y3] : Space)) 2 =
      ∫ ρ in Ioi r, ∫ e : ℝ × Space, ρ * xKerGm ν μ (oldPhys R c g) τ (!₂[ρ, 0, y3] : Space) 2 e := by
    refine integral_congr_ae ?_
    filter_upwards [hGae, ae_restrict_mem measurableSet_Ioi] with ρ hG hρ
    rw [hcomp ρ (Set.mem_Ioi.mp hρ) hG, integral_const_mul]
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
  have hF_int := pdOR_F_int ν μ R c τ r y3 g hν hg hr hsupp hfin
    ⟨C, hC0, hC⟩
  unfold outPrim
  rw [hA, integral_integral_swap hF_int]
  simp_rw [hC']
  rw [integral_neg, neg_neg]

end UnforcedLeray.Short.PartIIIb.Concrete

end
