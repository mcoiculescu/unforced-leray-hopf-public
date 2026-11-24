import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.Dyn.XMulTestInt
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The `X_{-m,c}` norm of a difference of two `L²` fields, as a real norm of `Lp` elements. -/
theorem chiCont_xNorm_eq {c m : ℝ} {f g : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hg : MemLp g 2 (B0579.cellMeasure c (-m))) :
    xNorm c (-m) (f - g) = ENNReal.ofReal ‖hf.toLp f - hg.toLp g‖ := by
  have hfg : MemLp (f - g) 2 (B0579.cellMeasure c (-m)) := hf.sub hg
  have hae : (⇑(hf.toLp f - hg.toLp g)) =ᵐ[B0579.cellMeasure c (-m)] f - g := by
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
      with x h1 h2 h3
    simp only [Pi.sub_apply] at h1 ⊢
    rw [h1, h2, h3]
  have hn : ‖hf.toLp f - hg.toLp g‖ = (eLpNorm (f - g) 2 (B0579.cellMeasure c (-m))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
  rw [hn, xNorm, ENNReal.ofReal_toReal hfg.eLpNorm_lt_top.ne]

/-- **(C3) `χ` is continuous into `X_{-m,c}` on `(a, b)`** (needs `8 < m`). -/
theorem chiCont (m : ℝ) : UnforcedLeray.Short.IIIa.ChiCont m := by
  unfold ChiCont
  intro hm8 ν tr t s g φ a b χ hctx r hr
  obtain ⟨hν, hν1, hLad, ht0, hts, hA, hT, hta, hab, hbs, hchi⟩ := hctx
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hs0 : 0 ≤ s := le_trans ht0 hts.le
  obtain ⟨C, hC⟩ := hLad s hs0
  obtain ⟨K, β, hKb, hKc, hKp⟩ := adjLocalizedCoeff m hm8 ν hν hν1 tr s C hs0 hC
  have hsub : Ioo a b ⊆ Icc t s := fun x hx => ⟨le_trans hta hx.1.le, le_trans hx.2.le hbs.le⟩
  have hsub0 : Ioo a b ⊆ Icc 0 s := fun x hx =>
    ⟨le_trans ht0 (le_trans hta hx.1.le), le_trans hx.2.le hbs.le⟩
  have hΦm : ∀ x ∈ Ioo a b, MemLp (φ x) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun x hx => hA.memX x (hsub hx)
  have hχm : ∀ x ∈ Ioo a b, MemLp (χ x) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun x hx => (hchi x (Ioo_subset_Icc_self hx)).2.1
  -- the `X_{-m,c}` elements of `φ` and `χ` on `(a, b)`
  let Φ : ℝ → AdjX (ν ^ (-2 : ℝ)) m := fun x =>
    if hx : x ∈ Ioo a b then (hΦm x hx).toLp (φ x) else 0
  let Xc : ℝ → AdjX (ν ^ (-2 : ℝ)) m := fun x =>
    if hx : x ∈ Ioo a b then (hχm x hx).toLp (χ x) else 0
  have hΦeq : ∀ x (hx : x ∈ Ioo a b), Φ x = (hΦm x hx).toLp (φ x) := fun x hx => dif_pos hx
  have hXcEq : ∀ x (hx : x ∈ Ioo a b), Xc x = (hχm x hx).toLp (χ x) := fun x hx => dif_pos hx
  -- the identification `χ = K φ` in `X_{-m,c}` on `(a, b)`
  have hclaim : ∀ ρ (hρ : ρ ∈ Ioo a b), Xc ρ = K ρ (Φ ρ) := by
    intro ρ hρ
    rw [hXcEq ρ hρ, hΦeq ρ hρ]
    have hzero : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          (⇑((hχm ρ hρ).toLp (χ ρ) - K ρ ((hΦm ρ hρ).toLp (φ ρ))) x) * (ψ x : ℂ) = 0 := by
      intro ψ hψ
      obtain ⟨uψ, hu⟩ := kernelBSExists (ν ^ (-2 : ℝ)) ψ hc hψ
      have hχP := (hchi ρ (Ioo_subset_Icc_self hρ)).2.2 ψ uψ hψ hu
      have hKP := hKp ρ (hsub0 hρ) ((hΦm ρ hρ).toLp (φ ρ)) ψ uψ hψ hu
      have hI1 := xMulTestInt (ν ^ (-2 : ℝ)) m (χ ρ) ψ hc (hχm ρ hρ) hψ
      have hI2 := xMulTestInt (ν ^ (-2 : ℝ)) m (⇑(K ρ ((hΦm ρ hρ).toLp (φ ρ)))) ψ hc
        (Lp.memLp _) hψ
      have ae1 : (⇑((hχm ρ hρ).toLp (χ ρ) - K ρ ((hΦm ρ hρ).toLp (φ ρ)))) =ᵐ[
          B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)] fun x => χ ρ x - (K ρ ((hΦm ρ hρ).toLp (φ ρ))) x := by
        filter_upwards [Lp.coeFn_sub ((hχm ρ hρ).toLp (χ ρ))
          (K ρ ((hΦm ρ hρ).toLp (φ ρ))), (hχm ρ hρ).coeFn_toLp] with x h1 h2
        rw [h1, Pi.sub_apply, h2]
      have ae2 : (⇑((hΦm ρ hρ).toLp (φ ρ))) =ᵐ[B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)]
          φ ρ := (hΦm ρ hρ).coeFn_toLp
      have ae1' : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
          (⇑((hχm ρ hρ).toLp (χ ρ) - K ρ ((hΦm ρ hρ).toLp (φ ρ)))) x =
            χ ρ x - (K ρ ((hΦm ρ hρ).toLp (φ ρ))) x :=
        (B0579.ac_cellMeasure (ν ^ (-2 : ℝ)) (-m)).ae_le ae1
      have ae2' : ∀ᵐ x ∂(volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))),
          (⇑((hΦm ρ hρ).toLp (φ ρ))) x = φ ρ x :=
        (B0579.ac_cellMeasure (ν ^ (-2 : ℝ)) (-m)).ae_le ae2
      have hW : ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (⇑((hΦm ρ hρ).toLp (φ ρ))) x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ) =
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ ρ x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr ρ) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ) :=
        integral_congr_ae (ae2'.mono fun x hx => by dsimp only; rw [hx])
      have e : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            (⇑((hχm ρ hρ).toLp (χ ρ) - K ρ ((hΦm ρ hρ).toLp (φ ρ))) x) * (ψ x : ℂ) =
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (χ ρ x * (ψ x : ℂ) -
            ⇑(K ρ ((hΦm ρ hρ).toLp (φ ρ))) x * (ψ x : ℂ)) :=
        integral_congr_ae (ae1'.mono fun x hx => by dsimp only; rw [hx]; ring)
      rw [e, integral_sub hI1 hI2, hχP.2, hKP.2, hW, sub_self]
    exact sub_eq_zero.1 (locCylUniq (ν ^ (-2 : ℝ)) m hc _ hzero)
  -- the real estimate on `(a, b)`
  have hsc : Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r)) (𝓝[Ioo a b] r)
      (𝓝 0) :=
    (hA.strongCont r (hsub hr)).mono_left (nhdsWithin_mono r hsub)
  have hΦt : Tendsto (fun r' => ‖Φ r' - Φ r‖) (𝓝[Ioo a b] r) (𝓝 0) := by
    have h2 : Tendsto (fun r' => (xNorm (ν ^ (-2 : ℝ)) (-m) (φ r' - φ r)).toReal)
        (𝓝[Ioo a b] r) (𝓝 (0 : ℝ≥0∞).toReal) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsc
    simp only [ENNReal.toReal_zero] at h2
    refine h2.congr' (eventually_nhdsWithin_of_forall fun r' hr' => ?_)
    dsimp only
    rw [hΦeq r' hr', hΦeq r hr, ← MemLp.toLp_sub, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (MemLp.coeFn_toLp _).symm)
  have hKt : Tendsto (fun r' => ‖K r' (Φ r) - K r (Φ r)‖) (𝓝[Ioo a b] r) (𝓝 0) := by
    have h : Tendsto (fun x => K x (Φ r)) (𝓝[Ioo a b] r) (𝓝 (K r (Φ r))) :=
      Tendsto.mono_left (hKc (Φ r) r (hsub0 hr)) (nhdsWithin_mono r hsub0)
    exact tendsto_iff_norm_sub_tendsto_zero.1 h
  have hbound : ∀ r' ∈ Ioo a b,
      ‖K r' (Φ r') - K r (Φ r)‖ ≤ β * ‖Φ r' - Φ r‖ + ‖K r' (Φ r) - K r (Φ r)‖ := by
    intro r' hr'
    have e : K r' (Φ r') - K r (Φ r) = K r' (Φ r' - Φ r) + (K r' (Φ r) - K r (Φ r)) := by
      rw [map_sub]; abel
    rw [e]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ le_rfl)
    calc ‖K r' (Φ r' - Φ r)‖ ≤ ‖K r'‖ * ‖Φ r' - Φ r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ β * ‖Φ r' - Φ r‖ := mul_le_mul_of_nonneg_right (hKb r' (hsub0 hr')) (norm_nonneg _)
  have hfin : Tendsto (fun r' => β * ‖Φ r' - Φ r‖ + ‖K r' (Φ r) - K r (Φ r)‖)
      (𝓝[Ioo a b] r) (𝓝 0) := by
    simpa using (hΦt.const_mul β).add hKt
  have hg0 : Tendsto (fun r' => ‖K r' (Φ r') - K r (Φ r)‖) (𝓝[Ioo a b] r) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfin
      (eventually_nhdsWithin_of_forall fun _ _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun r' hr' => hbound r' hr')
  have hrepr : ∀ r' ∈ Ioo a b, xNorm (ν ^ (-2 : ℝ)) (-m) (χ r' - χ r) =
      ENNReal.ofReal ‖K r' (Φ r') - K r (Φ r)‖ := by
    intro r' hr'
    rw [chiCont_xNorm_eq (hχm r' hr') (hχm r hr), ← hXcEq r' hr', ← hXcEq r hr,
      hclaim r' hr', hclaim r hr]
  have hfinal : Tendsto (fun r' => ENNReal.ofReal ‖K r' (Φ r') - K r (Φ r)‖) (𝓝[Ioo a b] r)
      (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hg0
    rw [ENNReal.ofReal_zero] at h
    exact h
  exact hfinal.congr' (eventually_nhdsWithin_of_forall fun r' hr' => (hrepr r' hr').symm)

end UnforcedLeray.Short.IIIa
