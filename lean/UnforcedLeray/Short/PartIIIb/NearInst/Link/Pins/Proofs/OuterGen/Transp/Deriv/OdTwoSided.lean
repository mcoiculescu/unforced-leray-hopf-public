import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdZero
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdAdd
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.OdCont

/-!
# `OD_TwoSided` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/16`)

Abstract upgrade: a right derivative `Ψ'` at `0` of `r ↦ U r Ψ` (with `U = outerTransp h`)
gives a two-sided derivative `U t Ψ'` at every `t > 0`.

Right side (`s > t`): `U s Ψ - U t Ψ = U t (U (s-t) Ψ - Ψ)`, so the difference quotient is
`U t (q (s-t))` with `q r = r⁻¹ • (U r Ψ - Ψ) → Ψ'`.
Left side (`0 < s < t`): `U t Ψ = U s (U (t-s) Ψ)`, so the quotient is `U s (q (t-s))`, and
`‖U s (q (t-s)) - U t Ψ'‖ ≤ ‖q (t-s) - Ψ'‖ + ‖U s Ψ' - U t Ψ'‖`.
The two one-sided derivatives are glued by `HasDerivWithinAt.union`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odTwoSided : OD_TwoSided := by
  intro P _ h hh Ψ Ψ' hΨ t ht
  have hZ : ∀ x : XC P, outerTransp h 0 x = x := fun x => odZero P h x
  have hN : ∀ s : ℝ, 0 ≤ s → ∀ x : XC P, ‖outerTransp h s x‖ ≤ ‖x‖ := by
    intro s hs x
    refine (odNorm P h s x).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 (by linarith))
  have hA : ∀ s u : ℝ, 0 ≤ s → 0 ≤ u → ∀ x : XC P,
      outerTransp h (s + u) x = outerTransp h s (outerTransp h u x) :=
    fun s u hs hu x => odAdd P h hh s u hs hu x
  have hCc : ContinuousOn (fun s : ℝ => outerTransp h s Ψ') (Ici 0) := odCont P h hh Ψ'
  have hadd : ∀ (s : ℝ) (x y : XC P),
      outerTransp h s (x - y) = outerTransp h s x - outerTransp h s y := by
    intro s x y
    unfold outerTransp
    simp only [map_sub, smul_sub]
  have hsmul : ∀ (s c : ℝ) (x : XC P), outerTransp h s (c • x) = c • outerTransp h s x := by
    intro s c x
    have hc : ∀ y : XC P, c • y = (c : ℂ) • y := fun y => (Complex.coe_smul c y).symm
    unfold outerTransp
    simp only [hc, map_smul]
    exact smul_comm _ _ _
  let q : ℝ → XC P := fun r => r⁻¹ • (outerTransp h r Ψ - Ψ)
  -- the right derivative of `r ↦ U r Ψ` at `0`, as a limit of `q`
  have hq : Tendsto q (𝓝[Ioi 0] 0) (𝓝 Ψ') := by
    have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hΨ).mono_left
      (nhdsWithin_mono (0 : ℝ) (fun x (hx : x ∈ Ioi 0) => ⟨le_of_lt hx, fun e => ne_of_gt hx e⟩))
    refine Tendsto.congr (fun r => ?_) h1
    simp only [slope_def_module, hZ, sub_zero, q]
  -- right side
  have hR : Tendsto (slope (fun s : ℝ => outerTransp h s Ψ) t) (𝓝[Ioi t] t)
      (𝓝 (outerTransp h t Ψ')) := by
    have h0 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
      exact (by fun_prop : Continuous fun s : ℝ => s - t).tendsto' t 0 (sub_self t)
    have hsub : Tendsto (fun s : ℝ => s - t) (𝓝[Ioi t] t) (𝓝[Ioi 0] 0) :=
      tendsto_nhdsWithin_iff.2
        ⟨h0.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Ioi t) => sub_pos.2 (show t < s from hs)⟩
    have hqs : Tendsto (fun s : ℝ => ‖q (s - t) - Ψ'‖) (𝓝[Ioi t] t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hq.comp hsub)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
      norm_nonneg _) ?_ hqs)
    refine eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Ioi t) => ?_
    have hts : t < s := hs
    have hpos : s - t ≠ 0 := (sub_pos.2 hts).ne'
    have hfs : outerTransp h s Ψ = outerTransp h t (outerTransp h (s - t) Ψ) := by
      have := hA t (s - t) ht.le (sub_pos.2 hts).le Ψ
      rwa [show t + (s - t) = s by ring] at this
    have e1 : outerTransp h s Ψ - outerTransp h t Ψ
        = outerTransp h t (outerTransp h (s - t) Ψ - Ψ) := by
      rw [hfs, hadd]
    have e2 : outerTransp h (s - t) Ψ - Ψ = (s - t) • q (s - t) := by
      simp only [q]
      rw [smul_inv_smul₀ hpos]
    have hslope : slope (fun s : ℝ => outerTransp h s Ψ) t s
        = outerTransp h t (q (s - t)) := by
      show (s - t)⁻¹ • (outerTransp h s Ψ - outerTransp h t Ψ) = _
      rw [e1, e2, hsmul, inv_smul_smul₀ hpos]
    show ‖slope (fun s : ℝ => outerTransp h s Ψ) t s - outerTransp h t Ψ'‖ ≤ ‖q (s - t) - Ψ'‖
    rw [hslope, ← hadd]
    exact hN t ht.le _
  -- left side
  have hL : Tendsto (slope (fun s : ℝ => outerTransp h s Ψ) t) (𝓝[Iio t] t)
      (𝓝 (outerTransp h t Ψ')) := by
    have h0 : Tendsto (fun s : ℝ => t - s) (𝓝 t) (𝓝 0) := by
      exact (by fun_prop : Continuous fun s : ℝ => t - s).tendsto' t 0 (sub_self t)
    have hsub : Tendsto (fun s : ℝ => t - s) (𝓝[Iio t] t) (𝓝[Ioi 0] 0) :=
      tendsto_nhdsWithin_iff.2
        ⟨h0.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Iio t) => sub_pos.2 (show s < t from hs)⟩
    have hqs : Tendsto (fun s : ℝ => ‖q (t - s) - Ψ'‖) (𝓝[Iio t] t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hq.comp hsub)
    have hc : ContinuousAt (fun s : ℝ => outerTransp h s Ψ') t :=
      hCc.continuousAt (Ici_mem_nhds ht)
    have hcont : Tendsto (fun s : ℝ => ‖outerTransp h s Ψ' - outerTransp h t Ψ'‖)
        (𝓝[Iio t] t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hc.tendsto.mono_left nhdsWithin_le_nhds)
    have hsum := hqs.add hcont
    rw [add_zero] at hsum
    have hnear : ∀ᶠ s in 𝓝[Iio t] t, s ∈ Iio t ∧ 0 < s :=
      eventually_mem_nhdsWithin.and (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds ht))
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
      norm_nonneg _) ?_ hsum)
    refine hnear.mono fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := hs
    have hpos : t - s ≠ 0 := (sub_pos.2 hs1).ne'
    have hpos' : s - t ≠ 0 := (sub_neg.2 hs1).ne
    have hfs : outerTransp h t Ψ = outerTransp h s (outerTransp h (t - s) Ψ) := by
      have := hA s (t - s) hs2.le (sub_pos.2 hs1).le Ψ
      rwa [show s + (t - s) = t by ring] at this
    have e1 : outerTransp h s Ψ - outerTransp h t Ψ
        = outerTransp h s (Ψ - outerTransp h (t - s) Ψ) := by
      rw [hfs, hadd]
    have e2 : Ψ - outerTransp h (t - s) Ψ = (-(t - s)) • q (t - s) := by
      simp only [q]
      rw [neg_smul, smul_inv_smul₀ hpos, neg_sub]
    have hslope : slope (fun s : ℝ => outerTransp h s Ψ) t s
        = outerTransp h s (q (t - s)) := by
      show (s - t)⁻¹ • (outerTransp h s Ψ - outerTransp h t Ψ) = _
      rw [e1, e2, hsmul, smul_smul, show (s - t)⁻¹ * (-(t - s)) = 1 by
        rw [show -(t - s) = s - t by ring]
        exact inv_mul_cancel₀ hpos', one_smul]
    have hsplit : outerTransp h s (q (t - s)) - outerTransp h t Ψ'
        = outerTransp h s (q (t - s) - Ψ') + (outerTransp h s Ψ' - outerTransp h t Ψ') := by
      rw [hadd]
      abel
    show ‖slope (fun s : ℝ => outerTransp h s Ψ) t s - outerTransp h t Ψ'‖
      ≤ ‖q (t - s) - Ψ'‖ + ‖outerTransp h s Ψ' - outerTransp h t Ψ'‖
    rw [hslope, hsplit]
    linarith [hN s hs2.le (q (t - s) - Ψ'),
      norm_add_le (outerTransp h s (q (t - s) - Ψ')) (outerTransp h s Ψ' - outerTransp h t Ψ')]
  -- glue
  have hR' : HasDerivWithinAt (fun s : ℝ => outerTransp h s Ψ) (outerTransp h t Ψ') (Ici t) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    exact hR.mono_left (nhdsWithin_mono t
      (fun x (hx : x ∈ Ici t \ {t}) => lt_of_le_of_ne hx.1 (fun e => hx.2 e.symm)))
  have hL' : HasDerivWithinAt (fun s : ℝ => outerTransp h s Ψ) (outerTransp h t Ψ') (Iic t) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    exact hL.mono_left (nhdsWithin_mono t
      (fun x (hx : x ∈ Iic t \ {t}) => lt_of_le_of_ne hx.1 (fun e => hx.2 e)))
  have hU := hL'.union hR'
  rw [Set.Iic_union_Ici] at hU
  exact hasDerivWithinAt_univ.1 hU

end UnforcedLeray.Short.PartIIIb.NearInst
