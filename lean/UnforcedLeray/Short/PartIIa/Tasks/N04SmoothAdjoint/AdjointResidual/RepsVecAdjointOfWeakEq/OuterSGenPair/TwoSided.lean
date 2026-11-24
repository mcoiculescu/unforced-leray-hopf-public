import UnforcedLeray.Units.B0223

/-!
# Generator pairs from a right derivative at `0` (helper for `PartII-a:N04/3/3/1`)

For a contraction semigroup `S` (`‖S(t)‖ ≤ 1`, `t ≥ 0`), a right derivative `y` at `0` of
`r ↦ S(r)x` gives `d/dt S(t)x = S(t)y` at every `t > 0`, i.e. `B0223.IsGenPair S x y`.
Right side: `S(s)x - S(t)x = S(t)(S(s-t)x - x)`; left side: `S(s)x - S(t)x = S(s)(x - S(t-s)x)`
and `S(s)y → S(t)y` by strong continuity (the argument of `OD_TwoSided`, PartIII-b).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.OuterSGen

open UnforcedLeray.Infra

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

theorem isGenPair_of_rightDeriv (S : ExpSemigroup Y) (hN : ∀ s : ℝ, 0 ≤ s → ‖S.T s‖ ≤ 1)
    {x y : Y} (hx : HasDerivWithinAt (fun r : ℝ => S.T r x) y (Ici 0) 0) :
    UnforcedLeray.B0223.IsGenPair S x y := by
  intro t ht
  have hN' : ∀ s : ℝ, 0 ≤ s → ∀ v : Y, ‖S.T s v‖ ≤ ‖v‖ := fun s hs v =>
    ((S.T s).le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) (hN s hs))
  have hsmul : ∀ (s c : ℝ) (v : Y), S.T s (c • v) = c • S.T s v := fun s c v =>
    (S.T s).map_smul_of_tower c v
  let q : ℝ → Y := fun r => r⁻¹ • (S.T r x - x)
  have hq : Tendsto q (𝓝[Ioi 0] 0) (𝓝 y) := by
    have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hx).mono_left
      (nhdsWithin_mono (0 : ℝ) (fun z (hz : z ∈ Ioi 0) => ⟨le_of_lt hz, fun e => ne_of_gt hz e⟩))
    refine Tendsto.congr (fun r => ?_) h1
    simp only [slope_def_module, S.T_zero_apply, sub_zero, q]
  have hR : Tendsto (slope (fun s : ℝ => S.T s x) t) (𝓝[Ioi t] t) (𝓝 (S.T t y)) := by
    have h0 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) :=
      (by fun_prop : Continuous fun s : ℝ => s - t).tendsto' t 0 (sub_self t)
    have hsub : Tendsto (fun s : ℝ => s - t) (𝓝[Ioi t] t) (𝓝[Ioi 0] 0) :=
      tendsto_nhdsWithin_iff.2
        ⟨h0.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Ioi t) => sub_pos.2 (show t < s from hs)⟩
    have hqs : Tendsto (fun s : ℝ => ‖q (s - t) - y‖) (𝓝[Ioi t] t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hq.comp hsub)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
      norm_nonneg _) ?_ hqs)
    refine eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Ioi t) => ?_
    have hts : t < s := hs
    have hpos : s - t ≠ 0 := (sub_pos.2 hts).ne'
    have hfs : S.T s x = S.T t (S.T (s - t) x) := by
      have := S.T_apply_add ht.le (sub_pos.2 hts).le x
      rwa [show t + (s - t) = s by ring] at this
    have e1 : S.T s x - S.T t x = S.T t (S.T (s - t) x - x) := by
      rw [hfs, map_sub]
    have e2 : S.T (s - t) x - x = (s - t) • q (s - t) := by
      simp only [q]
      rw [smul_inv_smul₀ hpos]
    have hslope : slope (fun s : ℝ => S.T s x) t s = S.T t (q (s - t)) := by
      show (s - t)⁻¹ • (S.T s x - S.T t x) = _
      rw [e1, e2, hsmul, inv_smul_smul₀ hpos]
    show ‖slope (fun s : ℝ => S.T s x) t s - S.T t y‖ ≤ ‖q (s - t) - y‖
    rw [hslope, ← map_sub]
    exact hN' t ht.le _
  have hL : Tendsto (slope (fun s : ℝ => S.T s x) t) (𝓝[Iio t] t) (𝓝 (S.T t y)) := by
    have h0 : Tendsto (fun s : ℝ => t - s) (𝓝 t) (𝓝 0) :=
      (by fun_prop : Continuous fun s : ℝ => t - s).tendsto' t 0 (sub_self t)
    have hsub : Tendsto (fun s : ℝ => t - s) (𝓝[Iio t] t) (𝓝[Ioi 0] 0) :=
      tendsto_nhdsWithin_iff.2
        ⟨h0.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun s (hs : s ∈ Iio t) => sub_pos.2 (show s < t from hs)⟩
    have hqs : Tendsto (fun s : ℝ => ‖q (t - s) - y‖) (𝓝[Iio t] t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hq.comp hsub)
    have hc : ContinuousAt (fun s : ℝ => S.T s y) t :=
      (S.T_cont y).continuousAt (Ici_mem_nhds ht)
    have hcont : Tendsto (fun s : ℝ => ‖S.T s y - S.T t y‖) (𝓝[Iio t] t) (𝓝 0) :=
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
    have hfs : S.T t x = S.T s (S.T (t - s) x) := by
      have := S.T_apply_add hs2.le (sub_pos.2 hs1).le x
      rwa [show s + (t - s) = t by ring] at this
    have e1 : S.T s x - S.T t x = S.T s (x - S.T (t - s) x) := by
      rw [hfs, map_sub]
    have e2 : x - S.T (t - s) x = (-(t - s)) • q (t - s) := by
      simp only [q]
      rw [neg_smul, smul_inv_smul₀ hpos, neg_sub]
    have hslope : slope (fun s : ℝ => S.T s x) t s = S.T s (q (t - s)) := by
      show (s - t)⁻¹ • (S.T s x - S.T t x) = _
      rw [e1, e2, hsmul, smul_smul, show (s - t)⁻¹ * (-(t - s)) = 1 by
        rw [show -(t - s) = s - t by ring]
        exact inv_mul_cancel₀ hpos', one_smul]
    have hsplit : S.T s (q (t - s)) - S.T t y
        = S.T s (q (t - s) - y) + (S.T s y - S.T t y) := by
      rw [map_sub]
      abel
    show ‖slope (fun s : ℝ => S.T s x) t s - S.T t y‖
      ≤ ‖q (t - s) - y‖ + ‖S.T s y - S.T t y‖
    rw [hslope, hsplit]
    linarith [hN' s hs2.le (q (t - s) - y),
      norm_add_le (S.T s (q (t - s) - y)) (S.T s y - S.T t y)]
  have hR' : HasDerivWithinAt (fun s : ℝ => S.T s x) (S.T t y) (Ici t) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    exact hR.mono_left (nhdsWithin_mono t
      (fun z (hz : z ∈ Ici t \ {t}) => lt_of_le_of_ne hz.1 (fun e => hz.2 e.symm)))
  have hL' : HasDerivWithinAt (fun s : ℝ => S.T s x) (S.T t y) (Iic t) t := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    exact hL.mono_left (nhdsWithin_mono t
      (fun z (hz : z ∈ Iic t \ {t}) => lt_of_le_of_ne hz.1 (fun e => hz.2 e)))
  have hU := hL'.union hR'
  rw [Set.Iic_union_Ici] at hU
  exact hasDerivWithinAt_univ.1 hU

end UnforcedLeray.Short.PartIIa.OuterSGen
