import UnforcedLeray.Short.PartI.Sub.PartI_C06
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildCocycle
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildShortBound
import UnforcedLeray.Cons.L2.CanonicalBranch.Evolution
import UnforcedLeray.Units.B0123

/-!


Source of record: `the November 2 reference manuscript`, lines 1102-1108 and
`lem:short-diffusion-complement`, lines 1014-1058.

Method. Fix `t` and `x`, and a point `s₀ ≤ t`. Then `Iic t = Iic s₀ ∪ Icc s₀ t`, and the two
one-sided limits are proved separately.

* Right (`s ∈ [s₀,t]`): the cocycle gives `U(t,s₀)x - U(t,s)x = U(t,s)(x - U(s,s₀)x)`, and the
  short block bound `‖U(t,s)‖ ≤ K` with `U(s,s₀)x → x` gives the limit.
* Left (`s ∈ (s₀-1,s₀]`): the cocycle gives `U(t,s)x - U(t,s₀)x = U(t,s₀)(U(s₀,s)x - x)`, and the
  Duhamel identity gives `‖U(s₀,s)x - x‖ ≤ ‖e^{D∫_s^{s₀}β}x - x‖ + (s₀-s) M K ‖x‖`. The first
  term tends to `0` because `∫_s^{s₀}β → 0` and `a ↦ e^{Da}x` is continuous with `e^{D·0} = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- One Duhamel step: if `W = e^{D∫_s^{s₀}β}x + ∫_s^{s₀} e^{D∫_r^{s₀}β} G(r) V(r) dr` with
`‖G r‖ ≤ M` and `‖V r‖ ≤ C` on `[s,s₀]`, then `‖W - x‖ ≤ ‖e^{D∫_s^{s₀}β}x - x‖ + (s₀-s)(MC)`. -/
theorem mcs_step {β : ℝ → ℝ} (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {G : ℝ → B0010.XG →L[ℂ] B0010.XG} {V : ℝ → B0010.XG} {s s₀ M C : ℝ} (hsr : s ≤ s₀)
    (x W : B0010.XG) (hG : ∀ r, ‖G r‖ ≤ M) (hV : ∀ r ∈ Icc s s₀, ‖V r‖ ≤ C)
    (hd : W = B0123.expD (∫ u in s..s₀, β u) x +
      ∫ r in s..s₀, B0123.expD (∫ u in r..s₀, β u) (G r (V r))) :
    ‖W - x‖ ≤ ‖B0123.expD (∫ u in s..s₀, β u) x - x‖ + (s₀ - s) * (M * C) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hG 0)
  have hI : ‖∫ r in s..s₀, B0123.expD (∫ u in r..s₀, β u) (G r (V r))‖ ≤ (M * C) * |s₀ - s| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    rw [uIoc_of_le hsr] at hr
    have hrI : r ∈ Icc s s₀ := ⟨hr.1.le, hr.2⟩
    calc ‖B0123.expD (∫ u in r..s₀, β u) (G r (V r))‖
        ≤ ‖B0123.expD (∫ u in r..s₀, β u)‖ * ‖G r (V r)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (‖G r‖ * ‖V r‖) :=
          mul_le_mul (B0123.norm_expD_le _) (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            zero_le_one
      _ ≤ 1 * (M * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hG r) (hV r hrI) (norm_nonneg _) hM0) zero_le_one
      _ = M * C := one_mul _
  rw [hd, add_sub_right_comm]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine hI.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₀ - s), mul_comm]

/-- Right block: for `s₀ ≤ t`, `s ↦ U(t,s)x` is continuous within `[s₀,t]` at `s₀`. -/
theorem mcs_right_limit {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hseed : IsSeedXG lam q l) {qd : B0010.XG} (hl : ∀ f, l f = inner ℂ qd f)
    {hq : q ∈ B0094.D.domain} {hqd : qd ∈ B0094.D.domain} {β : ℝ → ℝ}
    (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG} (hU : MildCtx lam q l qd hq hqd β U)
    (x : B0010.XG) {s₀ t : ℝ} (hs₀t : s₀ ≤ t) :
    ContinuousWithinAt (fun s => U t s x) (Icc s₀ t) s₀ := by
  obtain ⟨K, hK⟩ := mildComplementShortBound lam q l hseed qd hl hq hqd (t - s₀ + 2) (by linarith)
  have hev : ∀ᶠ s in 𝓝[Icc s₀ t] s₀, ‖U t s x - U t s₀ x‖ ≤ K * ‖x - U s s₀ x‖ := by
    refine (eventually_mem_nhdsWithin).mono fun s hs => ?_
    have hs₀s : s₀ ≤ s := hs.1
    have hst : s ≤ t := hs.2
    have hcoc := mildComplementCocycle lam q l hseed qd hl hq hqd β hβm hβ U hU s₀ s t hs₀s hst
    have hnorm : ‖U t s‖ ≤ K := hK β hβm hβ U hU s t hst (by linarith)
    have hx : U t s₀ x = U t s (U s s₀ x) := by
      rw [hcoc, ContinuousLinearMap.mul_apply]
    calc ‖U t s x - U t s₀ x‖ = ‖U t s (x - U s s₀ x)‖ := by rw [hx, map_sub]
      _ ≤ ‖U t s‖ * ‖x - U s s₀ x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖x - U s s₀ x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  have hc : ContinuousWithinAt (fun s => U s s₀ x) (Icc s₀ t) s₀ :=
    ((hU.cont s₀ x).mono Icc_subset_Ici_self).continuousWithinAt (left_mem_Icc.2 hs₀t)
  have h0 : U s₀ s₀ x = x := by simp [hU.self_eq s₀]
  have hc2 : ContinuousWithinAt (fun s => K * ‖x - U s s₀ x‖) (Icc s₀ t) s₀ :=
    (continuousWithinAt_const.sub hc).norm.const_mul K
  have hlim : Tendsto (fun s => K * ‖x - U s s₀ x‖) (𝓝[Icc s₀ t] s₀) (𝓝 0) := by
    have h2 : Tendsto (fun s => K * ‖x - U s s₀ x‖) (𝓝[Icc s₀ t] s₀)
        (𝓝 (K * ‖x - U s₀ s₀ x‖)) := hc2
    rw [h0, sub_self, norm_zero, mul_zero] at h2
    exact h2
  have hdiff : Tendsto (fun s => U t s x - U t s₀ x) (𝓝[Icc s₀ t] s₀) (𝓝 0) :=
    squeeze_zero_norm' hev hlim
  exact tendsto_sub_nhds_zero_iff.1 hdiff

/-- Left block: for `s₀ ≤ t`, `s ↦ U(t,s)x` is continuous within `(-∞,s₀]` at `s₀`. -/
theorem mcs_left_limit {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hseed : IsSeedXG lam q l) {qd : B0010.XG} (hl : ∀ f, l f = inner ℂ qd f)
    {hq : q ∈ B0094.D.domain} {hqd : qd ∈ B0094.D.domain} {β : ℝ → ℝ}
    (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {U : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG} (hU : MildCtx lam q l qd hq hqd β U)
    (x : B0010.XG) {s₀ t : ℝ} (hs₀t : s₀ ≤ t) :
    ContinuousWithinAt (fun s => U t s x) (Iic s₀) s₀ := by
  obtain ⟨K, hK⟩ := mildComplementShortBound lam q l hseed qd hl hq hqd (t - s₀ + 2) (by linarith)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ‖Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
      l.smulRight q‖ + ‖seedKappa l q hq‖ + ‖seedRf l q qd hq hqd‖ := ⟨_, rfl⟩
  have hG : ∀ r, ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
      (β r * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG) +
        (β r : ℂ) • seedRf l q qd hq hqd)‖ ≤ M := fun r => by
    rw [hMdef]
    exact mcc_norm_B_le lam l q (seedKappa l q hq) (seedRf l q qd hq hqd) (hβ r)
  -- the small-time limit of the free phase `a(s) = ∫_s^{s₀} β → 0`
  have hA : Tendsto (fun s => ∫ u in s..s₀, β u) (𝓝[Iic s₀] s₀) (𝓝 0) := by
    apply squeeze_zero' (g := fun s => s₀ - s)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact intervalIntegral.integral_nonneg (hs : s ≤ s₀) fun u _ => (hβ u).1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have := intervalIntegral.integral_mono_on (hs : s ≤ s₀)
        (mcc_intervalIntegrable_beta hβm hβ s s₀) (intervalIntegrable_const (c := (1 : ℝ)))
        (fun u _ => (hβ u).2)
      simpa using this
    · have hc : Continuous (fun s : ℝ => s₀ - s) := continuous_const.sub continuous_id
      have h1 : Tendsto (fun s : ℝ => s₀ - s) (𝓝 s₀) (𝓝 0) := by
        simpa using hc.tendsto s₀
      exact h1.mono_left nhdsWithin_le_nhds
  -- the free phase tends to zero
  have hE : Tendsto (fun s => ‖B0123.expD (∫ u in s..s₀, β u) x - x‖) (𝓝[Iic s₀] s₀) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => ‖B0123.expD a x - x‖) :=
      ((Cons.G3b.continuous_expD_apply x).sub continuous_const).norm
    have h0 : ‖B0123.expD 0 x - x‖ = 0 := by
      rw [B0123.expD_zero]
      simp
    have h2 : Tendsto (fun s => ‖B0123.expD (∫ u in s..s₀, β u) x - x‖) (𝓝[Iic s₀] s₀)
        (𝓝 ‖B0123.expD 0 x - x‖) := (hcont.tendsto 0).comp hA
    rw [h0] at h2
    exact h2
  have hs0 : Tendsto (fun s : ℝ => s₀ - s) (𝓝[Iic s₀] s₀) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s₀ - s) := continuous_const.sub continuous_id
    have h1 : Tendsto (fun s : ℝ => s₀ - s) (𝓝 s₀) (𝓝 0) := by
      simpa using hc.tendsto s₀
    exact h1.mono_left nhdsWithin_le_nhds
  have hG' : Tendsto (fun s => K * (‖B0123.expD (∫ u in s..s₀, β u) x - x‖ +
      (s₀ - s) * (M * (K * ‖x‖)))) (𝓝[Iic s₀] s₀) (𝓝 0) := by
    have := (hE.add (hs0.mul_const (M * (K * ‖x‖)))).const_mul K
    simpa only [zero_mul, zero_add, mul_zero] using this
  have hev : ∀ᶠ s in 𝓝[Iic s₀] s₀, ‖U t s x - U t s₀ x‖ ≤ K * (‖B0123.expD (∫ u in s..s₀, β u) x - x‖ +
      (s₀ - s) * (M * (K * ‖x‖))) := by
    have hmem : ∀ᶠ s in 𝓝[Iic s₀] s₀, s ∈ Ioc (s₀ - 1) s₀ := Ioc_mem_nhdsLE (by linarith)
    filter_upwards [hmem] with s hs
    have hss₀ : s ≤ s₀ := hs.2
    have hs1 : s₀ - 1 < s := hs.1
    have hcoc := mildComplementCocycle lam q l hseed qd hl hq hqd β hβm hβ U hU s s₀ t hss₀ hs₀t
    have hnorm : ‖U t s₀‖ ≤ K := hK β hβm hβ U hU s₀ t hs₀t (by linarith)
    have hK0 : 0 ≤ K := (norm_nonneg _).trans hnorm
    have hxU : U t s x - U t s₀ x = U t s₀ (U s₀ s x - x) := by
      rw [hcoc, ContinuousLinearMap.mul_apply, map_sub]
    have h1 : ‖U t s x - U t s₀ x‖ ≤ K * ‖U s₀ s x - x‖ := by
      rw [hxU]
      calc ‖U t s₀ (U s₀ s x - x)‖ ≤ ‖U t s₀‖ * ‖U s₀ s x - x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖U s₀ s x - x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    have hV : ∀ r ∈ Icc s s₀, ‖U r s x‖ ≤ K * ‖x‖ := by
      intro r hr
      have hK' : ‖U r s‖ ≤ K := hK β hβm hβ U hU s r hr.1 (by linarith [hr.2])
      calc ‖U r s x‖ ≤ ‖U r s‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖x‖ := mul_le_mul_of_nonneg_right hK' (norm_nonneg _)
    have hd := hU.duhamel s s₀ hss₀ x
    have h2 : ‖U s₀ s x - x‖ ≤ ‖B0123.expD (∫ u in s..s₀, β u) x - x‖ +
        (s₀ - s) * (M * (K * ‖x‖)) :=
      mcs_step hβ hss₀ x (U s₀ s x) (G := fun r => (Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
        l.smulRight q - (β r * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG) +
          (β r : ℂ) • seedRf l q qd hq hqd)) (V := fun r => U r s x) (M := M) (C := K * ‖x‖)
        hG hV hd
    calc ‖U t s x - U t s₀ x‖ ≤ K * ‖U s₀ s x - x‖ := h1
      _ ≤ K * (‖B0123.expD (∫ u in s..s₀, β u) x - x‖ + (s₀ - s) * (M * (K * ‖x‖))) :=
          mul_le_mul_of_nonneg_left h2 hK0
  have hfin : Tendsto (fun s => U t s x - U t s₀ x) (𝓝[Iic s₀] s₀) (𝓝 0) :=
    squeeze_zero_norm' hev hG'
  exact tendsto_sub_nhds_zero_iff.1 hfin

/-- **Target `PartI:C06/2`** (source lines 1102-1108): strong continuity of the mild complementary
evolution in its initial time on `(-∞,t]`. -/
theorem mildComplementContStart : MildComplementContStart := by
  intro lam q l hseed qd hl hq hqd β hβm hβ U hU t x
  intro s₀ hs₀
  have hs₀t : s₀ ≤ t := hs₀
  rw [← Set.Iic_union_Icc_eq_Iic hs₀t]
  exact continuousWithinAt_union.2
    ⟨mcs_left_limit hseed hl hβm hβ hU x hs₀t, mcs_right_limit hseed hl hβm hβ hU x hs₀t⟩

end UnforcedLeray.Short.PartI
