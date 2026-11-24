import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6

/-!
# Decomposition of `CgiLimitWeak` (task `PartII-b:T13/1/5/6/2`)

Source `the November 2 reference manuscript`
1933-1934: "integrate by parts against `φ`, and pass to the limit; the pairing with a compactly
supported `φ` is controlled by finitely many period cells and Hölder, using periodicity".

* `CgiLocalL1`: a `q`-periodic measurable function has `L¹` norm on a compact set bounded by a
  constant times its `L^r(cylMeas c)` norm (finitely many period cells; Hölder).
* `CgiIBP`: integration by parts for smooth `w` against a compactly supported test.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- **Local `L¹` bound from the cylinder norm (SP 1933-1934).** For `r > 1`, `c > 0` and a compact
`K ⊆ ℝ × ℝ²` there is `C` with `‖g‖_{L¹(K, dvol)} ≤ C ‖g‖_{L^r(cylMeas c)}` for every `q`-periodic
(a.e.) measurable `g`: `K` is covered by finitely many translates of the `q`-cell, on each of which
`vol ≤ c · cylMeas`-comparable after the shift (periodicity), and Hölder on a set of finite
`cylMeas` measure. -/
def CgiLocalL1 : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ K : Set Coord, IsCompact K →
    ∃ C : ℝ, ∀ g : Coord → ℂ, QPeriodicS c g → AEStronglyMeasurable g volume →
      eLpNorm g 1 (volume.restrict K) ≤ ENNReal.ofReal C * cylNorm c r g

/-- **Integration by parts (SP 1933-1934).** For smooth `w` and a compactly supported test `φ`,
`∫ w ∂_{i+1} φ = -∫ ∂_{i+1} w φ`. -/
def CgiIBP : Prop :=
  ∀ (w : Coord → ℂ), ContDiff ℝ ∞ w → ∀ (i : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
    ∫ x, w x * (cpd i.succ φ x : ℂ) = -∫ x, cdv i.succ w x * (φ x : ℂ)

lemma cdv_qShift {c : ℝ} {w : Coord → ℂ} (hw : ∀ x, w (qShift c x) = w x) (j : Fin 3) (x : Coord) :
    cdv j w (qShift c x) = cdv j w x := by
  have hq : qShift c = fun y => y + ((0 : ℝ), (c, (0 : ℝ))) := by
    funext y; ext <;> simp [qShift]
  have h1 : (fun y => w (y + ((0 : ℝ), (c, (0 : ℝ))))) = w := by
    funext y; have := hw y; rwa [hq] at this
  have h2 : fderiv ℝ (fun y => w (y + ((0 : ℝ), (c, (0 : ℝ))))) x =
      fderiv ℝ w (x + ((0 : ℝ), (c, (0 : ℝ)))) := fderiv_comp_add_right _
  have h3 : fderiv ℝ w (x + ((0 : ℝ), (c, (0 : ℝ)))) = fderiv ℝ w x := by rw [← h2, h1]
  have h4 : qShift c x = x + ((0 : ℝ), (c, (0 : ℝ))) := by rw [hq]
  unfold cdv
  rw [h4, h3]

lemma cgi_conv {c r : ℝ} (hr : 1 < r) (hc : 0 < c) (h1 : CgiLocalL1) {K : Set Coord}
    (hK : IsCompact K) (a : ℕ → Coord → ℂ) (g h : Coord → ℂ) (hh : Continuous h)
    (hhK : ∀ x, x ∉ K → h x = 0) (ha : ∀ n, Continuous (a n))
    (hper : ∀ n, QPeriodicS c (fun x => a n x - g x))
    (hmeas : ∀ n, AEStronglyMeasurable (fun x => a n x - g x) volume)
    (hT : Tendsto (fun n => cylNorm c r (fun x => a n x - g x)) atTop (𝓝 0)) :
    Integrable (fun x => g x * h x) ∧
      Tendsto (fun n => ∫ x, a n x * h x) atTop (𝓝 (∫ x, g x * h x)) := by
  obtain ⟨C, hC⟩ := h1 r hr c hc K hK
  set d : ℕ → Coord → ℂ := fun n x => a n x - g x with hd
  have he : Tendsto (fun n => eLpNorm (d n) 1 (volume.restrict K)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal C * cylNorm c r (d n)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hT (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le)
      (fun n => hC (d n) (hper n) (hmeas n))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M := by
    have hcs : HasCompactSupport h := HasCompactSupport.intro hK hhK
    obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hh
    exact ⟨M, hM⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hah : ∀ n, Integrable (fun x => a n x * h x) := fun n => by
    have hcs : HasCompactSupport (fun x => a n x * h x) :=
      HasCompactSupport.intro hK (fun x hx => by simp [hhK x hx])
    exact ((ha n).mul hh).integrable_of_hasCompactSupport hcs
  -- integrability of d n on K once its L¹ norm is finite
  have hdint : ∀ n, eLpNorm (d n) 1 (volume.restrict K) < ⊤ →
      Integrable (fun x => d n x * h x) ∧
      ‖∫ x, d n x * h x‖ ≤ M * (eLpNorm (d n) 1 (volume.restrict K)).toReal := by
    intro n hn
    have hdK : Integrable (d n) (volume.restrict K) :=
      memLp_one_iff_integrable.1 ⟨(hmeas n).restrict, hn⟩
    have hdh : Integrable (fun x => d n x * h x) (volume.restrict K) :=
      hdK.mul_bdd (hh.aestronglyMeasurable.restrict) (c := M) (Filter.Eventually.of_forall hM)
    have hsupp : Integrable (fun x => d n x * h x) := by
      rwa [← integrableOn_iff_integrable_of_support_subset (s := K)]
      intro x hx
      by_contra hxK
      exact hx (by simp [hhK x hxK])
    refine ⟨hsupp, ?_⟩
    have hEq : ∫ x, d n x * h x = ∫ x in K, d n x * h x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hhK x hx])).symm
    rw [hEq]
    have hint : Integrable (fun x => M * ‖d n x‖) (volume.restrict K) := hdK.norm.const_mul M
    refine (norm_integral_le_of_norm_le hint ?_).trans ?_
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _) |>.trans_eq (mul_comm _ _)
    · rw [integral_const_mul, integral_norm_eq_lintegral_enorm (hmeas n).restrict,
        eLpNorm_one_eq_lintegral_enorm]
  obtain ⟨N, hN⟩ := (he.eventually (gt_mem_nhds (ENNReal.zero_lt_top))).exists
  have hgh : Integrable (fun x => g x * h x) := by
    have := (hah N).sub (hdint N hN).1
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hd, Pi.sub_apply]; ring
  refine ⟨hgh, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => M * (eLpNorm (d n) 1 (volume.restrict K)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he
    simpa using this.const_mul M
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [he.eventually (gt_mem_nhds (ENNReal.zero_lt_top))] with n hn
  obtain ⟨hi, hb⟩ := hdint n hn
  have : (∫ x, a n x * h x) - ∫ x, g x * h x = ∫ x, d n x * h x := by
    rw [← integral_sub (hah n) hgh]
    congr 1; funext x; simp only [hd]; ring
  rw [this]; exact hb

theorem cgiLimitWeak_of (h1 : CgiLocalL1) (h2 : CgiIBP) : CgiLimitWeak := by
  intro r hr c hc u D2 w hw hup hum D1 hD1 hT i φ hφ
  have hK : IsCompact (tsupport φ) := hφ.compact
  have hwc : ∀ n, ContDiff ℝ ∞ (w n) := fun n => (hw.1 n).smooth
  -- the u-part
  have hA := cgi_conv (c := c) (r := r) hr hc h1 hK w u (fun x => (cpd i.succ φ x : ℂ))
    (by
      have : Continuous (cpd i.succ φ) := by
        unfold cpd
        exact (hφ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
      fun_prop)
    (fun x hx => by
      have : cpd i.succ φ x = 0 := by
        unfold cpd; rw [fderiv_of_notMem_tsupport ℝ hx]; rfl
      simp [this])
    (fun n => (hwc n).continuous)
    (fun n => by
      filter_upwards [hup] with x hx
      show w n (qShift c x) - u (qShift c x) = w n x - u x
      rw [(hw.1 n).periodic x, hx])
    (fun n => ((hwc n).continuous.aestronglyMeasurable).sub hum)
    hw.2.1
  -- the D1-part
  have hB := cgi_conv (c := c) (r := r) hr hc h1 hK (fun n => cdv i.succ (w n)) (D1 i)
    (fun x => (φ x : ℂ)) (by have := hφ.smooth.continuous; fun_prop)
    (fun x hx => by
      have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this])
    (fun n => by
      unfold cdv
      exact ((hwc n).continuous_fderiv (by simp)).clm_apply continuous_const)
    (fun n => by
      filter_upwards [(hD1 i).1] with x hx
      show cdv i.succ (w n) (qShift c x) - D1 i (qShift c x) = cdv i.succ (w n) x - D1 i x
      rw [cdv_qShift (hw.1 n).periodic, hx])
    (fun n => (((hwc n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.sub
      (hD1 i).2)
    (hT i)
  have hneg : Tendsto (fun n => ∫ x, w n x * (cpd i.succ φ x : ℂ)) atTop
      (𝓝 (-∫ x, D1 i x * (φ x : ℂ))) := by
    have := hB.2.neg
    refine this.congr (fun n => ?_)
    exact (h2 (w n) (hwc n) i φ hφ).symm
  exact tendsto_nhds_unique hA.2 hneg

end UnforcedLeray.Short.IIb
