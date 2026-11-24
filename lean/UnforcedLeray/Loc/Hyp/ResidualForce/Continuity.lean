import UnforcedLeray.Loc.Hyp.ResidualForce.Product
import UnforcedLeray.Loc.L09CompactDatum.Defect

/-!
# `H-Residual`, helpers: continuity in the phase `τ`

Support for `Loc/Hyp/ResidualForce.lean` (`paper/main.tex` lines 474–491, blueprint B0722).
The manuscript leaves the continuity of `G_*` in `τ` implicit (blueprint note on B0722); here it
is proved for the residual part.

* `continuousOn_toL2`: dominated convergence in `L²` with the fixed majorant `A(1 + |y|)^{-2}`.
* `continuous_kconv_param`: dominated convergence for kernel convolutions
  `∫ B(K(y - z), g_τ(z)) dz`, when `|g_τ(z)| ≤ C|z|^{-1}` uniformly in `τ`.
* `heatProfile_continuity`: for `v` continuous off zero with `|v(x)| ≤ C|x|^{-1}`, the heat
  profile `H_h[v](τ) = e^{hΔ}[e^{τ/2}v(e^{τ/2}·)]` (`Heat.simHeat_eq`, the identity of B0697) and
  its first and second coordinate derivatives at a fixed point are continuous in `τ`: the kernel
  `G_h` is fixed and the data `e^{τ/2}v(e^{τ/2}z)` depend continuously on `τ` for `z ≠ 0`, with
  the scale-invariant bound `C|z|^{-1}`.

Main declarations: `continuousOn_toL2`, `continuous_kconv_param`, `InvBound`,
`heatProfile_continuity`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.ResidualForceHyp

open UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L10

/-! ## `L²` continuity by dominated convergence -/

theorem toL2_sub' {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 f - toL2 g = toL2 (f - g) := by
  rw [toL2_of_memLp hf, toL2_of_memLp hg, toL2_of_memLp (hf.sub hg)]
  exact (hf.toLp_sub hg).symm

theorem memLp_of_bound {f : SpatialField} (hm : AEStronglyMeasurable f volume) {A : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ A / (1 + ‖y‖) ^ 2) : MemLp f 2 volume := by
  refine (memLp_l2Norm_le_of_sq hm ((integrable_inv_pow (n := 4) (by norm_num)).const_mul (A ^ 2))
    (fun y => ?_)).1
  have h0 := hb y
  have h1 := pow_le_pow_left₀ (norm_nonneg _) h0 2
  calc ‖f y‖ ^ 2 ≤ (A / (1 + ‖y‖) ^ 2) ^ 2 := h1
    _ = A ^ 2 * (1 / (1 + ‖y‖) ^ 4) := by field_simp

/-- **Dominated convergence in `L²`.** A family of fields, measurable and dominated by
`A(1 + |y|)^{-2}` on `s`, and pointwise continuous on `s`, is continuous on `s` in `L²`. -/
theorem continuousOn_toL2 {f : ℝ → SpatialField} {s : Set ℝ} {A : ℝ}
    (hm : ∀ τ ∈ s, AEStronglyMeasurable (f τ) volume)
    (hb : ∀ τ ∈ s, ∀ y, ‖f τ y‖ ≤ A / (1 + ‖y‖) ^ 2)
    (hc : ∀ y, ContinuousOn (fun τ => f τ y) s) :
    ContinuousOn (fun τ => toL2 (f τ)) s := by
  have hint4 := integrable_inv_pow (n := 4) (by norm_num)
  intro τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hdiff : ∀ τ ∈ s, ∀ y, ‖f τ y - f τ₀ y‖ ^ 2 ≤ (2 * A) ^ 2 * (1 / (1 + ‖y‖) ^ 4) := by
    intro τ hτ y
    have h1 := hb τ hτ y
    have h2 := hb τ₀ hτ₀ y
    have h3 : ‖f τ y - f τ₀ y‖ ≤ 2 * A / (1 + ‖y‖) ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have : 2 * A / (1 + ‖y‖) ^ 2 = A / (1 + ‖y‖) ^ 2 + A / (1 + ‖y‖) ^ 2 := by ring
      linarith
    calc ‖f τ y - f τ₀ y‖ ^ 2 ≤ (2 * A / (1 + ‖y‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = (2 * A) ^ 2 * (1 / (1 + ‖y‖) ^ 4) := by field_simp
  set I : ℝ → ℝ := fun τ => ∫ y, ‖f τ y - f τ₀ y‖ ^ 2 with hI
  have hlim : Tendsto I (𝓝[s] τ₀) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[s] τ₀)
      (F := fun τ y => ‖f τ y - f τ₀ y‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun y => (2 * A) ^ 2 * (1 / (1 + ‖y‖) ^ 4))
      (by
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact ((hm τ hτ).sub (hm τ₀ hτ₀)).norm.pow 2)
      (by
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        refine Eventually.of_forall fun y => ?_
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hdiff τ hτ y)
      (hint4.const_mul _)
      (Eventually.of_forall fun y => by
        have h1 : Tendsto (fun τ => f τ y) (𝓝[s] τ₀) (𝓝 (f τ₀ y)) := hc y τ₀ hτ₀
        have h2 : Tendsto (fun τ => ‖f τ y - f τ₀ y‖ ^ 2) (𝓝[s] τ₀)
            (𝓝 (‖f τ₀ y - f τ₀ y‖ ^ 2)) :=
          ((h1.sub tendsto_const_nhds).norm).pow 2
        simpa using h2)
    simpa using h
  have hsq : Tendsto (fun τ => Real.sqrt (I τ)) (𝓝[s] τ₀) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rwa [Real.sqrt_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun τ => norm_nonneg _) ?_ hsq
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hmτ := memLp_of_bound (hm τ hτ) (hb τ hτ)
  have hm0 := memLp_of_bound (hm τ₀ hτ₀) (hb τ₀ hτ₀)
  rw [toL2_sub' hmτ hm0, norm_toL2 (hmτ.sub hm0)]
  have hg : Integrable (fun y => ‖f τ y - f τ₀ y‖ ^ 2) :=
    (hint4.const_mul ((2 * A) ^ 2)).mono' (((hm τ hτ).sub (hm τ₀ hτ₀)).norm.pow 2)
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hdiff τ hτ y)
  exact (memLp_l2Norm_le_of_sq ((hm τ hτ).sub (hm τ₀ hτ₀)) hg (fun y => le_rfl)).2

/-! ## Kernel convolutions with a continuous family of `|z|^{-1}` data -/

/-- **Dominated convergence for kernel convolutions.** -/
theorem continuous_kconv_param {V W' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] [CompleteSpace W']
    (B : V →L[ℝ] Space →L[ℝ] W') {K : Space → V} {m : ℝ} (hm : 0 ≤ m) (hKc : Continuous K)
    {CK : ℝ} (hCK : ∀ z, ‖K z‖ ≤ CK * (1 + ‖z‖) ^ (-m))
    (g : ℝ → Space → Space) (hgm : ∀ τ, AEStronglyMeasurable (g τ) volume) {Cg : ℝ}
    (hgb : ∀ τ z, z ≠ 0 → ‖g τ z‖ ≤ Cg * ‖z‖⁻¹) (hgc : ∀ z, z ≠ 0 → Continuous fun τ => g τ z)
    (hint : Integrable fun z : Space => (1 + ‖z‖) ^ (-m) * ‖z‖⁻¹) (y : Space) :
    Continuous fun τ => Heat.kconv B K (g τ) y := by
  unfold Heat.kconv
  have hae : ∀ᵐ z : Space ∂volume, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  have hCK0 : 0 ≤ CK := by
    have := (norm_nonneg _).trans (hCK 0)
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos (by positivity) _)
  set c := ‖B‖ * CK * (1 + ‖y‖) ^ m with hc
  have hc0 : 0 ≤ c := by positivity
  refine continuous_of_dominated
    (bound := fun z => c * ((1 + ‖z‖) ^ (-m) * (Cg * ‖z‖⁻¹))) (fun τ => ?_) (fun τ => ?_) ?_ ?_
  · exact B.aestronglyMeasurable_comp₂
      (hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable (hgm τ)
  · filter_upwards [hae] with z hz
    refine (Heat.norm_kconv_integrand_le B hm hCK (g τ) y z).trans ?_
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgb τ z hz)
      (Real.rpow_nonneg (by positivity) _)) hc0
  · refine (hint.const_mul (c * Cg)).congr (Eventually.of_forall fun z => ?_)
    simp only
    ring
  · filter_upwards [hae] with z hz
    exact (B (K (y - z))).continuous.comp (hgc z hz)

/-! ## The heat profile of a `|x|^{-1}` field, as a function of the phase -/

/-- `v` is continuous off zero with `|v(x)| ≤ C|x|^{-1}`. -/
structure InvBound (v : SpatialField) (C : ℝ) : Prop where
  cont : ContinuousOn v {0}ᶜ
  bound : ∀ x : Space, x ≠ 0 → ‖v x‖ ≤ C * ‖x‖⁻¹

/-- `v_τ(y) = e^{τ/2} v(e^{τ/2} y)`. -/
def dil (v : SpatialField) (τ : ℝ) : SpatialField :=
  fun y => Real.exp (τ / 2) • v (Real.exp (τ / 2) • y)

theorem heatProfile_eq_kconv {h : ℝ} (hh : 0 < h) (v : SpatialField) (τ : ℝ) :
    heatProfile h v τ =
      Heat.kconv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space) (Heat.kernel h)
        (dil v τ) := by
  rw [show heatProfile h v τ = Heat.simHeat h v τ from rfl, Heat.simHeat_eq hh,
    Heat.average_eq_kconv]
  rfl

section InvBound

variable {v : SpatialField} {C : ℝ}

theorem InvBound.dil_bound (hv : InvBound v C) (τ : ℝ) (z : Space) (hz : z ≠ 0) :
    ‖dil v τ z‖ ≤ C * ‖z‖⁻¹ := by
  have he := Real.exp_pos (τ / 2)
  have hz' : Real.exp (τ / 2) • z ≠ 0 := smul_ne_zero he.ne' hz
  unfold dil
  rw [norm_smul, Real.norm_of_nonneg he.le]
  have h := hv.bound _ hz'
  rw [norm_smul, Real.norm_of_nonneg he.le, mul_inv] at h
  calc Real.exp (τ / 2) * ‖v (Real.exp (τ / 2) • z)‖
      ≤ Real.exp (τ / 2) * (C * ((Real.exp (τ / 2))⁻¹ * ‖z‖⁻¹)) :=
        mul_le_mul_of_nonneg_left h he.le
    _ = C * ‖z‖⁻¹ := by field_simp

theorem InvBound.dil_continuous (hv : InvBound v C) (z : Space) (hz : z ≠ 0) :
    Continuous fun τ => dil v τ z := by
  unfold dil
  have he : Continuous fun τ : ℝ => Real.exp (τ / 2) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  have hc : Continuous fun τ : ℝ => Real.exp (τ / 2) • z :=
    he.smul (continuous_const : Continuous fun _ : ℝ => z)
  refine he.smul ?_
  refine hv.cont.comp_continuous hc (fun τ => ?_)
  exact smul_ne_zero (Real.exp_pos _).ne' hz

theorem InvBound.dil_aesm (hv : InvBound v C) (τ : ℝ) :
    AEStronglyMeasurable (dil v τ) volume := by
  refine L09.aestronglyMeasurable_of_continuousOn_compl_zero ?_
  unfold dil
  have hs : ContinuousOn (fun y : Space => v (Real.exp (τ / 2) • y)) {0}ᶜ :=
    hv.cont.comp (continuous_const_smul (Real.exp (τ / 2))).continuousOn
      (fun y hy => smul_ne_zero (Real.exp_pos _).ne' hy)
  exact hs.const_smul (Real.exp (τ / 2))

theorem InvBound.aesm (hv : InvBound v C) : AEStronglyMeasurable v volume :=
  L09.aestronglyMeasurable_of_continuousOn_compl_zero hv.cont

theorem InvBound.heatAdmissible (hv : InvBound v C) : Heat.HeatAdmissible v :=
  Heat.HeatAdmissible.of_inv_bound hv.aesm hv.bound

end InvBound

/-- An exponent `m` with `(1 + |z|)^{-m}|z|^{-1} ∈ L¹(ℝ³)`. -/
theorem exists_inv_weight :
    ∃ m : ℕ, Integrable fun z : Space => (1 + ‖z‖) ^ (-(m : ℝ)) * ‖z‖⁻¹ := by
  obtain ⟨-, m, hm⟩ := Heat.HeatAdmissible.of_inv_bound (E := ℝ)
    (f := fun z : Space => ‖z‖⁻¹) (measurable_norm.inv.aestronglyMeasurable) (C := 1)
    (fun x _ => by rw [one_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))])
  exact ⟨m, hm.congr (Eventually.of_forall fun z => by simp only [smul_eq_mul])⟩

/-- **Phase continuity of the heat profile and its derivatives.** -/
theorem heatProfile_continuity {h : ℝ} (hh : 0 < h) {v : SpatialField} {C : ℝ}
    (hv : InvBound v C) (y : Space) (i l : Fin 3) :
    Continuous (fun τ => heatProfile h v τ y) ∧
    Continuous (fun τ => dpart (heatProfile h v τ) i y) ∧
    Continuous (fun τ => dpart (dpart (heatProfile h v τ) i) l y) := by
  obtain ⟨m, hm⟩ := exists_inv_weight
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hG := Heat.decayKernel_gaussKernel hh hm0
  have hG1 := hG.fderiv
  have hG2 := hG1.fderiv
  obtain ⟨C0, hC0⟩ := hG.norm_le
  obtain ⟨C1, hC1⟩ := hG1.norm_le
  obtain ⟨C2, hC2⟩ := hG2.norm_le
  have hgi : ∀ τ, Integrable (fun z : Space => (1 + ‖z‖) ^ (-(m : ℝ)) * ‖dil v τ z‖) := by
    intro τ
    refine (hm.const_mul C).mono' (((Heat.continuous_weight (m : ℝ)).aestronglyMeasurable).mul
      (hv.dil_aesm τ).norm) ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))]
    calc (1 + ‖z‖) ^ (-(m : ℝ)) * ‖dil v τ z‖ ≤ (1 + ‖z‖) ^ (-(m : ℝ)) * (C * ‖z‖⁻¹) :=
          mul_le_mul_of_nonneg_left (hv.dil_bound τ z hz) (Real.rpow_nonneg (by positivity) _)
      _ = C * ((1 + ‖z‖) ^ (-(m : ℝ)) * ‖z‖⁻¹) := by ring
  set B0 : ℝ →L[ℝ] Space →L[ℝ] Space := ContinuousLinearMap.lsmul ℝ ℝ with hB0
  have e0 : ∀ τ, heatProfile h v τ = Heat.kconv B0 (Heat.kernel h) (dil v τ) :=
    fun τ => heatProfile_eq_kconv hh v τ
  have e1 : ∀ τ, fderiv ℝ (heatProfile h v τ) =
      Heat.kconv (B0.precompL Space) (fderiv ℝ (Heat.kernel h)) (dil v τ) := by
    intro τ
    rw [e0 τ]
    exact Heat.fderiv_kconv B0 hm0 hG (hv.dil_aesm τ) (hgi τ)
  have e2 : ∀ τ, fderiv ℝ (fderiv ℝ (heatProfile h v τ)) =
      Heat.kconv ((B0.precompL Space).precompL Space) (fderiv ℝ (fderiv ℝ (Heat.kernel h)))
        (dil v τ) := by
    intro τ
    rw [e1 τ]
    exact Heat.fderiv_kconv (B0.precompL Space) hm0 hG1 (hv.dil_aesm τ) (hgi τ)
  have hsmooth : ∀ τ, ContDiff ℝ ∞ (heatProfile h v τ) :=
    fun τ => Heat.simHeat_contDiff hh hv.heatAdmissible τ
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [e0]
    exact continuous_kconv_param B0 hm0 hG.smooth.continuous hC0 (dil v) hv.dil_aesm
      hv.dil_bound hv.dil_continuous hm y
  · have hc := continuous_kconv_param (W' := Space →L[ℝ] Space) (B0.precompL Space) hm0 hG1.smooth.continuous hC1 (dil v)
      hv.dil_aesm hv.dil_bound hv.dil_continuous hm y
    have : (fun τ => dpart (heatProfile h v τ) i y) =
        fun τ => Heat.kconv (B0.precompL Space) (fderiv ℝ (Heat.kernel h)) (dil v τ) y
          (coordinateVector i) := by
      funext τ
      unfold dpart
      rw [e1 τ]
    rw [this]
    exact hc.clm_apply continuous_const
  · have hc := continuous_kconv_param (W' := Space →L[ℝ] Space →L[ℝ] Space)
      ((B0.precompL Space).precompL Space) hm0
      hG2.smooth.continuous hC2 (dil v) hv.dil_aesm hv.dil_bound hv.dil_continuous hm y
    have : (fun τ => dpart (dpart (heatProfile h v τ) i) l y) =
        fun τ => fderiv ℝ (fderiv ℝ (heatProfile h v τ)) y (coordinateVector l)
            (coordinateVector i) := by
      funext τ
      exact dpart_dpart_eq (hsmooth τ) i l y
    rw [this]
    simp_rw [e2]
    exact (hc.clm_apply continuous_const).clm_apply continuous_const

end UnforcedLeray.ResidualForceHyp
