import UnforcedLeray.Lib.LerayLp.Transfer

/-!
# The Riesz pairs `R_iR_k` as Calderón–Zygmund convolution operators (INF01 T13, part 1)

Blueprint: INF01 target T13 (`rieszPair_isCZConvolution`) of

(decision D5 of `scoping/README.md` §3). Manuscript: the Riesz-transform bound behind the
`L^q` boundedness of the Leray projection, `1 < q < ∞` (unit B0414, `paper/main.tex`
lines 7336–7344, citing Grafakos Cor. 5.2.8), for `R_iR_k = ∂_i∂_k(-Δ)^{-1}` with kernel
`K_ik = ∂_i∂_kN = (3xᵢxₖ - δᵢₖ|x|²)/(4π|x|⁵)` (lines 107–111).

The scalar operator `rieszPairL2 i k` of `Lib/CZL2` is transported to `Fin 3 → ℝ`
(`rieszFin i k`, kernel `rieszKernelFin i k = K_ik ∘ toLp`), where the Calderón–Zygmund core
`Lib/CZCore` applies with the isotropic weight `(1,1,1)`, whose gauge is the sup norm.

* `abs_newtonHessianKernel_sub_le_of_lt`: if `8|y| < 7|x|` (Euclidean norms), then
  `|K_ik(x - y) - K_ik(x)| ≤ 28672 π⁻¹ |y| |x|⁻⁴` (mean value theorem; this is the smoothness
  bound in the form needed for sup-norm balls, since `2|y|_∞ < |x|_∞` implies `8|y| < 7|x|`).
* `hormander_rieszKernelFin`: the Hörmander condition over sup-norm balls.
* `rieszFin_isCZConvolution` (**T13**): `rieszFin i k` is a Calderón–Zygmund convolution operator
  with kernel `rieszKernelFin i k` (size, Hörmander, off-support representation).
* `integral_rieszFin_mul`: `rieszFin k i` is the transpose of `rieszFin i k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

/-- The smoothness estimate for `K_ik` when `8|y| < 7|x|`:
`|K_ik(x - y) - K_ik(x)| ≤ 28672 π⁻¹ |y| |x|⁻⁴` (mean value theorem on the segment, where
`|z| ≥ |x|/8`, and `|DK_ik(z)| ≤ 7π⁻¹|z|⁻⁴`). -/
theorem abs_newtonHessianKernel_sub_le_of_lt (i k : Fin 3) {x y : Space}
    (h : 8 * ‖y‖ < 7 * ‖x‖) :
    |newtonHessianKernel i k (x - y) - newtonHessianKernel i k x| ≤
      28672 * Real.pi⁻¹ * ‖y‖ * (‖x‖ ^ 4)⁻¹ := by
  have hx : 0 < ‖x‖ := by nlinarith [norm_nonneg y]
  have hseg : ∀ z ∈ segment ℝ x (x - y), ‖x‖ / 8 ≤ ‖z‖ := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have he : a • x + b • (x - y) = x - b • y := by
      rw [smul_sub, ← add_sub_assoc, ← add_smul, hab, one_smul]
    have hb1 : b ≤ 1 := by linarith
    have hby : ‖b • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hb]
      exact mul_le_of_le_one_left (norm_nonneg y) hb1
    rw [he]
    have := norm_sub_norm_le x (b • y)
    linarith
  have hz0 : ∀ z ∈ segment ℝ x (x - y), z ≠ 0 := fun z hz =>
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hseg z hz))
  have hdiff : ∀ z ∈ segment ℝ x (x - y), DifferentiableAt ℝ (newtonHessianKernel i k) z := by
    intro z hz
    obtain ⟨L, hL, -⟩ := exists_hasFDerivAt_newtonHessianKernel i k (hz0 z hz)
    exact hL.differentiableAt
  have hbound : ∀ z ∈ segment ℝ x (x - y),
      ‖fderiv ℝ (newtonHessianKernel i k) z‖ ≤ 28672 * Real.pi⁻¹ * (‖x‖ ^ 4)⁻¹ := by
    intro z hz
    obtain ⟨L, hL, hLb⟩ := exists_hasFDerivAt_newtonHessianKernel i k (hz0 z hz)
    rw [hL.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [Real.norm_eq_abs]
    refine (hLb v).trans ?_
    have hzx := hseg z hz
    have h4 : (‖z‖ ^ 4)⁻¹ ≤ 4096 * (‖x‖ ^ 4)⁻¹ := by
      have e : (4096 : ℝ) * (‖x‖ ^ 4)⁻¹ = ((‖x‖ / 8) ^ 4)⁻¹ := by
        field_simp
        norm_num
      rw [e]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hzx 4)
    calc 7 * Real.pi⁻¹ * ‖v‖ * (‖z‖ ^ 4)⁻¹
        ≤ 7 * Real.pi⁻¹ * ‖v‖ * (4096 * (‖x‖ ^ 4)⁻¹) := by gcongr
      _ = 28672 * Real.pi⁻¹ * (‖x‖ ^ 4)⁻¹ * ‖v‖ := by ring
  have hmv := (convex_segment x (x - y)).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (left_mem_segment ℝ x (x - y)) (right_mem_segment ℝ x (x - y))
  rw [Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] at hmv
  exact hmv.trans (le_of_eq (by ring))

/-- `toLp 2 : (Fin 3 → ℝ) → Space` is a measurable embedding. -/
theorem measurableEmbedding_toLp :
    MeasurableEmbedding (WithLp.toLp 2 : (Fin 3 → ℝ) → Space) := by
  have h := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  rwa [MeasurableEquiv.coe_toLp] at h

theorem continuous_toLp' : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space) :=
  PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)

/-- The kernel `K_ik ∘ toLp` on `Fin 3 → ℝ`. -/
def rieszKernelFin (i k : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  newtonHessianKernel i k (WithLp.toLp 2 x)

/-- The Riesz pair `R_iR_k` transported to `L²(Fin 3 → ℝ)`. -/
def rieszFin (i k : Fin 3) :
    Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
  (toFinLp 2).comp ((rieszPairL2 i k).comp (ofFinLp 2))

theorem rieszFin_apply (i k : Fin 3) (f : Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) :
    rieszFin i k f = toFinLp 2 (rieszPairL2 i k (ofFinLp 2 f)) := rfl

theorem measurable_rieszKernelFin (i k : Fin 3) : Measurable (rieszKernelFin i k) :=
  (newtonHessianKernel_measurable i k).comp continuous_toLp'.measurable

/-- Size bound in the sup-norm gauge: `|K_ik(x)| ≤ π⁻¹ |x|_∞⁻³` for `x ≠ 0`. -/
theorem abs_rieszKernelFin_le (i k : Fin 3) {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    |rieszKernelFin i k x| ≤
      Real.pi⁻¹ * CZ.anisoNorm isoWeight x ^ (-(CZ.homDim isoWeight : ℝ)) := by
  rw [homDim_isoWeight]
  have hpos : 0 < CZ.anisoNorm isoWeight x := CZ.anisoNorm_pos isoWeight hx
  refine (norm_newtonHessianKernel_le i k _).trans ?_
  have h := Real.rpow_le_rpow_of_nonpos hpos (anisoNorm_iso_le_norm x)
    (by norm_num : (-3 : ℝ) ≤ 0)
  have e : (-((3 : ℕ) : ℝ)) = (-3 : ℝ) := by norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- The Hörmander constant `75264 π⁻¹ |B₁|`. -/
def hormanderConstFin : ℝ := 75264 * Real.pi⁻¹ * volume.real (Metric.ball (0 : Space) 1)

theorem hormanderConstFin_nonneg : 0 ≤ hormanderConstFin := by
  unfold hormanderConstFin
  have : 0 ≤ volume.real (Metric.ball (0 : Space) 1) := measureReal_nonneg
  positivity

/-- **Hörmander condition over sup-norm balls.** For every `y`,
`∫_{|x|_∞ > 2|y|_∞} |K_ik(x - y) - K_ik(x)| dx ≤ 75264 π⁻¹ |B₁|`. -/
theorem hormander_rieszKernelFin (i k : Fin 3) (y : Fin 3 → ℝ) :
    ∫⁻ x in {x | 2 * CZ.anisoNorm isoWeight y < CZ.anisoNorm isoWeight x},
      ‖rieszKernelFin i k (x - y) - rieszKernelFin i k x‖ₑ ≤
        ENNReal.ofReal hormanderConstFin := by
  by_cases hy : y = 0
  · subst hy
    simp
  set Y : Space := WithLp.toLp 2 y with hYdef
  have hY0 : Y ≠ 0 := by
    intro h
    apply hy
    have : WithLp.toLp 2 y = WithLp.toLp 2 (0 : Fin 3 → ℝ) := by rw [← hYdef, h]; rfl
    exact WithLp.toLp_injective 2 this
  have hY : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
  set V := volume.real (Metric.ball (0 : Space) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  set r : ℝ := 8 * ‖Y‖ / 7 with hr
  have hr0 : 0 < r := by positivity
  have hmeas : Measurable fun z : Space => ENNReal.ofReal ((‖z‖ ^ 4)⁻¹) :=
    ((measurable_norm.pow_const 4).inv).ennreal_ofReal
  have hkey : ∀ x ∈ {x | 2 * CZ.anisoNorm isoWeight y < CZ.anisoNorm isoWeight x},
      8 * ‖Y‖ < 7 * ‖(WithLp.toLp 2 x : Space)‖ := by
    intro x hx
    have hx' : 2 * CZ.anisoNorm isoWeight y < CZ.anisoNorm isoWeight x := hx
    have h1 := norm_sq_le_three_mul_anisoNorm_iso y
    have h2 := anisoNorm_iso_le_norm x
    have h3 := CZ.anisoNorm_nonneg isoWeight y
    have h4 : (2 * CZ.anisoNorm isoWeight y) ^ 2 < CZ.anisoNorm isoWeight x ^ 2 :=
      pow_lt_pow_left₀ hx' (by positivity) (by norm_num)
    have h5 : CZ.anisoNorm isoWeight x ^ 2 ≤ ‖(WithLp.toLp 2 x : Space)‖ ^ 2 :=
      pow_le_pow_left₀ (CZ.anisoNorm_nonneg _ _) h2 2
    have h6 : (8 * ‖Y‖) ^ 2 < (7 * ‖(WithLp.toLp 2 x : Space)‖) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h6
  calc ∫⁻ x in {x | 2 * CZ.anisoNorm isoWeight y < CZ.anisoNorm isoWeight x},
        ‖rieszKernelFin i k (x - y) - rieszKernelFin i k x‖ₑ
      ≤ ∫⁻ x in {x | 2 * CZ.anisoNorm isoWeight y < CZ.anisoNorm isoWeight x},
          ENNReal.ofReal (28672 * Real.pi⁻¹ * ‖Y‖) *
            ENNReal.ofReal ((‖(WithLp.toLp 2 x : Space)‖ ^ 4)⁻¹) := by
        refine setLIntegral_mono (measurable_const.mul (hmeas.comp continuous_toLp'.measurable))
          fun x hx => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := abs_newtonHessianKernel_sub_le_of_lt i k (hkey x hx)
        simpa [rieszKernelFin, WithLp.toLp_sub, hYdef] using this
    _ ≤ ∫⁻ x in (WithLp.toLp 2 : (Fin 3 → ℝ) → Space) ⁻¹' {z : Space | r < ‖z‖},
          ENNReal.ofReal (28672 * Real.pi⁻¹ * ‖Y‖) *
            ENNReal.ofReal ((‖(WithLp.toLp 2 x : Space)‖ ^ 4)⁻¹) := by
        refine lintegral_mono_set fun x hx => ?_
        have := hkey x hx
        change r < ‖(WithLp.toLp 2 x : Space)‖
        rw [hr]
        linarith
    _ = ∫⁻ z in {z : Space | r < ‖z‖},
          ENNReal.ofReal (28672 * Real.pi⁻¹ * ‖Y‖) * ENNReal.ofReal ((‖z‖ ^ 4)⁻¹) :=
        mp_toLp.setLIntegral_comp_preimage (measurableSet_lt measurable_const measurable_norm)
          (measurable_const.mul hmeas)
    _ = ENNReal.ofReal (28672 * Real.pi⁻¹ * ‖Y‖) * ENNReal.ofReal (3 * V * r⁻¹) := by
        rw [lintegral_const_mul _ hmeas, lintegral_norm_inv_pow_four hr0]
    _ = ENNReal.ofReal hormanderConstFin := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hormanderConstFin, hr]
        field_simp
        ring

/-- **Off-support kernel formula on `Fin 3 → ℝ`.** If `f ∈ L²` vanishes a.e. outside a compact
set `S`, then for a.e. `x ∉ S`, `(rieszFin i k f)(x) = ∫ K_ik(toLp (x - y)) f(y) dy`. -/
theorem rieszFin_offSupport (i k : Fin 3) (f : Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)))
    (S : Set (Fin 3 → ℝ)) (hS : IsCompact S) (hf : ∀ᵐ y ∂volume, y ∉ S → f y = 0) :
    ∀ᵐ x ∂volume, x ∉ S → rieszFin i k f x = ∫ y, rieszKernelFin i k (x - y) * f y := by
  set g := ofFinLp 2 f with hgdef
  set S' : Set Space := WithLp.toLp 2 '' S with hS'def
  have hS' : IsCompact S' := hS.image continuous_toLp'
  have hg : ∀ᵐ z ∂volume, z ∉ S' → g z = 0 := by
    have h1 : ∀ᵐ z : Space ∂volume, (WithLp.ofLp z ∉ S → f (WithLp.ofLp z) = 0) :=
      mp_ofLp.quasiMeasurePreserving.ae hf
    filter_upwards [coeFn_ofFinLp 2 f, h1] with z hz h1 hzS
    rw [hz]
    apply h1
    intro hmem
    exact hzS ⟨_, hmem, by simp⟩
  have hR := rieszPairL2_offSupport i k g hS' hg
  have hR' : ∀ᵐ x : Fin 3 → ℝ ∂volume, (WithLp.toLp 2 x ∉ S' →
      rieszPairL2 i k g (WithLp.toLp 2 x) =
        ∫ w, newtonHessianKernel i k (WithLp.toLp 2 x - w) * g w) :=
    mp_toLp.quasiMeasurePreserving.ae hR
  filter_upwards [coeFn_toFinLp 2 (rieszPairL2 i k g), hR'] with x hx hR' hxS
  have hxS' : WithLp.toLp 2 x ∉ S' := by
    rintro ⟨s, hs, hsx⟩
    have : s = x := WithLp.toLp_injective 2 hsx
    exact hxS (this ▸ hs)
  rw [rieszFin_apply, hx, hR' hxS']
  have h1 : (fun w => newtonHessianKernel i k (WithLp.toLp 2 x - w) * g w) =ᵐ[volume]
      fun w => newtonHessianKernel i k (WithLp.toLp 2 x - w) * f (WithLp.ofLp w) := by
    filter_upwards [coeFn_ofFinLp 2 f] with w hw
    rw [hw]
  rw [integral_congr_ae h1]
  rw [← mp_toLp.integral_comp measurableEmbedding_toLp]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [rieszKernelFin, WithLp.toLp_sub]

/-- `rieszFin k i` is the transpose of `rieszFin i k`. -/
theorem integral_rieszFin_mul (i k : Fin 3) (f g : Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) :
    ∫ x, rieszFin i k f x * g x = ∫ x, f x * rieszFin k i g x := by
  have e1 : ∫ x, rieszFin i k f x * g x = inner ℝ g (rieszFin i k f) := by
    rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.inner_apply]
    ring
  have e2 : ∫ x, f x * rieszFin k i g x = inner ℝ (rieszFin k i g) f := by
    rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.inner_apply]
    ring
  rw [e1, e2]
  calc inner ℝ g (rieszFin i k f)
      = inner ℝ (toFinLp 2 (ofFinLp 2 g)) (toFinLp 2 (rieszPairL2 i k (ofFinLp 2 f))) := by
        rw [toFinLp_ofFinLp, rieszFin_apply]
    _ = inner ℝ (ofFinLp 2 g) (rieszPairL2 i k (ofFinLp 2 f)) := inner_toFinLp_two _ _
    _ = inner ℝ (rieszPairL2 k i (ofFinLp 2 g)) (ofFinLp 2 f) := inner_rieszPairL2 i k _ _
    _ = inner ℝ (toFinLp 2 (rieszPairL2 k i (ofFinLp 2 g))) (toFinLp 2 (ofFinLp 2 f)) :=
        (inner_toFinLp_two _ _).symm
    _ = inner ℝ (rieszFin k i g) f := by rw [toFinLp_ofFinLp, rieszFin_apply]

/-- The Calderón–Zygmund constant of the Riesz pairs on `Fin 3 → ℝ`:
`max(size, Hörmander) ≤ π⁻¹ + 75264 π⁻¹ |B₁|`. -/
def rieszCZConst : ℝ≥0 := Real.toNNReal (Real.pi⁻¹ + hormanderConstFin)

/-- **INF01 T13.** The transported Riesz pair `rieszFin i k` is a Calderón–Zygmund convolution
operator for the isotropic weight `(1,1,1)`, with kernel `K_ik ∘ toLp` and constant
`rieszCZConst`. -/
theorem rieszFin_isCZConvolution (i k : Fin 3) :
    CZ.IsCZConvolution isoWeight (rieszFin i k) (rieszKernelFin i k) rieszCZConst where
  measurable := measurable_rieszKernelFin i k
  size := by
    intro x hx
    refine (abs_rieszKernelFin_le i k hx).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (CZ.anisoNorm_nonneg _ _) _)
    rw [rieszCZConst, Real.coe_toNNReal _ (by
      have := hormanderConstFin_nonneg; positivity)]
    linarith [hormanderConstFin_nonneg]
  hormander := by
    intro y
    refine (hormander_rieszKernelFin i k y).trans ?_
    change ENNReal.ofReal hormanderConstFin ≤ ENNReal.ofReal (Real.pi⁻¹ + hormanderConstFin)
    exact ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ Real.pi⁻¹ := by positivity
      linarith)
  offSupport := fun f S hS hf => rieszFin_offSupport i k f S hS hf

end UnforcedLeray.RieszLp
