import UnforcedLeray.Units.B0151.Linf
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.CompletePartialOrder

/-!
# B0151, part 5: integration by parts on the cylinder, `‖∇E‖₂ = ‖curl E‖₂`, interpolation

Blueprint unit **B0151** (`unlabeled:2291`), `paper/main.tex` lines 2291–2294 and 2310–2314:
`‖∇E‖₂ ≤ C ‖Z‖₂` for the divergence-free rescaled error `E` with `Z = curl E`, and the
interpolation constants, uniform for cylinder periods `L ≥ 1`.

On one cell `(0, L] × ℝ`, `∫ ∂_q F = 0` for `L`-periodic `F` and `∫ ∂_η G = 0` for `G` integrable
with integrable `∂_η G` (`integral_partialX_eq_zero`, `integral_partialY_eq_zero`). The Jacobian
`∂_q E₁ ∂_η E₂ − ∂_η E₁ ∂_q E₂ = ∂_q (E₁ ∂_η E₂) − ∂_η (E₁ ∂_q E₂)` therefore integrates to zero,
so `∑ ‖∂_i E_j‖₂² = ‖div E‖₂² + ‖curl E‖₂²` exactly (`gradL2Sq_eq`): the constant is `1` for
every period. Likewise `‖∂_q h‖₂² ≤ ‖h‖₂ ‖∂_q² h‖₂` and `‖∂_η h‖₂² ≤ ‖h‖₂ ‖∂_η² h‖₂`
(`interpolation_q`, `interpolation_η`), again with constant `1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.B0151

open UnforcedLeray.GaussianVortex (partialX partialY divergence curl)

theorem contDiff_partialX_two {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 1 (partialX h) :=
  contDiff_partialX (n := 1) (by rw [one_add_one_eq_two]; exact hh)

theorem contDiff_partialY_two {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 1 (partialY h) :=
  contDiff_partialY (n := 1) (by rw [one_add_one_eq_two]; exact hh)

/-- Mixed classical partial derivatives of a `C²` field commute. -/
theorem partialX_partialY_comm {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℝ × ℝ) :
    partialX (partialY f) z = partialY (partialX f) z := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [partialX_eq_fderiv ((contDiff_partialY_two hf).differentiable one_ne_zero) z,
    partialY_eq_fderiv ((contDiff_partialX_two hf).differentiable one_ne_zero) z]
  have ex : partialX f = fun z => fderiv ℝ f z (1, 0) := funext (partialX_eq_fderiv hd)
  have ey : partialY f = fun z => fderiv ℝ f z (0, 1) := funext (partialY_eq_fderiv hd)
  rw [ex, ey, fderiv_clm_apply (hdd z) (differentiableAt_const _),
    fderiv_clm_apply (hdd z) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Product rule for `∂_q`. -/
theorem partialX_mul {u v : ℝ × ℝ → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (z : ℝ × ℝ) :
    partialX (fun w => u w * v w) z = partialX u z * v z + u z * partialX v z := by
  obtain ⟨x, y⟩ := z
  exact ((hasDerivAt_sliceX hu x y).mul (hasDerivAt_sliceX hv x y)).deriv

/-- Product rule for `∂_η`. -/
theorem partialY_mul {u v : ℝ × ℝ → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (z : ℝ × ℝ) :
    partialY (fun w => u w * v w) z = partialY u z * v z + u z * partialY v z := by
  obtain ⟨x, y⟩ := z
  exact ((hasDerivAt_sliceY hu x y).mul (hasDerivAt_sliceY hv x y)).deriv

theorem IsPeriodicQ.mul {L : ℝ} {u v : ℝ × ℝ → ℝ} (hu : IsPeriodicQ L u)
    (hv : IsPeriodicQ L v) : IsPeriodicQ L (fun w => u w * v w) := fun q η => by
  simp only [hu q η, hv q η]

/-! ### Integration by parts on one cell -/

/-- `∫_cell ∂_q F = 0` for an `L`-periodic `C¹` field with integrable `∂_q F`. -/
theorem integral_partialX_eq_zero {L : ℝ} (hL : 0 < L) {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hp : IsPeriodicQ L F) (hi : Integrable (partialX F) (cellMeasure L)) :
    ∫ z, partialX F z ∂cellMeasure L = 0 := by
  have hd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hc : Continuous (partialX F) := continuous_partialX hF
  rw [cellMeasure_eq_prod] at hi ⊢
  rw [integral_prod_symm _ hi]
  have h0 : ∀ η : ℝ, ∫ s in Ioc 0 L, partialX F (s, η) = 0 := by
    intro η
    have hcs : Continuous fun s : ℝ => partialX F (s, η) :=
      hc.comp (continuous_id.prodMk continuous_const)
    rw [← intervalIntegral.integral_of_le hL.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_sliceX hd x η)
        (hcs.intervalIntegrable _ _)]
    have := hp 0 η
    rw [zero_add] at this
    rw [this, sub_self]
  simp only [h0, integral_zero]

/-- `∫_cell ∂_η G = 0` for a `C¹` field with `G` and `∂_η G` integrable on the cell. -/
theorem integral_partialY_eq_zero {L : ℝ} {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 1 G)
    (hi : Integrable G (cellMeasure L)) (hi' : Integrable (partialY G) (cellMeasure L)) :
    ∫ z, partialY G z ∂cellMeasure L = 0 := by
  have hd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have h1 := ae_integrable_slice hi
  have h2 := ae_integrable_slice hi'
  rw [cellMeasure_eq_prod] at hi' ⊢
  rw [integral_prod _ hi']
  have h0 : (fun q => ∫ η, partialY G (q, η)) =ᵐ[volume.restrict (Ioc 0 L)] fun _ => 0 := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact integral_eq_zero_of_hasDerivAt_of_integrable (fun η => hasDerivAt_sliceY hd q η)
      hq2 hq1
  rw [integral_congr_ae h0, integral_zero]

/-! ### Conversions between `L²` norms and real integrals -/

theorem integrable_mul_of_memLp_two {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun z => f z * g z) μ :=
  hf.integrable_mul hg

theorem eLpNorm_two_sq_eq {μ : Measure (ℝ × ℝ)} {g : ℝ × ℝ → ℝ} (hg : MemLp g 2 μ) :
    eLpNorm g 2 μ ^ 2 = ENNReal.ofReal (∫ z, g z ^ 2 ∂μ) := by
  rw [← lintegral_enorm_sq_eq, ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (ae_of_all _ fun z => sq_nonneg (g z))]
  refine lintegral_congr fun z => ?_
  rw [enorm_sq_eq, abs_of_nonneg (sq_nonneg _)]

theorem ofReal_integral_abs_mul_le {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ENNReal.ofReal (∫ z, |f z * g z| ∂μ) ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_mul_of_memLp_two hf hg).abs
    (ae_of_all _ fun z => abs_nonneg _)]
  refine le_trans (le_of_eq ?_) (lintegral_enorm_mul_le hf.1 hg.1)
  refine lintegral_congr fun z => ?_
  rw [← Real.enorm_eq_ofReal_abs, enorm_mul]

/-! ### The div–curl identity -/

/-- The squared `L²` norm of the full gradient of a planar vector field over one cell,
`∑_{i,j} ‖∂_i E_j‖₂²`. -/
def gradL2Sq (L : ℝ) (E : ℝ × ℝ → ℝ × ℝ) : ℝ≥0∞ :=
  eLpNorm (partialX fun z => (E z).1) 2 (cellMeasure L) ^ 2 +
    eLpNorm (partialY fun z => (E z).1) 2 (cellMeasure L) ^ 2 +
    eLpNorm (partialX fun z => (E z).2) 2 (cellMeasure L) ^ 2 +
    eLpNorm (partialY fun z => (E z).2) 2 (cellMeasure L) ^ 2

/-- The integrated Jacobian vanishes: `∫ (∂_q E₁ ∂_η E₂ − ∂_η E₁ ∂_q E₂) = 0` on one cell. -/
theorem integral_jacobian_eq_zero {L : ℝ} (hL : 0 < L) {u w : ℝ × ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hw : ContDiff ℝ 2 w) (hpu : IsPeriodicQ L u)
    (hpw : IsPeriodicQ L w) (hu2 : MemLp u 2 (cellMeasure L))
    (hux : MemLp (partialX u) 2 (cellMeasure L)) (huy : MemLp (partialY u) 2 (cellMeasure L))
    (hwx : MemLp (partialX w) 2 (cellMeasure L)) (hwy : MemLp (partialY w) 2 (cellMeasure L))
    (hwxy : MemLp (partialY (partialX w)) 2 (cellMeasure L)) :
    ∫ z, (partialX u z * partialY w z - partialY u z * partialX w z) ∂cellMeasure L = 0 := by
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  have hwx1 : ContDiff ℝ 1 (partialX w) := contDiff_partialX_two hw
  have hwy1 : ContDiff ℝ 1 (partialY w) := contDiff_partialY_two hw
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hcomm : ∀ z, partialX (partialY w) z = partialY (partialX w) z :=
    partialX_partialY_comm hw
  set P : ℝ × ℝ → ℝ := fun z => u z * partialY w z with hP
  set Q : ℝ × ℝ → ℝ := fun z => u z * partialX w z with hQ
  have ePx : ∀ z, partialX P z =
      partialX u z * partialY w z + u z * partialY (partialX w) z := fun z => by
    rw [hP, partialX_mul hud (hwy1.differentiable one_ne_zero), hcomm]
  have eQy : ∀ z, partialY Q z =
      partialY u z * partialX w z + u z * partialY (partialX w) z := fun z => by
    rw [hQ, partialY_mul hud (hwx1.differentiable one_ne_zero)]
  have iPx : Integrable (partialX P) (cellMeasure L) := by
    rw [show partialX P = _ from funext ePx]
    exact (integrable_mul_of_memLp_two hux hwy).add (integrable_mul_of_memLp_two hu2 hwxy)
  have iQy : Integrable (partialY Q) (cellMeasure L) := by
    rw [show partialY Q = _ from funext eQy]
    exact (integrable_mul_of_memLp_two huy hwx).add (integrable_mul_of_memLp_two hu2 hwxy)
  have hP0 : ∫ z, partialX P z ∂cellMeasure L = 0 :=
    integral_partialX_eq_zero hL (hu1.mul hwy1) (hpu.mul hpw.partialY) iPx
  have hQ0 : ∫ z, partialY Q z ∂cellMeasure L = 0 :=
    integral_partialY_eq_zero (hu1.mul hwx1) (integrable_mul_of_memLp_two hu2 hwx) iQy
  have e : (fun z => partialX u z * partialY w z - partialY u z * partialX w z) =
      fun z => partialX P z - partialY Q z := funext fun z => by
    rw [ePx, eQy]; ring
  rw [e, integral_sub iPx iQy, hP0, hQ0, sub_zero]

/-- **The div–curl identity on the cylinder** (B0151, tex 2310–2314): for a `C²` planar field
`E = (E₁, E₂)`, `L`-periodic in `q`, with `E₁`, the first derivatives of `E` and `∂_η ∂_q E₂`
square integrable on one cell,
`∑_{i,j} ‖∂_i E_j‖₂² = ‖div E‖₂² + ‖curl E‖₂²`. The constant is `1` for every period. -/
theorem gradL2Sq_eq {L : ℝ} (hL : 0 < L) {E : ℝ × ℝ → ℝ × ℝ} (hE : ContDiff ℝ 2 E)
    (hp : ∀ q η, E (q + L, η) = E (q, η))
    (hu2 : MemLp (fun z => (E z).1) 2 (cellMeasure L))
    (hux : MemLp (partialX fun z => (E z).1) 2 (cellMeasure L))
    (huy : MemLp (partialY fun z => (E z).1) 2 (cellMeasure L))
    (hwx : MemLp (partialX fun z => (E z).2) 2 (cellMeasure L))
    (hwy : MemLp (partialY fun z => (E z).2) 2 (cellMeasure L))
    (hwxy : MemLp (partialY (partialX fun z => (E z).2)) 2 (cellMeasure L)) :
    gradL2Sq L E = eLpNorm (divergence E) 2 (cellMeasure L) ^ 2 +
      eLpNorm (curl E) 2 (cellMeasure L) ^ 2 := by
  set u : ℝ × ℝ → ℝ := fun z => (E z).1 with hu_def
  set w : ℝ × ℝ → ℝ := fun z => (E z).2 with hw_def
  have hpu : IsPeriodicQ L u := fun q η => by simp only [hu_def, hp q η]
  have hpw : IsPeriodicQ L w := fun q η => by simp only [hw_def, hp q η]
  have hJ : ∫ z, (partialX u z * partialY w z - partialY u z * partialX w z) ∂cellMeasure L =
      0 := integral_jacobian_eq_zero hL hE.fst hE.snd hpu hpw hu2 hux huy hwx hwy hwxy
  have ediv : divergence E = fun z => partialX u z + partialY w z := rfl
  have ecurl : curl E = fun z => partialX w z - partialY u z := rfl
  have hdiv : MemLp (divergence E) 2 (cellMeasure L) := by rw [ediv]; exact hux.add hwy
  have hcurl : MemLp (curl E) 2 (cellMeasure L) := by rw [ecurl]; exact hwx.sub huy
  have n : ∀ f : ℝ × ℝ → ℝ, 0 ≤ ∫ z, f z ^ 2 ∂cellMeasure L :=
    fun f => integral_nonneg fun _ => sq_nonneg _
  rw [gradL2Sq, eLpNorm_two_sq_eq hux, eLpNorm_two_sq_eq huy, eLpNorm_two_sq_eq hwx,
    eLpNorm_two_sq_eq hwy, eLpNorm_two_sq_eq hdiv, eLpNorm_two_sq_eq hcurl,
    ← ENNReal.ofReal_add (n _) (n _), ← ENNReal.ofReal_add (add_nonneg (n _) (n _)) (n _),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (n _) (n _)) (n _)) (n _),
    ← ENNReal.ofReal_add (n _) (n _)]
  congr 1
  have iJ : Integrable (fun z => partialX u z * partialY w z - partialY u z * partialX w z)
      (cellMeasure L) :=
    (integrable_mul_of_memLp_two hux hwy).sub (integrable_mul_of_memLp_two huy hwx)
  have key : (fun z => divergence E z ^ 2 + curl E z ^ 2) = fun z =>
      (partialX u z ^ 2 + partialY u z ^ 2 + partialX w z ^ 2 + partialY w z ^ 2) +
        2 * (partialX u z * partialY w z - partialY u z * partialX w z) := by
    funext z; rw [ediv, ecurl]; ring
  have i1 := hux.integrable_sq
  have i2 := huy.integrable_sq
  have i3 := hwx.integrable_sq
  have i4 := hwy.integrable_sq
  have i12 : Integrable (fun z => partialX u z ^ 2 + partialY u z ^ 2) (cellMeasure L) :=
    i1.add i2
  have i123 : Integrable (fun z => partialX u z ^ 2 + partialY u z ^ 2 + partialX w z ^ 2)
      (cellMeasure L) := i12.add i3
  have iS : Integrable (fun z => partialX u z ^ 2 + partialY u z ^ 2 + partialX w z ^ 2 +
      partialY w z ^ 2) (cellMeasure L) := i123.add i4
  have i2J : Integrable (fun z => 2 * (partialX u z * partialY w z -
      partialY u z * partialX w z)) (cellMeasure L) := iJ.const_mul 2
  rw [← integral_add hdiv.integrable_sq hcurl.integrable_sq, key, integral_add iS i2J,
    integral_const_mul, hJ, mul_zero, add_zero, integral_add i123 i4, integral_add i12 i3,
    integral_add i1 i2]

/-- **`‖∇E‖₂ = ‖curl E‖₂` for divergence-free fields on the cylinder** (B0151, tex 2312:
`‖∇E‖₂ ≤ C‖Z‖₂` with `C = 1`, uniform in the period). -/
theorem gradL2Sq_eq_curl {L : ℝ} (hL : 0 < L) {E : ℝ × ℝ → ℝ × ℝ} (hE : ContDiff ℝ 2 E)
    (hp : ∀ q η, E (q + L, η) = E (q, η)) (hdiv : ∀ z, divergence E z = 0)
    (hu2 : MemLp (fun z => (E z).1) 2 (cellMeasure L))
    (hux : MemLp (partialX fun z => (E z).1) 2 (cellMeasure L))
    (huy : MemLp (partialY fun z => (E z).1) 2 (cellMeasure L))
    (hwx : MemLp (partialX fun z => (E z).2) 2 (cellMeasure L))
    (hwy : MemLp (partialY fun z => (E z).2) 2 (cellMeasure L))
    (hwxy : MemLp (partialY (partialX fun z => (E z).2)) 2 (cellMeasure L)) :
    gradL2Sq L E = eLpNorm (curl E) 2 (cellMeasure L) ^ 2 := by
  rw [gradL2Sq_eq hL hE hp hu2 hux huy hwx hwy hwxy,
    show divergence E = 0 from funext hdiv]
  simp

/-- Each first derivative of a divergence-free periodic field is bounded by its curl in `L²`. -/
theorem eLpNorm_partial_le_curl {L : ℝ} (hL : 0 < L) {E : ℝ × ℝ → ℝ × ℝ}
    (hE : ContDiff ℝ 2 E) (hp : ∀ q η, E (q + L, η) = E (q, η))
    (hdiv : ∀ z, divergence E z = 0)
    (hu2 : MemLp (fun z => (E z).1) 2 (cellMeasure L))
    (hux : MemLp (partialX fun z => (E z).1) 2 (cellMeasure L))
    (huy : MemLp (partialY fun z => (E z).1) 2 (cellMeasure L))
    (hwx : MemLp (partialX fun z => (E z).2) 2 (cellMeasure L))
    (hwy : MemLp (partialY fun z => (E z).2) 2 (cellMeasure L))
    (hwxy : MemLp (partialY (partialX fun z => (E z).2)) 2 (cellMeasure L)) :
    eLpNorm (partialX fun z => (E z).1) 2 (cellMeasure L) ≤ eLpNorm (curl E) 2 (cellMeasure L) ∧
    eLpNorm (partialY fun z => (E z).1) 2 (cellMeasure L) ≤ eLpNorm (curl E) 2 (cellMeasure L) ∧
    eLpNorm (partialX fun z => (E z).2) 2 (cellMeasure L) ≤ eLpNorm (curl E) 2 (cellMeasure L) ∧
    eLpNorm (partialY fun z => (E z).2) 2 (cellMeasure L) ≤
      eLpNorm (curl E) 2 (cellMeasure L) := by
  have h := gradL2Sq_eq_curl hL hE hp hdiv hu2 hux huy hwx hwy hwxy
  rw [gradL2Sq] at h
  have sq_le : ∀ a b : ℝ≥0∞, a ^ 2 ≤ b ^ 2 → a ≤ b := fun a b hab =>
    (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hab
  refine ⟨sq_le _ _ ?_, sq_le _ _ ?_, sq_le _ _ ?_, sq_le _ _ ?_⟩ <;> rw [← h]
  · exact le_self_add.trans (le_self_add.trans le_self_add)
  · exact le_add_self.trans (le_self_add.trans le_self_add)
  · exact le_add_self.trans le_self_add
  · exact le_add_self

/-! ### Interpolation, constant `1` -/

/-- **Interpolation in `q`** on the cylinder: `‖∂_q h‖₂² ≤ ‖h‖₂ ‖∂_q² h‖₂`, constant `1` for every
period (B0151, tex 2291–2294). -/
theorem interpolation_q {L : ℝ} (hL : 0 < L) {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hp : IsPeriodicQ L h) (h2 : MemLp h 2 (cellMeasure L))
    (hx : MemLp (partialX h) 2 (cellMeasure L))
    (hxx : MemLp (partialX (partialX h)) 2 (cellMeasure L)) :
    eLpNorm (partialX h) 2 (cellMeasure L) ^ 2 ≤
      eLpNorm h 2 (cellMeasure L) * eLpNorm (partialX (partialX h)) 2 (cellMeasure L) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hx1 : ContDiff ℝ 1 (partialX h) := contDiff_partialX_two hh
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have e : ∀ z, partialX (fun w => h w * partialX h w) z =
      partialX h z ^ 2 + h z * partialX (partialX h) z := fun z => by
    rw [partialX_mul hd (hx1.differentiable one_ne_zero)]; ring
  have iA : Integrable (partialX fun w => h w * partialX h w) (cellMeasure L) := by
    rw [show (partialX fun w => h w * partialX h w) = _ from funext e]
    exact hx.integrable_sq.add (integrable_mul_of_memLp_two h2 hxx)
  have h0 := integral_partialX_eq_zero hL (hh1.mul hx1) (hp.mul hp.partialX) iA
  rw [show (partialX fun w => h w * partialX h w) = _ from funext e,
    integral_add hx.integrable_sq (integrable_mul_of_memLp_two h2 hxx)] at h0
  rw [eLpNorm_two_sq_eq hx]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_integral_abs_mul_le h2 hxx)
  calc ∫ z, partialX h z ^ 2 ∂cellMeasure L
      = -∫ z, h z * partialX (partialX h) z ∂cellMeasure L := by linarith
    _ ≤ ∫ z, |h z * partialX (partialX h) z| ∂cellMeasure L := by
        rw [← integral_neg]
        exact integral_mono (integrable_mul_of_memLp_two h2 hxx).neg
          (integrable_mul_of_memLp_two h2 hxx).abs fun z => neg_le_abs _

/-- **Interpolation in `η`** on the cylinder: `‖∂_η h‖₂² ≤ ‖h‖₂ ‖∂_η² h‖₂`, constant `1`
(B0151, tex 2291–2294). -/
theorem interpolation_η {L : ℝ} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (h2 : MemLp h 2 (cellMeasure L)) (hy : MemLp (partialY h) 2 (cellMeasure L))
    (hyy : MemLp (partialY (partialY h)) 2 (cellMeasure L)) :
    eLpNorm (partialY h) 2 (cellMeasure L) ^ 2 ≤
      eLpNorm h 2 (cellMeasure L) * eLpNorm (partialY (partialY h)) 2 (cellMeasure L) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hy1 : ContDiff ℝ 1 (partialY h) := contDiff_partialY_two hh
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have e : ∀ z, partialY (fun w => h w * partialY h w) z =
      partialY h z ^ 2 + h z * partialY (partialY h) z := fun z => by
    rw [partialY_mul hd (hy1.differentiable one_ne_zero)]; ring
  have iA : Integrable (partialY fun w => h w * partialY h w) (cellMeasure L) := by
    rw [show (partialY fun w => h w * partialY h w) = _ from funext e]
    exact hy.integrable_sq.add (integrable_mul_of_memLp_two h2 hyy)
  have h0 := integral_partialY_eq_zero (hh1.mul hy1) (integrable_mul_of_memLp_two h2 hy) iA
  rw [show (partialY fun w => h w * partialY h w) = _ from funext e,
    integral_add hy.integrable_sq (integrable_mul_of_memLp_two h2 hyy)] at h0
  rw [eLpNorm_two_sq_eq hy]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_integral_abs_mul_le h2 hyy)
  calc ∫ z, partialY h z ^ 2 ∂cellMeasure L
      = -∫ z, h z * partialY (partialY h) z ∂cellMeasure L := by linarith
    _ ≤ ∫ z, |h z * partialY (partialY h) z| ∂cellMeasure L := by
        rw [← integral_neg]
        exact integral_mono (integrable_mul_of_memLp_two h2 hyy).neg
          (integrable_mul_of_memLp_two h2 hyy).abs fun z => neg_le_abs _

end UnforcedLeray.B0151
