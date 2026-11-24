import UnforcedLeray.Units.B0296.Kernel

/-!
# B0296: heat smoothing in divergence form on the cylinder

Helper of unit B0296 (`unlabeled:5039`, tex lines 5033–5053); blueprint unit B0296 of


Objects (on the cylinder carrier of B0284: `c`-periodic lifts `Plane → β`, normalized cell
measure `cellMeasure c = dq/c dη`):

* `symTensor v h = v ⊗ h + h ⊗ v`, stored by columns: column `j` is `h_j v + v_j h`, the
  vector differentiated by `∂_j` in `div`. The linearized coefficient of the flat equation is
  `B_v h = div (v ⊗ h + h ⊗ v)` (blueprint note of B0296; tex lines 5035–5040, 5414).
* `heatDiv θ T = e^{θΔ} div T`, for `θ > 0` the convolution
  `z ↦ ∫ (∂_q K_θ(w) T_q(z-w) + ∂_η K_θ(w) T_η(z-w)) dw` of the tensor field `T` with the
  gradient of the planar heat kernel `K_θ = B0284.heatKernel2 θ` (`B0296.Kernel`). For smooth `T`
  this is `e^{θΔ}(∂_q T_q + ∂_η T_η)` by integration by parts; for `T ∈ L^p_sp` it is the
  definition of `e^{θΔ} div T`. Where the convolution integral does not converge Lean's value is
  `0`; every estimate below is proved through `‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ`, and differences are only taken
  at points where both integrals converge (almost every point of the cell, for `L^p` inputs).
  For `θ ≤ 0` the value is `0` (never used: heat times are `ν(s-t) > 0`).

Results:
* `eLpNorm_heatDiv_sub_le`: `‖e^{θΔ}div T₁ - e^{θΔ}div T₂‖_{L^p_sp} ≤ 4 (4πθ)^{-1/2} ‖T₁ - T₂‖_{L^p_sp}`
  for periodic `T₁, T₂ ∈ L^p_sp`, `1 ≤ p < ∞` (the heat gradient smoothing of tex lines
  5042–5046, `C = 2π^{-1/2}`);
* `memLp_heatDiv`, `heatDiv_periodic`: `e^{θΔ} div` maps periodic `L^p_sp` tensors to periodic
  `L^p_sp` fields;
* `eLpNorm_heat_sub_heat_le`, `aestronglyMeasurable_heat`: the corresponding facts for
  `e^{θΔ}` itself (difference form of B0284's heat contraction).

The two Minkowski lemmas `eLpNorm_kernelAbs_le'` and `ae_kernelAbs_lt_top'` are the proofs of
`B0295.eLpNorm_kernelAbs_le` and `B0295.ae_kernelAbs_lt_top`

replaced by an arbitrary normed group.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real Topology
open scoped NNReal ENNReal

namespace UnforcedLeray.B0296

open UnforcedLeray.B0284
open UnforcedLeray.GaussianVortex (Plane)

/-! ## Kernel convolutions with values in a normed group -/

section Generic

variable {E : Type*} [NormedAddCommGroup E]

theorem aestronglyMeasurable_comp_sub {g : Plane → E} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun q : Plane × Plane => g (q.1 - q.2))
      ((volume : Measure Plane).prod volume) :=
  hg.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure Plane) volume)

theorem aestronglyMeasurable_comp_sub_left {g : Plane → E} (hg : AEStronglyMeasurable g volume)
    (z : Plane) : AEStronglyMeasurable (fun w => g (z - w)) volume :=
  hg.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Plane) z)

theorem isQPeriodic_sub {c : ℝ} {g₁ g₂ : Plane → E} (h₁ : IsQPeriodic c g₁)
    (h₂ : IsQPeriodic c g₂) : IsQPeriodic c (g₁ - g₂) := fun z => by
  simp only [Pi.sub_apply, h₁ z, h₂ z]

/-- Minkowski with a general kernel on the cylinder, for fields with values in a normed group
(the proof of `B0295.eLpNorm_kernelAbs_le`):
`‖∫ k(w) |g(·-w)| dw‖_{L^p(dq/c dη)} ≤ (∫ k) ‖g‖_{L^p(dq/c dη)}`, `1 ≤ p < ∞`. -/
theorem eLpNorm_kernelAbs_le' {c : ℝ} (hc : 0 < c) {k : Plane → ℝ≥0∞} (hk : Measurable k)
    (hk' : ∀ w, k w ≠ ⊤) {g : Plane → E} (hper : IsQPeriodic c g)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => ∫⁻ w, k w * ‖g (z - w)‖ₑ) p (cellMeasure c) ≤
      (∫⁻ w, k w) * eLpNorm g p (cellMeasure c) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hF : AEMeasurable (Function.uncurry fun z w => k w * ‖g (z - w)‖ₑ)
      ((cellMeasure c).prod volume) := by
    have h1 : AEMeasurable (fun q : Plane × Plane => ‖g (q.1 - q.2)‖ₑ)
        ((cellMeasure c).prod volume) :=
      ((aestronglyMeasurable_comp_sub hg).enorm).mono_ac
        ((cellMeasure_ac c).prod Measure.AbsolutelyContinuous.rfl)
    exact (hk.comp measurable_snd).aemeasurable.mul h1
  calc eLpNorm (fun z => ∫⁻ w, k w * ‖g (z - w)‖ₑ) p (cellMeasure c)
      ≤ ∫⁻ w, eLpNorm (fun z => k w * ‖g (z - w)‖ₑ) p (cellMeasure c) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hF hp hp'
    _ = ∫⁻ w, k w * eLpNorm g p (cellMeasure c) := by
        refine lintegral_congr fun w => ?_
        rw [eLpNorm_const_mul_ennreal (hk' w) _ hp0 hp', eLpNorm_enorm,
          eLpNorm_cellMeasure_sub hc hper hg hp0 hp' w]
    _ = (∫⁻ w, k w) * eLpNorm g p (cellMeasure c) := lintegral_mul_const _ hk

/-- The absolute kernel integral of a periodic `L^p` field against a finite-mass kernel is
finite at almost every point of the cell (the proof of `B0295.ae_kernelAbs_lt_top`). -/
theorem ae_kernelAbs_lt_top' {c : ℝ} (hc : 0 < c) {k : Plane → ℝ≥0∞} (hk : Measurable k)
    (hk' : ∀ w, k w ≠ ⊤) (hkfin : ∫⁻ w, k w ≠ ⊤) {g : Plane → E} (hper : IsQPeriodic c g)
    (hg : AEStronglyMeasurable g volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hfin : eLpNorm g p (cellMeasure c) ≠ ⊤) :
    ∀ᵐ z ∂(cellMeasure c), ∫⁻ w, k w * ‖g (z - w)‖ₑ < ⊤ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hF : AEMeasurable (fun q : Plane × Plane => k q.2 * ‖g (q.1 - q.2)‖ₑ)
      ((cellMeasure c).prod volume) := by
    have h1 : AEMeasurable (fun q : Plane × Plane => ‖g (q.1 - q.2)‖ₑ)
        ((cellMeasure c).prod volume) :=
      ((aestronglyMeasurable_comp_sub hg).enorm).mono_ac
        ((cellMeasure_ac c).prod Measure.AbsolutelyContinuous.rfl)
    exact (hk.comp measurable_snd).aemeasurable.mul h1
  refine B0295.ae_lt_top_of_eLpNorm_ne_top hF.lintegral_prod_right' hp0 hp' ?_
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hkfin hfin)
    (eLpNorm_kernelAbs_le' hc hk hk' hper hg hp hp')

/-- Pointwise domination of a kernel convolution `∫ A(w)(g(z-w)) dw` whose kernel action is
bounded by `k`. No integrability is needed. -/
theorem enorm_integral_le_kernelAbs (A : Plane → E → Plane) {k : Plane → ℝ≥0∞}
    (hA : ∀ w x, ‖A w x‖ₑ ≤ k w * ‖x‖ₑ) (g : Plane → E) (z : Plane) :
    ‖∫ w, A w (g (z - w))‖ₑ ≤ ∫⁻ w, k w * ‖g (z - w)‖ₑ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun w => hA w _)

/-- `L^p_sp` bound of a kernel convolution: `‖∫ A(w)(g(·-w)) dw‖ ≤ (∫ k) ‖g‖`. -/
theorem eLpNorm_kconv_le {c : ℝ} (hc : 0 < c) {k : Plane → ℝ≥0∞} (hk : Measurable k)
    (hk' : ∀ w, k w ≠ ⊤) (A : Plane → E → Plane) (hA : ∀ w x, ‖A w x‖ₑ ≤ k w * ‖x‖ₑ)
    {g : Plane → E} (hper : IsQPeriodic c g) (hg : AEStronglyMeasurable g volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => ∫ w, A w (g (z - w))) p (cellMeasure c) ≤
      (∫⁻ w, k w) * eLpNorm g p (cellMeasure c) :=
  (eLpNorm_mono_enorm fun z =>
    (enorm_integral_le_kernelAbs A hA g z).trans_eq (enorm_eq_self _).symm).trans
    (eLpNorm_kernelAbs_le' hc hk hk' hper hg hp hp')

theorem integrable_kconv_of_lt_top (A : Plane → E → Plane) {k : Plane → ℝ≥0∞}
    (hA : ∀ w x, ‖A w x‖ₑ ≤ k w * ‖x‖ₑ) {g : Plane → E} (z : Plane)
    (hm : AEStronglyMeasurable (fun w => A w (g (z - w))) volume)
    (hfin : ∫⁻ w, k w * ‖g (z - w)‖ₑ < ⊤) : Integrable (fun w => A w (g (z - w))) := by
  refine ⟨hm, ?_⟩
  show ∫⁻ w, ‖A w (g (z - w))‖ₑ < ⊤
  exact (lintegral_mono fun w => hA w _).trans_lt hfin

/-- **Difference bound for a kernel convolution.** For periodic `g₁, g₂ ∈ L^p_sp` and an additive
kernel action bounded by a finite-mass kernel `k`, the two convolution integrals converge at
almost every point of the cell and
`‖∫ A(w)(g₁(·-w)) - ∫ A(w)(g₂(·-w))‖_{L^p_sp} ≤ (∫ k) ‖g₁ - g₂‖_{L^p_sp}`. -/
theorem eLpNorm_kconv_sub_le {c : ℝ} (hc : 0 < c) {k : Plane → ℝ≥0∞} (hk : Measurable k)
    (hk' : ∀ w, k w ≠ ⊤) (hkfin : ∫⁻ w, k w ≠ ⊤) (A : Plane → E → Plane)
    (hA : ∀ w x, ‖A w x‖ₑ ≤ k w * ‖x‖ₑ) (hAsub : ∀ w x y, A w x - A w y = A w (x - y))
    {g₁ g₂ : Plane → E} (hper₁ : IsQPeriodic c g₁) (hper₂ : IsQPeriodic c g₂)
    (hg₁ : AEStronglyMeasurable g₁ volume) (hg₂ : AEStronglyMeasurable g₂ volume)
    (hAm₁ : ∀ z, AEStronglyMeasurable (fun w => A w (g₁ (z - w))) volume)
    (hAm₂ : ∀ z, AEStronglyMeasurable (fun w => A w (g₂ (z - w))) volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hfin₁ : eLpNorm g₁ p (cellMeasure c) ≠ ⊤) (hfin₂ : eLpNorm g₂ p (cellMeasure c) ≠ ⊤) :
    eLpNorm (fun z => (∫ w, A w (g₁ (z - w))) - ∫ w, A w (g₂ (z - w))) p (cellMeasure c) ≤
      (∫⁻ w, k w) * eLpNorm (g₁ - g₂) p (cellMeasure c) := by
  have h₁ := ae_kernelAbs_lt_top' hc hk hk' hkfin hper₁ hg₁ hp hp' hfin₁
  have h₂ := ae_kernelAbs_lt_top' hc hk hk' hkfin hper₂ hg₂ hp hp' hfin₂
  refine le_trans ?_
    (eLpNorm_kernelAbs_le' hc hk hk' (isQPeriodic_sub hper₁ hper₂) (hg₁.sub hg₂) hp hp')
  refine eLpNorm_mono_enorm_ae ?_
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [enorm_eq_self, ← integral_sub (integrable_kconv_of_lt_top A hA z (hAm₁ z) hz₁)
    (integrable_kconv_of_lt_top A hA z (hAm₂ z) hz₂)]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun w => ?_)
  rw [hAsub]
  exact hA w _

omit [NormedAddCommGroup E] in
/-- A kernel convolution of a jointly measurable integrand is almost everywhere strongly
measurable on the cell. -/
theorem aestronglyMeasurable_kconv (c : ℝ) (A : Plane → E → Plane) {g : Plane → E}
    (hΦ : AEStronglyMeasurable (fun q : Plane × Plane => A q.2 (g (q.1 - q.2)))
      ((volume : Measure Plane).prod volume)) :
    AEStronglyMeasurable (fun z => ∫ w, A w (g (z - w))) (cellMeasure c) :=
  (hΦ.integral_prod_right').mono_ac (cellMeasure_ac c)

end Generic

/-! ## The heat semigroup: difference bound and measurability -/

theorem heat_eq_integral {θ : ℝ} (hθ : 0 < θ) (g : Plane → Plane) :
    heat θ g = fun z => ∫ w, (fun w x => heatKernel2 θ w • x) w (g (z - w)) := by
  funext z
  exact heat_apply_of_pos hθ g z

theorem enorm_heatKernel2_smul_le {θ : ℝ} (hθ : 0 < θ) (w x : Plane) :
    ‖heatKernel2 θ w • x‖ₑ ≤ ENNReal.ofReal (heatKernel2 θ w) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_of_nonneg (heatKernel2_nonneg hθ w)]

theorem aestronglyMeasurable_heatIntegrand (θ : ℝ) {g : Plane → Plane}
    (hg : AEStronglyMeasurable g volume) (z : Plane) :
    AEStronglyMeasurable (fun w => heatKernel2 θ w • g (z - w)) volume :=
  (measurable_heatKernel2_right θ).aestronglyMeasurable.smul
    (aestronglyMeasurable_comp_sub_left hg z)

/-- `e^{θΔ} g` of a periodic, almost everywhere strongly measurable field is almost everywhere
strongly measurable on the cell. -/
theorem aestronglyMeasurable_heat (c θ : ℝ) {g : Plane → Plane}
    (hg : AEStronglyMeasurable g volume) : AEStronglyMeasurable (heat θ g) (cellMeasure c) := by
  by_cases hθ : 0 < θ
  · rw [heat_eq_integral hθ]
    refine aestronglyMeasurable_kconv c (fun w x => heatKernel2 θ w • x) ?_
    exact ((measurable_heatKernel2_right θ).comp measurable_snd).aestronglyMeasurable.smul
      (aestronglyMeasurable_comp_sub hg)
  · rw [heat_of_nonpos (not_lt.mp hθ)]
    exact hg.mono_ac (cellMeasure_ac c)

/-- **Heat difference bound**: `‖e^{θΔ}g₁ - e^{θΔ}g₂‖_{L^p_sp} ≤ ‖g₁ - g₂‖_{L^p_sp}` for periodic,
almost everywhere strongly measurable `g₁, g₂ ∈ L^p_sp`, every `θ` and `1 ≤ p < ∞`. -/
theorem eLpNorm_heat_sub_heat_le {c : ℝ} (hc : 0 < c) (θ : ℝ) {g₁ g₂ : Plane → Plane}
    (hper₁ : IsQPeriodic c g₁) (hper₂ : IsQPeriodic c g₂)
    (hg₁ : AEStronglyMeasurable g₁ volume) (hg₂ : AEStronglyMeasurable g₂ volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hfin₁ : eLpNorm g₁ p (cellMeasure c) ≠ ⊤) (hfin₂ : eLpNorm g₂ p (cellMeasure c) ≠ ⊤) :
    eLpNorm (heat θ g₁ - heat θ g₂) p (cellMeasure c) ≤ eLpNorm (g₁ - g₂) p (cellMeasure c) := by
  by_cases hθ : 0 < θ
  · have hk : Measurable fun w => ENNReal.ofReal (heatKernel2 θ w) :=
      (measurable_heatKernel2_right θ).ennreal_ofReal
    have hmass := lintegral_heatKernel2 hθ
    have key := eLpNorm_kconv_sub_le hc hk (fun _ => ENNReal.ofReal_ne_top)
      (by rw [hmass]; exact ENNReal.one_ne_top) (fun w x => heatKernel2 θ w • x)
      (enorm_heatKernel2_smul_le hθ) (fun w x y => (smul_sub _ x y).symm) hper₁ hper₂ hg₁ hg₂
      (aestronglyMeasurable_heatIntegrand θ hg₁) (aestronglyMeasurable_heatIntegrand θ hg₂)
      hp hp' hfin₁ hfin₂
    rw [hmass, one_mul] at key
    refine le_of_eq_of_le ?_ key
    congr 1
    funext z
    simp only [Pi.sub_apply, heat_apply_of_pos hθ]
  · rw [heat_of_nonpos (not_lt.mp hθ), heat_of_nonpos (not_lt.mp hθ)]

/-! ## Symmetric tensors and `e^{θΔ} div` -/

/-- The symmetric tensor `v ⊗ h + h ⊗ v`, by columns: column `j` is `h_j v + v_j h`. -/
def symTensor (v h : Plane) : Plane × Plane := (h.1 • v + v.1 • h, h.2 • v + v.2 • h)

theorem symTensor_sub (v h₁ h₂ : Plane) :
    symTensor v h₁ - symTensor v h₂ = symTensor v (h₁ - h₂) := by
  ext <;> simp only [symTensor, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul] <;> ring

theorem norm_symTensor_le (v h : Plane) : ‖symTensor v h‖ ≤ 2 * ‖v‖ * ‖h‖ := by
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · calc ‖h.1 • v + v.1 • h‖ ≤ ‖h.1 • v‖ + ‖v.1 • h‖ := norm_add_le _ _
      _ = ‖h.1‖ * ‖v‖ + ‖v.1‖ * ‖h‖ := by rw [norm_smul, norm_smul]
      _ ≤ ‖h‖ * ‖v‖ + ‖v‖ * ‖h‖ := by
          gcongr
          · exact norm_fst_le h
          · exact norm_fst_le v
      _ = 2 * ‖v‖ * ‖h‖ := by ring
  · calc ‖h.2 • v + v.2 • h‖ ≤ ‖h.2 • v‖ + ‖v.2 • h‖ := norm_add_le _ _
      _ = ‖h.2‖ * ‖v‖ + ‖v.2‖ * ‖h‖ := by rw [norm_smul, norm_smul]
      _ ≤ ‖h‖ * ‖v‖ + ‖v‖ * ‖h‖ := by
          gcongr
          · exact norm_snd_le h
          · exact norm_snd_le v
      _ = 2 * ‖v‖ * ‖h‖ := by ring

theorem continuous_symTensor : Continuous fun q : Plane × Plane => symTensor q.1 q.2 := by
  unfold symTensor
  fun_prop

/-- The kernel action of `e^{θΔ} div`: `x = (x_q, x_η) ↦ ∂_q K_θ(w) x_q + ∂_η K_θ(w) x_η`. -/
def divKernel (θ : ℝ) (w : Plane) (x : Plane × Plane) : Plane :=
  (gradHeatKernel2 θ w).1 • x.1 + (gradHeatKernel2 θ w).2 • x.2

/-- `e^{θΔ} div T` for a tensor field `T` on the cylinder given by its columns
`T = (T_q, T_η)`: for `θ > 0` the convolution `∫ (∂_q K_θ(w) T_q(z-w) + ∂_η K_θ(w) T_η(z-w)) dw`
with the gradient of the planar heat kernel; `0` for `θ ≤ 0` (never used). -/
def heatDiv (θ : ℝ) (T : Plane → Plane × Plane) : Plane → Plane :=
  fun z => if 0 < θ then ∫ w : Plane, divKernel θ w (T (z - w)) else 0

theorem heatDiv_apply_of_pos {θ : ℝ} (hθ : 0 < θ) (T : Plane → Plane × Plane) (z : Plane) :
    heatDiv θ T z = ∫ w : Plane, divKernel θ w (T (z - w)) := by
  simp [heatDiv, hθ]

theorem heatDiv_eq_integral {θ : ℝ} (hθ : 0 < θ) (T : Plane → Plane × Plane) :
    heatDiv θ T = fun z => ∫ w : Plane, divKernel θ w (T (z - w)) := by
  funext z
  exact heatDiv_apply_of_pos hθ T z

theorem enorm_fst_le' (x : Plane × Plane) : ‖x.1‖ₑ ≤ ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_fst_le x)

theorem enorm_snd_le' (x : Plane × Plane) : ‖x.2‖ₑ ≤ ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_snd_le x)

theorem enorm_divKernel_le (θ : ℝ) (w : Plane) (x : Plane × Plane) :
    ‖divKernel θ w x‖ₑ ≤ gradKernelAbs θ w * ‖x‖ₑ := by
  unfold divKernel gradKernelAbs
  calc ‖(gradHeatKernel2 θ w).1 • x.1 + (gradHeatKernel2 θ w).2 • x.2‖ₑ
      ≤ ‖(gradHeatKernel2 θ w).1 • x.1‖ₑ + ‖(gradHeatKernel2 θ w).2 • x.2‖ₑ := enorm_add_le _ _
    _ = ‖(gradHeatKernel2 θ w).1‖ₑ * ‖x.1‖ₑ + ‖(gradHeatKernel2 θ w).2‖ₑ * ‖x.2‖ₑ := by
        rw [enorm_smul, enorm_smul]
    _ ≤ ‖(gradHeatKernel2 θ w).1‖ₑ * ‖x‖ₑ + ‖(gradHeatKernel2 θ w).2‖ₑ * ‖x‖ₑ := by
        gcongr
        · exact enorm_fst_le' x
        · exact enorm_snd_le' x
    _ = (‖(gradHeatKernel2 θ w).1‖ₑ + ‖(gradHeatKernel2 θ w).2‖ₑ) * ‖x‖ₑ := (add_mul _ _ _).symm

theorem divKernel_sub (θ : ℝ) (w : Plane) (x y : Plane × Plane) :
    divKernel θ w x - divKernel θ w y = divKernel θ w (x - y) := by
  simp only [divKernel, Prod.fst_sub, Prod.snd_sub, smul_sub]
  abel

theorem aestronglyMeasurable_divIntegrand (θ : ℝ) {T : Plane → Plane × Plane}
    (hT : AEStronglyMeasurable T volume) (z : Plane) :
    AEStronglyMeasurable (fun w => divKernel θ w (T (z - w))) volume := by
  have h := aestronglyMeasurable_comp_sub_left hT z
  exact ((measurable_gradHeatKernel2_fst θ).aestronglyMeasurable.smul h.fst).add
    ((measurable_gradHeatKernel2_snd θ).aestronglyMeasurable.smul h.snd)

theorem aestronglyMeasurable_divIntegrand_prod (θ : ℝ) {T : Plane → Plane × Plane}
    (hT : AEStronglyMeasurable T volume) :
    AEStronglyMeasurable (fun q : Plane × Plane => divKernel θ q.2 (T (q.1 - q.2)))
      ((volume : Measure Plane).prod volume) := by
  have h := aestronglyMeasurable_comp_sub hT
  exact (((measurable_gradHeatKernel2_fst θ).comp measurable_snd).aestronglyMeasurable.smul
    h.fst).add (((measurable_gradHeatKernel2_snd θ).comp measurable_snd).aestronglyMeasurable.smul
    h.snd)

/-- `e^{θΔ} div` maps cylinder tensors to cylinder fields. -/
theorem heatDiv_periodic {c θ : ℝ} {T : Plane → Plane × Plane} (hT : IsQPeriodic c T) :
    IsQPeriodic c (heatDiv θ T) := by
  intro z
  by_cases hθ : 0 < θ
  · rw [heatDiv_apply_of_pos hθ, heatDiv_apply_of_pos hθ]
    congr 1
    funext w
    have hz : ((z.1 + c, z.2) : Plane) - w = ((z - w).1 + c, (z - w).2) := by
      ext
      · simp only [Prod.fst_sub]
        ring
      · simp
    rw [hz, hT]
  · simp [heatDiv, hθ]

/-- **Heat gradient smoothing in divergence form** (tex lines 5042–5046): for `θ > 0`, periodic,
almost everywhere strongly measurable tensors `T₁, T₂ ∈ L^p_sp` and `1 ≤ p < ∞`,
`‖e^{θΔ}div T₁ - e^{θΔ}div T₂‖_{L^p_sp} ≤ 4 (4πθ)^{-1/2} ‖T₁ - T₂‖_{L^p_sp}`. -/
theorem eLpNorm_heatDiv_sub_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T₁ T₂ : Plane → Plane × Plane} (hper₁ : IsQPeriodic c T₁) (hper₂ : IsQPeriodic c T₂)
    (hT₁ : AEStronglyMeasurable T₁ volume) (hT₂ : AEStronglyMeasurable T₂ volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hfin₁ : eLpNorm T₁ p (cellMeasure c) ≠ ⊤) (hfin₂ : eLpNorm T₂ p (cellMeasure c) ≠ ⊤) :
    eLpNorm (heatDiv θ T₁ - heatDiv θ T₂) p (cellMeasure c) ≤
      ENNReal.ofReal (4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) *
        eLpNorm (T₁ - T₂) p (cellMeasure c) := by
  have hmass := lintegral_gradKernelAbs hθ
  have key := eLpNorm_kconv_sub_le hc (measurable_gradKernelAbs θ) (gradKernelAbs_ne_top θ)
    (by rw [hmass]; exact ENNReal.ofReal_ne_top) (divKernel θ) (enorm_divKernel_le θ)
    (divKernel_sub θ) hper₁ hper₂ hT₁ hT₂ (aestronglyMeasurable_divIntegrand θ hT₁)
    (aestronglyMeasurable_divIntegrand θ hT₂) hp hp' hfin₁ hfin₂
  rw [hmass] at key
  refine le_of_eq_of_le ?_ key
  congr 1
  funext z
  simp only [Pi.sub_apply, heatDiv_apply_of_pos hθ]

/-- **Heat gradient smoothing**, single-field form:
`‖e^{θΔ}div T‖_{L^p_sp} ≤ 4 (4πθ)^{-1/2} ‖T‖_{L^p_sp}` (`θ > 0`, `1 ≤ p < ∞`). -/
theorem eLpNorm_heatDiv_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : AEStronglyMeasurable T volume) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) :
    eLpNorm (heatDiv θ T) p (cellMeasure c) ≤
      ENNReal.ofReal (4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) *
        eLpNorm T p (cellMeasure c) := by
  rw [heatDiv_eq_integral hθ, ← lintegral_gradKernelAbs hθ]
  exact eLpNorm_kconv_le hc (measurable_gradKernelAbs θ) (gradKernelAbs_ne_top θ) (divKernel θ)
    (enorm_divKernel_le θ) hper hT hp hp'

/-- `e^{θΔ} div T ∈ L^p_sp` for a periodic, almost everywhere strongly measurable `T ∈ L^p_sp`
(`θ > 0`, `1 ≤ p < ∞`). -/
theorem memLp_heatDiv {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : AEStronglyMeasurable T volume) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) (hfin : eLpNorm T p (cellMeasure c) ≠ ⊤) :
    MemLp (heatDiv θ T) p (cellMeasure c) := by
  refine ⟨?_, ?_⟩
  · rw [heatDiv_eq_integral hθ]
    exact aestronglyMeasurable_kconv c (divKernel θ) (aestronglyMeasurable_divIntegrand_prod θ hT)
  · exact (eLpNorm_heatDiv_le hc hθ hper hT hp hp').trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top)

/-! ## The tensor `v ⊗ h + h ⊗ v` of two cylinder fields -/

theorem symTensor_field_periodic {c : ℝ} {v h : Plane → Plane} (hv : IsQPeriodic c v)
    (hh : IsQPeriodic c h) : IsQPeriodic c (fun z => symTensor (v z) (h z)) := fun z => by
  simp only [hv z, hh z]

theorem aestronglyMeasurable_symTensor_field {v h : Plane → Plane}
    (hv : AEStronglyMeasurable v volume) (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (fun z => symTensor (v z) (h z)) volume :=
  continuous_symTensor.comp_aestronglyMeasurable (hv.prodMk hh)

/-- `‖v ⊗ h + h ⊗ v‖_{L^p_sp} ≤ 2M ‖h‖_{L^p_sp}` when `|v| ≤ M` almost everywhere on the cell. -/
theorem eLpNorm_symTensor_field_le {c M : ℝ} {v h : Plane → Plane}
    (hvM : ∀ᵐ z ∂(cellMeasure c), ‖v z‖ ≤ M) (p : ℝ≥0∞) :
    eLpNorm (fun z => symTensor (v z) (h z)) p (cellMeasure c) ≤
      ENNReal.ofReal (2 * M) * eLpNorm h p (cellMeasure c) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ p
  filter_upwards [hvM] with z hz
  calc ‖symTensor (v z) (h z)‖ ≤ 2 * ‖v z‖ * ‖h z‖ := norm_symTensor_le _ _
    _ ≤ 2 * M * ‖h z‖ := by gcongr

end UnforcedLeray.B0296
