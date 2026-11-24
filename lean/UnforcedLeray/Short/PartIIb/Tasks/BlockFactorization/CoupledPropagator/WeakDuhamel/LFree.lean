import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open PartIIbF22Aux

namespace WeakDuhamelLF

/-- The coefficient function multiplying the vorticity in `cylFreeIntegrand`. -/
def aT {ν c : ℝ} (tr : B0140.TrainSol ν c) (φ : B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) : ℝ :=
  ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x)

theorem cylFreeIntegrand_eq {ν c : ℝ} (tr : B0140.TrainSol ν c) (w : B0579.Plane → ℝ) (r : ℝ)
    (φ : B0579.Plane → ℝ) (x : B0579.Plane) :
    cylFreeIntegrand tr w r φ x = w x * aT tr φ r x := rfl

/-- Vanishing in the band `|η| > R`. -/
def Van (R : ℝ) (f : B0579.Plane → ℝ) : Prop := ∀ x : B0579.Plane, R < |x.2| → f x = 0

theorem Van.pd {R : ℝ} {f : B0579.Plane → ℝ} (h : Van R f) (j : Fin 2) :
    Van R (B0579.pd j f) := by
  intro x hx
  have hU : IsOpen {y : B0579.Plane | R < |y.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy using h y hy
  simp only [B0579.pd]
  rw [hev.fderiv_eq]
  simp

theorem Van.lapP {R : ℝ} {f : B0579.Plane → ℝ} (h : Van R f) :
    Van R (IIb.lapP f) := by
  intro x hx
  unfold IIb.lapP
  rw [(h.pd 0).pd 0 x hx, (h.pd 1).pd 1 x hx, add_zero]

theorem Van.aT {ν c R : ℝ} (tr : B0140.TrainSol ν c) {φ : B0579.Plane → ℝ}
    (h : Van R φ) (r : ℝ) :
    Van R (aT tr φ r) := by
  intro x hx
  unfold WeakDuhamelLF.aT
  rw [h.lapP x hx, h.pd 0 x hx, h.pd 1 x hx]
  ring

theorem smooth_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : B0579.Plane => tr.v r x i) := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × B0579.Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v
  have h2 : ContDiffOn ℝ ∞ (fun x : B0579.Plane => (r, x)) univ :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have h3 : ContDiffOn ℝ ∞ (fun x : B0579.Plane => tr.v r x) univ :=
    h1.comp h2 (fun x _ => ⟨hr, mem_univ _⟩)
  have h4 : ContDiff ℝ ∞ (fun x : B0579.Plane => tr.v r x) := contDiffOn_univ.1 h3
  exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp h4

theorem periodic_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r) (i : Fin 2)
    (x : B0579.Plane) :
    tr.v r (x.1 + c, x.2) i = tr.v r x i :=
  congrArg (fun u => u i) (tr.isTrain.periodic_v r hr x)

theorem isCylTest_add {c : ℝ} {φ ψ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun x => φ x + ψ x) where
  smooth := hφ.smooth.add hψ.smooth
  periodic x := by simp [hφ.periodic x, hψ.periodic x]
  band := by
    obtain ⟨R₁, hR₁⟩ := hφ.band
    obtain ⟨R₂, hR₂⟩ := hψ.band
    refine ⟨max R₁ R₂, fun x hx => ?_⟩
    simp [hR₁ x ((le_max_left _ _).trans_lt hx), hR₂ x ((le_max_right _ _).trans_lt hx)]

theorem isCylTest_const_mul {c : ℝ} (a : ℝ) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun x => a * φ x) where
  smooth := contDiff_const.mul hφ.smooth
  periodic x := by simp [hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

theorem isCylTest_lapP {c : ℝ} {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (lapP φ) :=
  isCylTest_add ((hφ.pd 0).pd 0) ((hφ.pd 1).pd 1)

theorem isCylTest_aT {ν c : ℝ} (tr : B0140.TrainSol ν c) {φ : B0579.Plane → ℝ}
    (hφ : B0579.IsCylTest c φ) {r : ℝ} (hr : 0 ≤ r) :
    B0579.IsCylTest c (aT tr φ r) :=
  isCylTest_add (isCylTest_const_mul ν (isCylTest_lapP hφ))
    (isCylTest_add
      (B0610.isCylTest_smooth_mul (smooth_slice tr hr 0) (periodic_slice tr hr 0) (hφ.pd 0))
      (B0610.isCylTest_smooth_mul (smooth_slice tr hr 1) (periodic_slice tr hr 1) (hφ.pd 1)))

/-- Continuous linear functional realizing `w ↦ ∫ x in B0579.cell c, cylFreeIntegrand tr w r φ x`
for `r ≥ 0`. -/
def freeTestCLM {ν c : ℝ} (tr : B0140.TrainSol ν c) (m : ℝ)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (r : ℝ) :
    Xmc c m →L[ℝ] ℝ :=
  if hr : 0 ≤ r then cellTestCLM c m (isCylTest_aT tr hφ hr) else 0

theorem freeTestCLM_apply {ν c : ℝ} (tr : B0140.TrainSol ν c) (m : ℝ)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) {r : ℝ} (hr : 0 ≤ r) (w : Xmc c m) :
    freeTestCLM tr m hφ r w = ∫ x in B0579.cell c, cylFreeIntegrand tr w r φ x := by
  simp only [freeTestCLM, hr, ↓reduceDIte, cellTestCLM_apply]
  rfl

/-- `L¹(cell c)` norm control on `Xmc c m` (`1 / 2 < m`) via `B0610.oneX`. -/
theorem integral_abs_le_norm_oneX_mul {c m : ℝ} (hm : 1 / 2 < m) (w : Xmc c m) :
    (∫ x in B0579.cell c, |w x|) ≤ ‖B0610.oneX c m hm‖ * ‖w‖ := by
  let wn : Xmc c m := (Lp.memLp w).norm.toLp (fun x => ‖w x‖)
  have hwn_norm : ‖wn‖ = ‖w‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have hae : (fun x => |w x|) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => wn x * (B0610.oneX c m hm) x := by
    filter_upwards [ae_restrict_cell_of_cellMeasure (MemLp.coeFn_toLp (Lp.memLp w).norm),
      B0610.coeFn_oneX (c := c) hm] with x hx₁ hx₂
    rw [hx₁, hx₂, Real.norm_eq_abs, mul_one]
  have h_nonneg : 0 ≤ ∫ x in B0579.cell c, |w x| :=
    integral_nonneg fun _ => abs_nonneg _
  calc ∫ x in B0579.cell c, |w x|
      = |(∫ x in B0579.cell c, |w x|)| := (abs_of_nonneg h_nonneg).symm
    _ = |∫ x in B0579.cell c, wn x * (B0610.oneX c m hm) x| := by
        rw [integral_congr_ae hae]
    _ ≤ ‖wn‖ * ‖B0610.oneX c m hm‖ := B0579.abs_integral_mul_le c m wn (B0610.oneX c m hm)
    _ = ‖B0610.oneX c m hm‖ * ‖w‖ := by rw [hwn_norm, mul_comm]

theorem norm_cellTestCLM_le_of_bound {c m : ℝ} (hm : 1 / 2 < m)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) {M : ℝ} (hM0 : 0 ≤ M)
    (hbd : ∀ x ∈ B0579.cell c, |ψ x| ≤ M) :
    ‖cellTestCLM c m hψ‖ ≤ M * ‖B0610.oneX c m hm‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [cellTestCLM_apply]
  have hw_abs : Integrable (fun x => |w x|) (volume.restrict (B0579.cell c)) := by
    simpa [Real.norm_eq_abs] using (integrableOn_cell_of_Xmc c m hm w).norm
  have h_pt : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ‖w x * ψ x‖ ≤ M * |w x| := by
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell c)] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd x hx) (abs_nonneg _)
  calc ‖∫ x in B0579.cell c, w x * ψ x‖
      ≤ ∫ x in B0579.cell c, ‖w x * ψ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in B0579.cell c, M * |w x| :=
        integral_mono_ae (integrableOn_mul_cylTest_of_memLp (Lp.memLp w) hψ).norm
          (hw_abs.const_mul M) h_pt
    _ = M * ∫ x in B0579.cell c, |w x| := integral_const_mul M _
    _ ≤ M * (‖B0610.oneX c m hm‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (integral_abs_le_norm_oneX_mul hm w) hM0
    _ = M * ‖B0610.oneX c m hm‖ * ‖w‖ := (mul_assoc _ _ _).symm

theorem norm_cellTestCLM_sub_le_of_bound {c m : ℝ} (hm : 1 / 2 < m)
    {ψ₁ ψ₂ : B0579.Plane → ℝ} (hψ₁ : B0579.IsCylTest c ψ₁) (hψ₂ : B0579.IsCylTest c ψ₂)
    {M : ℝ} (hM0 : 0 ≤ M) (hbd : ∀ x ∈ B0579.cell c, |ψ₁ x - ψ₂ x| ≤ M) :
    ‖cellTestCLM c m hψ₁ - cellTestCLM c m hψ₂‖ ≤ M * ‖B0610.oneX c m hm‖ := by
  have hsub : B0579.IsCylTest c (fun x => ψ₁ x - ψ₂ x) := by
    simpa [sub_eq_add_neg] using isCylTest_add hψ₁ (isCylTest_const_mul (-1) hψ₂)
  have heq : cellTestCLM c m hψ₁ - cellTestCLM c m hψ₂ = cellTestCLM c m hsub := by
    ext w
    simp only [sub_apply, cellTestCLM_apply]
    have h₁ := integrableOn_mul_cylTest_of_memLp (Lp.memLp w) hψ₁
    have h₂ := integrableOn_mul_cylTest_of_memLp (Lp.memLp w) hψ₂
    rw [← integral_sub h₁ h₂]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [heq]
  exact norm_cellTestCLM_le_of_bound hm hsub hM0 hbd

theorem continuousOn_aT_prod {ν c : ℝ} (tr : B0140.TrainSol ν c)
    {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    ContinuousOn (fun z : ℝ × B0579.Plane => aT tr φ z.1 z.2) (Ici 0 ×ˢ univ) := by
  have hv : ContinuousOn (fun z : ℝ × B0579.Plane => tr.v z.1 z.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hv0 : ContinuousOn (fun z : ℝ × B0579.Plane => tr.v z.1 z.2 0) (Ici 0 ×ˢ univ) :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn hv
  have hv1 : ContinuousOn (fun z : ℝ × B0579.Plane => tr.v z.1 z.2 1) (Ici 0 ×ˢ univ) :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous.comp_continuousOn hv
  have hlap : ContinuousOn (fun z : ℝ × B0579.Plane => lapP φ z.2) (Ici 0 ×ˢ univ) :=
    ((isCylTest_lapP hφ).continuous.comp continuous_snd).continuousOn
  have hpd0 : ContinuousOn (fun z : ℝ × B0579.Plane => B0579.pd 0 φ z.2) (Ici 0 ×ˢ univ) :=
    ((hφ.pd 0).continuous.comp continuous_snd).continuousOn
  have hpd1 : ContinuousOn (fun z : ℝ × B0579.Plane => B0579.pd 1 φ z.2) (Ici 0 ×ˢ univ) :=
    ((hφ.pd 1).continuous.comp continuous_snd).continuousOn
  exact (continuousOn_const.mul hlap).add ((hv0.mul hpd0).add (hv1.mul hpd1))

/-- Uniform operator-norm bound and operator-norm continuity of `freeTestCLM` on `Icc 0 H`. -/
theorem freeTestCLM_bound_and_continuousOn {ν c m H : ℝ} (hm : 1 / 2 < m)
    (tr : B0140.TrainSol ν c) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    (∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ r ∈ Icc 0 H, ‖freeTestCLM tr m hφ r‖ ≤ C_L) ∧
    ContinuousOn (freeTestCLM tr m hφ) (Icc 0 H) := by
  obtain ⟨R, hR⟩ := hφ.band
  have hvan_aT : ∀ (r : ℝ), ∀ x ∈ B0579.cell c, x ∉ B0579.box c R → aT tr φ r x = 0 := by
    intro r x hx hxK
    refine (Van.aT tr hR r) x ?_
    by_contra hle
    exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 hle))
  set K : Set (ℝ × B0579.Plane) := Icc 0 H ×ˢ B0579.box c R
  have hK_compact : IsCompact K := isCompact_Icc.prod (B0579.isCompact_box c R)
  have hK_sub : K ⊆ Ici 0 ×ˢ univ := prod_mono Icc_subset_Ici_self (subset_univ _)
  have haT_cont : ContinuousOn (fun z : ℝ × B0579.Plane => aT tr φ z.1 z.2) K :=
    (continuousOn_aT_prod tr hφ).mono hK_sub
  refine ⟨?_, ?_⟩
  · obtain ⟨M₀, hM₀⟩ := hK_compact.exists_bound_of_continuousOn haT_cont
    set M : ℝ := max M₀ 0
    have hM0 : 0 ≤ M := le_max_right _ _
    refine ⟨M * ‖B0610.oneX c m hm‖, by positivity, fun r hr => ?_⟩
    simp only [freeTestCLM, hr.1, ↓reduceDIte]
    refine norm_cellTestCLM_le_of_bound hm (isCylTest_aT tr hφ hr.1) hM0 fun x hx => ?_
    by_cases hxK : x ∈ B0579.box c R
    · have h1 : ‖aT tr φ r x‖ ≤ M₀ := hM₀ (r, x) ⟨hr, hxK⟩
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (le_max_left _ _)
    · rw [hvan_aT r x hx hxK, abs_zero]
      exact hM0
  · have huc := Metric.uniformContinuousOn_iff.1
      (hK_compact.uniformContinuousOn_of_continuous haT_cont)
    intro r hr
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    set C1 : ℝ := ‖B0610.oneX c m hm‖ + 1
    have hC1_pos : 0 < C1 := by dsimp [C1]; positivity
    set ε' : ℝ := ε / C1
    have hε' : 0 < ε' := div_pos hε hC1_pos
    obtain ⟨δ, hδ, hδ_uc⟩ := huc ε' hε'
    refine ⟨δ, hδ, fun r' hr' hdist => ?_⟩
    rw [dist_eq_norm]
    simp only [freeTestCLM, hr'.1, hr.1, ↓reduceDIte]
    have hbd : ∀ x ∈ B0579.cell c, |aT tr φ r' x - aT tr φ r x| ≤ ε' := by
      intro x hx
      by_cases hxK : x ∈ B0579.box c R
      · have hd : dist ((r', x) : ℝ × B0579.Plane) (r, x) < δ := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
          exact hdist
        have hlt := hδ_uc (r', x) ⟨hr', hxK⟩ (r, x) ⟨hr, hxK⟩ hd
        rw [Real.dist_eq] at hlt
        exact hlt.le
      · rw [hvan_aT r' x hx hxK, hvan_aT r x hx hxK, sub_self, abs_zero]
        exact hε'.le
    have hle := norm_cellTestCLM_sub_le_of_bound hm
      (isCylTest_aT tr hφ hr'.1) (isCylTest_aT tr hφ hr.1) hε'.le hbd
    have hstrict : ε' * ‖B0610.oneX c m hm‖ < ε := by
      have h1 : ‖B0610.oneX c m hm‖ < C1 := by dsimp [C1]; linarith
      calc ε' * ‖B0610.oneX c m hm‖
          < ε' * C1 := mul_lt_mul_of_pos_left h1 hε'
        _ = ε := div_mul_cancel₀ ε hC1_pos.ne'
    exact hle.trans_lt hstrict

end WeakDuhamelLF

end UnforcedLeray.Short.IIb

end
