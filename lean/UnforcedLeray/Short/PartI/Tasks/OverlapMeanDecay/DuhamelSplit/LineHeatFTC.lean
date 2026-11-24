import UnforcedLeray.Lib.HeatR3.Duhamel
import UnforcedLeray.Lib.HeatR3.Anisotropic
import UnforcedLeray.Lib.HeatR3.Generator
import Mathlib.Analysis.Calculus.MeanValue

/-!
# 1D Heat Kernel Calculus and Duhamel Formula on `ℝ` (`PartI:T15/1`, helper 1)

This module proves:
1. `iteratedDeriv_lineHeat_data`: for `θ > 0` and smooth `f : ℝ → ℝ` with bounded derivatives up
   to order `k`, `iteratedDeriv k (Heat.lineHeat θ f) = Heat.lineHeat θ (iteratedDeriv k f)`.
2. `iteratedDeriv_lineDuhamel_one`: for `T > 0`, smooth `ψ₀`, and smooth `F` on `(0, ∞) × ℝ` with
   bounded spatial derivatives up to order `k` on `[0, T] × ℝ`,
   `iteratedDeriv k (Heat.lineDuhamel 1 ψ₀ F T) =
     Heat.lineDuhamel 1 (iteratedDeriv k ψ₀) (fun t => iteratedDeriv k (F t)) T`.
3. `lineHeat_duhamel_of_pde`: if `u : ℝ → ℝ → ℝ` is smooth on `[0, ∞) × ℝ` with `u`, `∂_Y u`,
   `∂_Y² u`, `∂_t u` bounded on `[0, T] × ℝ` and solves `∂_t u - ∂_Y² u = F` on `[0, T] × ℝ`,
   then `u T Y = Heat.lineDuhamel 1 (u 0) F T Y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real Topology intervalIntegral
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.PartI.DuhamelSplit

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.Heat (lineIso lineGauss lineHeat lineDuhamel gaussDt)

/-! ### 1. Iterated spatial derivatives of `lineHeat` and `lineDuhamel` -/

private theorem contDiff_deriv_of_top {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.comp hfd

theorem contDiff_iteratedDeriv_of_top {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact contDiff_deriv_of_top ih

/-- For `θ > 0` and `f ∈ C^∞(ℝ)` with `|iteratedDeriv m f| ≤ M` for all `m ≤ k`,
`iteratedDeriv k (lineHeat θ f) = lineHeat θ (iteratedDeriv k f)`. -/
theorem iteratedDeriv_lineHeat_data {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (k : ℕ) {M : ℝ} (hM : ∀ m ≤ k, ∀ x : ℝ, |iteratedDeriv m f x| ≤ M) :
    iteratedDeriv k (lineHeat θ f) = lineHeat θ (iteratedDeriv k f) := by
  induction k with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih (fun m hm => hM m (Nat.le_succ_of_le hm))]
    have hgk : ContDiff ℝ ∞ (iteratedDeriv k f) := contDiff_iteratedDeriv_of_top hf k
    have hdiff : ∀ η : ℝ, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f η) η := by
      intro η
      rw [iteratedDeriv_succ]
      exact (hgk.differentiable (by simp) η).hasDerivAt
    funext η
    exact (Heat.hasDerivAt_lineHeat_data hθ hdiff
      (hM k (Nat.le_succ k)) (hM (k + 1) le_rfl) η).deriv

/-- If `(t, x) ↦ F t x` is `C^∞` on `(0, ∞) × ℝ`, then so is `(t, x) ↦ iteratedDeriv m (F t) x`
for every `m : ℕ`. -/
theorem contDiffOn_iteratedDeriv_snd {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (Ioi 0 ×ˢ univ)) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv m (F p.1) p.2) (Ioi 0 ×ˢ univ) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  induction m with
  | zero =>
    simpa [iteratedDeriv_zero] using hF
  | succ m ih =>
    set G : ℝ × ℝ → ℝ := fun p => iteratedDeriv m (F p.1) p.2
    have hG_fd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fderiv ℝ G p (0, 1)) (Ioi 0 ×ˢ univ) :=
      (ih.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
    refine hG_fd.congr fun p hp => ?_
    rw [iteratedDeriv_succ]
    have hdiff : DifferentiableAt ℝ G p :=
      (ih.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)
    have hpath : HasDerivAt (fun y : ℝ => (p.1, y)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt p.2 hpath).deriv

/-- Measurability of the piecewise extension of `iteratedDeriv m (F t) x` from `(0, ∞) × ℝ`. -/
private theorem measurable_piecewise_iteratedDeriv {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (Ioi 0 ×ˢ univ)) (m : ℕ) :
    Measurable (Function.uncurry fun t x : ℝ =>
      if 0 < t then iteratedDeriv m (F t) x else 0) := by
  classical
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hcont : ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv m (F p.1) p.2) (Ioi 0 ×ˢ univ) :=
    (contDiffOn_iteratedDeriv_snd hF m).continuousOn
  have hpw : (Function.uncurry fun t x : ℝ => if 0 < t then iteratedDeriv m (F t) x else 0) =
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).piecewise
        (fun p : ℝ × ℝ => iteratedDeriv m (F p.1) p.2) (fun _ => 0) := by
    ext ⟨t, x⟩
    simp [Set.piecewise]
  rw [hpw]
  exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet

/-- For `T > 0`, `ψ₀ ∈ C^∞(ℝ)`, and `F` jointly `C^∞` on `(0, ∞) × ℝ` with spatial derivatives
up to order `k` bounded by `M` on `[0, T] × ℝ`,
`iteratedDeriv k (lineDuhamel 1 ψ₀ F T) =
  lineDuhamel 1 (iteratedDeriv k ψ₀) (fun t => iteratedDeriv k (F t)) T`. -/
theorem iteratedDeriv_lineDuhamel_one {T : ℝ} (hT : 0 < T) {ψ₀ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hψ₀ : ContDiff ℝ ∞ ψ₀)
    (hF_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (Ioi 0 ×ˢ univ))
    (k : ℕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hψ_bd : ∀ m ≤ k, ∀ x : ℝ, |iteratedDeriv m ψ₀ x| ≤ M)
    (hF_bd : ∀ m ≤ k, ∀ t ∈ Icc 0 T, ∀ x : ℝ, |iteratedDeriv m (F t) x| ≤ M) :
    iteratedDeriv k (lineDuhamel 1 ψ₀ F T) =
      lineDuhamel 1 (iteratedDeriv k ψ₀) (fun t => iteratedDeriv k (F t)) T := by
  set F_pos : ℕ → ℝ → ℝ → ℝ := fun m t x => if 0 < t then iteratedDeriv m (F t) x else 0
  have hduhamel_eq : ∀ m : ℕ,
      lineDuhamel 1 (iteratedDeriv m ψ₀) (F_pos m) T =
        lineDuhamel 1 (iteratedDeriv m ψ₀) (fun t => iteratedDeriv m (F t)) T := by
    intro m
    funext η
    unfold lineDuhamel
    congr 1
    refine integral_congr_ae ?_
    rw [uIoc_of_le hT.le]
    refine Eventually.of_forall fun r hr => ?_
    have hr0 : 0 < r := hr.1
    have hfun : F_pos m r = iteratedDeriv m (F r) := by
      funext x
      simp [F_pos, hr0]
    rw [hfun]
  suffices hmain : iteratedDeriv k (lineDuhamel 1 ψ₀ (F_pos 0) T) =
      lineDuhamel 1 (iteratedDeriv k ψ₀) (F_pos k) T by
    have h0 : lineDuhamel 1 ψ₀ (F_pos 0) T = lineDuhamel 1 ψ₀ F T := by
      simpa [iteratedDeriv_zero] using hduhamel_eq 0
    rw [← h0, hmain, hduhamel_eq k]
  induction k with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih (fun m hm => hψ_bd m (Nat.le_succ_of_le hm))
      (fun m hm => hF_bd m (Nat.le_succ_of_le hm))]
    have hψk : ContDiff ℝ ∞ (iteratedDeriv k ψ₀) := contDiff_iteratedDeriv_of_top hψ₀ k
    have hψ_diff : ∀ η : ℝ,
        HasDerivAt (iteratedDeriv k ψ₀) (iteratedDeriv (k + 1) ψ₀ η) η := by
      intro η
      rw [iteratedDeriv_succ]
      exact (hψk.differentiable (by simp) η).hasDerivAt
    have hF_diff : ∀ r ∈ Icc 0 T, ∀ η : ℝ,
        HasDerivAt (F_pos k r) (F_pos (k + 1) r η) η := by
      intro r hr η
      by_cases hr0 : 0 < r
      · have hslice : ContDiff ℝ ∞ (F r) := by
          have hmap : ContDiff ℝ ∞ (fun x : ℝ => ((r, x) : ℝ × ℝ)) :=
            contDiff_const.prodMk contDiff_id
          exact contDiffOn_univ.1
            (hF_smooth.comp hmap.contDiffOn (fun x _ => ⟨hr0, mem_univ x⟩))
        have hfk : ContDiff ℝ ∞ (iteratedDeriv k (F r)) := contDiff_iteratedDeriv_of_top hslice k
        have hfun : F_pos k r = iteratedDeriv k (F r) := by funext x; simp [F_pos, hr0]
        have hval : F_pos (k + 1) r η = deriv (iteratedDeriv k (F r)) η := by
          simp [F_pos, hr0, iteratedDeriv_succ]
        rw [hfun, hval]
        exact (hfk.differentiable (by simp) η).hasDerivAt
      · have hfun : F_pos k r = fun _ => 0 := by funext x; simp [F_pos, hr0]
        have hval : F_pos (k + 1) r η = 0 := by simp [F_pos, hr0]
        rw [hfun, hval]
        exact hasDerivAt_const η 0
    have hFk_bd : ∀ r ∈ Icc 0 T, ∀ η : ℝ, |F_pos k r η| ≤ M := by
      intro r hr η
      by_cases hr0 : 0 < r
      · simpa [F_pos, hr0] using hF_bd k (Nat.le_succ k) r hr η
      · simpa [F_pos, hr0] using hM0
    have hFk1_bd : ∀ r ∈ Icc 0 T, ∀ η : ℝ, |F_pos (k + 1) r η| ≤ M := by
      intro r hr η
      by_cases hr0 : 0 < r
      · simpa [F_pos, hr0] using hF_bd (k + 1) le_rfl r hr η
      · simpa [F_pos, hr0] using hM0
    exact Heat.deriv_lineDuhamel one_pos hT hψ_diff
      (hψ_bd k (Nat.le_succ k)) (hψ_bd (k + 1) le_rfl)
      (measurable_piecewise_iteratedDeriv hF_smooth k)
      (measurable_piecewise_iteratedDeriv hF_smooth (k + 1))
      hF_diff hFk_bd hFk1_bd

/-- Joint measurability of `(Y, t) ↦ lineHeat (T - t) (g t) Y` when `g` is jointly measurable. -/
theorem stronglyMeasurable_lineHeat_uncurry {g : ℝ → ℝ → ℝ} (hgm : Measurable (Function.uncurry g))
    (T : ℝ) : StronglyMeasurable (fun x : ℝ × ℝ => lineHeat (T - x.2) (g x.2) x.1) := by
  have h1 : Measurable fun p : (ℝ × ℝ) × ℝ => Heat.lineGauss (T - p.1.2) p.2 :=
    Heat.measurable_lineGauss_uncurry.comp
      ((measurable_const.sub measurable_fst.snd).prodMk measurable_snd)
  have h2 : Measurable fun p : (ℝ × ℝ) × ℝ => g p.1.2 (p.1.1 - p.2) :=
    hgm.comp (measurable_fst.snd.prodMk (measurable_fst.fst.sub measurable_snd))
  exact (h1.mul h2).stronglyMeasurable.integral_prod_right'

/-- Interval integrability of `t ↦ lineHeat (T - t) (iteratedDeriv m (F t)) Y` on `[0, T]`. -/
theorem intervalIntegrable_lineHeat_iteratedDeriv {T : ℝ} (hT : 0 ≤ T) {F : ℝ → ℝ → ℝ}
    (hF_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (Ioi 0 ×ˢ univ))
    (m : ℕ) {M : ℝ} (hF_bd : ∀ t ∈ Icc 0 T, ∀ x : ℝ, |iteratedDeriv m (F t) x| ≤ M)
    (Y : ℝ) :
    IntervalIntegrable (fun t => lineHeat (T - t) (iteratedDeriv m (F t)) Y) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  set F_pos : ℝ → ℝ → ℝ := fun t x => if 0 < t then iteratedDeriv m (F t) x else 0
  have hsm : StronglyMeasurable (fun t => lineHeat (T - t) (F_pos t) Y) := by
    simpa [one_mul] using
      Heat.stronglyMeasurable_lineHeat_param (measurable_piecewise_iteratedDeriv hF_smooth m) 1 T Y
  have hae_eq : (fun t => lineHeat (T - t) (F_pos t) Y) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun t => lineHeat (T - t) (iteratedDeriv m (F t)) Y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hfun : F_pos t = iteratedDeriv m (F t) := by
      funext x
      simp [F_pos, ht.1]
    rw [hfun]
  have hfin : volume (Ioc 0 T) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hint_pos : IntegrableOn (fun t => lineHeat (T - t) (F_pos t) Y) (Ioc 0 T) volume :=
    Measure.integrableOn_of_bounded hfin hsm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => by
        have hfun : F_pos t = iteratedDeriv m (F t) := by funext x; simp [F_pos, ht.1]
        rw [hfun, Real.norm_eq_abs]
        exact Heat.abs_lineHeat_le (sub_nonneg.2 ht.2) (hF_bd t ⟨ht.1.le, ht.2⟩) Y))
  exact hint_pos.congr_fun_ae hae_eq

/-- Continuity of `lineHeat θ ψ` for `θ > 0` when `ψ ∈ C^∞(ℝ)` has bounded value and first
derivative. -/
theorem continuous_lineHeat_of_contDiff {θ : ℝ} (hθ : 0 < θ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {M : ℝ} (hψ0 : ∀ x : ℝ, |ψ x| ≤ M) (hψ1 : ∀ x : ℝ, |deriv ψ x| ≤ M) :
    Continuous (lineHeat θ ψ) :=
  continuous_iff_continuousAt.2 fun η =>
    (Heat.hasDerivAt_lineHeat_data hθ
      (fun x => (hψ.differentiable (by simp) x).hasDerivAt) hψ0 hψ1 η).continuousAt

/-- Joint a.e.-strong measurability of `(Y, t) ↦ lineHeat (T - t) (iteratedDeriv m (F t)) Y`
on `volume.prod (volume.restrict (Ioc a b))` for `0 ≤ a`. -/
theorem aestronglyMeasurable_lineHeat_iteratedDeriv_Ioc {T a b : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ → ℝ}
    (hF_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (Ioi 0 ×ˢ univ)) (m : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => lineHeat (T - p.2) (iteratedDeriv m (F p.2)) p.1)
      (volume.prod (volume.restrict (Ioc a b))) := by
  set F_pos : ℝ → ℝ → ℝ := fun t x => if 0 < t then iteratedDeriv m (F t) x else 0
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => lineHeat (T - p.2) (F_pos p.2) p.1) :=
    stronglyMeasurable_lineHeat_uncurry (measurable_piecewise_iteratedDeriv hF_smooth m) T
  have hae_snd : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Ioc a b))), p.2 ∈ Ioc a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  refine hsm.aestronglyMeasurable.congr ?_
  filter_upwards [hae_snd] with p hp
  have hp0 : 0 < p.2 := ha.trans_lt hp.1
  have hfun : F_pos p.2 = iteratedDeriv m (F p.2) := by
    funext x
    simp [F_pos, hp0]
  rw [hfun]

/-- Joint a.e.-strong measurability of `(Y, t) ↦ iteratedDeriv m (lineHeat (T - t) (F t)) Y`
on `volume.prod (volume.restrict (Ioc 0 b))` when `b < T` and spatial derivatives up to order `m`
are bounded on `[0, b] × ℝ`. -/
theorem aestronglyMeasurable_iteratedDeriv_lineHeat_Ioc {T b : ℝ} (hbT : b < T) {F : ℝ → ℝ → ℝ}
    (hF_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (Ioi 0 ×ˢ univ))
    (m : ℕ) {M : ℝ} (hF_bd : ∀ t ∈ Ioc 0 b, ∀ k ≤ m, ∀ x : ℝ, |iteratedDeriv k (F t) x| ≤ M) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => iteratedDeriv m (lineHeat (T - p.2) (F p.2)) p.1)
      (volume.prod (volume.restrict (Ioc 0 b))) := by
  have hsm := aestronglyMeasurable_lineHeat_iteratedDeriv_Ioc (T := T) (a := 0) (b := b)
    le_rfl hF_smooth m
  have hae_snd : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Ioc 0 b))), p.2 ∈ Ioc 0 b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  refine hsm.congr ?_
  filter_upwards [hae_snd] with p hp
  have hθ : 0 < T - p.2 := sub_pos.2 (hp.2.trans_lt hbT)
  have hslice : ContDiff ℝ ∞ (F p.2) := by
    have hmap : ContDiff ℝ ∞ (fun x : ℝ => ((p.2, x) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1
      (hF_smooth.comp hmap.contDiffOn (fun x _ => ⟨hp.1, mem_univ x⟩))
  exact (congr_fun (iteratedDeriv_lineHeat_data hθ hslice m (hF_bd p.2 hp)) p.1).symm

/-! ### 2. Kernel derivatives of `lineGauss` and the 1D heat generator identity -/

private def lineGaussD1 (θ η : ℝ) : ℝ := -(η / (2 * θ)) * lineGauss θ η

private def lineGaussD2 (θ η : ℝ) : ℝ :=
  (η ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) * lineGauss θ η

private theorem lineGaussD2_eq_gaussDt (θ η : ℝ) :
    lineGaussD2 θ η = gaussDt 1 θ (lineIso η) := by
  unfold lineGaussD2 gaussDt
  rw [Heat.lineGauss_eq, Heat.norm_lineIso, sq_abs, Nat.cast_one]

private theorem hasDerivAt_lineGauss_eta {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasDerivAt (lineGauss θ) (lineGaussD1 θ η) η := by
  have harg : HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * θ)) (-(η / (2 * θ))) η := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * η) η := by
      simpa using hasDerivAt_pow 2 η
    have h2 := h1.neg.div_const (4 * θ)
    refine h2.congr_deriv ?_
    field_simp [hθ.ne']
    ring
  have h := harg.exp.const_mul ((4 * Real.pi * θ) ^ (-(1 : ℝ) / 2))
  unfold lineGaussD1 lineGauss
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_lineGaussD1_eta {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasDerivAt (lineGaussD1 θ) (lineGaussD2 θ η) η := by
  have hfun : lineGaussD1 θ = fun x : ℝ => (-(2 * θ)⁻¹ * x) * lineGauss θ x := by
    funext x
    unfold lineGaussD1
    ring
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => -(2 * θ)⁻¹ * x) (-(2 * θ)⁻¹ * 1) η :=
    (hasDerivAt_id η).const_mul (-(2 * θ)⁻¹)
  refine (hlin.mul (hasDerivAt_lineGauss_eta hθ η)).congr_deriv ?_
  unfold lineGaussD1 lineGaussD2
  field_simp [hθ.ne']
  ring

private theorem hasDerivAt_lineGauss_time {θ : ℝ} (hθ : 0 < θ) (η : ℝ) :
    HasDerivAt (fun s : ℝ => lineGauss s η) (lineGaussD2 θ η) θ := by
  rw [lineGaussD2_eq_gaussDt]
  have h := Heat.hasDerivAt_gaussKernel_time (d := 1) hθ (lineIso η)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => Heat.lineGauss_eq s η)

private theorem abs_lineGauss_Gaussian_le {θ : ℝ} (hθ : 0 < θ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η : ℝ,
      |lineGauss θ η| ≤ A * Real.exp (-(1 / (16 * θ)) * η ^ 2) ∧
      |lineGaussD1 θ η| ≤ A * Real.exp (-(1 / (16 * θ)) * η ^ 2) ∧
      |lineGaussD2 θ η| ≤ A * Real.exp (-(1 / (16 * θ)) * η ^ 2) := by
  obtain ⟨A₂, hA₂0, hA₂⟩ := Heat.abs_gaussDt_le (d := 1) hθ
  obtain ⟨C₁, hC₁0, hC₁⟩ := Heat.abs_pow_mul_iteratedDeriv_lineGauss_le 1 0
  set B₀ : ℝ := (4 * Real.pi * θ) ^ (-(1 : ℝ) / 2)
  set B₁ : ℝ := (2 * θ)⁻¹ * (C₁ * θ ^ ((((1 : ℕ) : ℝ) - (0 : ℕ)) / 2) *
    (4 * Real.pi * (4 * θ)) ^ (-(1 : ℝ) / 2))
  refine ⟨B₀ + B₁ + A₂, by positivity, fun η => ?_⟩
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hB₁0 : 0 ≤ B₁ := by dsimp [B₁]; positivity
  have hA_ge₀ : B₀ ≤ B₀ + B₁ + A₂ := by linarith
  have hA_ge₁ : B₁ ≤ B₀ + B₁ + A₂ := by linarith
  have hA_ge₂ : A₂ ≤ B₀ + B₁ + A₂ := by linarith
  have hexp_mono : Real.exp (-η ^ 2 / (4 * θ)) ≤ Real.exp (-(1 / (16 * θ)) * η ^ 2) := by
    apply Real.exp_le_exp.mpr
    have : 1 / (16 * θ) * η ^ 2 ≤ η ^ 2 / (4 * θ) := by
      rw [div_mul_eq_mul_div, one_mul]
      exact div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) (by linarith)
    rw [neg_div, neg_mul]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg (Heat.lineGauss_nonneg hθ η)]
    unfold lineGauss
    calc B₀ * Real.exp (-η ^ 2 / (4 * θ))
        ≤ B₀ * Real.exp (-(1 / (16 * θ)) * η ^ 2) :=
          mul_le_mul_of_nonneg_left hexp_mono hB₀0
      _ ≤ (B₀ + B₁ + A₂) * Real.exp (-(1 / (16 * θ)) * η ^ 2) :=
          mul_le_mul_of_nonneg_right hA_ge₀ (Real.exp_pos _).le
  · unfold lineGaussD1
    rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * θ),
      abs_of_nonneg (Heat.lineGauss_nonneg hθ η)]
    have h1 := hC₁ hθ η
    rw [pow_one, iteratedDeriv_zero, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ η)] at h1
    have h4 : lineGauss (4 * θ) η =
        (4 * Real.pi * (4 * θ)) ^ (-(1 : ℝ) / 2) * Real.exp (-(1 / (16 * θ)) * η ^ 2) := by
      unfold lineGauss
      congr 2
      ring
    calc |η| / (2 * θ) * lineGauss θ η
        = (2 * θ)⁻¹ * (|η| * lineGauss θ η) := by ring
      _ ≤ (2 * θ)⁻¹ * (C₁ * θ ^ ((((1 : ℕ) : ℝ) - (0 : ℕ)) / 2) * lineGauss (4 * θ) η) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B₁ * Real.exp (-(1 / (16 * θ)) * η ^ 2) := by rw [h4]; dsimp [B₁]; ring
      _ ≤ (B₀ + B₁ + A₂) * Real.exp (-(1 / (16 * θ)) * η ^ 2) :=
          mul_le_mul_of_nonneg_right hA_ge₁ (Real.exp_pos _).le
  · rw [lineGaussD2_eq_gaussDt]
    have h2 := hA₂ θ (by linarith) (by linarith) (lineIso η)
    rw [Heat.norm_lineIso, sq_abs] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right hA_ge₂ (Real.exp_pos _).le)

/-- Differentiation under the integral on the kernel side for a Gaussian-bounded kernel `K`. -/
private theorem hasDerivAt_kconv_gauss {K K' f : ℝ → ℝ} {A b M : ℝ}
    (hb : 0 < b) (hM0 : 0 ≤ M) (hKc : Continuous K) (hK'c : Continuous K') (hfc : Continuous f)
    (hK_diff : ∀ z : ℝ, HasDerivAt K (K' z) z)
    (hK_bd : ∀ z : ℝ, |K z| ≤ A * Real.exp (-b * z ^ 2))
    (hK'_bd : ∀ z : ℝ, |K' z| ≤ A * Real.exp (-b * z ^ 2))
    (hf_bd : ∀ z : ℝ, |f z| ≤ M) (Y : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ ξ : ℝ, K (y - ξ) * f ξ)
      (∫ ξ : ℝ, K' (Y - ξ) * f ξ) Y := by
  have hA0 : 0 ≤ A := by
    have := (abs_nonneg (K 0)).trans (hK_bd 0)
    simpa using this
  set C : ℝ := A * Real.exp (b * (|Y| + 1) ^ 2) * M
  have hshift_exp : ∀ y ∈ Ioo (Y - 1) (Y + 1), ∀ ξ : ℝ,
      Real.exp (-b * (y - ξ) ^ 2) ≤ Real.exp (b * (|Y| + 1) ^ 2) * Real.exp (-(b / 2) * ξ ^ 2) := by
    intro y hy ξ
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hy_abs : |y| ≤ |Y| + 1 := by
      rw [abs_le]
      have hY := le_abs_self Y
      have hY' := neg_abs_le Y
      constructor <;> linarith [hy.1, hy.2]
    have hy_sq : y ^ 2 ≤ (|Y| + 1) ^ 2 := by
      rw [← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg y) hy_abs 2
    have hquad : ξ ^ 2 / 2 - y ^ 2 ≤ (y - ξ) ^ 2 := by
      have hsq : 0 ≤ (ξ - 2 * y) ^ 2 := sq_nonneg _
      linarith [show (ξ - 2 * y) ^ 2 = 2 * (y - ξ) ^ 2 + 2 * y ^ 2 - ξ ^ 2 by ring]
    nlinarith
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun ξ : ℝ => K (y - ξ) * f ξ) volume :=
    fun y => ((hKc.comp (continuous_const.sub continuous_id)).mul hfc).aestronglyMeasurable
  have hint_Y : Integrable (fun ξ : ℝ => K (Y - ξ) * f ξ) volume := by
    have hdom : Integrable (fun ξ : ℝ => C * Real.exp (-(b / 2) * ξ ^ 2)) volume :=
      (integrable_exp_neg_mul_sq (half_pos hb)).const_mul C
    refine hdom.mono' (hmeas Y) (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hY_in : Y ∈ Ioo (Y - 1) (Y + 1) := ⟨by linarith, by linarith⟩
    calc |K (Y - ξ)| * |f ξ|
        ≤ (A * Real.exp (-b * (Y - ξ) ^ 2)) * M :=
          mul_le_mul (hK_bd _) (hf_bd _) (abs_nonneg _) (by positivity)
      _ ≤ (A * (Real.exp (b * (|Y| + 1) ^ 2) * Real.exp (-(b / 2) * ξ ^ 2))) * M :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hshift_exp Y hY_in ξ) hA0) hM0
      _ = C * Real.exp (-(b / 2) * ξ ^ 2) := by dsimp [C]; ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun y ξ => K (y - ξ) * f ξ)
    (F' := fun y ξ => K' (y - ξ) * f ξ)
    (bound := fun ξ => C * Real.exp (-(b / 2) * ξ ^ 2))
    (x₀ := Y) (s := Ioo (Y - 1) (Y + 1)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall hmeas)
    hint_Y
    (((hK'c.comp (continuous_const.sub continuous_id)).mul hfc).aestronglyMeasurable)
    (Eventually.of_forall fun ξ y hy => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |K' (y - ξ)| * |f ξ|
          ≤ (A * Real.exp (-b * (y - ξ) ^ 2)) * M :=
            mul_le_mul (hK'_bd _) (hf_bd _) (abs_nonneg _) (by positivity)
        _ ≤ (A * (Real.exp (b * (|Y| + 1) ^ 2) * Real.exp (-(b / 2) * ξ ^ 2))) * M :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hshift_exp y hy ξ) hA0) hM0
        _ = C * Real.exp (-(b / 2) * ξ ^ 2) := by dsimp [C]; ring)
    ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul C)
    (Eventually.of_forall fun ξ y _ => by
      have h1 : HasDerivAt (fun z : ℝ => z - ξ) 1 y := (hasDerivAt_id y).sub_const ξ
      have h2 := (hK_diff (y - ξ)).comp y h1
      rw [mul_one] at h2
      exact h2.mul_const (f ξ))).2

/-- **1D Heat Generator Identity**: for `θ > 0` and `f ∈ C²(ℝ)` with `f, f', f''` bounded by `M`,
`∫ ξ, lineGaussD2 θ ξ * f (Y - ξ) = lineHeat θ (deriv (deriv f)) Y`. -/
theorem integral_lineGaussD2_mul_eq {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {M : ℝ} (hM0 : 0 ≤ M)
    (hb0 : ∀ x : ℝ, |f x| ≤ M) (hb1 : ∀ x : ℝ, |deriv f x| ≤ M)
    (hb2 : ∀ x : ℝ, |deriv (deriv f) x| ≤ M) (Y : ℝ) :
    (∫ ξ : ℝ, lineGaussD2 θ ξ * f (Y - ξ)) = lineHeat θ (deriv (deriv f)) Y := by
  obtain ⟨A, _, hA⟩ := abs_lineGauss_Gaussian_le hθ
  have hb : 0 < 1 / (16 * θ) := by positivity
  have hK0c : Continuous (lineGauss θ) := Heat.continuous_lineGauss θ
  have hK1c : Continuous (lineGaussD1 θ) := by
    unfold lineGaussD1
    exact (continuous_id.div_const (2 * θ)).neg.mul hK0c
  have hK2c : Continuous (lineGaussD2 θ) := by
    have hfun : lineGaussD2 θ = fun η => gaussDt 1 θ (lineIso η) :=
      funext (lineGaussD2_eq_gaussDt θ)
    rw [hfun]
    exact (Heat.continuous_gaussDt 1 θ).comp lineIso.continuous
  have hd_ker1 : ∀ y : ℝ,
      deriv (lineHeat θ f) y = ∫ ξ : ℝ, lineGaussD1 θ (y - ξ) * f ξ := by
    intro y
    have h := hasDerivAt_kconv_gauss hb hM0 hK0c hK1c hf.continuous
      (hasDerivAt_lineGauss_eta hθ) (fun z => (hA z).1) (fun z => (hA z).2.1) hb0 y
    have heq : (fun y' : ℝ => ∫ ξ : ℝ, lineGauss θ (y' - ξ) * f ξ) = lineHeat θ f :=
      funext fun y' => (Heat.lineHeat_eq_conv θ f y').symm
    rw [heq] at h
    exact h.deriv
  have hd_ker2 : deriv (deriv (lineHeat θ f)) Y =
      ∫ ξ : ℝ, lineGaussD2 θ (Y - ξ) * f ξ := by
    have h := hasDerivAt_kconv_gauss hb hM0 hK1c hK2c hf.continuous
      (hasDerivAt_lineGaussD1_eta hθ) (fun z => (hA z).2.1) (fun z => (hA z).2.2) hb0 Y
    rw [← funext hd_ker1] at h
    exact h.deriv
  have hd_data1 : deriv (lineHeat θ f) = lineHeat θ (deriv f) := by
    funext y
    exact (Heat.hasDerivAt_lineHeat_data hθ
      (fun η => (hf.differentiable (by simp) η).hasDerivAt) hb0 hb1 y).deriv
  have hd_data2 : deriv (deriv (lineHeat θ f)) Y = lineHeat θ (deriv (deriv f)) Y := by
    rw [hd_data1]
    exact (Heat.hasDerivAt_lineHeat_data hθ
      (fun η => ((contDiff_deriv_of_top hf).differentiable (by simp) η).hasDerivAt) hb1 hb2 Y).deriv
  have hsub : (∫ ξ : ℝ, lineGaussD2 θ ξ * f (Y - ξ)) =
      ∫ ξ : ℝ, lineGaussD2 θ (Y - ξ) * f ξ := by
    rw [← integral_sub_left_eq_self (fun ξ => lineGaussD2 θ (Y - ξ) * f ξ) volume Y]
    simp only [sub_sub_cancel]
  rw [hsub, ← hd_ker2, hd_data2]

/-! ### 3. Approximate identity and Duhamel formula on `[0, T]` -/

/-- Quantitative approximate-identity bound: if `f` is differentiable on `ℝ` with `|deriv f| ≤ M`,
then for all `θ > 0` and `Y : ℝ`, `|lineHeat θ f Y - f Y| ≤ M * C * θ ^ (1 / 2)`. -/
private theorem exists_abs_lineHeat_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {θ : ℝ}, 0 < θ → ∀ {f : ℝ → ℝ} {M : ℝ},
      0 ≤ M → (∀ x : ℝ, |f x| ≤ M) → Differentiable ℝ f → (∀ x : ℝ, |deriv f x| ≤ M) →
      ∀ Y : ℝ, |lineHeat θ f Y - f Y| ≤ M * C * θ ^ ((1 : ℝ) / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Heat.abs_pow_mul_iteratedDeriv_lineGauss_le 1 0
  refine ⟨C₁, hC₁0.le, fun {θ} hθ {f} {M} hM0 hf0 hfd hf1 Y => ?_⟩
  have h1 : lineHeat θ f Y - f Y = ∫ ξ : ℝ, lineGauss θ ξ * (f (Y - ξ) - f Y) := by
    have hint1 : Integrable (fun ξ : ℝ => lineGauss θ ξ * f (Y - ξ)) volume := by
      refine ((Heat.integrable_lineGauss hθ).mul_const M).mono'
        ((Heat.continuous_lineGauss θ).mul
          (hfd.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun ξ => by
          rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hf0 _) (Heat.lineGauss_nonneg hθ ξ))
    have hint2 : Integrable (fun ξ : ℝ => lineGauss θ ξ * f Y) volume :=
      (Heat.integrable_lineGauss hθ).mul_const (f Y)
    calc lineHeat θ f Y - f Y
        = (∫ ξ : ℝ, lineGauss θ ξ * f (Y - ξ)) - (∫ ξ : ℝ, lineGauss θ ξ) * f Y := by
          rw [Heat.integral_lineGauss hθ, one_mul]; rfl
      _ = (∫ ξ : ℝ, lineGauss θ ξ * f (Y - ξ)) - ∫ ξ : ℝ, lineGauss θ ξ * f Y := by
          rw [MeasureTheory.integral_mul_const]
      _ = ∫ ξ : ℝ, (lineGauss θ ξ * f (Y - ξ) - lineGauss θ ξ * f Y) :=
          (integral_sub hint1 hint2).symm
      _ = ∫ ξ : ℝ, lineGauss θ ξ * (f (Y - ξ) - f Y) := by
          refine integral_congr_ae (Eventually.of_forall fun ξ => by ring)
  rw [h1, ← Real.norm_eq_abs]
  have hdom : Integrable (fun ξ : ℝ => (M * C₁ * θ ^ ((1 : ℝ) / 2)) * lineGauss (4 * θ) ξ) volume :=
    (Heat.integrable_lineGauss (by positivity)).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hdom (Eventually.of_forall fun ξ => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ ξ)]
    have hmvt : ‖f (Y - ξ) - f Y‖ ≤ M * ‖(Y - ξ) - Y‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun _ _ => hfd _)
        (fun x _ => by rw [Real.norm_eq_abs]; exact hf1 x) convex_univ (mem_univ _) (mem_univ _)
    rw [sub_sub_cancel_left, norm_neg, Real.norm_eq_abs] at hmvt
    have hker := hC₁ hθ ξ
    rw [pow_one, iteratedDeriv_zero, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ ξ)] at hker
    have hexp : (((1 : ℕ) : ℝ) - (0 : ℕ)) / 2 = (1 : ℝ) / 2 := by norm_num
    rw [hexp] at hker
    calc lineGauss θ ξ * ‖f (Y - ξ) - f Y‖
        ≤ lineGauss θ ξ * (M * |ξ|) :=
          mul_le_mul_of_nonneg_left hmvt (Heat.lineGauss_nonneg hθ ξ)
      _ = M * (|ξ| * lineGauss θ ξ) := by ring
      _ ≤ M * (C₁ * θ ^ ((1 : ℝ) / 2) * lineGauss (4 * θ) ξ) :=
          mul_le_mul_of_nonneg_left hker hM0
      _ = (M * C₁ * θ ^ ((1 : ℝ) / 2)) * lineGauss (4 * θ) ξ := by ring
  · rw [MeasureTheory.integral_const_mul, Heat.integral_lineGauss (by positivity), mul_one]

/-- Time derivative of `t ↦ lineHeat (T - t) (u t) Y` at `t₀ ∈ (0, T)`. -/
private theorem hasDerivAt_lineHeat_duhamel_step {u F : ℝ → ℝ → ℝ} {T M : ℝ}
    (hu_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (Ici 0 ×ˢ univ))
    (hM0 : 0 ≤ M)
    (hb0 : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |u t Y| ≤ M)
    (hb1 : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (u t) Y| ≤ M)
    (hb2 : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (deriv (u t)) Y| ≤ M)
    (hbt : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (fun r => u r Y) t| ≤ M)
    (hpde : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, deriv (fun r => u r Y) t - deriv (deriv (u t)) Y = F t Y)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) (Y : ℝ) :
    HasDerivAt (fun t : ℝ => lineHeat (T - t) (u t) Y)
      (lineHeat (T - t₀) (F t₀) Y) t₀ := by
  set θ₀ : ℝ := T - t₀
  have hθ₀ : 0 < θ₀ := sub_pos.2 ht₀.2
  obtain ⟨A₂, hA₂0, hA₂⟩ := Heat.abs_gaussDt_le (d := 1) hθ₀
  set B₀ : ℝ := (2 * Real.pi * θ₀) ^ (-(1 : ℝ) / 2)
  set s_nhd : Set ℝ := Ioo (max 0 (T - 2 * θ₀)) (T - θ₀ / 2)
  have hs_mem : s_nhd ∈ 𝓝 t₀ := by
    refine Ioo_mem_nhds (max_lt ht₀.1 ?_) ?_
    · dsimp [θ₀]; linarith
    · dsimp [θ₀]; linarith
  have hs_sub : ∀ t ∈ s_nhd, t ∈ Ioo 0 T ∧ T - t ∈ Ioo (θ₀ / 2) (2 * θ₀) := by
    intro t ht
    have ht1 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have ht2 : T - 2 * θ₀ < t := lt_of_le_of_lt (le_max_right _ _) ht.1
    have ht3 : t < T - θ₀ / 2 := ht.2
    refine ⟨⟨ht1, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hu_open : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hu_smooth.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hut_diff : ∀ t > 0, ∀ z : ℝ,
      HasDerivAt (fun r : ℝ => u r z) (deriv (fun r => u r z) t) t := by
    intro t ht z
    have hmem : ((t, z) : ℝ × ℝ) ∈ Ioi 0 ×ˢ univ := ⟨ht, mem_univ z⟩
    have hd : DifferentiableAt ℝ (fun x : ℝ × ℝ => u x.1 x.2) (t, z) :=
      (hu_open.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))).differentiableAt.hasDerivAt
  let F_int : ℝ → ℝ → ℝ := fun t ξ => lineGauss (T - t) ξ * u t (Y - ξ)
  let F_der : ℝ → ℝ → ℝ := fun t ξ =>
    -lineGaussD2 (T - t) ξ * u t (Y - ξ) +
      lineGauss (T - t) ξ * deriv (fun r => u r (Y - ξ)) t
  let bound : ℝ → ℝ := fun ξ =>
    (A₂ + B₀) * M * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2)
  have hu_slice : ∀ t ≥ 0, ContDiff ℝ ∞ (u t) := by
    intro t ht
    have hmap : ContDiff ℝ ∞ (fun z : ℝ => ((t, z) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1 (hu_smooth.comp hmap.contDiffOn (fun z _ => ⟨ht, mem_univ z⟩))
  have hmeas_F : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F_int t) volume := by
    filter_upwards [hs_mem] with t ht
    have ht_pos : 0 ≤ t := (hs_sub t ht).1.1.le
    exact ((Heat.continuous_lineGauss (T - t)).mul
      ((hu_slice t ht_pos).continuous.comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hint_t₀ : Integrable (F_int t₀) volume := by
    refine ((Heat.integrable_lineGauss hθ₀).mul_const M).mono'
      (((Heat.continuous_lineGauss θ₀).mul
        ((hu_slice t₀ ht₀.1.le).continuous.comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ₀ ξ), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb0 t₀ ⟨ht₀.1.le, ht₀.2.le⟩ _) (Heat.lineGauss_nonneg hθ₀ ξ)
  have hK2c : Continuous (lineGaussD2 θ₀) := by
    have hfun : lineGaussD2 θ₀ = fun η => gaussDt 1 θ₀ (lineIso η) :=
      funext (lineGaussD2_eq_gaussDt θ₀)
    rw [hfun]
    exact (Heat.continuous_gaussDt 1 θ₀).comp lineIso.continuous
  have hut₀_cont : Continuous (fun z : ℝ => deriv (fun r => u r z) t₀) := by
    have hfd : ContinuousOn
        (fun x : ℝ × ℝ => fderiv ℝ (fun y : ℝ × ℝ => u y.1 y.2) x (1, 0))
        (Ioi 0 ×ˢ univ) :=
      (hu_open.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply continuousOn_const
    have hslice : Continuous (fun z : ℝ =>
        fderiv ℝ (fun y : ℝ × ℝ => u y.1 y.2) (t₀, z) (1, 0)) :=
      hfd.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => ⟨ht₀.1, mem_univ z⟩)
    refine hslice.congr fun z => ?_
    have hmem : ((t₀, z) : ℝ × ℝ) ∈ Ioi 0 ×ˢ univ := ⟨ht₀.1, mem_univ z⟩
    have hd : DifferentiableAt ℝ (fun x : ℝ × ℝ => u x.1 x.2) (t₀, z) :=
      (hu_open.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt t₀
      ((hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ z))).deriv.symm
  have hmeas_F' : AEStronglyMeasurable (F_der t₀) volume := by
    refine AEStronglyMeasurable.add ?_ ?_
    · exact (hK2c.neg.mul
        ((hu_slice t₀ ht₀.1.le).continuous.comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable
    · exact ((Heat.continuous_lineGauss θ₀).mul
        (hut₀_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hbd_F' : ∀ ξ : ℝ, ∀ t ∈ s_nhd, ‖F_der t ξ‖ ≤ bound ξ := by
    intro ξ t ht
    obtain ⟨htIoo, hθIoo⟩ := hs_sub t ht
    have htIcc : t ∈ Icc 0 T := ⟨htIoo.1.le, htIoo.2.le⟩
    have hθ_pos : 0 < T - t := by linarith [hθIoo.1]
    have h1 : |lineGaussD2 (T - t) ξ| ≤ A₂ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by
      rw [lineGaussD2_eq_gaussDt]
      have h := hA₂ (T - t) hθIoo.1 hθIoo.2 (lineIso ξ)
      rwa [Heat.norm_lineIso, sq_abs] at h
    have h2 : |lineGauss (T - t) ξ| ≤ B₀ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by
      rw [abs_of_nonneg (Heat.lineGauss_nonneg hθ_pos ξ)]
      unfold lineGauss
      have hpre : (4 * Real.pi * (T - t)) ^ (-(1 : ℝ) / 2) ≤ B₀ :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by nlinarith [Real.pi_pos, hθIoo.1]) (by norm_num)
      have hexp : Real.exp (-ξ ^ 2 / (4 * (T - t))) ≤ Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by
        apply Real.exp_le_exp.mpr
        have : 1 / (16 * θ₀) * ξ ^ 2 ≤ ξ ^ 2 / (4 * (T - t)) := by
          rw [div_mul_eq_mul_div, one_mul]
          exact div_le_div_of_nonneg_left (sq_nonneg ξ) (by positivity) (by linarith [hθIoo.2])
        rw [neg_div, neg_mul]
        linarith
      exact mul_le_mul hpre hexp (Real.exp_pos _).le (by positivity)
    calc ‖F_der t ξ‖
        ≤ ‖-lineGaussD2 (T - t) ξ * u t (Y - ξ)‖ +
            ‖lineGauss (T - t) ξ * deriv (fun r => u r (Y - ξ)) t‖ := norm_add_le _ _
      _ = |lineGaussD2 (T - t) ξ| * |u t (Y - ξ)| +
            |lineGauss (T - t) ξ| * |deriv (fun r => u r (Y - ξ)) t| := by
          simp [norm_mul, Real.norm_eq_abs]
      _ ≤ (A₂ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2)) * M +
            (B₀ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2)) * M :=
          add_le_add
            (mul_le_mul h1 (hb0 t htIcc _) (abs_nonneg _) (by positivity))
            (mul_le_mul h2 (hbt t htIcc _) (abs_nonneg _) (by positivity))
      _ = bound ξ := by dsimp [bound]; ring
  have hdiff_F : ∀ ξ : ℝ, ∀ t ∈ s_nhd, HasDerivAt (fun r => F_int r ξ) (F_der t ξ) t := by
    intro ξ t ht
    obtain ⟨htIoo, hθIoo⟩ := hs_sub t ht
    have hθ_pos : 0 < T - t := by linarith [hθIoo.1]
    have hsub : HasDerivAt (fun r : ℝ => T - r) (0 - 1) t :=
      (hasDerivAt_const t T).sub (hasDerivAt_id t)
    have hker : HasDerivAt (fun r : ℝ => lineGauss (T - r) ξ) (-lineGaussD2 (T - t) ξ) t := by
      have h := (hasDerivAt_lineGauss_time hθ_pos ξ).comp t hsub
      exact h.congr_deriv (by ring)
    exact hker.mul (hut_diff t htIoo.1 (Y - ξ))
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F_int) (F' := F_der) (bound := bound) (x₀ := t₀) (s := s_nhd) hs_mem
    hmeas_F hint_t₀ hmeas_F' (Eventually.of_forall hbd_F')
    ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (16 * θ₀))).const_mul ((A₂ + B₀) * M))
    (Eventually.of_forall hdiff_F)).2
  refine hmain.congr_deriv ?_
  have hint1 : Integrable (fun ξ : ℝ => -lineGaussD2 θ₀ ξ * u t₀ (Y - ξ)) volume := by
    refine ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (16 * θ₀))).const_mul (A₂ * M)).mono'
      (hK2c.neg.mul
        ((hu_slice t₀ ht₀.1.le).continuous.comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |lineGaussD2 θ₀ ξ| ≤ A₂ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by
      rw [lineGaussD2_eq_gaussDt]
      have h := hA₂ θ₀ (by linarith) (by linarith) (lineIso ξ)
      rwa [Heat.norm_lineIso, sq_abs] at h
    calc |lineGaussD2 θ₀ ξ| * |u t₀ (Y - ξ)|
        ≤ (A₂ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2)) * M :=
          mul_le_mul h1 (hb0 t₀ ⟨ht₀.1.le, ht₀.2.le⟩ _) (abs_nonneg _) (by positivity)
      _ = A₂ * M * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by ring
  have hint2 : Integrable (fun ξ : ℝ => lineGauss θ₀ ξ * deriv (fun r => u r (Y - ξ)) t₀) volume := by
    refine ((Heat.integrable_lineGauss hθ₀).mul_const M).mono'
      ((Heat.continuous_lineGauss θ₀).mul
        (hut₀_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ₀ ξ), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbt t₀ ⟨ht₀.1.le, ht₀.2.le⟩ _) (Heat.lineGauss_nonneg hθ₀ ξ)
  have hint3 : Integrable (fun ξ : ℝ => lineGauss θ₀ ξ * deriv (deriv (u t₀)) (Y - ξ)) volume := by
    refine ((Heat.integrable_lineGauss hθ₀).mul_const M).mono'
      ((Heat.continuous_lineGauss θ₀).mul
        (((contDiff_deriv_of_top (contDiff_deriv_of_top (hu_slice t₀ ht₀.1.le)))).continuous.comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ₀ ξ), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb2 t₀ ⟨ht₀.1.le, ht₀.2.le⟩ _) (Heat.lineGauss_nonneg hθ₀ ξ)
  have hgen := integral_lineGaussD2_mul_eq hθ₀ (hu_slice t₀ ht₀.1.le) hM0
    (hb0 t₀ ⟨ht₀.1.le, ht₀.2.le⟩) (hb1 t₀ ⟨ht₀.1.le, ht₀.2.le⟩)
    (hb2 t₀ ⟨ht₀.1.le, ht₀.2.le⟩) Y
  calc ∫ ξ : ℝ, F_der t₀ ξ
      = (∫ ξ : ℝ, -lineGaussD2 θ₀ ξ * u t₀ (Y - ξ)) +
          ∫ ξ : ℝ, lineGauss θ₀ ξ * deriv (fun r => u r (Y - ξ)) t₀ :=
        integral_add hint1 hint2
    _ = -(∫ ξ : ℝ, lineGaussD2 θ₀ ξ * u t₀ (Y - ξ)) +
          ∫ ξ : ℝ, lineGauss θ₀ ξ * deriv (fun r => u r (Y - ξ)) t₀ := by
        simp_rw [neg_mul, MeasureTheory.integral_neg]
    _ = -lineHeat θ₀ (deriv (deriv (u t₀))) Y +
          ∫ ξ : ℝ, lineGauss θ₀ ξ * deriv (fun r => u r (Y - ξ)) t₀ := by
        rw [hgen]
    _ = (∫ ξ : ℝ, lineGauss θ₀ ξ * deriv (fun r => u r (Y - ξ)) t₀) -
          ∫ ξ : ℝ, lineGauss θ₀ ξ * deriv (deriv (u t₀)) (Y - ξ) := by
        unfold lineHeat; ring
    _ = ∫ ξ : ℝ, (lineGauss θ₀ ξ * deriv (fun r => u r (Y - ξ)) t₀ -
          lineGauss θ₀ ξ * deriv (deriv (u t₀)) (Y - ξ)) :=
        (integral_sub hint2 hint3).symm
    _ = lineHeat θ₀ (F t₀) Y := by
        unfold lineHeat
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [← mul_sub, hpde t₀ ⟨ht₀.1.le, ht₀.2.le⟩ (Y - ξ)]

/-- **1D Heat Duhamel Formula for Classical Solutions**: if `u : ℝ → ℝ → ℝ` is `C^∞` on `[0, ∞) × ℝ`
with `u, ∂_Y u, ∂_Y² u, ∂_t u` bounded by `M` on `[0, T] × ℝ` and solves `∂_t u - ∂_Y² u = F`,
then `u T Y = lineDuhamel 1 (u 0) F T Y`. -/
theorem lineHeat_duhamel_of_pde {u F : ℝ → ℝ → ℝ} {T M : ℝ} (hT : 0 < T)
    (hu_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (Ici 0 ×ˢ univ))
    (hut_diff : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, DifferentiableAt ℝ (fun r => u r Y) t)
    (hM0 : 0 ≤ M)
    (hb0 : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |u t Y| ≤ M)
    (hb1 : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (u t) Y| ≤ M)
    (hb2 : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (deriv (u t)) Y| ≤ M)
    (hbt : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (fun r => u r Y) t| ≤ M)
    (hpde : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, deriv (fun r => u r Y) t - deriv (deriv (u t)) Y = F t Y)
    (Y : ℝ) :
    u T Y = lineDuhamel 1 (u 0) F T Y := by
  set Φ : ℝ → ℝ := fun t => if t < T then lineHeat (T - t) (u t) Y else u T Y
  have hu_slice : ∀ t ≥ 0, ContDiff ℝ ∞ (u t) := by
    intro t ht
    have hmap : ContDiff ℝ ∞ (fun z : ℝ => ((t, z) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1 (hu_smooth.comp hmap.contDiffOn (fun z _ => ⟨ht, mem_univ z⟩))
  have hut_mvt : ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ z : ℝ,
      |u t₁ z - u t₂ z| ≤ M * |t₁ - t₂| := by
    intro t₁ ht₁ t₂ ht₂ z
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc 0 T)
      (fun r hr => hut_diff r hr z)
      (fun r hr => by rw [Real.norm_eq_abs]; exact hbt r hr z)
      (convex_Icc 0 T) ht₂ ht₁
    simpa [Real.norm_eq_abs] using h
  have hlineHeat_sub_u : ∀ {θ : ℝ}, 0 < θ → ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T,
      |lineHeat θ (u t₁) Y - lineHeat θ (u t₂) Y| ≤ M * |t₁ - t₂| := by
    intro θ hθ t₁ ht₁ t₂ ht₂
    have hint1 : Integrable (fun ξ : ℝ => lineGauss θ ξ * u t₁ (Y - ξ)) volume := by
      refine ((Heat.integrable_lineGauss hθ).mul_const M).mono'
        ((Heat.continuous_lineGauss θ).mul
          ((hu_slice t₁ ht₁.1).continuous.comp
            (continuous_const.sub continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun ξ => by
          rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hb0 t₁ ht₁ _) (Heat.lineGauss_nonneg hθ ξ))
    have hint2 : Integrable (fun ξ : ℝ => lineGauss θ ξ * u t₂ (Y - ξ)) volume := by
      refine ((Heat.integrable_lineGauss hθ).mul_const M).mono'
        ((Heat.continuous_lineGauss θ).mul
          ((hu_slice t₂ ht₂.1).continuous.comp
            (continuous_const.sub continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun ξ => by
          rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hb0 t₂ ht₂ _) (Heat.lineGauss_nonneg hθ ξ))
    have hsub : lineHeat θ (u t₁) Y - lineHeat θ (u t₂) Y =
        ∫ ξ : ℝ, lineGauss θ ξ * (u t₁ (Y - ξ) - u t₂ (Y - ξ)) := by
      unfold lineHeat
      rw [← integral_sub hint1 hint2]
      exact integral_congr_ae (Eventually.of_forall fun ξ => by ring)
    rw [hsub, ← Real.norm_eq_abs]
    refine (MeasureTheory.norm_integral_le_of_norm_le
      ((Heat.integrable_lineGauss hθ).mul_const (M * |t₁ - t₂|))
      (Eventually.of_forall fun ξ => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul, Real.norm_of_nonneg (Heat.lineGauss_nonneg hθ ξ), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hut_mvt t₁ ht₁ t₂ ht₂ _) (Heat.lineGauss_nonneg hθ ξ)
    · rw [MeasureTheory.integral_mul_const, Heat.integral_lineGauss hθ, one_mul]
  have hΦ_deriv : ∀ t ∈ Ioo 0 T,
      HasDerivAt Φ (lineHeat (T - t) (F t) Y) t := by
    intro t ht
    have h := hasDerivAt_lineHeat_duhamel_step hu_smooth hM0 hb0 hb1 hb2 hbt hpde ht Y
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht.2] with r hr
    have hr' : r < T := hr
    simp [Φ, hr']
  have hΦ_cont : ContinuousOn Φ (Icc 0 T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · -- Continuity at `t = 0`
      have h0_const : ContinuousAt (fun r : ℝ => lineHeat (T - r) (u 0) Y) 0 := by
        have h_u0_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u 0 x.2) (Ici 0 ×ˢ univ) :=
          (hu_slice 0 le_rfl).comp_contDiffOn contDiffOn_snd
        have h_step := hasDerivAt_lineHeat_duhamel_step (u := fun _ z => u 0 z)
          (F := fun _ z => -deriv (deriv (u 0)) z) (T := T + 1) (M := M)
          h_u0_smooth hM0 (fun _ _ => hb0 0 ⟨le_rfl, hT.le⟩)
          (fun _ _ => hb1 0 ⟨le_rfl, hT.le⟩) (fun _ _ => hb2 0 ⟨le_rfl, hT.le⟩)
          (fun _ _ _ => by simp [hM0]) (fun _ _ _ => by simp) (t₀ := 1) ⟨zero_lt_one, by linarith⟩ Y
        have hcomp : ContinuousAt (fun r : ℝ => lineHeat ((T + 1) - (r + 1)) (u 0) Y) 0 :=
          ContinuousAt.comp (g := fun s : ℝ => lineHeat ((T + 1) - s) (u 0) Y)
            (f := fun r : ℝ => r + 1) (by simpa using h_step.continuousAt)
            (continuous_id.add continuous_const).continuousAt
        refine hcomp.congr (Eventually.of_forall fun r => ?_)
        dsimp
        have : (T + 1) - (r + 1) = T - r := by ring
        rw [this]
      rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ₁, hδ₁, h0_lim⟩ := Metric.tendsto_nhds_nhds.1 h0_const (ε / 2) (half_pos hε)
      set δ : ℝ := min (min δ₁ (T / 2)) ((ε / 2) / (M + 1))
      have hδ : 0 < δ := lt_min (lt_min hδ₁ (half_pos hT)) (div_pos (half_pos hε) (by positivity))
      refine ⟨δ, hδ, fun r hr hdist => ?_⟩
      have hr_lt_T : r < T := by
        have : r < T / 2 := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1] at hdist
          exact hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _))
        linarith
      have hΦr : Φ r = lineHeat (T - r) (u r) Y := by simp [Φ, hr_lt_T]
      have hΦ0 : Φ 0 = lineHeat T (u 0) Y := by simp [Φ, hT]
      rw [Real.dist_eq, hΦr, hΦ0]
      have h1 : |lineHeat (T - r) (u r) Y - lineHeat (T - r) (u 0) Y| < ε / 2 := by
        have hle := hlineHeat_sub_u (sub_pos.2 hr_lt_T) r hr 0 ⟨le_rfl, hT.le⟩
        rw [sub_zero, abs_of_nonneg hr.1] at hle
        have hr_lt : r < (ε / 2) / (M + 1) := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1] at hdist
          exact hdist.trans_le (min_le_right _ _)
        calc |lineHeat (T - r) (u r) Y - lineHeat (T - r) (u 0) Y|
            ≤ M * r := hle
          _ ≤ (M + 1) * r := by nlinarith [hr.1]
          _ < (M + 1) * ((ε / 2) / (M + 1)) := mul_lt_mul_of_pos_left hr_lt (by positivity)
          _ = ε / 2 := mul_div_cancel₀ _ (by positivity)
      have h2 : |lineHeat (T - r) (u 0) Y - lineHeat T (u 0) Y| < ε / 2 := by
        have hr_δ₁ : dist r 0 < δ₁ :=
          hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _))
        simpa [Real.dist_eq] using h0_lim hr_δ₁
      calc |lineHeat (T - r) (u r) Y - lineHeat T (u 0) Y|
          ≤ |lineHeat (T - r) (u r) Y - lineHeat (T - r) (u 0) Y| +
              |lineHeat (T - r) (u 0) Y - lineHeat T (u 0) Y| := abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add h1 h2
        _ = ε := add_halves ε
    · rcases eq_or_lt_of_le ht.2 with rfl | htT
      · -- Continuity at `t = T`
        obtain ⟨C₁, hC₁0, happrox⟩ := exists_abs_lineHeat_sub_le
        have hlim1 : Tendsto (fun r : ℝ => M * |r - t|) (𝓝 t) (𝓝 0) := by
          have h : Continuous (fun r : ℝ => M * |r - t|) :=
            continuous_const.mul (continuous_id.sub continuous_const).abs
          simpa using h.tendsto t
        have hlim2 : Tendsto (fun r : ℝ => M * C₁ * (t - r) ^ ((1 : ℝ) / 2)) (𝓝 t) (𝓝 0) := by
          have hsub : Continuous (fun r : ℝ => (t - r) ^ ((1 : ℝ) / 2)) :=
            (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr (by norm_num)
          have h := (hsub.const_mul (M * C₁)).tendsto t
          simpa using h
        have hlim := hlim1.add hlim2
        rw [add_zero] at hlim
        rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
          (Filter.Eventually.mono self_mem_nhdsWithin fun r hr => ?_)
          (hlim.mono_left nhdsWithin_le_nhds)
        rcases eq_or_lt_of_le hr.2 with rfl | hr_lt
        · simp
        · have hΦr : Φ r = lineHeat (t - r) (u r) Y := by simp [Φ, hr_lt]
          have hΦt : Φ t = u t Y := by simp [Φ]
          rw [Real.dist_eq, hΦr, hΦt]
          have h1 := hlineHeat_sub_u (sub_pos.2 hr_lt) r hr t ⟨hT.le, le_rfl⟩
          have h2 := happrox (sub_pos.2 hr_lt) hM0 (hb0 t ⟨hT.le, le_rfl⟩)
            ((hu_slice t hT.le).differentiable (by simp)) (hb1 t ⟨hT.le, le_rfl⟩) Y
          calc |lineHeat (t - r) (u r) Y - u t Y|
              ≤ |lineHeat (t - r) (u r) Y - lineHeat (t - r) (u t) Y| +
                  |lineHeat (t - r) (u t) Y - u t Y| := abs_sub_le _ _ _
            _ ≤ M * |r - t| + M * C₁ * (t - r) ^ ((1 : ℝ) / 2) := add_le_add h1 h2
      · exact (hΦ_deriv t ⟨ht0, htT⟩).continuousAt.continuousWithinAt
  have hF_bd : ∀ t ∈ Icc 0 T, ∀ z : ℝ, |F t z| ≤ 2 * M := by
    intro t ht z
    rw [← hpde t ht z]
    calc |deriv (fun r => u r z) t - deriv (deriv (u t)) z|
        ≤ |deriv (fun r => u r z) t| + |deriv (deriv (u t)) z| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbt t ht z) (hb2 t ht z)
      _ = 2 * M := by ring
  have hint_F : IntervalIntegrable (fun t => lineHeat (T - t) (F t) Y) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    have hae_eq : (fun t => lineHeat (T - t) (F t) Y) =ᵐ[volume.restrict (Ioc 0 T)] deriv Φ := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [Measure.ae_ne volume T] with t ht_ne ht_mem
      have ht_Ioo : t ∈ Ioo 0 T := ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
      exact (hΦ_deriv t ht_Ioo).deriv.symm
    have hint_dΦ : IntegrableOn (deriv Φ) (Ioc 0 T) volume := by
      refine Measure.integrableOn_of_bounded (M := 2 * M) measure_Ioc_lt_top.ne
        (measurable_deriv Φ).aestronglyMeasurable ?_
      filter_upwards [hae_eq.symm, ae_restrict_mem measurableSet_Ioc] with t ht_eq ht
      rw [ht_eq, Real.norm_eq_abs]
      exact Heat.abs_lineHeat_le (sub_nonneg.2 ht.2) (hF_bd t ⟨ht.1.le, ht.2⟩) Y
    exact hint_dΦ.congr_fun_ae hae_eq.symm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT.le hΦ_cont
    (fun t ht => (hΦ_deriv t ht).hasDerivWithinAt) hint_F
  have hΦT : Φ T = u T Y := by simp [Φ]
  have hΦ0 : Φ 0 = lineHeat T (u 0) Y := by simp [Φ, hT]
  rw [hΦT, hΦ0] at hftc
  unfold lineDuhamel
  simp only [one_mul]
  linarith

/-- Joint continuity of `(Y, t) ↦ lineHeat (T - t) (H t) Y` on `ℝ × (0, T)` for any bounded
continuous `H : ℝ → ℝ → ℝ` on `[0, T] × ℝ`. -/
theorem continuousOn_lineHeat_sub {H : ℝ → ℝ → ℝ} {T M : ℝ}
    (hH_cont : ContinuousOn (fun x : ℝ × ℝ => H x.1 x.2) (Icc 0 T ×ˢ univ))
    (hH_bd : ∀ t ∈ Icc 0 T, ∀ z : ℝ, |H t z| ≤ M) :
    ContinuousOn (fun x : ℝ × ℝ => lineHeat (T - x.2) (H x.2) x.1) (univ ×ˢ Ioo 0 T) := by
  intro ⟨Y₀, t₀⟩ ⟨_, ht₀⟩
  set θ₀ : ℝ := T - t₀
  have hθ₀ : 0 < θ₀ := sub_pos.2 ht₀.2
  set B₀ : ℝ := (2 * Real.pi * θ₀) ^ (-(1 : ℝ) / 2)
  set s_nhd : Set ℝ := Ioo (max 0 (T - 2 * θ₀)) (T - θ₀ / 2)
  have hs_mem : s_nhd ∈ 𝓝 t₀ := by
    refine Ioo_mem_nhds (max_lt ht₀.1 ?_) ?_
    · dsimp [θ₀]; linarith
    · dsimp [θ₀]; linarith
  have hs_sub : ∀ t ∈ s_nhd, t ∈ Ioo 0 T ∧ T - t ∈ Ioo (θ₀ / 2) (2 * θ₀) := by
    intro t ht
    have ht1 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have ht2 : T - 2 * θ₀ < t := lt_of_le_of_lt (le_max_right _ _) ht.1
    refine ⟨⟨ht1, by linarith [ht.2]⟩, ⟨by linarith [ht.2], by linarith⟩⟩
  have hU_mem : univ ×ˢ s_nhd ∈ 𝓝 (Y₀, t₀) := prod_mem_nhds univ_mem hs_mem
  let F_int : (ℝ × ℝ) → ℝ → ℝ := fun x ξ => lineGauss (T - x.2) ξ * H x.2 (x.1 - ξ)
  let bound : ℝ → ℝ := fun ξ => B₀ * M * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2)
  have hmeas_F : ∀ᶠ x in 𝓝 (Y₀, t₀), AEStronglyMeasurable (F_int x) volume := by
    filter_upwards [hU_mem] with x hx
    have ht : x.2 ∈ Icc 0 T := ⟨(hs_sub x.2 hx.2).1.1.le, (hs_sub x.2 hx.2).1.2.le⟩
    have hHx : Continuous (H x.2) :=
      hH_cont.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨ht, mem_univ z⟩
    exact ((Heat.continuous_lineGauss (T - x.2)).mul
      (hHx.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hbd_F : ∀ᶠ x in 𝓝 (Y₀, t₀), ∀ᵐ ξ ∂volume, ‖F_int x ξ‖ ≤ bound ξ := by
    filter_upwards [hU_mem] with x hx
    refine Eventually.of_forall fun ξ => ?_
    obtain ⟨htIoo, hθIoo⟩ := hs_sub x.2 hx.2
    have hθ_pos : 0 < T - x.2 := by linarith [hθIoo.1]
    have h2 : |lineGauss (T - x.2) ξ| ≤ B₀ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by
      rw [abs_of_nonneg (Heat.lineGauss_nonneg hθ_pos ξ)]
      unfold lineGauss
      have hpre : (4 * Real.pi * (T - x.2)) ^ (-(1 : ℝ) / 2) ≤ B₀ :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by nlinarith [Real.pi_pos, hθIoo.1]) (by norm_num)
      have hexp : Real.exp (-ξ ^ 2 / (4 * (T - x.2))) ≤ Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2) := by
        apply Real.exp_le_exp.mpr
        have : 1 / (16 * θ₀) * ξ ^ 2 ≤ ξ ^ 2 / (4 * (T - x.2)) := by
          rw [div_mul_eq_mul_div, one_mul]
          exact div_le_div_of_nonneg_left (sq_nonneg ξ) (by positivity) (by linarith [hθIoo.2])
        rw [neg_div, neg_mul]
        linarith
      exact mul_le_mul hpre hexp (Real.exp_pos _).le (by positivity)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |lineGauss (T - x.2) ξ| * |H x.2 (x.1 - ξ)|
        ≤ (B₀ * Real.exp (-(1 / (16 * θ₀)) * ξ ^ 2)) * M :=
          mul_le_mul h2 (hH_bd x.2 ⟨htIoo.1.le, htIoo.2.le⟩ _) (abs_nonneg _) (by positivity)
      _ = bound ξ := by dsimp [bound]; ring
  have hcont_F : ∀ᵐ ξ ∂volume, ContinuousAt (fun x : ℝ × ℝ => F_int x ξ) (Y₀, t₀) := by
    refine Eventually.of_forall fun ξ => ?_
    have hker : ContinuousAt (fun x : ℝ × ℝ => lineGauss (T - x.2) ξ) (Y₀, t₀) :=
      ContinuousAt.comp (g := fun s : ℝ => lineGauss s ξ) (f := fun x : ℝ × ℝ => T - x.2)
        (hasDerivAt_lineGauss_time hθ₀ ξ).continuousAt
        (continuous_const.sub continuous_snd).continuousAt
    have hH_at : ContinuousAt (fun y : ℝ × ℝ => H y.1 y.2) (t₀, Y₀ - ξ) :=
      hH_cont.continuousAt
        (prod_mem_nhds (Icc_mem_nhds ht₀.1 ht₀.2) univ_mem)
    have hmap : ContinuousAt (fun x : ℝ × ℝ => (x.2, x.1 - ξ)) (Y₀, t₀) :=
      (continuous_snd.prodMk (continuous_fst.sub continuous_const)).continuousAt
    exact hker.mul (ContinuousAt.comp (g := fun y : ℝ × ℝ => H y.1 y.2)
      (f := fun x : ℝ × ℝ => (x.2, x.1 - ξ)) hH_at hmap)
  exact (MeasureTheory.continuousAt_of_dominated hmeas_F hbd_F
    ((integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (16 * θ₀))).const_mul (B₀ * M))
    hcont_F).continuousWithinAt

end UnforcedLeray.Short.PartI.DuhamelSplit
