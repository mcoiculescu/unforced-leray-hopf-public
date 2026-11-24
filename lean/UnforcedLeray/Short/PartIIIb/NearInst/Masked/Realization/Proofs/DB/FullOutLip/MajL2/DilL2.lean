import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.PhaseMinkowski
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.KerMeas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.KerL1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.FixedL
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.MajL2.Margin

/-!
# `L²` bound of the dilated radial operator (source 3996-4011, 4002)

`fmDilL2`: the `L²([0,P) × ℝ³)` norm of `dilMajG` is the `L²` norm of the `l`-integral of the
fixed-`l` terms `fdlDmlF l (τ, y)`. Minkowski's integral inequality (`PhaseMinkowski`) bounds it
by the integral over `l ∈ (0,1)` of the fixed-`l` norms; `FmFixedL` bounds each of those by
`l^{2μ+1/2} A ‖g‖` with `A = K' (1-l²)^{-1/2}` (from `FmKerL1` with `(ν(1-l²))^{-1/2} =
ν^{-1/2}(1-l²)^{-1/2}`), and `FmMargin` gives the finite `l`-integral. Squaring finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The fixed-dilation term of `dilMajG` at `a = (τ, y)`: `dilMajG ν μ g τ y = ∫_{(0,1)} fdlDmlF l (τ,y) dl`. -/
private def fdlDmlF (ν μ : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞) (l : ℝ)
    (a : ℝ × UnforcedLeray.Space) : ℝ≥0∞ :=
  ENNReal.ofReal (l ^ (2 * μ + 2)) * ∫⁻ z : UnforcedLeray.Space,
    fmKer ν l (a.2 - l • z) * g (a.1 + 2 * Real.log l) z

/-- Joint measurability of the fixed-`l` terms in `(l, τ, y)`. -/
private lemma fdl_meas (ν μ : ℝ) (g : ℝ → UnforcedLeray.Space → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × (ℝ × UnforcedLeray.Space) => fdlDmlF ν μ g p.1 p.2) := by
  have hk : Measurable (fun p : ℝ × UnforcedLeray.Space => fmKer ν p.1 p.2) :=
    fmKerMeasurable ν
  have h1 : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      q.1.2.2 - q.1.1 • q.2) :=
    (measurable_snd.comp (measurable_snd.comp measurable_fst)).sub
      ((measurable_fst.comp measurable_fst).smul measurable_snd)
  have hpair : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      (q.1.1, q.1.2.2 - q.1.1 • q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk h1
  have h2 : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      (q.1.2.1 + 2 * Real.log q.1.1, q.2)) :=
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).add
      (measurable_const.mul (Real.measurable_log.comp (measurable_fst.comp measurable_fst)))).prodMk
      measurable_snd
  have hI : Measurable (fun q : (ℝ × (ℝ × UnforcedLeray.Space)) × UnforcedLeray.Space =>
      fmKer ν q.1.1 (q.1.2.2 - q.1.1 • q.2) *
        Function.uncurry g (q.1.2.1 + 2 * Real.log q.1.1, q.2)) :=
    Measurable.mul (hk.comp hpair) (hg.comp h2)
  have hGint : Measurable (fun p : ℝ × (ℝ × UnforcedLeray.Space) =>
      ∫⁻ z : UnforcedLeray.Space, fmKer ν p.1 (p.2.2 - p.1 • z) *
        Function.uncurry g (p.2.1 + 2 * Real.log p.1, z)) :=
    hI.lintegral_prod_right'
  exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hGint

/-- **`L²` bound of the dilated radial operator** (squared form of `FmDilL2`). -/
theorem fmDilL2 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FmDilL2 := by
  intro ν μ hν hμ
  obtain ⟨CK, hCK0, hKL1⟩ := fmKerL1
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = CK * ν ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K' := by
    rw [hK'def]
    exact mul_nonneg hCK0 (Real.rpow_nonneg hν.le _)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ≥0∞, M = ∫⁻ l in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) :=
    ⟨_, rfl⟩
  have hMfin : M < ⊤ := by
    rw [hMdef]
    exact fmMargin μ hμ
  refine ⟨M.toReal * K', mul_nonneg ENNReal.toReal_nonneg hK0, fun g hg P hP0 hper => ?_⟩
  have hFm : Measurable (fun p : ℝ × (ℝ × UnforcedLeray.Space) => fdlDmlF ν μ g p.1 p.2) :=
    fdl_meas ν μ g hg
  have hsw : Measurable (fun q : (ℝ × UnforcedLeray.Space) × ℝ => fdlDmlF ν μ g q.2 q.1) :=
    hFm.comp (measurable_snd.prodMk measurable_fst)
  have hPhi : Measurable (fun a : ℝ × UnforcedLeray.Space =>
      ∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) := hsw.lintegral_prod_right'
  have hdil : ∀ τ y, dilMajG ν μ g τ y = ∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l (τ, y) :=
    fun τ y => rfl
  -- the left-hand side is the `(τ, y)`-integral of the squared `l`-integral
  have hLHS : (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space, dilMajG ν μ g τ y ^ (2 : ℝ)) =
      ∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)) := by
    rw [lintegral_prod (fun a => (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ))
      (hPhi.pow_const (2 : ℝ)).aemeasurable]
    refine lintegral_congr fun τ => lintegral_congr fun y => ?_
    exact congrArg (· ^ (2 : ℝ)) (hdil τ y)
  -- fixed `l`: Young (`FmFixedL`) with the kernel bound `A = K' (1-l²)^{-1/2}`
  have hfix : ∀ l ∈ Ioo (0 : ℝ) 1,
      (∫⁻ a, fdlDmlF ν μ g l a ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
          (ENNReal.ofReal K' * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have h1l : 0 < 1 - l ^ 2 := by nlinarith [hl.1, hl.2]
    have hm : Measurable (fun a : ℝ × UnforcedLeray.Space => fdlDmlF ν μ g l a ^ (2 : ℝ)) :=
      (hFm.comp (measurable_const.prodMk measurable_id)).pow_const _
    have hA : ∫⁻ w : UnforcedLeray.Space, fmKer ν l w ≤
        ENNReal.ofReal K' * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ))) := by
      refine (hKL1 ν hν l hl).trans (le_of_eq ?_)
      rw [Real.mul_rpow hν.le h1l.le, hK'def, ← ENNReal.ofReal_mul hCK0,
        ← ENNReal.ofReal_mul (mul_nonneg hCK0 (Real.rpow_nonneg hν.le _))]
      congr 1
      ring
    rw [lintegral_prod (fun a => fdlDmlF ν μ g l a ^ (2 : ℝ)) hm.aemeasurable]
    exact fmFixedL ν μ g hg P hP0 hper _ l hl hA
  have hRHS : (∫⁻ l in Ioo (0 : ℝ) 1, (∫⁻ a, fdlDmlF ν μ g l a ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
          (1 / 2 : ℝ)) ≤
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
          (ENNReal.ofReal K' * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    setLIntegral_mono' (μ := volume) measurableSet_Ioo hfix
  have hmeas : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
      ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_const.sub (measurable_id.pow_const 2)).pow_const _))
  have hcoef : ENNReal.ofReal (M.toReal * K') = M * ENNReal.ofReal K' := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hMfin.ne]
  -- the square root of the left-hand side (Minkowski + the margin)
  have hroot : (∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
          (1 / 2 : ℝ) ≤
      ENNReal.ofReal (M.toReal * K') *
        (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    calc (∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ)
            ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
          (1 / 2 : ℝ)
        ≤ ∫⁻ l in Ioo (0 : ℝ) 1, (∫⁻ a, fdlDmlF ν μ g l a ^ (2 : ℝ)
            ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
              (1 / 2 : ℝ) :=
          phaseMinkowski_holds _ _ (fdlDmlF ν μ g) hFm (Ioo (0 : ℝ) 1) measurableSet_Ioo
      _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
          (ENNReal.ofReal K' * ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) *
          (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          hRHS
      _ = ∫⁻ l in Ioo (0 : ℝ) 1, (ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
          ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) *
          (ENNReal.ofReal K' *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
          lintegral_congr fun l => by ring
      _ = (∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 1 / 2)) *
          ENNReal.ofReal ((1 - l ^ 2) ^ (-(1 / 2 : ℝ)))) *
          (ENNReal.ofReal K' *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
          lintegral_mul_const _ hmeas
      _ = M * (ENNReal.ofReal K' *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
          rw [hMdef]
      _ = ENNReal.ofReal (M.toReal * K') *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [hcoef]
          ring
  have hsq : (∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ)
        ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ≤
      ENNReal.ofReal (M.toReal * K') ^ (2 : ℝ) *
        ∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ) := by
    calc (∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ)
            ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)))
        = ((∫⁻ a, (∫⁻ l in Ioo (0 : ℝ) 1, fdlDmlF ν μ g l a) ^ (2 : ℝ)
            ∂((volume.restrict (Ico (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) ^
              (1 / 2 : ℝ)) ^ (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]
          norm_num
      _ ≤ (ENNReal.ofReal (M.toReal * K') *
            (∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^
              (2 : ℝ) := ENNReal.rpow_le_rpow hroot (by norm_num)
      _ = ENNReal.ofReal (M.toReal * K') ^ (2 : ℝ) *
            ((∫⁻ τ in Ico (0 : ℝ) P, ∫⁻ z : UnforcedLeray.Space, g τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^
              (2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = _ := by
          rw [← ENNReal.rpow_mul]
          norm_num
  rw [hLHS]
  exact hsq

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
