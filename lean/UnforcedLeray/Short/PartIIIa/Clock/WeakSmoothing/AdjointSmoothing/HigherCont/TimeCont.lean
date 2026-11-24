import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.HigherCont.ChiBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.IntH1.CutRate.Cont
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Static.Comm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel.Bridge
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# `PartIII-a:T21/2/7/2/4/4`: time derivative continuity `∂^w ∂_r φ ∈ C([t, s); X_{-m,c})` (`|w| ≤ 1`)

Source of record: `the November 2 reference manuscript`
(SP), lines 3060-3073 (and 3052-3058 for the order `-1` localized interaction `K_c^T(φ∇E)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace TimeContAux

/-! ### Section 1: `InCX` (`C([t, s); X_{-m,c})`) closure combinators -/

/-- Membership and strong `X_{-m,c}` continuity on `[t, s)`. -/
def InCX (c m t s : ℝ) (f : ℝ → ℝ × ℝ → ℂ) : Prop :=
  ∀ r ∈ Ico t s, MemLp (f r) 2 (B0579.cellMeasure c (-m)) ∧
    Tendsto (fun r' => xNorm c (-m) (f r' - f r)) (𝓝[Ico t s] r) (𝓝 0)

lemma tendsto_zero_of_le {l : Filter ℝ} {H U : ℝ → ℝ≥0∞}
    (hU : Tendsto U l (𝓝 0)) (hle : ∀ᶠ r' in l, H r' ≤ U r') :
    Tendsto H l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun _ => zero_le) hle

lemma InCX.congr {c m t s : ℝ} {f g : ℝ → ℝ × ℝ → ℂ} (hf : InCX c m t s f)
    (heq : ∀ r ∈ Ico t s, g r = f r) : InCX c m t s g := by
  intro r hr
  rw [heq r hr]
  refine ⟨(hf r hr).1, (hf r hr).2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  rw [heq r' hr']

lemma InCX.add {c m t s : ℝ} {f g : ℝ → ℝ × ℝ → ℂ} (hf : InCX c m t s f)
    (hg : InCX c m t s g) : InCX c m t s (fun r x => f r x + g r x) := by
  intro r hr
  refine ⟨(hf r hr).1.add (hg r hr).1, ?_⟩
  have hsum : Tendsto (fun r' => xNorm c (-m) (f r' - f r) + xNorm c (-m) (g r' - g r))
      (𝓝[Ico t s] r) (𝓝 0) := by
    simpa using (hf r hr).2.add (hg r hr).2
  refine tendsto_zero_of_le hsum ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have e : (fun x => f r' x + g r' x) - (fun x => f r x + g r x) =
      (f r' - f r) + (g r' - g r) := by ext x; simp [Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  exact eLpNorm_add_le ((hf r' hr').1.sub (hf r hr).1).1
    ((hg r' hr').1.sub (hg r hr).1).1 (by norm_num)

lemma InCX.sub {c m t s : ℝ} {f g : ℝ → ℝ × ℝ → ℂ} (hf : InCX c m t s f)
    (hg : InCX c m t s g) : InCX c m t s (fun r x => f r x - g r x) := by
  intro r hr
  refine ⟨(hf r hr).1.sub (hg r hr).1, ?_⟩
  have hsum : Tendsto (fun r' => xNorm c (-m) (f r' - f r) + xNorm c (-m) (g r' - g r))
      (𝓝[Ico t s] r) (𝓝 0) := by
    simpa using (hf r hr).2.add (hg r hr).2
  refine tendsto_zero_of_le hsum ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have e : (fun x => f r' x - g r' x) - (fun x => f r x - g r x) =
      (f r' - f r) - (g r' - g r) := by ext x; simp [Pi.sub_apply]; ring
  rw [e]
  exact eLpNorm_sub_le ((hf r' hr').1.sub (hf r hr).1).1
    ((hg r' hr').1.sub (hg r hr).1).1 (by norm_num)

lemma InCX.const_mul {c m t s : ℝ} (a : ℂ) {f : ℝ → ℝ × ℝ → ℂ} (hf : InCX c m t s f) :
    InCX c m t s (fun r x => a * f r x) := by
  intro r hr
  refine ⟨(hf r hr).1.const_mul a, ?_⟩
  have hmul : Tendsto (fun r' => (‖a‖₊ : ℝ≥0∞) * xNorm c (-m) (f r' - f r))
      (𝓝[Ico t s] r) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hf r hr).2 (Or.inr ENNReal.coe_ne_top)
  refine tendsto_zero_of_le hmul ?_
  filter_upwards [self_mem_nhdsWithin] with r' _
  have e : (fun x => a * f r' x) - (fun x => a * f r x) = a • (f r' - f r) := by
    ext x; simp [Pi.sub_apply, mul_sub]
  rw [e, xNorm, eLpNorm_const_smul]
  rfl

/-- **Bounded continuous multiplier in `C([t, s); X_{-m,c})`**. -/
lemma InCX.ofReal_mul {c m t s : ℝ} {a : ℝ → ℝ × ℝ → ℝ} {F : ℝ → ℝ × ℝ → ℂ}
    (ha_cont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => a p.1 p.2) (Ico t s ×ˢ univ))
    (ha_bdd : ∀ b ∈ Ioo t s, ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ ∈ Ico t b, ∀ x : ℝ × ℝ, |a ρ x| ≤ A)
    (hF : InCX c m t s F) :
    InCX c m t s (fun r x => ((a r x : ℝ) : ℂ) * F r x) := by
  have hac_slice : ∀ ρ ∈ Ico t s, Continuous (a ρ) := fun ρ hρ =>
    ha_cont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hρ, mem_univ x⟩)
  have hmem_mul : ∀ {b : ℝ × ℝ → ℝ} {A : ℝ} {H : ℝ × ℝ → ℂ},
      Continuous b → (∀ x, |b x| ≤ A) → MemLp H 2 (B0579.cellMeasure c (-m)) →
      MemLp (fun x => ((b x : ℝ) : ℂ) * H x) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (fun x => ((b x : ℝ) : ℂ) * H x) ≤
          ENNReal.ofReal A * xNorm c (-m) H := by
    intro b A H hbc hb hH
    have hle : ∀ᵐ x ∂(B0579.cellMeasure c (-m)),
        ‖((b x : ℝ) : ℂ) * H x‖ ≤ A * ‖H x‖ := by
      refine ae_of_all _ fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    have hmeas : AEStronglyMeasurable (fun x => ((b x : ℝ) : ℂ) * H x)
        (B0579.cellMeasure c (-m)) :=
      (Complex.continuous_ofReal.comp hbc).aestronglyMeasurable.mul hH.1
    exact ⟨hH.of_le_mul hmeas hle, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hle 2⟩
  intro r hr
  let b : ℝ := (r + s) / 2
  have hb : b ∈ Ioo t s := ⟨by dsimp [b]; linarith [hr.1, hr.2], by dsimp [b]; linarith [hr.2]⟩
  have hrb : r ∈ Ico t b := ⟨hr.1, by dsimp [b]; linarith [hr.2]⟩
  obtain ⟨A, hA0, hA⟩ := ha_bdd b hb
  refine ⟨(hmem_mul (hac_slice r hr) (hA r hrb) (hF r hr).1).1, ?_⟩
  let G₁ : ℝ → ℝ × ℝ → ℂ := fun r' x => ((a r' x : ℝ) : ℂ) * (F r' x - F r x)
  let G₂ : ℝ → ℝ × ℝ → ℂ := fun r' x => ((a r' x - a r x : ℝ) : ℂ) * F r x
  have hIco_b : Ico t b ∈ 𝓝[Ico t s] r := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hrb.2)] with r' hr'1 hr'2
    exact ⟨hr'1.1, hr'2⟩
  have hG1_tendsto : Tendsto (fun r' => xNorm c (-m) (G₁ r')) (𝓝[Ico t s] r) (𝓝 0) := by
    have hmul : Tendsto (fun r' => ENNReal.ofReal A * xNorm c (-m) (F r' - F r))
        (𝓝[Ico t s] r) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hF r hr).2 (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_zero_of_le hmul ?_
    filter_upwards [hIco_b] with r' hr'
    have hr's : r' ∈ Ico t s := ⟨hr'.1, hr'.2.trans hb.2⟩
    exact (hmem_mul (hac_slice r' hr's) (hA r' hr') ((hF r' hr's).1.sub (hF r hr).1)).2
  have hG2_mem : ∀ r' ∈ Ico t b, MemLp (G₂ r') 2 (B0579.cellMeasure c (-m)) := by
    intro r' hr'
    have hr's : r' ∈ Ico t s := ⟨hr'.1, hr'.2.trans hb.2⟩
    refine (hmem_mul ((hac_slice r' hr's).sub (hac_slice r hr)) (A := 2 * A) (fun x => ?_)
      (hF r hr).1).1
    calc |a r' x - a r x| ≤ |a r' x| + |a r x| := abs_sub _ _
      _ ≤ A + A := add_le_add (hA r' hr' x) (hA r hrb x)
      _ = 2 * A := by ring
  have hG2_int : Tendsto (fun r' => ∫ x, ‖G₂ r' x‖ ^ 2 ∂(B0579.cellMeasure c (-m)))
      (𝓝[Ico t s] r) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _x : ℝ × ℝ, (0 : ℝ) ∂(B0579.cellMeasure c (-m)) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (2 * A) ^ 2 * ‖F r x‖ ^ 2) ?_ ?_ ?_ ?_
    · filter_upwards [hIco_b] with r' hr'
      exact (hG2_mem r' hr').1.norm.pow 2
    · filter_upwards [hIco_b] with r' hr'
      refine ae_of_all _ fun x => ?_
      have habs : |a r' x - a r x| ≤ 2 * A := by
        calc |a r' x - a r x| ≤ |a r' x| + |a r x| := abs_sub _ _
          _ ≤ A + A := add_le_add (hA r' hr' x) (hA r hrb x)
          _ = 2 * A := by ring
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      show ‖((a r' x - a r x : ℝ) : ℂ) * F r x‖ ^ 2 ≤ (2 * A) ^ 2 * ‖F r x‖ ^ 2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) habs 2) (sq_nonneg _)
    · exact (hF r hr).1.norm.integrable_sq.const_mul ((2 * A) ^ 2)
    · refine ae_of_all _ fun x => ?_
      have hax : Tendsto (fun r' => a r' x) (𝓝[Ico t s] r) (𝓝 (a r x)) := by
        have h1 : ContinuousWithinAt (fun p : ℝ × (ℝ × ℝ) => a p.1 p.2)
            (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) (r, x) :=
          ha_cont.continuousWithinAt ⟨hr, mem_univ x⟩
        have h2 : ContinuousWithinAt (fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) (Ico t s) r :=
          (continuous_id.prodMk continuous_const).continuousWithinAt
        exact ContinuousWithinAt.comp (f := fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ)))
          (g := fun p : ℝ × (ℝ × ℝ) => a p.1 p.2) h1 h2 (fun r' hr' => ⟨hr', mem_univ x⟩)
      have hsub0 : Tendsto (fun r' => a r' x - a r x) (𝓝[Ico t s] r) (𝓝 0) := by
        simpa [sub_self] using hax.sub (tendsto_const_nhds (x := a r x))
      have hsubC : Tendsto (fun r' => ((a r' x - a r x : ℝ) : ℂ)) (𝓝[Ico t s] r) (𝓝 0) := by
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hsub0
      have hsub : Tendsto (fun r' => G₂ r' x) (𝓝[Ico t s] r) (𝓝 0) := by
        simpa [G₂] using hsubC.mul_const (F r x)
      simpa using hsub.norm.pow 2
  have hG2_tendsto : Tendsto (fun r' => xNorm c (-m) (G₂ r')) (𝓝[Ico t s] r) (𝓝 0) := by
    have hsqrt : Tendsto (fun r' => Real.sqrt (∫ x, ‖G₂ r' x‖ ^ 2 ∂(B0579.cellMeasure c (-m))))
        (𝓝[Ico t s] r) (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hG2_int
    have hofR : Tendsto (fun r' => ENNReal.ofReal
        (Real.sqrt (∫ x, ‖G₂ r' x‖ ^ 2 ∂(B0579.cellMeasure c (-m)))))
        (𝓝[Ico t s] r) (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hsqrt
    refine hofR.congr' ?_
    filter_upwards [hIco_b] with r' hr'
    have hm := hG2_mem r' hr'
    have hne : xNorm c (-m) (G₂ r') ≠ ⊤ := hm.eLpNorm_ne_top
    rw [← st_xNorm_toReal_sq hm, Real.sqrt_sq ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hne]
  have hsum : Tendsto (fun r' => xNorm c (-m) (G₁ r') + xNorm c (-m) (G₂ r'))
      (𝓝[Ico t s] r) (𝓝 0) := by
    simpa using hG1_tendsto.add hG2_tendsto
  refine tendsto_zero_of_le hsum ?_
  filter_upwards [hIco_b] with r' hr'
  have hr's : r' ∈ Ico t s := ⟨hr'.1, hr'.2.trans hb.2⟩
  have e : (fun x => ((a r' x : ℝ) : ℂ) * F r' x) - (fun x => ((a r x : ℝ) : ℂ) * F r x) =
      G₁ r' + G₂ r' := by
    ext x; simp [G₁, G₂, Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  have hm1 := (hmem_mul (hac_slice r' hr's) (hA r' hr') ((hF r' hr's).1.sub (hF r hr).1)).1
  have hm2 := hG2_mem r' hr'
  exact eLpNorm_add_le hm1.1 hm2.1 (by norm_num)

/-! ### Section 2: Identification of `adjDt` on `[t, s)` and joint smoothness of `ladChi` -/

/-- On the half-open interval `[t, s)`, `adjDt t s φ r` coincides pointwise with `ladDt φ r`. -/
lemma adjDt_eq_ladDt_of_mem_Ico {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ico t s) (x : ℝ × ℝ) :
    adjDt t s φ r x = ladDt φ r x := by
  have hmem : ((r, x) : ℝ × (ℝ × ℝ)) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hr, mem_univ _⟩
  have hd : DifferentiableWithinAt ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
      (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) ((r, x) : ℝ × (ℝ × ℝ)) :=
    (hj _ hmem).differentiableWithinAt (by simp)
  have hline : HasDerivWithinAt (fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ))
      (Ico t s) r :=
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r x)).hasDerivWithinAt
  have hmaps : MapsTo (fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) (Ico t s)
      (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) :=
    fun r' hr' => ⟨hr', mem_univ x⟩
  have h1 : HasDerivWithinAt (fun r' => φ r' x)
      (fderivWithin ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) (r, x)
        ((1 : ℝ), (0 : ℝ × ℝ)))
      (Ico t s) r :=
    HasFDerivWithinAt.comp_hasDerivWithinAt (f := fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) r
      hd.hasFDerivWithinAt hline hmaps
  rw [adjDt, h1.derivWithin (uniqueDiffOn_Ico t s r hr),
    AdjCutE0ContAux.ladDt_eq_fderivWithin_Ico hj hr x]

/-- Joint `C^∞` smoothness of `ladDt φ` on `Ico t s ×ˢ univ`. -/
lemma jointSmooth_ladDt {t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ladDt φ p.1 p.2) (Ico t s ×ˢ univ) := by
  have hf : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) =>
        fderivWithin ℝ (fun q : ℝ × (ℝ × ℝ) => φ q.1 q.2) (Ico t s ×ˢ univ) p
          ((1 : ℝ), (0 : ℝ × ℝ)))
      (Ico t s ×ˢ univ) :=
    (hj.fderivWithin (adjStrip_uniqueDiff t s) (m := ∞) (by simp)).clm_apply contDiffOn_const
  exact hf.congr fun p hp => AdjCutE0ContAux.ladDt_eq_fderivWithin_Ico hj hp.1 p.2

/-- Joint `C^∞` smoothness of `ladChi tr φ` on `Ico t s ×ˢ univ`. -/
lemma jointSmooth_ladChi {ν c t s : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ladChi tr φ p.1 p.2) (Ico t s ×ˢ univ) := by
  have hdt := jointSmooth_ladDt hj
  have hlap : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ladLapCx (φ p.1) p.2)
      (Ico t s ×ˢ univ) :=
    (HigherContAux.jointSmooth_adjSpatial hj [0, 0]).add
      (HigherContAux.jointSmooth_adjSpatial hj [1, 1])
  have hsub : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun p hp => ⟨ht.trans hp.1.1, mem_univ _⟩
  have hv_all : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ico t s ×ˢ univ) :=
    tr.isTrain.smooth_v.mono hsub
  have hv : ∀ j : Fin 2, ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((tr.v p.1 p.2 j : ℝ) : ℂ)) (Ico t s ×ˢ univ) := fun j =>
    (Complex.ofRealCLM.contDiff.comp
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff).comp_contDiffOn hv_all
  have htr : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ladTransport tr p.1 (φ p.1) p.2)
      (Ico t s ×ˢ univ) :=
    ((hv 0).mul (HigherContAux.jointSmooth_adjSpatial hj [0])).add
      ((hv 1).mul (HigherContAux.jointSmooth_adjSpatial hj [1]))
  exact (hdt.add (contDiffOn_const.mul hlap)).add htr

/-- Pointwise decomposition of `adjSpatial w (adjDt t s φ r)` on `Ico t s`. -/
lemma adjSpatial_adjDt_decomp {ν c t s : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    {r : ℝ} (hr : r ∈ Ico t s) (w : List (Fin 2)) :
    adjSpatial w (adjDt t s φ r) =
      fun x => adjSpatial w (ladChi tr φ r) x -
        (ν : ℂ) * adjSpatial w (ladLapCx (φ r)) x -
        adjSpatial w (ladTransport tr r (φ r)) x := by
  have hφr : ContDiff ℝ ∞ (φ r) := adjContDiff_slice hj hr
  have hχ_sm : ContDiff ℝ ∞ (ladChi tr φ r) := adjContDiff_slice (jointSmooth_ladChi tr ht hj) hr
  have hlap_sm : ContDiff ℝ ∞ (ladLapCx (φ r)) :=
    (contDiff_adjSpatial hφr [0, 0]).add (contDiff_adjSpatial hφr [1, 1])
  have hνlap_sm : ContDiff ℝ ∞ (fun x => (ν : ℂ) * ladLapCx (φ r) x) :=
    (contDiff_const (c := (ν : ℂ))).mul hlap_sm
  have hv_sm : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v r x j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (UnforcedLeray.B0238.contDiff_Vc tr (ht.trans hr.1)))
  have htr_sm : ContDiff ℝ ∞ (ladTransport tr r (φ r)) :=
    ((hv_sm 0).mul (contDiff_pdCx hφr 0)).add ((hv_sm 1).mul (contDiff_pdCx hφr 1))
  have heq : adjDt t s φ r =
      fun x => (ladChi tr φ r x - (ν : ℂ) * ladLapCx (φ r) x) - ladTransport tr r (φ r) x := by
    ext x
    rw [adjDt_eq_ladDt_of_mem_Ico hj hr x]
    simp only [ladChi]
    ring
  rw [heq]
  have h1 := st_adjSpatial_sub (hχ_sm.sub hνlap_sm) htr_sm w
  have h2 := st_adjSpatial_sub hχ_sm hνlap_sm w
  have h3 := st_adjSpatial_const_mul (ν : ℂ) hlap_sm w
  ext x
  have h1x := congrFun h1 x
  have h2x := congrFun h2 x
  have h3x := congrFun h3 x
  rw [h1x, h2x, h3x]

/-! ### Section 3: Laplacian term `(ν : ℂ) * adjSpatial w (ladLapCx (φ r)) x` -/

lemma inCX_lap {ν c m t s : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hSp : AdjSpatialCont c m t s 3 φ)
    {w : List (Fin 2)} (hw : w.length ≤ 1) :
    InCX c m t s (fun r x => (ν : ℂ) * adjSpatial w (ladLapCx (φ r)) x) := by
  have hw0 : (w ++ [0, 0]).length ≤ 3 := by simp; omega
  have hw1 : (w ++ [1, 1]).length ≤ 3 := by simp; omega
  have h0 : InCX c m t s (fun r => adjSpatial (w ++ [0, 0]) (φ r)) :=
    fun r hr => hSp r hr (w ++ [0, 0]) hw0
  have h1 : InCX c m t s (fun r => adjSpatial (w ++ [1, 1]) (φ r)) :=
    fun r hr => hSp r hr (w ++ [1, 1]) hw1
  refine InCX.const_mul (ν : ℂ) ((h0.add h1).congr fun r hr => ?_)
  have hφr : ContDiff ℝ ∞ (φ r) := adjContDiff_slice hj hr
  have hadd := st_adjSpatial_add (contDiff_adjSpatial hφr [0, 0])
    (contDiff_adjSpatial hφr [1, 1]) w
  ext x
  have haddx : adjSpatial w (ladLapCx (φ r)) x =
      adjSpatial w (adjSpatial [0, 0] (φ r)) x + adjSpatial w (adjSpatial [1, 1] (φ r)) x :=
    congrFun hadd x
  change adjSpatial w (ladLapCx (φ r)) x =
    adjSpatial (w ++ [0, 0]) (φ r) x + adjSpatial (w ++ [1, 1]) (φ r) x
  rw [haddx, st_adjSpatial_append, st_adjSpatial_append]

/-! ### Section 4: Joint smoothness of spatial partials on `Ici 0 ×ˢ univ` and transport term -/

/-- If `G : ℝ × (ℝ × ℝ) → ℝ` is `C^∞` on `Ici 0 ×ˢ univ`, then for each `k : Fin 2` its spatial
directional derivative `(ρ, x) ↦ B0579.pd k (fun y => G (ρ, y)) x` is also `C^∞` on `Ici 0 ×ˢ univ`. -/
lemma contDiffOn_pd_halfST {G : ℝ × (ℝ × ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ici (0 : ℝ) ×ˢ univ)) (k : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (fun y => G (p.1, y)) p.2)
      (Ici (0 : ℝ) ×ˢ univ) := by
  have hf : ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) =>
        fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ univ) p ((0 : ℝ), B0579.dir k))
      (Ici (0 : ℝ) ×ˢ univ) :=
    (hG.fderivWithin halfST_uniqueDiffOn (m := ∞) (by simp)).clm_apply contDiffOn_const
  refine hf.congr fun p hp => ?_
  have hd : DifferentiableWithinAt ℝ G (Ici (0 : ℝ) ×ˢ univ) p :=
    (hG p hp).differentiableWithinAt (by simp)
  let L : (ℝ × ℝ) →L[ℝ] ℝ × (ℝ × ℝ) :=
    (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))
  have hι : HasFDerivWithinAt (fun y : ℝ × ℝ => (p.1, y)) L univ p.2 :=
    ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)).hasFDerivWithinAt
  have hmaps : MapsTo (fun y : ℝ × ℝ => (p.1, y)) univ (Ici (0 : ℝ) ×ˢ univ) :=
    fun y _ => ⟨hp.1, mem_univ y⟩
  have hcomp : HasFDerivWithinAt (fun y : ℝ × ℝ => G (p.1, y))
      ((fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ univ) p).comp L) univ p.2 := by
    have hp_eq : (p.1, p.2) = p := Prod.mk.eta
    have hd' : HasFDerivWithinAt G (fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ univ) p)
        (Ici (0 : ℝ) ×ˢ univ) (p.1, p.2) := by
      rw [hp_eq]
      exact hd.hasFDerivWithinAt
    exact hd'.comp p.2 hι hmaps
  have hfd : fderiv ℝ (fun y : ℝ × ℝ => G (p.1, y)) p.2 =
      (fderivWithin ℝ G (Ici (0 : ℝ) ×ˢ univ) p).comp L :=
    (hasFDerivWithinAt_univ.1 hcomp).fderiv
  unfold B0579.pd
  rw [hfd]
  rfl

lemma train_v_contOn {ν c t s : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (ht : 0 ≤ t) (l : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (Ico t s ×ˢ univ) := by
  have hsub : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun p hp => ⟨ht.trans hp.1.1, mem_univ _⟩
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (Ici (0 : ℝ) ×ˢ univ) :=
    (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  exact (hG.mono hsub).continuousOn

lemma train_pd_v_contOn {ν c t s : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    (ht : 0 ≤ t) (k l : Fin 2) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd k (fun y => tr.v p.1 y l) p.2)
      (Ico t s ×ˢ univ) := by
  have hsub : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun p hp => ⟨ht.trans hp.1.1, mem_univ _⟩
  have hG : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 l) (Ici (0 : ℝ) ×ˢ univ) :=
    (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      tr.isTrain.smooth_v
  exact ((contDiffOn_pd_halfST hG k).mono hsub).continuousOn

lemma train_iteratedFDeriv_bdd {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ht : 0 ≤ t) (hJ : ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S)
    {j : ℕ} (hj6 : j ≤ 6) (b : ℝ) (hb : b ∈ Ioo t s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ ∈ Ico t b, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (tr.v ρ) x‖ ≤ A := by
  obtain ⟨CJ, hCJ⟩ := hJ b (ht.trans hb.1.le)
  refine ⟨|CJ|, abs_nonneg CJ, fun ρ hρ x => ?_⟩
  have hρIcc : ρ ∈ Icc (0 : ℝ) b := ⟨ht.trans hρ.1, hρ.2.le⟩
  have h1x : 1 ≤ (1 + x.2 ^ 2) ^ ⌈max 0 ((m + 2) / 2)⌉₊ :=
    one_le_pow₀ (by nlinarith [sq_nonneg x.2])
  have hbd := (hCJ j hj6 ρ hρIcc x).trans (le_abs_self CJ)
  calc ‖iteratedFDeriv ℝ j (tr.v ρ) x‖
      ≤ (1 + x.2 ^ 2) ^ ⌈max 0 ((m + 2) / 2)⌉₊ * ‖iteratedFDeriv ℝ j (tr.v ρ) x‖ :=
        le_mul_of_one_le_left (norm_nonneg _) h1x
    _ ≤ |CJ| := hbd

lemma train_v_bdd {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ht : 0 ≤ t) (hJ : ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) (l : Fin 2)
    (b : ℝ) (hb : b ∈ Ioo t s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ ∈ Ico t b, ∀ x : ℝ × ℝ, |tr.v ρ x l| ≤ A := by
  obtain ⟨A, hA0, hA⟩ := train_iteratedFDeriv_bdd ht hJ (j := 0) (by omega) b hb
  refine ⟨A, hA0, fun ρ hρ x => ?_⟩
  calc |tr.v ρ x l| = ‖tr.v ρ x l‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖tr.v ρ x‖ := PiLp.norm_apply_le (tr.v ρ x) l
    _ = ‖iteratedFDeriv ℝ 0 (tr.v ρ) x‖ := (norm_iteratedFDeriv_zero (f := tr.v ρ) (x := x)).symm
    _ ≤ A := hA ρ hρ x

lemma train_pd_v_bdd {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ht : 0 ≤ t) (hJ : ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S) (k l : Fin 2)
    (b : ℝ) (hb : b ∈ Ioo t s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ ∈ Ico t b, ∀ x : ℝ × ℝ, |B0579.pd k (fun y => tr.v ρ y l) x| ≤ A := by
  obtain ⟨A, hA0, hA⟩ := train_iteratedFDeriv_bdd ht hJ (j := 1) (by omega) b hb
  refine ⟨A, hA0, fun ρ hρ x => ?_⟩
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr (ht.trans hρ.1)
  have hvl : ContDiff ℝ ∞ (fun y => tr.v ρ y l) :=
    (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  calc |B0579.pd k (fun y => tr.v ρ y l) x|
      = ‖iteratedFDeriv ℝ 0 (B0579.pd k (fun y => tr.v ρ y l)) x‖ := by
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ 1 (fun y => tr.v ρ y l) x‖ :=
        ChiBoundAux.norm_iteratedFDeriv_pd_le hvl k 0 x
    _ ≤ ‖iteratedFDeriv ℝ 1 (tr.v ρ) x‖ :=
        ChiBoundAux.norm_iteratedFDeriv_proj_le (tr.v ρ) hv l 1 x
    _ ≤ A := hA ρ hρ x

lemma inCX_transport {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ht : 0 ≤ t) (hJ : ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S)
    {φ : ℝ → ℝ × ℝ → ℂ}
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hSp : AdjSpatialCont c m t s 3 φ)
    {w : List (Fin 2)} (hw : w.length ≤ 1) :
    InCX c m t s (fun r x => adjSpatial w (ladTransport tr r (φ r)) x) := by
  have hterm0 : ∀ l : Fin 2,
      InCX c m t s (fun r x => ((tr.v r x l : ℝ) : ℂ) * adjSpatial [l] (φ r) x) :=
    fun l => InCX.ofReal_mul (train_v_contOn tr ht l) (train_v_bdd ht hJ l)
      (fun r hr => hSp r hr [l] (by simp))
  match w, hw with
  | [], _ =>
    exact ((hterm0 0).add (hterm0 1)).congr fun r _ => rfl
  | [k], _ =>
    have hterm1 : ∀ l : Fin 2,
        InCX c m t s (fun r x =>
          ((B0579.pd k (fun y => tr.v r y l) x : ℝ) : ℂ) * adjSpatial [l] (φ r) x +
          ((tr.v r x l : ℝ) : ℂ) * adjSpatial [k, l] (φ r) x) := fun l =>
      (InCX.ofReal_mul (train_pd_v_contOn tr ht k l) (train_pd_v_bdd ht hJ k l)
        (fun r hr => hSp r hr [l] (by simp))).add
        (InCX.ofReal_mul (train_v_contOn tr ht l) (train_v_bdd ht hJ l)
          (fun r hr => hSp r hr [k, l] (by simp)))
    refine ((hterm1 0).add (hterm1 1)).congr fun r hr => ?_
    have hφr : ContDiff ℝ ∞ (φ r) := adjContDiff_slice hj hr
    have hv : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr (ht.trans hr.1)
    have hvl : ∀ l : Fin 2, ContDiff ℝ ∞ (fun y => tr.v r y l) := fun l =>
      (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
    have hm_sm : ∀ l : Fin 2,
        ContDiff ℝ ∞ (fun x => ((tr.v r x l : ℝ) : ℂ) * pdCx l (φ r) x) := fun l =>
      (Complex.ofRealCLM.contDiff.comp (hvl l)).mul (contDiff_pdCx hφr l)
    have hadd := st_pdCx_add ((hm_sm 0).differentiable (by simp))
      ((hm_sm 1).differentiable (by simp)) k
    have hmul0 := st_pdCx_ofReal_mul ((hvl 0).differentiable (by simp))
      ((contDiff_pdCx hφr 0).differentiable (by simp)) k
    have hmul1 := st_pdCx_ofReal_mul ((hvl 1).differentiable (by simp))
      ((contDiff_pdCx hφr 1).differentiable (by simp)) k
    ext x
    have haddx : pdCx k (ladTransport tr r (φ r)) x =
        pdCx k (fun y => ((tr.v r y 0 : ℝ) : ℂ) * pdCx 0 (φ r) y) x +
          pdCx k (fun y => ((tr.v r y 1 : ℝ) : ℂ) * pdCx 1 (φ r) y) x :=
      congrFun hadd x
    have hm0x := congrFun hmul0 x
    have hm1x := congrFun hmul1 x
    dsimp at hm0x hm1x
    change pdCx k (ladTransport tr r (φ r)) x =
      ((B0579.pd k (fun y => tr.v r y 0) x : ℝ) : ℂ) * pdCx 0 (φ r) x +
        ((tr.v r x 0 : ℝ) : ℂ) * pdCx k (pdCx 0 (φ r)) x +
      (((B0579.pd k (fun y => tr.v r y 1) x : ℝ) : ℂ) * pdCx 1 (φ r) x +
        ((tr.v r x 1 : ℝ) : ℂ) * pdCx k (pdCx 1 (φ r)) x)
    rw [haddx, hm0x, hm1x]
  | _ :: _ :: _, hw => simp at hw

/-! ### Section 5: Localized interaction `adjSpatial w (ladChi tr φ r)` (`|w| ≤ 1`) -/

/-- Reference weight `B_wt m l x = (1 + x.2 ^ 2) ^ (-(m + 1) / 2)`. -/
def B_wt (m : ℝ) : Fin 2 → ℝ × ℝ → ℝ :=
  fun _ x => (1 + x.2 ^ 2) ^ (-((m + 1) / 2))

/-- Weighted vorticity gradient multiplier `aEc tr m j r x = (1 + x.2^2)^((m+1)/2) ∂_j E(r, x)`. -/
def aEc {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ) (j : Fin 2)
    (r : ℝ) (x : ℝ × ℝ) : ℝ :=
  (1 + x.2 ^ 2) ^ ((m + 1) / 2) * B0579.pd j (UnforcedLeray.B0238.Ec tr r) x

/-- Weighted source `gEc tr m φ j r x = aEc tr m j r x * φ r x`. -/
def gEc {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (j : Fin 2) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((aEc tr m j r x : ℝ) : ℂ) * φ r x

lemma B_wt_cont (m : ℝ) (l : Fin 2) : Continuous (B_wt m l) := by
  unfold B_wt
  exact (continuous_const.add (continuous_snd.pow 2)).rpow continuous_const
    (fun x => Or.inl (by dsimp; nlinarith [sq_nonneg x.2]))

lemma B_wt_bdd (m : ℝ) (l : Fin 2) (x : ℝ × ℝ) :
    (1 + x.2 ^ 2) ^ ((m + 1) / 2) * |B_wt m l x| ≤ 1 := by
  have hpos : 0 < 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
  unfold B_wt
  rw [abs_of_nonneg (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos, add_neg_cancel,
    Real.rpow_zero]

lemma gEc_mul_B_wt {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (j : Fin 2) (r : ℝ) (x : ℝ × ℝ) :
    gEc tr m φ j r x * (B_wt m j x : ℂ) =
      φ r x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) := by
  have hpos : 0 < 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
  have h1 : (1 + x.2 ^ 2) ^ ((m + 1) / 2) * (1 + x.2 ^ 2) ^ (-((m + 1) / 2)) = 1 := by
    rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero]
  have h2 : aEc tr m j r x * B_wt m j x = B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by
    unfold aEc B_wt
    calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) * B0579.pd j (UnforcedLeray.B0238.Ec tr r) x *
          (1 + x.2 ^ 2) ^ (-((m + 1) / 2))
        = ((1 + x.2 ^ 2) ^ ((m + 1) / 2) * (1 + x.2 ^ 2) ^ (-((m + 1) / 2))) *
          B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by ring
      _ = B0579.pd j (UnforcedLeray.B0238.Ec tr r) x := by rw [h1, one_mul]
  unfold gEc
  rw [← h2]
  push_cast
  ring

lemma inCX_gEc {ν c m t s : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ht : 0 ≤ t) (hJ : ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S)
    {φ : ℝ → ℝ × ℝ → ℂ} (hSp : AdjSpatialCont c m t s 3 φ) (j : Fin 2) :
    InCX c m t s (gEc tr m φ j) := by
  refine InCX.ofReal_mul ?_ ?_ (fun r hr => hSp r hr [] (by simp))
  · have hsub : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
      fun p hp => ⟨ht.trans hp.1.1, mem_univ _⟩
    have hpd : ContinuousOn
        (fun p : ℝ × (ℝ × ℝ) => B0579.pd j (UnforcedLeray.B0238.Ec tr p.1) p.2)
        (Ico t s ×ˢ univ) :=
      ((contDiffOn_pd_halfST (Ec_contDiffOn tr) j).mono hsub).continuousOn
    have hwt : Continuous (fun p : ℝ × (ℝ × ℝ) => (1 + p.2.2 ^ 2) ^ ((m + 1) / 2)) :=
      (continuous_const.add ((continuous_snd.comp continuous_snd).pow 2)).rpow
        continuous_const (fun p => Or.inl (by dsimp; nlinarith [sq_nonneg p.2.2]))
    exact hwt.continuousOn.mul hpd
  · intro b hb
    obtain ⟨CJ, hCJ⟩ := hJ b (ht.trans hb.1.le)
    refine ⟨2 * |CJ|, by positivity, fun ρ hρ x => ?_⟩
    let kw : ℕ := ⌈max 0 ((m + 2) / 2)⌉₊
    have h1x : 1 ≤ 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
    have hexp : (m + 1) / 2 ≤ (kw : ℝ) := by
      have h1 : (m + 1) / 2 ≤ (m + 2) / 2 := by linarith
      exact h1.trans ((le_max_right 0 _).trans (Nat.le_ceil _))
    have hw_le : (1 + x.2 ^ 2) ^ ((m + 1) / 2) ≤ (1 + x.2 ^ 2) ^ kw := by
      calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) ≤ (1 + x.2 ^ 2) ^ (kw : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1x hexp
        _ = (1 + x.2 ^ 2) ^ kw := Real.rpow_natCast _ _
    have hρ0 : 0 ≤ ρ := ht.trans hρ.1
    have hd_le := ChiBoundAux.norm_iteratedFDeriv_pd_Ec_le tr hρ0 j 0 x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hd_le
    have hρb : ρ ∈ Icc (0 : ℝ) b := ⟨hρ0, hρ.2.le⟩
    have htr_bd : (1 + x.2 ^ 2) ^ kw * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖ ≤ |CJ| :=
      (hCJ 2 (by omega) ρ hρb x).trans (le_abs_self CJ)
    unfold aEc
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x|
        ≤ (1 + x.2 ^ 2) ^ kw * (2 * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖) :=
          mul_le_mul hw_le hd_le (abs_nonneg _) (by positivity)
      _ = 2 * ((1 + x.2 ^ 2) ^ kw * ‖iteratedFDeriv ℝ 2 (tr.v ρ) x‖) := by ring
      _ ≤ 2 * |CJ| := mul_le_mul_of_nonneg_left htr_bd (by norm_num)

/-- General `H^1_{-m,c}` bound for any smooth `c`-periodic field `Ψ` paired against a vector source
`(f j * B_wt m j)_{j=0,1}` against kernel Biot-Savart test velocities. -/
lemma exists_chi_source_bound {m c : ℝ} (hm1 : 1 < m) (hc1 : 1 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (h : ℝ × ℝ → ℂ), MemLp h 2 (B0579.cellMeasure c (-m)) →
        ∀ j : Fin 2, IntegrableOn (fun x => h x * (B_wt m j x : ℂ)) (B0579.cell c) ∧
          MemLp (fun x => h x * (B_wt m j x : ℂ)) 2 (volume.restrict (B0579.cell c))) ∧
      ∀ (Ψ : ℝ × ℝ → ℂ) (f : Fin 2 → ℝ × ℝ → ℂ),
        ContDiff ℝ ∞ Ψ → (∀ x : ℝ × ℝ, Ψ (x.1 + c, x.2) = Ψ x) →
        (∀ j : Fin 2, MemLp (f j) 2 (B0579.cellMeasure c (-m))) →
        (∀ (ψ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ),
          B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ u →
          ∫ x in B0579.cell c, Ψ x * (ψ x : ℂ) =
            ∫ x in B0579.cell c, ∑ j : Fin 2, (f j x * (B_wt m j x : ℂ)) * (u x j : ℂ)) →
        ∀ w : List (Fin 2), w.length ≤ 1 →
          xNorm c (-m) (adjSpatial w Ψ) ≤
            ENNReal.ofReal C * ∑ j : Fin 2, xNorm c (-m) (f j) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨CS, hCS, HS0⟩ := _root_.ktSource m hm1 c hc0 1
  have HS := HS0 (B_wt m) (B_wt_cont m) (B_wt_bdd m)
  obtain ⟨CK, hCK, HK⟩ := kernelAdjointBound m hm1
  refine ⟨CK * CS, mul_nonneg hCK hCS,
    fun h hh j => ⟨(HS h hh j).1, (HS h hh j).2.1⟩, ?_⟩
  intro Ψ f hΨ_sm hΨ_per hf hΨ_pair
  let F : Fin 2 → ℝ × ℝ → ℂ := fun j x => f j x * (B_wt m j x : ℂ)
  have hFs := fun j => HS (f j) (hf j) j
  obtain ⟨χ0, gχ, hweak, hnorm, hpair⟩ :=
    HK c hc1 F (fun j => ⟨(hFs j).1, (hFs j).2.1⟩)
  have hH : h1Norm c m χ0 gχ ≤
      ENNReal.ofReal (CK * CS) * ∑ j : Fin 2, xNorm c (-m) (f j) := by
    calc h1Norm c m χ0 gχ
        ≤ ENNReal.ofReal CK * ∑ j : Fin 2, (eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
            eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) := hnorm
      _ ≤ ENNReal.ofReal CK * ∑ j : Fin 2, (ENNReal.ofReal CS * xNorm c (-m) (f j)) :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => (hFs j).2.2)
      _ = ENNReal.ofReal (CK * CS) * ∑ j : Fin 2, xNorm c (-m) (f j) := by
          rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.ofReal_mul hCK]
  have hsum_ne : (∑ j : Fin 2, xNorm c (-m) (f j)) ≠ ⊤ := by
    rw [Fin.sum_univ_two]
    exact ENNReal.add_ne_top.2 ⟨(hf 0).eLpNorm_ne_top, (hf 1).eLpNorm_ne_top⟩
  have hHtop : h1Norm c m χ0 gχ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum_ne) hH
  have hLb : ∀ R : ℝ, IntegrableOn Ψ (AdjE1.bandSet c R) :=
    fun R => AdjE1.continuous_bandInt hΨ_sm.continuous R
  have hbandχ := _root_.weakFieldBandInt m c χ0 gχ hc0 hweak hHtop
  have hae0 : Ψ =ᵐ[volume.restrict (B0579.cell c)] χ0 := by
    have hsub : (Ψ - χ0) =ᵐ[volume.restrict (B0579.cell c)] 0 := by
      refine _root_.cellUnique c (Ψ - χ0) hc0 (fun R => (hLb R).sub (hbandχ R).1) ?_
      intro ψ hψ
      obtain ⟨u, hu⟩ := _root_.kernelBSExists c ψ hc0 hψ
      have i1 := _root_.bandMulTest c Ψ ψ hc0 hLb hψ
      have i2 := _root_.bandMulTest c χ0 ψ hc0 (fun R => (hbandχ R).1) hψ
      rw [AdjE1.int_sub_mul c Ψ χ0 ψ i1 i2, hΨ_pair ψ u hψ hu, hpair ψ u hψ hu, sub_self]
    filter_upwards [hsub] with x hx
    exact sub_eq_zero.1 hx
  have haej : ∀ j : Fin 2, pdCx j Ψ =ᵐ[volume.restrict (B0579.cell c)] gχ j := by
    intro j
    have h1 := ibpPdCxWeak c j Ψ hc0 hΨ_sm hΨ_per
    have h1' : HasWeakCellDerivC c j χ0 (pdCx j Ψ) :=
      HasWeakCellDerivC.congr_ae hae0.symm (Eventually.of_forall fun _ => rfl) h1
    exact weakCellAeUnique c j χ0 (pdCx j Ψ) (gχ j) h1' (hweak j)
  obtain ⟨hxχ, hxg⟩ := ChiBoundAux.xNorm_le_h1Norm_both c m χ0 gχ
  intro w hw
  match w, hw with
  | [], _ =>
    have hae_cm : Ψ =ᵐ[B0579.cellMeasure c (-m)] χ0 := (B0579.cellMeasure_ac c (-m)) hae0
    change xNorm c (-m) Ψ ≤ _
    rw [xNorm, eLpNorm_congr_ae hae_cm]
    exact hxχ.trans hH
  | [j], _ =>
    have hae_cm : pdCx j Ψ =ᵐ[B0579.cellMeasure c (-m)] gχ j :=
      (B0579.cellMeasure_ac c (-m)) (haej j)
    change xNorm c (-m) (pdCx j Ψ) ≤ _
    rw [xNorm, eLpNorm_congr_ae hae_cm]
    exact (hxg j).trans hH
  | _ :: _ :: _, hw => simp at hw

/-- Approximating sequence `ρSeq r s n = r + (s - r) / (n + 2) ∈ Ioo t s` for `r ∈ Ico t s`. -/
def ρSeq (r s : ℝ) (n : ℕ) : ℝ := r + (s - r) / ((n + 2 : ℕ) : ℝ)

lemma ρSeq_mem_Ioo {t s r : ℝ} (hr : r ∈ Ico t s) (n : ℕ) :
    ρSeq r s n ∈ Ioo t s := by
  have hn : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 2)
  have hsr : 0 < s - r := sub_pos.2 hr.2
  refine ⟨?_, ?_⟩
  · dsimp [ρSeq]
    linarith [hr.1, div_pos hsr hn]
  · dsimp [ρSeq]
    have hdiv : (s - r) / ((n + 2 : ℕ) : ℝ) < s - r := div_lt_self hsr hn1
    linarith

lemma tendsto_ρSeq_nhdsWithin {t s r : ℝ} (hr : r ∈ Ico t s) :
    Tendsto (ρSeq r s) atTop (𝓝[Ico t s] r) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_,
    Eventually.of_forall fun n => Ioo_subset_Ico_self (ρSeq_mem_Ioo hr n)⟩
  have hat : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have h0 : Tendsto (fun n : ℕ => (s - r) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hat
  have hadd : Tendsto (ρSeq r s) atTop (𝓝 (r + 0)) :=
    tendsto_const_nhds.add h0
  rwa [add_zero] at hadd

lemma eLpNorm_le_of_ae_tendsto_seq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {q : ℝ≥0∞} {f : ℕ → α → E} {v : α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hv : ∀ᵐ y ∂μ, Tendsto (fun n => f n y) atTop (𝓝 (v y))) {R : ℕ → ℝ≥0∞} {R₀ : ℝ≥0∞}
    (hR : Tendsto R atTop (𝓝 R₀)) (hb : ∀ n, eLpNorm (f n) q μ ≤ R n) :
    eLpNorm v q μ ≤ R₀ :=
  (Lp.eLpNorm_lim_le_liminf_eLpNorm hf v hv).trans
    ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq hR.liminf_eq)

lemma inCX_ladChi {ν c m t s : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc1 : 1 ≤ c)
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    (hJ : ∀ S : ℝ, 0 ≤ S → TrainJetsBdd tr m S)
    (ht : 0 ≤ t) (hts : t < s) {g : ℝ × ℝ → ℂ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsAdjointWeak ν c m tr t s g φ)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hSp : AdjSpatialCont c m t s 3 φ)
    {w : List (Fin 2)} (hw : w.length ≤ 1) :
    InCX c m t s (fun r => adjSpatial w (ladChi tr φ r)) := by
  have hm1 : 1 < m := by linarith
  have hc0 : 0 < c := by linarith
  have hctx : AdjWCtx m ν c tr t s g φ := ⟨hν, hc0, ht, hts, hb, hφ, hj⟩
  have hgEc : ∀ j : Fin 2, InCX c m t s (gEc tr m φ j) :=
    fun j => inCX_gEc ht hJ hSp j
  obtain ⟨C, hC0, hHS, hBound⟩ := exists_chi_source_bound (m := m) (c := c) hm1 hc1
  have hpair_single : ∀ ρ ∈ Ioo t s, ∀ (ψ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → Fin 2 → ℝ),
      B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ u →
      ∫ x in B0579.cell c, ladChi tr φ ρ x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, ∑ j : Fin 2, (gEc tr m φ j ρ x * (B_wt m j x : ℂ)) * (u x j : ℂ) := by
    intro ρ hρ ψ u hψ hu
    rw [adjWeakPointwise m ν c tr t s g φ hctx ρ hρ ψ u hψ hu]
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => ?_
    simp only [Fin.sum_univ_two, gEc_mul_B_wt]
    push_cast
    ring
  have hbd_Ioo : ∀ ρ ∈ Ioo t s,
      xNorm c (-m) (adjSpatial w (ladChi tr φ ρ)) ≤
        ENNReal.ofReal C * ∑ j : Fin 2, xNorm c (-m) (gEc tr m φ j ρ) := by
    intro ρ hρ
    exact hBound (ladChi tr φ ρ) (fun j => gEc tr m φ j ρ)
      (ChiBoundAux.contDiff_ladChi tr ht hj hρ)
      (ChiBoundAux.periodic_ladChi tr ht hj hφ.periodic hρ)
      (fun j => (hgEc j ρ (Ioo_subset_Ico_self hρ)).1)
      (hpair_single ρ hρ) w hw
  have hbd_diff_Ioo : ∀ ρ₁ ∈ Ioo t s, ∀ ρ₂ ∈ Ioo t s,
      xNorm c (-m) (adjSpatial w (ladChi tr φ ρ₁) - adjSpatial w (ladChi tr φ ρ₂)) ≤
        ENNReal.ofReal C * ∑ j : Fin 2, xNorm c (-m) (gEc tr m φ j ρ₁ - gEc tr m φ j ρ₂) := by
    intro ρ₁ hρ₁ ρ₂ hρ₂
    have hsm1 := ChiBoundAux.contDiff_ladChi tr ht hj hρ₁
    have hsm2 := ChiBoundAux.contDiff_ladChi tr ht hj hρ₂
    have hper1 := ChiBoundAux.periodic_ladChi tr ht hj hφ.periodic hρ₁
    have hper2 := ChiBoundAux.periodic_ladChi tr ht hj hφ.periodic hρ₂
    have hsub_w : adjSpatial w (ladChi tr φ ρ₁) - adjSpatial w (ladChi tr φ ρ₂) =
        adjSpatial w (fun x => ladChi tr φ ρ₁ x - ladChi tr φ ρ₂ x) :=
      (st_adjSpatial_sub hsm1 hsm2 w).symm
    rw [hsub_w]
    refine hBound (fun x => ladChi tr φ ρ₁ x - ladChi tr φ ρ₂ x)
      (fun j => gEc tr m φ j ρ₁ - gEc tr m φ j ρ₂)
      (hsm1.sub hsm2)
      (fun x => by simp [hper1 x, hper2 x])
      (fun j => (hgEc j ρ₁ (Ioo_subset_Ico_self hρ₁)).1.sub
        (hgEc j ρ₂ (Ioo_subset_Ico_self hρ₂)).1)
      (fun ψ u hψ hu => ?_) w hw
    have i1 := _root_.bandMulTest c (ladChi tr φ ρ₁) ψ hc0
      (fun R => AdjE1.continuous_bandInt hsm1.continuous R) hψ
    have i2 := _root_.bandMulTest c (ladChi tr φ ρ₂) ψ hc0
      (fun R => AdjE1.continuous_bandInt hsm2.continuous R) hψ
    have hisub : ∫ x in B0579.cell c, (ladChi tr φ ρ₁ x - ladChi tr φ ρ₂ x) * (ψ x : ℂ) =
        (∫ x in B0579.cell c, ladChi tr φ ρ₁ x * (ψ x : ℂ)) -
          ∫ x in B0579.cell c, ladChi tr φ ρ₂ x * (ψ x : ℂ) :=
      AdjE1.int_sub_mul c (ladChi tr φ ρ₁) (ladChi tr φ ρ₂) ψ i1 i2
    rw [hisub, hpair_single ρ₁ hρ₁ ψ u hψ hu, hpair_single ρ₂ hρ₂ ψ u hψ hu]
    have hint : ∀ ρ ∈ Ioo t s, IntegrableOn
        (fun x => ∑ j : Fin 2, (gEc tr m φ j ρ x * (B_wt m j x : ℂ)) * (u x j : ℂ))
        (B0579.cell c) := by
      intro ρ hρ
      have h := UnforcedLeray.Short.IIIa.ktPairInt c
        (fun j x => gEc tr m φ j ρ x * (B_wt m j x : ℂ))
        (fun j => hHS (gEc tr m φ j ρ) (hgEc j ρ (Ioo_subset_Ico_self hρ)).1 j) ψ u hψ hu
      simpa [Fin.sum_univ_two] using h
    rw [← integral_sub (hint ρ₁ hρ₁) (hint ρ₂ hρ₂)]
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => ?_
    simp only [Fin.sum_univ_two, Pi.sub_apply]
    ring
  have hχw_cont : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (ladChi tr φ p.1) p.2)
      (Ico t s ×ˢ univ) :=
    (HigherContAux.jointSmooth_adjSpatial (jointSmooth_ladChi tr ht hj) w).continuousOn
  have hχw_slice_cont : ∀ r ∈ Ico t s, Continuous (adjSpatial w (ladChi tr φ r)) :=
    fun r hr => (contDiff_adjSpatial (adjContDiff_slice (jointSmooth_ladChi tr ht hj) hr) w).continuous
  have hχw_lim : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ,
      Tendsto (fun n => adjSpatial w (ladChi tr φ (ρSeq r s n)) x)
        atTop (𝓝 (adjSpatial w (ladChi tr φ r) x)) := by
    intro r hr x
    have h1 : ContinuousWithinAt (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (ladChi tr φ p.1) p.2)
        (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) (r, x) :=
      hχw_cont.continuousWithinAt ⟨hr, mem_univ x⟩
    have h2 : ContinuousWithinAt (fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) (Ico t s) r :=
      (continuous_id.prodMk continuous_const).continuousWithinAt
    have hc : ContinuousWithinAt (fun r' => adjSpatial w (ladChi tr φ r') x) (Ico t s) r :=
      ContinuousWithinAt.comp (f := fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ)))
        (g := fun p : ℝ × (ℝ × ℝ) => adjSpatial w (ladChi tr φ p.1) p.2)
        h1 h2 (fun r' hr' => ⟨hr', mem_univ x⟩)
    exact hc.tendsto.comp (tendsto_ρSeq_nhdsWithin hr)
  intro r hr
  refine ⟨?_, ?_⟩
  · -- Membership `MemLp (adjSpatial w (ladChi tr φ r)) 2` via `eLpNorm_le_of_ae_tendsto_seq`
    let R : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal C * ∑ j : Fin 2,
      (xNorm c (-m) (gEc tr m φ j (ρSeq r s n) - gEc tr m φ j r) +
        xNorm c (-m) (gEc tr m φ j r))
    have hR_lim : Tendsto R atTop
        (𝓝 (ENNReal.ofReal C * ∑ j : Fin 2, (0 + xNorm c (-m) (gEc tr m φ j r)))) := by
      refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun j _ => ?_)
        (Or.inr ENNReal.ofReal_ne_top)
      exact ((hgEc j r hr).2.comp (tendsto_ρSeq_nhdsWithin hr)).add tendsto_const_nhds
    have hbd_n : ∀ n : ℕ, xNorm c (-m) (adjSpatial w (ladChi tr φ (ρSeq r s n))) ≤ R n := by
      intro n
      have hρn := ρSeq_mem_Ioo hr n
      have hρn' := Ioo_subset_Ico_self hρn
      refine (hbd_Ioo (ρSeq r s n) hρn).trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_))
      have h1 := (hgEc j (ρSeq r s n) hρn').1
      have h2 := (hgEc j r hr).1
      have htri := eLpNorm_add_le (p := 2) (h1.sub h2).1 h2.1 (by norm_num)
      rwa [sub_add_cancel] at htri
    have hbound := eLpNorm_le_of_ae_tendsto_seq
      (fun n => (hχw_slice_cont _ (Ioo_subset_Ico_self (ρSeq_mem_Ioo hr n))).aestronglyMeasurable)
      (ae_of_all _ (hχw_lim r hr)) hR_lim hbd_n
    have hfin : ENNReal.ofReal C * ∑ j : Fin 2, (0 + xNorm c (-m) (gEc tr m φ j r)) < ⊤ := by
      rw [Fin.sum_univ_two, zero_add, zero_add]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.2 ⟨(hgEc 0 r hr).1.2, (hgEc 1 r hr).1.2⟩)
    exact ⟨(hχw_slice_cont r hr).aestronglyMeasurable, lt_of_le_of_lt hbound hfin⟩
  · -- Continuity `xNorm c (-m) (adjSpatial w (ladChi tr φ r') - adjSpatial w (ladChi tr φ r)) → 0`
    have hsum_tendsto : Tendsto
        (fun r' => ENNReal.ofReal C * ∑ j : Fin 2, xNorm c (-m) (gEc tr m φ j r' - gEc tr m φ j r))
        (𝓝[Ico t s] r) (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal C * ∑ _j : Fin 2, (0 : ℝ≥0∞) := by simp
      rw [h0]
      exact ENNReal.Tendsto.const_mul
        (tendsto_finsetSum _ fun j _ => (hgEc j r hr).2)
        (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_zero_of_le hsum_tendsto ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    let Rd : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal C * ∑ j : Fin 2,
      ((xNorm c (-m) (gEc tr m φ j (ρSeq r' s n) - gEc tr m φ j r') +
          xNorm c (-m) (gEc tr m φ j r' - gEc tr m φ j r)) +
        xNorm c (-m) (gEc tr m φ j (ρSeq r s n) - gEc tr m φ j r))
    have hRd_lim : Tendsto Rd atTop
        (𝓝 (ENNReal.ofReal C * ∑ j : Fin 2,
          ((0 + xNorm c (-m) (gEc tr m φ j r' - gEc tr m φ j r)) + 0))) := by
      refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun j _ => ?_)
        (Or.inr ENNReal.ofReal_ne_top)
      exact (((hgEc j r' hr').2.comp (tendsto_ρSeq_nhdsWithin hr')).add tendsto_const_nhds).add
        ((hgEc j r hr).2.comp (tendsto_ρSeq_nhdsWithin hr))
    simp only [zero_add, add_zero] at hRd_lim
    have hRd_bd : ∀ n : ℕ,
        xNorm c (-m) (adjSpatial w (ladChi tr φ (ρSeq r' s n)) -
          adjSpatial w (ladChi tr φ (ρSeq r s n))) ≤ Rd n := by
      intro n
      have h1 := ρSeq_mem_Ioo hr' n
      have h2 := ρSeq_mem_Ioo hr n
      have h1' := Ioo_subset_Ico_self h1
      have h2' := Ioo_subset_Ico_self h2
      refine (hbd_diff_Ioo (ρSeq r' s n) h1 (ρSeq r s n) h2).trans
        (mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_))
      have hm1 := (hgEc j (ρSeq r' s n) h1').1.sub (hgEc j r' hr').1
      have hm2 := (hgEc j r' hr').1.sub (hgEc j r hr).1
      have hm3 := (hgEc j (ρSeq r s n) h2').1.sub (hgEc j r hr).1
      have e : gEc tr m φ j (ρSeq r' s n) - gEc tr m φ j (ρSeq r s n) =
          ((gEc tr m φ j (ρSeq r' s n) - gEc tr m φ j r') +
            (gEc tr m φ j r' - gEc tr m φ j r)) -
          (gEc tr m φ j (ρSeq r s n) - gEc tr m φ j r) := by
        ext x; simp [Pi.sub_apply]
      rw [e]
      exact (eLpNorm_sub_le (p := 2) (hm1.add hm2).1 hm3.1 (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (p := 2) hm1.1 hm2.1 (by norm_num)) le_rfl)
    exact eLpNorm_le_of_ae_tendsto_seq
      (fun n => ((hχw_slice_cont _ (Ioo_subset_Ico_self (ρSeq_mem_Ioo hr' n))).sub
        (hχw_slice_cont _ (Ioo_subset_Ico_self (ρSeq_mem_Ioo hr n)))).aestronglyMeasurable)
      (ae_of_all _ fun x => (hχw_lim r' hr' x).sub (hχw_lim r hr x))
      hRd_lim hRd_bd

end TimeContAux

open TimeContAux in
/-- **(v) Time derivative `∂^w ∂_r φ ∈ C([t, s); X_{-m,c})` (`|w| ≤ 1`)**
(`PartIII-a:T21/2/7/2/4/4`, SP lines 3060-3073). -/
theorem adjHigherTimeCont (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjHigherTimeCont m := by
  intro ν hν hν1 tr hb hJ t s ht hts G _hG φ hφ hj hSp r hr w hw
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hχ : InCX c m t s (fun r' => adjSpatial w (ladChi tr φ r')) :=
    inCX_ladChi hm hν hc1 tr hb hJ ht hts hφ hj hSp hw
  have hlap : InCX c m t s (fun r' x => (ν : ℂ) * adjSpatial w (ladLapCx (φ r')) x) :=
    inCX_lap hj hSp hw
  have htr : InCX c m t s (fun r' x => adjSpatial w (ladTransport tr r' (φ r')) x) :=
    inCX_transport ht hJ hj hSp hw
  have hdt : InCX c m t s (fun r' => adjSpatial w (adjDt t s φ r')) :=
    ((hχ.sub hlap).sub htr).congr (fun r' hr' => adjSpatial_adjDt_decomp tr ht hj hr' w)
  exact hdt r hr

end UnforcedLeray.Short.IIIa
