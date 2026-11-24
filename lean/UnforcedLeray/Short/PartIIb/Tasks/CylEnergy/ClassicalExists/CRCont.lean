import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRDeriv

/-!


Proves `CRCont` (`Sub/T22_1_10.lean`). Source `the November 2 reference manuscript`,
lines 2074-2093 and 2103-2105.

Route: the Duhamel integral `∫_s^τ Op(ν(τ-r)) (g r) x dr` is rewritten as the integral over the
fixed interval `t ∈ (0, T-s]` (substitution `r = τ - t`, indicator of `t ≤ τ - s`). The integrand
is `Op(νt)(g(τ-t))(x)`, and for `t > 0` the scaled representation of the heat operators
(`HC.heatSG_pos_eq`, `DPC.heatSGd_pos_eq`) makes it jointly continuous in `(τ, x)` through a
clamped extension of `g`. The majorant `2 e^{ν(T-s)} M0 (1 + ν^{-1/2} t^{-1/2})` is independent
of `τ`, so `intervalIntegral.continuousWithinAt_of_dominated_interval` applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace CC

/-- Clamp of the time variable into `[s, T]`. -/
def clampT (s T σ : ℝ) : ℝ := min T (max s σ)

lemma clampT_mem {s T : ℝ} (hsT : s ≤ T) (σ : ℝ) : clampT s T σ ∈ Icc s T :=
  ⟨le_min hsT (le_max_left _ _), min_le_left _ _⟩

lemma clampT_of_mem {s T σ : ℝ} (h : σ ∈ Icc s T) : clampT s T σ = σ := by
  unfold clampT
  rw [max_eq_right h.1, min_eq_right h.2]

/-- The clamped extension of a jointly continuous `g` is jointly continuous on `ℝ × Pl`. -/
lemma gext_continuous {s T : ℝ} (hsT : s ≤ T) {g : ℝ → Pl → ℝ}
    (hg : ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ)) :
    Continuous (fun q : ℝ × Pl => g (clampT s T q.1) q.2) := by
  have hcl : Continuous (fun σ : ℝ => clampT s T σ) := by
    unfold clampT
    exact continuous_const.min (continuous_const.max continuous_id)
  have hc : Continuous (fun q : ℝ × Pl => (clampT s T q.1, q.2)) :=
    (hcl.comp continuous_fst).prodMk continuous_snd
  have hmap : MapsTo (fun q : ℝ × Pl => (clampT s T q.1, q.2)) univ (Icc s T ×ˢ univ) :=
    fun q _ => ⟨clampT_mem hsT q.1, mem_univ _⟩
  exact continuousOn_univ.mp (hg.comp hc.continuousOn hmap)

/-- The `t`-integrand: `e^{νt Δ}`-type scaled integral of the clamped extension of `g`. -/
def psiI (ν s T : ℝ) (κ : ℝ → ℝ) (ℓ : Pl → ℝ) (g : ℝ → Pl → ℝ) (z : ℝ × Pl) (t : ℝ) : ℝ :=
  ∫ w : Pl, κ (ν * t) * ℓ w * heatK 1 w * g (clampT s T (z.1 - t)) (z.2 - Real.sqrt (ν * t) • w)

/-- The `t`-integrand cut off at `t ≤ τ - s`. -/
def indF (ν s T : ℝ) (κ : ℝ → ℝ) (ℓ : Pl → ℝ) (g : ℝ → Pl → ℝ) (z : ℝ × Pl) (t : ℝ) : ℝ :=
  Set.indicator (Iic (z.1 - s)) (fun t' => psiI ν s T κ ℓ g z t') t

/-- Joint continuity of `(z, t) ↦ psiI z t` at `t0 > 0`. -/
lemma psi_jointAt {ν s T : ℝ} (hν : 0 < ν) (hsT : s ≤ T) {g : ℝ → Pl → ℝ} {M0 : ℝ}
    (hg : ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ))
    (hgM : ∀ r ∈ Icc s T, ∀ y : Pl, |g r y| ≤ M0)
    {κ : ℝ → ℝ} (hκ : ∀ a : ℝ, 0 < a → ContinuousAt κ a)
    {ℓ : Pl → ℝ} (hℓ : Continuous ℓ) (hℓi : Integrable (fun w : Pl => |ℓ w| * heatK 1 w))
    (z0 : ℝ × Pl) (t0 : ℝ) (ht0 : 0 < t0) :
    ContinuousAt (fun p : (ℝ × Pl) × ℝ => psiI ν s T κ ℓ g p.1 p.2) (z0, t0) := by
  have hG : Continuous (fun q : ℝ × Pl => g (clampT s T q.1) q.2) := gext_continuous hsT hg
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hgM s ⟨le_rfl, hsT⟩ 0)
  have hκc : ContinuousAt (fun p : (ℝ × Pl) × ℝ => κ (ν * p.2)) (z0, t0) := by
    have h1 : ContinuousAt (fun p : (ℝ × Pl) × ℝ => ν * p.2) (z0, t0) :=
      continuousAt_const.mul continuousAt_snd
    exact ContinuousAt.comp (f := fun p : (ℝ × Pl) × ℝ => ν * p.2) (hκ (ν * t0) (mul_pos hν ht0)) h1
  have hκa : ∀ᶠ p in 𝓝 (z0, t0), |κ (ν * p.2)| < |κ (ν * t0)| + 1 := by
    have h1 : Tendsto (fun p : (ℝ × Pl) × ℝ => |κ (ν * p.2)|) (𝓝 (z0, t0))
        (𝓝 |κ (ν * t0)|) := continuous_abs.continuousAt.comp hκc
    exact h1.eventually (gt_mem_nhds (lt_add_one _))
  have hC0 : 0 ≤ |κ (ν * t0)| + 1 := by positivity
  unfold psiI
  refine continuousAt_of_dominated (bound := fun w => (|κ (ν * t0)| + 1) * M0 * (|ℓ w| * heatK 1 w))
    ?_ ?_ (hℓi.const_mul _) ?_
  · refine Eventually.of_forall (fun p => ?_)
    refine Continuous.aestronglyMeasurable ?_
    exact ((continuous_const.mul hℓ).mul HC.heatK1_continuous).mul
      (hG.comp (f := fun w : Pl => (p.1.1 - p.2, p.1.2 - Real.sqrt (ν * p.2) • w))
        (by fun_prop))
  · filter_upwards [hκa] with p hp
    refine ae_of_all _ (fun w => ?_)
    have hK : 0 < heatK 1 w := (heatKernelMoments 1 one_pos).1 w
    have hGb : |g (clampT s T (p.1.1 - p.2)) (p.1.2 - Real.sqrt (ν * p.2) • w)| ≤ M0 :=
      hgM _ (clampT_mem hsT _) _
    rw [Real.norm_eq_abs]
    calc |κ (ν * p.2) * ℓ w * heatK 1 w * g (clampT s T (p.1.1 - p.2))
          (p.1.2 - Real.sqrt (ν * p.2) • w)|
        = (|κ (ν * p.2)| * |g (clampT s T (p.1.1 - p.2)) (p.1.2 - Real.sqrt (ν * p.2) • w)|) *
            (|ℓ w| * heatK 1 w) := by
          simp only [abs_mul, abs_of_pos hK]
          ring
      _ ≤ ((|κ (ν * t0)| + 1) * M0) * (|ℓ w| * heatK 1 w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hp.le hGb (abs_nonneg _) hC0)
            (mul_nonneg (abs_nonneg _) hK.le)
  · refine ae_of_all _ (fun w => ?_)
    have hcont : Continuous (fun p : (ℝ × Pl) × ℝ =>
        ((p.1.1 - p.2, p.1.2 - Real.sqrt (ν * p.2) • w) : ℝ × Pl)) := by
      refine Continuous.prodMk ?_ ?_
      · exact (continuous_fst.comp continuous_fst).sub continuous_snd
      · exact (continuous_snd.comp continuous_fst).sub
          (((Real.continuous_sqrt.comp (continuous_const.mul continuous_snd))).smul
            continuous_const)
    have hG' : ContinuousAt (fun p : (ℝ × Pl) × ℝ =>
        g (clampT s T (p.1.1 - p.2)) (p.1.2 - Real.sqrt (ν * p.2) • w)) (z0, t0) :=
      (hG.comp hcont).continuousAt
    exact (((hκc.mul continuousAt_const).mul continuousAt_const).mul hG')

/-- The clamped integrand agrees with `g` for `τ - t ∈ [s, T]`. -/
lemma psi_eq {ν s T : ℝ} (hν : 0 < ν) {g : ℝ → Pl → ℝ}
    {Op : ℝ → (Pl → ℝ) → Pl → ℝ} {κ : ℝ → ℝ} {ℓ : Pl → ℝ}
    (hOp : ∀ a : ℝ, 0 < a → ∀ (h : Pl → ℝ) (x : Pl),
      Op a h x = ∫ w : Pl, κ a * ℓ w * heatK 1 w * h (x - Real.sqrt a • w))
    (z : ℝ × Pl) (t : ℝ) (ht : 0 < t) (hmem : z.1 - t ∈ Icc s T) :
    psiI ν s T κ ℓ g z t = Op (ν * t) (g (z.1 - t)) z.2 := by
  rw [hOp (ν * t) (mul_pos hν ht) (g (z.1 - t)) z.2]
  unfold psiI
  rw [clampT_of_mem hmem]

/-- **Generic continuity of a Duhamel integral.** -/
lemma gen_cont {ν s T : ℝ} (hν : 0 < ν) (hsT : s ≤ T) {g : ℝ → Pl → ℝ} {M0 : ℝ}
    (hg : ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ))
    (hgM : ∀ r ∈ Icc s T, ∀ y : Pl, |g r y| ≤ M0)
    {Op : ℝ → (Pl → ℝ) → Pl → ℝ} {κ : ℝ → ℝ} (hκ : ∀ a : ℝ, 0 < a → ContinuousAt κ a)
    {ℓ : Pl → ℝ} (hℓ : Continuous ℓ) (hℓi : Integrable (fun w : Pl => |ℓ w| * heatK 1 w))
    (hOp : ∀ a : ℝ, 0 < a → ∀ (h : Pl → ℝ) (x : Pl),
      Op a h x = ∫ w : Pl, κ a * ℓ w * heatK 1 w * h (x - Real.sqrt a • w))
    (B : ℝ → ℝ) (hB0 : ∀ t : ℝ, 0 < t → 0 ≤ B t) (hB : IntervalIntegrable B volume 0 (T - s))
    (hdom : ∀ τ ∈ Icc s T, ∀ t : ℝ, 0 < t → t ≤ τ - s → ∀ x : Pl,
      |Op (ν * t) (g (τ - t)) x| ≤ B t) :
    ContinuousOn (fun z : ℝ × Pl => ∫ r in s..z.1, Op (ν * (z.1 - r)) (g r) z.2)
      (Icc s T ×ˢ univ) := by
  have hTs : (0 : ℝ) ≤ T - s := by linarith
  have hpsiAt : ∀ z0 : ℝ × Pl, ∀ t0 : ℝ, 0 < t0 →
      ContinuousAt (fun p : (ℝ × Pl) × ℝ => psiI ν s T κ ℓ g p.1 p.2) (z0, t0) :=
    fun z0 t0 ht0 => psi_jointAt hν hsT hg hgM hκ hℓ hℓi z0 t0 ht0
  have hpsiT : ∀ t0 : ℝ, 0 < t0 → ∀ z0 : ℝ × Pl,
      ContinuousAt (fun z => psiI ν s T κ ℓ g z t0) z0 := by
    intro t0 ht0 z0
    exact ContinuousAt.comp (f := fun z : ℝ × Pl => (z, t0)) (hpsiAt z0 t0 ht0)
      (Continuous.continuousAt (f := fun z : ℝ × Pl => (z, t0)) (continuous_id.prodMk continuous_const))
  have hpsiZ : ∀ z : ℝ × Pl, ContinuousOn (fun t => psiI ν s T κ ℓ g z t) (Ioi 0) := by
    intro z t0 ht0
    exact (ContinuousAt.comp (f := fun t : ℝ => (z, t)) (hpsiAt z t0 ht0)
      (Continuous.continuousAt (f := fun t : ℝ => (z, t)) (continuous_const.prodMk continuous_id))
      ).continuousWithinAt
  -- identity: the integral over `r ∈ [s, τ]` equals the cut-off integral over `t ∈ (0, T - s]`
  have hPsiEq : ∀ z ∈ Icc s T ×ˢ (univ : Set Pl), ∀ t : ℝ, 0 < t → t ≤ z.1 - s →
      psiI ν s T κ ℓ g z t = Op (ν * t) (g (z.1 - t)) z.2 := by
    intro z hz t ht htz
    exact psi_eq hν hOp z t ht ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have hIdent : ∀ z ∈ Icc s T ×ˢ (univ : Set Pl),
      ∫ r in s..z.1, Op (ν * (z.1 - r)) (g r) z.2
        = ∫ t in (0 : ℝ)..(T - s), indF ν s T κ ℓ g z t := by
    rintro ⟨τ, x⟩ hz
    have hτ : τ ∈ Icc s T := hz.1
    have hτs : 0 ≤ τ - s := by linarith [hτ.1]
    have hsub : ∫ r in s..τ, Op (ν * (τ - r)) (g r) x
        = ∫ t in (0 : ℝ)..(τ - s), Op (ν * t) (g (τ - t)) x := by
      have := intervalIntegral.integral_comp_sub_left
        (f := fun t => Op (ν * t) (g (τ - t)) x) (a := s) (b := τ) (d := τ)
      simpa only [sub_sub_cancel, sub_self] using this
    rw [hsub, intervalIntegral.integral_of_le hτs,
      intervalIntegral.integral_of_le hTs]
    have hEq : ∫ t in Ioc (0 : ℝ) (τ - s), Op (ν * t) (g (τ - t)) x
        = ∫ t in Ioc (0 : ℝ) (τ - s), psiI ν s T κ ℓ g (τ, x) t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact (hPsiEq (τ, x) hz t ht.1 ht.2).symm
    have hRHS : ∫ t in Ioc (0 : ℝ) (T - s), indF ν s T κ ℓ g (τ, x) t
        = ∫ t in Ioc (0 : ℝ) (τ - s), psiI ν s T κ ℓ g (τ, x) t := by
      unfold indF
      rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic]
      rw [min_eq_right (show τ - s ≤ T - s by linarith [hτ.2])]
    rw [hEq, hRHS]
  -- continuity of the cut-off integral
  have hCont : ∀ z0 ∈ Icc s T ×ˢ (univ : Set Pl),
      ContinuousWithinAt (fun z => ∫ t in (0 : ℝ)..(T - s), indF ν s T κ ℓ g z t)
        (Icc s T ×ˢ univ) z0 := by
    intro z0 hz0
    refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := B) ?_ ?_ hB ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      rw [uIoc_of_le hTs]
      unfold indF
      exact (((hpsiZ z).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc).indicator
        measurableSet_Iic
    · refine eventually_nhdsWithin_of_forall (fun z hz => ?_)
      refine ae_of_all _ (fun t ht => ?_)
      rw [uIoc_of_le hTs] at ht
      by_cases h : t ≤ z.1 - s
      · unfold indF
        rw [Set.indicator_of_mem (show t ∈ Iic (z.1 - s) from h)]
        rw [hPsiEq z hz t ht.1 h, Real.norm_eq_abs]
        exact hdom z.1 hz.1 t ht.1 h z.2
      · unfold indF
        rw [Set.indicator_of_notMem (show t ∉ Iic (z.1 - s) from h), norm_zero]
        exact hB0 t ht.1
    · filter_upwards [DiffC.ae_ne_point (z0.1 - s)] with t hne ht
      rw [uIoc_of_le hTs] at ht
      have ht0 : 0 < t := ht.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hev : ∀ᶠ z in 𝓝 z0, t < z.1 - s :=
          Filter.Tendsto.eventually (continuous_fst.sub continuous_const).continuousAt
            (lt_mem_nhds hlt)
        have h1 : ∀ᶠ z in 𝓝[Icc s T ×ˢ univ] z0,
            indF ν s T κ ℓ g z t = psiI ν s T κ ℓ g z t :=
          eventually_nhdsWithin_of_eventually_nhds (hev.mono fun z hz => by
            unfold indF
            exact Set.indicator_of_mem (show t ∈ Iic (z.1 - s) from le_of_lt hz) _)
        have hx : indF ν s T κ ℓ g z0 t = psiI ν s T κ ℓ g z0 t := by
          unfold indF
          exact Set.indicator_of_mem (show t ∈ Iic (z0.1 - s) from le_of_lt hlt) _
        exact ((hpsiT t ht0 z0).continuousWithinAt).congr_of_eventuallyEq h1 hx
      · have hev : ∀ᶠ z in 𝓝 z0, z.1 - s < t :=
          Filter.Tendsto.eventually (continuous_fst.sub continuous_const).continuousAt
            (Iio_mem_nhds hgt)
        have h1 : ∀ᶠ z in 𝓝[Icc s T ×ˢ univ] z0,
            indF ν s T κ ℓ g z t = 0 :=
          eventually_nhdsWithin_of_eventually_nhds (hev.mono fun z hz => by
            unfold indF
            exact Set.indicator_of_notMem (show t ∉ Iic (z.1 - s) from not_le.2 hz) _)
        have hx : indF ν s T κ ℓ g z0 t = 0 := by
          unfold indF
          exact Set.indicator_of_notMem (show t ∉ Iic (z0.1 - s) from not_le.2 hgt) _
        exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq h1 hx
  have hQ : ContinuousOn (fun z : ℝ × Pl => ∫ t in (0 : ℝ)..(T - s), indF ν s T κ ℓ g z t)
      (Icc s T ×ˢ univ) := fun z hz => hCont z hz
  exact hQ.congr (fun z hz => hIdent z hz)

/-- The majorant `2 e^{ν(T-s)} M0 (1 + ν^{-1/2} t^{-1/2})`. -/
def kB (ν s T M0 : ℝ) (t : ℝ) : ℝ :=
  2 * Real.exp (ν * (T - s)) * M0 + 2 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ)) *
    t ^ (-(1 / 2 : ℝ))

lemma kB_nonneg {ν s T M0 : ℝ} (hν : 0 < ν) (hM0 : 0 ≤ M0) {t : ℝ} (ht : 0 < t) :
    0 ≤ kB ν s T M0 t := by
  have hA : 0 ≤ 2 * Real.exp (ν * (T - s)) * M0 := mul_nonneg (by positivity) hM0
  have hC : 0 ≤ 2 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hA (Real.rpow_nonneg hν.le _)
  have hp : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  unfold kB
  nlinarith [mul_nonneg hC hp]

lemma kB_int (ν s T M0 : ℝ) : IntervalIntegrable (kB ν s T M0) volume 0 (T - s) := by
  unfold kB
  exact intervalIntegrable_const.add
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _)

lemma kB_ge {ν s T M0 : ℝ} (hν : 0 < ν) (hM0 : 0 ≤ M0) {t : ℝ} (ht : 0 < t) :
    2 * Real.exp (ν * (T - s)) * M0 ≤ kB ν s T M0 t := by
  have hA : 0 ≤ 2 * Real.exp (ν * (T - s)) * M0 := mul_nonneg (by positivity) hM0
  have hC : 0 ≤ 2 * Real.exp (ν * (T - s)) * M0 * ν ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hA (Real.rpow_nonneg hν.le _)
  have hp : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  unfold kB
  nlinarith [mul_nonneg hC hp]

lemma wb_abs {B : ℝ} {h : Pl → ℝ} (hB : WB B h) (y : Pl) : |h y| ≤ B := by
  have h1 := hB y
  have hc : 1 ≤ Real.cosh y.2 := Real.one_le_cosh _
  have h0 : 0 ≤ |h y| := abs_nonneg _
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hc)]

lemma hv_coord (i : Fin 2) : Continuous (fun w : Pl => ![w.1, w.2] i) := by
  fin_cases i <;> simp [continuous_fst, continuous_snd]

/-- Integrability of `|w_j| K_1(w)` from the first-moment bound of the heat kernel. -/
lemma abs_coord_int (j : Fin 2) : Integrable (fun w : Pl => |![w.1, w.2] j| * heatK 1 w) := by
  have hint := ((heatKernelMoments 1 one_pos).2.2.2.2.2 j).1
  have hc : Continuous (heatKd j 1) := by
    unfold heatKd
    exact ((hv_coord j).neg.div_const (2 * 1)).mul HC.heatK1_continuous
  have hmeas : AEStronglyMeasurable (fun w : Pl => |heatKd j 1 w|) volume :=
    (continuous_abs.comp hc).aestronglyMeasurable
  have hI : Integrable (fun w : Pl => |heatKd j 1 w|) :=
    Integrable.mono' hint hmeas (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_abs]
      exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _))
  have heq : (fun w : Pl => |![w.1, w.2] j| * heatK 1 w) = fun w : Pl => 2 * |heatKd j 1 w| := by
    funext w
    have hK : 0 < heatK 1 w := (heatKernelMoments 1 one_pos).1 w
    have hd : |heatKd j 1 w| = |![w.1, w.2] j| / 2 * heatK 1 w := by
      unfold heatKd
      rw [abs_mul, abs_div, abs_neg, abs_of_pos hK]
      norm_num
    rw [hd]
    ring
  rw [heq]
  exact hI.const_mul 2

end CC

open CC

/-- **`PartII-b:T22/1/10/3`** Joint continuity of `G`, `∂_j G`, `∂_i ∂_j G` on `[s, T] × Pl`. -/
theorem crCont : UnforcedLeray.Short.IIb.CylPDE.CRCont := by
  intro ν s T hν hsT F b hH
  have hCRD : ∀ τ ∈ Icc s T, ContDiff ℝ 2 (duhamelConv ν s F τ) ∧ CRFormulas ν s F τ :=
    fun τ hτ => crDeriv ν s T hν hsT F b hH τ hτ
  have hFo : ∀ τ ∈ Icc s T, CRFormulas ν s F τ := fun τ hτ => (hCRD τ hτ).2
  have hf1 : ∀ τ ∈ Icc s T, ∀ (i : Fin 2) (x : Pl), B0579.pd i (duhamelConv ν s F τ) x =
      ∫ r in s..τ, heatSGd i (ν * (τ - r)) (F r) x := fun τ hτ => by
    obtain ⟨h1, _⟩ := hFo τ hτ
    exact h1
  have hf2 : ∀ τ ∈ Icc s T, ∀ (i j : Fin 2) (x : Pl),
      B0579.pd i (B0579.pd j (duhamelConv ν s F τ)) x =
        ∫ r in s..τ, heatSGd i (ν * (τ - r)) (B0579.pd j (F r)) x := fun τ hτ => by
    obtain ⟨_, h2⟩ := hFo τ hτ
    exact h2
  obtain ⟨hF, hb, hb0, hFb⟩ := hH
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := s) (b := T)).exists_bound_of_continuousOn hb
  have hM' : ∀ r ∈ Icc s T, |b r| ≤ M0 := fun r hr => by
    have := hM0 r hr
    rwa [Real.norm_eq_abs] at this
  have hM0nn : 0 ≤ M0 := (abs_nonneg _).trans (hM' s ⟨le_rfl, hsT⟩)
  have hgF : ∀ r ∈ Icc s T, ∀ y : Pl, |F r y| ≤ M0 := fun r hr y =>
    (wb_abs (hFb r hr).1 y).trans ((le_abs_self _).trans (hM' r hr))
  have hgD : ∀ j : Fin 2, ∀ r ∈ Icc s T, ∀ y : Pl, |B0579.pd j (F r) y| ≤ M0 :=
    fun j r hr y => (wb_abs ((hFb r hr).2 j) y).trans ((le_abs_self _).trans (hM' r hr))
  have hκD : ∀ a : ℝ, 0 < a → ContinuousAt (fun a : ℝ => -1 / (2 * Real.sqrt a)) a :=
    fun a ha => ContinuousAt.div continuousAt_const
      (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
      (mul_pos two_pos (Real.sqrt_pos.2 ha)).ne'
  have hOpD : ∀ (j : Fin 2) (a : ℝ), 0 < a → ∀ (h : Pl → ℝ) (x : Pl),
      heatSGd j a h x = ∫ w : Pl, (-1 / (2 * Real.sqrt a)) * ![w.1, w.2] j * heatK 1 w *
        h (x - Real.sqrt a • w) := by
    intro j a ha h x
    rw [DPC.heatSGd_pos_eq ha j h x]
    congr 1
    funext w
    ring
  have hdomD : ∀ (g : ℝ → Pl → ℝ), (∀ r ∈ Icc s T, WB (b r) (g r)) → ∀ i : Fin 2,
      ∀ τ ∈ Icc s T, ∀ t : ℝ, 0 < t → t ≤ τ - s → ∀ x : Pl,
        |heatSGd i (ν * t) (g (τ - t)) x| ≤ kB ν s T M0 t := by
    intro g hg i τ hτ t ht htτ x
    have hmem : τ - t ∈ Icc s T := ⟨by linarith, by linarith [hτ.2]⟩
    have h := DiffC.heatSGd_bound_int hν hτ.2 hmem.1 (by linarith : τ - t < τ)
      ((le_abs_self _).trans (hM' _ hmem)) (hb0 _ hmem) (hg _ hmem) i x
    rw [sub_sub_cancel] at h
    unfold kB
    linarith
  have hBint := kB_int ν s T M0
  have hℓ1i : Integrable (fun w : Pl => |(fun _ : Pl => (1 : ℝ)) w| * heatK 1 w) := by
    simpa using (heatKernelMoments 1 one_pos).2.1
  -- part 1: `G` itself
  have part1 : ContinuousOn (fun z : ℝ × Pl => duhamelConv ν s F z.1 z.2) (Icc s T ×ˢ univ) := by
    unfold duhamelConv
    refine gen_cont (Op := heatSG) (κ := fun _ => (1 : ℝ)) hν hsT hF.contF hgF
      (fun _ _ => continuousAt_const) continuous_const hℓ1i
      (fun a ha h x => by rw [HC.heatSG_pos_eq ha h x]; simp) (kB ν s T M0)
      (fun t ht => kB_nonneg hν hM0nn ht) hBint ?_
    intro τ hτ t ht htτ x
    have hmem : τ - t ∈ Icc s T := ⟨by linarith, by linarith [hτ.2]⟩
    have h := DiffC.heatSG_bound_aux hν hτ.2 hmem.1 (by linarith : τ - t ≤ τ)
      ((le_abs_self _).trans (hM' _ hmem)) (hb0 _ hmem) (hFb _ hmem).1 x
    rw [sub_sub_cancel] at h
    exact h.trans (kB_ge hν hM0nn ht)
  -- part 2: first derivatives
  have part2 : ∀ j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd j (duhamelConv ν s F z.1) z.2) (Icc s T ×ˢ univ) := by
    intro j
    refine ContinuousOn.congr (gen_cont (Op := heatSGd j)
      (κ := fun a : ℝ => -1 / (2 * Real.sqrt a)) (ℓ := fun w : Pl => ![w.1, w.2] j) hν hsT
      hF.contF hgF hκD (hv_coord j) (abs_coord_int j) (hOpD j) (kB ν s T M0)
      (fun t ht => kB_nonneg hν hM0nn ht) hBint (hdomD F (fun r hr => (hFb r hr).1) j)) ?_
    intro z hz
    exact hf1 z.1 hz.1 j z.2
  -- part 3: second derivatives
  have part3 : ∀ i j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (duhamelConv ν s F z.1)) z.2) (Icc s T ×ˢ univ) := by
    intro i j
    refine ContinuousOn.congr (gen_cont (Op := heatSGd i)
      (g := fun r => B0579.pd j (F r)) (M0 := M0)
      (κ := fun a : ℝ => -1 / (2 * Real.sqrt a)) (ℓ := fun w : Pl => ![w.1, w.2] i) hν hsT
      (hF.contdF j) (hgD j) hκD (hv_coord i) (abs_coord_int i) (hOpD i) (kB ν s T M0)
      (fun t ht => kB_nonneg hν hM0nn ht) hBint
      (hdomD (fun r => B0579.pd j (F r)) (fun r hr => (hFb r hr).2 j) i)) ?_
    intro z hz
    exact hf2 z.1 hz.1 i j z.2
  exact ⟨part1, part2, part3⟩

end UnforcedLeray.Short.IIb.CylPDE
