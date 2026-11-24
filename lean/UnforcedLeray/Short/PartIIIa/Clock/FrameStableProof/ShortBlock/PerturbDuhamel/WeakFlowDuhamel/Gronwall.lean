import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3

/-!
# Moving-time Gronwall lemma (helper of `WeakFlowDuhamel.lean`, task `PartIII-a:T21/c3/3/1/1`)

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958
and 2982-2988: the free moving bound `e^{μ₀ (z - z')}` (`eq:short-causal-free-moving`) and a
bounded perturbation of size `C` combine into the raw moving-time rate `μ₀ + C`.

Moving time is `z = movingZ ν`, with `dz = a(r)⁻² dr` (`hasDerivAt_movingZ`).

* `gronwall_normalized`: if `ψ` is bounded on `[t₁, t₂]` and
  `ψ(s) ≤ A + ∫_{(t₁, s]} a(r)⁻² (C ψ(r) + g(r)) dr` for all `s ∈ [t₁, t₂]` with `g` measurable,
  then `ψ(t₂) ≤ e^{C (z_{t₂} - z_{t₁})} A + ∫_{(t₁, t₂]} a(r)⁻² e^{C (z_{t₂} - z_r)} g(r) dr`.
  Proof: the right-hand side `T` is a measurable supersolution (Tonelli), the defect
  `D = ψ - T` satisfies `D(s) ≤ C ∫_{(t₁, s]} a⁻² D`, and iterating gives
  `D(s) ≤ M (C (z_s - z_{t₁}))ⁿ / n! → 0`.
* `gronwall_movingZ`: the same statement with the free rate `μ₀` in the kernel, obtained by the
  normalisation `ψ = e^{-μ₀ z} φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal Nat

namespace UnforcedLeray.Short.IIIa

namespace WeakFlowGronwallSub

open FrameShortBlockSub

theorem clockA_pos' {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 < clockA ν r := by
  unfold clockA; positivity

theorem rpow_clockA_nonneg {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) : 0 ≤ (clockA ν r) ^ (-2 : ℝ) :=
  (Real.rpow_pos_of_pos (clockA_pos' hν hr) _).le

theorem continuousOn_clockA_rpow {ν u s : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) :
    ContinuousOn (fun r => (clockA ν r) ^ (-2 : ℝ)) (Icc u s) := by
  have hcA : ContinuousOn (clockA ν) (Icc u s) := by
    unfold clockA
    exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  exact hcA.rpow_const (fun r hr => Or.inl (clockA_pos' hν (hu.trans hr.1)).ne')

theorem continuousOn_movingZ' {ν u s : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) :
    ContinuousOn (movingZ ν) (Icc u s) := by
  have hcA : ContinuousOn (clockA ν) (Icc u s) := by
    unfold clockA
    exact continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  unfold movingZ
  exact continuousOn_id.div hcA (fun r hr => (clockA_pos' hν (hu.trans hr.1)).ne')

theorem measurable_movingZ' (ν : ℝ) : Measurable (movingZ ν) := by
  unfold movingZ clockA
  exact measurable_id.div (measurable_const.add (measurable_const.mul measurable_id))

theorem measurable_clockA_rpow (ν : ℝ) : Measurable (fun r => (clockA ν r) ^ (-2 : ℝ)) := by
  unfold clockA
  exact (measurable_const.add (measurable_const.mul measurable_id)).pow_const _

/-- Fundamental theorem of calculus as an `ℝ≥0∞` integral over `Ioc u s`. -/
theorem lintegral_Ioc_ofReal_eq_sub {u s : ℝ} (hus : u ≤ s) {F f : ℝ → ℝ}
    (hF : ∀ r ∈ Icc u s, HasDerivAt F (f r) r) (hf : ContinuousOn f (Icc u s))
    (hf0 : ∀ r ∈ Icc u s, 0 ≤ f r) :
    ∫⁻ r in Ioc u s, ENNReal.ofReal (f r) = ENNReal.ofReal (F s - F u) := by
  have hint : IntegrableOn f (Ioc u s) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc u s)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hf0 r (Ioc_subset_Icc_self hr)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hus,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hF r (by rwa [uIcc_of_le hus] at hr))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hus).2 hf.integrableOn_Icc)]

/-- `∫_{(u, s]} a⁻² C e^{C (z_r - z₀)} dr = e^{C (z_s - z₀)} - e^{C (z_u - z₀)}`. -/
theorem lintegral_exp_movingZ {ν u s C z₀ : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) (hus : u ≤ s)
    (hC : 0 ≤ C) :
    ∫⁻ r in Ioc u s,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * C * Real.exp (C * (movingZ ν r - z₀))) =
      ENNReal.ofReal (Real.exp (C * (movingZ ν s - z₀)) - Real.exp (C * (movingZ ν u - z₀))) := by
  refine lintegral_Ioc_ofReal_eq_sub hus
    (F := fun r => Real.exp (C * (movingZ ν r - z₀))) ?_ ?_ ?_
  · intro r hr
    have hz := hasDerivAt_movingZ hν (hu.trans hr.1)
    have h1 : HasDerivAt (fun r => C * (movingZ ν r - z₀))
        (C * ((clockA ν r) ^ (-2 : ℝ) - 0)) r :=
      (hz.sub (hasDerivAt_const r z₀)).const_mul C
    refine h1.exp.congr_deriv ?_
    ring
  · exact ((continuousOn_clockA_rpow hν hu).mul continuousOn_const).mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_movingZ' hν hu).sub continuousOn_const)))
  · intro r hr
    have h2 := rpow_clockA_nonneg hν (hu.trans hr.1)
    have h3 := Real.exp_nonneg (C * (movingZ ν r - z₀))
    positivity

/-- `∫_{(u, s]} a⁻² (z_r - z_u)ⁿ dr = (z_s - z_u)ⁿ⁺¹ / (n + 1)`. -/
theorem lintegral_pow_movingZ {ν u s : ℝ} (hν : 0 < ν) (hu : 0 ≤ u) (hus : u ≤ s) (n : ℕ) :
    ∫⁻ r in Ioc u s,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (movingZ ν r - movingZ ν u) ^ n) =
      ENNReal.ofReal ((movingZ ν s - movingZ ν u) ^ (n + 1) / ((n : ℝ) + 1)) := by
  have h := lintegral_Ioc_ofReal_eq_sub hus
    (F := fun r => (movingZ ν r - movingZ ν u) ^ (n + 1) / ((n : ℝ) + 1))
    (f := fun r => (clockA ν r) ^ (-2 : ℝ) * (movingZ ν r - movingZ ν u) ^ n) ?_ ?_ ?_
  · rw [h]
    congr 1
    simp
  · intro r hr
    have hz := hasDerivAt_movingZ hν (hu.trans hr.1)
    have h1 := ((hz.sub (hasDerivAt_const r (movingZ ν u))).pow (n + 1)).div_const ((n : ℝ) + 1)
    refine h1.congr_deriv ?_
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [Pi.sub_apply, Nat.add_sub_cancel, sub_zero]
    push_cast
    field_simp
  · exact (continuousOn_clockA_rpow hν hu).mul
      (((continuousOn_movingZ' hν hu).sub continuousOn_const).pow n)
  · intro r hr
    have h2 := rpow_clockA_nonneg hν (hu.trans hr.1)
    have h3 : 0 ≤ movingZ ν r - movingZ ν u :=
      sub_nonneg.2 (FrameStableSub.movingZ_le_movingZ hν hu hr.1)
    positivity

/-- **Normalised moving-time Gronwall lemma.** -/
theorem gronwall_normalized {ν t₁ t₂ C : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hC : 0 ≤ C) {ψ g : ℝ → ℝ≥0∞} {A M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hψM : ∀ r ∈ Icc t₁ t₂, ψ r ≤ M) (hg : Measurable g)
    (hH : ∀ s ∈ Icc t₁ t₂, ψ s ≤ A + ∫⁻ r in Ioc t₁ s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * ψ r + g r)) :
    ψ t₂ ≤ ENNReal.ofReal (Real.exp (C * (movingZ ν t₂ - movingZ ν t₁))) * A +
      ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
        Real.exp (C * (movingZ ν t₂ - movingZ ν r))) * g r := by
  have hzm : Measurable (movingZ ν) := measurable_movingZ' ν
  have hρm : Measurable fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_clockA_rpow ν)
  -- the density `h(x) = a(x)⁻² e^{-C z_x}` and its running integral against `g`
  set h : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((clockA ν x) ^ (-2 : ℝ) * Real.exp (-(C * movingZ ν x))) with hh_def
  have hhm : Measurable h := ENNReal.measurable_ofReal.comp
    ((measurable_clockA_rpow ν).mul (Real.measurable_exp.comp ((measurable_const.mul hzm).neg)))
  set I : ℝ → ℝ≥0∞ := fun r => ∫⁻ x in Ioc t₁ r, h x * g x with hI_def
  have hIm : Measurable I := by
    refine Monotone.measurable ?_
    intro r r' hrr'
    exact lintegral_mono_set (Ioc_subset_Ioc_right hrr')
  -- the candidate bound `T`
  set T : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (Real.exp (C * (movingZ ν r - movingZ ν t₁))) * A +
      ENNReal.ofReal (Real.exp (C * (movingZ ν r - 0))) * I r with hT_def
  have hTm : Measurable T := by
    refine Measurable.add ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (hzm.sub measurable_const)))).mul measurable_const
    · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (hzm.sub measurable_const)))).mul hIm
  -- `T` is a supersolution
  have hsup : ∀ s ∈ Icc t₁ t₂, A + ∫⁻ r in Ioc t₁ s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * T r + g r) ≤ T s := by
    intro s hs
    have hts : t₁ ≤ s := hs.1
    set k₀ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * C *
      Real.exp (C * (movingZ ν r - movingZ ν t₁))) with hk₀_def
    set k₁ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * C *
      Real.exp (C * (movingZ ν r - 0))) with hk₁_def
    have hk₀m : Measurable k₀ := ENNReal.measurable_ofReal.comp
      (((measurable_clockA_rpow ν).mul measurable_const).mul
        (Real.measurable_exp.comp (measurable_const.mul (hzm.sub measurable_const))))
    have hk₁m : Measurable k₁ := ENNReal.measurable_ofReal.comp
      (((measurable_clockA_rpow ν).mul measurable_const).mul
        (Real.measurable_exp.comp (measurable_const.mul (hzm.sub measurable_const))))
    -- pointwise decomposition of the integrand
    have hdec : ∀ r ∈ Ioc t₁ s,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * T r + g r) =
          k₀ r * A + (k₁ r * I r + ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * g r) := by
      intro r hr
      have ha2 := rpow_clockA_nonneg hν (ht₁.trans hr.1.le)
      simp only [hT_def, hk₀_def, hk₁_def]
      rw [ENNReal.ofReal_mul (mul_nonneg ha2 hC), ENNReal.ofReal_mul ha2,
        ENNReal.ofReal_mul (mul_nonneg ha2 hC), ENNReal.ofReal_mul ha2]
      ring
    -- the `k₀` term
    have hk₀int : ∫⁻ r in Ioc t₁ s, k₀ r =
        ENNReal.ofReal (Real.exp (C * (movingZ ν s - movingZ ν t₁)) - 1) := by
      simp only [hk₀_def]
      rw [lintegral_exp_movingZ hν ht₁ hts hC]
      simp
    -- Tonelli for the `k₁ I` term
    have hI_ind : ∀ r ∈ Ioc t₁ s,
        I r = ∫⁻ x in Ioc t₁ s, (Iic r).indicator (fun x => h x * g x) x := by
      intro r hr
      rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
      have hset : Iic r ∩ Ioc t₁ s = Ioc t₁ r := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨h1, h2, _⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, h1, h2.trans hr.2⟩
      rw [hset]
    have hunc : Measurable (Function.uncurry fun r x =>
        k₁ r * (Iic r).indicator (fun x => h x * g x) x) := by
      have heq : (Function.uncurry fun r x => k₁ r * (Iic r).indicator (fun x => h x * g x) x) =
          fun p : ℝ × ℝ => k₁ p.1 *
            ({q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q => h q.2 * g q.2) p) := by
        funext p
        simp only [Function.uncurry, Set.indicator_apply, mem_Iic, mem_setOf_eq]
      rw [heq]
      exact (hk₁m.comp measurable_fst).mul
        (((hhm.comp measurable_snd).mul (hg.comp measurable_snd)).indicator
          (measurableSet_le measurable_snd measurable_fst))
    have hTon : ∫⁻ r in Ioc t₁ s, k₁ r * I r =
        ∫⁻ x in Ioc t₁ s, h x * g x *
          ENNReal.ofReal (Real.exp (C * (movingZ ν s - 0)) - Real.exp (C * (movingZ ν x - 0))) := by
      calc ∫⁻ r in Ioc t₁ s, k₁ r * I r
          = ∫⁻ r in Ioc t₁ s, ∫⁻ x in Ioc t₁ s,
              k₁ r * (Iic r).indicator (fun x => h x * g x) x := by
            refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
            rw [hI_ind r hr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ x in Ioc t₁ s, ∫⁻ r in Ioc t₁ s,
              k₁ r * (Iic r).indicator (fun x => h x * g x) x :=
            lintegral_lintegral_swap hunc.aemeasurable
        _ = ∫⁻ x in Ioc t₁ s, h x * g x * ∫⁻ r in Ioc t₁ s, (Ici x).indicator k₁ r := by
            refine lintegral_congr (fun x => ?_)
            rw [← lintegral_const_mul _ (hk₁m.indicator measurableSet_Ici)]
            refine lintegral_congr (fun r => ?_)
            by_cases hxr : x ≤ r
            · simp only [Set.indicator_apply, mem_Iic, mem_Ici, hxr, ↓reduceIte]
              ring
            · simp only [Set.indicator_apply, mem_Iic, mem_Ici, hxr, ↓reduceIte, mul_zero]
        _ = ∫⁻ x in Ioc t₁ s, h x * g x *
              ENNReal.ofReal (Real.exp (C * (movingZ ν s - 0)) -
                Real.exp (C * (movingZ ν x - 0))) := by
            refine setLIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
            congr 1
            rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
            have hset : Ici x ∩ Ioc t₁ s = Icc x s := by
              ext r
              simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
              constructor
              · rintro ⟨h1, _, h3⟩
                exact ⟨h1, h3⟩
              · rintro ⟨h1, h2⟩
                exact ⟨h1, hx.1.trans_le h1, h2⟩
            rw [hset, ← setLIntegral_congr Ioc_ae_eq_Icc]
            exact lintegral_exp_movingZ hν (ht₁.trans hx.1.le) hx.2 hC
    -- recombination of the `k₁ I` and `g` terms
    have hXm : Measurable fun x => h x * g x *
        ENNReal.ofReal (Real.exp (C * (movingZ ν s - 0)) - Real.exp (C * (movingZ ν x - 0))) :=
      (hhm.mul hg).mul (ENNReal.measurable_ofReal.comp (measurable_const.sub
        (Real.measurable_exp.comp (measurable_const.mul (hzm.sub measurable_const)))))
    have hrec : (∫⁻ r in Ioc t₁ s, k₁ r * I r) +
        ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * g r =
          ENNReal.ofReal (Real.exp (C * (movingZ ν s - 0))) * I s := by
      rw [hTon, ← lintegral_add_left hXm]
      simp only [hI_def]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      have ha2 := rpow_clockA_nonneg hν (ht₁.trans hx.1.le)
      have hzx : movingZ ν x ≤ movingZ ν s :=
        FrameStableSub.movingZ_le_movingZ hν (ht₁.trans hx.1.le) hx.2
      have hE : 0 ≤ Real.exp (C * (movingZ ν s - 0)) - Real.exp (C * (movingZ ν x - 0)) := by
        rw [sub_nonneg, Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_left (by linarith) hC
      have he : Real.exp (-(C * movingZ ν x)) * Real.exp (C * (movingZ ν x - 0)) = 1 := by
        rw [← Real.exp_add]
        simp
      simp only [hh_def]
      rw [show ∀ p q r : ℝ≥0∞, p * r * q + ENNReal.ofReal ((clockA ν x) ^ (-2 : ℝ)) * r =
          (p * q + ENNReal.ofReal ((clockA ν x) ^ (-2 : ℝ))) * r from fun p q r => by ring,
        show ∀ p q r : ℝ≥0∞, p * (q * r) = (p * q) * r from fun p q r => by ring]
      congr 1
      rw [← ENNReal.ofReal_mul (mul_nonneg ha2 (Real.exp_nonneg _)),
        ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg ha2 (Real.exp_nonneg _)) hE) ha2,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      congr 1
      linear_combination (-((clockA ν x) ^ (-2 : ℝ))) * he
    -- assemble the supersolution inequality
    have hone : 1 + ENNReal.ofReal (Real.exp (C * (movingZ ν s - movingZ ν t₁)) - 1) =
        ENNReal.ofReal (Real.exp (C * (movingZ ν s - movingZ ν t₁))) := by
      have hge : 1 ≤ Real.exp (C * (movingZ ν s - movingZ ν t₁)) :=
        Real.one_le_exp (mul_nonneg hC
          (sub_nonneg.2 (FrameStableSub.movingZ_le_movingZ hν ht₁ hts)))
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
      congr 1
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioc hdec,
      lintegral_add_left (hk₀m.mul_const A), lintegral_mul_const A hk₀m,
      lintegral_add_left (f := fun a => k₁ a * I a) (hk₁m.mul hIm), hrec, hk₀int]
    refine le_of_eq ?_
    simp only [hT_def]
    rw [← hone]
    ring
  -- the defect `D = ψ - T`
  set D : ℝ → ℝ≥0∞ := fun r => ψ r - T r with hD_def
  have hDle : ∀ s ∈ Icc t₁ t₂, D s ≤ ∫⁻ r in Ioc t₁ s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r) := by
    intro s hs
    have h1 : ∫⁻ r in Ioc t₁ s,
          ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * ψ r + g r) ≤
        (∫⁻ r in Ioc t₁ s,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * T r + g r)) +
          ∫⁻ r in Ioc t₁ s,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r) := by
      rw [← lintegral_add_left (f := fun r => ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
        (ENNReal.ofReal C * T r + g r)) (hρm.mul ((measurable_const.mul hTm).add hg))]
      refine lintegral_mono (fun r => ?_)
      have hψ : ψ r ≤ T r + D r := le_add_tsub
      calc ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * ψ r + g r)
          ≤ ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
              (ENNReal.ofReal C * (T r + D r) + g r) := by gcongr
        _ = ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * T r + g r) +
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r) := by ring
    have h3 : ψ s ≤ T s + ∫⁻ r in Ioc t₁ s,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r) :=
      calc ψ s ≤ A + ∫⁻ r in Ioc t₁ s,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * ψ r + g r) := hH s hs
        _ ≤ A + ((∫⁻ r in Ioc t₁ s,
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * T r + g r)) +
            ∫⁻ r in Ioc t₁ s,
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r)) := by
            gcongr
        _ = (A + ∫⁻ r in Ioc t₁ s,
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * T r + g r)) +
            ∫⁻ r in Ioc t₁ s,
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r) := by ring
        _ ≤ T s + ∫⁻ r in Ioc t₁ s,
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r) := by
            gcongr
            exact hsup s hs
    exact tsub_le_iff_left.2 h3
  -- iteration
  have hiter : ∀ n : ℕ, ∀ s ∈ Icc t₁ t₂,
      D s ≤ M * ENNReal.ofReal ((C * (movingZ ν s - movingZ ν t₁)) ^ n / (n ! : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
        mul_one]
      exact tsub_le_self.trans (hψM s hs)
    | succ n ih =>
      intro s hs
      refine (hDle s hs).trans ?_
      calc ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * D r)
          ≤ ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C *
              (M * ENNReal.ofReal ((C * (movingZ ν r - movingZ ν t₁)) ^ n / (n ! : ℝ)))) := by
            refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
            have hr' : r ∈ Icc t₁ t₂ := ⟨hr.1.le, hr.2.trans hs.2⟩
            gcongr
            exact ih r hr'
        _ = ∫⁻ r in Ioc t₁ s, (M * ENNReal.ofReal (C ^ (n + 1) / (n ! : ℝ))) *
              ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (movingZ ν r - movingZ ν t₁) ^ n) := by
            refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
            have ha2 := rpow_clockA_nonneg hν (ht₁.trans hr.1.le)
            have hΔ : 0 ≤ movingZ ν r - movingZ ν t₁ :=
              sub_nonneg.2 (FrameStableSub.movingZ_le_movingZ hν ht₁ hr.1.le)
            have hX : 0 ≤ (C * (movingZ ν r - movingZ ν t₁)) ^ n / (n ! : ℝ) := by positivity
            have hY : 0 ≤ C ^ (n + 1) / (n ! : ℝ) := by positivity
            rw [show ∀ p q x : ℝ≥0∞, p * (q * (M * x)) = M * (p * q * x) from
                fun p q x => by ring,
              ← ENNReal.ofReal_mul ha2, ← ENNReal.ofReal_mul (mul_nonneg ha2 hC), mul_assoc M,
              ← ENNReal.ofReal_mul hY]
            congr 2
            rw [mul_pow, pow_succ]
            ring
        _ = (M * ENNReal.ofReal (C ^ (n + 1) / (n ! : ℝ))) *
              ENNReal.ofReal ((movingZ ν s - movingZ ν t₁) ^ (n + 1) / ((n : ℝ) + 1)) := by
            rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top),
              lintegral_pow_movingZ hν ht₁ hs.1 n]
        _ = M * ENNReal.ofReal
              ((C * (movingZ ν s - movingZ ν t₁)) ^ (n + 1) / ((n + 1) ! : ℝ)) := by
            have hY : 0 ≤ C ^ (n + 1) / (n ! : ℝ) := by positivity
            rw [mul_assoc, ← ENNReal.ofReal_mul hY]
            congr 2
            rw [Nat.factorial_succ, mul_pow]
            push_cast
            have hn : (n ! : ℝ) ≠ 0 := by positivity
            have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
            field_simp
  -- passage to the limit
  have hlim : Tendsto (fun n : ℕ => M * ENNReal.ofReal
      ((C * (movingZ ν t₂ - movingZ ν t₁)) ^ n / (n ! : ℝ))) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_ofReal
      (FloorSemiring.tendsto_pow_div_factorial_atTop (C * (movingZ ν t₂ - movingZ ν t₁)))
    rw [ENNReal.ofReal_zero] at h0
    have h1 := ENNReal.Tendsto.const_mul h0 (Or.inr hM)
    rwa [mul_zero] at h1
  have hD0 : D t₂ ≤ 0 :=
    ge_of_tendsto' hlim (fun n => hiter n t₂ ⟨h12, le_rfl⟩)
  have hψT : ψ t₂ ≤ T t₂ := tsub_eq_zero_iff_le.1 (le_antisymm hD0 bot_le)
  refine hψT.trans (le_of_eq ?_)
  simp only [hT_def, hI_def]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
  have ha2 := rpow_clockA_nonneg hν (ht₁.trans hr.1.le)
  simp only [hh_def]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 2
  rw [show C * (movingZ ν t₂ - movingZ ν r) = C * (movingZ ν t₂ - 0) + -(C * movingZ ν r) by ring,
    Real.exp_add]
  ring

/-- **Moving-time Gronwall lemma with free rate `μ₀`.** -/
theorem gronwall_movingZ {ν t₁ t₂ μ₀ C : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hμ₀ : 0 ≤ μ₀) (hC : 0 ≤ C) {Q G : ℝ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hQM : ∀ r ∈ Icc t₁ t₂, Q r ≤ M) (hG : Measurable G)
    (hH : ∀ s ∈ Icc t₁ t₂, Q s ≤
      ENNReal.ofReal (Real.exp (μ₀ * (movingZ ν s - movingZ ν t₁))) * Q t₁ +
        ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
          Real.exp (μ₀ * (movingZ ν s - movingZ ν r))) * (ENNReal.ofReal C * Q r + G r)) :
    Q t₂ ≤ ENNReal.ofReal (Real.exp ((μ₀ + C) * (movingZ ν t₂ - movingZ ν t₁))) * Q t₁ +
      ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
        Real.exp ((μ₀ + C) * (movingZ ν t₂ - movingZ ν r))) * G r := by
  have hzm : Measurable (movingZ ν) := measurable_movingZ' ν
  set e : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(μ₀ * movingZ ν r))) with he_def
  have hem : Measurable e :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_const.mul hzm).neg))
  set ψ : ℝ → ℝ≥0∞ := fun r => e r * Q r with hψ_def
  set g : ℝ → ℝ≥0∞ := fun r => e r * G r with hg_def
  have hgm : Measurable g := hem.mul hG
  have he_le : ∀ r, 0 ≤ r → e r ≤ 1 := by
    intro r hr
    simp only [he_def]
    rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff, neg_nonpos]
    have hz : 0 ≤ movingZ ν r := by
      have := FrameStableSub.movingZ_le_movingZ hν le_rfl hr
      simpa [movingZ] using this
    exact mul_nonneg hμ₀ hz
  have hψM : ∀ r ∈ Icc t₁ t₂, ψ r ≤ M := by
    intro r hr
    calc ψ r = e r * Q r := rfl
      _ ≤ 1 * M := mul_le_mul' (he_le r (ht₁.trans hr.1)) (hQM r hr)
      _ = M := one_mul M
  have hH' : ∀ s ∈ Icc t₁ t₂, ψ s ≤ ψ t₁ + ∫⁻ r in Ioc t₁ s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * ψ r + g r) := by
    intro s hs
    calc ψ s = e s * Q s := rfl
      _ ≤ e s * (ENNReal.ofReal (Real.exp (μ₀ * (movingZ ν s - movingZ ν t₁))) * Q t₁ +
            ∫⁻ r in Ioc t₁ s, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
              Real.exp (μ₀ * (movingZ ν s - movingZ ν r))) * (ENNReal.ofReal C * Q r + G r)) :=
          by gcongr; exact hH s hs
      _ = ψ t₁ + ∫⁻ r in Ioc t₁ s,
            ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C * ψ r + g r) := by
          rw [mul_add, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          · simp only [hψ_def, he_def]
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            congr 3
            ring
          · refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
            have ha2 := rpow_clockA_nonneg hν (ht₁.trans hr.1.le)
            simp only [hψ_def, hg_def, he_def]
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
              show ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal C *
                  (ENNReal.ofReal (Real.exp (-(μ₀ * movingZ ν r))) * Q r) +
                  ENNReal.ofReal (Real.exp (-(μ₀ * movingZ ν r))) * G r) =
                (ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) *
                  ENNReal.ofReal (Real.exp (-(μ₀ * movingZ ν r)))) *
                    (ENNReal.ofReal C * Q r + G r) from by ring,
              ← ENNReal.ofReal_mul ha2]
            congr 2
            rw [show -(μ₀ * movingZ ν r) =
                -(μ₀ * movingZ ν s) + μ₀ * (movingZ ν s - movingZ ν r) by ring, Real.exp_add]
            ring
  have hmain := gronwall_normalized hν ht₁ h12 hC hM hψM hgm hH'
  -- undo the normalisation
  have hQψ : Q t₂ = ENNReal.ofReal (Real.exp (μ₀ * movingZ ν t₂)) * ψ t₂ := by
    simp only [hψ_def, he_def]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  rw [hQψ]
  calc ENNReal.ofReal (Real.exp (μ₀ * movingZ ν t₂)) * ψ t₂
      ≤ ENNReal.ofReal (Real.exp (μ₀ * movingZ ν t₂)) *
          (ENNReal.ofReal (Real.exp (C * (movingZ ν t₂ - movingZ ν t₁))) * ψ t₁ +
            ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
              Real.exp (C * (movingZ ν t₂ - movingZ ν r))) * g r) :=
        by gcongr
    _ = ENNReal.ofReal (Real.exp ((μ₀ + C) * (movingZ ν t₂ - movingZ ν t₁))) * Q t₁ +
          ∫⁻ r in Ioc t₁ t₂, ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) *
            Real.exp ((μ₀ + C) * (movingZ ν t₂ - movingZ ν r))) * G r := by
        rw [mul_add, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        · simp only [hψ_def, he_def]
          rw [show ∀ p q x y : ℝ≥0∞, p * (q * (x * y)) = (p * q * x) * y from
              fun p q x y => by ring,
            ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (by positivity),
            ← Real.exp_add, ← Real.exp_add]
          congr 3
          ring
        · refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
          have ha2 := rpow_clockA_nonneg hν (ht₁.trans hr.1.le)
          simp only [hg_def, he_def]
          rw [show ∀ p q x y : ℝ≥0∞, p * (q * (x * y)) = (p * q * x) * y from
              fun p q x y => by ring,
            ← ENNReal.ofReal_mul (Real.exp_nonneg _),
            ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _)
              (mul_nonneg ha2 (Real.exp_nonneg _)))]
          congr 2
          rw [show (μ₀ + C) * (movingZ ν t₂ - movingZ ν r) =
              μ₀ * movingZ ν t₂ + C * (movingZ ν t₂ - movingZ ν r) + -(μ₀ * movingZ ν r) by ring,
            Real.exp_add, Real.exp_add]
          ring

end WeakFlowGronwallSub

end UnforcedLeray.Short.IIIa
