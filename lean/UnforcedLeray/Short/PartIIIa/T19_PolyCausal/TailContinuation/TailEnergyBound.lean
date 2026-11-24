import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.AdvectionEnergy

/-!
# Part III-a, task `PartIII-a:T19/3/2`: tail energy bound from the advection energy identity

Source of record: `the November 2 reference manuscript` (SP), lines 3525-3537
(Step P5 of `prop:short-polynomial-causal`).

Proves `trainTailEnergyFromAdvection : UnforcedLeray.Short.IIIa.TrainTailEnergyFromAdvection`:
assuming `TrainAdvectionEnergyIdentity`, deduces `TrainTailEnergyBound` by testing with
`ψ_n(s) = exp(-2 ∫_{H-1}^s L_n(τ) dτ) * tailRamp H B s` where `L_n = SmoothToC1Aux.sm L_0 n`
mollifies the truncated strain rate `L_0 = (Icc (H - 1) (2B + H)).indicator L_str` and
`tailRamp H B s = rampPsi (1 / 2) B (s - (H - 3 / 2))` ramps up on `[H - 1, H - 1 / 2]`, equals `1`
on `[H - 1 / 2, B]`, and ramps down on `[B + H - 3 / 2, 2B + H - 3 / 2]`, absorbing the forcing inner
product via Young's inequality (`θ = ν`), passing to `n → ∞` by dominated convergence / Fatou, and
then letting `B → ∞` via Fatou.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

namespace TailEnergyBoundAux

open UnforcedLeray.Short.IIIa.SmoothToC1Aux
open UnforcedLeray.Short.IIIa.AdvectionEnergyAux

/-! ## 1. Mollification of bounded locally integrable functions via `SmoothToC1Aux.sm` -/

theorem sm_contDiff_of_locallyIntegrable {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) (n : ℕ) :
    ContDiff ℝ ∞ (sm g n) :=
  (mol_hasCompactSupport n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (mol_contDiff n) hg

theorem sm_ae_tendsto_of_locallyIntegrable {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ x ∂volume, Tendsto (fun n => sm g n x) atTop (𝓝 (g x)) := by
  refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2)
    tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => ?_) hg
  show 1 / ((n : ℝ) + 1) ≤ 2 * (1 / (2 * ((n : ℝ) + 1)))
  field_simp
  linarith

theorem sm_le_of_le {g : ℝ → ℝ} {M : ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x)
    (hM : ∀ x, g x ≤ M) (n : ℕ) (x : ℝ) :
    sm g n x ≤ M := by
  have hmol_int : Integrable (mol n) volume :=
    (mol_contDiff n).continuous.integrable_of_hasCompactSupport (mol_hasCompactSupport n)
  have hsub_meas : Measurable (fun t : ℝ => g (x - t)) :=
    hg.comp (measurable_const.sub measurable_id)
  have hprod_int : Integrable (fun t => mol n t * g (x - t)) volume := by
    refine (hmol_int.mul_const M).mono'
      (((mol_contDiff n).continuous.measurable.mul hsub_meas).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mol_nonneg n t) (h0 _))]
    exact mul_le_mul_of_nonneg_left (hM _) (mol_nonneg n t)
  rw [sm_apply]
  calc ∫ t, mol n t * g (x - t)
      ≤ ∫ t, mol n t * M :=
        integral_mono hprod_int (hmol_int.mul_const M) fun t =>
          mul_le_mul_of_nonneg_left (hM _) (mol_nonneg n t)
    _ = (∫ t, mol n t) * M := integral_mul_const M (mol n)
    _ = 1 * M := by rw [mol, (bumpR n).integral_normed]
    _ = M := one_mul M

/-! ## 2. Shifted ramp cutoff `tailRamp H B` -/

/-- Shifted ramp cutoff `rampPsi (1 / 2) B (s - (H - 3 / 2))`:
supported in `[H - 1, 2B + H - 3 / 2]`, ramps up on `[H - 1, H - 1 / 2]`, and equals `1` on
`[H - 1 / 2, B + H - 3 / 2] ⊇ [H - 1 / 2, B]` (when `H > 2`). -/
def tailRamp (H B s : ℝ) : ℝ :=
  rampPsi (1 / 2) B (s - (H - 3 / 2))

theorem rampPsi_contDiff (δ B : ℝ) : ContDiff ℝ 1 (rampPsi δ B) := by
  unfold rampPsi
  exact (smooth_sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (smooth_sigma_contDiff.comp (((contDiff_const (c := 2 * B)).sub contDiff_id).div_const B))

theorem rampPsi_deriv_le {K δ B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hδ : 0 < δ) (hB2 : 2 * δ < B) (s : ℝ) :
    deriv (rampPsi δ B) s ≤
      (2 * K + 1) / δ * (Icc δ (2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
  have hB : 0 < B := by linarith
  by_cases hs : s ∈ Icc δ (2 * δ)
  · simp only [indicator_of_mem hs, mul_one]
    rw [rampPsi_hasDerivAt δ B s hδ hB]
    have ha := abs_le.1 (hK ((s - δ) / δ))
    have hb := abs_le.1 (hK ((2 * B - s) / B))
    have hf0' : Real.smoothTransition ((s - δ) / δ) ≤ 1 := Real.smoothTransition.le_one _
    have hg1 : 0 ≤ Real.smoothTransition ((2 * B - s) / B) := Real.smoothTransition.nonneg _
    have hg1' : Real.smoothTransition ((2 * B - s) / B) ≤ 1 := Real.smoothTransition.le_one _
    have hf0n : 0 ≤ Real.smoothTransition ((s - δ) / δ) := Real.smoothTransition.nonneg _
    have hp : 0 ≤ 1 / δ := by positivity
    have hq : 0 ≤ 1 / B := by positivity
    have hqp : 1 / B ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith [hs.1, hs.2])
    have ht : (0 - 1) / B = -(1 / B) := by ring
    rw [ht]
    have hgoal : (2 * K + 1) / δ = (2 * K + 1) * (1 / δ) := by ring
    rw [hgoal]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha.2) hp) hg1,
      mul_nonneg (mul_nonneg hK0 hp) (sub_nonneg.2 hg1'),
      mul_nonneg (mul_nonneg hf0n hq)
        (by linarith [hb.1] : (0 : ℝ) ≤ K + deriv Real.smoothTransition ((2 * B - s) / B)),
      mul_nonneg (mul_nonneg hK0 hq) (sub_nonneg.2 hf0'),
      mul_nonneg hK0 (sub_nonneg.2 hqp), hp]
  · rw [indicator_of_notMem hs, mul_zero]
    have hsc : s < δ ∨ 2 * δ < s := by
      by_contra hc
      exact hs ⟨not_lt.1 (fun h => hc (Or.inl h)), not_lt.1 (fun h => hc (Or.inr h))⟩
    rcases hsc with h | h
    · have hev : rampPsi δ B =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact rampPsi_eq_zero_of_lt hδ hy
      rw [hev.deriv_eq]
      simp
    · have hev : rampPsi δ B =ᶠ[𝓝 s] fun y => Real.smoothTransition ((2 * B - y) / B) := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 * δ < y := hy
        have h1 : 1 ≤ (y - δ) / δ := by
          rw [le_div_iff₀ hδ]
          linarith
        unfold rampPsi
        rw [Real.smoothTransition.one_of_one_le h1, one_mul]
      rw [hev.deriv_eq]
      have hin2 : HasDerivAt (fun y : ℝ => (2 * B - y) / B) ((0 - 1) / B) s :=
        ((hasDerivAt_const s (2 * B)).sub (hasDerivAt_id' s)).div_const B
      have hd : HasDerivAt (fun y => Real.smoothTransition ((2 * B - y) / B))
          (deriv Real.smoothTransition ((2 * B - s) / B) * ((0 - 1) / B)) s :=
        sigma_comp_hasDerivAt hin2
      rw [hd.deriv]
      have h1 := sigma_deriv_nonneg ((2 * B - s) / B)
      have h2 : (0 - 1) / B ≤ 0 := by
        rw [div_le_iff₀ hB]
        linarith
      nlinarith

theorem tailRamp_contDiff (H B : ℝ) : ContDiff ℝ 1 (tailRamp H B) := by
  unfold tailRamp
  exact (rampPsi_contDiff (1 / 2) B).comp (contDiff_id.sub contDiff_const)

theorem tailRamp_nonneg (H B s : ℝ) : 0 ≤ tailRamp H B s :=
  rampPsi_nonneg (1 / 2) B (s - (H - 3 / 2))

theorem tailRamp_le_one (H B s : ℝ) : tailRamp H B s ≤ 1 :=
  rampPsi_le_one (1 / 2) B (s - (H - 3 / 2))

theorem tailRamp_eq_zero_of_not_mem {H B s : ℝ} (hB : 0 < B)
    (hs : s ∉ Icc (H - 1) (2 * B + H - 3 / 2)) : tailRamp H B s = 0 := by
  unfold tailRamp
  apply rampPsi_eq_zero_of_not_mem (by norm_num : (0 : ℝ) < 1 / 2) hB
  intro hmem
  exact hs ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem tailRamp_tsupport_subset {H B : ℝ} (hB : 0 < B) :
    tsupport (tailRamp H B) ⊆ Icc (H - 1) (2 * B + H - 3 / 2) := by
  refine closure_minimal (fun s hs => ?_) isClosed_Icc
  by_contra hs'
  exact hs (tailRamp_eq_zero_of_not_mem hB hs')

theorem tailRamp_one {H B s : ℝ} (hH : 2 < H) (hB : 0 < B) (hs : s ∈ Icc (H - 1 / 2) B) :
    tailRamp H B s = 1 := by
  unfold tailRamp
  apply rampPsi_one (by norm_num : (0 : ℝ) < 1 / 2) hB
  exact ⟨by linarith [hs.1], by linarith [hs.2, hH]⟩

theorem tailRamp_deriv_le {K H B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hB1 : 1 < B) (s : ℝ) :
    deriv (tailRamp H B) s ≤
      2 * (2 * K + 1) * (Icc (H - 1) (H - 1 / 2)).indicator (fun _ => (1 : ℝ)) s := by
  have h1 : HasDerivAt (rampPsi (1 / 2) B)
      (deriv (rampPsi (1 / 2) B) (s - (H - 3 / 2))) (s - (H - 3 / 2)) :=
    ((rampPsi_contDiff (1 / 2) B).differentiable one_ne_zero _).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => t - (H - 3 / 2)) 1 s :=
    (hasDerivAt_id' s).sub_const (H - 3 / 2)
  have hd : deriv (tailRamp H B) s = deriv (rampPsi (1 / 2) B) (s - (H - 3 / 2)) := by
    have hcomp : HasDerivAt (tailRamp H B) (deriv (rampPsi (1 / 2) B) (s - (H - 3 / 2)) * 1) s :=
      h1.comp s h2
    rw [hcomp.deriv, mul_one]
  rw [hd]
  have hle := rampPsi_deriv_le hK0 hK (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith : 2 * (1 / 2 : ℝ) < B) (s - (H - 3 / 2))
  have hind : (Icc (1 / 2 : ℝ) (2 * (1 / 2))).indicator (fun _ => (1 : ℝ)) (s - (H - 3 / 2)) =
      (Icc (H - 1) (H - 1 / 2)).indicator (fun _ => (1 : ℝ)) s := by
    by_cases hs : s ∈ Icc (H - 1) (H - 1 / 2)
    · have hs' : s - (H - 3 / 2) ∈ Icc (1 / 2 : ℝ) (2 * (1 / 2)) :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [indicator_of_mem hs, indicator_of_mem hs']
    · have hs' : s - (H - 3 / 2) ∉ Icc (1 / 2 : ℝ) (2 * (1 / 2)) := fun h =>
        hs ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [indicator_of_notMem hs, indicator_of_notMem hs']
  rw [hind] at hle
  linarith

/-! ## 3. Young absorption with general advection-derivative term -/

theorem advection_cutoff_young {k ν α : ℝ} {A N M Q ψ D : ℝ → ℝ} {a b : ℝ}
    (_hν : 0 < ν) (hα : 2 * k ≤ α)
    (hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M s ∧ 0 ≤ Q s)
    (hA : IntegrableOn A (Icc a b)) (hN : IntegrableOn N (Icc a b))
    (hQ : IntegrableOn Q (Icc a b))
    (hY : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 2 * M s ≤ ν * N s + ν⁻¹ * Q s)
    (hψ : ContDiff ℝ 1 ψ) (ha : 0 < a) (hsupp : tsupport ψ ⊆ Icc a b) (hψ0 : ∀ s, 0 ≤ ψ s)
    (hW : (∫ s in Ioi (0 : ℝ), ψ s * (α * s ^ (-3 / 2 : ℝ) * A s + 2 * ν * s ^ (-1 / 2 : ℝ) * N s))
        ≤ (∫ s in Ioi (0 : ℝ), D s * (s ^ (-1 / 2 : ℝ) * A s)) +
          2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * M s) :
    Integrable (fun s => ψ s * cutG k ν ν A N s) (volume.restrict (Ioi (0 : ℝ))) ∧
    ∫ s in Ioi (0 : ℝ), ψ s * cutG k ν ν A N s ≤
      (∫ s in Ioi (0 : ℝ), D s * (s ^ (-1 / 2 : ℝ) * A s)) +
        ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s) := by
  have iA : Integrable (fun s => ψ s * (s ^ (-3 / 2 : ℝ) * A s)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_cutoff_mul hψ ha hsupp (intOn_rpow_mul ha hA _)
  have iN : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * N s)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_cutoff_mul hψ ha hsupp (intOn_rpow_mul ha hN _)
  have iQ : Integrable (fun s => ψ s * (s ^ (-1 / 2 : ℝ) * Q s)) (volume.restrict (Ioi (0 : ℝ))) :=
    integrable_cutoff_mul hψ ha hsupp (intOn_rpow_mul ha hQ _)
  have hP1 : 0 ≤ ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-3 / 2 : ℝ) * A s) := by
    refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
    exact mul_nonneg (hψ0 s) (mul_nonneg (Real.rpow_nonneg (le_of_lt hs) _) (hnn s).1)
  have hM : 2 * ∫ s in Ioi (0 : ℝ), ψ s * s ^ (-1 / 2 : ℝ) * M s ≤
      ν * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * N s)) +
        ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * Q s) := by
    have hle : ∫ s in Ioi (0 : ℝ), 2 * (ψ s * s ^ (-1 / 2 : ℝ) * M s) ≤
        ∫ s in Ioi (0 : ℝ), (ν * (ψ s * (s ^ (-1 / 2 : ℝ) * N s)) +
          ν⁻¹ * (ψ s * (s ^ (-1 / 2 : ℝ) * Q s))) := by
      refine integral_mono_of_nonneg ?_ ((iN.const_mul ν).add (iQ.const_mul ν⁻¹)) ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have := mul_nonneg (hψ0 s) (Real.rpow_nonneg (le_of_lt hs) (-1 / 2 : ℝ))
        have := mul_nonneg this (hnn s).2.2.1
        simp only [Pi.zero_apply]
        linarith
      · filter_upwards [hY, ae_restrict_mem measurableSet_Ioi] with s hs1 hs
        have hr := mul_nonneg (hψ0 s) (Real.rpow_nonneg (le_of_lt hs) (-1 / 2 : ℝ))
        have := mul_le_mul_of_nonneg_left hs1 hr
        nlinarith [this]
    rw [integral_add (iN.const_mul ν) (iQ.const_mul ν⁻¹)] at hle
    simp only [integral_const_mul] at hle
    exact hle
  have e1 : (∫ s in Ioi (0 : ℝ), ψ s * (α * s ^ (-3 / 2 : ℝ) * A s + 2 * ν * s ^ (-1 / 2 : ℝ) * N s))
      = α * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-3 / 2 : ℝ) * A s)) +
        2 * ν * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * N s) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul α) (iN.const_mul _)]
    congr 1; funext s; ring
  have e2 : (∫ s in Ioi (0 : ℝ), ψ s * cutG k ν ν A N s)
      = 2 * k * (∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-3 / 2 : ℝ) * A s)) +
        (2 * ν - ν) * ∫ s in Ioi (0 : ℝ), ψ s * (s ^ (-1 / 2 : ℝ) * N s) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iA.const_mul (2 * k)) (iN.const_mul (2 * ν - ν))]
    congr 1; funext s; unfold cutG; ring
  refine ⟨?_, ?_⟩
  · have := (iA.const_mul (2 * k)).add (iN.const_mul (2 * ν - ν))
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only [Pi.add_apply, cutG]; ring
  · rw [e2]
    have h3 := mul_nonneg (sub_nonneg.2 hα) hP1
    rw [e1] at hW
    linarith [hW, hM, h3]

/-! ## 4. Tail norms as slice integrals -/

theorem hCalNormTail_sq_eq {c t_star : ℝ} (hc : 0 < c) (ht : 0 < t_star)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i)
    (hfin : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (u p) ^ 2) < ⊤) :
    hCalNormTail c t_star u ^ 2 =
      ENNReal.ofReal c⁻¹ *
        ∫⁻ s in Ici t_star, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * sliceSq c (fun p => vnorm2 (u p) ^ 2) s) := by
  unfold hCalNormTail
  rw [eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => vnorm2 (u p)) (fun _ => Real.sqrt_nonneg _)]
  exact ageSlice_aux (fun p => vnorm2 (u p) ^ 2) hc (measurable_vnorm2_sq hu)
    (fun _ => sq_nonneg _) hfin (Ici t_star) measurableSet_Ici (fun s hs => lt_of_lt_of_le ht hs)

theorem tCalNormTail_sq_eq {c t_star : ℝ} (hc : 0 < c) (ht : 0 < t_star)
    {T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} (hT : ∀ i j, Measurable fun p => T p i j)
    (hfin : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (tnorm2 (T p) ^ 2) < ⊤) :
    tCalNormTail c t_star T ^ 2 =
      ENNReal.ofReal c⁻¹ *
        ∫⁻ s in Ici t_star, ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * sliceSq c (fun p => tnorm2 (T p) ^ 2) s) := by
  unfold tCalNormTail
  rw [eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => tnorm2 (T p)) (fun _ => Real.sqrt_nonneg _)]
  exact ageSlice_aux (fun p => tnorm2 (T p) ^ 2) hc ((measurable_tnorm2 hT).pow_const 2)
    (fun _ => sq_nonneg _) hfin (Ici t_star) measurableSet_Ici (fun s hs => lt_of_lt_of_le ht hs)

theorem hCalNormOn_sq_eq {c H : ℝ} (hc : 0 < c)
    {u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} (hu : ∀ i, Measurable fun p => u p i)
    (hfin : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (u p) ^ 2) < ⊤) :
    hCalNormOn c H u ^ 2 =
      ENNReal.ofReal c⁻¹ *
        ∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * sliceSq c (fun p => vnorm2 (u p) ^ 2) s) := by
  unfold hCalNormOn
  rw [eLpNorm_two_sq_eq_lintegral_nonneg _ (fun p => vnorm2 (u p)) (fun _ => Real.sqrt_nonneg _)]
  have hres : ((ageμ c (-3 / 2)).restrict (Iio H ×ˢ (univ : Set (ℝ × ℝ)))) =
      (ageμ c (-3 / 2)).restrict (Ioo 0 H ×ˢ (univ : Set (ℝ × ℝ))) := by
    refine Measure.restrict_congr_set ?_
    filter_upwards [ae_ageμ_mem hc (-3 / 2)] with p hp
    exact propext ⟨fun (h : p ∈ Iio H ×ˢ univ) => ⟨⟨hp.1, h.1⟩, trivial⟩,
      fun (h : p ∈ Ioo 0 H ×ˢ univ) => ⟨h.1.2, trivial⟩⟩
  rw [hres]
  exact (ageSlice c (-3 / 2) (fun p => vnorm2 (u p) ^ 2) hc
    (measurable_vnorm2_sq hu) (fun _ => sq_nonneg _) hfin).2 H

end TailEnergyBoundAux

open TailEnergyBoundAux
open UnforcedLeray.Short.IIIa.SmoothToC1Aux
open UnforcedLeray.Short.IIIa.AdvectionEnergyAux

/-! ## Main theorem: `trainTailEnergyFromAdvection` (`PartIII-a:T19/3/2`) -/

theorem trainTailEnergyFromAdvection : UnforcedLeray.Short.IIIa.TrainTailEnergyFromAdvection := by
  intro hAdv P hP K hK
  obtain ⟨Kσ, hKσ0, hKσ⟩ := sigma_deriv_bound
  set C_ramp : ℝ := 2 * Kσ + 1
  have hC_ramp : 0 < C_ramp := by unfold C_ramp; linarith
  set C_trace : ℝ := max (2 * C_ramp) 1
  have hC_trace_nn : 0 ≤ C_trace := le_trans zero_le_one (le_max_right _ _)
  refine ⟨C_trace, hC_trace_nn, fun ν H I_H hν0 hH2 hIH0 tr htr hStrain μ hμ F _hFsym hFm hFfin b_sol G_sol hsol => ?_⟩
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν0 _
  let γ : ℝ := P.eigenvalue.re
  have hγ : 0 ≤ γ := hP.eigenpair.re_pos.le
  have hk1 : (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 := kStar_ge hμ (fun μ' h => (hK.2 μ' h).1)
  have hkμ : (⨅ μ' : K, μ'.1.re + 1 / 4) ≤ μ.re + 1 / 4 := by
    refine ciInf_le (f := fun μ' : K => μ'.1.re + 1 / 4) ⟨1 / 4, ?_⟩ ⟨μ, hμ⟩
    rintro _ ⟨μ', rfl⟩
    have := (hK.2 μ'.1 μ'.2).1
    linarith
  set k : ℝ := ⨅ μ' : K, μ'.1.re + 1 / 4
  have hkpos : 0 < k := by linarith
  -- Local finiteness and measurability of conjugated fields
  have hBG := gainLocBG c ν γ hγ hν0 b_sol G_sol hsol.energyLoc
  have hFl := gainLocF c ν γ hc hγ hν0 F hFm hFfin
  have hbm : ∀ i, Measurable fun p => b_sol p i := hsol.measurable
  have hGm : ∀ i j, Measurable fun p => G_sol p i j := hsol.gradMeasurable
  have hbm' := measurable_gainConj_vec (γ := γ) (ν := ν) hbm
  have hGm' := measurable_gainConj_ten γ ν hGm
  have hFm' := measurable_gainConj_ten γ ν hFm
  let gV : ℝ × (ℝ × ℝ) → ℝ := fun p => vnorm2 (gainConj γ ν b_sol p) ^ 2
  let gN : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν G_sol p) ^ 2
  let gQ : ℝ × (ℝ × ℝ) → ℝ := fun p => tnorm2 (gainConj γ ν F p) ^ 2
  have hgVm : Measurable gV := measurable_vnorm2_sq hbm'
  have hgNm : Measurable gN := (measurable_tnorm2 hGm').pow_const 2
  have hgQm : Measurable gQ := (measurable_tnorm2 hFm').pow_const 2
  have hgV0 : ∀ p, 0 ≤ gV p := fun _ => sq_nonneg _
  have hgN0 : ∀ p, 0 ≤ gN p := fun _ => sq_nonneg _
  have hgQ0 : ∀ p, 0 ≤ gQ p := fun _ => sq_nonneg _
  obtain ⟨hVm, hVi, -⟩ := sliceLoc c gV hc hgVm hgV0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1
  obtain ⟨hNm, hNi, -⟩ := sliceLoc c gN hc hgNm hgN0 fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2
  obtain ⟨hQm, hQi, -⟩ := sliceLoc c gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2
  let A : ℝ → ℝ := sliceSq c gV
  let N : ℝ → ℝ := sliceSq c gN
  let M_slice : ℝ → ℝ :=
    sliceSq c (fun p => tnorm2 (gainConj γ ν F p) * tnorm2 (gainConj γ ν G_sol p))
  let Q : ℝ → ℝ := sliceSq c gQ
  have hnn : ∀ s, 0 ≤ A s ∧ 0 ≤ N s ∧ 0 ≤ M_slice s ∧ 0 ≤ Q s :=
    fun s => ⟨sliceSq_nonneg hgV0 s, sliceSq_nonneg hgN0 s,
      sliceSq_nonneg (fun p => mul_nonneg (tnorm2_nonneg _) (tnorm2_nonneg _)) s,
      sliceSq_nonneg hgQ0 s⟩
  have hAdv_sol := hAdv c ν γ μ hc hν0 hγ tr htr F b_sol G_sol
    (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).1) hFm hsol
  have hY := youngSlice c (gainConj γ ν F) (gainConj γ ν G_sol) hc hFm' hGm'
    (fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2)
    (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2) ν hν0
  let L_str : ℝ → ℝ := fun s => (UnforcedLeray.B0277.supNormD 1 (tr.v s)).toReal
  let L_ite : ℝ → ℝ := fun s => if 0 < s then L_str s else 0
  have hL_meas : Measurable L_ite := measurable_supNormD_one_toReal_ite tr
  have hGm_fun : Measurable (Gfun k ν ν A N) := by
    unfold Gfun
    have h1 : Measurable fun s : ℝ => s ^ (-3 / 2 : ℝ) * A s := by fun_prop
    have h2 : Measurable fun s : ℝ => s ^ (-1 / 2 : ℝ) * N s := by fun_prop
    exact (h1.ennreal_ofReal.const_mul _).add (h2.ennreal_ofReal.const_mul _)
  -- Step 1: For every B > H, bound the tail integral of Gfun on [H - 1/2, B]
  have hB_bound : ∀ B : ℝ, H < B →
      ENNReal.ofReal (Real.exp (-2 * I_H)) *
          (∫⁻ s in Icc (H - 1 / 2) B, Gfun k ν ν A N s) ≤
        ENNReal.ofReal (2 * C_ramp * H) *
          (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
        ENNReal.ofReal ν⁻¹ *
          (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s)) := by
    intro B hHB
    have hB1 : 1 < B := by linarith
    have hB0 : 0 < B := by linarith
    set a : ℝ := H - 1
    set b_end : ℝ := 2 * B + H - 3 / 2
    have ha : 0 < a := by dsimp [a]; linarith
    have hab : a < b_end := by dsimp [a, b_end]; linarith
    let K_int : Set ℝ := Icc (H - 1) (2 * B + H)
    let L_0 : ℝ → ℝ := K_int.indicator L_str
    have hL0_of_mem : ∀ {s : ℝ}, s ∈ K_int → L_0 s = L_str s := fun hs =>
      Set.indicator_of_mem hs L_str
    have hL0_of_notMem : ∀ {s : ℝ}, s ∉ K_int → L_0 s = 0 := fun hs =>
      Set.indicator_of_notMem hs L_str
    have hL0_eq_ite : L_0 = K_int.indicator L_ite := by
      funext s
      by_cases hs : s ∈ K_int
      · have hs0 : 0 < s := by linarith [hs.1, hH2]
        simp [L_0, L_ite, hs, hs0]
      · simp [L_0, hs]
    have hL0_meas : Measurable L_0 := by
      rw [hL0_eq_ite]
      exact hL_meas.indicator measurableSet_Icc
    obtain ⟨M_L, hML0, hML_bd⟩ := supNormD_one_bound_on tr htr (by linarith : (0 : ℝ) ≤ 2 * B + H)
    have hL0_nn : ∀ s, 0 ≤ L_0 s := fun s => by
      by_cases hs : s ∈ K_int
      · simp [L_0, L_str, hs, ENNReal.toReal_nonneg]
      · simp [L_0, hs]
    have hL0_le : ∀ s, L_0 s ≤ M_L := fun s => by
      by_cases hs : s ∈ K_int
      · rw [hL0_of_mem hs]
        exact (hML_bd s ⟨by linarith [hs.1, hH2], hs.2⟩).2.1
      · rw [hL0_of_notMem hs]
        exact hML0
    have hL0_intOn : IntegrableOn L_0 K_int := by
      have hK_fin : volume K_int ≠ ⊤ := by
        dsimp [K_int]
        exact measure_Icc_lt_top.ne
      refine (integrableOn_const (C := M_L) hK_fin).mono' hL0_meas.aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hL0_nn s)]
      exact hL0_le s
    have hL0_int : Integrable L_0 volume := by
      have heq : K_int.indicator L_0 = L_0 := by
        funext s; by_cases hs : s ∈ K_int <;> simp [L_0, hs]
      rw [← heq]
      exact (integrable_indicator_iff measurableSet_Icc).2 hL0_intOn
    have hL0_loc : LocallyIntegrable L_0 volume := hL0_int.locallyIntegrable
    let L_n : ℕ → ℝ → ℝ := fun n => sm L_0 n
    have hLn_cd : ∀ n, ContDiff ℝ ∞ (L_n n) := fun n => sm_contDiff_of_locallyIntegrable hL0_loc n
    have hLn_cont : ∀ n, Continuous (L_n n) := fun n => (hLn_cd n).continuous
    have hLn_nn : ∀ n s, 0 ≤ L_n n s := fun n s => sm_nonneg L_0 hL0_nn n s
    have hLn_le : ∀ n s, L_n n s ≤ M_L := fun n s => sm_le_of_le hL0_meas hL0_nn hL0_le n s
    have hLn_ae : ∀ᵐ s ∂volume, Tendsto (fun n => L_n n s) atTop (𝓝 (L_0 s)) :=
      sm_ae_tendsto_of_locallyIntegrable hL0_loc
    -- Antiderivatives Ψ_n and Φ from H - 1 to s
    let Ψ_n : ℕ → ℝ → ℝ := fun n s => ∫ t in (H - 1)..s, L_n n t
    let Φ : ℝ → ℝ := fun s => ∫ t in (H - 1)..s, L_0 t
    have hΨn_deriv : ∀ n s, HasDerivAt (Ψ_n n) (L_n n s) s :=
      fun n s => ((hLn_cont n).integral_hasStrictDerivAt (H - 1) s).hasDerivAt
    have hΨn_cd : ∀ n, ContDiff ℝ 1 (Ψ_n n) := by
      intro n
      refine contDiff_one_iff_deriv.2 ⟨fun s => (hΨn_deriv n s).differentiableAt, ?_⟩
      have hd : deriv (Ψ_n n) = L_n n := funext fun s => (hΨn_deriv n s).deriv
      rw [hd]
      exact hLn_cont n
    have hΨn_nn : ∀ n {s : ℝ}, H - 1 ≤ s → 0 ≤ Ψ_n n s :=
      fun n _ hs => intervalIntegral.integral_nonneg hs (fun t _ => hLn_nn n t)
    have hΦ_le_IH : ∀ {s : ℝ}, H - 1 ≤ s → Φ s ≤ I_H := by
      intro s hs
      dsimp [Φ]
      rw [intervalIntegral.integral_of_le hs]
      have hInt : IntegrableOn L_0 (Ioc (H - 1) s) := hL0_int.integrableOn
      have h1 : ENNReal.ofReal (∫ t in Ioc (H - 1) s, L_0 t) ≤ ENNReal.ofReal I_H := by
        calc ENNReal.ofReal (∫ t in Ioc (H - 1) s, L_0 t)
            ≤ ∫⁻ t in Ioc (H - 1) s, ENNReal.ofReal (L_0 t) := ofReal_integral_le_lintegral' hInt
          _ ≤ ∫⁻ t in Ioi (H - 1), ENNReal.ofReal (L_0 t) :=
              lintegral_mono_set (fun t ht => ht.1)
          _ ≤ ∫⁻ t in Ioi (H - 1), UnforcedLeray.B0277.supNormD 1 (tr.v t) := by
              refine lintegral_mono fun t => ?_
              by_cases ht : t ∈ K_int
              · rw [hL0_of_mem ht]
                exact ENNReal.ofReal_toReal_le
              · rw [hL0_of_notMem ht, ENNReal.ofReal_zero]
                exact zero_le
          _ ≤ ENNReal.ofReal I_H := hStrain
      exact (ENNReal.ofReal_le_ofReal_iff hIH0).1 h1
    have hΨn_lim : ∀ {s : ℝ}, H - 1 ≤ s → Tendsto (fun n => Ψ_n n s) atTop (𝓝 (Φ s)) := by
      intro s hs
      dsimp [Ψ_n, Φ]
      simp only [intervalIntegral.integral_of_le hs]
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => M_L)
        (Eventually.of_forall fun n => (hLn_cont n).aestronglyMeasurable.restrict)
        (Eventually.of_forall fun n => Eventually.of_forall fun t => ?_)
        (integrableOn_const measure_Ioc_lt_top.ne)
        (ae_restrict_of_ae hLn_ae)
      rw [Real.norm_eq_abs, abs_of_nonneg (hLn_nn n t)]
      exact hLn_le n t
    -- Test weights ψ_n(s) = exp(-2 Ψ_n(s)) * tailRamp H B s
    let ψ_n : ℕ → ℝ → ℝ := fun n s => Real.exp (-2 * Ψ_n n s) * tailRamp H B s
    have hψn_cd : ∀ n, ContDiff ℝ 1 (ψ_n n) := fun n =>
      ((contDiff_const.mul (hΨn_cd n)).exp).mul (tailRamp_contDiff H B)
    have hψn_zero : ∀ n {s : ℝ}, s ∉ Icc a b_end → ψ_n n s = 0 := by
      intro n s hs
      dsimp [ψ_n]
      rw [tailRamp_eq_zero_of_not_mem hB0 hs, mul_zero]
    have hψn_supp : ∀ n, tsupport (ψ_n n) ⊆ Icc a b_end := by
      intro n
      refine closure_minimal (fun s hs => ?_) isClosed_Icc
      by_contra hs'
      exact hs (hψn_zero n hs')
    have hψn_cs : ∀ n, HasCompactSupport (ψ_n n) := fun n =>
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hψn_supp n)
    have hψn_ts : ∀ n, tsupport (ψ_n n) ⊆ Ioi 0 := fun n =>
      (hψn_supp n).trans fun s hs => lt_of_lt_of_le ha hs.1
    have hψn_nn : ∀ n s, 0 ≤ ψ_n n s := fun n s =>
      mul_nonneg (Real.exp_nonneg _) (tailRamp_nonneg H B s)
    have hψn_le_one : ∀ n s, ψ_n n s ≤ 1 := by
      intro n s
      by_cases hs : s ∈ Icc a b_end
      · have hexp : Real.exp (-2 * Ψ_n n s) ≤ 1 := by
          apply Real.exp_le_one_iff.2
          have := hΨn_nn n hs.1
          linarith
        exact mul_le_one₀ hexp (tailRamp_nonneg H B s) (tailRamp_le_one H B s)
      · rw [hψn_zero n hs]; exact zero_le_one
    have hψn_deriv_add : ∀ n s,
        deriv (ψ_n n) s + 2 * L_str s * ψ_n n s =
          2 * (L_0 s - L_n n s) * ψ_n n s + Real.exp (-2 * Ψ_n n s) * deriv (tailRamp H B) s := by
      intro n s
      have h1 : HasDerivAt (fun t => Real.exp (-2 * Ψ_n n t))
          (Real.exp (-2 * Ψ_n n s) * (-2 * L_n n s)) s :=
        ((hΨn_deriv n s).const_mul (-2)).exp
      have h2 : HasDerivAt (tailRamp H B) (deriv (tailRamp H B) s) s :=
        ((tailRamp_contDiff H B).differentiable one_ne_zero s).hasDerivAt
      have hd : deriv (ψ_n n) s =
          Real.exp (-2 * Ψ_n n s) * (-2 * L_n n s) * tailRamp H B s +
            Real.exp (-2 * Ψ_n n s) * deriv (tailRamp H B) s :=
        (h1.mul h2).deriv
      have hL_eq : L_str s * ψ_n n s = L_0 s * ψ_n n s := by
        by_cases hs : s ∈ Icc a b_end
        · have hsK : s ∈ K_int := ⟨hs.1, by dsimp [b_end] at hs; linarith [hs.2]⟩
          rw [hL0_of_mem hsK]
        · rw [hψn_zero n hs, mul_zero, mul_zero]
      rw [hd]
      dsimp [ψ_n] at hL_eq ⊢
      linarith
    -- Per-n bound
    have hper_n : ∀ n : ℕ,
        ∫⁻ s in Icc (H - 1 / 2) B, ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s ≤
          (∫⁻ s in Icc a b_end, ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))) +
          (ENNReal.ofReal (2 * C_ramp * H) *
              (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
            ENNReal.ofReal ν⁻¹ *
              (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))) := by
      intro n
      have hc1 := hψn_cd n
      have hsupp := hψn_supp n
      have hcs := hψn_cs n
      have hts := hψn_ts n
      have hψ0 := hψn_nn n
      obtain ⟨hint, hle⟩ := advection_cutoff_young (k := k) (ν := ν) (α := 1 / 2 + 2 * μ.re)
        (A := A) (N := N) (M := M_slice) (Q := Q) (ψ := ψ_n n)
        (D := fun s => deriv (ψ_n n) s + 2 * L_str s * ψ_n n s) (a := a) (b := b_end)
        hν0 (by linarith [hk1, hkμ]) hnn (hVi a b_end ha hab) (hNi a b_end ha hab)
        (hQi a b_end ha hab) hY hc1 ha hsupp hψ0 (hAdv_sol (ψ_n n) hc1 hcs hts hψ0)
      have iA12 : Integrable (fun s => ψ_n n s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_cutoff_mul hc1 ha hsupp (intOn_rpow_mul ha (hVi a b_end ha hab) _)
      have iQ12 : Integrable (fun s => ψ_n n s * (s ^ (-1 / 2 : ℝ) * Q s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_cutoff_mul hc1 ha hsupp (intOn_rpow_mul ha (hQi a b_end ha hab) _)
      have hDint1 : Integrable (fun s => deriv (ψ_n n) s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) :=
        integrable_contcutoff_mul (hc1.continuous_deriv le_rfl) ha
          (tsupport_deriv_subset.trans hsupp) (intOn_rpow_mul ha (hVi a b_end ha hab) _)
      have hDint2 : Integrable (fun s => 2 * L_str s * ψ_n n s * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) := by
        have heq : (fun s => 2 * L_str s * ψ_n n s * (s ^ (-1 / 2 : ℝ) * A s)) =
            fun s => 2 * L_0 s * (ψ_n n s * (s ^ (-1 / 2 : ℝ) * A s)) := by
          funext s
          by_cases hs : s ∈ Icc a b_end
          · have hsK : s ∈ K_int := ⟨hs.1, by dsimp [b_end] at hs; linarith [hs.2]⟩
            rw [hL0_of_mem hsK]; ring
          · simp [hψn_zero n hs]
        rw [heq]
        refine (iA12.const_mul (2 * M_L)).mono'
          (((measurable_const.mul hL0_meas).aestronglyMeasurable.restrict).mul iA12.aestronglyMeasurable)
          ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        have hpos : 0 ≤ ψ_n n s * (s ^ (-1 / 2 : ℝ) * A s) :=
          mul_nonneg (hψ0 s) (mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg zero_le_two (hL0_nn s)) hpos)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hL0_le s) zero_le_two) hpos
      have hDint : Integrable
          (fun s => (deriv (ψ_n n) s + 2 * L_str s * ψ_n n s) * (s ^ (-1 / 2 : ℝ) * A s))
          (volume.restrict (Ioi (0 : ℝ))) := by
        refine (hDint1.add hDint2).congr (Eventually.of_forall fun s => ?_)
        simp only [Pi.add_apply]; ring
      -- LHS lower bound on [H - 1/2, B]
      have s1 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s =
          ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ψ_n n s * cutG k ν ν A N s) := by
        have hc_eq : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s =
            ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (ψ_n n s * cutG k ν ν A N s) :=
          setLIntegral_congr_fun measurableSet_Ioi fun s hs =>
            ofReal_mul_Gfun hkpos (by linarith) (hnn s).1 (hnn s).2.1 hs (hψ0 s)
        rw [hc_eq]
        refine (ofReal_integral_eq_lintegral_ofReal hint ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 ≤ s := le_of_lt hs
        have h1 := mul_nonneg (Real.rpow_nonneg hs0 (-3 / 2 : ℝ)) (hnn s).1
        have h2 := mul_nonneg (Real.rpow_nonneg hs0 (-1 / 2 : ℝ)) (hnn s).2.1
        have : 0 ≤ cutG k ν ν A N s := by
          unfold cutG
          exact add_nonneg (mul_nonneg (by linarith) h1) (mul_nonneg (by linarith) h2)
        exact mul_nonneg (hψ0 s) this
      have hLHS_sub : ∫⁻ s in Icc (H - 1 / 2) B, ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s ≤
          ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ψ_n n s * cutG k ν ν A N s) := by
        rw [← s1]
        exact lintegral_mono_set (fun s hs => show (0 : ℝ) < s by linarith [hs.1, hH2])
      -- RHS bound for D term
      have s4 : ENNReal.ofReal (∫ s in Ioi (0 : ℝ),
            (deriv (ψ_n n) s + 2 * L_str s * ψ_n n s) * (s ^ (-1 / 2 : ℝ) * A s)) ≤
          (∫⁻ s in Icc a b_end, ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))) +
          ENNReal.ofReal (2 * C_ramp * H) *
            ∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
        refine (ofReal_integral_le_lintegral' hDint).trans ?_
        have hm1 : Measurable fun s : ℝ =>
            (Icc a b_end).indicator
              (fun s => ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))) s := by
          have hsub : Measurable fun s : ℝ => 2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s) :=
            (measurable_const.mul (measurable_abs.comp (hL0_meas.sub (hLn_cont n).measurable))).mul
              ((measurable_id.pow_const (-1 / 2 : ℝ)).mul hVm)
          exact hsub.ennreal_ofReal.indicator measurableSet_Icc
        calc ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal ((deriv (ψ_n n) s + 2 * L_str s * ψ_n n s) * (s ^ (-1 / 2 : ℝ) * A s))
            ≤ ∫⁻ s in Ioi (0 : ℝ),
                ((Icc a b_end).indicator
                  (fun s => ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))) s +
                (Ioo 0 H).indicator
                  (fun s => ENNReal.ofReal (2 * C_ramp * H) *
                    ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) s) := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
              have hs0 : 0 < s := hs
              have hpA : 0 ≤ s ^ (-1 / 2 : ℝ) * A s :=
                mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
              by_cases hs_ab : s ∈ Icc a b_end
              · rw [Set.indicator_of_mem hs_ab, hψn_deriv_add n s, add_mul]
                refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
                · apply ENNReal.ofReal_le_ofReal
                  have h1 : 2 * (L_0 s - L_n n s) * ψ_n n s ≤ 2 * |L_0 s - L_n n s| := by
                    have hle_abs : L_0 s - L_n n s ≤ |L_0 s - L_n n s| := le_abs_self _
                    have hψ1 := hψn_le_one n s
                    have hψ0' := hψ0 s
                    nlinarith [abs_nonneg (L_0 s - L_n n s)]
                  exact mul_le_mul_of_nonneg_right h1 hpA
                · have hd_ramp := tailRamp_deriv_le (H := H) hKσ0 hKσ hB1 s
                  by_cases hs_up : s ∈ Icc (H - 1) (H - 1 / 2)
                  · have hs_Ioo : s ∈ Ioo 0 H := ⟨hs0, by linarith [hs_up.2]⟩
                    rw [Set.indicator_of_mem hs_Ioo, ← ENNReal.ofReal_mul (by positivity)]
                    apply ENNReal.ofReal_le_ofReal
                    rw [Set.indicator_of_mem hs_up, mul_one] at hd_ramp
                    have hexp1 : Real.exp (-2 * Ψ_n n s) ≤ 1 :=
                      Real.exp_le_one_iff.2 (by linarith [hΨn_nn n hs_ab.1])
                    have hr : s ^ (-1 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s := by
                      rw [← Real.rpow_add_one hs0.ne']; norm_num
                    have hr3 : 0 ≤ s ^ (-3 / 2 : ℝ) * A s :=
                      mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
                    have hsH : s ≤ H := by linarith [hs_up.2]
                    have hA_le : s ^ (-1 / 2 : ℝ) * A s ≤ H * (s ^ (-3 / 2 : ℝ) * A s) := by
                      rw [hr]; nlinarith [mul_le_mul_of_nonneg_right hsH hr3]
                    have h1 : Real.exp (-2 * Ψ_n n s) * deriv (tailRamp H B) s ≤ 2 * C_ramp := by
                      calc Real.exp (-2 * Ψ_n n s) * deriv (tailRamp H B) s
                          ≤ Real.exp (-2 * Ψ_n n s) * (2 * C_ramp) :=
                            mul_le_mul_of_nonneg_left hd_ramp (Real.exp_nonneg _)
                        _ ≤ 1 * (2 * C_ramp) :=
                            mul_le_mul_of_nonneg_right hexp1 (by positivity)
                        _ = 2 * C_ramp := one_mul _
                    calc Real.exp (-2 * Ψ_n n s) * deriv (tailRamp H B) s * (s ^ (-1 / 2 : ℝ) * A s)
                        ≤ 2 * C_ramp * (s ^ (-1 / 2 : ℝ) * A s) :=
                          mul_le_mul_of_nonneg_right h1 hpA
                      _ ≤ 2 * C_ramp * (H * (s ^ (-3 / 2 : ℝ) * A s)) :=
                          mul_le_mul_of_nonneg_left hA_le (by positivity)
                      _ = 2 * C_ramp * H * (s ^ (-3 / 2 : ℝ) * A s) := by ring
                  · rw [Set.indicator_of_notMem hs_up, mul_zero] at hd_ramp
                    have hnp : Real.exp (-2 * Ψ_n n s) * deriv (tailRamp H B) s *
                        (s ^ (-1 / 2 : ℝ) * A s) ≤ 0 :=
                      mul_nonpos_of_nonpos_of_nonneg
                        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hd_ramp) hpA
                    rw [ENNReal.ofReal_of_nonpos hnp]
                    exact zero_le
              · have hd0 : deriv (ψ_n n) s = 0 :=
                  deriv_of_notMem_tsupport (fun h => hs_ab (hsupp h))
                rw [hd0, hψn_zero n hs_ab]
                simp
          _ = (∫⁻ s in Icc a b_end, ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))) +
              ENNReal.ofReal (2 * C_ramp * H) *
                ∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) := by
              have h_ab : Icc a b_end ∩ Ioi (0 : ℝ) = Icc a b_end :=
                Set.inter_eq_left.2 (fun x hx => lt_of_lt_of_le ha hx.1)
              have h_0H : Ioo (0 : ℝ) H ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) H :=
                Set.inter_eq_left.2 (fun x hx => hx.1)
              rw [lintegral_add_left hm1,
                lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc, h_ab,
                lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo, h_0H,
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      -- RHS bound for Q term
      have s5 : ENNReal.ofReal (ν⁻¹ * ∫ s in Ioi (0 : ℝ), ψ_n n s * (s ^ (-1 / 2 : ℝ) * Q s)) ≤
          ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hν0.le)]
        refine mul_le_mul_of_nonneg_left ((ofReal_integral_le_lintegral' iQ12).trans ?_) zero_le
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        apply ENNReal.ofReal_le_ofReal
        have h1 := mul_nonneg (Real.rpow_nonneg (le_of_lt hs) (-1 / 2 : ℝ)) (hnn s).2.2.2
        nlinarith [hψn_le_one n s, hψ0 s]
      rw [← add_assoc]
      exact hLHS_sub.trans ((ENNReal.ofReal_le_ofReal hle).trans
        (ENNReal.ofReal_add_le.trans (add_le_add s4 s5)))
    -- Pass to the limit n → ∞
    have hfat_n : ENNReal.ofReal (Real.exp (-2 * I_H)) *
          (∫⁻ s in Icc (H - 1 / 2) B, Gfun k ν ν A N s) ≤
        liminf (fun n => ∫⁻ s in Icc (H - 1 / 2) B,
          ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s) atTop := by
      have hmeasn : ∀ n, Measurable (fun s => ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s) :=
        fun n => (hψn_cd n).continuous.measurable.ennreal_ofReal.mul hGm_fun
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (setLIntegral_mono' measurableSet_Icc fun s hs => ?_).trans (lintegral_liminf_le hmeasn)
      have hs_H1 : H - 1 ≤ s := by linarith [hs.1]
      have htr1 : tailRamp H B s = 1 := tailRamp_one hH2 hB0 hs
      have hpt : Tendsto (fun n => ENNReal.ofReal (ψ_n n s) * Gfun k ν ν A N s) atTop
          (𝓝 (ENNReal.ofReal (Real.exp (-2 * Φ s)) * Gfun k ν ν A N s)) := by
        have h1 : Tendsto (fun n => ψ_n n s) atTop (𝓝 (Real.exp (-2 * Φ s))) := by
          dsimp [ψ_n]
          simp only [htr1, mul_one]
          exact (Real.continuous_exp.tendsto (-2 * Φ s)).comp ((hΨn_lim hs_H1).const_mul (-2))
        exact ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1)
          (Or.inl (ENNReal.ofReal_pos.2 (Real.exp_pos (-2 * Φ s))).ne')
      rw [hpt.liminf_eq]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      apply Real.exp_le_exp.2
      linarith [hΦ_le_IH hs_H1]
    have herr_lim : Tendsto
        (fun n => ∫⁻ s in Icc a b_end,
          ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s)))
        atTop (𝓝 0) := by
      have h0_eq : (0 : ℝ≥0∞) = ∫⁻ _ in Icc a b_end, (0 : ℝ≥0∞) := by simp
      rw [h0_eq]
      refine tendsto_lintegral_of_dominated_convergence'
        (fun s => ENNReal.ofReal (4 * M_L * (s ^ (-1 / 2 : ℝ) * A s))) ?_ ?_ ?_ ?_
      · intro n
        have hsub : Measurable fun s : ℝ => 2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s) :=
          (measurable_const.mul (measurable_abs.comp (hL0_meas.sub (hLn_cont n).measurable))).mul
            ((measurable_id.pow_const (-1 / 2 : ℝ)).mul hVm)
        exact hsub.ennreal_ofReal.aemeasurable
      · intro n
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
        apply ENNReal.ofReal_le_ofReal
        have hpA : 0 ≤ s ^ (-1 / 2 : ℝ) * A s :=
          mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1
        have habs : |L_0 s - L_n n s| ≤ 2 * M_L := by
          rw [abs_le]
          constructor <;> linarith [hL0_nn s, hL0_le s, hLn_nn n s, hLn_le n s]
        nlinarith [mul_le_mul_of_nonneg_right habs hpA]
      · have hIntA : IntegrableOn (fun s => 4 * M_L * (s ^ (-1 / 2 : ℝ) * A s)) (Icc a b_end) :=
          (intOn_rpow_mul ha (hVi a b_end ha hab) (-1 / 2)).const_mul (4 * M_L)
        have h_eq : ∫⁻ s in Icc a b_end, ENNReal.ofReal (4 * M_L * (s ^ (-1 / 2 : ℝ) * A s)) =
            ENNReal.ofReal (∫ s in Icc a b_end, 4 * M_L * (s ^ (-1 / 2 : ℝ) * A s)) := by
          refine (ofReal_integral_eq_lintegral_ofReal hIntA ?_).symm
          filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
          have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
          exact mul_nonneg (by positivity)
            (mul_nonneg (Real.rpow_nonneg hs0.le _) (hnn s).1)
        rw [h_eq]
        exact ENNReal.ofReal_ne_top
      · filter_upwards [ae_restrict_of_ae hLn_ae] with s hs_lim
        have h1 : Tendsto (fun n => 2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))
            atTop (𝓝 0) := by
          have hsub : Tendsto (fun n => |L_0 s - L_n n s|) atTop (𝓝 0) := by
            simpa using ((tendsto_const_nhds (x := L_0 s)).sub hs_lim).abs
          simpa using (hsub.const_mul 2).mul_const (s ^ (-1 / 2 : ℝ) * A s)
        simpa using ENNReal.tendsto_ofReal h1
    set RHS_B : ℝ≥0∞ :=
      ENNReal.ofReal (2 * C_ramp * H) *
        (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
      ENNReal.ofReal ν⁻¹ *
        (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))
    have hRHS_lim : Tendsto
        (fun n => (∫⁻ s in Icc a b_end,
          ENNReal.ofReal (2 * |L_0 s - L_n n s| * (s ^ (-1 / 2 : ℝ) * A s))) + RHS_B)
        atTop (𝓝 RHS_B) := by
      simpa using herr_lim.add_const RHS_B
    exact hfat_n.trans ((liminf_le_liminf (Eventually.of_forall hper_n)).trans hRHS_lim.liminf_eq.le)
  -- Step 2: Let B = (m : ℝ) + H + 1 → ∞ via Fatou on Ici (H - 1/2)
  set Bm : ℕ → ℝ := fun m => (m : ℝ) + H + 1
  have hBm_gt : ∀ m, H < Bm m := fun m => by
    unfold Bm
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hTail_Gfun : ∫⁻ s in Ici (H - 1 / 2), Gfun k ν ν A N s ≤
      ENNReal.ofReal (Real.exp (2 * I_H)) *
        (ENNReal.ofReal (2 * C_ramp * H) *
            (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
          ENNReal.ofReal ν⁻¹ *
            (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))) := by
    have hper_m : ∀ m : ℕ,
        ∫⁻ s in Ici (H - 1 / 2), (Iic (Bm m)).indicator (Gfun k ν ν A N) s ≤
          ENNReal.ofReal (Real.exp (2 * I_H)) *
            (ENNReal.ofReal (2 * C_ramp * H) *
                (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
              ENNReal.ofReal ν⁻¹ *
                (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))) := by
      intro m
      have h_ind : ∫⁻ s in Ici (H - 1 / 2), (Iic (Bm m)).indicator (Gfun k ν ν A N) s =
          ∫⁻ s in Icc (H - 1 / 2) (Bm m), Gfun k ν ν A N s := by
        rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        have hinter : Iic (Bm m) ∩ Ici (H - 1 / 2) = Icc (H - 1 / 2) (Bm m) := by
          ext s; simp [and_comm]
        rw [hinter]
      rw [h_ind]
      calc ∫⁻ s in Icc (H - 1 / 2) (Bm m), Gfun k ν ν A N s
          = ENNReal.ofReal (Real.exp (2 * I_H)) *
              (ENNReal.ofReal (Real.exp (-2 * I_H)) *
                ∫⁻ s in Icc (H - 1 / 2) (Bm m), Gfun k ν ν A N s) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            ring_nf
            rw [Real.exp_zero, ENNReal.ofReal_one, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (2 * I_H)) *
              (ENNReal.ofReal (2 * C_ramp * H) *
                  (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
                ENNReal.ofReal ν⁻¹ *
                  (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))) :=
            mul_le_mul_of_nonneg_left (hB_bound (Bm m) (hBm_gt m)) zero_le
    have hmeas_m : ∀ m, Measurable (fun s => (Iic (Bm m)).indicator (Gfun k ν ν A N) s) :=
      fun m => hGm_fun.indicator measurableSet_Iic
    calc ∫⁻ s in Ici (H - 1 / 2), Gfun k ν ν A N s
        = ∫⁻ s in Ici (H - 1 / 2),
            liminf (fun m => (Iic (Bm m)).indicator (Gfun k ν ν A N) s) atTop := by
          refine setLIntegral_congr_fun measurableSet_Ici fun s _hs => ?_
          have e1 : ∀ᶠ m : ℕ in atTop, s ≤ (m : ℝ) :=
            tendsto_natCast_atTop_atTop.eventually_ge_atTop s
          have hev : ∀ᶠ m : ℕ in atTop,
              (Iic (Bm m)).indicator (Gfun k ν ν A N) s = Gfun k ν ν A N s := by
            filter_upwards [e1] with m hm
            have hmem : s ∈ Iic (Bm m) := by
              rw [mem_Iic]
              dsimp [Bm]
              linarith [hm, hH2]
            exact Set.indicator_of_mem hmem _
          exact (tendsto_const_nhds.congr' (hev.mono fun m h => h.symm)).liminf_eq.symm
      _ ≤ liminf (fun m => ∫⁻ s in Ici (H - 1 / 2),
            (Iic (Bm m)).indicator (Gfun k ν ν A N) s) atTop :=
          lintegral_liminf_le hmeas_m
      _ ≤ _ := (liminf_le_liminf (Eventually.of_forall hper_m)).trans tendsto_const_nhds.liminf_eq.le
  -- Step 3: Convert slice integrals to hCalNormTail, tCalNormTail, hCalNormOn, tCalNorm
  have ht_pos : 0 < H - 1 / 2 := by linarith
  have eTailB : hCalNormTail c (H - 1 / 2) (gainConj γ ν b_sol) ^ 2 =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) :=
    hCalNormTail_sq_eq hc ht_pos hbm' (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1)
  have eTailG : tCalNormTail c (H - 1 / 2) (gainConj γ ν G_sol) ^ 2 =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s) :=
    tCalNormTail_sq_eq hc ht_pos hGm' (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).2)
  have eOnB : hCalNormOn c H (gainConj γ ν b_sol) ^ 2 =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s) :=
    hCalNormOn_sq_eq hc hbm' (fun s₁ s₂ h1 h2 => (hBG s₁ s₂ h1 h2).1)
  have eFullF : tCalNorm c (gainConj γ ν F) ^ 2 =
      ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s) := by
    rw [normSq.2]
    exact (ageSlice c (-1 / 2) gQ hc hgQm hgQ0 fun s₁ s₂ h1 h2 => (hFl s₁ s₂ h1 h2).2).1
  have hLHS_Gfun : ENNReal.ofReal (2 * k) *
        (∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
      ENNReal.ofReal ν *
        (∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s)) =
      ∫⁻ s in Ici (H - 1 / 2), Gfun k ν ν A N s := by
    have h1 : Measurable fun s : ℝ => s ^ (-3 / 2 : ℝ) * A s := by fun_prop
    have hsub : 2 * ν - ν = ν := by ring
    unfold Gfun
    rw [hsub, lintegral_add_left (h1.ennreal_ofReal.const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [eTailB, eTailG, eOnB, eFullF]
  have hmul_c := mul_le_mul_of_nonneg_left hTail_Gfun (zero_le (a := ENNReal.ofReal c⁻¹))
  rw [← hLHS_Gfun] at hmul_c
  have hC1 : ENNReal.ofReal (2 * C_ramp * H) ≤ ENNReal.ofReal (C_trace * H) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hC2 : ENNReal.ofReal ν⁻¹ ≤ ENNReal.ofReal (C_trace * ν⁻¹) := by
    apply ENNReal.ofReal_le_ofReal
    have : 1 ≤ C_trace := le_max_right _ _
    nlinarith [inv_pos.2 hν0]
  calc ENNReal.ofReal (2 * k) *
          (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
        ENNReal.ofReal ν *
          (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s))
      = ENNReal.ofReal c⁻¹ *
          (ENNReal.ofReal (2 * k) *
              (∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
            ENNReal.ofReal ν *
              (∫⁻ s in Ici (H - 1 / 2), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * N s))) := by ring
    _ ≤ ENNReal.ofReal c⁻¹ *
          (ENNReal.ofReal (Real.exp (2 * I_H)) *
            (ENNReal.ofReal (2 * C_ramp * H) *
                (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
              ENNReal.ofReal ν⁻¹ *
                (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s)))) := hmul_c
    _ ≤ ENNReal.ofReal c⁻¹ *
          (ENNReal.ofReal (Real.exp (2 * I_H)) *
            (ENNReal.ofReal (C_trace * H) *
                (∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
              ENNReal.ofReal (C_trace * ν⁻¹) *
                (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_right hC1 zero_le)
              (mul_le_mul_of_nonneg_right hC2 zero_le))
            zero_le)
          zero_le
    _ = ENNReal.ofReal (Real.exp (2 * I_H)) *
          (ENNReal.ofReal (C_trace * H) *
              (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioo 0 H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ) * A s)) +
            ENNReal.ofReal (C_trace * ν⁻¹) *
              (ENNReal.ofReal c⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * Q s))) := by
        ring

end UnforcedLeray.Short.IIIa
