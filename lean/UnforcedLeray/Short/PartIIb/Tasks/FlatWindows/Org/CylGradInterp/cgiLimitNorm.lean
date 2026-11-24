import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6

/-!
# `CgiLimitNorm`: passing the a priori inequality to the limit (SP 1934-1935)
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem cylMeas_ac_volume (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  have h : cylMeas c ≪ (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) := by
    refine Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.refl _) ?_
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.smul_absolutelyContinuous.trans Measure.restrict_le_self.absolutelyContinuous
  simpa [Measure.volume_eq_prod] using h

theorem cdv_aesm (c : ℝ) {w : Coord → ℂ} (hw : ContDiff ℝ ∞ w) (j : Fin 3) :
    AEStronglyMeasurable (cdv j w) (cylMeas c) := by
  have : Continuous (cdv j w) := by
    unfold cdv
    have h1 : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
    exact h1.clm_apply continuous_const
  exact this.aestronglyMeasurable

theorem cdv_contDiff {w : Coord → ℂ} (hw : ContDiff ℝ ∞ w) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j w) := by
  unfold cdv
  have h1 : ContDiff ℝ ∞ (fderiv ℝ w) := hw.fderiv_right (by simp)
  exact h1.clm_apply contDiff_const

theorem cgiLimitNorm_proof : UnforcedLeray.Short.IIb.CgiLimitNorm := by
  intro r hr c C hc hC hA u D2 w hw hup hum hD2 D1 hD1 hT i lam hlam
  obtain ⟨hnice, hu, hd2⟩ := hw
  have hacS : ∀ f : Coord → ℂ, AEStronglyMeasurable f volume →
      AEStronglyMeasurable f (cylMeas c) := fun f hf => hf.mono_ac (cylMeas_ac_volume c)
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  set p := ENNReal.ofReal r with hpdef
  -- triangle inequality helpers
  have tri : ∀ f g : Coord → ℂ, AEStronglyMeasurable f (cylMeas c) →
      AEStronglyMeasurable g (cylMeas c) →
      cylNorm c r f ≤ cylNorm c r g + cylNorm c r (fun x => g x - f x) := by
    intro f g hf hg
    have : f = fun x => g x - (g x - f x) := by funext x; ring
    calc cylNorm c r f = cylNorm c r (fun x => g x - (g x - f x)) := by rw [← this]
      _ ≤ _ := by
        refine eLpNorm_sub_le hg (hg.sub hf) hp |>.trans ?_
        refine add_le_add le_rfl (le_of_eq ?_)
        rfl
  have tri' : ∀ f g : Coord → ℂ, AEStronglyMeasurable f (cylMeas c) →
      AEStronglyMeasurable g (cylMeas c) →
      cylNorm c r f ≤ cylNorm c r g + cylNorm c r (fun x => f x - g x) := by
    intro f g hf hg
    have : f = fun x => g x + (f x - g x) := by funext x; ring
    calc cylNorm c r f = cylNorm c r (fun x => g x + (f x - g x)) := by rw [← this]
      _ ≤ _ := eLpNorm_add_le hg (hf.sub hg) hp
  have hwm : ∀ n, AEStronglyMeasurable (w n) (cylMeas c) := fun n =>
    (hnice n).smooth.continuous.aestronglyMeasurable
  have hum' := hacS u hum
  have hD2m : ∀ k l, AEStronglyMeasurable (D2 k l) (cylMeas c) := fun k l => hacS _ (hD2 k l)
  have hD1m := hacS _ (hD1 i).2
  have hcm : ∀ n, AEStronglyMeasurable (cdv i.succ (w n)) (cylMeas c) := fun n =>
    cdv_aesm c (hnice n).smooth _
  have hcc : ∀ (n : ℕ) (k l : Fin 2), AEStronglyMeasurable (cdv k.succ (cdv l.succ (w n))) (cylMeas c) := fun n (k l : Fin 2) =>
    cdv_aesm c (cdv_contDiff (hnice n).smooth _) _
  set a : ℕ → ℝ≥0∞ := fun n => cylNorm c r (fun x => w n x - u x) with ha
  set b : ℕ → Fin 2 → Fin 2 → ℝ≥0∞ := fun n k l =>
    cylNorm c r (fun x => cdv k.succ (cdv l.succ (w n)) x - D2 k l x) with hb
  set t : ℕ → ℝ≥0∞ := fun n => cylNorm c r (fun x => cdv i.succ (w n) x - D1 i x) with ht
  let F : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * (cylNorm c r u + a n) +
      ENNReal.ofReal lam * ∑ k : Fin 2, ∑ l : Fin 2, (cylNorm c r (D2 k l) + b n k l)) + t n
  have hle : ∀ n, cylNorm c r (D1 i) ≤ F n := by
    intro n
    refine (tri _ _ hD1m (hcm n)).trans ?_
    show _ ≤ _ + t n
    refine add_le_add_left ?_ _
    refine (hA (w n) (hnice n) i lam hlam).trans ?_
    gcongr with k _ l _
    · exact tri' _ _ (hwm n) hum'
    · exact tri' _ _ (hcc n k l) (hD2m k l)
  have hlim : Tendsto F atTop (𝓝 (cgiRhs c r C lam u D2)) := by
    have h1 : Tendsto a atTop (𝓝 0) := hu
    have h2 : ∀ k l, Tendsto (fun n => b n k l) atTop (𝓝 0) := fun k l => hd2 k l
    have h3 : Tendsto t atTop (𝓝 0) := hT i
    have e1 : Tendsto (fun n => cylNorm c r u + a n) atTop (𝓝 (cylNorm c r u + 0)) :=
      tendsto_const_nhds.add h1
    have e2 : Tendsto (fun n => ∑ k : Fin 2, ∑ l : Fin 2, (cylNorm c r (D2 k l) + b n k l))
        atTop (𝓝 (∑ k : Fin 2, ∑ l : Fin 2, (cylNorm c r (D2 k l) + 0))) :=
      tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
        tendsto_const_nhds.add (h2 k l)
    have e3 := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal lam⁻¹) e1 (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal lam) e2 (Or.inr ENNReal.ofReal_ne_top))
    have e4 := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) e3 (Or.inr ENNReal.ofReal_ne_top)).add h3
    simpa [F, cgiRhs] using e4
  exact ge_of_tendsto' hlim hle

end UnforcedLeray.Short.IIb
