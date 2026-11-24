import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5

/-!
# `PartII-b:T13/1/5/5/7` decomposition: approximate identity on `L^r(cylMeas)`

Source: `the November 2 reference manuscript` lines 1932-1935 (preliminary smoothing,
standard).  `MollApprox` follows from `MollLoc`, `MollYoung`, a density statement (`MollDensity`:
periodic `L^r(cylMeas)` functions are approximated by continuous, bounded, `q`-periodic functions
with compact support in `(s, η)`) and the approximate identity for such nice functions (`MollNice`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- **Density** (periodization of `C_c` approximants): a `q`-periodic measurable function of finite
`L^r(cylMeas c)` norm is `L^r(cylMeas c)`-approximated by continuous, bounded, exactly `q`-periodic
functions vanishing for `|s|` or `|η|` large. -/
def MollDensity : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (f : Coord → ℂ), QPeriodicS c f →
    AEStronglyMeasurable f volume → eLpNorm f (ENNReal.ofReal r) (cylMeas c) < ⊤ →
    ∀ δ : ℝ≥0∞, 0 < δ → ∃ g : Coord → ℂ, Continuous g ∧ (∀ x, g (qShift c x) = g x) ∧
      (∃ B : ℝ, ∀ x, ‖g x‖ ≤ B) ∧ (∃ M : ℝ, ∀ x : Coord, M < |x.1| ∨ M < |x.2.2| → g x = 0) ∧
      eLpNorm (fun x => f x - g x) (ENNReal.ofReal r) (cylMeas c) < δ

/-- **Approximate identity for nice functions**: for `g` continuous, bounded, with support in a
bounded `(s, η)` region (and `q`-periodic), `g ⋆ ρ_n → g` in `L^r(cylMeas c)`. -/
def MollNice : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (ρ : Coord → ℝ), IsMollifier ρ →
    (∀ n : ℕ, IsMollifier (molN ρ n)) → ∀ g : Coord → ℂ, Continuous g → (∀ x, g (qShift c x) = g x) →
    ∀ B : ℝ, (∀ x, ‖g x‖ ≤ B) → ∀ M : ℝ, (∀ x : Coord, M < |x.1| ∨ M < |x.2.2| → g x = 0) →
    Tendsto (fun n : ℕ => eLpNorm (fun x => convK (molN ρ n) g x - g x) (ENNReal.ofReal r)
      (cylMeas c)) atTop (𝓝 0)

theorem mollApprox_cylMeas_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  have h1 : UnforcedLeray.Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)) := by
    refine Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal c⁻¹) ?_
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    refine Measure.le_iff'.2 fun s => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_le_self s) _
  exact Measure.AbsolutelyContinuous.prod (Measure.AbsolutelyContinuous.rfl) h1

theorem mollApprox_conv_sub {κ : Coord → ℝ} (hκ : IsKer κ) {f g : Coord → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) (x : Coord) :
    convK κ (fun y => f y - g y) x = convK κ f x - convK κ g x := by
  have hc : Continuous (fun y => (κ (x - y) : ℂ)) :=
    Complex.continuous_ofReal.comp (hκ.1.continuous.comp (continuous_const.sub continuous_id))
  have hs : HasCompactSupport (fun y => (κ (x - y) : ℂ)) := by
    have : HasCompactSupport (fun y => κ (x - y)) :=
      hκ.2.comp_homeomorph ((Homeomorph.neg Coord).trans (Homeomorph.addLeft x))
    exact this.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have h1 := hf.integrable_smul_left_of_hasCompactSupport hc hs
  have h2 := hg.integrable_smul_left_of_hasCompactSupport hc hs
  simp only [convK, sub_mul]
  rw [integral_sub]
  · simpa [mul_comm] using h1
  · simpa [mul_comm] using h2

theorem mollApprox_norm_one {ρ : Coord → ℝ} (h : IsMollifier ρ) :
    ENNReal.ofReal (∫ x, |ρ x|) = 1 := by
  have : ∫ x, |ρ x| = 1 := by
    rw [← h.2.2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => abs_of_nonneg (h.2.1 x))
  rw [this]; simp

/-- **Assembly.** `MollApprox` from `MollLoc`, `MollYoung`, `MollDensity`, `MollNice`. -/
theorem mollApprox_of (hL : MollLoc) (hY : MollYoung) (hD : MollDensity) (hN : MollNice)
    (hC : MollConvNice) : MollApprox := by
  intro c r hc hr ρ hρ hρn f hper hfm hfin
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have hfloc := hL c r hc hr f hper hfm hfin
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδ : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨g, hgc, hgp, ⟨B, hB⟩, ⟨M, hM⟩, hfg⟩ := hD c r hc hr f hper hfm hfin (ε / 3) hδ
  have hnice := hN c r hc hr ρ hρ hρn g hgc hgp B hB M hM
  have hev : ∀ᶠ n : ℕ in atTop, eLpNorm (fun x => convK (molN ρ n) g x - g x)
      (ENNReal.ofReal r) (cylMeas c) < ε / 3 := (tendsto_order.1 hnice).2 _ hδ
  filter_upwards [hev] with n hn
  have hgloc : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hker : IsKer (molN ρ n) := (hρn n).1
  have hperfg : QPeriodicS c (fun y => f y - g y) := by
    filter_upwards [hper] with x hx
    simp [hx, hgp x]
  have hmfg : AEStronglyMeasurable (fun y => f y - g y) volume :=
    hfm.sub hgc.aestronglyMeasurable
  have hlocfg : LocallyIntegrable (fun y => f y - g y) volume := hfloc.sub hgloc
  have hY' := hY c r hc hr (molN ρ n) (fun y => f y - g y) hker hperfg hmfg
  rw [mollApprox_norm_one (hρn n), one_mul] at hY'
  have hcont1 : Continuous (convK (molN ρ n) (fun y => f y - g y)) :=
    (hC c (molN ρ n) _ hker hperfg hlocfg).1.continuous
  have hcont2 : Continuous (convK (molN ρ n) g) :=
    (hC c (molN ρ n) g hker (Filter.Eventually.of_forall hgp) hgloc).1.continuous
  have hac := mollApprox_cylMeas_ac c
  have hfm' : AEStronglyMeasurable f (cylMeas c) := hfm.mono_ac hac
  have heq : (fun x => convK (molN ρ n) f x - f x) =
      (fun x => convK (molN ρ n) (fun y => f y - g y) x) +
      (fun x => convK (molN ρ n) g x - g x) + (fun x => g x - f x) := by
    funext x
    simp only [Pi.add_apply]
    rw [mollApprox_conv_sub hker hfloc hgloc x]
    ring
  rw [heq]
  have m1 : AEStronglyMeasurable (fun x => convK (molN ρ n) (fun y => f y - g y) x) (cylMeas c) :=
    hcont1.aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun x => convK (molN ρ n) g x - g x) (cylMeas c) :=
    (hcont2.sub hgc).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun x => g x - f x) (cylMeas c) :=
    hgc.aestronglyMeasurable.sub hfm'
  have e3 : eLpNorm (fun x => g x - f x) (ENNReal.ofReal r) (cylMeas c) =
      eLpNorm (fun x => f x - g x) (ENNReal.ofReal r) (cylMeas c) := by
    rw [← eLpNorm_neg]; congr 1; funext x; simp
  calc eLpNorm _ (ENNReal.ofReal r) (cylMeas c)
      ≤ eLpNorm ((fun x => convK (molN ρ n) (fun y => f y - g y) x) +
          (fun x => convK (molN ρ n) g x - g x)) (ENNReal.ofReal r) (cylMeas c) +
        eLpNorm (fun x => g x - f x) (ENNReal.ofReal r) (cylMeas c) :=
        eLpNorm_add_le (m1.add m2) m3 hp1
    _ ≤ (eLpNorm (fun x => convK (molN ρ n) (fun y => f y - g y) x) (ENNReal.ofReal r)
          (cylMeas c) + eLpNorm (fun x => convK (molN ρ n) g x - g x) (ENNReal.ofReal r)
          (cylMeas c)) + eLpNorm (fun x => g x - f x) (ENNReal.ofReal r) (cylMeas c) := by
        exact add_le_add (eLpNorm_add_le m1 m2 hp1) le_rfl
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := by
        rw [e3]
        exact add_le_add (add_le_add (hY'.trans hfg.le) hn.le) hfg.le
    _ = ε := ENNReal.add_thirds ε

end UnforcedLeray.Short.IIb
