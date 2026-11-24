import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis.NvLimit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis.TrainDecay
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!
# The axis continuity of the raw lift (task `PartIII-b:C/rep/8/2/pres/4/2/1/1/3`)

Source `the November 2 reference manuscript`:
Proposition `sct:lift` (1205-1225: the lift is smooth through the axis for positive time) and its
proof (1310-1323: term-by-term heat expansion, flat fluctuations, leading mean `2R⁻¹a₀G_ν`).

`Params.raw = axisExt (N_v b_raw)` takes `limUnder` along `𝓝[axisᶜ] y` at axis points
(`Cons/L2/BackgroundConcrete/Fields.lean:126-140`).

## What is proved

* **Lemma A** (`RawAxisOrg.rawAxisContinuous_of_tendsto`): if the off-axis lift has a limit along
  `𝓝[axisᶜ] y` at every axis point, then `RawAxisContinuous` holds (`limUnder` is that limit, and the
  test points `y + (m+1)⁻¹e₀` approach `y` off the axis).
* `rawAxisCont_of_of_limExists`: the target `D.RawAxisCont` from the smooth-extension statement
  `RawAxisOrg.RawAxisLimExists D` (the off-axis limit exists at every level).
* `rawAxisLimExists_eventually` / `rawAxisCont_eventually_of`: for all **large** `n` the limit exists,
  from the Part I standing hypotheses `TrainMeanExpansion`, `TrainFluctuationDecay` (and the proved
  `trainMeanEquations_proof`), through the accepted chain of task `pres/6/axis`
  (`axisEvNvLimit`, `axisEvTrainDecay_of`): the limit is `2εa₀G_ν(y₃)e₃`.
* `rawSupBound_of_eventually`: the parent `RawSupBound` needs the axis continuity only for large
  `n`, so it follows from `rawAxisCont_eventually_of`.

## Why the target as stated (`∀ n`) is not closed here

`SeqData.RawAxisCont D := ∀ n, RawAxisContinuous D.Pl (D.level n)` asks for every level, but the
Part I statements (`sct:heat`, 437-467) hold only for `ν ≤ ν₀` with `ν₀` existential, and nothing in
`SeqData`/`RepairStanding` controls the finitely many levels with `ν_n > ν₀`.  The large-age
asymptotics of those trains (true in the source for each fixed `ν`, Proposition `sct:lift`) is the
remaining input `RawAxisLimExists` at those levels.  The consumer of this task, `rawSupBound_of`
(`Org.lean:55`), uses the axis continuity only inside `∀ᶠ n`; `rawSupBound_of_eventually` below is
that theorem with the eventual hypothesis (as `AxisEv` of task `pres/6` already does for the
measurability consumer).
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace RawAxisOrg

/-- **The off-axis limit of the raw lift exists at every level** (the smooth-extension statement of
source 1205-1225, `sct:lift`: the lift is smooth through the axis for positive time): at every
level `n`, phase `τ` and axis point `y`, the off-axis lift `N_v b_raw(τ, ·)` has a limit along
`𝓝[axisᶜ] y`. -/
def RawAxisLimExists (D : SeqData) : Prop :=
  ∀ (n : ℕ) (τ : ℝ) (y : Space), y ∈ axis → ∃ L : Space,
    Tendsto (Nv (D.level n).ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v
      (D.train n).ψ) τ) (𝓝[axisᶜ] y) (𝓝 L)

/-- **Lemma A**: the axis value of `rawU` is the continuous extension as soon as the off-axis lift
has a limit along `𝓝[axisᶜ] y` at each axis point. -/
theorem rawAxisContinuous_of_tendsto (Pl : PlanarData) (L : ReturnLevel)
    (h : ∀ (τ : ℝ) (y : Space), y ∈ axis → ∃ A : Space,
      Tendsto (Nv L.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ) τ)
        (𝓝[axisᶜ] y) (𝓝 A)) :
    RawAxisContinuous Pl L := by
  intro τ y hy
  obtain ⟨A, hlim⟩ := h τ y hy
  set f : Space → Space :=
    Nv L.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile L.ε L.train.v L.train.ψ) τ with hf
  have hseq := AxisEvOrg.tendsto_shift y hy
  have : (𝓝[axisᶜ] y).NeBot := hseq.neBot
  have hraw : rawU Pl L τ = UnforcedLeray.Cons.C03.Concrete.axisExt f := rfl
  have hval : rawU Pl L τ y = A := by
    rw [hraw]
    simp only [UnforcedLeray.Cons.C03.Concrete.axisExt, hy, ↓reduceIte]
    exact hlim.limUnder_eq
  rw [hval]
  refine (hlim.comp hseq).congr fun m => ?_
  rw [hraw]
  exact (UnforcedLeray.Cons.C03.Concrete.axisExt_of_not_mem
    (AxisEvOrg.shift_not_mem_axis y hy m)).symm

end RawAxisOrg

open RawAxisOrg

/-- **The target from the smooth-extension statement**: if the off-axis limit of the raw lift
exists at every level (`RawAxisLimExists`, source 1205-1225), the axis value is the continuous
extension at every level. -/
theorem rawAxisCont_of_of_limExists (D : SeqData) (h : RawAxisLimExists D) : D.RawAxisCont :=
  fun n => rawAxisContinuous_of_tendsto D.Pl (D.level n) (h n)

/-- **The off-axis limit exists at every large level** (source 1205-1225, 1310-1323), from the
Part I standing hypotheses `sct:fluctuation` (439-446) and `sct:expansion` (447-459) with the
proved mean equations `sct:mean` (397-404): `ν_n → 0`, so for large `n` the raw profile of the BUC
train of level `n` has the uniform late-age axis decay (`axisEvTrainDecay_of`) with axial limit
`2εa₀G_ν`, and the ring lift then tends to `2εa₀G_ν(y₃)e₃` (`axisEvNvLimit`). -/
theorem rawAxisLimExists_eventually (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, ∀ (τ : ℝ) (y : Space), y ∈ axis → ∃ L : Space,
      Tendsto (Nv (D.level n).ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v
        (D.train n).ψ) τ) (𝓝[axisᶜ] y) (𝓝 L) := by
  obtain ⟨ν₀, hν₀, hT⟩ :=
    axisEvTrainDecay_of hF hM UnforcedLeray.Short.PartI.trainMeanEquations_proof
  have hev : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  filter_upwards [hev] with n hn τ y hy
  have hd := hT (retNu D.Pl D.σ₀ n) (retNu_pos _ _ _) hn.le (D.train n) (D.train_buc n)
    (retEps D.Pl D.σ₀ n)
  exact ⟨_, axisEvNvLimit _ _ _ (inv_pos.2 (D.level n).ε_pos) hd τ y hy⟩

/-- **The axis continuity at every large level** (source 1205-1225), from the Part I standing
hypotheses. -/
theorem rawAxisCont_eventually_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, RawAxisContinuous D.Pl (D.level n) := by
  filter_upwards [rawAxisLimExists_eventually hM hF D hst] with n hn
  exact rawAxisContinuous_of_tendsto D.Pl (D.level n) hn

/-- **The parent sup bound needs the axis continuity only for large `n`**: `rawSupBound_of`
(`Org.lean`) with the hypothesis `D.RawAxisCont` replaced by its eventual form (which
`rawAxisCont_eventually_of` supplies from the Part I standing hypotheses). -/
theorem rawSupBound_of_eventually (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : RawSupOrg.VelWeightedSup D) (h2 : RawSupOrg.RaisedWeightedSup D)
    (h3 : ∀ᶠ n : ℕ in atTop, RawAxisContinuous D.Pl (D.level n)) :
    RawSupBound D := by
  obtain ⟨C1, k1, hA⟩ := h1
  obtain ⟨C2, k2, hB⟩ := h2
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)
  refine ⟨|C1| + |C2|, max k1 k2, ?_⟩
  filter_upwards [hA, hB, hν1, h3] with n hA hB hν hax τ y
  have hνpos : 0 < (D.level n).ν := (D.level n).ν_pos
  have ha : (1 : ℝ) ≤ (D.level n).ν⁻¹ := one_le_inv_iff₀.2 ⟨hνpos, hν⟩
  set a := (D.level n).ν⁻¹ with hadef
  have hapos : 0 < a := by linarith
  -- the bound on the off-axis points
  have hoff : ∀ y : Space, y ∉ axis →
      ‖rawU D.Pl (D.level n) τ y‖ ≤ (|C1| + |C2|) * a ^ (max k1 k2) := by
    intro y hy
    have hε := (D.level n).ε_pos
    have hR : ((D.level n).ε⁻¹) ≠ 0 := (inv_pos.2 hε).ne'
    have hs : 0 < age (D.level n).ε⁻¹ y := age_pos hR hy
    have e : rawU D.Pl (D.level n) τ y = Nv (D.level n).ε⁻¹
        (UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v (D.train n).ψ) τ y :=
      ((D.level n).params D.Pl).raw_eq_off_axis τ y hy
    rw [e, norm_Nv _ _ _ hy]
    set s := age (D.level n).ε⁻¹ y
    set z := (chart (D.level n).ε⁻¹ τ y).2 with hz
    have hchart : (chart (D.level n).ε⁻¹ τ y) = (s, z) := rfl
    rw [hchart]
    have hp : ‖UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v (D.train n).ψ (s, z)‖
        ≤ ‖(D.train n).v s z‖ + (D.level n).ε *
          |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s z.1 z.2| := by
      unfold UnforcedLeray.Cons.C03.rawProfile
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, PiLp.norm_single, norm_one, Real.norm_eq_abs, mul_one, abs_mul,
        abs_of_pos hε]
    have h1 := hA s hs z
    have h2 := hB s z.1 z.2 hs
    have hk1 : a ^ k1 ≤ a ^ (max k1 k2) := pow_le_pow_right₀ ha (le_max_left _ _)
    have hk2 : a ^ k2 ≤ a ^ (max k1 k2) := pow_le_pow_right₀ ha (le_max_right _ _)
    have hsq := Real.sqrt_nonneg s
    calc Real.sqrt s * ‖UnforcedLeray.Cons.C03.rawProfile (D.level n).ε (D.train n).v
            (D.train n).ψ (s, z)‖
        ≤ Real.sqrt s * (‖(D.train n).v s z‖ + (D.level n).ε *
          |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s z.1 z.2|) :=
          mul_le_mul_of_nonneg_left hp hsq
      _ = Real.sqrt s * ‖(D.train n).v s z‖ + Real.sqrt s * ((D.level n).ε *
          |UnforcedLeray.Cons.C03.raisedStream (D.train n).ψ s z.1 z.2|) := by ring
      _ ≤ C1 * a ^ k1 + C2 * a ^ k2 := add_le_add h1 h2
      _ ≤ |C1| * a ^ k1 + |C2| * a ^ k2 :=
          add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
            (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      _ ≤ |C1| * a ^ (max k1 k2) + |C2| * a ^ (max k1 k2) :=
          add_le_add (mul_le_mul_of_nonneg_left hk1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hk2 (abs_nonneg _))
      _ = (|C1| + |C2|) * a ^ (max k1 k2) := by ring
  by_cases hy : y ∈ axis
  · -- axis: limit of off-axis values along `y + (m+1)⁻¹ e₀`
    have hlim := hax τ y hy
    exact le_of_tendsto hlim.norm
      (Eventually.of_forall fun m => hoff _ (AxisEvOrg.shift_not_mem_axis y hy m))
  · exact hoff y hy

end UnforcedLeray.Short.PartIIIb.Concrete
