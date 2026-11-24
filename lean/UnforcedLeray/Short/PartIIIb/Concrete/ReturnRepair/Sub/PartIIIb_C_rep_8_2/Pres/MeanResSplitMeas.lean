import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.PresCoef
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasDefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasWard
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6.AxisEv
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth

/-!
# Split measurability of the mean residual (`PartIII-b:C/rep/8/2/pres/4/org2/5`)

Source `the November 2 reference manuscript`
lines 1205-1225, 4139-4141, 5272-5289.

Proves `meanResSplitMeas`: the two parts of the coefficient/pressure change of the mean Ward
residual (`(U, p) → (V, p_lift)` and `(V, p_lift) → (U_raw, p_lift)`) are `AEStronglyMeasurable`
with respect to `srcMeasure (cOf ν)` eventually along the sequence. Mirrors `meanResMeasAt_of`
and `wardDiffMeasAt_of_parts`, using the split `V = U_raw + Σ_i coord z i • inlet i` on an actual
level.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Measurability of `coefOf ε⁻¹` of the difference of two `meanWard` evaluations from joint
measurability and off-axis `C²` regularity of their coefficient/pressure pairs. -/
theorem meanWardDiff_aestronglyMeasurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (μ : ℝ) (T : LStr Pl K L) {U₁ U₂ : ℝ → SpatialField} {p₁ p₂ : ℝ → Space → ℝ}
    (hU1m : Measurable fun q : ℝ × Space => U₁ q.1 q.2)
    (hU1d : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (U₁ τ) y)
    (hp1m : Measurable fun q : ℝ × Space => p₁ q.1 q.2)
    (hp1d : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (p₁ τ) y)
    (hU2m : Measurable fun q : ℝ × Space => U₂ q.1 q.2)
    (hU2d : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (U₂ τ) y)
    (hp2m : Measurable fun q : ℝ × Space => p₂ q.1 q.2)
    (hp2d : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (p₂ τ) y) :
    AEStronglyMeasurable (coefOf L.ε⁻¹ (fun τ y =>
      meanWard Pl K L μ T U₁ p₁ τ y - meanWard Pl K L μ T U₂ p₂ τ y))
      (srcMeasure (cOf L.ν)) := by
  have hR : L.ε⁻¹ ≠ 0 := (inv_pos.2 L.ε_pos).ne'
  rw [coefOf_axis_zero L.ε⁻¹ hR]
  have hS : MeasurableSet {x : ℝ × Space | x.2 ∈ axis} :=
    isClosed_axis.measurableSet.preimage measurable_snd
  have hA := wardEXY_meas L.ν μ L.ε⁻¹
    (fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
    (fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) hU1m hU1d hp1m hp1d
  have hB := wardEXY_meas L.ν μ L.ε⁻¹
    (fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
    (fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) hU2m hU2d hp2m hp2d
  have h0 : Measurable fun _ : ℝ × Space => (0 : Space) := measurable_const
  have hG : Measurable fun x : ℝ × Space =>
      if x.2 ∈ axis then (0 : Space) else
        ((if x.2 ∈ axis then (0 : Space) else
            wardEXY L.ν μ L.ε⁻¹ U₁ p₁
              (fun _ => fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
              (fun _ => fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) x.1 x.2)
          - (if x.2 ∈ axis then (0 : Space) else
            wardEXY L.ν μ L.ε⁻¹ U₂ p₂
              (fun _ => fun y => Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y)
              (fun _ => fun y => Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) 0 y) x.1 x.2)) :=
    Measurable.ite hS h0 (hA.sub hB)
  have hMeas : Measurable fun x : ℝ × Space =>
      if x.2 ∈ axis then (0 : Space) else
        (meanWard Pl K L μ T U₁ p₁ x.1 x.2 - meanWard Pl K L μ T U₂ p₂ x.1 x.2) := by
    convert hG using 1
    funext x
    by_cases hx : x.2 ∈ axis
    · simp [hx]
    · simp only [hx, ↓reduceIte]
      rfl
  exact (vyh_measurable_coefOf L.ε⁻¹ hMeas).aestronglyMeasurable

/-- Single-level reduction of `MeanResSplitMeasAt` from the exact profile, `RawLiftRegularAt`, and
joint measurability / off-axis `C²` regularity of `L.V`. -/
theorem meanResSplitMeasAt_of_parts (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (μ P : ℝ) (hE : IsExactProfile L.ν P L.U L.pres) (hR : RawLiftRegularAt Pl L)
    (hVm : Measurable fun q : ℝ × Space => L.V q.1 q.2)
    (hVd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (L.V τ) y) :
    MeanResSplitMeasAt Pl K L μ := by
  intro T
  have hUs : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (L.U τ) := fun τ =>
    hE.smoothU.comp (contDiff_const.prodMk contDiff_id)
  have hPs : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (L.pres τ) := fun τ =>
    hE.smoothP.comp (contDiff_const.prodMk contDiff_id)
  have hUd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (L.U τ) y := fun τ y _ =>
    ((hUs τ).contDiffAt).of_le (WithTop.coe_le_coe.2 le_top)
  have hPd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (L.pres τ) y := fun τ y _ =>
    ((hPs τ).contDiffAt).of_le (WithTop.coe_le_coe.2 le_top)
  have hUm : Measurable fun q : ℝ × Space => L.U q.1 q.2 := hE.smoothU.continuous.measurable
  have hPm : Measurable fun q : ℝ × Space => L.pres q.1 q.2 := hE.smoothP.continuous.measurable
  have hRd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (rawU Pl L τ) y :=
    fun τ y hy => (hR.2.2.1 τ y hy).1
  have hLd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (liftP L τ) y :=
    fun τ y hy => (hR.2.2.1 τ y hy).2
  exact ⟨meanWardDiff_aestronglyMeasurable Pl K L μ T hUm hUd hPm hPd hVm hVd hR.2.1 hLd,
    meanWardDiff_aestronglyMeasurable Pl K L μ T hVm hVd hR.2.1 hLd hR.1 hRd hR.2.1 hLd⟩

/-- Joint measurability and off-axis `C²` regularity of `V = rawF + Σ_i c i • inletF i`. -/
theorem v_meas_and_contDiffAt {V rawF : ℝ → Space → Space} {inletF : Fin 2 → ℝ → Space → Space}
    {c : Fin 2 → ℝ}
    (hV : ∀ τ y, V τ y = rawF τ y + ∑ i : Fin 2, c i • inletF i τ y)
    (hRm : Measurable fun q : ℝ × Space => rawF q.1 q.2)
    (hRd : ∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (rawF τ) y)
    (hIn : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × Space => inletF i x.1 x.2)) :
    (Measurable fun q : ℝ × Space => V q.1 q.2) ∧
      (∀ (τ : ℝ) (y : Space), y ∉ axis → ContDiffAt ℝ 2 (V τ) y) := by
  refine ⟨?_, ?_⟩
  · have he : (fun q : ℝ × Space => V q.1 q.2) =
        fun q : ℝ × Space => rawF q.1 q.2 + ∑ i : Fin 2, c i • inletF i q.1 q.2 := by
      funext q
      exact hV q.1 q.2
    rw [he]
    refine hRm.add (Finset.measurable_sum _ fun i _ => ?_)
    exact ((hIn i).continuous.measurable).const_smul (c i)
  · intro τ y hy
    have he : V τ = fun y' : Space => rawF τ y' + ∑ i : Fin 2, c i • inletF i τ y' := by
      funext y'
      exact hV τ y'
    rw [he]
    refine (hRd τ y hy).add (ContDiffAt.sum fun i _ => ?_)
    have hiτ : ContDiff ℝ ∞ (inletF i τ) :=
      (hIn i).comp (contDiff_const.prodMk contDiff_id)
    exact ((hiτ.contDiffAt).of_le (WithTop.coe_le_coe.2 le_top)).const_smul (c i)

/-- **Split measurability of the mean residual along the sequence**
(`PartIII-b:C/rep/8/2/pres/4/org2/5`, source 1205-1225, 4139-4141, 5272-5289). -/
theorem meanResSplitMeas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.MeanResSplitMeas := by
  obtain ⟨ν₀, hν₀, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue D.Pl.mode
    D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  have hInlet : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 2,
      ContDiff ℝ ∞ (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) := by
    filter_upwards [hst.actual, hν] with n hn hνn
    exact fun i => hS ((D.level n).params D.Pl) _ hn.regime hνn.le rfl rfl i
  filter_upwards [hst.actual, axisEv D hst, hInlet] with n hn hax hi z _
  have hR : RawLiftRegularAt D.Pl (D.level n) :=
    rawLiftRegularAt D.Pl (D.level n) hn.buc (hax hn)
  obtain ⟨zc, -, hVz, -, -⟩ := hn.split.state
  obtain ⟨hVm, hVd⟩ := v_meas_and_contDiffAt hVz hR.1 (fun τ y hy => (hR.2.2.1 τ y hy).1) hi
  exact meanResSplitMeasAt_of_parts D.Pl D.K (D.level n) (D.mu n z) _ hn.profile hR hVm hVd

end UnforcedLeray.Short.PartIIIb.Concrete
