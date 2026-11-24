import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.TransInv
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski

/-!
# Part II-b, task `PartII-b:T13/1/4/3/1/3` (`chmYoungCyl`): Young inequality in `L^r(cylMeas c)`

Source: `the November 2 reference manuscript` (SP) lines 1933-1935.

Proof. `chmConv K u` does not change when `u` is modified on a Lebesgue null set, so we may
replace `u` by a measurable a.e. `q`-periodic representative `v`.  Minkowski's integral inequality
for `μ = cylMeas c`, `ν = volume` gives
`‖chmConv K v‖_{L^r(cylMeas c)} ≤ ∫ ‖K y‖ ‖v(· - y)‖_{L^r(cylMeas c)} dy`.  The translation
`‖v(· - y)‖_{L^r(cylMeas c)} = ‖v‖_{L^r(cylMeas c)}` is `chmCylTransInv` applied to `‖v‖ₑ ^ r`.
Finally `∫ ‖K y‖ dy = eLpNorm K 1 volume`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal

/-- `cylMeas c` is absolutely continuous with respect to Lebesgue measure on `Coord`. -/
theorem chmY_cyl_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  intro s hs
  rw [chmTI_cyl_eq c, Measure.smul_apply, smul_eq_mul]
  have h1 : (volume : Measure Coord).restrict {x : Coord | x.2.1 ∈ Ico (-c / 2) (c / 2)} s ≤
      volume s := Measure.restrict_apply_le _ _
  rw [hs] at h1
  rw [le_antisymm h1 zero_le, mul_zero]

/-- An a.e. equal modification of a `q`-periodic function is a.e. `q`-periodic. -/
theorem chmY_per {c : ℝ} {u v : Coord → ℂ} (hup : QPeriodicS c u) (hvu : u =ᵐ[volume] v) :
    ∀ᵐ x : Coord, v (qShift c x) = v x := by
  have hT := (measurePreserving_add_right (volume : Measure Coord)
    ((0 : ℝ), ((c : ℝ), (0 : ℝ)))).quasiMeasurePreserving
  have h1 : ∀ᵐ x : Coord, u (x + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) =
      v (x + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
    hT.ae (p := fun y => u y = v y) hvu
  filter_upwards [h1, hup, hvu] with x h1x hupx hvux
  have hq : x + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = qShift c x :=
    Prod.ext (by simp [qShift]) (Prod.ext (by simp [qShift]) (by simp [qShift]))
  rw [hq] at h1x
  rw [← h1x, hupx, hvux]

/-- The difference map `(x, y) ↦ x - y` is quasi measure preserving from `μ.prod volume`. -/
theorem chmY_sub_qmp (μ : Measure Coord) :
    Measure.QuasiMeasurePreserving (fun p : Coord × Coord => p.1 - p.2) (μ.prod volume) volume := by
  have hm : Measurable (fun p : Coord × Coord => p.1 - p.2) := measurable_fst.sub measurable_snd
  refine ⟨hm, ?_⟩
  intro N hN
  have hM : (volume : Measure Coord) (toMeasurable volume N) = 0 := by
    rw [measure_toMeasurable]; exact hN
  have hMm : MeasurableSet (toMeasurable volume N) := measurableSet_toMeasurable _ _
  refine le_antisymm ?_ zero_le
  calc Measure.map (fun p : Coord × Coord => p.1 - p.2) (μ.prod volume) N
      ≤ Measure.map (fun p : Coord × Coord => p.1 - p.2) (μ.prod volume)
          (toMeasurable volume N) := measure_mono (subset_toMeasurable _ _)
    _ = (μ.prod volume) ((fun p : Coord × Coord => p.1 - p.2) ⁻¹' toMeasurable volume N) :=
        Measure.map_apply hm hMm
    _ = 0 := by
        rw [Measure.prod_apply (hm hMm)]
        have hz : ∀ x : Coord,
            (volume : Measure Coord) (Prod.mk x ⁻¹' ((fun p : Coord × Coord => p.1 - p.2) ⁻¹'
              toMeasurable volume N)) = 0 := by
          intro x
          have h2 : Prod.mk x ⁻¹' ((fun p : Coord × Coord => p.1 - p.2) ⁻¹'
              toMeasurable volume N) = (fun y : Coord => x - y) ⁻¹' toMeasurable volume N := rfl
          rw [h2, (Measure.measurePreserving_sub_left (volume : Measure Coord) x).measure_preimage
            hMm.nullMeasurableSet, hM]
        simp only [hz, lintegral_zero]

/-- A finite nonzero multiple of a sigma-finite measure is sigma-finite. -/
theorem chmY_sf_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  rw [sigmaFinite_iff]
  exact ⟨{ set := spanningSets μ
           set_mem := fun _ => mem_univ _
           finite := fun i => by
             rw [Measure.smul_apply, smul_eq_mul]
             exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) (measure_spanningSets_lt_top μ i)
           spanning := iUnion_spanningSets μ }⟩

/-- **Leaf `PartII-b:T13/1/4/3/1/3`.** Young inequality for a `q`-periodic function in
`L^r(cylMeas c)` and an integrable kernel on `Coord` (SP 1933-1935). -/
theorem chmYoungCyl : UnforcedLeray.Short.IIb.ChmYoungCyl := by
  intro c hc r hr K u hK hup hum hun
  obtain ⟨v, hvs, hvu⟩ := hum
  have hv : Measurable v := hvs.measurable
  have hvper : ∀ᵐ x : Coord, v (qShift c x) = v x := chmY_per hup hvu
  have hr0 : (0 : ℝ) < r := by linarith
  have hpos : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  -- `chmConv K` does not see values of `u` off a null set.
  have hconv : chmConv K u = chmConv K v := by
    funext x
    unfold chmConv
    apply integral_congr_ae
    have h1 : ∀ᵐ y : Coord, u (x - y) = v (x - y) :=
      (Measure.measurePreserving_sub_left (volume : Measure Coord) x).quasiMeasurePreserving.ae
        (p := fun z => u z = v z) hvu
    filter_upwards [h1] with y hy
    rw [hy]
  have hcylUV : cylNorm c r u = cylNorm c r v := eLpNorm_congr_ae ((chmY_cyl_ac c).ae_eq hvu)
  have hfin : cylNorm c r v < ⊤ := by
    rw [← hcylUV]
    exact hun
  rw [hconv, hcylUV]
  -- translation invariance of the `L^r(cylMeas c)` norm of `v`
  have hGmeas : Measurable (fun x : Coord => ‖v x‖ₑ ^ r) := hv.enorm.pow_const r
  have hGper : ∀ᵐ x : Coord, (fun x : Coord => ‖v x‖ₑ ^ r) (qShift c x)
      = (fun x : Coord => ‖v x‖ₑ ^ r) x :=
    hvper.mono fun x hx => by simp only [hx]
  have hTI : ∀ c : ℝ, 0 < c → ∀ G : Coord → ℝ≥0∞, Measurable G →
      (∀ᵐ x : Coord, G (qShift c x) = G x) →
      ∀ y : Coord, ∫⁻ x, G (x - y) ∂(cylMeas c) = ∫⁻ x, G x ∂(cylMeas c) := chmCylTransInv
  have hshift : ∀ y : Coord, eLpNorm (fun x => v (x - y)) (ENNReal.ofReal r) (cylMeas c)
      = eLpNorm v (ENNReal.ofReal r) (cylMeas c) := by
    intro y
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hpos hpt, ENNReal.toReal_ofReal hr0.le]
    congr 1
    exact hTI c hc (fun x => ‖v x‖ₑ ^ r) hGmeas hGper y
  -- Minkowski's integral inequality
  have hF : AEStronglyMeasurable (Function.uncurry fun (x y : Coord) => ((K y : ℝ) : ℂ) * v (x - y))
      ((cylMeas c).prod (volume : Measure Coord)) := by
    have hKa : AEStronglyMeasurable (fun p : Coord × Coord => K p.2)
        ((cylMeas c).prod (volume : Measure Coord)) :=
      hK.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h1 : AEStronglyMeasurable (fun p : Coord × Coord => ((K p.2 : ℝ) : ℂ))
        ((cylMeas c).prod (volume : Measure Coord)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hKa
    have h2 : AEStronglyMeasurable (fun p : Coord × Coord => v (p.1 - p.2))
        ((cylMeas c).prod (volume : Measure Coord)) :=
      hv.aestronglyMeasurable.comp_quasiMeasurePreserving (chmY_sub_qmp (cylMeas c))
    exact h1.mul h2
  have hσ : SigmaFinite (cylMeas c) := by
    rw [chmTI_cyl_eq c]
    exact chmY_sf_smul _ _ ENNReal.ofReal_ne_top
  have hmink := UnforcedLeray.PlanarBS.Conv.eLpNorm_integral_le
    (μ := cylMeas c) (ν := (volume : Measure Coord))
    (F := fun (x y : Coord) => ((K y : ℝ) : ℂ) * v (x - y)) hF
    (ENNReal.one_le_ofReal.2 hr.le) hpt
  have hn : ∀ y : Coord, ‖((K y : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |K y| := fun y => by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  have hpt2 : ∀ y : Coord, eLpNorm (fun x => ((K y : ℝ) : ℂ) * v (x - y)) (ENNReal.ofReal r)
      (cylMeas c) = ENNReal.ofReal |K y| * eLpNorm v (ENNReal.ofReal r) (cylMeas c) := by
    intro y
    rw [← hn y, ← hshift y]
    exact eLpNorm_const_smul ((K y : ℝ) : ℂ) (fun x => v (x - y)) (ENNReal.ofReal r) (cylMeas c)
  calc cylNorm c r (chmConv K v)
      = eLpNorm (chmConv K v) (ENNReal.ofReal r) (cylMeas c) := rfl
    _ ≤ ∫⁻ y, eLpNorm (fun x => ((K y : ℝ) : ℂ) * v (x - y)) (ENNReal.ofReal r) (cylMeas c)
          ∂(volume : Measure Coord) := hmink
    _ = ∫⁻ y, ENNReal.ofReal |K y| * eLpNorm v (ENNReal.ofReal r) (cylMeas c)
          ∂(volume : Measure Coord) := lintegral_congr fun y => hpt2 y
    _ = (∫⁻ y, ENNReal.ofReal |K y| ∂(volume : Measure Coord)) *
          eLpNorm v (ENNReal.ofReal r) (cylMeas c) :=
        lintegral_mul_const' _ _ hfin.ne
    _ = eLpNorm K 1 volume * cylNorm c r v := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        simp only [Real.enorm_eq_ofReal_abs]

end UnforcedLeray.Short.IIb

end
