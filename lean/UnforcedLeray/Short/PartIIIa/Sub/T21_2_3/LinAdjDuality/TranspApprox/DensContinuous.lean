import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1_1_1
import UnforcedLeray.Units.B0579
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support

/-!
# `PartIII-a:T21/2/3/1/9/1/1/1`: `ladDensContinuous` (`LadDensContinuous`)

Source `the November 2 reference manuscript` lines 3230-3240.

Proof: for `w ∈ L²(cellMeasure c m)` and `ε > 0`,
1. the tail `|η| ≥ ...` near the seams `q = ±c/2` has small `L²` mass (dominated convergence);
2. the truncated function `w₁ = 1_{|q| < c/2 - δ} w` is approximated in `L²(cellMeasure)` by a
   compactly supported continuous `g` (Mathlib density, `μ` locally finite on a proper space);
3. `h = g · χ_δ(q)` with a transverse cutoff `χ_δ` vanishing for `|q| ≥ c/2 - δ/2` keeps the error;
4. `G(q, η) = h(toIcoMod (-c/2) q, η)` is `c`-periodic, continuous (it vanishes near the seams) and
   agrees with `h` on the cell.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace LadDensContAux

/-- The cellMeasure, as a measure on the plane. -/
abbrev CM (c m : ℝ) : Measure (ℝ × ℝ) := UnforcedLeray.B0579.cellMeasure c m

/-- Transverse seam cutoff: `1` on `|q| ≤ c/2 - δ`, `0` on `|q| ≥ c/2 - δ/2`. -/
def seamCut (c δ : ℝ) (x : ℝ × ℝ) : ℝ := min 1 (max 0 (2 * (c / 2 - δ / 2 - |x.1|) / δ))

lemma continuous_seamCut (c δ : ℝ) : Continuous (seamCut c δ) := by
  unfold seamCut
  fun_prop

lemma seamCut_nonneg (c δ : ℝ) (x : ℝ × ℝ) : 0 ≤ seamCut c δ x :=
  le_min zero_le_one (le_max_left _ _)

lemma seamCut_le_one (c δ : ℝ) (x : ℝ × ℝ) : seamCut c δ x ≤ 1 :=
  min_le_left _ _

lemma seamCut_eq_zero {c δ : ℝ} (hδ : 0 < δ) {x : ℝ × ℝ} (hx : c / 2 - δ / 2 ≤ |x.1|) :
    seamCut c δ x = 0 := by
  have hq : 2 * (c / 2 - δ / 2 - |x.1|) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  unfold seamCut
  rw [max_eq_left hq, min_eq_right zero_le_one]

lemma seamCut_eq_one {c δ : ℝ} (hδ : 0 < δ) {x : ℝ × ℝ} (hx : |x.1| ≤ c / 2 - δ) :
    seamCut c δ x = 1 := by
  have hq : 1 ≤ 2 * (c / 2 - δ / 2 - |x.1|) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  unfold seamCut
  rw [min_eq_left (le_max_of_le_right hq)]

/-- The tail set `|q| ≥ c/2 - δ`. -/
def tailSet (c δ : ℝ) : Set (ℝ × ℝ) := {x | c / 2 - δ ≤ |x.1|}

lemma measurableSet_tailSet (c δ : ℝ) : MeasurableSet (tailSet c δ) :=
  (isClosed_le continuous_const (continuous_abs.comp continuous_fst)).measurableSet

lemma ae_cell (c m : ℝ) :
    ∀ᵐ x ∂(CM c m), x ∈ UnforcedLeray.B0579.cell c := by
  have h1 : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      x ∈ UnforcedLeray.B0579.cell c :=
    ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)
  have h2 := ae_iff.1 h1
  exact ae_iff.2 (UnforcedLeray.B0579.cellMeasure_ac c m h2)

lemma cellMeasure_line_null (c m a : ℝ) : CM c m {x : ℝ × ℝ | x.1 = a} = 0 := by
  have hS : volume {x : ℝ × ℝ | x.1 = a} = 0 := by
    have e : {x : ℝ × ℝ | x.1 = a} = ({a} : Set ℝ) ×ˢ (univ : Set ℝ) := by
      ext x
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  refine (UnforcedLeray.B0579.cellMeasure_ac c m) ?_
  rw [Measure.restrict_apply' (UnforcedLeray.B0579.measurableSet_cell c)]
  exact measure_mono_null inter_subset_left hS

/-- Absolute continuity of the tail of an `L²` function. -/
lemma tendsto_tail {c : ℝ} (hc : 0 < c) (m : ℝ) {w : ℝ × ℝ → ℂ} (hwm : Measurable w)
    (hw : MemLp w 2 (CM c m)) :
    Tendsto (fun δ : ℝ => eLpNorm ((tailSet c δ).indicator w) 2 (CM c m)) (𝓝[>] 0) (𝓝 0) := by
  have hL : Tendsto (fun δ : ℝ => ∫⁻ x, ‖(tailSet c δ).indicator w x‖ₑ ^ (2 : ℝ) ∂(CM c m))
      (𝓝[>] 0) (𝓝 0) := by
    have hb : ∫⁻ x, ‖w x‖ₑ ^ (2 : ℝ) ∂(CM c m) ≠ ⊤ := by
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := CM c m) (p := 2)
        (by norm_num) (by norm_num)).1 hw.eLpNorm_lt_top
      simpa using this.ne
    have hmain := tendsto_lintegral_filter_of_dominated_convergence (μ := CM c m)
      (l := 𝓝[>] (0 : ℝ))
      (F := fun δ x => ‖(tailSet c δ).indicator w x‖ₑ ^ (2 : ℝ))
      (f := fun _ => (0 : ℝ≥0∞))
      (fun x => ‖w x‖ₑ ^ (2 : ℝ))
      (Eventually.of_forall fun δ => (hwm.indicator (measurableSet_tailSet c δ)).enorm.pow_const _)
      (Eventually.of_forall fun δ => Eventually.of_forall fun x => by
        by_cases hx : x ∈ tailSet c δ
        · simp [Set.indicator_apply, hx]
        · simp [Set.indicator_apply, hx])
      hb
      (by
        have hline : ∀ᵐ x ∂(CM c m), x.1 ≠ -(c / 2) := by
          rw [ae_iff]
          simpa using cellMeasure_line_null c m (-(c / 2))
        filter_upwards [ae_cell c m, hline] with x hx1 hx2
        have hx1' := hx1
        simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_univ, and_true,
          Set.mem_Ico] at hx1'
        have hlo : -(c / 2) < x.1 := lt_of_le_of_ne hx1'.1 (fun h => hx2 h.symm)
        have hlt : |x.1| < c / 2 := abs_lt.2 ⟨by linarith, hx1'.2⟩
        apply tendsto_const_nhds.congr'
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < c / 2 - |x.1| by linarith))]
          with δ hδ
        have hδ' : δ < c / 2 - |x.1| := hδ
        have hxn : x ∉ tailSet c δ := by
          intro hmem
          have hmem' : c / 2 - δ ≤ |x.1| := hmem
          linarith
        simp [Set.indicator_apply, hxn])
    rw [lintegral_zero] at hmain
    exact hmain
  have key : ∀ δ : ℝ, eLpNorm ((tailSet c δ).indicator w) 2 (CM c m)
      = (∫⁻ x, ‖(tailSet c δ).indicator w x‖ₑ ^ (2 : ℝ) ∂(CM c m)) ^ (1 / (2 : ℝ)) := by
    intro δ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have hfun : (fun δ : ℝ => eLpNorm ((tailSet c δ).indicator w) 2 (CM c m))
      = fun δ : ℝ => (∫⁻ x, ‖(tailSet c δ).indicator w x‖ₑ ^ (2 : ℝ) ∂(CM c m)) ^ (1 / (2 : ℝ)) :=
    funext key
  rw [hfun]
  have hcont := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hL
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hcont
  exact hcont

/-- Near a seam point `q = -c/2 + k c`, the periodized coordinate lies in the seam region. -/
lemma abs_toIcoMod_near {c δ : ℝ} (hc : 0 < c) (hδc : δ < c) (hδ : 0 < δ) (k : ℤ) (y : ℝ)
    (hy : |y - (-(c / 2) + k * c)| < δ / 2) :
    c / 2 - δ / 2 ≤ |toIcoMod hc (-(c / 2)) y| := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 hy
  have hy' : y = (-(c / 2) + (y - (-(c / 2) + k * c))) + k • c := by
    rw [zsmul_eq_mul]
    ring
  rw [hy', toIcoMod_add_zsmul]
  rcases le_or_gt 0 (y - (-(c / 2) + k * c)) with h0 | h0
  · have hT : toIcoMod hc (-(c / 2)) (-(c / 2) + (y - (-(c / 2) + k * c)))
        = -(c / 2) + (y - (-(c / 2) + k * c)) :=
      (toIcoMod_eq_self hc).2 ⟨by linarith, by linarith⟩
    rw [hT]
    exact le_trans (by linarith) (neg_le_abs _)
  · have hT : toIcoMod hc (-(c / 2)) (-(c / 2) + (y - (-(c / 2) + k * c)))
        = -(c / 2) + (y - (-(c / 2) + k * c)) + c := by
      refine (toIcoMod_eq_iff hc).2 ⟨⟨by linarith, by linarith⟩, -1, ?_⟩
      simp only [neg_smul, one_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [hT]
    exact le_trans (by linarith) (le_abs_self _)

/-- Periodic extension of a continuous band function vanishing near the seams. -/
lemma continuous_periodize {c δ : ℝ} (hc : 0 < c) (hδc : δ < c) (hδ : 0 < δ)
    {h : ℝ × ℝ → ℂ} (hh : Continuous h)
    (hvan : ∀ y : ℝ × ℝ, c / 2 - δ / 2 ≤ |y.1| → h y = 0) :
    Continuous (fun x : ℝ × ℝ => h (toIcoMod hc (-(c / 2)) x.1, x.2)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hk : ∃ k : ℤ, x.1 = -(c / 2) + k * c
  · obtain ⟨k, hk⟩ := hk
    have hev : ∀ᶠ x' in 𝓝 x, |x'.1 - x.1| < δ / 2 := by
      have hcont : Continuous (fun x' : ℝ × ℝ => |x'.1 - x.1|) := by fun_prop
      exact hcont.continuousAt.eventually_lt continuousAt_const
        (by simp only [sub_self, abs_zero]; linarith)
    have hG : (fun x' : ℝ × ℝ => h (toIcoMod hc (-(c / 2)) x'.1, x'.2)) =ᶠ[𝓝 x]
        fun _ => (0 : ℂ) := by
      filter_upwards [hev] with x' hx'
      apply hvan
      exact abs_toIcoMod_near hc hδc hδ k x'.1 (by rw [← hk]; exact hx')
    exact (continuousAt_congr hG).2 continuousAt_const
  · have hx : ¬ x.1 ≡ -(c / 2) [PMOD c] := by
      intro hm
      obtain ⟨z, hz⟩ := (AddCommGroup.modEq_iff_eq_add_zsmul).1 hm
      apply hk
      refine ⟨-z, ?_⟩
      rw [zsmul_eq_mul] at hz
      push_cast
      linarith
    have hT : ContinuousAt (fun x' : ℝ × ℝ => toIcoMod hc (-(c / 2)) x'.1) x :=
      (continuousAt_toIcoMod hc (-(c / 2)) hx).comp continuousAt_fst
    have hcomp : ContinuousAt (fun x' : ℝ × ℝ => (toIcoMod hc (-(c / 2)) x'.1, x'.2)) x :=
      hT.prodMk continuousAt_snd
    exact hh.continuousAt.comp hcomp

end LadDensContAux

open LadDensContAux in
theorem ladDensContinuous : UnforcedLeray.Short.IIIa.LadDensContinuous := by
  intro c m hc w0 hw0 ε hε
  have hc0 : 0 < c := hc
  have hloc : IsLocallyFiniteMeasure (CM c m) :=
    IsLocallyFiniteMeasure.withDensity_coe (UnforcedLeray.B0579.continuous_density m)
  have := hloc
  have : (CM c m).Regular := inferInstance
  have hwae : w0 =ᵐ[CM c m] hw0.1.mk w0 := hw0.1.ae_eq_mk
  set w := hw0.1.mk w0 with hwdef
  have hwsm : StronglyMeasurable w := hw0.1.stronglyMeasurable_mk
  have hw : MemLp w 2 (CM c m) := hw0.ae_eq hwae
  have hwm : Measurable w := hwsm.measurable
  -- choose the tail width
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by linarith)
  have hT := tendsto_tail hc0 m hwm hw
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      eLpNorm ((tailSet c δ).indicator w) 2 (CM c m) < ENNReal.ofReal (ε / 2) :=
    hT.eventually (gt_mem_nhds hpos)
  have hevc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < c / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
  have hevp : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hA, hδc2, hδpos⟩ := (hev.and (hevc.and hevp)).exists
  have hδc : δ < c := by linarith
  -- truncated function and its approximant
  have hw1 : MemLp ((tailSet c δ)ᶜ.indicator w) 2 (CM c m) :=
    hw.indicator (measurableSet_tailSet c δ).compl
  obtain ⟨g, hgc, hgn, hgcont, -⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num) hw1
      (ENNReal.ofReal_pos.2 (by linarith : (0 : ℝ) < ε / 2)).ne'
  -- cutoff
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ × ℝ → ℂ, ∀ x, h x = g x * ((seamCut c δ x : ℝ) : ℂ) :=
    ⟨fun x => g x * ((seamCut c δ x : ℝ) : ℂ), fun x => rfl⟩
  have hhc : Continuous h := by
    have : h = fun x => g x * ((seamCut c δ x : ℝ) : ℂ) := funext hh_def
    rw [this]
    exact hgcont.mul (Complex.continuous_ofReal.comp (continuous_seamCut c δ))
  have hhvan : ∀ y : ℝ × ℝ, c / 2 - δ / 2 ≤ |y.1| → h y = 0 := by
    intro y hy
    rw [hh_def, seamCut_eq_zero hδpos hy]
    simp
  -- periodic extension
  obtain ⟨G, hG_def⟩ : ∃ G : ℝ × ℝ → ℂ, ∀ x, G x = h (toIcoMod hc0 (-(c / 2)) x.1, x.2) :=
    ⟨fun x => h (toIcoMod hc0 (-(c / 2)) x.1, x.2), fun x => rfl⟩
  have hGc : Continuous G := by
    have : G = fun x : ℝ × ℝ => h (toIcoMod hc0 (-(c / 2)) x.1, x.2) := funext hG_def
    rw [this]
    exact continuous_periodize hc0 hδc hδpos hhc hhvan
  have hGp : ∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x := by
    intro x
    rw [hG_def, hG_def, toIcoMod_add_right]
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  have hgR : ∀ y : ℝ × ℝ, R < |y.2| → g y = 0 := by
    intro y hy
    by_contra hne
    have hmem : y ∈ tsupport g := subset_tsupport g (Function.mem_support.2 hne)
    have h1 := hR hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 := norm_snd_le y
    rw [Real.norm_eq_abs] at h2
    linarith
  have hGR : ∀ x : ℝ × ℝ, R < |x.2| → G x = 0 := by
    intro x hx
    rw [hG_def, hh_def, hgR (toIcoMod hc0 (-(c / 2)) x.1, x.2) (by simpa using hx), zero_mul]
  -- on the cell, `G = h`
  have hGh : ∀ x ∈ UnforcedLeray.B0579.cell c, G x = h x := by
    intro x hx
    have hx1 := hx
    simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_univ, and_true,
      Set.mem_Ico] at hx1
    have hT : toIcoMod hc0 (-(c / 2)) x.1 = x.1 :=
      (toIcoMod_eq_self hc0).2 ⟨hx1.1, by linarith [hx1.2]⟩
    rw [hG_def, hT]
  -- pointwise identity
  have hid : ∀ x : ℝ × ℝ, w x - h x = (tailSet c δ).indicator w x
      + ((tailSet c δ)ᶜ.indicator w x - g x) * ((seamCut c δ x : ℝ) : ℂ) := by
    intro x
    rw [hh_def]
    by_cases hx : x ∈ tailSet c δ
    · have hn : x ∉ (tailSet c δ)ᶜ := fun h' => h' hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hn]
      ring
    · have hx' : |x.1| ≤ c / 2 - δ := by
        have hn : ¬ (c / 2 - δ ≤ |x.1|) := hx
        exact le_of_lt (not_le.1 hn)
      rw [seamCut_eq_one hδpos hx']
      simp [Set.indicator_apply, hx]
  -- the bound on the cell
  have hm1 : AEStronglyMeasurable ((tailSet c δ).indicator w) (CM c m) :=
    (hwm.indicator (measurableSet_tailSet c δ)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable
      (fun x => ((tailSet c δ)ᶜ.indicator w x - g x) * ((seamCut c δ x : ℝ) : ℂ)) (CM c m) :=
    (hw1.1.sub hgcont.aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp (continuous_seamCut c δ)).aestronglyMeasurable
  have hmono : eLpNorm (fun x => ((tailSet c δ)ᶜ.indicator w x - g x) * ((seamCut c δ x : ℝ) : ℂ))
      2 (CM c m) ≤ eLpNorm (fun x => (tailSet c δ)ᶜ.indicator w x - g x) 2 (CM c m) := by
    apply eLpNorm_mono
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (seamCut_nonneg c δ x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (seamCut_le_one c δ x)
  have hX : eLpNorm (fun x => ((tailSet c δ)ᶜ.indicator w x - g x) * ((seamCut c δ x : ℝ) : ℂ))
      2 (CM c m) ≤ ENNReal.ofReal (ε / 2) := hmono.trans hgn
  have hXne : eLpNorm (fun x => ((tailSet c δ)ᶜ.indicator w x - g x) * ((seamCut c δ x : ℝ) : ℂ))
      2 (CM c m) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hX
  have hbound : eLpNorm (fun x => w x - h x) 2 (CM c m) < ENNReal.ofReal ε := by
    have e1 : (fun x => w x - h x) = fun x => (tailSet c δ).indicator w x
        + ((tailSet c δ)ᶜ.indicator w x - g x) * ((seamCut c δ x : ℝ) : ℂ) := funext hid
    rw [e1]
    have htri := eLpNorm_add_le hm1 hm2 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    calc _ ≤ _ := htri
      _ < ENNReal.ofReal (ε / 2) + eLpNorm (fun x => ((tailSet c δ)ᶜ.indicator w x - g x)
            * ((seamCut c δ x : ℝ) : ℂ)) 2 (CM c m) :=
          ENNReal.add_lt_add_right hXne hA
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add le_rfl hX
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  -- conclude
  refine ⟨G, hGc, hGp, ⟨R, hGR⟩, ?_⟩
  unfold UnforcedLeray.Short.IIIa.xNorm
  have hae : (fun x => w0 x - G x) =ᵐ[CM c m] (fun x => w x - h x) := by
    filter_upwards [hwae, ae_cell c m] with x hx1 hx2
    rw [hx1, hGh x hx2]
  rw [eLpNorm_congr_ae hae]
  exact hbound

end UnforcedLeray.Short.IIIa
