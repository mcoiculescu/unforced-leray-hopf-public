import UnforcedLeray.Units.B0448
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The space-time causal kernel and the sup bound on the unit strip (INF04 T14)


(block 3B HEAT-R3). Manuscript `paper/main.tex` lines 7397–7401 (`eq:free-stress-5`, B0449),
7663–7683 (`eq:free-stress-22`, B0448, and the end of the proof of `eq:free-stress-5`) and
3632–3636 (`eq:free-background-b-2`, B0450):

> The causal inverse kernel is `K(t,z) = 1_{t>0}e^{-t}H_t(z)`. It belongs to `L^{q'}` precisely
> when `q > 5/2` [...] The identity `H = K*F` is distributionally valid. [...] Hölder's
> inequality gives `‖H‖_∞ ≤ ‖K‖_{q'}‖F‖_q`, and translation continuity of `K` in `L^{q'}` gives a
> continuous representative.

The kernel, its `L^{q'}` criterion and the representation `H = K * F` were drafted as unit B0448

of the manuscript's argument on the unit strip (after the pullback of B0447):

* `norm_kernelConv_le`: Hölder, `|(K * F)(X)| ≤ ‖K‖_{q'}‖F‖_q` at **every** point `X`;
* `continuous_kernelConv`: `K * F` is continuous (translation continuity of `K` in `L^{q'}`,
  `q' < ∞`);
* `strip_sup_le`: if `H, F ∈ L^q(ℝ × ℝ³)` with `q > 5/2` and `(∂_t - Δ_z + 1)H = F` against
  every `C_c^∞` test, then `H` has a continuous representative bounded everywhere by
  `‖K‖_{q'}‖F‖_q` (tex 7677–7683).

The route is the manuscript's (Fourier uniqueness, done in B0448); the Duhamel route BP5
(`strip_duhamel`) of the scoping note is therefore not needed and not built.

Conventions. Space-time is B0448's `ST = WithLp 2 (ℝ × ℝ³)`, time first; fields are complex
valued (`ℂ`), as in B0448; `q, q'` are real Hölder conjugates (`1 < q < ∞`). The hypothesis
`5/2 < q` is the manuscript's; it makes `‖K‖_{q'}` finite, so no `toReal ∞ = 0` junk enters the
bound.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal SchwartzMap
open UnforcedLeray.B0448

/-- **INF04 T14 `stKernel`** (tex 7666–7669, B0448): `K(t,z) = 1_{t>0} e^{-t} H_t(z)` on
`ℝ × ℝ³`, the drafted `B0448.kernel`. -/
abbrev stKernel : ℝ × Space → ℝ := B0448.kernel

theorem stKernel_of_pos {t : ℝ} (ht : 0 < t) (z : Space) :
    stKernel (t, z) = Real.exp (-t) * Heat.kernel t z :=
  kernel_of_pos ht z

/-- **INF04 T14 `memLp_stKernel`** (`eq:free-stress-22`, tex 7671–7676): for `q > 5/2`,
`K ∈ L^{q'}(ℝ × ℝ³)`, `q' = q/(q-1)`. -/
theorem memLp_stKernel {q q' : ℝ} (hqq' : q.HolderConjugate q') (hq : 5 / 2 < q) :
    MemLp stKernel (ENNReal.ofReal q') volume :=
  (memLp_kernel_iff hqq').2 hq

/-- The `L^r` norm of the transported kernel `kerC` on `ST` is that of `K` on `ℝ × ℝ³`. -/
theorem eLpNorm_kerC (r : ℝ≥0∞) :
    eLpNorm kerC r (volume : Measure ST) = eLpNorm stKernel r volume := by
  have h := eLpNorm_comp_measurePreserving (g := fun p => ((stKernel p : ℝ) : ℂ)) (p := r)
    (Complex.measurable_ofReal.comp measurable_kernel).aestronglyMeasurable
    measurePreserving_ofLp
  have e : kerC = (fun p => ((stKernel p : ℝ) : ℂ)) ∘
      (MeasurableEquiv.toLp 2 (ℝ × Space)).symm := rfl
  rw [e, h]
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun p => by simp)

theorem memLp_kerC {q q' : ℝ} (hqq' : q.HolderConjugate q') (hq : 5 / 2 < q) :
    MemLp kerC (ENNReal.ofReal q') (volume : Measure ST) :=
  ⟨measurable_kerC.aestronglyMeasurable, by
    rw [eLpNorm_kerC]; exact (memLp_stKernel hqq' hq).2⟩

/-- The reflected translate `Y ↦ K(X - Y)` has the same `L^r` norm as `K`. -/
theorem eLpNorm_kerC_sub (r : ℝ≥0∞) (X : ST) :
    eLpNorm (fun Y => kerC (X - Y)) r (volume : Measure ST) = eLpNorm stKernel r volume := by
  rw [← eLpNorm_kerC r]
  exact eLpNorm_comp_measurePreserving measurable_kerC.aestronglyMeasurable
    (Measure.measurePreserving_sub_left volume X)

/-- **Hölder at a point** (tex 7681): `|(K * F)(X)| ≤ ‖K‖_{q'} ‖F‖_q` for every `X`, `q > 5/2`. -/
theorem norm_kernelConv_le {q q' : ℝ} (hqq' : q.HolderConjugate q') (hq : 5 / 2 < q)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ST)) (X : ST) :
    ‖kernelConv F X‖ ≤ (eLpNorm stKernel (ENNReal.ofReal q') volume).toReal *
      (eLpNorm F (ENNReal.ofReal q) volume).toReal := by
  have : ENNReal.HolderTriple (ENNReal.ofReal q') (ENNReal.ofReal q) 1 :=
    hqq'.symm.ennrealOfReal
  have hK : AEStronglyMeasurable (fun Y => kerC (X - Y)) (volume : Measure ST) :=
    (measurable_kerC.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := (volume : Measure ST))
    (p := ENNReal.ofReal q') (q := ENNReal.ofReal q) (r := 1) hK (Lp.aestronglyMeasurable F)
    (fun a b => a * b) 1 (Eventually.of_forall fun Y => by simp [nnnorm_mul])
  rw [eLpNorm_kerC_sub, ENNReal.coe_one, one_mul] at hH
  have hfin1 : eLpNorm stKernel (ENNReal.ofReal q') volume ≠ ∞ :=
    (memLp_stKernel hqq' hq).eLpNorm_lt_top.ne
  have hfin2 : eLpNorm (F : ST → ℂ) (ENNReal.ofReal q) volume ≠ ∞ := Lp.eLpNorm_ne_top F
  have h1 : ‖kernelConv F X‖ₑ ≤ eLpNorm (fun Y => kerC (X - Y) * F Y) 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm _
  have h2 := h1.trans hH
  rw [← ENNReal.toReal_mul]
  rw [← enorm_norm, ← ENNReal.ofReal_toReal (ENNReal.mul_ne_top hfin1 hfin2),
    Real.enorm_of_nonneg (norm_nonneg _)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2

/-- `X ↦ (K(X - ·))` as a continuous family of continuous maps `Y ↦ X - Y`. -/
def reflectMap (X : ST) : C(ST, ST) := ⟨fun Y => X - Y, continuous_const.sub continuous_id⟩

theorem continuous_reflectMap : Continuous reflectMap :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.sub continuous_snd)

/-- **Translation continuity** (tex 7682–7683): `K * F` is continuous for `q > 5/2`. -/
theorem continuous_kernelConv {q q' : ℝ} (hqq' : q.HolderConjugate q') (hq : 5 / 2 < q)
    (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ST)) : Continuous (kernelConv F) := by
  have : Fact (1 ≤ ENNReal.ofReal q') := ⟨ENNReal.one_le_ofReal.2 hqq'.symm.lt.le⟩
  have : ENNReal.HolderTriple (ENNReal.ofReal q') (ENNReal.ofReal q) 1 :=
    hqq'.symm.ennrealOfReal
  have hq'top : ENNReal.ofReal q' ≠ ∞ := ENNReal.ofReal_ne_top
  set k : Lp ℂ (ENNReal.ofReal q') (volume : Measure ST) := (memLp_kerC hqq' hq).toLp kerC
  have hmp : ∀ X : ST, MeasurePreserving (reflectMap X) (volume : Measure ST) volume :=
    fun X => Measure.measurePreserving_sub_left volume X
  have hc : Continuous fun X : ST => Lp.compMeasurePreserving (reflectMap X) (hmp X) k :=
    continuous_const.compMeasurePreservingLp continuous_reflectMap hmp hq'top
  have hrep : ∀ X : ST, (Lp.compMeasurePreserving (reflectMap X) (hmp X) k : ST → ℂ) =ᵐ[volume]
      fun Y => kerC (X - Y) := by
    intro X
    have h1 := Lp.coeFn_compMeasurePreserving k (hmp X)
    have h2 : (fun Y => (k : ST → ℂ) (reflectMap X Y)) =ᵐ[volume] fun Y => kerC (X - Y) :=
      (hmp X).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp (memLp_kerC hqq' hq))
    exact h1.trans h2
  rw [Metric.continuous_iff]
  intro X ε hε
  have hFfin : eLpNorm (F : ST → ℂ) (ENNReal.ofReal q) volume ≠ ∞ := Lp.eLpNorm_ne_top F
  set B : ℝ := (eLpNorm (F : ST → ℂ) (ENNReal.ofReal q) volume).toReal + 1 with hB
  have hBpos : 0 < B := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hc X (ε / B) (div_pos hε hBpos)
  refine ⟨δ, hδ, fun X' hX' => ?_⟩
  have hd := hδ' X' hX'
  rw [Lp.dist_def] at hd
  have hdiff : eLpNorm ((Lp.compMeasurePreserving (reflectMap X') (hmp X') k : ST → ℂ) -
      (Lp.compMeasurePreserving (reflectMap X) (hmp X) k : ST → ℂ)) (ENNReal.ofReal q') volume =
      eLpNorm (fun Y => kerC (X' - Y) - kerC (X - Y)) (ENNReal.ofReal q') volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hrep X, hrep X'] with Y h1 h2
    simp only [Pi.sub_apply]
    rw [h1, h2]
  rw [hdiff] at hd
  -- Hölder for the difference of the two convolutions.
  have hKd : AEStronglyMeasurable (fun Y => kerC (X' - Y) - kerC (X - Y)) (volume : Measure ST) :=
    ((measurable_kerC.comp (measurable_const.sub measurable_id)).sub
      (measurable_kerC.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := (volume : Measure ST))
    (p := ENNReal.ofReal q') (q := ENNReal.ofReal q) (r := 1) hKd (Lp.aestronglyMeasurable F)
    (fun a b => a * b) 1 (Eventually.of_forall fun Y => by simp [nnnorm_mul])
  rw [ENNReal.coe_one, one_mul] at hH
  have hint : ∀ Z : ST, Integrable (fun Y => kerC (Z - Y) * F Y) volume := by
    intro Z
    have hm := MemLp.mul' (p := ENNReal.ofReal q') (q := ENNReal.ofReal q) (r := 1)
      (Lp.memLp F) (((memLp_kerC hqq' hq).comp_measurePreserving
        (Measure.measurePreserving_sub_left volume Z)))
    exact memLp_one_iff_integrable.1 hm
  have hsub : kernelConv F X' - kernelConv F X =
      ∫ Y, (kerC (X' - Y) - kerC (X - Y)) * F Y := by
    rw [kernelConv, kernelConv, ← integral_sub (hint X') (hint X)]
    congr 1; funext Y; ring
  rw [dist_eq_norm, hsub]
  have h1 : ‖∫ Y, (kerC (X' - Y) - kerC (X - Y)) * F Y‖ₑ ≤
      eLpNorm (fun Y => (kerC (X' - Y) - kerC (X - Y)) * F Y) 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm _
  have hfinK : eLpNorm (fun Y => kerC (X' - Y) - kerC (X - Y)) (ENNReal.ofReal q') volume ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (eLpNorm_sub_le ?_ ?_ ?_) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
    · exact (measurable_kerC.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (measurable_kerC.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ENNReal.one_le_ofReal.2 hqq'.symm.lt.le
    · rw [eLpNorm_kerC_sub]; exact (memLp_stKernel hqq' hq).eLpNorm_lt_top
    · rw [eLpNorm_kerC_sub]; exact (memLp_stKernel hqq' hq).eLpNorm_lt_top
  have h2 := h1.trans hH
  rw [← enorm_norm, ← ENNReal.ofReal_toReal (ENNReal.mul_ne_top hfinK hFfin),
    Real.enorm_of_nonneg (norm_nonneg _)] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  rw [ENNReal.toReal_mul] at h3
  calc _ ≤ _ := h3
    _ ≤ (eLpNorm (fun Y => kerC (X' - Y) - kerC (X - Y)) (ENNReal.ofReal q') volume).toReal * B := by
        gcongr; rw [hB]; linarith
    _ < ε / B * B := by gcongr
    _ = ε := by field_simp

/-- **INF04 T14 `strip_sup_le`** (`eq:free-stress-5` on the unit strip, tex 7663–7683;
B0448, B0449, B0450). Let `q > 5/2` with conjugate `q'`. If `H, F ∈ L^q(ℝ × ℝ³)` and
`(∂_t - Δ_z + 1)H = F` in distributions (against every `C_c^∞` test), then `H` has a
continuous representative `Hc` with `|Hc(X)| ≤ ‖K‖_{L^{q'}} ‖F‖_{L^q}` at every point `X`, where
`K = stKernel` and `‖K‖_{L^{q'}} < ∞`. -/
theorem strip_sup_le {q q' : ℝ} (hqq' : q.HolderConjugate q') (hq : 5 / 2 < q)
    {H F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ST)}
    (hHF : ∀ φ : 𝓢(ST, ℂ), HasCompactSupport φ →
      ∫ X, resolventOpT φ X * H X = ∫ X, φ X * F X) :
    eLpNorm stKernel (ENNReal.ofReal q') volume < ∞ ∧
    ∃ Hc : ST → ℂ, Continuous Hc ∧ (H : ST → ℂ) =ᵐ[volume] Hc ∧
      ∀ X, ‖Hc X‖ ≤ (eLpNorm stKernel (ENNReal.ofReal q') volume).toReal *
        (eLpNorm F (ENNReal.ofReal q) volume).toReal := by
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.2 hqq'.lt.le⟩
  exact ⟨(memLp_stKernel hqq' hq).eLpNorm_lt_top, kernelConv F, continuous_kernelConv hqq' hq F,
    ae_eq_kernelConv_of_compactSupport hHF, norm_kernelConv_le hqq' hq F⟩

end UnforcedLeray.Heat
