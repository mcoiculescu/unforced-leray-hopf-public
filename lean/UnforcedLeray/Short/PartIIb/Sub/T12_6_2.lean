import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Time

/-!
# Part II-b, task `PartII-b:T12/6/2` (`DsolDuhamelIntegrable`): conditional reduction

Source of record: `the November 2 reference manuscript`, lines 1920-1930 (SP 1924:
`D G(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} G(t) dt/t`, bound by `1/a_r`, `a_r = Re μ + (3/r-1)/2 > 0`).

The target is split into

* `DsolDMeas`: a.e. strong measurability of the Duhamel body on the box times the time line;
* `BoxSlice`: for a.e. `t > 0` the box integral (over `x = (s, z) ∈ [σ,H] × [-R,R]²`) of
  `(t/s)^{Re μ} t⁻¹ ‖e^{ν(s-t)Δ} G(t)(z)‖` is at most `C t^{Re μ - 1} ‖G(t,·)‖_{L^r(Cyl.avgμ c)}`
  (`t < H`), and `0` for `t ≥ H`. It is itself reduced to `FlatHeatBoxBound` (periodic `L^r` cell
  bound plus Hölder on the box, uniform in the heat time) and `BoxSliceS` (the `s`-integral);
* `DeqAbsTime` (proved: `deqAbsTime`): `∫_0^H t^{Re μ - 1} ‖G(t,·)‖_{L^r} dt < ∞`.

Proved here: `flatHeatBoxBound_of`, `dsolDuhamelIntegrable_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Box integrand `1_{0<t<s} (t/s)^{Re μ} t⁻¹ ‖e^{ν(s-t)Δ} G(t)(z)‖`, `x = (s, z)`. -/
def boxIntegrand (ν : ℝ) (μ : ℂ) (G : CProf) (t : ℝ) (x : Coord) : ℝ :=
  if 0 < t ∧ t < x.1 then
    ‖(((t / x.1 : ℝ) : ℂ) ^ μ)‖ * t⁻¹ *
      ‖flatHeat (ν * (x.1 - t)) (fun w => G (t, w)) x.2‖
  else 0

/-- **Leaf `PartII-b:T12/6/2/1`** (measurability of the Duhamel body on the box times the time line;
SP 1924): replace `G` by `exists_periodic_rep` and use `stronglyMeasurable_duhamelBody`,
`flatDuhamel_congr_of_ae`. -/
def DsolDMeas : Prop :=
  ∀ (c r ν : ℝ) (μ : ℂ) (G : CProf), 0 < c → 1 < r → r < 3 → 0 < ν →
    0 < μ.re + (3 / r - 1) / 2 → InHr c r G →
    ∀ σ H R : ℝ, 0 < σ →
      AEStronglyMeasurable (duhamelS.indicator (duhamelBody ν μ G))
        ((volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))).prod (volume : Measure ℝ))

/-- **Leaf `PartII-b:T12/6/2/2`** (periodic box bound; SP 1923-1927). A measurable function on the
plane which is everywhere `c`-periodic in `q` has box `L¹` norm bounded by `C` times its
`L^r(Cyl.avgμ c)` norm (Hölder on the finite box, the box meets finitely many `q`-cells). -/
def PeriodicBoxBound : Prop :=
  ∀ (r c R : ℝ), 1 ≤ r → 0 < c → ∃ C : ℝ, ∀ f : ℝ × ℝ → CMerid,
    AEStronglyMeasurable f volume → (∀ z : ℝ × ℝ, f (z.1 + c, z.2) = f z) →
      ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖f z‖ₑ ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `PartII-b:T12/6/2/3`** (measurability of the heat flow). For `θ > 0` and an a.e.
strongly measurable `g`, `flatHeat θ g` is a.e. strongly measurable (replace `g` by a strongly
measurable representative; `flatHeat` only sees the a.e. class; then parametric integral as in
`stronglyMeasurable_duhamelBody`). -/
def FlatHeatAEMeas : Prop :=
  ∀ (θ : ℝ) (g : ℝ × ℝ → CMerid), 0 < θ → AEStronglyMeasurable g volume →
    AEStronglyMeasurable (flatHeat θ g) volume

/-- Heat flow, box bound uniform in the heat time (assembled from the two leaves above). -/
def FlatHeatBoxBound : Prop :=
  ∀ (r c R : ℝ), 1 ≤ r → 0 < c → ∃ C : ℝ, ∀ (θ : ℝ) (g : ℝ × ℝ → CMerid), 0 < θ →
    (∀ᵐ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) → AEStronglyMeasurable g volume →
      ∫⁻ z in Icc (-R) R ×ˢ Icc (-R) R, ‖flatHeat θ g z‖ₑ ≤
        ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

theorem flatHeatBoxBound_of (h1 : PeriodicBoxBound) (h2 : FlatHeatAEMeas) : FlatHeatBoxBound := by
  intro r c R hr hc
  obtain ⟨C, hC⟩ := h1 r c R hr hc
  refine ⟨C, fun θ g hθ hper hg => ?_⟩
  have hf := hC (flatHeat θ g) (h2 θ g hθ hg) (fun z => flatHeat_qShift_of_ae hper z)
  exact hf.trans (by gcongr; exact flatHeatContraction r c θ g hr hc hθ hper hg)

/-- **Leaf `PartII-b:T12/6/2/4`** (the `s`-integral; SP 1924). For real `a` and `0 < σ`, there is
`K` with `∫_{s ∈ [σ,H], s > t} (t/s)^a ds ≤ K t^a` for `0 < t < H`. -/
def BoxSliceS : Prop :=
  ∀ (a σ H : ℝ), 0 < σ → ∃ K : ℝ, ∀ t : ℝ, 0 < t → t < H →
    ∫⁻ s in Icc σ H ∩ Ioi t, ENNReal.ofReal ((t / s) ^ a) ≤ ENNReal.ofReal (K * t ^ a)

/-- **Leaf `PartII-b:T12/6/2/5`** (slice bound on the box; SP 1923-1927). Follows from
`FlatHeatBoxBound`, `BoxSliceS` and `deqSliceAe` (a.e. slices of an `H_r` profile are periodic,
measurable, with finite `L^r` norm) by Tonelli in `(s, z)`. -/
def BoxSlice : Prop :=
  ∀ (r : ℝ), 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 → ∀ ν c : ℝ, 0 < ν → 0 < c →
    ∀ G : CProf, InHr c r G → ∀ σ H R : ℝ, 0 < σ →
      ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R),
            ENNReal.ofReal (boxIntegrand ν μ G t x) ≤
          ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
            (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
              eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
                (UnforcedLeray.Cyl.avgμ c)) t

theorem enorm_duhamel_indicator (ν : ℝ) (μ : ℂ) (G : CProf) (t : ℝ) (x : Coord) :
    ‖duhamelS.indicator (duhamelBody ν μ G) (x, t)‖ₑ =
      ENNReal.ofReal (boxIntegrand ν μ G t x) := by
  by_cases h : 0 < t ∧ t < x.1
  · have hm : (x, t) ∈ duhamelS := ⟨h.1, h.2⟩
    rw [Set.indicator_of_mem hm, boxIntegrand, if_pos h, ← ofReal_norm_eq_enorm]
    congr 1
    unfold duhamelBody
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h.1)]
  · have hm : (x, t) ∉ duhamelS := fun hh => h ⟨hh.1, hh.2⟩
    rw [Set.indicator_of_notMem hm, boxIntegrand, if_neg h]
    simp

theorem dsolDuhamelIntegrable_of (hM : DsolDMeas) (hB : BoxSlice) :
    DsolDuhamelIntegrable := by
  intro c r ν μ G hc hr1 hr3 hν hμ hG σ H R hσ
  obtain ⟨C, hC⟩ := hB r hr1 hr3 μ hμ ν c hν hc G hG σ H R hσ
  have hmeas := hM c r ν μ G hc hr1 hr3 hν hμ hG σ H R hσ
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hP0 : AEMeasurable (fun p : Coord × ℝ => ‖duhamelS.indicator (duhamelBody ν μ G) p‖ₑ)
      ((volume.restrict (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R))).prod (volume : Measure ℝ)) :=
    hmeas.enorm
  rw [lintegral_prod_symm _ hP0]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R),
          ‖duhamelS.indicator (duhamelBody ν μ G) (x, t)‖ₑ ≤
        ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
          (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c)) t := by
    have h1 := (ae_restrict_iff' measurableSet_Ioi).1 hC
    filter_upwards [h1] with t ht
    simp_rw [enorm_duhamel_indicator]
    by_cases htp : 0 < t
    · exact ht htp
    · have hz : ∀ x : Coord, boxIntegrand ν μ G t x = 0 := fun x => by
        rw [boxIntegrand, if_neg (fun h => htp h.1)]
      simp [hz]
  calc ∫⁻ t : ℝ, ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-R) R),
          ‖duhamelS.indicator (duhamelBody ν μ G) (x, t)‖ₑ
      ≤ ∫⁻ t : ℝ, ENNReal.ofReal C * Set.indicator (Ioo (0 : ℝ) H)
          (fun t : ℝ => ENNReal.ofReal (t ^ (μ.re - 1)) *
            eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
              (UnforcedLeray.Cyl.avgμ c)) t := lintegral_mono_ae hae
    _ = ENNReal.ofReal C * ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (μ.re - 1)) *
          eLpNorm (fun z : ℝ × ℝ => G (t, z)) (ENNReal.ofReal r)
            (UnforcedLeray.Cyl.avgμ c) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator measurableSet_Ioo]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (deqAbsTime r hr1 hr3 μ hμ c hc G hG H)

end UnforcedLeray.Short.IIb
