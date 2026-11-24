import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp

/-!
# Decomposition of `GradL2pMollify` (source 2531; 1415-1424)

Source of record `the November 2 reference manuscript`
(line 2531: `‖Dw‖²_{Y_{2p}} ≤ C ‖w‖_∞ ‖D²w‖_{Y_p}` is proved by spatial mollification and a
slice integration by parts; 1415-1424 and 1515-1531 for `w ∈ Y_{q₀}`, `w ∈ L^∞`).

`gradL2pMollify_of` proves `GradL2pMollify` from four Prop lemmas:
`MollSeqExists`, `MollSliceFacts`, `MollDerivIdentity`, `MollConv`.

The approximants are the slice mollifications `Moll (ρ n) (rep ·)` *gated* to a measurable set
`A n ⊆ (0,P]` of good periods (slices where the pointwise bounds/derivative identities hold and
`‖rep g τ‖_{q₀} ≤ n`), and `0` elsewhere.  The gating gives the uniform sup bound of `G n`
(the `Y_{q₀}` norm gives no sup bound in `τ`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (rep)

/-- Spatial convolution `(ρ * f)(y) = ∫ ρ(y - z) f(z) dz`. -/
def Moll (ρ : UnforcedLeray.Space → ℝ) (f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) :
    UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3 :=
  fun y => ∫ z, ρ (y - z) • f z

/-- Gate a phase function to periods `τ ∈ A` (zero elsewhere). -/
def gate (A : Set ℝ) (F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) :
    ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3 :=
  Set.indicator {x : ℝ × UnforcedLeray.Space | x.1 ∈ A} F

/-- A mollifier sequence: smooth, compactly supported, nonnegative, mass one, support in the ball
of radius `1/(n+1)`. -/
def MollSeq (ρ : ℕ → UnforcedLeray.Space → ℝ) : Prop :=
  ∀ n, ContDiff ℝ ∞ (ρ n) ∧ HasCompactSupport (ρ n) ∧ (∀ y, 0 ≤ ρ n y) ∧ (∫ y, ρ n y = 1) ∧
    tsupport (ρ n) ⊆ Metric.closedBall 0 (1 / ((n : ℝ) + 1))

/-- Lemma 1 (Haiku): a mollifier sequence exists (`ContDiffBump`, normalized by its integral). -/
def MollSeqExists : Prop := ∃ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ

/-- Lemma 2 (slice facts on `ℝ³`, standard): convolution of a mass-one mollifier with `f ∈ L^{q₀}`
is smooth, in `L^{q₀}` with norm at most `‖f‖_{q₀}` (Young), bounded by
`‖ρ n‖_{q₀'} ‖f‖_{q₀}` (Hölder), and bounded by `M` when `|f| ≤ M` a.e. (mass one, `ρ ≥ 0`). -/
def MollSliceFacts : Prop :=
  ∀ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ → ∀ (n : ℕ)
    (f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    MemLp f UnforcedLeray.B0412.q0E volume →
    ContDiff ℝ ∞ (Moll (ρ n) f) ∧ MemLp (Moll (ρ n) f) UnforcedLeray.B0412.q0E volume ∧
    (∀ y, ‖Moll (ρ n) f y‖ ≤
      (eLpNorm (ρ n) (UnforcedLeray.PhaseSpace.conjExp UnforcedLeray.B0412.q0E) volume).toReal *
        (eLpNorm f UnforcedLeray.B0412.q0E volume).toReal) ∧
    (∀ M : ℝ, (∀ᵐ y ∂(volume : MeasureTheory.Measure UnforcedLeray.Space), ‖f y‖ ≤ M) →
      ∀ y, ‖Moll (ρ n) f y‖ ≤ M)

/-- Lemma 3 (phase operator to slice derivative; source 1415-1424): if `∂_j w = g` in the phase
distributional sense (`HasPhaseOp (-dy j) w g`, `w, g ∈ Y_{q₀}`), then for a.e. `τ` and every
`n, y`, `∂_j (ρ_n * rep w τ)(y) = (ρ_n * rep g τ)(y)`.  Proof: test with
`Φ(τ,y) = a(τ) ρ_n(x - y) e_c`, `a` periodic smooth; differentiate under the integral; the
a.e.-`τ` identity for all `x` follows from continuity of both sides in `x` and a countable dense
set of `x`, a countable family of `a`s (or Lebesgue differentiation / fundamental lemma in `τ`). -/
def MollDerivIdentity : Prop :=
  ∀ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ → ∀ (P : ℝ) [Fact (0 < P)]
    (w g : Yq P UnforcedLeray.B0412.q0E) (j : Fin 3),
    HasPhaseOp (fun Φ => -dy j Φ) w g →
    ∀ᵐ τ ∂(volume : Measure ℝ), ∀ (n : ℕ) (y : UnforcedLeray.Space),
      fderiv ℝ (Moll (ρ n) (rep w τ)) y (EuclideanSpace.single j 1) = Moll (ρ n) (rep g τ) y

/-- Lemma 4 (approximate identity on `L^{q₀}(phaseμ)` with gating): for `F ∈ L^{q₀}(phaseμ P)`
strongly measurable and measurable `A n` eventually containing a.e. `τ ∈ (0,P]`,
the gated mollifications converge to `F` in `L^{q₀}(phaseμ P)`. (Dominated convergence in `τ`
with dominator `2^{q₀}‖F τ‖_{q₀}^{q₀}`, approximate identity in each slice.) -/
def MollConv : Prop :=
  ∀ ρ : ℕ → UnforcedLeray.Space → ℝ, MollSeq ρ → ∀ (P : ℝ) [Fact (0 < P)]
    (F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3),
    StronglyMeasurable F → MemLp F UnforcedLeray.B0412.q0E (phaseμ P) →
    ∀ A : ℕ → Set ℝ, (∀ n, MeasurableSet (A n)) →
    (∀ᵐ τ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)), ∃ N, ∀ m ≥ N, τ ∈ A m) →
    Tendsto (fun n => eLpNorm
      (fun x => gate (A n) (fun x => Moll (ρ n) (fun z => F (x.1, z)) x.2) x - F x)
      UnforcedLeray.B0412.q0E (phaseμ P)) atTop (𝓝 0)

lemma gate_of_mem {A : Set ℝ} {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    {τ : ℝ} (h : τ ∈ A) (y : UnforcedLeray.Space) : gate A F (τ, y) = F (τ, y) :=
  Set.indicator_of_mem (show (τ, y) ∈ {x : ℝ × UnforcedLeray.Space | x.1 ∈ A} from h) F

lemma gate_of_not_mem {A : Set ℝ} {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    {τ : ℝ} (h : τ ∉ A) (y : UnforcedLeray.Space) : gate A F (τ, y) = 0 :=
  Set.indicator_of_notMem (show (τ, y) ∉ {x : ℝ × UnforcedLeray.Space | x.1 ∈ A} from h) F

/-- Joint measurability of the slice mollification. -/
lemma stronglyMeasurable_moll {ρ : UnforcedLeray.Space → ℝ} (hρ : Continuous ρ)
    {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3} (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun x : ℝ × UnforcedLeray.Space =>
      Moll ρ (fun z => F (x.1, z)) x.2) := by
  have h1 : StronglyMeasurable (fun p : (ℝ × UnforcedLeray.Space) × UnforcedLeray.Space =>
      ρ (p.1.2 - p.2)) :=
    (hρ.comp ((continuous_snd.comp continuous_fst).sub continuous_snd)).stronglyMeasurable
  have h2 : StronglyMeasurable (fun p : (ℝ × UnforcedLeray.Space) × UnforcedLeray.Space =>
      F (p.1.1, p.2)) :=
    hF.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h : StronglyMeasurable (fun p : (ℝ × UnforcedLeray.Space) × UnforcedLeray.Space =>
      ρ (p.1.2 - p.2) • F (p.1.1, p.2)) := h1.smul h2
  exact h.integral_prod_right'

lemma memLp_rep_slice {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E) (τ : ℝ) :
    MemLp (rep w τ) UnforcedLeray.B0412.q0E volume :=
  (Lp.memLp (w (τ : AddCircle P))).ae_eq (UnforcedLeray.Cons.C03.Concrete.rep_slice w τ).symm

lemma memLp_rep_phase {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E) :
    MemLp (fun x : ℝ × UnforcedLeray.Space => rep w x.1 x.2) UnforcedLeray.B0412.q0E (phaseμ P) := by
  have hprod : (volume : Measure (ℝ × UnforcedLeray.Space)).restrict
      (Ioc (0 : ℝ) P ×ˢ (univ : Set UnforcedLeray.Space)) = phaseμ P := by
    simpa only [Measure.volume_eq_prod, phaseμ] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure UnforcedLeray.Space)) (Ioc 0 P)).symm
  rw [← hprod]
  exact UnforcedLeray.Cons.C03.Concrete.memLp_rep_periodCell UnforcedLeray.B0412.q0E_ne_top w

open Classical in
/-- `GradL2pMollify` from the four slice/convergence lemmas (gated slice mollification). -/
theorem gradL2pMollify_of (h1 : MollSeqExists) (h2 : MollSliceFacts) (h3 : MollDerivIdentity)
    (h4 : MollConv) : GradL2pMollify := by
  intro P _ w g h M j hM0 hwM hwg hgh
  obtain ⟨ρ, hρ⟩ := h1
  set q := UnforcedLeray.B0412.q0E with hq
  have hqtop : q ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq1)
  -- a.e. spatial bound of `rep w`
  have hbd : ∀ᵐ τ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), ‖rep w τ y‖ ≤ M := by
    have hmeas : MeasurableSet {x : ℝ × UnforcedLeray.Space | ‖rep w x.1 x.2‖ ≤ M} :=
      measurableSet_le (UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep w).measurable.norm
        measurable_const
    have := hwM
    unfold phaseμ at this
    exact (Measure.ae_prod_iff_ae_ae hmeas).1 this
  have hd1 := h3 ρ hρ P w g j hwg
  have hd2 := h3 ρ hρ P g h j hgh
  let Q : ℝ → Prop := fun τ =>
    (∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), ‖rep w τ y‖ ≤ M) ∧
    (∀ (n : ℕ) (y : UnforcedLeray.Space), fderiv ℝ (Moll (ρ n) (rep w τ)) y
        (EuclideanSpace.single j 1) = Moll (ρ n) (rep g τ) y) ∧
    (∀ (n : ℕ) (y : UnforcedLeray.Space), fderiv ℝ (Moll (ρ n) (rep g τ)) y
        (EuclideanSpace.single j 1) = Moll (ρ n) (rep h τ) y)
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) P) with hμ
  have hQ : ∀ᵐ τ ∂μ, Q τ := by
    filter_upwards [hbd, ae_restrict_of_ae hd1, ae_restrict_of_ae hd2] with τ a b c
    exact ⟨a, b, c⟩
  -- measurable set of good periods
  set B : Set ℝ := toMeasurable μ {τ | ¬ Q τ} with hB
  have hB0 : μ B = 0 := by
    rw [hB, measure_toMeasurable]; exact ae_iff.1 hQ
  set S : Set ℝ := Bᶜ ∩ Ioc (0 : ℝ) P with hS
  have hSmeas : MeasurableSet S := (measurableSet_toMeasurable _ _).compl.inter measurableSet_Ioc
  have hSQ : ∀ τ ∈ S, Q τ := by
    intro τ hτ
    by_contra hnot
    exact hτ.1 (subset_toMeasurable μ _ hnot)
  have hSae : ∀ᵐ τ ∂μ, τ ∈ S := by
    have h1' : ∀ᵐ τ ∂μ, τ ∉ B := measure_eq_zero_iff_ae_notMem.1 hB0
    have h2' : ∀ᵐ τ ∂μ, τ ∈ Ioc (0 : ℝ) P := ae_restrict_mem measurableSet_Ioc
    filter_upwards [h1', h2'] with τ a b using ⟨a, b⟩
  -- measurability of the slice norm
  have hrepg := UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep g
  have hreph := UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep h
  have hrepw := UnforcedLeray.Cons.C03.Concrete.stronglyMeasurable_rep w
  have hng : Measurable (fun τ : ℝ => eLpNorm (rep g τ) q volume) := by
    have : (fun τ : ℝ => eLpNorm (rep g τ) q volume) =
        fun τ => (∫⁻ y, ‖rep g τ y‖ₑ ^ q.toReal ∂(volume : Measure UnforcedLeray.Space)) ^
          (1 / q.toReal) := by
      funext τ; exact eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop
    rw [this]
    exact (Measurable.lintegral_prod_right'
      (f := fun x : ℝ × UnforcedLeray.Space => ‖rep g x.1 x.2‖ₑ ^ q.toReal)
      (hrepg.measurable.enorm.pow_const _)).pow_const _
  let A : ℕ → Set ℝ := fun n => S ∩ {τ | eLpNorm (rep g τ) q volume ≤ (n : ℝ≥0∞)}
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    hSmeas.inter (measurableSet_le hng measurable_const)
  have hAmono : Monotone A := by
    intro a b hab τ hτ
    exact ⟨hτ.1, show eLpNorm (rep g τ) q volume ≤ (b : ℝ≥0∞) from
      hτ.2.trans (by exact_mod_cast hab)⟩
  have hAcover : ∀ᵐ τ ∂μ, ∃ N, ∀ m ≥ N, τ ∈ A m := by
    filter_upwards [hSae] with τ hτ
    have hlt : eLpNorm (rep g τ) q volume < ⊤ := (memLp_rep_slice g τ).2
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hlt.ne
    exact ⟨N, fun m hm => ⟨hτ, (hN.le.trans (by exact_mod_cast hm))⟩⟩
  have hcw := stronglyMeasurable_moll (hρ 0 |>.1.continuous) hrepw
  refine ⟨fun n => gate (A n) (fun x => Moll (ρ n) (rep w x.1) x.2),
    fun n => gate (A n) (fun x => Moll (ρ n) (rep g x.1) x.2),
    fun n => gate (A n) (fun x => Moll (ρ n) (rep h x.1) x.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n τ
    by_cases hτ : τ ∈ A n
    · have hQτ := hSQ τ hτ.1
      have fw := h2 ρ hρ n (rep w τ) (memLp_rep_slice w τ)
      have fg := h2 ρ hρ n (rep g τ) (memLp_rep_slice g τ)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [gate_of_mem hτ] using fw.1
      · simpa [gate_of_mem hτ] using fg.1
      · intro y
        simpa [gate_of_mem hτ] using fw.2.2.2 M hQτ.1 y
      · exact ⟨_, fun y => by simpa [gate_of_mem hτ] using fg.2.2.1 y⟩
      · intro y
        simpa [gate_of_mem hτ] using hQτ.2.1 n y
      · intro y
        simpa [gate_of_mem hτ] using hQτ.2.2 n y
    · have e : ∀ F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3,
          (fun y => gate (A n) F (τ, y)) = fun _ => 0 := fun F => funext (gate_of_not_mem hτ)
      rw [e, e, e]
      refine ⟨contDiff_const, contDiff_const, ?_, ⟨0, fun y => by simp⟩, ?_, ?_⟩
      · intro y; simpa using hM0
      · intro y; simp
      · intro y; simp
  · intro n τ
    by_cases hτ : τ ∈ A n
    · have fg := h2 ρ hρ n (rep g τ) (memLp_rep_slice g τ)
      have fh := h2 ρ hρ n (rep h τ) (memLp_rep_slice h τ)
      constructor
      · simpa [gate_of_mem hτ] using fg.2.1
      · simpa [gate_of_mem hτ] using fh.2.1
    · have e : ∀ F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3,
          (fun y => gate (A n) F (τ, y)) = fun _ => 0 := fun F => funext (gate_of_not_mem hτ)
      rw [e, e]
      exact ⟨MemLp.zero, MemLp.zero⟩
  · intro n
    refine ⟨(eLpNorm (ρ n) (UnforcedLeray.PhaseSpace.conjExp q) volume).toReal * n, ?_⟩
    rintro ⟨τ, y⟩
    show ‖gate (A n) (fun x => Moll (ρ n) (rep g x.1) x.2) (τ, y)‖ ≤ _
    by_cases hτ : τ ∈ A n
    · have fg := h2 ρ hρ n (rep g τ) (memLp_rep_slice g τ)
      rw [gate_of_mem hτ]
      refine (fg.2.2.1 y).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      have := ENNReal.toReal_mono (by simp) hτ.2
      simpa using this
    · rw [gate_of_not_mem hτ, norm_zero]; positivity
  · intro n
    have hmg := stronglyMeasurable_moll (hρ n |>.1.continuous) hrepg
    have hmh := stronglyMeasurable_moll (hρ n |>.1.continuous) hreph
    have hset : MeasurableSet {x : ℝ × UnforcedLeray.Space | x.1 ∈ A n} :=
      measurable_fst (hAmeas n)
    exact ⟨(hmg.indicator hset).aestronglyMeasurable, (hmh.indicator hset).aestronglyMeasurable⟩
  · exact h4 ρ hρ P (fun x => rep g x.1 x.2) hrepg (memLp_rep_phase g) A hAmeas hAcover
  · exact h4 ρ hρ P (fun x => rep h x.1 x.2) hreph (memLp_rep_phase h) A hAmeas hAcover

end UnforcedLeray.Short.PartIIIb.Concrete
