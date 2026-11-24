import UnforcedLeray.Short.PartIIb.Sub.T09
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.PairCont.Holder

/-!
# Part II-b, task `PartII-b:T09/3` (`DivCont`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

`DivCont` follows from a single linear bound `DivBound` for the functional
`(b, Qb, Eb) ↦ ⟪φ, sLift (gDiv ε b Qb Eb)⟫` in the norm
`‖b‖_{H_r} + ‖√s Qb‖_{H_r} + ‖√s Eb‖_{H_r}` (this file: `divCont_of`).  `DivBound` in turn is
the sum of two scalar Hölder estimates, both from `‖N_v G‖ = √s ‖G(chart)‖`
(`nvCPointwise`) and `phaseLpNorm_NvC`:
* `DivHolderH` (weight `√s`): `s Qb_i = √s (√s Qb)_i`;
* `DivHolderB` (weight `s`): `s b_i`, using `s = (‖N_v b‖/‖b‖)²` i.e. `s |b| = √s ‖N_v b‖` and
  `√s ∈ L^{r'}_loc` (`1/ρ ∈ L^{r'}_loc`, `r' < 2`, since `r > 2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- **Lemma `T09/3/1`** (SP 1912-1918, weight `√s`): for a phase test `φ` and `r > 2` there is `K`
with, for every `G ∈ H_r` and component `i`, the function
`φ · sLift(√s G_i)` integrable over the phase slab and
`‖⟪φ, sLift(√s G_i)⟫‖ ≤ K ‖G‖_{H_r}`. -/
def DivHolderH : Prop :=
  ∀ (c ε r : ℝ) (φ : ℝ × Space → ℂ), 0 < c → 0 < ε → 2 < r → IsPhaseTest (2 * ε * c) φ →
    ∃ K : ℝ, ∀ (G : CProf) (i : Fin 2), InHr c r G →
      Integrable (fun z => φ z * sLift ε⁻¹ (fun y => (Real.sqrt y.1 : ℂ) * G y i) z)
          (hSlab (2 * ε * c)) ∧
        ‖phaseInt (2 * ε * c)
            (fun z => φ z * sLift ε⁻¹ (fun y => (Real.sqrt y.1 : ℂ) * G y i) z)‖ ≤
          K * (hNorm c r G).toReal

/-- **Lemma `T09/3/2`** (SP 1912-1918, weight `s`, the `1/ρ` term): same with
`sLift(s G_i)` in place of `sLift(√s G_i)`; needs `φ/ρ ∈ L^{r'}` (`r > 2`). -/
def DivHolderB : Prop :=
  ∀ (c ε r : ℝ) (φ : ℝ × Space → ℂ), 0 < c → 0 < ε → 2 < r → IsPhaseTest (2 * ε * c) φ →
    ∃ K : ℝ, ∀ (G : CProf) (i : Fin 2), InHr c r G →
      Integrable (fun z => φ z * sLift ε⁻¹ (fun y => (y.1 : ℂ) * G y i) z)
          (hSlab (2 * ε * c)) ∧
        ‖phaseInt (2 * ε * c)
            (fun z => φ z * sLift ε⁻¹ (fun y => (y.1 : ℂ) * G y i) z)‖ ≤
          K * (hNorm c r G).toReal

/-- **Lemma `T09/3/3`**: the linear bound for the divergence functional on the graph norm
(no weak derivatives needed). -/
def DivBound : Prop :=
  ∀ (c ε r : ℝ) (φ : ℝ × Space → ℂ), 0 < c → 0 < ε → 2 < r → IsPhaseTest (2 * ε * c) φ →
    ∃ K : ℝ, ∀ (b Qb Eb : CProf), InHr c r b → InHr c r (sqrtS Qb) → InHr c r (sqrtS Eb) →
      Integrable (fun z => φ z * sLift ε⁻¹ (gDiv ε b Qb Eb) z) (hSlab (2 * ε * c)) ∧
        ‖phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x)‖ ≤
          K * ((hNorm c r b).toReal + (hNorm c r (sqrtS Qb)).toReal +
            (hNorm c r (sqrtS Eb)).toReal)

theorem inHr_sub {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r f) (hg : InHr c r g) :
    InHr c r (fun x => f x - g x) := by
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  refine ⟨?_, hf.meas.sub hg.meas, ?_⟩
  · filter_upwards [hf.periodic, hg.periodic] with x h1 h2
    simp only [h1, h2]
  · have := eLpNorm_sub_le (μ := hMeas c r) (p := ENNReal.ofReal r) hf.meas hg.meas hr1
    exact lt_of_le_of_lt this (ENNReal.add_lt_top.2 ⟨hf.finite, hg.finite⟩)

theorem inHr_sqrtS_sub {c r : ℝ} (hr : 1 < r) {f g : CProf} (hf : InHr c r (sqrtS f))
    (hg : InHr c r (sqrtS g)) : InHr c r (sqrtS fun x => f x - g x) := by
  have e : (sqrtS fun x => f x - g x) = fun x => sqrtS f x - sqrtS g x := by
    funext x; simp [sqrtS, smul_sub]
  rw [e]; exact inHr_sub hr hf hg

theorem hNorm_toReal_ne {c r : ℝ} {f : CProf} (hf : InHr c r f) : hNorm c r f ≠ ⊤ :=
  hf.finite.ne

theorem divCont_of (h : DivBound) : DivCont := by
  intro c ε r φ b Qb Eb bn Qbn Ebn hc hε hr hφ hd hdn t1 t2 t3
  have hr1 : 1 < r := by linarith
  obtain ⟨K, hK⟩ := h c ε r φ hc hε hr hφ
  set P : ℝ := 2 * ε * c with hP
  have hb := hK b Qb Eb hd.inHr hd.inQ hd.inE
  have hbn : ∀ n, _ := fun n => hK (bn n) (Qbn n) (Ebn n) (hdn n).inHr (hdn n).inQ (hdn n).inE
  -- difference triple
  have hdiff : ∀ n, Integrable (fun z => φ z * sLift ε⁻¹
        (gDiv ε (fun x => bn n x - b x) (fun x => Qbn n x - Qb x) (fun x => Ebn n x - Eb x)) z)
        (hSlab P) ∧
      ‖phaseInt P (fun x => φ x * sLift ε⁻¹
        (gDiv ε (fun x => bn n x - b x) (fun x => Qbn n x - Qb x) (fun x => Ebn n x - Eb x)) x)‖
        ≤ K * ((hNorm c r (fun x => bn n x - b x)).toReal +
          (hNorm c r (sqrtS fun x => Qbn n x - Qb x)).toReal +
          (hNorm c r (sqrtS fun x => Ebn n x - Eb x)).toReal) := fun n =>
    hK _ _ _ (inHr_sub hr1 (hdn n).inHr hd.inHr) (inHr_sqrtS_sub hr1 (hdn n).inQ hd.inQ)
      (inHr_sqrtS_sub hr1 (hdn n).inE hd.inE)
  have hpt : ∀ n, (fun z => φ z * sLift ε⁻¹
        (gDiv ε (fun x => bn n x - b x) (fun x => Qbn n x - Qb x) (fun x => Ebn n x - Eb x)) z) =
      fun z => φ z * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) z -
        φ z * sLift ε⁻¹ (gDiv ε b Qb Eb) z := by
    intro n; funext z
    simp only [sLift, gDiv, PiLp.sub_apply]
    ring
  have hlin : ∀ n, phaseInt P (fun z => φ z * sLift ε⁻¹
        (gDiv ε (fun x => bn n x - b x) (fun x => Qbn n x - Qb x) (fun x => Ebn n x - Eb x)) z) =
      phaseInt P (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x) -
        phaseInt P (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) := by
    intro n
    have i1 := (hbn n).1
    have i2 := hb.1
    have i3 : Integrable (fun z => φ z * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) z -
        φ z * sLift ε⁻¹ (gDiv ε b Qb Eb) z) (hSlab P) := i1.sub i2
    rw [hpt n, phaseInt_eq_slab i3, phaseInt_eq_slab i1, phaseInt_eq_slab i2,
      integral_sub i1 i2, smul_sub]
  have ht : Tendsto (fun n => K * ((hNorm c r (fun x => bn n x - b x)).toReal +
          (hNorm c r (sqrtS fun x => Qbn n x - Qb x)).toReal +
          (hNorm c r (sqrtS fun x => Ebn n x - Eb x)).toReal)) atTop (𝓝 0) := by
    have tr : ∀ {f : ℕ → ℝ≥0∞}, Tendsto f atTop (𝓝 0) →
        Tendsto (fun n => (f n).toReal) atTop (𝓝 0) := fun {f} hf => by
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hf
    have := (((tr t1).add (tr t2)).add (tr t3)).const_mul K
    simpa using this
  have hsq : Tendsto (fun n => phaseInt P (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x) -
      phaseInt P (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) ht
    rw [← hlin n]
    exact (hdiff n).2
  simpa using hsq.add_const (phaseInt P (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x))

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divCont_of
