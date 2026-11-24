import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Props
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: `s ↦ 𝒫₀ Y(s)` has a jointly measurable version

Source of record: `the November 2 reference manuscript` lines 3427-3440.

`lmToL2vPath`: a jointly measurable field is a strongly measurable path in `L²(cell; ℝ²)`: the
distance from the path to any fixed class is measurable in `s` by Tonelli, and `L²(cell; ℝ²)` is
second countable. `lmP0Rep`: `Cyl.P0` is continuous, and a strongly measurable path has a jointly
measurable representative (`Infra.JointMeasurableRep.exists_stronglyMeasurable_rep`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Cyl in
/-- The distance from the path to a fixed class is measurable. -/
theorem lmToL2v_edist_measurable {c : ℝ} {f : ℝ × (ℝ × ℝ) → Vec2} (hf : Measurable f) (e : L2v c) :
    Measurable (fun s : ℝ => edist (toL2v c (fun x => f (s, x))) e) := by
  classical
  have hint : ∀ g : ℝ × (ℝ × ℝ) → Vec2, Measurable g →
      Measurable fun s : ℝ => ∫⁻ x, ‖g (s, x)‖ₑ ^ (2 : ℝ) ∂(cellμ c) := fun g hg =>
    Measurable.lintegral_prod_right' (hg.enorm.pow_const _)
  have hS : MeasurableSet {s : ℝ | MemLp (fun x => f (s, x)) 2 (cellμ c)} := by
    have heq : {s : ℝ | MemLp (fun x => f (s, x)) 2 (cellμ c)} =
        {s : ℝ | ∫⁻ x, ‖f (s, x)‖ₑ ^ (2 : ℝ) ∂(cellμ c) < ⊤} := by
      ext s
      have hm : AEStronglyMeasurable (fun x => f (s, x)) (cellμ c) :=
        (hf.comp measurable_prodMk_left).aestronglyMeasurable
      simp only [mem_setOf_eq, MemLp, hm, true_and]
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      simp
    rw [heq]
    exact measurableSet_lt (hint f hf) measurable_const
  have hem : Measurable (fun x : ℝ × ℝ => (e : ℝ × ℝ → Vec2) x) :=
    (Lp.stronglyMeasurable e).measurable
  have hdiff : Measurable fun p : ℝ × (ℝ × ℝ) => f p - (e : ℝ × ℝ → Vec2) p.2 :=
    hf.sub (hem.comp measurable_snd)
  have hval : ∀ s, MemLp (fun x => f (s, x)) 2 (cellμ c) →
      edist (toL2v c (fun x => f (s, x))) e =
        (∫⁻ x, ‖f (s, x) - (e : ℝ × ℝ → Vec2) x‖ₑ ^ (2 : ℝ) ∂(cellμ c)) ^ ((2 : ℝ)⁻¹) := by
    intro s hs
    have hto : toL2v c (fun x => f (s, x)) = hs.toLp _ := by
      unfold toL2v
      rw [dif_pos hs]
    rw [hto, Lp.edist_def]
    have hae : (⇑(hs.toLp (fun x => f (s, x))) - ⇑e) =ᵐ[cellμ c]
        fun x => f (s, x) - (e : ℝ × ℝ → Vec2) x := by
      filter_upwards [hs.coeFn_toLp] with x hx
      simp only [Pi.sub_apply, hx]
    rw [eLpNorm_congr_ae hae, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp
  have heq2 : (fun s : ℝ => edist (toL2v c (fun x => f (s, x))) e) = fun s =>
      if MemLp (fun x => f (s, x)) 2 (cellμ c) then
        (∫⁻ x, ‖f (s, x) - (e : ℝ × ℝ → Vec2) x‖ₑ ^ (2 : ℝ) ∂(cellμ c)) ^ ((2 : ℝ)⁻¹)
      else edist (0 : L2v c) e := by
    funext s
    by_cases hs : MemLp (fun x => f (s, x)) 2 (cellμ c)
    · rw [if_pos hs, hval s hs]
    · rw [if_neg hs]
      unfold toL2v
      rw [dif_neg hs]
  rw [heq2]
  exact Measurable.ite hS ((hint _ hdiff).pow_const _) measurable_const

/-- **A jointly measurable field is a strongly measurable path in `L²(cell; ℝ²)`.** -/
theorem lmToL2vPath : LMToL2vPath := by
  intro c _hc f hf
  borelize (↥(UnforcedLeray.Cyl.L2v c))
  set u : ℝ → UnforcedLeray.Cyl.L2v c := fun s => toL2v c (fun x => f (s, x)) with hu
  refine Measurable.stronglyMeasurable (measurable_of_isOpen fun U hU => ?_)
  let e : ℕ → UnforcedLeray.Cyl.L2v c := TopologicalSpace.denseSeq _
  have hball : ∀ (n m : ℕ), MeasurableSet {s : ℝ | dist (u s) (e n) < 1 / ((m : ℝ) + 1)} := by
    intro n m
    have h1 : {s : ℝ | dist (u s) (e n) < 1 / ((m : ℝ) + 1)} =
        {s : ℝ | edist (u s) (e n) < ENNReal.ofReal (1 / ((m : ℝ) + 1))} := by
      ext s
      simp only [mem_setOf_eq]
      rw [edist_lt_ofReal]
    rw [h1]
    exact measurableSet_lt (lmToL2v_edist_measurable hf (e n)) measurable_const
  have hrep : u ⁻¹' U = ⋃ (n : ℕ) (m : ℕ) (_ : Metric.ball (e n) (1 / ((m : ℝ) + 1)) ⊆ U),
      {s : ℝ | dist (u s) (e n) < 1 / ((m : ℝ) + 1)} := by
    ext s
    simp only [mem_preimage, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro hs
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU _ hs
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq _).exists_dist_lt (u s)
        (show 0 < 1 / ((m : ℝ) + 1) by positivity)
      refine ⟨n, m, fun w hw => hsub ?_, hn⟩
      rw [Metric.mem_ball] at hw ⊢
      calc dist w (u s) ≤ dist w (e n) + dist (e n) (u s) := dist_triangle _ _ _
        _ < 1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
            rw [dist_comm (e n)]
            exact add_lt_add hw hn
        _ < ε := by linarith
    · rintro ⟨n, m, hsub, hs⟩
      exact hsub hs
  rw [hrep]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    MeasurableSet.iUnion fun _ => hball n m

/-- **`s ↦ 𝒫₀ Y(s)` has a jointly measurable version.** -/
theorem lmP0Rep : LMP0Rep := by
  intro c hc Y hY
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := fact_one_le_two_ennreal
  have hvec : ∀ g : ℝ × (ℝ × ℝ) → ℂ × ℂ, Measurable g → Measurable fun p =>
      UnforcedLeray.Cyl.vec (g p).1.re (g p).2.re := fun g hg => by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    fin_cases i
    · exact Complex.measurable_re.comp hg.fst
    · exact Complex.measurable_re.comp hg.snd
  have hvec' : ∀ g : ℝ × (ℝ × ℝ) → ℂ × ℂ, Measurable g → Measurable fun p =>
      UnforcedLeray.Cyl.vec (g p).1.im (g p).2.im := fun g hg => by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
    fin_cases i
    · exact Complex.measurable_im.comp hg.fst
    · exact Complex.measurable_im.comp hg.snd
  have hg : Measurable fun p : ℝ × (ℝ × ℝ) => (Y p 0, Y p 1) := (hY 0).prodMk (hY 1)
  have h1 := lmToL2vPath c hc _ (hvec _ hg)
  have h2 := lmToL2vPath c hc _ (hvec' _ hg)
  have hP1 : StronglyMeasurable fun s => P0re c (fun y => Y (s, y)) :=
    (UnforcedLeray.Cyl.P0 c).continuous.comp_stronglyMeasurable h1
  have hP2 : StronglyMeasurable fun s => P0im c (fun y => Y (s, y)) :=
    (UnforcedLeray.Cyl.P0 c).continuous.comp_stronglyMeasurable h2
  obtain ⟨F₁, hF₁m, hF₁⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep hP1
  obtain ⟨F₂, hF₂m, hF₂⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep hP2
  refine ⟨fun p i => ((F₁ p i : ℝ) : ℂ) + Complex.I * ((F₂ p i : ℝ) : ℂ), fun i => ?_, fun s => ?_⟩
  · have hc₁ : Continuous fun v : UnforcedLeray.Cyl.Vec2 => v i := by fun_prop
    have m₁ : Measurable fun p => F₁ p i := (hc₁.comp_stronglyMeasurable hF₁m).measurable
    have m₂ : Measurable fun p => F₂ p i := (hc₁.comp_stronglyMeasurable hF₂m).measurable
    exact (Complex.measurable_ofReal.comp m₁).add
      (measurable_const.mul (Complex.measurable_ofReal.comp m₂))
  · rw [← cellμ_eq c]
    filter_upwards [hF₁ s, hF₂ s] with x hx₁ hx₂ i
    have h₁' : F₁ (s, x) = (P0re c fun y => Y (s, y)) x := hx₁
    have h₂' : F₂ (s, x) = (P0im c fun y => Y (s, y)) x := hx₂
    simp only [P0C, cplxOf, h₁', h₂']

end UnforcedLeray.Short.IIIa
