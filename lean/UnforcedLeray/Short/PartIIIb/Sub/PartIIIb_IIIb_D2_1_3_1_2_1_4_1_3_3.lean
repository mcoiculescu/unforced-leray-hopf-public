import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3

/-!
# `selComplete`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1341-1344, 1470-1480.
`Y_2` is an `L²` space over `(0,P] × ℝ³` (norm constant `P^{-1/2}`) of periodic functions.  A Cauchy
sequence has an `L²(0,P]×ℝ³` limit (Mathlib `Lp` completeness); the limit is extended periodically.
Only values on one period enter `phaseLpNorm`, so `YConv` and finiteness transfer exactly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `phaseLpNorm P 2 g = (P⁻¹)^{1/2} ‖g‖_{L²((0,P]×ℝ³)}` (source 1341-1344): Tonelli on the product
measure `volume = volume.prod volume` restricted to `Ioc 0 P ×ˢ univ`. -/
def SelNormEq : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ g : ℝ × Space → CVec3, AEStronglyMeasurable g volume →
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 g
      = ENNReal.ofReal P⁻¹ ^ (1 / 2 : ℝ)
        * eLpNorm g 2 (volume.restrict (Ioc (0 : ℝ) P ×ˢ (Set.univ : Set Space)))

/-- Completeness on one period (source 1341-1344): a `Y_2`-Cauchy sequence of members of `Y_2` has a
measurable limit `F0` of finite norm with `‖f n - F0‖_{Y_2} → 0` (no periodicity needed here:
`phaseLpNorm` only sees `t ∈ (0,P]`).  Sketch: `f n ∈ Lp ℂ-vector 2 (volume.restrict (Ioc 0 P ×ˢ
univ))` by `SelNormEq` and `IsInYr.finite`/`meas`; `eLpNorm (f n - f m)` is a constant multiple of
`phaseLpNorm (f n - f m)`, so the sequence is Cauchy in `Lp`; use `Lp` completeness
(`cauchySeq_tendsto_of_complete`), take `F0 := (limit).aestronglyMeasurable.mk` (a total measurable
function; `Memℒp`/`Lp.coeFn`), and transfer back with `SelNormEq` (`f n - F0` is a.e.-measurable). -/
def SelCompleteL1 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ f : ℕ → ℝ × Space → CVec3,
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (f n)) → YCauchy P f →
      ∃ F0 : ℝ × Space → CVec3, Measurable F0 ∧
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 F0 < ⊤ ∧ YConv P f F0

/-- `phaseLpNorm` only depends on the values on `Ioc 0 P`. -/
theorem phaseLpNorm_congr_Ioc (P r : ℝ) (f g : ℝ × Space → CVec3)
    (h : ∀ t ∈ Ioc (0 : ℝ) P, ∀ y : Space, f (t, y) = g (t, y)) :
    UnforcedLeray.Short.IIb.phaseLpNorm P r f = UnforcedLeray.Short.IIb.phaseLpNorm P r g := by
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  have : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖f (t, y)‖ₑ ^ r)
      = ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖g (t, y)‖ₑ ^ r := by
    refine setLIntegral_congr_fun (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) P)) ?_
    intro t ht
    simp [h t ht]
  rw [this]

/-- Periodic extension of a measurable function from `(0,P]` (source 1334-1337). -/
theorem selPerExt (P : ℝ) (hP : 0 < P) (F0 : ℝ × Space → CVec3) (hF0 : Measurable F0) :
    ∃ F : ℝ × Space → CVec3, Measurable F ∧ (∀ t y, F (t + P, y) = F (t, y)) ∧
      ∀ t ∈ Ioc (0 : ℝ) P, ∀ y, F (t, y) = F0 (t, y) := by
  refine ⟨fun x => F0 (x.1 - P * ((⌈x.1 / P⌉ : ℤ) - 1 : ℝ), x.2), ?_, ?_, ?_⟩
  · have : Measurable (fun x : ℝ × Space => (x.1 - P * ((⌈x.1 / P⌉ : ℤ) - 1 : ℝ), x.2)) := by
      have hc : Measurable (fun x : ℝ × Space => ((⌈x.1 / P⌉ : ℤ) : ℝ)) :=
        (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp (Int.measurable_ceil.comp
          (measurable_fst.div_const P))
      exact (measurable_fst.sub (measurable_const.mul (hc.sub measurable_const))).prodMk
        measurable_snd
    exact hF0.comp this
  · intro t y
    have : ⌈(t + P) / P⌉ = ⌈t / P⌉ + 1 := by
      rw [add_div, div_self hP.ne', Int.ceil_add_one]
    simp only [this]
    congr 2
    push_cast
    ring
  · intro t ht y
    have : ⌈t / P⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · simpa using div_pos ht.1 hP
      · simpa using (div_le_one hP).2 ht.2
    simp [this]

theorem selComplete_of (h1 : SelCompleteL1) : SelComplete := by
  intro P hP f hf hC
  obtain ⟨F0, hm, hfin, hconv⟩ := h1 P hP f hf hC
  obtain ⟨F, hFm, hFp, hFe⟩ := selPerExt P hP F0 hm
  have hn : UnforcedLeray.Short.IIb.phaseLpNorm P 2 F
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 F0 :=
    phaseLpNorm_congr_Ioc P 2 F F0 hFe
  refine ⟨F, ⟨Filter.Eventually.of_forall fun x => hFp x.1 x.2, hFm.aestronglyMeasurable,
    hn ▸ hfin⟩, ?_⟩
  have : ∀ n, UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => f n x - F x)
      = UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => f n x - F0 x) := fun n =>
    phaseLpNorm_congr_Ioc P 2 _ _ (fun t ht y => by simp [hFe t ht y])
  unfold YConv at hconv ⊢
  simpa only [this] using hconv

end UnforcedLeray.Short.PartIIIb.Concrete
