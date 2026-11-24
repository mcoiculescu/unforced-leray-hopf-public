import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.ThinMass
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window
import UnforcedLeray.Lib.Axisymmetric.Measure

/-!
# `PartIII-b:C/rep/5/1/1/3`: the single-term per-bin velocity bound, reduced

Source `the November 2 reference manuscript`
5569-5593 (thin mass `N₀(a) ≤ C(a^{-3/4}+a^{-1/2})‖T‖_{Z₁}`; logarithmic output bins of width
`h < δ/2`; on a bin of upper age `s` all source ages exceed `e^{δ-h}s`, uniform radial gap
`D ≍ R/√s`; the order-four kernel has spatial `L²` norm `C D^{-5/2}`; Minkowski and the mass
estimate bound the normalized velocity on the bin by `C ε^{3/2}(s^{1/2}+s^{3/4})‖T‖_{Z₁}`),
3902-3912 (the far mask `1_{s<S, t>e^δ s}` and its kernel realization), 3604-3621 (the kernel
bound `|∇K_t(x)| ≤ C|x|^{-4}` and the resolvent `W_μ`).

The kernel estimate is applied to `thinPart T` itself, with no splitting by source age: sources of
age `< e^{δ-h}s` do not reach the bin `(s e^{-h}, s]` (mask `t > e^δ u`, `u > s e^{-h}`).

Chain (each arrow proved here):

* `PerBinVelocitySeq` (the target, `PartIII-b_C_rep_5_1_1Org.lean`) ⇐ `TailBinGenSeq`
  (`perBinVelocitySeq_of`; `BinGenAt` with no regime restriction `allQ`, applied to `thinPart T`);
* `TailBinGenSeq` ⇐ `BinDensityTransfer` (box tensors to all thin stresses by density,
  `BoxDenseZ`; sibling task `/3/2/2`) and `TailBoxBinSeq` (`tailBinGenSeq_of`);
* `TailBoxBinSeq` ⇐ `TailBoxThinSeq` and the thin mass bound `thinMassBoundSlice`
  (`tailBoxBinSeq_of`; `s^{5/4}(a^{-3/4}+a^{-1/2}) ≤ s^{1/2}+s^{3/4}` for `a = e^{δ-h}s ≥ s`);
* `TailBoxThinSeq` (box level, `ε^{3/2} s^{5/4} N₀(e^{δ-h}s)`) ⇐ `FarPointDom` (pointwise
  domination of the masked far response by the order-four gap-kernel majorant `wardYChartMaj`)
  and `TailMajBinSeq` (`tailBoxThinSeq_of`; `srcMeasure = π · ageμ(-3/2)`, window `μ > -1/4`);
* `TailMajBinSeq` ⇐ `WardYMajBinCore` (the chart bin `L²` bound of the majorant, order-four
  kernel `L²` norm `C D^{-5/2}` and Minkowski; task `PartIII-b:C/rep/5/1/2/4/1/3/3`) and
  `AgeMassLeThin` (`L¹_q` mass `≤` `L²_q` mass) (`tailMajBinSeq_of`; the bin of width `h < δ/2`
  is covered by two bins of width `δ/4`, and the majorant on the bin only sees sources of age
  `> e^{δ-h}s`, `wardYChartMaj_congr`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The statements -/

/-- No restriction on the source age (the single-term bound of 5585-5593). -/
def allQ : ℝ → ℝ → ℝ → Prop := fun _ _ _ => True

theorem measurable_allQ (h s : ℝ) : MeasurableSet {t : ℝ | allQ h s t} := by
  simp [allQ]

theorem z1Part_allQ (c mZ a h s : ℝ) (F : Chart → Ten3) :
    z1Part c mZ (fun t => a ≤ t ∧ allQ h s t) F = z1Tail c mZ a F := by
  simp only [allQ, and_true, z1Tail]

/-- The masked far response of a chart tensor field at a level (3905-3912 with `sep:resolvent`
3611-3621): the right side of the pin `IsFarMaskG` below the output cut. -/
def farBoxResp (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (f : Chart → Ten3) :
    Chart → Merid :=
  fun p => (Real.sqrt p.1)⁻¹ • NearInst.merRe (-NearInst.sepWfar L.ν (μ : ℂ) L.ε⁻¹ K.δ p.1
    (NearInst.cartLift L.ε⁻¹ (cOf L.ν) f) (NearInst.chartY L.ε⁻¹ p) (NearInst.chartTau L.ε⁻¹ p))

/-- **Single-term bound for all thin stresses** (5585-5593), sequence level: `BinGenAt` with no
regime restriction and `ε^{3/2}`. -/
def TailBinGenSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      BinGenAt D.Pl D.K (D.level n) (D.mu n z) allQ (3 / 2 : ℝ) C k

/-- **Single-term bound for box tensors** (5585-5593), sequence level: `BinBoxAt` with no regime
restriction and `ε^{3/2}`. -/
def TailBoxBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      BinBoxAt D.Pl D.K (D.level n) (D.mu n z) allQ (3 / 2 : ℝ) C k

/-- **Box-level single-term core in terms of the thin mass** (5585-5593): for a box tensor `f`,
the bin `(s e^{-h}, s]` norm of the masked far response is at most
`C ν^{-k} ε^{3/2} s^{5/4} N₀(e^{δ-h}s)`. -/
def TailBoxThinAt (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K →
    ∀ f : Chart → Ten3, NearInst.IsBoxTensor f →
      velBin (cOf L.ν) (s * Real.exp (-h)) s (farBoxResp K L μ f) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)) *
          thinMass (cOf L.ν) f (Real.exp (K.δ - h) * s)

/-- Sequence-level `TailBoxThinAt`. -/
def TailBoxThinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      TailBoxThinAt D.K (D.level n) (D.mu n z) C k

/-- **The order-four kernel bound** (`sep:kernel`, 3604-3610, `IIIa.SepKernelBounds` with `j = 0`):
`|∂_k (K_t)_{ij}(x)| ≤ C |x|^{-4}` for `t > 0`, `x ≠ 0`. -/
def FarKerDeriv (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : Space, x ≠ 0 → ∀ i j k : Fin 3,
    ‖fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) x (coordinateVector k)‖ ≤
      C * (‖x‖ ^ 4)⁻¹

/-- **Pointwise domination of the masked far response** (3604-3621, 3905-3912, 5588-5589): at a
chart point of positive age `s = p.1`, the sources kept by the mask `t > e^δ s` are exactly those
of horizontal radius `ϱ(z) < θ ϱ(y)`, `θ = e^{-δ/2}`, `y = chartY R p`; there `|y - λz| ≥
(1-θ)ϱ(y) > 0`, `|∇K_{ν(1-λ²)}(y-λz)| ≤ C|y-λz|^{-4}` and `|λ^{2μ+2}| ≤ 1` (`μ > -1/4`), so the
response is dominated by the gap-kernel majorant `wardYChartMaj`. -/
def FarPointDom (C : ℝ) : Prop :=
  ∀ (ν μ R c δ : ℝ), 0 < ν → 0 < R → -(1 / 4) < μ → 0 < δ →
    ∀ (f : Chart → Ten3) (p : Chart), 0 < p.1 →
      ‖(Real.sqrt p.1)⁻¹ • NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1
          (NearInst.cartLift R c f) (NearInst.chartY R p) (NearInst.chartTau R p))‖ₑ ≤
        ENNReal.ofReal C * wardYChartMaj R c (Real.exp (-(δ / 2))) f p

/-- The `ageμ c (-3/2)` `L²` norm of the gap-kernel majorant over the output ages `(s₀, s₁]`. -/
def majBin (R c θ s₀ s₁ : ℝ) (g : Chart → Ten3) : ℝ≥0∞ :=
  (∫⁻ p in {p : Chart | s₀ < p.1 ∧ p.1 ≤ s₁}, wardYChartMaj R c θ g p ^ (2 : ℝ)
    ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ)

/-- **The majorant on one bin, with the thin mass** (5585-5593): for a bin `(s e^{-h}, s]` with
`0 < h < δ/2` and a measurable source, the `L²` norm of the majorant is at most
`C ν^{-k} ε^{3/2} s^{5/4} N₀(e^{δ-h}s)`. -/
def TailMajBinAt (K : ReturnConsts) (L : ReturnLevel) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → ∀ g : Chart → Ten3, Measurable g →
    majBin L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) (s * Real.exp (-h)) s g ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)) *
        thinMass (cOf L.ν) g (Real.exp (K.δ - h) * s)

/-- Sequence-level `TailMajBinAt`. -/
def TailMajBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, TailMajBinAt D.K (D.level n) C k

/-- **`L¹_q` mass below `L²_q` mass** (5569-5575): the age mass `ageMass c a g` (the `L¹` norm of
`g` over the ages `> a` for `ageμ c (-3/2)`, normalized cell measure `c⁻¹ dq`) is at most the thin
mass `N₀(a) = ∫_a^∞ t^{-3/2} ∫ ‖g(t,·,η)‖_{L²_q} dη dt` (Cauchy–Schwarz on the cell of length
`c`). -/
def AgeMassLeThin : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (a : ℝ) (g : Chart → Ten3), Measurable g → ageMass c a g ≤ thinMass c g a

/-! ## 2. All thin stresses from box tensors -/

theorem perBinAt_of_gen {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ C : ℝ} {k : ℕ}
    (hG : BinGenAt Pl K L μ allQ (3 / 2 : ℝ) C k) : PerBinVelocityAt Pl K L μ C k := by
  intro h s hh hhδ hs hsS Sf hSf T
  have hb := hG h s hh hhδ hs hsS Sf hSf (thinPart T) (thinPart_thinPart T)
    (Eventually.of_forall fun p hp => (hp trivial).elim)
  rwa [z1Part_allQ] at hb

/-- **The per-bin velocity bound** (5585-5593) from the single-term bound for thin stresses. -/
theorem perBinVelocitySeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hG : TailBinGenSeq Pl σ₀ mZ dm dp) : PerBinVelocitySeq Pl σ₀ mZ dm dp := by
  intro D h1 h2 h3 h4
  obtain ⟨C, k, hev⟩ := hG D h1 h2 h3 h4
  exact ⟨C, k, hev.mono fun n hn z hz => perBinAt_of_gen (hn z hz)⟩

/-- Thin stresses from box tensors (3905-3912, the pin on the dense class). -/
theorem tailBinGenSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hT : BinDensityTransfer)
    (hB : TailBoxBinSeq Pl σ₀ mZ dm dp) : TailBinGenSeq Pl σ₀ mZ dm dp := by
  intro D h1 h2 h3 h4
  obtain ⟨C, k, hev⟩ := hB D h1 h2 h3 h4
  exact ⟨C, k, hev.mono fun n hn z hz =>
    hT _ _ h4.C0_pos _ _ _ _ _ _ measurable_allQ (hn z hz)⟩

/-! ## 3. Box tensors: the thin mass bound -/

/-- The restriction of `f` to the source ages `≥ a`. -/
def tailRestr (a : ℝ) (f : Chart → Ten3) : Chart → Ten3 := fun p => if a ≤ p.1 then f p else 0

theorem tailRestr_measurable (a : ℝ) {f : Chart → Ten3} (hf : Measurable f) :
    Measurable (tailRestr a f) :=
  Measurable.ite (measurableSet_le measurable_const measurable_fst) hf measurable_const

theorem thinMass_tailRestr (c a : ℝ) (f : Chart → Ten3) :
    thinMass c (tailRestr a f) a = thinMass c f a := by
  unfold thinMass
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : a ≤ t := le_of_lt ht
  beta_reduce
  congr 1
  apply lintegral_congr
  intro η
  unfold sliceL2q
  congr 1
  apply lintegral_congr
  intro q
  simp [tailRestr, ht']

theorem z1Norm_tailRestr (c mZ a : ℝ) (f : Chart → Ten3) :
    z1Norm c mZ (tailRestr a f) = z1Tail c mZ a f := by
  have hS : MeasurableSet {p : Chart | a ≤ p.1} := measurableSet_le measurable_const measurable_fst
  unfold z1Norm z1Tail z1Part
  congr 1
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro p
  by_cases h : a ≤ p.1
  · have hp : p ∈ {p : Chart | a ≤ p.1} := h
    simp [tailRestr, h]
  · have hp : p ∉ {p : Chart | a ≤ p.1} := h
    simp [tailRestr, h]

theorem tailBoxBinAt_of {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ C1 : ℝ}
    {k : ℕ} (Cm : ℝ)
    (hCm : ∀ (c : ℝ), 0 < c → ∀ a : ℝ, 0 < a → ∀ F : Chart → Ten3, Measurable F →
      thinMass c F a ≤ ENNReal.ofReal (Cm * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) *
        z1Norm c K.mZ F)
    (hG : TailBoxThinAt K L μ C1 k) :
    BinBoxAt Pl K L μ allQ (3 / 2 : ℝ) (|C1| * |Cm|) k := by
  intro h s h0 h1 hs hS f hbox _
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := by unfold cOf; positivity
  rw [z1Part_allQ]
  set a : ℝ := Real.exp (K.δ - h) * s with ha
  have hexp : 1 ≤ Real.exp (K.δ - h) := Real.one_le_exp (by linarith)
  have hsa : s ≤ a := by rw [ha]; nlinarith
  have hapos : 0 < a := lt_of_lt_of_le hs hsa
  have hm := hCm _ hc a hapos _ (tailRestr_measurable a hbox.measurable)
  rw [thinMass_tailRestr, z1Norm_tailRestr] at hm
  have hmain := hG h s h0 h1 hs hS f hbox
  set N : ℝ := L.ν⁻¹ ^ k with hN
  have hN0 : 0 ≤ N := by positivity
  have hE0 : 0 ≤ L.ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hε.le _
  have hs54 : 0 ≤ s ^ (5 / 4 : ℝ) := Real.rpow_nonneg hs.le _
  set A' : ℝ := |C1| * N * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  have hB : Cm * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)) ≤
      |Cm| * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hA : C1 * N * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) ≤ A' := by
    rw [hA']
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hN0) hE0) hs54
  have e1 : a ^ (-3 / 4 : ℝ) ≤ s ^ (-3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hs hsa (by norm_num)
  have e2 : a ^ (-1 / 2 : ℝ) ≤ s ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hs hsa (by norm_num)
  have f1 : s ^ (5 / 4 : ℝ) * s ^ (-3 / 4 : ℝ) = s ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hs]; norm_num
  have f2 : s ^ (5 / 4 : ℝ) * s ^ (-1 / 2 : ℝ) = s ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hs]; norm_num
  have hreal : A' * (|Cm| * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) ≤
      |C1| * |Cm| * N * L.ε ^ (3 / 2 : ℝ) * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ)) := by
    have : s ^ (5 / 4 : ℝ) * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)) ≤
        s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ) := by
      rw [← f1, ← f2, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left e1 hs54) (mul_le_mul_of_nonneg_left e2 hs54)
    have hK : 0 ≤ |C1| * |Cm| * N * L.ε ^ (3 / 2 : ℝ) := by positivity
    calc A' * (|Cm| * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)))
        = |C1| * |Cm| * N * L.ε ^ (3 / 2 : ℝ) *
            (s ^ (5 / 4 : ℝ) * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) := by rw [hA']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hK
  calc _ ≤ _ := hmain
    _ ≤ ENNReal.ofReal A' * (ENNReal.ofReal (|Cm| * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ))) *
          z1Tail (cOf L.ν) K.mZ a f) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hA)
          (hm.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hB) le_rfl))
    _ = ENNReal.ofReal (A' * (|Cm| * (a ^ (-3 / 4 : ℝ) + a ^ (-1 / 2 : ℝ)))) *
          z1Tail (cOf L.ν) K.mZ a f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hA'0]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- The box-level single-term bound from its thin-mass form and the thin mass bound (5569-5584). -/
theorem tailBoxBinSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hG : TailBoxThinSeq Pl σ₀ mZ dm dp) : TailBoxBinSeq Pl σ₀ mZ dm dp := by
  intro D h1 h2 h3 h4
  obtain ⟨C1, k, hev⟩ := hG D h1 h2 h3 h4
  obtain ⟨Cm, hCm⟩ := thinMassBoundSlice D.K.mZ h4.mZ_gt
  refine ⟨|C1| * |Cm|, k, hev.mono fun n hn z hz => ?_⟩
  exact tailBoxBinAt_of Cm hCm (hn z hz)

/-! ## 4. Box tensors: pointwise domination and the majorant -/

theorem tailBoxThinAt_of {K : ReturnConsts} {L : ReturnLevel} {μ C1 C2 : ℝ} {k : ℕ}
    (hμ : -(1 / 4) < μ) (hδ : 0 < K.δ) (hP : FarPointDom C1) (hM : TailMajBinAt K L C2 k) :
    TailBoxThinAt K L μ (Real.sqrt Real.pi * |C1| * |C2|) k := by
  intro h s hh hhδ hs hsS f hbox
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hBm : MeasurableSet {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  set A : ℝ≥0∞ := ENNReal.ofReal C1 with hAdef
  set M : Chart → ℝ≥0∞ := wardYChartMaj L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) f with hMdef
  set I : ℝ≥0∞ := ∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s}, M p ^ (2 : ℝ)
    ∂(ageμ (cOf L.ν) (-3 / 2)) with hIdef
  have hpt : ∀ p ∈ {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
      ‖farBoxResp K L μ f p‖ₑ ^ (2 : ℝ) ≤ A ^ (2 : ℝ) * M p ^ (2 : ℝ) := by
    intro p hp
    have hp0 : 0 < p.1 := lt_trans (mul_pos hs (Real.exp_pos _)) hp.1
    have h1 := hP L.ν μ L.ε⁻¹ (cOf L.ν) K.δ hν hR hμ hδ f p hp0
    calc ‖farBoxResp K L μ f p‖ₑ ^ (2 : ℝ) ≤ (A * M p) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = A ^ (2 : ℝ) * M p ^ (2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hAt : A ^ (2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hI : ∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
      ‖farBoxResp K L μ f p‖ₑ ^ (2 : ℝ) ∂srcMeasure (cOf L.ν) ≤
      ENNReal.ofReal Real.pi * (A ^ (2 : ℝ) * I) := by
    rw [srcMeasure, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul' le_rfl ?_
    calc ∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
          ‖farBoxResp K L μ f p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2)
        ≤ ∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
          A ^ (2 : ℝ) * M p ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2) := setLIntegral_mono' hBm hpt
      _ = A ^ (2 : ℝ) * I := lintegral_const_mul' _ _ hAt
  have hmaj : I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (C2 * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) *
      s ^ (5 / 4 : ℝ)) * thinMass (cOf L.ν) f (Real.exp (K.δ - h) * s) :=
    hM h s hh hhδ hs f hbox.measurable
  have hsq : ENNReal.ofReal Real.pi ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt Real.pi) := by
    rw [ENNReal.ofReal_rpow_of_nonneg Real.pi_pos.le (by norm_num), Real.sqrt_eq_rpow]
  have hA2 : (A ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = A := by
    rw [← ENNReal.rpow_mul]; norm_num
  have hX0 : 0 ≤ L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hε.le _))
      (Real.rpow_nonneg hs.le _)
  have hC2 : C2 * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) ≤
      |C2| * (L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C2) hX0
    calc C2 * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)
        = C2 * (L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)) := by ring
      _ ≤ _ := this
  have hAle : A ≤ ENNReal.ofReal |C1| := ENNReal.ofReal_le_ofReal (le_abs_self _)
  unfold velBin
  calc (∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
          ‖farBoxResp K L μ f p‖ₑ ^ (2 : ℝ) ∂srcMeasure (cOf L.ν)) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal Real.pi * (A ^ (2 : ℝ) * I)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt Real.pi) * A * I ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq, hA2, mul_assoc]
    _ ≤ ENNReal.ofReal (Real.sqrt Real.pi) * ENNReal.ofReal |C1| *
          (ENNReal.ofReal (|C2| * (L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ))) *
            thinMass (cOf L.ν) f (Real.exp (K.δ - h) * s)) := by
        gcongr
        exact hmaj.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC2) le_rfl)
    _ = ENNReal.ofReal (Real.sqrt Real.pi * |C1| * |C2| * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) *
          s ^ (5 / 4 : ℝ)) * thinMass (cOf L.ν) f (Real.exp (K.δ - h) * s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- The box-level single-term core (5585-5593) from the pointwise domination and the majorant
bin bound, along the sequence (window `μ > -1/4`, `muWin_gt_quarter`). -/
theorem tailBoxThinSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hP : ∃ C : ℝ, FarPointDom C)
    (hM : TailMajBinSeq Pl σ₀ mZ dm dp) : TailBoxThinSeq Pl σ₀ mZ dm dp := by
  intro D h1 h2 h3 hst
  obtain ⟨C1, hC1⟩ := hP
  obtain ⟨C2, k, hev⟩ := hM D h1 h2 h3 hst
  refine ⟨Real.sqrt Real.pi * |C1| * |C2|, k, ?_⟩
  filter_upwards [hev, muWin_gt_quarter D hst] with n hn hμ z hz
  exact tailBoxThinAt_of (hμ z hz) hst.δ_pos hC1 hn

/-! ## 5. The majorant on one bin -/

/-- On the output bin the majorant only sees sources older than `p.1 / θ²`
(`ϱ(z) < θ ϱ(y)` with `ϱ(chartY R p) = R/√p.1`; on the axis `cartLift` vanishes). -/
theorem wardYChartMaj_congr {R c θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) (f g : Chart → Ten3)
    (p : Chart) (hp : 0 < p.1) (hfg : ∀ q : Chart, p.1 / θ ^ 2 < q.1 → f q = g q) :
    wardYChartMaj R c θ f p = wardYChartMaj R c θ g p := by
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hy0 : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    have h0 : (NearInst.chartY R p) 0 = R / Real.sqrt p.1 := rfl
    have h1 : (NearInst.chartY R p) 1 = 0 := rfl
    rw [ϱ, h0, h1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    exact Real.sqrt_sq (div_pos hR hsq).le
  have hS : MeasurableSet {z : Space | ϱ z < θ * ϱ (NearInst.chartY R p)} :=
    measurableSet_lt measurable_ϱ measurable_const
  have hkey : ∀ z ∈ {z : Space | ϱ z < θ * ϱ (NearInst.chartY R p)}, ∀ τ' : ℝ,
      NearInst.cartLift R c f τ' z = NearInst.cartLift R c g τ' z := by
    intro z hz τ'
    have hsm : (NearInst.chartOf R c z τ').1 • NearInst.nsSym (f (NearInst.chartOf R c z τ')) =
        (NearInst.chartOf R c z τ').1 • NearInst.nsSym (g (NearInst.chartOf R c z τ')) := by
      by_cases h0 : (NearInst.chartOf R c z τ').1 = 0
      · rw [h0, zero_smul, zero_smul]
      · have hq : (NearInst.chartOf R c z τ').1 = R ^ 2 / NearInst.hRad z ^ 2 := rfl
        have hz' : NearInst.hRad z < θ * R / Real.sqrt p.1 := by
          have h := hz
          simp only [mem_ofPred_eq, hy0] at h
          rw [mul_div_assoc]
          exact h
        have hh0 : 0 ≤ NearInst.hRad z := Real.sqrt_nonneg _
        have hhpos : 0 < NearInst.hRad z := by
          rcases hh0.lt_or_eq with h | h
          · exact h
          · exfalso; apply h0; rw [hq, ← h]; simp
        have h1 : NearInst.hRad z * Real.sqrt p.1 < θ * R := (lt_div_iff₀ hsq).1 hz'
        have h2 : (NearInst.hRad z * Real.sqrt p.1) ^ 2 < (θ * R) ^ 2 :=
          pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
        rw [mul_pow, Real.sq_sqrt hp.le] at h2
        rw [hfg]
        rw [hq, div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    simp only [NearInst.cartLift, hsm]
  unfold wardYChartMaj wardYKerMaj
  congr 1
  apply lintegral_congr
  intro l
  apply setLIntegral_congr_fun hS
  intro z hz
  simp only [UnforcedLeray.Short.IIIa.srcNorm, oldPhys, hkey z hz]

theorem tailMajBinAt_of {K : ReturnConsts} {L : ReturnLevel} {C0 : ℝ}
    (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (hA : AgeMassLeThin)
    (hC0 : ∀ (R c S : ℝ), 0 < R → 0 < c → ∀ (j : ℕ) (g : Chart → Ten3), Measurable g →
      (∫⁻ p in binSet S (K.δ / 4) j,
          wardYChartMaj R c (Real.exp (-(K.δ / 2))) g p ^ (2 : ℝ) ∂(ageμ c (-3 / 2))) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C0 * (1 + c / R) * R ^ (-(3 / 2 : ℝ)) * binUpper S (K.δ / 4) j ^ (5 / 4 : ℝ)) *
          ageMass c (Real.exp (K.δ - K.δ / 4) * binUpper S (K.δ / 4) j) g) :
    TailMajBinAt K L (4 * |C0|) 2 := by
  intro h s hh hhδ hs g hg
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := by unfold cOf; positivity
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  set a : ℝ := Real.exp (K.δ - h) * s with hadef
  set g' : Chart → Ten3 := fun p => if a < p.1 then g p else 0 with hg'def
  have hg' : Measurable g' :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) hg measurable_const
  have hBm : MeasurableSet {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have hθ : 0 < Real.exp (-(K.δ / 2)) := Real.exp_pos _
  have hθ2 : Real.exp (-(K.δ / 2)) ^ 2 = Real.exp (-K.δ) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have ha_eq : a = Real.exp K.δ * (s * Real.exp (-h)) := by
    rw [hadef, show K.δ - h = K.δ + -h by ring, Real.exp_add]; ring
  -- locality on the bin
  have hloc : ∀ p ∈ {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
      wardYChartMaj L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) g p ^ (2 : ℝ) =
        wardYChartMaj L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) g' p ^ (2 : ℝ) := by
    intro p hp
    have hp0 : 0 < p.1 := lt_trans (mul_pos hs (Real.exp_pos _)) hp.1
    rw [wardYChartMaj_congr hR hθ g g' p hp0]
    intro q hq
    have hpq : p.1 / Real.exp (-(K.δ / 2)) ^ 2 = Real.exp K.δ * p.1 := by
      rw [hθ2, Real.exp_neg, div_inv_eq_mul, mul_comm]
    have haq : a < q.1 := by
      have : a < Real.exp K.δ * p.1 := by
        rw [ha_eq]; exact mul_lt_mul_of_pos_left hp.1 (Real.exp_pos _)
      linarith [hpq ▸ hq]
    simp [hg'def, haq]
  -- two bins of width `δ/4` cover the bin
  have e0 : binUpper s (K.δ / 4) 0 = s := by simp [binUpper]
  have e1 : binUpper s (K.δ / 4) 1 = s * Real.exp (-(K.δ / 4)) := by simp [binUpper]
  have e2 : binUpper s (K.δ / 4) 2 = s * Real.exp (-(K.δ / 2)) := by
    unfold binUpper; congr 2; push_cast; ring
  have hcover : {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s} ⊆
      binSet s (K.δ / 4) 0 ∪ binSet s (K.δ / 4) 1 := by
    intro p hp
    have hlt : s * Real.exp (-(K.δ / 2)) < p.1 := by
      have : Real.exp (-(K.δ / 2)) < Real.exp (-h) := Real.exp_lt_exp.2 (by linarith)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left this.le hs.le) hp.1
    by_cases h4 : s * Real.exp (-(K.δ / 4)) < p.1
    · left
      show binUpper s (K.δ / 4) (0 + 1) < p.1 ∧ p.1 ≤ binUpper s (K.δ / 4) 0
      rw [zero_add, e0, e1]; exact ⟨h4, hp.2⟩
    · right
      show binUpper s (K.δ / 4) (1 + 1) < p.1 ∧ p.1 ≤ binUpper s (K.δ / 4) 1
      rw [e1, show (1 + 1 : ℕ) = 2 from rfl, e2]; exact ⟨hlt, not_lt.1 h4⟩
  set M' : Chart → ℝ≥0∞ := fun p =>
    wardYChartMaj L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) g' p ^ (2 : ℝ) with hM'
  have hI : ∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
      wardYChartMaj L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) g p ^ (2 : ℝ)
        ∂(ageμ (cOf L.ν) (-3 / 2)) ≤
      (∫⁻ p in binSet s (K.δ / 4) 0, M' p ∂(ageμ (cOf L.ν) (-3 / 2))) +
        ∫⁻ p in binSet s (K.δ / 4) 1, M' p ∂(ageμ (cOf L.ν) (-3 / 2)) := by
    calc _ = ∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s}, M' p
            ∂(ageμ (cOf L.ν) (-3 / 2)) := setLIntegral_congr_fun hBm hloc
      _ ≤ ∫⁻ p in binSet s (K.δ / 4) 0 ∪ binSet s (K.δ / 4) 1, M' p
            ∂(ageμ (cOf L.ν) (-3 / 2)) := lintegral_mono_set hcover
      _ ≤ _ := lintegral_union_le _ _ _
  -- the mass of the restricted source
  have hmass : ∀ t : ℝ, ageMass (cOf L.ν) t g' ≤ thinMass (cOf L.ν) g a := by
    intro t
    have hSa : MeasurableSet {p : Chart | a < p.1} := measurableSet_lt measurable_const measurable_fst
    calc ageMass (cOf L.ν) t g' ≤ ∫⁻ p, ‖g' p‖ₑ ∂(ageμ (cOf L.ν) (-3 / 2)) :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ p in {p : Chart | a < p.1}, ‖g p‖ₑ ∂(ageμ (cOf L.ν) (-3 / 2)) := by
          rw [← lintegral_indicator hSa]
          apply lintegral_congr
          intro p
          by_cases hp : a < p.1
          · have hm : p ∈ {p : Chart | a < p.1} := hp
            simp [hg'def, hp, hm]
          · have hm : p ∉ {p : Chart | a < p.1} := hp
            simp [hg'def, hp, hm]
      _ = ageMass (cOf L.ν) a g := rfl
      _ ≤ thinMass (cOf L.ν) g a := hA _ hc a g hg
  -- the real coefficient
  have hcoef : ∀ j : ℕ, C0 * (1 + cOf L.ν / L.ε⁻¹) * L.ε⁻¹ ^ (-(3 / 2 : ℝ)) *
      binUpper s (K.δ / 4) j ^ (5 / 4 : ℝ) ≤
      2 * |C0| * L.ν⁻¹ ^ 2 * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) := by
    intro j
    have eR : L.ε⁻¹ ^ (-(3 / 2 : ℝ)) = L.ε ^ (3 / 2 : ℝ) := by
      rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le, neg_neg]
    have hcR : cOf L.ν / L.ε⁻¹ ≤ L.ν⁻¹ ^ 2 := by
      unfold cOf
      rw [div_inv_eq_mul, ← inv_pow]
      have : (L.ν ^ 2)⁻¹ * L.ε ≤ (L.ν ^ 2)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hε1 (by positivity)
      simpa using this
    have h1 : (1 : ℝ) ≤ L.ν⁻¹ ^ 2 := one_le_pow₀ (one_le_inv₀ hν |>.2 hν1)
    have hfac : 1 + cOf L.ν / L.ε⁻¹ ≤ 2 * L.ν⁻¹ ^ 2 := by linarith
    have hcpos : 0 ≤ 1 + cOf L.ν / L.ε⁻¹ := by
      have : 0 ≤ cOf L.ν / L.ε⁻¹ := div_nonneg hc.le hR.le
      linarith
    have hbu0 : 0 ≤ binUpper s (K.δ / 4) j := by
      unfold binUpper; exact mul_nonneg hs.le (Real.exp_pos _).le
    have hbu : binUpper s (K.δ / 4) j ≤ s := by
      unfold binUpper
      have hj : 0 ≤ K.δ / 4 * (j : ℝ) := by
        have := (show (0 : ℝ) ≤ j from Nat.cast_nonneg j)
        have hδ0 : 0 ≤ K.δ := by linarith
        positivity
      have : Real.exp (-(K.δ / 4 * j)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc s * Real.exp (-(K.δ / 4 * j)) ≤ s * 1 := mul_le_mul_of_nonneg_left this hs.le
        _ = s := mul_one s
    have hpow : binUpper s (K.δ / 4) j ^ (5 / 4 : ℝ) ≤ s ^ (5 / 4 : ℝ) :=
      Real.rpow_le_rpow hbu0 hbu (by norm_num)
    have hE : 0 ≤ L.ε ^ (3 / 2 : ℝ) := Real.rpow_nonneg hε.le _
    have hB0 : 0 ≤ binUpper s (K.δ / 4) j ^ (5 / 4 : ℝ) := Real.rpow_nonneg hbu0 _
    rw [eR]
    calc C0 * (1 + cOf L.ν / L.ε⁻¹) * L.ε ^ (3 / 2 : ℝ) * binUpper s (K.δ / 4) j ^ (5 / 4 : ℝ)
        ≤ |C0| * (1 + cOf L.ν / L.ε⁻¹) * L.ε ^ (3 / 2 : ℝ) *
            binUpper s (K.δ / 4) j ^ (5 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self C0) hcpos) hE) hB0
      _ ≤ |C0| * (2 * L.ν⁻¹ ^ 2) * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfac (abs_nonneg _)) hE) hpow hB0
            (mul_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) hE)
      _ = 2 * |C0| * L.ν⁻¹ ^ 2 * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ) := by ring
  set Y : ℝ≥0∞ := ENNReal.ofReal (2 * |C0| * L.ν⁻¹ ^ 2 * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)) *
    thinMass (cOf L.ν) g a with hY
  have hj : ∀ j : ℕ, (∫⁻ p in binSet s (K.δ / 4) j, M' p ∂(ageμ (cOf L.ν) (-3 / 2))) ^
      (1 / 2 : ℝ) ≤ Y := fun j =>
    (hC0 L.ε⁻¹ (cOf L.ν) s hR hc j g' hg').trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (hcoef j)) (hmass _))
  unfold majBin
  calc (∫⁻ p in {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s},
          wardYChartMaj L.ε⁻¹ (cOf L.ν) (Real.exp (-(K.δ / 2))) g p ^ (2 : ℝ)
            ∂(ageμ (cOf L.ν) (-3 / 2))) ^ (1 / 2 : ℝ)
      ≤ ((∫⁻ p in binSet s (K.δ / 4) 0, M' p ∂(ageμ (cOf L.ν) (-3 / 2))) +
          ∫⁻ p in binSet s (K.δ / 4) 1, M' p ∂(ageμ (cOf L.ν) (-3 / 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hI (by norm_num)
    _ ≤ (∫⁻ p in binSet s (K.δ / 4) 0, M' p ∂(ageμ (cOf L.ν) (-3 / 2))) ^ (1 / 2 : ℝ) +
          (∫⁻ p in binSet s (K.δ / 4) 1, M' p ∂(ageμ (cOf L.ν) (-3 / 2))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ ≤ Y + Y := add_le_add (hj 0) (hj 1)
    _ = ENNReal.ofReal (4 * |C0| * L.ν⁻¹ ^ 2 * L.ε ^ (3 / 2 : ℝ) * s ^ (5 / 4 : ℝ)) *
          thinMass (cOf L.ν) g a := by
        rw [hY, ← two_mul, ← mul_assoc]
        congr 1
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- The majorant bin bound along the sequence from the bin core `WardYMajBinCore` (task
`PartIII-b:C/rep/5/1/2/4/1/3/3`) and `AgeMassLeThin`. -/
theorem tailMajBinSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hcore : WardYMajBinCore)
    (hA : AgeMassLeThin) : TailMajBinSeq Pl σ₀ mZ dm dp := by
  intro D _ _ _ hst
  obtain ⟨C0, hC0⟩ := hcore D.K.δ hst.δ_pos hst.δ_lt
  refine ⟨4 * |C0|, 2, ?_⟩
  have hle := retNu_retEps_eventually_le_one (Pl := D.Pl) (σ₀ := D.σ₀) hst.omega_ne
    hst.gamma_pos D.coeff_ne
  filter_upwards [hle] with n hn
  exact tailMajBinAt_of hn.1 hn.2 hA hC0

end UnforcedLeray.Short.PartIIIb.Concrete

end
