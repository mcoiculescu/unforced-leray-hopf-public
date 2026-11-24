import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3

/-!
# `PartIII-b:C/rep/5/1/1/3/2` and `/3/3`: margin and gap bin kernel estimates, decomposed

Source `the November 2 reference manuscript`
5585-5593, 5569-5584, 3902-3920, 3996-4011 (margin), 4925-4937 (gap).

Both estimates are the same statement for a regime predicate `Q h s t` on the source age and an
exponent `ep` of `ε`.  They split into

* `BinBoxAt` : the estimate for the explicit far-kernel expression on box tensors (analytic
  content: order-four kernel bound with radial gap, Minkowski, `ThinMassBound`);
* `BinDensityTransfer` : box tensors to general thin stresses with an `IsFarMaskG` operator
  (`BoxDenseZ`, continuity of `Sf` and of `velBin`, `z1Part`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Margin regime predicate. -/
def marginQ (L : ReturnLevel) : ℝ → ℝ → ℝ → Prop := fun h s t => MarginSrc L.ν s h t

/-- Gap regime predicate (complement of the margin regime). -/
def gapQ (L : ReturnLevel) : ℝ → ℝ → ℝ → Prop := fun h s t => ¬ MarginSrc L.ν s h t

/-- **Box-level bin estimate** (5585-5593 with 3902-3920; 4925-4937 with the fixed gap): for a box
tensor `f` vanishing outside the regime `Q h s`, the bin `(s e^{-h}, s]` norm of the explicit
masked far response `√p.1⁻¹ • Re(-sepWfar … f)` is at most
`C ν⁻ᵏ ε^ep (s^{1/2}+s^{3/4})` times the `Z_1` mass of `f` on the sources of age `≥ e^{δ-h}s`
in the regime. -/
def BinBoxAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (Q : ℝ → ℝ → ℝ → Prop) (ep : ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K →
    ∀ f : Chart → Ten3, NearInst.IsBoxTensor f → (∀ p : Chart, ¬ Q h s p.1 → f p = 0) →
      velBin (cOf L.ν) (s * Real.exp (-h)) s
          (fun p : Chart => (Real.sqrt p.1)⁻¹ • NearInst.merRe (-NearInst.sepWfar L.ν (μ : ℂ)
            L.ε⁻¹ K.δ p.1 (NearInst.cartLift L.ε⁻¹ (cOf L.ν) f) (NearInst.chartY L.ε⁻¹ p)
            (NearInst.chartTau L.ε⁻¹ p))) ≤
        ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ ep * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ))) *
          z1Part (cOf L.ν) K.mZ (fun t => Real.exp (K.δ - h) * s ≤ t ∧ Q h s t) f

/-- The general-thin-stress bin estimate for a regime predicate `Q` (the common shape of
`MarginBinKernelAt` and `GapBinKernelAt`). -/
def BinGenAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (Q : ℝ → ℝ → ℝ → Prop) (ep : ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K →
    ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
      ∀ T : LStr Pl K L, thinPart T = T →
        (∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), ¬ Q h s p.1 →
          (((T.fst : Lp Ten3 2 _)) : Chart → Ten3) p = 0) →
        velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf T : Chart → Merid) ≤
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ ep * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ))) *
            z1Part (cOf L.ν) K.mZ (fun t => Real.exp (K.δ - h) * s ≤ t ∧ Q h s t)
              (((T.fst : Lp Ten3 2 _)) : Chart → Ten3)

/-- **Box-to-general transfer** (source 3905-3912: the kernel pin is on the dense class): the
box-level bin estimate implies the general one with the same constants, for measurable regime
predicates; by `BoxDenseZ`, continuity of `Sf : LStr →L LVel`, of `velBin` along `L²` and of
`z1Part` in the stress, restricting approximants to the regime by `IsBoxTensor.indicator`. -/
def BinDensityTransfer : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts), 0 < K.C0 → ∀ (L : ReturnLevel) (μ : ℝ)
    (Q : ℝ → ℝ → ℝ → Prop) (ep C : ℝ) (k : ℕ), (∀ h s, MeasurableSet {t : ℝ | Q h s t}) →
    BinBoxAt Pl K L μ Q ep C k → BinGenAt Pl K L μ Q ep C k

/-- Sequence-level box margin estimate. -/
def MarginBoxBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      BinBoxAt D.Pl D.K (D.level n) (D.mu n z) (marginQ (D.level n)) (3 / 2 : ℝ) C k

/-- Sequence-level box gap estimate. -/
def GapBoxBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      BinBoxAt D.Pl D.K (D.level n) (D.mu n z) (gapQ (D.level n)) (3 : ℝ) C k

theorem marginAt_of_gen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) (k : ℕ)
    (h : BinGenAt Pl K L μ (marginQ L) (3 / 2 : ℝ) C k) : MarginBinKernelAt Pl K L μ C k :=
  fun hh s h0 h1 hs hS Sf hSf TM hTM hsupp => h hh s h0 h1 hs hS Sf hSf TM hTM hsupp

theorem gapAt_of_gen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ C : ℝ) (k : ℕ)
    (h : BinGenAt Pl K L μ (gapQ L) (3 : ℝ) C k) : GapBinKernelAt Pl K L μ C k := by
  intro hh s h0 h1 hs hS Sf hSf TG hTG hsupp
  refine h hh s h0 h1 hs hS Sf hSf TG hTG ?_
  filter_upwards [hsupp] with p hp hn
  exact hp (by simpa [gapQ] using hn)

theorem measurable_marginQ (L : ReturnLevel) (h s : ℝ) :
    MeasurableSet {t : ℝ | marginQ L h s t} := measurableSet_marginSrc L.ν s h

theorem measurable_gapQ (L : ReturnLevel) (h s : ℝ) :
    MeasurableSet {t : ℝ | gapQ L h s t} := (measurableSet_marginSrc L.ν s h).compl

/-- The margin kernel estimate from the box-level estimate and the density transfer. -/
theorem marginBinKernelSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hT : BinDensityTransfer)
    (hB : MarginBoxBinSeq Pl σ₀ mZ dm dp) : MarginBinKernelSeq Pl σ₀ mZ dm dp := by
  intro D h1 h2 h3 h4
  obtain ⟨C, k, hev⟩ := hB D h1 h2 h3 h4
  refine ⟨C, k, hev.mono fun n hn z hz => ?_⟩
  exact marginAt_of_gen _ _ _ _ _ _ (hT _ _ h4.C0_pos _ _ _ _ _ _ (measurable_marginQ _) (hn z hz))

/-- The gap kernel estimate from the box-level estimate and the density transfer. -/
theorem gapBinKernelSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (hT : BinDensityTransfer)
    (hB : GapBoxBinSeq Pl σ₀ mZ dm dp) : GapBinKernelSeq Pl σ₀ mZ dm dp := by
  intro D h1 h2 h3 h4
  obtain ⟨C, k, hev⟩ := hB D h1 h2 h3 h4
  refine ⟨C, k, hev.mono fun n hn z hz => ?_⟩
  exact gapAt_of_gen _ _ _ _ _ _ (hT _ _ h4.C0_pos _ _ _ _ _ _ (measurable_gapQ _) (hn z hz))

end UnforcedLeray.Short.PartIIIb.Concrete
