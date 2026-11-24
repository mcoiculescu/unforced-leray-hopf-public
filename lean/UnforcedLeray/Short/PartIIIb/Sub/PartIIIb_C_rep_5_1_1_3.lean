import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# `PartIII-b:C/rep/5/1/1/3`: the per-bin velocity bound — shared definitions

Source `the November 2 reference manuscript`
5585-5593.

**Restated (organizer `PartIII-b:C/rep/5/1/1/3/org`).**  `PerBinVelocityAt` (in
`PartIII-b_C_rep_5_1_1Org.lean`) is the true single-term kernel bound of 5585-5593: the bin
`(s e^{-h}, s]` norm of `S_far (thinPart T)` is at most `C ν^{-k} ε^{3/2}(s^{1/2}+s^{3/4})` times the
unweighted `Z_1` norm of the sources of age `≥ e^{δ-h}s`.  The source-age splitting into a margin
and a gap regime is no longer used: the kernel estimate is applied to `thinPart T` itself (sources of
age `< e^{δ-h}s` do not reach the bin, by the mask `t > e^δ u` and `u > s e^{-h}`).  The former
two-term reduction `perBinAt_of`/`perBinVelocitySeq_of` is retired; the new reduction is in
`PartIII-b_C_rep_5_1_1_3/Tail.lean`.

Kept here (imported by the sibling files): `velBin_add_le` (Minkowski in `L²`), `z1Part_congr`,
`measurableSet_marginSrc`, `thinPart_thinPart`, and the definitions `AgeSplitThin` (proved,
`AgeSplit.lean`), `MarginBinKernelAt/Seq` (true, a special case of the single-term bound) and
`GapBinKernelAt/Seq`.  **`GapBinKernelAt` (with `ε^3`) is false in substance and unused**: the
`ε^3` of 4925-4934 is the pointwise jet of `D_y X` in the norm of `A`, not the normalized `L²`
velocity; the order-four kernel bound `ε^{3/2} s^{5/4} N₀` is sharp (5347).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Source-age splitting of the thin part**: for a measurable age set `{t | P t}`, every thin
part `thinPart T` is the sum of two thin stresses whose first components are the restrictions of
`T_1` to the ages in `P`, resp. not in `P` (restriction of an `L²` class by an indicator; the
measure classes of `Z_1`-norms agree, `ae_gainZ1Measure`). -/
def AgeSplitThinAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (P : ℝ → Prop) : Prop :=
  MeasurableSet {t : ℝ | P t} → ∀ T : LStr Pl K L, ∃ TM TG : LStr Pl K L,
    thinPart T = TM + TG ∧ thinPart TM = TM ∧ thinPart TG = TG ∧
    ((((TM.fst : Lp Ten3 2 _)) : Chart → Ten3) =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      fun p => if P p.1 then (((thinPart T).fst : Lp Ten3 2 _) : Chart → Ten3) p else 0) ∧
    ((((TG.fst : Lp Ten3 2 _)) : Chart → Ten3) =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      fun p => if P p.1 then 0 else (((thinPart T).fst : Lp Ten3 2 _) : Chart → Ten3) p)

/-- Splitting of the thin part for all levels and all measurable age sets. -/
def AgeSplitThin : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (P : ℝ → Prop), AgeSplitThinAt Pl K L P

/-- **Margin-regime kernel estimate** (5585-5593): for `S_far` with `IsFarMaskG`, a bin
`(s e^{-h}, s]`, `0 < h < δ/2`, `0 < s ≤ S`, and a thin `T_M` whose first component vanishes a.e.
outside the margin regime `MarginSrc` (late output bin `ν u ≥ 4/5`, or early source `ν t ≤ 3/2`):
radial gap `D ≍ R/√s` for the sources of age `≥ e^{δ-h}s`, order-four kernel with `L²` norm
`C D^{-5/2}`, Minkowski, `ThinMassBound`; sources of age `< e^{δ-h}s` do not reach the bin (the
mask `t > e^δ u`). -/
def MarginBinKernelAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K →
    ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
      ∀ TM : LStr Pl K L, thinPart TM = TM →
        (∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), ¬ MarginSrc L.ν s h p.1 →
          (((TM.fst : Lp Ten3 2 _)) : Chart → Ten3) p = 0) →
        velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf TM : Chart → Merid) ≤
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 / 2 : ℝ) * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ))) *
            z1Part (cOf L.ν) K.mZ
              (fun t => Real.exp (K.δ - h) * s ≤ t ∧ MarginSrc L.ν s h t)
              (((TM.fst : Lp Ten3 2 _)) : Chart → Ten3)

/-- **(Retired: false as stated, `ε^3`; unused.)** Source-gap kernel estimate (4925-4937, 3902-3912): same, for a thin `T_G` whose first
component vanishes a.e. on the margin regime (so every source reaching the bin has `ν t > 3/2`,
early-output bin, `t/u > 15/8`: fixed fractional radial gap, order-four kernel): the bound has
`ε^3`. -/
def GapBinKernelAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (C : ℝ) (k : ℕ) : Prop :=
  ∀ (h s : ℝ), 0 < h → h < K.δ / 2 → 0 < s → s ≤ L.Scut K →
    ∀ Sf : LStr Pl K L →L[ℝ] LVel Pl L, IsFarMaskG L.ε⁻¹ μ K.δ (L.Scut K) Sf →
      ∀ TG : LStr Pl K L, thinPart TG = TG →
        (∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), MarginSrc L.ν s h p.1 →
          (((TG.fst : Lp Ten3 2 _)) : Chart → Ten3) p = 0) →
        velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf TG : Chart → Merid) ≤
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ (3 : ℝ) * (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ))) *
            z1Part (cOf L.ν) K.mZ
              (fun t => Real.exp (K.δ - h) * s ≤ t ∧ ¬ MarginSrc L.ν s h t)
              (((TG.fst : Lp Ten3 2 _)) : Chart → Ten3)

/-- Sequence-level margin kernel estimate, constants uniform for large `n`, `z ∈ [-1,1]`. -/
def MarginBinKernelSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      MarginBinKernelAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- Sequence-level source-gap kernel estimate. -/
def GapBinKernelSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      GapBinKernelAt D.Pl D.K (D.level n) (D.mu n z) C k

/-- `velBin` is subadditive (Minkowski in `L²`). -/
theorem velBin_add_le (c γ ν : ℝ) (s₀ s₁ : ℝ) (v w : VelG c γ ν) :
    velBin c s₀ s₁ ((v + w : VelG c γ ν) : Chart → Merid) ≤
      velBin c s₀ s₁ (v : Chart → Merid) + velBin c s₀ s₁ (w : Chart → Merid) := by
  set S : Set Chart := {p : Chart | s₀ < p.1 ∧ p.1 ≤ s₁} with hS
  set μ' : Measure Chart := (srcMeasure c).restrict S with hμ'
  have hac : μ' ≪ bodyMeasure c γ ν := by
    have h1 : srcMeasure c ≪ bodyMeasure c γ ν := by
      rw [← Measure.ae_le_iff_absolutelyContinuous, NearInst.ae_srcMeasure, ← NearInst.ae_bodyMeasure]
    exact (Measure.restrict_le_self).absolutelyContinuous.trans h1
  have hv : AEMeasurable (fun p => ‖(v : Chart → Merid) p‖ₑ) μ' :=
    (((Lp.aestronglyMeasurable v).enorm)).mono_ac hac
  have hw : AEMeasurable (fun p => ‖(w : Chart → Merid) p‖ₑ) μ' :=
    (((Lp.aestronglyMeasurable w).enorm)).mono_ac hac
  have hae : ((v + w : VelG c γ ν) : Chart → Merid) =ᵐ[μ'] (v : Chart → Merid) + w :=
    (Lp.coeFn_add v w).filter_mono (hac.ae_le)
  unfold velBin
  calc (∫⁻ p in S, ‖((v + w : VelG c γ ν) : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ p, ((fun p => ‖(v : Chart → Merid) p‖ₑ) + (fun p => ‖(w : Chart → Merid) p‖ₑ)) p
            ^ (2 : ℝ) ∂μ') ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        apply lintegral_mono_ae
        filter_upwards [hae] with p hp
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        rw [hp]
        exact enorm_add_le _ _
    _ ≤ _ := ENNReal.lintegral_Lp_add_le hv hw (by norm_num)


/-- `z1Part` only sees the values of the field on the selected ages. -/
theorem z1Part_congr (c mZ : ℝ) (P : ℝ → Prop) (hP : MeasurableSet {t : ℝ | P t})
    (F G : Chart → Ten3)
    (h : ∀ᵐ p ∂(ageμ c (-1 / 2)), P p.1 → F p = G p) :
    z1Part c mZ P F = z1Part c mZ P G := by
  unfold z1Part
  congr 1
  apply lintegral_congr_ae
  have h' : ∀ᵐ p ∂(z1Measure c mZ), P p.1 → F p = G p := by
    rw [NearInst.ae_z1Measure]; exact h
  have hm : MeasurableSet {p : Chart | P p.1} := measurable_fst hP
  rw [Filter.EventuallyEq, ae_restrict_iff' hm]
  filter_upwards [h'] with p hp hpm
  rw [hp hpm]

theorem measurableSet_marginSrc (ν s h : ℝ) : MeasurableSet {t : ℝ | MarginSrc ν s h t} := by
  unfold MarginSrc LateOutBin
  by_cases hA : 4 / 5 ≤ ν * (s * Real.exp (-h))
  · simp [hA]
  · simp only [hA, false_or]
    exact measurableSet_le (by fun_prop) measurable_const

theorem coef_le (C1 C' a1 a2 e g : ℝ) (hC : C1 ≤ C') (hC' : 0 ≤ C') (ha1 : 0 ≤ a1) (ha : a1 ≤ a2)
    (he : 0 ≤ e) (hg : 0 ≤ g) : C1 * a1 * e * g ≤ C' * a2 * e * g := by
  have ha2 : 0 ≤ a2 := ha1.trans ha
  have h1 : C1 * a1 ≤ C' * a2 :=
    calc C1 * a1 ≤ max C1 0 * a1 := mul_le_mul_of_nonneg_right (le_max_left _ _) ha1
      _ ≤ C' * a2 := mul_le_mul (max_le hC hC') ha ha1 hC'
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 he) hg

/-- `thinPart` is idempotent: `thinPart (thinPart T) = thinPart T`. -/
theorem thinPart_thinPart {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    thinPart (thinPart T) = thinPart T := rfl

end UnforcedLeray.Short.PartIIIb.Concrete
