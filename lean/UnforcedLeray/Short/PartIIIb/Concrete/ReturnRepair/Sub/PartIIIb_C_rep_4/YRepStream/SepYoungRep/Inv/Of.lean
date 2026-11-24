import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.PeriodSmall
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HU
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window

/-!
# `PartIII-b:C/rep/4/4/1/org/1/1/inv`: `sepYoungRepInv_of`

`SepYoungRep` from the density route: the four Props of `Inv/Defs.lean`, free weak uniqueness
and the existence of the weak stress inverse.  Source
`the November 2 reference manuscript`
3596-3626, 4145, 4163-4174, 4187-4194, 5169-5176.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

section One

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}

/-- On an old bounded source the weak stress inverse is `-W_μ` on the young region. -/
theorem sepSmoothAgree
    (hU : FreeWeakUniqueness (cOf L.ν) (gRate Pl) L.ν L.ε μ)
    (hS : ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ)
    (h1 : SepSmoothResponseAt Pl K L μ) (F : LStr Pl K L) (f₁ f₂ : Chart → Ten3)
    (hF : OldBoxAt Pl K L F f₁ f₂) :
    ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
      (Sop Pl K L μ F : Chart → Merid) p =
        -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (f₁ + f₂)) p := by
  obtain ⟨B, hBw, hBy⟩ := h1 F f₁ f₂ hF
  have hSs : IsWeakStressInverse (Sop Pl K L μ) L.ε μ := Classical.epsilon_spec hS
  have hEq : Sop Pl K L μ F = B := hU _ _ _ (hSs _) hBw
  rw [hEq]
  exact hBy

theorem eLpNorm_two_tri {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {m : Measure α}
    {f g h : α → E} (hf : AEStronglyMeasurable f m) (hg : AEStronglyMeasurable g m)
    (hh : AEStronglyMeasurable h m) :
    eLpNorm (fun x => f x - h x) 2 m ≤
      eLpNorm (fun x => f x - g x) 2 m + eLpNorm (fun x => g x - h x) 2 m := by
  have e : (fun x => f x - h x) = (fun x => f x - g x) + (fun x => g x - h x) := by
    ext x; simp
  rw [e]
  exact eLpNorm_add_le (hf.sub hg) (hg.sub hh) (by norm_num)

/-- `SepYoungRepAt` from the density route. -/
theorem sepYoungRepAtInv_of
    (hU : FreeWeakUniqueness (cOf L.ν) (gRate Pl) L.ν L.ε μ)
    (hS : ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ)
    (h1 : SepSmoothResponseAt Pl K L μ) (h2 : SepOldSrcFiniteAt Pl K L μ)
    (h3 : SepOldDensityAt Pl K L μ) (h4 : SepYoungContAt Pl K L μ) :
    SepYoungRepAt Pl K L μ := by
  intro w g₁ g₂ hg
  obtain ⟨T, hT⟩ := h2 w g₁ g₂ hg
  obtain ⟨Fn, f₁, f₂, Tn, hbox, hconv, hsrc⟩ := h3 w g₁ g₂ T hg hT
  obtain ⟨C, hC0, hC⟩ := h4
  set bm := bodyMeasure (cOf L.ν) (gRate Pl) L.ν with hbm
  set A : Set Chart := {p : Chart | L.ν * p.1 ≤ 1} with hA
  have hAm : MeasurableSet A := measurableSet_le (measurable_const.mul measurable_fst) measurable_const
  set u : Chart → Merid := (Sop Pl K L μ (oldRep Pl K L w) : Chart → Merid) with hu
  set y : Chart → Merid := youngWCoef Pl K L μ (g₁ + g₂) with hy
  have hsm := fun n => sepSmoothAgree hU hS h1 (Fn n) (f₁ n) (f₂ n) (hbox n).1
  -- bound for each n
  have key : ∀ n, eLpNorm (fun p => u p - y p) 2 (bm.restrict A) ≤
      ‖Sop Pl K L μ (oldRep Pl K L w) - Sop Pl K L μ (Fn n)‖ₑ +
        ENNReal.ofReal C * IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19)
          (IIIa.srcNorm (fun τ z => Tn n τ z - T τ z)) := by
    intro n
    obtain ⟨m1, m2, hb⟩ := hC _ _ _ _ (hbox n).2 hT
    have hun : AEStronglyMeasurable (Sop Pl K L μ (Fn n) : Chart → Merid) bm :=
      (Lp.aestronglyMeasurable _)
    have hu' : AEStronglyMeasurable u bm := Lp.aestronglyMeasurable _
    have t1 := eLpNorm_two_tri (m := bm.restrict A) (f := u)
      (g := (Sop Pl K L μ (Fn n) : Chart → Merid)) (h := y) hu'.restrict hun.restrict m2.restrict
    have t2 := eLpNorm_two_tri (m := bm.restrict A) (f := (Sop Pl K L μ (Fn n) : Chart → Merid))
      (g := youngWCoef Pl K L μ (f₁ n + f₂ n)) (h := y) hun.restrict m1.restrict m2.restrict
    have e0 : eLpNorm (fun p => (Sop Pl K L μ (Fn n) : Chart → Merid) p -
        youngWCoef Pl K L μ (f₁ n + f₂ n) p) 2 (bm.restrict A) = 0 := by
      refine (eLpNorm_eq_zero_iff ((hun.restrict).sub m1.restrict) (by norm_num)).2 ?_
      have := (ae_restrict_iff' hAm).2 (hsm n)
      filter_upwards [this, ae_restrict_mem hAm] with p hp hpA
      have hp' := hp
      have hpA' : L.ν * p.1 ≤ 1 := hpA
      simp [youngWCoef, hpA', hp']
    have e1 : eLpNorm (fun p => u p - (Sop Pl K L μ (Fn n) : Chart → Merid) p) 2 (bm.restrict A) ≤
        ‖Sop Pl K L μ (oldRep Pl K L w) - Sop Pl K L μ (Fn n)‖ₑ := by
      calc _ ≤ eLpNorm (fun p => u p - (Sop Pl K L μ (Fn n) : Chart → Merid) p) 2 bm :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = ‖Sop Pl K L μ (oldRep Pl K L w) - Sop Pl K L μ (Fn n)‖ₑ := by
            rw [Lp.enorm_def]
            apply eLpNorm_congr_ae
            filter_upwards [Lp.coeFn_sub (Sop Pl K L μ (oldRep Pl K L w))
              (Sop Pl K L μ (Fn n))] with p hp
            exact hp.symm
    have e2 : eLpNorm (fun p => youngWCoef Pl K L μ (f₁ n + f₂ n) p - y p) 2 (bm.restrict A) ≤
        ENNReal.ofReal C * IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19)
          (IIIa.srcNorm (fun τ z => Tn n τ z - T τ z)) :=
      (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hb
    exact t1.trans (add_le_add e1 (t2.trans (by rw [e0, zero_add]; exact e2)))
  have hT1 : Tendsto (fun n => ‖Sop Pl K L μ (oldRep Pl K L w) - Sop Pl K L μ (Fn n)‖ₑ)
      atTop (𝓝 0) := by
    have h := tendsto_iff_edist_tendsto_0.1
      (((Sop Pl K L μ).continuous.tendsto _).comp hconv)
    refine h.congr (fun n => ?_)
    simp only [Function.comp]
    rw [edist_comm, edist_eq_enorm_sub]
  have hT2 := ENNReal.Tendsto.const_mul hsrc (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  have hlim := ge_of_tendsto' (hT1.add hT2) key
  rw [mul_zero, add_zero] at hlim
  have hz : eLpNorm (fun p => u p - y p) 2 (bm.restrict A) = 0 := le_antisymm hlim bot_le
  have hmu : AEStronglyMeasurable u bm := Lp.aestronglyMeasurable _
  have hmy : AEStronglyMeasurable y bm := (hC _ _ _ _ hT hT).1
  replace hz := (eLpNorm_eq_zero_iff (hmu.restrict.sub hmy.restrict) (by norm_num)).1 hz
  have hz' : ∀ᵐ p ∂(bm.restrict A), u p = y p := by
    filter_upwards [hz] with p hp
    simpa [sub_eq_zero] using hp
  filter_upwards [(ae_restrict_iff' hAm).1 hz'] with p hp hpA
  rw [hp hpA]
  simp [hy, youngWCoef, hpA]

end One


/-- (i) along the sequence. -/
def SepSmoothResponse (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepSmoothResponseAt D.Pl D.K (D.level n) (D.mu n z)

/-- (ii) along the sequence. -/
def SepOldSrcFinite (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepOldSrcFiniteAt D.Pl D.K (D.level n) (D.mu n z)

/-- (iii) along the sequence. -/
def SepOldDensity (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepOldDensityAt D.Pl D.K (D.level n) (D.mu n z)

/-- (iv) along the sequence. -/
def SepYoungCont (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepYoungContAt D.Pl D.K (D.level n) (D.mu n z)

/-- **`SepYoungRep` by density** (replaces `sepYoungRep_of` from `SepRepBody`/`SepRepWeak`). -/
theorem sepYoungRepInv_of (dm dp : ℝ) (h1 : SepSmoothResponse dm dp)
    (h2 : SepOldSrcFinite dm dp) (h3 : SepOldDensity dm dp) (h4 : SepYoungCont dm dp) :
    SepYoungRep dm dp := by
  intro D hst
  filter_upwards [h1 D hst, h2 D hst, h3 D hst, h4 D hst, periodSmall D hst,
    muWin_gt_quarter D hst, hst.pins] with n a1 a2 a3 a4 a5 a6 a7 z hz
  exact sepYoungRepAtInv_of
    (freeWeakUniquenessAll _ _ _ _ _ (cOf_pos (D.level n).ν_pos) (D.level n).ν_pos
      (D.level n).ε_pos a5 (by linarith [a6 z hz]))
    (a7 z hz).stress (a1 z hz) (a2 z hz) (a3 z hz) (a4 z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
