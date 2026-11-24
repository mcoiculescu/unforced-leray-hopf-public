import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ClmExtend

/-!
# `farMaskExists_of`: the far mask `S_far` exists (source 3905-3912, "its exact kernel realization")

Source of record: `the November 2 reference manuscript`, lines 3905-3912.

The dense class `D = {F ∈ Z : zsum F is a.e. a box tensor}` is a submodule (box tensors are
closed under `f + a • g` and `zsum` is additive and homogeneous a.e.), and dense by `BoxDenseZ`.
On `D` the map `F ↦ 1_{s<S} s^{-1/2} Re(-W_μ[1_{t>e^δ s} 𝒩_T f])` (the chosen box witness `f`) is
well defined a.e. (`FarKernelLinear` with `FarKernelL2` gives the a.e. independence of the witness),
linear, and bounded by `C ‖zsumL‖` (`FarKernelL2`). The bounded linear extension
`exists_clm_extend_of_dense` gives `S_far`, which has the pin `IsFarMask` by `isFarMask_iff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-! ## Box tensors: closure under linear combinations -/

theorem fm_isBox_zero : IsBoxTensor (0 : Chart → Ten3) where
  measurable := measurable_const
  bounded := ⟨0, fun p => by simp⟩
  band := ⟨1, 1, 0, one_pos, fun p hp => (hp (Pi.zero_apply p)).elim⟩

theorem fm_isBox_add_smul {f g : Chart → Ten3} (hf : IsBoxTensor f) (hg : IsBoxTensor g) (a : ℝ) :
    IsBoxTensor (f + a • g) where
  measurable := hf.measurable.add (hg.measurable.const_smul a)
  bounded := by
    obtain ⟨B, hB⟩ := hf.bounded
    obtain ⟨B', hB'⟩ := hg.bounded
    refine ⟨B + |a| * B', fun p => ?_⟩
    calc ‖(f + a • g) p‖ = ‖f p + a • g p‖ := rfl
      _ ≤ ‖f p‖ + ‖a • g p‖ := norm_add_le _ _
      _ = ‖f p‖ + |a| * ‖g p‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ B + |a| * B' := add_le_add (hB p) (mul_le_mul_of_nonneg_left (hB' p) (abs_nonneg a))
  band := by
    obtain ⟨s₁, s₂, L, hs₁, h1⟩ := hf.band
    obtain ⟨t₁, t₂, L', ht₁, h2⟩ := hg.band
    refine ⟨min s₁ t₁, max s₂ t₂, |L| + |L'|, lt_min hs₁ ht₁, fun p hp => ?_⟩
    by_cases hfp : f p = 0
    · have hgp : g p ≠ 0 := by
        intro h0
        apply hp
        simp [hfp, h0]
      obtain ⟨e1, e2, e3⟩ := h2 p hgp
      exact ⟨(min_le_right _ _).trans e1, e2.trans (le_max_right _ _),
        e3.trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))⟩
    · obtain ⟨e1, e2, e3⟩ := h1 p hfp
      exact ⟨(min_le_left _ _).trans e1, e2.trans (le_max_left _ _),
        e3.trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))⟩

theorem fm_isBox_add {f g : Chart → Ten3} (hf : IsBoxTensor f) (hg : IsBoxTensor g) :
    IsBoxTensor (f + g) := by
  simpa only [one_smul] using fm_isBox_add_smul hf hg 1

theorem fm_isBox_smul {g : Chart → Ten3} (hg : IsBoxTensor g) (a : ℝ) :
    IsBoxTensor (a • g) := by
  simpa only [zero_add] using fm_isBox_add_smul fm_isBox_zero hg a

/-! ## The box class on `Z` -/

/-- `F ∈ Z` is in the box class: `zsum F` is a.e. a box tensor. -/
abbrev fmBox {c mZ ρb : ℝ} (F : Zsp c mZ ρb) : Prop :=
  ∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum F =ᵐ[ageμ c (-1 / 2)] f

theorem fm_zsum_add {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (F G : Zsp c mZ ρb) :
    zsum (F + G) =ᵐ[ageμ c (-1 / 2)] fun p => zsum F p + zsum G p := by
  have h1 := zsumL_ae c mZ ρb hmZ hρ (F + G)
  have h2 := Lp.coeFn_add (zsumL c mZ ρb hmZ hρ F) (zsumL c mZ ρb hmZ hρ G)
  have h3 := zsumL_ae c mZ ρb hmZ hρ F
  have h4 := zsumL_ae c mZ ρb hmZ hρ G
  rw [map_add] at h1
  filter_upwards [h1, h2, h3, h4] with p q1 q2 q3 q4
  show zsum (F + G) p = zsum F p + zsum G p
  rw [← q1, q2, Pi.add_apply, q3, q4]

theorem fm_zsum_smul {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (a : ℝ) (F : Zsp c mZ ρb) :
    zsum (a • F) =ᵐ[ageμ c (-1 / 2)] fun p => a • zsum F p := by
  have h1 := zsumL_ae c mZ ρb hmZ hρ (a • F)
  have h2 := Lp.coeFn_smul a (zsumL c mZ ρb hmZ hρ F)
  have h3 := zsumL_ae c mZ ρb hmZ hρ F
  rw [map_smul] at h1
  filter_upwards [h1, h2, h3] with p q1 q2 q3
  show zsum (a • F) p = a • zsum F p
  rw [← q1, q2, Pi.smul_apply, q3]

theorem fm_zsum_zero {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) :
    zsum (0 : Zsp c mZ ρb) =ᵐ[ageμ c (-1 / 2)] (0 : Chart → Ten3) := by
  have h1 := zsumL_ae c mZ ρb hmZ hρ 0
  rw [map_zero] at h1
  have h2 : (⇑(0 : HTsp c) : Chart → Ten3) =ᵐ[ageμ c (-1 / 2)] (0 : Chart → Ten3) :=
    Lp.coeFn_zero _ _ _
  filter_upwards [h1, h2] with p q1 q2
  show zsum (0 : Zsp c mZ ρb) p = (0 : Chart → Ten3) p
  rw [← q1, q2]

theorem fm_zsum_add_wit {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {F G : Zsp c mZ ρb}
    {f g : Chart → Ten3} (hF : zsum F =ᵐ[ageμ c (-1 / 2)] f)
    (hG : zsum G =ᵐ[ageμ c (-1 / 2)] g) :
    zsum (F + G) =ᵐ[ageμ c (-1 / 2)] f + g := by
  filter_upwards [fm_zsum_add hmZ hρ F G, hF, hG] with p q1 q2 q3
  show zsum (F + G) p = (f + g) p
  rw [q1, Pi.add_apply, q2, q3]

theorem fm_zsum_smul_wit {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (a : ℝ) {F : Zsp c mZ ρb}
    {f : Chart → Ten3} (hF : zsum F =ᵐ[ageμ c (-1 / 2)] f) :
    zsum (a • F) =ᵐ[ageμ c (-1 / 2)] a • f := by
  filter_upwards [fm_zsum_smul hmZ hρ a F, hF] with p q1 q2
  show zsum (a • F) p = (a • f) p
  rw [q1, Pi.smul_apply, q2]

/-- The box class as a submodule of `Z`. -/
def fmSub (c mZ ρb : ℝ) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) : Submodule ℝ (Zsp c mZ ρb) where
  carrier := {F | fmBox F}
  add_mem' := by
    rintro F G ⟨f, hf, hF⟩ ⟨g, hg, hG⟩
    show fmBox (F + G)
    exact ⟨f + g, fm_isBox_add hf hg, fm_zsum_add_wit hmZ hρ hF hG⟩
  zero_mem' := by
    show fmBox (0 : Zsp c mZ ρb)
    exact ⟨0, fm_isBox_zero, fm_zsum_zero hmZ hρ⟩
  smul_mem' := by
    rintro a F ⟨f, hf, hF⟩
    show fmBox (a • F)
    exact ⟨a • f, fm_isBox_smul hf a, fm_zsum_smul_wit hmZ hρ a hF⟩

theorem mem_fmSub {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (F : Zsp c mZ ρb) :
    F ∈ fmSub c mZ ρb hmZ hρ ↔ fmBox F :=
  Iff.rfl

/-- Membership in the box submodule is the box class. -/
theorem fmBox_of_mem {c mZ ρb : ℝ} {hmZ : 0 ≤ mZ} {hρ : 0 < ρb} {F : Zsp c mZ ρb}
    (h : F ∈ fmSub c mZ ρb hmZ hρ) : fmBox F :=
  h

/-- The box class is dense in `Z` (`BoxDenseZ`). -/
theorem fmSub_dense (hD : BoxDenseZ) {c mZ ρb : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) :
    Dense (fmSub c mZ ρb hmZ hρ : Set (Zsp c mZ ρb)) := by
  rw [Metric.dense_iff]
  intro F r hr
  obtain ⟨F', hF', hd⟩ := hD c mZ ρb hc hmZ hρ F r hr
  refine ⟨F', Metric.mem_ball.2 ?_, (mem_fmSub hmZ hρ F').2 hF'⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hd

/-! ## Witnesses and the `L²` class -/

open Classical in
/-- A chosen box witness of `F` (zero off the box class). -/
def fmWit {c mZ ρb : ℝ} (F : Zsp c mZ ρb) : Chart → Ten3 :=
  if h : fmBox F then Classical.choose h else 0

theorem fmWit_spec {c mZ ρb : ℝ} {F : Zsp c mZ ρb} (h : fmBox F) :
    IsBoxTensor (fmWit F) ∧ zsum F =ᵐ[ageμ c (-1 / 2)] fmWit F := by
  unfold fmWit
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem fmWit_memLp {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {F : Zsp c mZ ρb} (h : fmBox F) :
    MemLp (fmWit F) 2 (ageμ c (-1 / 2)) := by
  have hw := (fmWit_spec h).2
  exact MemLp.ae_eq ((zsumL_ae c mZ ρb hmZ hρ F).trans hw)
    (Lp.memLp (zsumL c mZ ρb hmZ hρ F))

open Classical in
/-- The `L²` class of `g` when `g` is `MemLp` (zero otherwise). -/
def fmToHsp (c : ℝ) (g : Chart → Merid) : Hsp c :=
  if h : MemLp g 2 (ageμ c (-3 / 2)) then h.toLp g else 0

theorem fmToHsp_ae (c : ℝ) {g : Chart → Merid} (h : MemLp g 2 (ageμ c (-3 / 2))) :
    (fmToHsp c g : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] g := by
  unfold fmToHsp
  rw [dif_pos h]
  exact h.coeFn_toLp

/-! ## The far kernel on box tensors -/

theorem fm_farOut_memLp (hL : FarKernelL2) {R c ν μ δ S : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ) {f : Chart → Ten3}
    (hf : IsBoxTensor f) (hfL : MemLp f 2 (ageμ c (-1 / 2))) :
    MemLp (farOut R c ν μ δ S f) 2 (ageμ c (-3 / 2)) := by
  obtain ⟨C, _, hC⟩ := hL R c ν δ S μ hR hc hν hδ hS hμ
  obtain ⟨haes, hle⟩ := hC f hf
  exact ⟨haes, lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfL.eLpNorm_lt_top)⟩

theorem fm_farOut_ae_zero (hL : FarKernelL2) {R c ν μ δ S : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ) {h : Chart → Ten3}
    (hh : IsBoxTensor h) (h0 : h =ᵐ[ageμ c (-1 / 2)] 0) :
    farOut R c ν μ δ S h =ᵐ[ageμ c (-3 / 2)] 0 := by
  obtain ⟨C, _, hC⟩ := hL R c ν δ S μ hR hc hν hδ hS hμ
  obtain ⟨haes, hle⟩ := hC h hh
  have h1 : eLpNorm h 2 (ageμ c (-1 / 2)) = 0 := by
    rw [eLpNorm_congr_ae h0]
    exact eLpNorm_zero
  have h2 : eLpNorm (farOut R c ν μ δ S h) 2 (ageμ c (-3 / 2)) = 0 :=
    le_antisymm (hle.trans (le_of_eq (by rw [h1, mul_zero]))) zero_le
  exact (eLpNorm_eq_zero_iff haes (by norm_num)).1 h2

theorem fm_farOut_congr (hL : FarKernelL2) (hA : FarKernelLinear) {R c ν μ δ S : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ)
    {f g : Chart → Ten3} (hf : IsBoxTensor f) (hg : IsBoxTensor g)
    (hfg : f =ᵐ[ageμ c (-1 / 2)] g) :
    farOut R c ν μ δ S f =ᵐ[ageμ c (-3 / 2)] farOut R c ν μ δ S g := by
  have hbox := fm_isBox_add_smul hf hg (-1)
  have h0 : (f + (-1 : ℝ) • g) =ᵐ[ageμ c (-1 / 2)] 0 := by
    filter_upwards [hfg] with p hp
    simp [hp]
  have h1 := fm_farOut_ae_zero hL hR hc hν hδ hS hμ hbox h0
  have h2 := hA R c ν δ S μ hR hc hν hδ hS hμ f g hf hg (-1)
  filter_upwards [h1, h2] with p q1 q2
  rw [q2, Pi.add_apply, Pi.smul_apply] at q1
  show farOut R c ν μ δ S f p = farOut R c ν μ δ S g p
  have h3 : farOut R c ν μ δ S f p - farOut R c ν μ δ S g p = 0 := by
    rw [sub_eq_add_neg, ← neg_one_smul ℝ]
    simpa using q1
  exact sub_eq_zero.1 h3

theorem fm_farOut_add (hA : FarKernelLinear) {R c ν μ δ S : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ)
    {f g : Chart → Ten3} (hf : IsBoxTensor f) (hg : IsBoxTensor g) :
    farOut R c ν μ δ S (f + g) =ᵐ[ageμ c (-3 / 2)] farOut R c ν μ δ S f + farOut R c ν μ δ S g := by
  have h := hA R c ν δ S μ hR hc hν hδ hS hμ f g hf hg 1
  simpa only [one_smul] using h

theorem fm_farOut_smul (hL : FarKernelL2) (hA : FarKernelLinear) {R c ν μ δ S : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsBoxTensor g) (a : ℝ) :
    farOut R c ν μ δ S (a • g) =ᵐ[ageμ c (-3 / 2)] a • farOut R c ν μ δ S g := by
  have h := hA R c ν δ S μ hR hc hν hδ hS hμ (0 : Chart → Ten3) g fm_isBox_zero hg a
  have h0 : farOut R c ν μ δ S (0 : Chart → Ten3) =ᵐ[ageμ c (-3 / 2)] 0 :=
    fm_farOut_ae_zero hL hR hc hν hδ hS hμ fm_isBox_zero (Filter.EventuallyEq.refl _ _)
  filter_upwards [h, h0] with p q1 q2
  simp only [zero_add, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at q1 q2 ⊢
  rw [q1, q2, zero_add]

theorem fm_phi_ae (hL : FarKernelL2) (hA : FarKernelLinear) {R c ν μ δ S : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ)
    {mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {F : Zsp c mZ ρb} (hF : fmBox F)
    {f : Chart → Ten3} (hf : IsBoxTensor f) (hFf : zsum F =ᵐ[ageμ c (-1 / 2)] f) :
    ⇑(fmToHsp c (farOut R c ν μ δ S (fmWit F))) =ᵐ[ageμ c (-3 / 2)] farOut R c ν μ δ S f := by
  obtain ⟨hw1, hw2⟩ := fmWit_spec hF
  have hm := fm_farOut_memLp hL hR hc hν hδ hS hμ hw1 (fmWit_memLp hmZ hρ hF)
  exact (fmToHsp_ae c hm).trans
    (fm_farOut_congr hL hA hR hc hν hδ hS hμ hw1 hf (hw2.symm.trans hFf))

/-! ## `S_far` -/

theorem fm_phi_add_eq (hL : FarKernelL2) (hA : FarKernelLinear) {R c ν μ δ S : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ)
    {mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {F G : Zsp c mZ ρb} (hF : fmBox F) (hG : fmBox G) :
    fmToHsp c (farOut R c ν μ δ S (fmWit (F + G))) =
      fmToHsp c (farOut R c ν μ δ S (fmWit F)) + fmToHsp c (farOut R c ν μ δ S (fmWit G)) := by
  have hwF := fmWit_spec hF
  have hwG := fmWit_spec hG
  have hFG : fmBox (F + G) :=
    ⟨fmWit F + fmWit G, fm_isBox_add hwF.1 hwG.1, fm_zsum_add_wit hmZ hρ hwF.2 hwG.2⟩
  apply Lp.ext
  filter_upwards [fm_phi_ae hL hA hR hc hν hδ hS hμ hmZ hρ hFG (fm_isBox_add hwF.1 hwG.1)
      (fm_zsum_add_wit hmZ hρ hwF.2 hwG.2),
    fm_farOut_add hA hR hc hν hδ hS hμ hwF.1 hwG.1,
    Lp.coeFn_add (fmToHsp c (farOut R c ν μ δ S (fmWit F)))
      (fmToHsp c (farOut R c ν μ δ S (fmWit G))),
    fm_phi_ae hL hA hR hc hν hδ hS hμ hmZ hρ hF hwF.1 hwF.2,
    fm_phi_ae hL hA hR hc hν hδ hS hμ hmZ hρ hG hwG.1 hwG.2] with p h1 h2 h3 h4 h5
  rw [h1, h2, h3]
  simp only [Pi.add_apply]
  rw [h4, h5]

theorem fm_phi_smul_eq (hL : FarKernelL2) (hA : FarKernelLinear) {R c ν μ δ S : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ) (hS : 0 < S) (hμ : -(1 / 4) < μ)
    {mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (a : ℝ) {F : Zsp c mZ ρb} (hF : fmBox F) :
    fmToHsp c (farOut R c ν μ δ S (fmWit (a • F))) =
      a • fmToHsp c (farOut R c ν μ δ S (fmWit F)) := by
  have hwF := fmWit_spec hF
  have haF : fmBox (a • F) :=
    ⟨a • fmWit F, fm_isBox_smul hwF.1 a, fm_zsum_smul_wit hmZ hρ a hwF.2⟩
  apply Lp.ext
  filter_upwards [fm_phi_ae hL hA hR hc hν hδ hS hμ hmZ hρ haF (fm_isBox_smul hwF.1 a)
      (fm_zsum_smul_wit hmZ hρ a hwF.2),
    fm_farOut_smul hL hA hR hc hν hδ hS hμ hwF.1 a,
    Lp.coeFn_smul a (fmToHsp c (farOut R c ν μ δ S (fmWit F))),
    fm_phi_ae hL hA hR hc hν hδ hS hμ hmZ hρ hF hwF.1 hwF.2] with p h1 h2 h3 h4
  rw [h1, h2, h3]
  simp only [Pi.smul_apply]
  rw [h4]

theorem fm_farOut_memLp_of {R c ν μ δ S C : ℝ}
    (hC : ∀ f : Chart → Ten3, IsBoxTensor f →
      AEStronglyMeasurable (farOut R c ν μ δ S f) (ageμ c (-3 / 2)) ∧
        eLpNorm (farOut R c ν μ δ S f) 2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal C * eLpNorm f 2 (ageμ c (-1 / 2)))
    {f : Chart → Ten3} (hf : IsBoxTensor f) (hfL : MemLp f 2 (ageμ c (-1 / 2))) :
    MemLp (farOut R c ν μ δ S f) 2 (ageμ c (-3 / 2)) := by
  obtain ⟨haes, hle⟩ := hC f hf
  exact ⟨haes, lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfL.eLpNorm_lt_top)⟩

theorem fm_phi_bound {R c ν μ δ S : ℝ} (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν) (hδ : 0 < δ)
    (hS : 0 < S) (hμ : -(1 / 4) < μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ f : Chart → Ten3, IsBoxTensor f →
      AEStronglyMeasurable (farOut R c ν μ δ S f) (ageμ c (-3 / 2)) ∧
        eLpNorm (farOut R c ν μ δ S f) 2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal C * eLpNorm f 2 (ageμ c (-1 / 2)))
    {mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {F : Zsp c mZ ρb} (hF : fmBox F) :
    ‖fmToHsp c (farOut R c ν μ δ S (fmWit F))‖ ≤
      C * ‖zsumL c mZ ρb hmZ hρ F‖ := by
  obtain ⟨hw1, hw2⟩ := fmWit_spec hF
  have hwL := fmWit_memLp hmZ hρ hF
  have hg := fm_farOut_memLp_of hC hw1 hwL
  have hzL : (zsumL c mZ ρb hmZ hρ F : Chart → Ten3) =ᵐ[ageμ c (-1 / 2)] fmWit F :=
    (zsumL_ae c mZ ρb hmZ hρ F).trans hw2
  have e1 : ‖fmToHsp c (farOut R c ν μ δ S (fmWit F))‖ =
      (eLpNorm (farOut R c ν μ δ S (fmWit F)) 2 (ageμ c (-3 / 2))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (fmToHsp_ae c hg)]
  have e2 := (hC (fmWit F) hw1).2
  have e3 : eLpNorm (fmWit F) 2 (ageμ c (-1 / 2)) =
      eLpNorm (zsumL c mZ ρb hmZ hρ F) 2 (ageμ c (-1 / 2)) :=
    eLpNorm_congr_ae hzL.symm
  have e4 : ‖zsumL c mZ ρb hmZ hρ F‖ =
      (eLpNorm (zsumL c mZ ρb hmZ hρ F) 2 (ageμ c (-1 / 2))).toReal :=
    Lp.norm_def _
  have e6 : (eLpNorm (farOut R c ν μ δ S (fmWit F)) 2 (ageμ c (-3 / 2))).toReal ≤
      C * ‖zsumL c mZ ρb hmZ hρ F‖ := by
    rw [e4, ← e3]
    calc (eLpNorm (farOut R c ν μ δ S (fmWit F)) 2 (ageμ c (-3 / 2))).toReal
        ≤ (ENNReal.ofReal C * eLpNorm (fmWit F) 2 (ageμ c (-1 / 2))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwL.eLpNorm_ne_top) e2
      _ = C * (eLpNorm (fmWit F) 2 (ageμ c (-1 / 2))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0]
  rw [e1]
  exact e6

/-- **`S_far` exists** (source 3905-3912). -/
theorem farMaskExists_of (hL : FarKernelL2) (hA : FarKernelLinear) (hD : BoxDenseZ) :
    FarMaskExists := by
  intro c mZ ρb R ν δ S μ hc hmZ hρ hR hν hδ hS hμ
  obtain ⟨C, hC0, hC⟩ := hL R c ν δ S μ hR hc hν hδ hS hμ
  let phiL : fmSub c mZ ρb hmZ hρ →ₗ[ℝ] Hsp c :=
    { toFun := fun F => fmToHsp c (farOut R c ν μ δ S (fmWit (F : Zsp c mZ ρb)))
      map_add' := fun F G => by
        rw [Submodule.coe_add]
        exact fm_phi_add_eq hL hA hR hc hν hδ hS hμ hmZ hρ
          (fmBox_of_mem F.2) (fmBox_of_mem G.2)
      map_smul' := fun a F => by
        rw [Submodule.coe_smul]
        exact fm_phi_smul_eq hL hA hR hc hν hδ hS hμ hmZ hρ a (fmBox_of_mem F.2) }
  have hbound : ∀ F : fmSub c mZ ρb hmZ hρ,
      ‖phiL F‖ ≤ (C * ‖zsumL c mZ ρb hmZ hρ‖) * ‖(F : Zsp c mZ ρb)‖ := by
    intro F
    have h := fm_phi_bound hR hc hν hδ hS hμ hC0 hC hmZ hρ (fmBox_of_mem F.2)
    calc ‖phiL F‖ ≤ C * ‖zsumL c mZ ρb hmZ hρ (F : Zsp c mZ ρb)‖ := h
      _ ≤ C * (‖zsumL c mZ ρb hmZ hρ‖ * ‖(F : Zsp c mZ ρb)‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hC0
      _ = (C * ‖zsumL c mZ ρb hmZ hρ‖) * ‖(F : Zsp c mZ ρb)‖ := (mul_assoc _ _ _).symm
  obtain ⟨L, hL'⟩ := exists_clm_extend_of_dense (fmSub c mZ ρb hmZ hρ)
    (fmSub_dense hD hc hmZ hρ) phiL (C * ‖zsumL c mZ ρb hmZ hρ‖) hbound
  refine ⟨L, (isFarMask_iff R ν μ δ S L).2 ?_⟩
  intro F f hf hFf
  have hFD : fmBox F := ⟨f, hf, hFf⟩
  have hLF : L F = fmToHsp c (farOut R c ν μ δ S (fmWit F)) :=
    hL' ⟨F, (mem_fmSub hmZ hρ F).2 hFD⟩
  rw [hLF]
  exact fm_phi_ae hL hA hR hc hν hδ hS hμ hmZ hρ hFD hf hFf

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
