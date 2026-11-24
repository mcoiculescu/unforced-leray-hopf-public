import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# `PartII-b:F7/1` Helper 2: `q`-Periodization of Coordinate Tests and Slice-to-Joint Pairing

Source of record: `the November 2 reference manuscript` (SP), lines 2213–2239,
2269–2282.

Periodizes coordinate tests `IsCoordTest φ` and planar solenoidal tests `IsPlanarSolTest Ψ` in `q`
with period `c > 0`, proves the slice-to-`Coord` Fubini/unfolding identity for `q`-periodic locally
`L¹_s L²(C_c)` fields, and derives `sliceWeakToJoint` (`HasWeakVec`) and `sliceBodySourceToJoint`
(`IsBodySource`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.TailPeriodizeAux

open UnforcedLeray.Short.IIb

/-! ### 1. Compact support box for `IsCoordTest` and `coordTranspose` for `∂_q, ∂_η` -/

theorem coordTranspose_vQ0_vEta (j : Fin 2) (φ : Coord → ℝ) (x : Coord) :
    coordTranspose (![vQ0, vEta] j) dZero φ x = -cpd j.succ φ x := by
  have hzero : ∀ k : Fin 3, cpd k (fun _ : Coord => (0 : ℝ)) x = 0 := by
    intro k
    simp [cpd]
  fin_cases j
  · change coordTranspose vQ0 dZero φ x = -cpd 1 φ x
    unfold coordTranspose vQ0 dZero
    rw [Fin.sum_univ_three]
    simp [hzero]
  · change coordTranspose vEta dZero φ x = -cpd 2 φ x
    unfold coordTranspose vEta dZero
    rw [Fin.sum_univ_three]
    simp [hzero]

theorem coordTest_box {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    ∃ a b R : ℝ, 0 < a ∧ a ≤ b ∧ 0 < R ∧
      ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) →
        φ x = 0 ∧ ∀ j : Fin 3, cpd j φ x = 0 := by
  have hvan : ∀ x : Coord, x ∉ tsupport φ → φ x = 0 ∧ ∀ j : Fin 3, cpd j φ x = 0 := by
    intro x hx
    refine ⟨image_eq_zero_of_notMem_tsupport hx, fun j => ?_⟩
    simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
  obtain ⟨M, hM⟩ := hφ.compact.isBounded.subset_closedBall (0 : Coord)
  let R : ℝ := max 1 M
  have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hR_mem : ∀ x ∈ tsupport φ, |x.2.1| ≤ R ∧ |x.2.2| ≤ R := by
    intro x hx
    have hxM : ‖x‖ ≤ M := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hM hx
    have hxR : ‖x‖ ≤ R := hxM.trans (le_max_right _ _)
    have h2 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
    exact ⟨(Real.norm_eq_abs x.2.1 ▸ ( norm_fst_le x.2 ).trans (h2.trans hxR)),
      (Real.norm_eq_abs x.2.2 ▸ ( norm_snd_le x.2 ).trans (h2.trans hxR))⟩
  by_cases hne : (tsupport φ).Nonempty
  · let K₁ : Set ℝ := Prod.fst '' tsupport φ
    have hK₁_comp : IsCompact K₁ := hφ.compact.image continuous_fst
    have hK₁_ne : K₁.Nonempty := hne.image Prod.fst
    let a : ℝ := sInf K₁
    let b : ℝ := max a (sSup K₁)
    have ha_mem : a ∈ K₁ := hK₁_comp.sInf_mem hK₁_ne
    obtain ⟨x₀, hx₀, hx₀_eq⟩ := ha_mem
    have ha_pos : 0 < a := by
      rw [← hx₀_eq]
      exact (hφ.supp hx₀).1
    refine ⟨a, b, R, ha_pos, le_max_left _ _, hR_pos, fun x hx => hvan x fun hxt => ?_⟩
    have hx1 : x.1 ∈ K₁ := ⟨x, hxt, rfl⟩
    have hx_ab : x.1 ∈ Icc a b :=
      ⟨csInf_le hK₁_comp.bddBelow hx1,
        (le_csSup hK₁_comp.bddAbove hx1).trans (le_max_right _ _)⟩
    obtain ⟨hqR, hηR⟩ := hR_mem x hxt
    rcases hx with h1 | h2 | h3
    · exact h1 hx_ab
    · linarith
    · linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨1, 1, R, one_pos, le_rfl, hR_pos, fun x _ => hvan x ?_⟩
    rw [hne]
    exact notMem_empty x

/-! ### 2. `q`-Periodization of coordinate and planar solenoidal tests -/

/-- `q`-periodization of a function `φ : Coord → ℝ` on slice `s` with period `c`. -/
def qPeriodize (c : ℝ) (φ : Coord → ℝ) (s : ℝ) (z : B0579.Plane) : ℝ :=
  ∑' k : ℤ, φ (s, (z.1 + (k : ℝ) * c, z.2))

/-- Componentwise `q`-periodization of a planar test field `Ψ : Coord → Fin 2 → ℝ`. -/
def qPeriodizeVec (c : ℝ) (Ψ : Coord → Fin 2 → ℝ) (s : ℝ) (z : B0579.Plane) (i : Fin 2) : ℝ :=
  qPeriodize c (fun x => Ψ x i) s z

private theorem shift_outside_box {c R Q : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : (Q + R) / c + 1 < (N : ℝ))
    {z : B0579.Plane} (hz : |z.1| ≤ Q) {k : ℤ} (hk : k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    R < |z.1 + (k : ℝ) * c| := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (N : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : Q + R + c < ((N : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hN hc
    have hdiv : ((Q + R) / c + 1) * c = Q + R + c := by field_simp [hc.ne']
    linarith
  have h2 : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c :=
    mul_le_mul_of_nonneg_right hk_abs hc.le
  have h3 : |(k : ℝ)| * c - |z.1| ≤ |z.1 + (k : ℝ) * c| := by
    have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) z.1
    rw [add_comm, abs_mul, abs_of_pos hc] at hsub
    linarith
  linarith

private theorem qPeriodize_eq_finset {c R Q : ℝ} (hc : 0 < c) {α : Coord → ℝ}
    (hα : ∀ x : Coord, R < |x.2.1| → α x = 0) :
    ∃ N : ℕ, ∀ (s : ℝ) (z : B0579.Plane), |z.1| ≤ Q →
      qPeriodize c α s z =
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), α (s, (z.1 + (k : ℝ) * c, z.2)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((Q + R) / c + 1)
  refine ⟨N, fun s z hz => tsum_eq_sum fun k hk => ?_⟩
  exact hα (s, (z.1 + (k : ℝ) * c, z.2)) (shift_outside_box hc hN hz hk)

theorem qPeriodize_periodic {c : ℝ} (φ : Coord → ℝ) (s : ℝ) (z : B0579.Plane) :
    qPeriodize c φ s (z.1 + c, z.2) = qPeriodize c φ s z := by
  unfold qPeriodize
  have e : (fun k : ℤ => φ (s, (z.1 + c + (k : ℝ) * c, z.2))) =
      fun k : ℤ => φ (s, (z.1 + ((k + 1 : ℤ) : ℝ) * c, z.2)) := by
    funext k
    congr 2
    (ext <;> simp); ring
  rw [e]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => φ (s, (z.1 + (k : ℝ) * c, z.2)))

private theorem fderiv_slice_shift {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (s t : ℝ) (z : B0579.Plane) (j : Fin 2) :
    B0579.pd j (fun w : B0579.Plane => φ (s, (w.1 + t, w.2))) z =
      cpd j.succ φ (s, (z.1 + t, z.2)) := by
  let ι : B0579.Plane →L[ℝ] Coord := ContinuousLinearMap.inr ℝ ℝ B0579.Plane
  let p₀ : Coord := (s, (t, 0))
  have hfun : (fun w : B0579.Plane => φ (s, (w.1 + t, w.2))) = fun w => φ (ι w + p₀) := by
    funext w
    congr 1
    ext <;> simp [ι, p₀]
  have hg : HasFDerivAt (fun w : B0579.Plane => ι w + p₀) ι z :=
    (ι.hasFDerivAt).add_const p₀
  have hf : HasFDerivAt φ (fderiv ℝ φ (ι z + p₀)) (ι z + p₀) :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : fderiv ℝ (fun w : B0579.Plane => φ (ι w + p₀)) z =
      (fderiv ℝ φ (ι z + p₀)).comp ι := (hf.comp z hg).fderiv
  have hp : ι z + p₀ = (s, (z.1 + t, z.2)) := by
    ext <;> simp [ι, p₀]
  have hdir : ι (B0579.dir j) = cdir j.succ := by
    fin_cases j <;> rfl
  unfold B0579.pd cpd
  rw [hfun, hcomp, ContinuousLinearMap.comp_apply, hp, hdir]

theorem isCylTest_qPeriodize {c : ℝ} (hc : 0 < c) {φ : Coord → ℝ} (hφ : IsCoordTest φ) (s : ℝ) :
    B0579.IsCylTest c (qPeriodize c φ s) := by
  obtain ⟨_a, _b, R, _ha, _hab, _hR, hbox⟩ := coordTest_box hφ
  have hq : ∀ x : Coord, R < |x.2.1| → φ x = 0 := fun x hx => (hbox x (Or.inr (Or.inl hx))).1
  refine ⟨?_, qPeriodize_periodic φ s, R, fun z hz => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z₀
    obtain ⟨N, hN⟩ := qPeriodize_eq_finset (Q := |z₀.1| + 1) hc hq
    have hU : {z : B0579.Plane | |z.1| < |z₀.1| + 1} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (lt_add_one |z₀.1|)
    have hev : qPeriodize c φ s =ᶠ[𝓝 z₀]
        fun z : B0579.Plane =>
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ (s, (z.1 + (k : ℝ) * c, z.2)) :=
      Filter.eventually_of_mem hU fun z hz => hN s z (le_of_lt hz)
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine ContDiff.contDiffAt ?_
    refine ContDiff.sum fun k _ => ?_
    exact hφ.smooth.comp
      (contDiff_const.prodMk ((contDiff_fst.add contDiff_const).prodMk contDiff_snd))
  · unfold qPeriodize
    have h0 : (fun k : ℤ => φ (s, (z.1 + (k : ℝ) * c, z.2))) = fun _ => 0 :=
      funext fun k => (hbox (s, (z.1 + (k : ℝ) * c, z.2)) (Or.inr (Or.inr hz))).1
    rw [h0, tsum_zero]

theorem pd_qPeriodize {c : ℝ} (hc : 0 < c) {φ : Coord → ℝ} (hφ : IsCoordTest φ)
    (s : ℝ) (j : Fin 2) (z₀ : B0579.Plane) :
    B0579.pd j (qPeriodize c φ s) z₀ = qPeriodize c (cpd j.succ φ) s z₀ := by
  obtain ⟨_a, _b, R, _ha, _hab, _hR, hbox⟩ := coordTest_box hφ
  obtain ⟨N, hN⟩ := exists_nat_gt (((|z₀.1| + 1) + R) / c + 1)
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hU : {z : B0579.Plane | |z.1| < |z₀.1| + 1} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (lt_add_one |z₀.1|)
  have hev : qPeriodize c φ s =ᶠ[𝓝 z₀]
      fun z : B0579.Plane => ∑ k ∈ S, φ (s, (z.1 + (k : ℝ) * c, z.2)) := by
    refine Filter.eventually_of_mem hU fun z hz => ?_
    exact tsum_eq_sum fun k hk =>
      (hbox (s, (z.1 + (k : ℝ) * c, z.2))
        (Or.inr (Or.inl (shift_outside_box hc hN (le_of_lt hz) hk)))).1
  have hdiff : ∀ k ∈ S,
      DifferentiableAt ℝ (fun z : B0579.Plane => φ (s, (z.1 + (k : ℝ) * c, z.2))) z₀ := by
    intro k _
    exact ((hφ.smooth.comp
      (contDiff_const.prodMk ((contDiff_fst.add contDiff_const).prodMk contDiff_snd))).differentiable
      (by simp)).differentiableAt
  have hfd_sum : fderiv ℝ (fun z : B0579.Plane => ∑ k ∈ S, φ (s, (z.1 + (k : ℝ) * c, z.2))) z₀ =
      ∑ k ∈ S, fderiv ℝ (fun z : B0579.Plane => φ (s, (z.1 + (k : ℝ) * c, z.2))) z₀ :=
    fderiv_fun_sum hdiff
  have hrhs : qPeriodize c (cpd j.succ φ) s z₀ =
      ∑ k ∈ S, cpd j.succ φ (s, (z₀.1 + (k : ℝ) * c, z₀.2)) := by
    refine tsum_eq_sum fun k hk => ?_
    exact (hbox (s, (z₀.1 + (k : ℝ) * c, z₀.2))
      (Or.inr (Or.inl (shift_outside_box hc hN (le_add_of_nonneg_right zero_le_one) hk)))).2 j.succ
  unfold B0579.pd
  rw [hev.fderiv_eq, hfd_sum, FunLike.coe_sum, Finset.sum_apply, hrhs]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact fderiv_slice_shift hφ.smooth s ((k : ℝ) * c) z₀ j

theorem isDivFreeTestField_qPeriodizeVec {c : ℝ} (hc : 0 < c)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) (s : ℝ) :
    IIIa.IsDivFreeTestField c (qPeriodizeVec c Ψ s) := by
  refine ⟨fun i => isCylTest_qPeriodize hc (hΨ.smooth i) s, fun z => ?_⟩
  change B0579.pd 0 (qPeriodize c (fun y => Ψ y 0) s) z +
      B0579.pd 1 (qPeriodize c (fun y => Ψ y 1) s) z = 0
  rw [pd_qPeriodize hc (hΨ.smooth 0) s 0 z, pd_qPeriodize hc (hΨ.smooth 1) s 1 z]
  change qPeriodize c (cpd 1 (fun y => Ψ y 0)) s z +
      qPeriodize c (cpd 2 (fun y => Ψ y 1)) s z = 0
  obtain ⟨_a0, _b0, R0, _, _, _, hbox0⟩ := coordTest_box (hΨ.smooth 0)
  obtain ⟨_a1, _b1, R1, _, _, _, hbox1⟩ := coordTest_box (hΨ.smooth 1)
  obtain ⟨N, hN⟩ := exists_nat_gt ((|z.1| + max R0 R1) / c + 1)
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hs0 : qPeriodize c (cpd 1 (fun y => Ψ y 0)) s z =
      ∑ k ∈ S, cpd 1 (fun y => Ψ y 0) (s, (z.1 + (k : ℝ) * c, z.2)) := by
    refine tsum_eq_sum fun k hk => ?_
    have hout := shift_outside_box hc hN (le_refl |z.1|) hk
    exact (hbox0 (s, (z.1 + (k : ℝ) * c, z.2))
      (Or.inr (Or.inl ((le_max_left R0 R1).trans_lt hout)))).2 1
  have hs1 : qPeriodize c (cpd 2 (fun y => Ψ y 1)) s z =
      ∑ k ∈ S, cpd 2 (fun y => Ψ y 1) (s, (z.1 + (k : ℝ) * c, z.2)) := by
    refine tsum_eq_sum fun k hk => ?_
    have hout := shift_outside_box hc hN (le_refl |z.1|) hk
    exact (hbox1 (s, (z.1 + (k : ℝ) * c, z.2))
      (Or.inr (Or.inl ((le_max_right R0 R1).trans_lt hout)))).2 2
  rw [hs0, hs1, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  exact hΨ.div_free (s, (z.1 + (k : ℝ) * c, z.2))

/-! ### 3. Unfolding `∫_{Coord} u α` into `∫_{Icc a b} ∫_{cell c} u (qPeriodize α)` -/

private def coordQShift (t : ℝ) (x : Coord) : Coord := x + (0, (t, 0))

private theorem ae_coordQShift_int {c : ℝ} {u : Coord → ℂ}
    (hu_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), u (qShift c x) = u x) (k : ℤ) :
    ∀ᵐ x : Coord ∂volume, 0 < x.1 → u (coordQShift ((k : ℝ) * c) x) = u x := by
  have h1 : ∀ᵐ x : Coord ∂volume, 0 < x.1 → u (coordQShift c x) = u x := by
    filter_upwards [(ae_restrict_iff' QPerHalf.measurableSet_pos).1 hu_per] with x hx hpos
    have heq : coordQShift c x = qShift c x := by ext <;> simp [coordQShift, qShift]
    rw [heq]
    exact hx hpos
  induction k using Int.induction_on with
  | zero =>
    refine Eventually.of_forall fun x _ => ?_
    have heq : coordQShift (((0 : ℤ) : ℝ) * c) x = x := by ext <;> simp [coordQShift]
    rw [heq]
  | succ n ih =>
    have hshift : ∀ᵐ x : Coord ∂volume,
        0 < (coordQShift ((n : ℝ) * c) x).1 →
          u (coordQShift c (coordQShift ((n : ℝ) * c) x)) = u (coordQShift ((n : ℝ) * c) x) :=
      (measurePreserving_add_right volume ((0, ((n : ℝ) * c, 0)) : Coord)).quasiMeasurePreserving.ae h1
    filter_upwards [ih, hshift] with x hih hsh hpos
    have hpos' : 0 < (coordQShift ((n : ℝ) * c) x).1 := by simpa [coordQShift] using hpos
    push_cast
    have hcomp : coordQShift (((n : ℝ) + 1) * c) x =
        coordQShift c (coordQShift ((n : ℝ) * c) x) := by
      (ext <;> simp [coordQShift]); ring
    rw [hcomp, hsh hpos']
    simpa using hih hpos
  | pred n ih =>
    have hshift : ∀ᵐ x : Coord ∂volume,
        0 < (coordQShift ((-(n : ℝ) - 1) * c) x).1 →
          u (coordQShift c (coordQShift ((-(n : ℝ) - 1) * c) x)) =
            u (coordQShift ((-(n : ℝ) - 1) * c) x) :=
      (measurePreserving_add_right volume
        ((0, ((-(n : ℝ) - 1) * c, 0)) : Coord)).quasiMeasurePreserving.ae h1
    filter_upwards [ih, hshift] with x hih hsh hpos
    have hpos' : 0 < (coordQShift ((-(n : ℝ) - 1) * c) x).1 := by simpa [coordQShift] using hpos
    have hcomp : coordQShift c (coordQShift ((-(n : ℝ) - 1) * c) x) =
        coordQShift (-(n : ℝ) * c) x := by
      (ext <;> simp [coordQShift]); ring
    have hsh' := hsh hpos'
    rw [hcomp] at hsh'
    have hcast : (((-(n : ℤ) - 1 : ℤ) : ℝ) * c) = (-(n : ℝ) - 1) * c := by push_cast; ring
    have hih' : u (coordQShift (-(n : ℝ) * c) x) = u x := by
      simpa using hih hpos
    rw [hcast, ← hsh', hih']

private theorem integrableOn_cellBox_of_loc_L2 {c a b R : ℝ} (_hc : 0 < c) (_hR : 0 < R)
    {u : Coord → ℂ} (hu_meas : AEStronglyMeasurable u volume)
    (hu_loc : (∫⁻ s in Icc a b,
      eLpNorm (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c))) < ⊤) :
    IntegrableOn u (Icc a b ×ˢ (Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) volume := by
  let B : Set B0579.Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hB_sub : B ⊆ B0579.cell c := prod_mono Subset.rfl (subset_univ _)
  have hB_fin : volume B < ⊤ := by
    dsimp [B]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  let u' : Coord → ℂ := hu_meas.mk u
  have hu'_sm : StronglyMeasurable u' := hu_meas.stronglyMeasurable_mk
  have hu_ae : u =ᵐ[volume] u' := hu_meas.ae_eq_mk
  rw [integrableOn_congr_fun_ae (ae_restrict_of_ae hu_ae)]
  refine ⟨hu'_sm.aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h_ton : ∫⁻ x in Icc a b ×ˢ B, ‖u' x‖ₑ =
      ∫⁻ s in Icc a b, ∫⁻ z in B, ‖u' (s, z)‖ₑ :=
    setLIntegral_prod (fun x : Coord => ‖u' x‖ₑ) hu'_sm.enorm.aemeasurable.restrict
  have h_slice_ae : ∀ᵐ s ∂volume,
      eLpNorm (fun z => u' (s, z)) 2 (volume.restrict (B0579.cell c)) =
        eLpNorm (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c)) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hu_ae.symm] with s hs
    exact eLpNorm_congr_ae (ae_restrict_of_ae hs)
  have h_pt : ∀ s : ℝ, ∫⁻ z in B, ‖u' (s, z)‖ₑ ≤
      eLpNorm (fun z => u' (s, z)) 2 (volume.restrict (B0579.cell c)) *
        (volume B) ^ (1 / 2 : ℝ) := by
    intro s
    have hsm_s : StronglyMeasurable (fun z : B0579.Plane => u' (s, z)) :=
      hu'_sm.comp_measurable (measurable_const.prodMk measurable_id)
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict B) (p := 1) (q := 2) one_le_two hsm_s.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm, Measure.restrict_apply_univ] at hH
    have hexp : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    rw [hexp] at hH
    exact hH.trans (mul_le_mul
      (eLpNorm_mono_measure _ (Measure.restrict_mono hB_sub le_rfl))
      (le_refl _) zero_le zero_le)
  rw [h_ton]
  have h_le : ∫⁻ s in Icc a b, ∫⁻ z in B, ‖u' (s, z)‖ₑ ≤
      (∫⁻ s in Icc a b, eLpNorm (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c))) *
        (volume B) ^ (1 / 2 : ℝ) := by
    calc ∫⁻ s in Icc a b, ∫⁻ z in B, ‖u' (s, z)‖ₑ
        ≤ ∫⁻ s in Icc a b,
            eLpNorm (fun z => u' (s, z)) 2 (volume.restrict (B0579.cell c)) *
              (volume B) ^ (1 / 2 : ℝ) :=
          lintegral_mono h_pt
      _ = ∫⁻ s in Icc a b,
            eLpNorm (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c)) *
              (volume B) ^ (1 / 2 : ℝ) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae h_slice_ae] with s hs
          rw [hs]
      _ = (∫⁻ s in Icc a b, eLpNorm (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c))) *
            (volume B) ^ (1 / 2 : ℝ) := by
          rw [lintegral_mul_const']
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB_fin.ne
  exact h_le.trans_lt (ENNReal.mul_lt_top hu_loc
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB_fin.ne))

theorem integrable_and_integral_coord_eq_cell_qPeriodize
    {c a b R : ℝ} (hc : 0 < c) (ha : 0 < a) (_hab : a ≤ b) (hR : 0 < R)
    {u : Coord → ℂ} (hu_meas : AEStronglyMeasurable u volume)
    (hu_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), u (qShift c x) = u x)
    (hu_loc : (∫⁻ s in Icc a b,
      eLpNorm (fun z => u (s, z)) 2 (volume.restrict (B0579.cell c))) < ⊤)
    {α : Coord → ℝ} (hα_cont : Continuous α)
    (hα_supp : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → α x = 0) :
    Integrable (fun x : Coord => u x * (α x : ℂ)) volume ∧
      IntegrableOn (fun x : Coord => u x * (qPeriodize c α x.1 x.2 : ℂ))
        (Icc a b ×ˢ B0579.cell c) volume ∧
      ∫ x : Coord, u x * (α x : ℂ) =
        ∫ s in Icc a b, ∫ z in B0579.cell c, u (s, z) * (qPeriodize c α s z : ℂ) := by
  let Box : Set Coord := Icc a b ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hBox_comp : IsCompact Box := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨M0, hM0⟩ := hBox_comp.exists_bound_of_continuousOn hα_cont.continuousOn
  let M : ℝ := max 0 M0
  have hα_bdd : ∀ x : Coord, ‖(α x : ℂ)‖ ≤ M := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hx : x ∈ Box
    · exact (Real.norm_eq_abs (α x) ▸ hM0 x hx).trans (le_max_right 0 M0)
    · have h0 : α x = 0 := by
        apply hα_supp
        by_contra hnot
        push Not at hnot
        apply hx
        exact ⟨hnot.1, abs_le.1 hnot.2.1, abs_le.1 hnot.2.2⟩
      rw [h0, abs_zero]
      exact le_max_left 0 M0
  obtain ⟨K, hK⟩ := exists_nat_gt ((c / 2 + R) / c + 1)
  let I : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let B : Set B0579.Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  let S : ℤ → Set B0579.Plane := fun k =>
    Ico (-(c / 2) + (k : ℝ) * c) (c / 2 + (k : ℝ) * c) ×ˢ Icc (-R) R
  let T : ℤ → Set Coord := fun k => Icc a b ×ˢ S k
  have hT_meas : ∀ k : ℤ, MeasurableSet (T k) :=
    fun _ => measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
  have hU_meas : MeasurableSet (⋃ k ∈ I, T k) := Finset.measurableSet_biUnion I (fun k _ => hT_meas k)
  have h_compl_zero : ∀ x : Coord, x ∉ ⋃ k ∈ I, T k → u x * (α x : ℂ) = 0 := by
    intro x hx
    suffices h0 : α x = 0 by simp [h0]
    apply hα_supp
    by_contra hnot
    push Not at hnot
    obtain ⟨hx_ab, hxq, hxη⟩ := hnot
    let m : ℤ := ⌊(x.2.1 + c / 2) / c⌋
    have hm1 : (m : ℝ) ≤ (x.2.1 + c / 2) / c := Int.floor_le _
    have hm2 : (x.2.1 + c / 2) / c < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have hm_lo : -(c / 2) + (m : ℝ) * c ≤ x.2.1 := by
      have h := mul_le_mul_of_nonneg_right hm1 hc.le
      have hdiv : (x.2.1 + c / 2) / c * c = x.2.1 + c / 2 := div_mul_cancel₀ _ hc.ne'
      linarith
    have hm_hi : x.2.1 < c / 2 + (m : ℝ) * c := by
      have h := mul_lt_mul_of_pos_right hm2 hc
      have hdiv : (x.2.1 + c / 2) / c * c = x.2.1 + c / 2 := div_mul_cancel₀ _ hc.ne'
      linarith
    have hm_I : m ∈ I := by
      rw [Finset.mem_Icc]
      rw [abs_le] at hxq
      have hKc : c / 2 + R + c < (K : ℝ) * c := by
        have h := mul_lt_mul_of_pos_right hK hc
        have hd : ((c / 2 + R) / c + 1) * c = c / 2 + R + c := by field_simp [hc.ne']
        linarith
      have h_upper : (m : ℝ) < (K : ℝ) := by
        have : (m : ℝ) * c < (K : ℝ) * c := by linarith
        exact (mul_lt_mul_iff_left₀ hc).1 this
      have h_lower : -(K : ℝ) < (m : ℝ) := by
        have : -(K : ℝ) * c < (m : ℝ) * c := by linarith
        exact (mul_lt_mul_iff_left₀ hc).1 this
      constructor
      · have h' : -(K : ℤ) < m := by exact_mod_cast h_lower
        omega
      · have h' : m < (K : ℤ) := by exact_mod_cast h_upper
        omega
    apply hx
    rw [mem_iUnion₂]
    exact ⟨m, hm_I, hx_ab, ⟨hm_lo, hm_hi⟩, abs_le.1 hxη⟩
  have hT_disj : PairwiseDisjoint (I : Set ℤ) T := by
    intro k _ l _ hkl
    change Disjoint (T k) (T l)
    rw [Set.disjoint_left]
    intro x hxk hxl
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · have hle : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hlt
      have hk_hi : x.2.1 < c / 2 + (k : ℝ) * c := hxk.2.1.2
      have hl_lo : -(c / 2) + (l : ℝ) * c ≤ x.2.1 := hxl.2.1.1
      nlinarith
    · have hle : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hlt
      have hl_hi : x.2.1 < c / 2 + (l : ℝ) * c := hxl.2.1.2
      have hk_lo : -(c / 2) + (k : ℝ) * c ≤ x.2.1 := hxk.2.1.1
      nlinarith
  have hu_box : IntegrableOn u (Icc a b ×ˢ B) volume :=
    integrableOn_cellBox_of_loc_L2 hc hR hu_meas hu_loc
  have hpre : ∀ k : ℤ, coordQShift ((k : ℝ) * c) ⁻¹' T k = Icc a b ×ˢ B := by
    intro k
    ext x
    simp only [coordQShift, T, S, B, mem_preimage, mem_prod, mem_Icc, mem_Ico,
      Prod.fst_add, Prod.snd_add, add_zero]
    constructor <;> rintro ⟨hab, ⟨hq1, hq2⟩, hη⟩ <;>
      exact ⟨hab, ⟨by linarith, by linarith⟩, hη⟩
  have hBox_meas : MeasurableSet (Icc a b ×ˢ B) :=
    measurableSet_Icc.prod (measurableSet_Ico.prod measurableSet_Icc)
  have hCell_meas : MeasurableSet (Icc a b ×ˢ B0579.cell c) :=
    measurableSet_Icc.prod (B0579.measurableSet_cell c)
  have hBox_sub_cell : Icc a b ×ˢ B ⊆ Icc a b ×ˢ B0579.cell c :=
    prod_mono Subset.rfl (prod_mono Subset.rfl (subset_univ _))
  have hae_box : ∀ k : ℤ,
      (fun x : Coord => u (coordQShift ((k : ℝ) * c) x)) =ᵐ[volume.restrict (Icc a b ×ˢ B)] u := by
    intro k
    change ∀ᵐ x : Coord ∂(volume.restrict (Icc a b ×ˢ B)), u (coordQShift ((k : ℝ) * c) x) = u x
    rw [ae_restrict_iff' hBox_meas]
    filter_upwards [ae_coordQShift_int hu_per k] with x hx hmem
    exact hx (lt_of_lt_of_le ha hmem.1.1)
  have hint_cell_k : ∀ k : ℤ,
      IntegrableOn (fun x : Coord => u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ))
        (Icc a b ×ˢ B0579.cell c) volume := by
    classical
    intro k
    have hαk_meas : AEStronglyMeasurable
        (fun x : Coord => (α (coordQShift ((k : ℝ) * c) x) : ℂ))
        (volume.restrict (Icc a b ×ˢ B)) :=
      (Complex.continuous_ofReal.comp
        (hα_cont.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    have hint_B : IntegrableOn (fun x : Coord => u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ))
        (Icc a b ×ˢ B) volume :=
      hu_box.mul_bdd hαk_meas
        (Eventually.of_forall fun x => hα_bdd (coordQShift ((k : ℝ) * c) x))
    have hdiff_zero : ∀ x ∈ (Icc a b ×ˢ B0579.cell c) \ (Icc a b ×ˢ B),
        u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ) = 0 := by
      intro x ⟨⟨hx_ab, hx_cell⟩, hx_notB⟩
      have hnot_η : x.2.2 ∉ Icc (-R) R := fun hη => hx_notB ⟨hx_ab, hx_cell.1, hη⟩
      have hη_gt : R < |x.2.2| := by
        by_contra hle
        push Not at hle
        exact hnot_η (abs_le.1 hle)
      have h0 : α (coordQShift ((k : ℝ) * c) x) = 0 :=
        hα_supp _ (Or.inr (Or.inr (by simpa [coordQShift] using hη_gt)))
      simp [h0]
    have h_ind : (Icc a b ×ˢ B).piecewise
        (fun x : Coord => u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ)) 0 =
        (Icc a b ×ˢ B0579.cell c).piecewise
          (fun x : Coord => u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ)) 0 := by
      funext x
      by_cases hxB : x ∈ Icc a b ×ˢ B
      · rw [Set.piecewise_eq_of_mem _ _ _ hxB,
          Set.piecewise_eq_of_mem _ _ _ (hBox_sub_cell hxB)]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxB]
        by_cases hxC : x ∈ Icc a b ×ˢ B0579.cell c
        · rw [Set.piecewise_eq_of_mem _ _ _ hxC]
          exact (hdiff_zero x ⟨hxC, hxB⟩).symm
        · rw [Set.piecewise_eq_of_notMem _ _ _ hxC]
    have hp1 : Integrable ((Icc a b ×ˢ B).piecewise
        (fun x : Coord => u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ)) 0) volume :=
      Integrable.piecewise hBox_meas hint_B integrableOn_zero
    rw [h_ind] at hp1
    refine (hp1.integrableOn (s := Icc a b ×ˢ B0579.cell c)).congr_fun ?_ hCell_meas
    intro x hx
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hint_Tk : ∀ k ∈ I, IntegrableOn (fun x : Coord => u x * (α x : ℂ)) (T k) volume := by
    intro k _
    have hint_B : IntegrableOn
        (fun x : Coord => u (coordQShift ((k : ℝ) * c) x) *
          (α (coordQShift ((k : ℝ) * c) x) : ℂ))
        (Icc a b ×ˢ B) volume := by
      refine ((hint_cell_k k).mono_set hBox_sub_cell).congr_fun_ae ?_
      filter_upwards [hae_box k] with x hx
      rw [hx]
    have hmp : MeasurePreserving (coordQShift ((k : ℝ) * c)) volume volume :=
      measurePreserving_add_right volume ((0, ((k : ℝ) * c, 0)) : Coord)
    have hemb : MeasurableEmbedding (coordQShift ((k : ℝ) * c)) :=
      measurableEmbedding_addRight ((0, ((k : ℝ) * c, 0)) : Coord)
    rw [← hpre k] at hint_B
    exact (hmp.integrableOn_comp_preimage hemb).1 hint_B
  have hint_U : IntegrableOn (fun x : Coord => u x * (α x : ℂ)) (⋃ k ∈ I, T k) volume :=
    integrableOn_finset_iUnion.2 hint_Tk
  have hint_all : Integrable (fun x : Coord => u x * (α x : ℂ)) volume := by
    classical
    have hpw : (⋃ k ∈ I, T k).piecewise (fun x : Coord => u x * (α x : ℂ)) 0 =
        fun x : Coord => u x * (α x : ℂ) := by
      funext x
      by_cases hx : x ∈ ⋃ k ∈ I, T k
      · exact Set.piecewise_eq_of_mem _ _ _ hx
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        exact (h_compl_zero x hx).symm
    rw [← hpw]
    exact Integrable.piecewise hU_meas hint_U integrableOn_zero
  have h_step1 : ∫ x : Coord, u x * (α x : ℂ) =
      ∑ k ∈ I, ∫ x in T k, u x * (α x : ℂ) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl_zero,
      integral_biUnion_finset I (fun k _ => hT_meas k) hT_disj hint_Tk]
  have h_step2 : ∀ k ∈ I, ∫ x in T k, u x * (α x : ℂ) =
      ∫ x in Icc a b ×ˢ B0579.cell c, u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ) := by
    intro k _
    have hmp : MeasurePreserving (coordQShift ((k : ℝ) * c)) volume volume :=
      measurePreserving_add_right volume ((0, ((k : ℝ) * c, 0)) : Coord)
    have hemb : MeasurableEmbedding (coordQShift ((k : ℝ) * c)) :=
      measurableEmbedding_addRight ((0, ((k : ℝ) * c, 0)) : Coord)
    have h1 := hmp.setIntegral_preimage_emb hemb (fun x : Coord => u x * (α x : ℂ)) (T k)
    rw [hpre k] at h1
    have h2 : ∫ x in Icc a b ×ˢ B,
          u (coordQShift ((k : ℝ) * c) x) * (α (coordQShift ((k : ℝ) * c) x) : ℂ) =
        ∫ x in Icc a b ×ˢ B, u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hae_box k] with x hx
      rw [hx]
    have h3 : ∫ x in Icc a b ×ˢ B, u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ) =
        ∫ x in Icc a b ×ˢ B0579.cell c, u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ) := by
      refine (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hCell_meas hBox_sub_cell ?_).symm
      intro x ⟨⟨hx_ab, hx_cell⟩, hx_notB⟩
      have hnot_η : x.2.2 ∉ Icc (-R) R := fun hη => hx_notB ⟨hx_ab, hx_cell.1, hη⟩
      have hη_gt : R < |x.2.2| := by
        by_contra hle; push Not at hle; exact hnot_η (abs_le.1 hle)
      have h0 : α (coordQShift ((k : ℝ) * c) x) = 0 :=
        hα_supp _ (Or.inr (Or.inr (by simpa [coordQShift] using hη_gt)))
      simp [h0]
    exact h1.symm.trans (h2.trans h3)
  have hint_sum_cell : IntegrableOn
      (fun x : Coord => ∑ k ∈ I, u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ))
      (Icc a b ×ˢ B0579.cell c) volume :=
    integrable_finsetSum I fun k _ => hint_cell_k k
  have h_eq_on_cell : EqOn
      (fun x : Coord => ∑ k ∈ I, u x * (α (coordQShift ((k : ℝ) * c) x) : ℂ))
      (fun x : Coord => u x * (qPeriodize c α x.1 x.2 : ℂ))
      (Icc a b ×ˢ B0579.cell c) := by
    intro ⟨s, z⟩ hsz
    have hz_abs : |z.1| ≤ c / 2 := abs_le.2 ⟨hsz.2.1.1, le_of_lt hsz.2.1.2⟩
    have hper_eq : qPeriodize c α s z = ∑ k ∈ I, α (s, (z.1 + (k : ℝ) * c, z.2)) :=
      tsum_eq_sum fun k hk =>
        hα_supp _ (Or.inr (Or.inl (shift_outside_box hc hK hz_abs hk)))
    have hshift_eq : ∀ k : ℤ,
        coordQShift ((k : ℝ) * c) (s, z) = (s, (z.1 + (k : ℝ) * c, z.2)) := by
      intro k; ext <;> simp [coordQShift]
    simp_rw [hshift_eq]
    rw [hper_eq, Complex.ofReal_sum, Finset.mul_sum]
  have hint_per_cell : IntegrableOn
      (fun x : Coord => u x * (qPeriodize c α x.1 x.2 : ℂ))
      (Icc a b ×ˢ B0579.cell c) volume :=
    hint_sum_cell.congr_fun h_eq_on_cell hCell_meas
  have hint_per_prod : IntegrableOn
      (fun x : Coord => u x * (qPeriodize c α x.1 x.2 : ℂ))
      (Icc a b ×ˢ B0579.cell c) ((volume : Measure ℝ).prod (volume : Measure B0579.Plane)) := by
    rwa [← Measure.volume_eq_prod]
  have h_fub : ∫ x in Icc a b ×ˢ B0579.cell c, u x * (qPeriodize c α x.1 x.2 : ℂ) =
      ∫ s in Icc a b, ∫ z in B0579.cell c, u (s, z) * (qPeriodize c α s z : ℂ) := by
    rw [Measure.volume_eq_prod (α := ℝ) (β := B0579.Plane)]
    exact setIntegral_prod _ hint_per_prod
  refine ⟨hint_all, hint_per_cell, ?_⟩
  rw [h_step1, Finset.sum_congr rfl h_step2,
    ← integral_finsetSum I (fun k _ => hint_cell_k k),
    setIntegral_congr_fun hCell_meas h_eq_on_cell, h_fub]

/-! ### 4. High-level corollaries: `sliceWeakToJoint` and `sliceBodySourceToJoint` -/

private theorem eLpNorm_comp_le_merid (c : ℝ) (g : CProf) (s : ℝ) (i : Fin 2) :
    eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) := by
  refine eLpNorm_mono_enorm fun z => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact_mod_cast PiLp.norm_apply_le (g (s, z)) i

private theorem fubini_cell_slices {c a b : ℝ} {F : Coord → ℂ}
    (hF : IntegrableOn F (Icc a b ×ˢ B0579.cell c) volume) :
    IntegrableOn (fun s : ℝ => ∫ z in B0579.cell c, F (s, z)) (Icc a b) volume ∧
      ∀ᵐ s ∂(volume.restrict (Icc a b)),
        IntegrableOn (fun z : B0579.Plane => F (s, z)) (B0579.cell c) volume := by
  have hF' : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell c))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact ⟨hF'.integral_prod_left, hF'.prod_right_ae⟩

theorem sliceWeakToJoint {c : ℝ} (hc : 0 < c) (j : Fin 2) (g G : CProf)
    (hg_meas : StronglyMeasurable g) (hG_meas : StronglyMeasurable G)
    (hg_per : QPeriodic c g) (hG_per : QPeriodic c G)
    (hLoc : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c)))) < ⊤)
    (hWeak : ∀ᵐ s ∂volume, 0 < s → ∀ i : Fin 2,
      IIIa.HasWeakCellDerivC c j (fun z => g (s, z) i) (fun z => G (s, z) i)) :
    HasWeakVec (![vQ0, vEta] j) dZero g G := by
  intro i
  have hgi_meas : AEStronglyMeasurable (fun x : Coord => g x i) volume :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      hg_meas).aestronglyMeasurable
  have hGi_meas : AEStronglyMeasurable (fun x : Coord => G x i) volume :=
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      hG_meas).aestronglyMeasurable
  have hgi_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), g (qShift c x) i = g x i :=
    hg_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
  have hGi_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), G (qShift c x) i = G x i :=
    hG_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
  have hpair : ∀ φ : Coord → ℝ, IsCoordTest φ →
      (Integrable (fun x => g x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) ∧
        Integrable (fun x => G x i * (φ x : ℂ))) ∧
      ∫ x, G x i * (φ x : ℂ) =
        ∫ x, g x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ) := by
    intro φ hφ
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := coordTest_box hφ
    have hLoc_ab := hLoc a b ha
    have hg_loc : (∫⁻ s in Icc a b,
        eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      (lintegral_mono fun s => (eLpNorm_comp_le_merid c g s i).trans le_self_add).trans_lt hLoc_ab
    have hG_loc : (∫⁻ s in Icc a b,
        eLpNorm (fun z => G (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      (lintegral_mono fun s => (eLpNorm_comp_le_merid c G s i).trans le_add_self).trans_lt hLoc_ab
    have hcpd_cont : Continuous (cpd j.succ φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const).continuous
    obtain ⟨hint_cpd, _, heq_cpd⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR hgi_meas hgi_per hg_loc
        hcpd_cont (fun x hx => (hbox x hx).2 j.succ)
    obtain ⟨hint_G, _, heq_G⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR hGi_meas hGi_per hG_loc
        hφ.smooth.continuous (fun x hx => (hbox x hx).1)
    have hct_eq : (fun x : Coord => g x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)) =
        fun x : Coord => -(g x i * (cpd j.succ φ x : ℂ)) := by
      funext x
      rw [coordTranspose_vQ0_vEta, Complex.ofReal_neg, mul_neg]
    refine ⟨⟨hct_eq ▸ hint_cpd.neg, hint_G⟩, ?_⟩
    rw [heq_G, hct_eq, integral_neg, heq_cpd, ← integral_neg]
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hWeak] with s hs hs_ab
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs_ab.1
    have hcell := (hs hs_pos i).2 (qPeriodize c φ s) (isCylTest_qPeriodize hc hφ s)
    simp_rw [pd_qPeriodize hc hφ s j] at hcell
    rw [hcell, neg_neg]
  exact ⟨fun φ hφ => (hpair φ hφ).1, fun φ hφ => (hpair φ hφ).2⟩

theorem sliceBodySourceToJoint {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (b0 b0q b0η g : CProf)
    (hg_meas : StronglyMeasurable g)
    (hU_meas : AEStronglyMeasurable (flatBv tr b0 b0q b0η) volume)
    (hg_per : QPeriodic c g)
    (hU_per : QPeriodic c (flatBv tr b0 b0q b0η))
    (hLoc : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun z => flatBv tr b0 b0q b0η (s, z)) 2
            (volume.restrict (B0579.cell c)))) < ⊤)
    (hSol : ∀ᵐ s ∂volume, 0 < s → ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ →
      ∫ z in B0579.cell c,
        (g (s, z) 0 * (B0579.pd 0 ψ z : ℂ) + g (s, z) 1 * (B0579.pd 1 ψ z : ℂ)) = 0)
    (hOrth : ∀ᵐ s ∂volume, 0 < s → ∀ Ψ : B0579.Plane → Fin 2 → ℝ, IIIa.IsDivFreeTestField c Ψ →
      ∫ z in B0579.cell c,
        ∑ i : Fin 2, (g (s, z) i + flatBv tr b0 b0q b0η (s, z) i) * (Ψ z i : ℂ) = 0) :
    IsBodySource tr b0 b0q b0η g := by
  let U := flatBv tr b0 b0q b0η
  have hgi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => g x i) volume := fun i =>
    ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
      hg_meas).aestronglyMeasurable
  have hUi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => U x i) volume := fun i =>
    (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hU_meas
  have hgi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      g (qShift c x) i = g x i :=
    fun i => hg_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
  have hUi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      U (qShift c x) i = U x i :=
    fun i => hU_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
  refine ⟨?_, ?_⟩
  · intro φ hφ
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := coordTest_box hφ
    have hLoc_ab := hLoc a b ha
    have hg0_loc : (∫⁻ s in Icc a b,
        eLpNorm (fun z => g (s, z) 0) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      (lintegral_mono fun s => (eLpNorm_comp_le_merid c g s 0).trans le_self_add).trans_lt hLoc_ab
    have hg1_loc : (∫⁻ s in Icc a b,
        eLpNorm (fun z => g (s, z) 1) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      (lintegral_mono fun s => (eLpNorm_comp_le_merid c g s 1).trans le_self_add).trans_lt hLoc_ab
    have hcpd1_cont : Continuous (cpd 1 φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const).continuous
    have hcpd2_cont : Continuous (cpd 2 φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const).continuous
    obtain ⟨hint0, hcell0, heq0⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR (hgi_meas 0) (hgi_per 0)
        hg0_loc hcpd1_cont (fun x hx => (hbox x hx).2 1)
    obtain ⟨hint1, hcell1, heq1⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR (hgi_meas 1) (hgi_per 1)
        hg1_loc hcpd2_cont (fun x hx => (hbox x hx).2 2)
    obtain ⟨hs_int0, hz_int0⟩ := fubini_cell_slices hcell0
    obtain ⟨hs_int1, hz_int1⟩ := fubini_cell_slices hcell1
    dsimp only at hs_int0 hs_int1 hz_int0 hz_int1
    refine ⟨hint0.add hint1, ?_⟩
    rw [integral_add hint0 hint1, heq0, heq1, ← integral_add hs_int0 hs_int1]
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
    filter_upwards [ae_restrict_of_ae hSol, hz_int0, hz_int1,
      ae_restrict_mem measurableSet_Icc] with s hs hi0 hi1 hs_ab
    rw [← integral_add hi0 hi1]
    have hpd0 : (fun z => qPeriodize c (cpd 1 φ) s z) = B0579.pd 0 (qPeriodize c φ s) :=
      funext fun z => (pd_qPeriodize hc hφ s 0 z).symm
    have hpd1 : (fun z => qPeriodize c (cpd 2 φ) s z) = B0579.pd 1 (qPeriodize c φ s) :=
      funext fun z => (pd_qPeriodize hc hφ s 1 z).symm
    simp_rw [hpd0, hpd1]
    exact hs (lt_of_lt_of_le ha hs_ab.1) (qPeriodize c φ s) (isCylTest_qPeriodize hc hφ s)
  · intro Ψ hΨ
    obtain ⟨a0, b0', R0, ha0, hab0, hR0, hbox0⟩ := coordTest_box (hΨ.smooth 0)
    obtain ⟨a1, b1', R1, ha1, hab1, hR1, hbox1⟩ := coordTest_box (hΨ.smooth 1)
    let a : ℝ := min a0 a1
    let b : ℝ := max b0' b1'
    let R : ℝ := max R0 R1
    have ha : 0 < a := lt_min ha0 ha1
    have hab : a ≤ b := (min_le_left a0 a1).trans (hab0.trans (le_max_left b0' b1'))
    have hR : 0 < R := lt_of_lt_of_le hR0 (le_max_left R0 R1)
    have hsupp0 : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ x 0 = 0 := by
      intro x hx
      refine (hbox0 x ?_).1
      rcases hx with h1 | h2 | h3
      · exact Or.inl fun hmem => h1 ⟨(min_le_left a0 a1).trans hmem.1, hmem.2.trans (le_max_left _ _)⟩
      · exact Or.inr (Or.inl ((le_max_left R0 R1).trans_lt h2))
      · exact Or.inr (Or.inr ((le_max_left R0 R1).trans_lt h3))
    have hsupp1 : ∀ x : Coord, (x.1 ∉ Icc a b ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ x 1 = 0 := by
      intro x hx
      refine (hbox1 x ?_).1
      rcases hx with h1 | h2 | h3
      · exact Or.inl fun hmem => h1 ⟨(min_le_right a0 a1).trans hmem.1, hmem.2.trans (le_max_right _ _)⟩
      · exact Or.inr (Or.inl ((le_max_right R0 R1).trans_lt h2))
      · exact Or.inr (Or.inr ((le_max_right R0 R1).trans_lt h3))
    have hLoc_ab := hLoc a b ha
    have hg_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
        eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      fun i => (lintegral_mono fun s => (eLpNorm_comp_le_merid c g s i).trans le_self_add).trans_lt hLoc_ab
    have hU_loc : ∀ i : Fin 2, (∫⁻ s in Icc a b,
        eLpNorm (fun z => U (s, z) i) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      fun i => (lintegral_mono fun s => (eLpNorm_comp_le_merid c U s i).trans le_add_self).trans_lt hLoc_ab
    obtain ⟨hg0_int, hg0_cell, hg0_eq⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR (hgi_meas 0) (hgi_per 0)
        (hg_loc 0) (hΨ.smooth 0).smooth.continuous hsupp0
    obtain ⟨hg1_int, hg1_cell, hg1_eq⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR (hgi_meas 1) (hgi_per 1)
        (hg_loc 1) (hΨ.smooth 1).smooth.continuous hsupp1
    obtain ⟨hU0_int, hU0_cell, hU0_eq⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR (hUi_meas 0) (hUi_per 0)
        (hU_loc 0) (hΨ.smooth 0).smooth.continuous hsupp0
    obtain ⟨hU1_int, hU1_cell, hU1_eq⟩ :=
      integrable_and_integral_coord_eq_cell_qPeriodize hc ha hab hR (hUi_meas 1) (hUi_per 1)
        (hU_loc 1) (hΨ.smooth 1).smooth.continuous hsupp1
    obtain ⟨hgs0, hgz0⟩ := fubini_cell_slices hg0_cell
    obtain ⟨hgs1, hgz1⟩ := fubini_cell_slices hg1_cell
    obtain ⟨hUs0, hUz0⟩ := fubini_cell_slices hU0_cell
    obtain ⟨hUs1, hUz1⟩ := fubini_cell_slices hU1_cell
    dsimp only at hgs0 hgs1 hUs0 hUs1 hgz0 hgz1 hUz0 hUz1
    have hcdot_g : cdot g Ψ = fun x => g x 0 * (Ψ x 0 : ℂ) + g x 1 * (Ψ x 1 : ℂ) := by
      funext x; unfold cdot; rw [Fin.sum_univ_two]
    have hcdot_U : cdot U Ψ = fun x => U x 0 * (Ψ x 0 : ℂ) + U x 1 * (Ψ x 1 : ℂ) := by
      funext x; unfold cdot; rw [Fin.sum_univ_two]
    refine ⟨hcdot_g ▸ (hg0_int.add hg1_int), hcdot_U ▸ (hU0_int.add hU1_int), ?_⟩
    have hgs : Integrable (fun s =>
        (∫ z in B0579.cell c, g (s, z) 0 * (qPeriodize c (fun x => Ψ x 0) s z : ℂ)) +
        (∫ z in B0579.cell c, g (s, z) 1 * (qPeriodize c (fun x => Ψ x 1) s z : ℂ)))
        (volume.restrict (Icc a b)) := hgs0.add hgs1
    have hUs : Integrable (fun s =>
        (∫ z in B0579.cell c, U (s, z) 0 * (qPeriodize c (fun x => Ψ x 0) s z : ℂ)) +
        (∫ z in B0579.cell c, U (s, z) 1 * (qPeriodize c (fun x => Ψ x 1) s z : ℂ)))
        (volume.restrict (Icc a b)) := hUs0.add hUs1
    rw [hcdot_g, hcdot_U, integral_add hg0_int hg1_int, integral_add hU0_int hU1_int,
      hg0_eq, hg1_eq, hU0_eq, hU1_eq, ← sub_eq_zero, sub_neg_eq_add,
      ← integral_add hgs0 hgs1, ← integral_add hUs0 hUs1,
      ← integral_add hgs hUs]
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
    filter_upwards [ae_restrict_of_ae hOrth, hgz0, hgz1, hUz0, hUz1,
      ae_restrict_mem measurableSet_Icc] with s hs ig0 ig1 iU0 iU1 hs_ab
    have hs_pos : 0 < s := lt_of_lt_of_le ha hs_ab.1
    have horth_s := hs hs_pos (qPeriodizeVec c Ψ s) (isDivFreeTestField_qPeriodizeVec hc hΨ s)
    have ig : Integrable (fun z =>
        g (s, z) 0 * (qPeriodize c (fun x => Ψ x 0) s z : ℂ) +
        g (s, z) 1 * (qPeriodize c (fun x => Ψ x 1) s z : ℂ))
        (volume.restrict (B0579.cell c)) := ig0.add ig1
    have iU : Integrable (fun z =>
        U (s, z) 0 * (qPeriodize c (fun x => Ψ x 0) s z : ℂ) +
        U (s, z) 1 * (qPeriodize c (fun x => Ψ x 1) s z : ℂ))
        (volume.restrict (B0579.cell c)) := iU0.add iU1
    rw [← integral_add ig0 ig1, ← integral_add iU0 iU1,
      ← integral_add ig iU]
    refine (integral_congr_ae ?_).trans horth_s
    refine Eventually.of_forall fun z => ?_
    dsimp [qPeriodizeVec, U]
    rw [Fin.sum_univ_two]
    ring

end UnforcedLeray.Short.IIb.TailPeriodizeAux

end

