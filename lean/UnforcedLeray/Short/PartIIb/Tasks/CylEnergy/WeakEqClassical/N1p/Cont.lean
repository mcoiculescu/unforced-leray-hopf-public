import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common

/-!
# Part II-b, task `PartII-b:T22/2/2/5`: continuity of the pairing (`rtdCont`)

Source of record: `the November 2 reference manuscript`, lines 2074-2105.
The map `r ↦ ∫_cell ω(r) φ(r)` is continuous on `[s, t₁]` by dominated convergence on the cell
with the measure `volume.restrict (cell c)`: the integrand is jointly continuous in `(r, x)` on
`[s, t₁] × cell`, and it is dominated by `|C₁| |C₂| jb^{-4}` (the decay of `ω` with exponent `4`
on the strip `|q| ≤ c/2`, the decay of `φ` with exponent `0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem rtdCont : UnforcedLeray.Short.IIb.RtdCont := by
  intro ν c tr s T t₁ ω φ hc hst htT hω hφ
  obtain ⟨C1, hC1⟩ := hω.cell_decay 4
  obtain ⟨C2, hC2⟩ := hφ.decay 0
  have hsub : Icc s t₁ ⊆ Icc s T := fun r hr => ⟨hr.1, hr.2.trans htT⟩
  -- pointwise bound on ω, on the strip |q| ≤ c/2
  have hωb : ∀ r ∈ Icc s t₁, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |ω r x| ≤ |C1| * B0579.jb x ^ (-4 : ℝ) := by
    intro r hr x hx
    have h := hC1 r (hsub hr) x hx
    have hpos : 0 < B0579.jb x ^ (4 : ℝ) := Real.rpow_pos_of_pos (B0579.jb_pos x) _
    have hneg : B0579.jb x ^ (-4 : ℝ) = (B0579.jb x ^ (4 : ℝ))⁻¹ :=
      Real.rpow_neg (B0579.jb_pos x).le 4
    have h0 : |ω r x| ≤ |ω r x| + |B0579.pd 0 (ω r) x| + |B0579.pd 1 (ω r) x|
        + |lapP (ω r) x| := by
      linarith [abs_nonneg (B0579.pd 0 (ω r) x), abs_nonneg (B0579.pd 1 (ω r) x),
        abs_nonneg (lapP (ω r) x)]
    have h1 : |ω r x| * B0579.jb x ^ (4 : ℝ) ≤ C1 :=
      le_trans (mul_le_mul_of_nonneg_right h0 hpos.le) h
    rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith [le_abs_self C1]
  -- pointwise bound on φ
  have hφb : ∀ r ∈ Icc s t₁, ∀ x : B0579.Plane, |φ r x| ≤ |C2| := by
    intro r hr x
    have h := hC2 r hr x
    rw [Real.rpow_zero, mul_one] at h
    linarith [le_abs_self C2, abs_nonneg (B0579.pd 0 (φ r) x), abs_nonneg (B0579.pd 1 (φ r) x),
      abs_nonneg (lapP (φ r) x)]
  -- continuity of the slices in the plane variable
  have hωc : ∀ r ∈ Icc s T, Continuous (ω r) := fun r hr => (hω.slice r hr).smooth.continuous
  have hφc : ∀ r ∈ Icc s t₁, Continuous (φ r) := by
    intro r hr
    have hmap : MapsTo (fun y : B0579.Plane => (r, y)) univ (Icc s t₁ ×ˢ univ) :=
      fun y _ => ⟨hr, mem_univ _⟩
    have h2 : Continuous (fun y : B0579.Plane => (r, y)) := continuous_const.prodMk continuous_id
    have hc' : ContinuousOn (fun y : B0579.Plane => φ r y) univ :=
      hφ.smooth.continuousOn.comp h2.continuousOn hmap
    exact continuousOn_univ.1 hc'
  -- continuity in the age, for fixed x
  have hωr : ∀ a : B0579.Plane, ContinuousOn (fun r => ω r a) (Icc s t₁) := by
    intro a
    have hmap : MapsTo (fun r : ℝ => (r, a)) (Icc s t₁) (Icc s T ×ˢ univ) :=
      fun r hr => ⟨⟨hr.1, hr.2.trans htT⟩, mem_univ _⟩
    have h2 : Continuous (fun r : ℝ => (r, a)) := continuous_id.prodMk continuous_const
    exact hω.jointCont.comp h2.continuousOn hmap
  have hφr : ∀ a : B0579.Plane, ContinuousOn (fun r => φ r a) (Icc s t₁) := by
    intro a
    have hmap : MapsTo (fun r : ℝ => (r, a)) (Icc s t₁) (Icc s t₁ ×ˢ univ) :=
      fun r hr => ⟨hr, mem_univ _⟩
    have h2 : Continuous (fun r : ℝ => (r, a)) := continuous_id.prodMk continuous_const
    exact hφ.smooth.continuousOn.comp h2.continuousOn hmap
  refine continuousOn_of_dominated
    (bound := fun x => (|C1| * |C2|) * B0579.jb x ^ (-4 : ℝ)) ?_ ?_ ?_ ?_
  · intro r hr
    exact ((hωc r (hsub hr)).mul (hφc r hr)).aestronglyMeasurable
  · intro r hr
    refine ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun x hx => ?_
    show ‖ω r x * φ r x‖ ≤ (|C1| * |C2|) * B0579.jb x ^ (-4 : ℝ)
    have hx' := abs_fst_le_of_mem_cell hx
    rw [Real.norm_eq_abs, abs_mul]
    have hJ : 0 ≤ B0579.jb x ^ (-4 : ℝ) := Real.rpow_nonneg (B0579.jb_pos x).le _
    have h := mul_le_mul (hωb r hr x hx') (hφb r hr x) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) hJ)
    calc |ω r x| * |φ r x| ≤ (|C1| * B0579.jb x ^ (-4 : ℝ)) * |C2| := h
      _ = (|C1| * |C2|) * B0579.jb x ^ (-4 : ℝ) := by ring
  · exact (DbCommon.integrable_jb_neg4.const_mul (|C1| * |C2|)).integrableOn
  · exact ae_of_all _ fun a => (hωr a).mul (hφr a)

end UnforcedLeray.Short.IIb
