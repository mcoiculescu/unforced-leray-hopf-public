import UnforcedLeray.Short.PartI.Sub.T02_1_4_6

/-!
# Part I, task `PartI:T02/1/4/6/1`: differentiation under the cell integral

Source of record: `the November 2 reference manuscript`, lines 261-288.
Target: `TimeDerivUnderIntegral` (`Short/PartI/Sub/T02_1_4_6.lean`).

For a jointly smooth `w` on `[0,T] × ℝ²` and a continuous `φ` vanishing for `|η|` large, the map
`t ↦ ∫_cell ⟨w t, φ⟩` has derivative `∫_cell ⟨∂ₜ w s, φ⟩` at every `s ∈ (0,T)`.

Proof: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the cell.  The time derivative is
`fderiv` of the joint map applied to `(1,0)`; it is continuous on the open set `(0,T) × ℝ²` and
hence bounded on the compact `[s-δ,s+δ] × [-c/2,c/2] × [-R,R]`.  The dominating function is
`C ‖φ‖`, integrable because `φ` is continuous and vanishes for `|η| > R`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

theorem timeDerivUnderIntegral : TimeDerivUnderIntegral := by
  unfold TimeDerivUnderIntegral
  intro c T _hc w hw s hs φ hφc hφR
  obtain ⟨R, hR⟩ := hφR
  -- the joint map and the open set where it is smooth
  set G : ℝ × Plane → Vec := fun x => w x.1 x.2 with hGdef
  set U : Set (ℝ × Plane) := Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hUsub : U ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    prod_mono Ioo_subset_Icc_self (subset_refl _)
  have hGU : ContDiffOn ℝ ∞ G U := hw.mono hUsub
  have hmemU : ∀ x ∈ Ioo (0 : ℝ) T, ∀ a : Plane, (x, a) ∈ U :=
    fun x hx a => ⟨hx, mem_univ a⟩
  have hGd : ∀ x ∈ Ioo (0 : ℝ) T, ∀ a : Plane, DifferentiableAt ℝ G (x, a) :=
    fun x hx a => (hGU.contDiffAt (hUopen.mem_nhds (hmemU x hx a))).differentiableAt (by simp)
  -- time derivative as the derivative of the joint map in the direction (1,0)
  have hderiv_of : ∀ x ∈ Ioo (0 : ℝ) T, ∀ a : Plane,
      HasDerivAt (fun t : ℝ => w t a) (fderiv ℝ G (x, a) (1, 0)) x := by
    intro x hx a
    have h1 : HasFDerivAt G (fderiv ℝ G (x, a)) (x, a) := (hGd x hx a).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => ((t, a) : ℝ × Plane)) ((1 : ℝ), (0 : Plane)) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x a)
    exact h1.comp_hasDerivAt x h2
  have hderiv_eq : ∀ x ∈ Ioo (0 : ℝ) T, ∀ a : Plane,
      deriv (fun t : ℝ => w t a) x = fderiv ℝ G (x, a) (1, 0) :=
    fun x hx a => (hderiv_of x hx a).deriv
  -- continuity of the joint derivative
  have hDcont : ContinuousOn (fderiv ℝ G) U :=
    hGU.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hcontD : Continuous (fun a : Plane => fderiv ℝ G (s, a) (1, 0)) := by
    have h1 : ContinuousOn (fun a : Plane => fderiv ℝ G (s, a)) univ :=
      hDcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun a _ => hmemU s hs a)
    have h2 : ContinuousOn (fun a : Plane => fderiv ℝ G (s, a) (1, 0)) univ :=
      h1.clm_apply continuousOn_const
    exact continuousOn_univ.1 h2
  -- continuity of `w x` for `x` in `(0,T)`
  have hwc : ∀ x ∈ Ioo (0 : ℝ) T, Continuous (fun a : Plane => w x a) := by
    intro x hx
    have h2 : ContinuousOn (fun a : Plane => (x, a)) univ :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h3 : ContinuousOn (fun a : Plane => w x a) univ :=
      hGU.continuousOn.comp h2 (fun a _ => hmemU x hx a)
    exact continuousOn_univ.1 h3
  -- a neighbourhood `[s-δ, s+δ]` of `s` inside `(0,T)`
  have hmpos : 0 < min s (T - s) := lt_min hs.1 (by linarith [hs.2])
  obtain ⟨δ, hδpos, hδs, hδT⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < s ∧ s + δ < T :=
    ⟨min s (T - s) / 2, half_pos hmpos, by linarith [min_le_left s (T - s), hs.1],
      by linarith [min_le_right s (T - s)]⟩
  have hIsub : Icc (s - δ) (s + δ) ⊆ Ioo (0 : ℝ) T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hI_nhds : Icc (s - δ) (s + δ) ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
  -- compact box carrying the uniform bound
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R : Set Plane) :=
    isCompact_Icc.prod isCompact_Icc
  have hZ : IsCompact (Icc (s - δ) (s + δ) ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) : Set (ℝ × Plane)) :=
    isCompact_Icc.prod hK
  have hZU : (Icc (s - δ) (s + δ) ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) : Set (ℝ × Plane)) ⊆ U :=
    fun x hx => ⟨hIsub hx.1, mem_univ _⟩
  have hHcont : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ G x (1, 0))
      (Icc (s - δ) (s + δ) ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) : Set (ℝ × Plane)) :=
    (hDcont.mono hZU).clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := hZ.exists_bound_of_continuousOn hHcont
  -- the cell and integrability of continuous functions vanishing for `|η| > R`
  have hcellm : MeasurableSet (Cyl.cell c) := Cyl.measurableSet_cell c
  have hvan : ∀ f : Plane → ℝ, Continuous f → (∀ z : Plane, R < |z.2| → f z = 0) →
      Integrable f (volume.restrict (Cyl.cell c)) :=
    fun f hf h0 => Cyl.VanishesOutside.integrableOn_cell h0 hf c
  have hF_int : Integrable (fun a : Plane => inner ℝ (w s a) (φ a)) (volume.restrict (Cyl.cell c)) :=
    hvan _ ((hwc s hs).inner hφc) (fun z hz => by simp [hR z hz])
  have hbound_int : Integrable (fun a : Plane => C * ‖φ a‖) (volume.restrict (Cyl.cell c)) :=
    hvan _ (continuous_const.mul hφc.norm) (fun z hz => by simp [hR z hz])
  have hF'_cont : Continuous (fun a : Plane => inner ℝ (deriv (fun t : ℝ => w t a) s) (φ a)) := by
    have hfun : (fun a : Plane => inner ℝ (deriv (fun t : ℝ => w t a) s) (φ a)) =
        fun a : Plane => inner ℝ (fderiv ℝ G (s, a) (1, 0)) (φ a) :=
      funext fun a => by rw [hderiv_eq s hs a]
    rw [hfun]
    exact hcontD.inner hφc
  have hF_meas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (fun a : Plane => inner ℝ (w x a) (φ a)) (volume.restrict (Cyl.cell c)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    exact ((hwc x hx).inner hφc).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun a : Plane => inner ℝ (deriv (fun t : ℝ => w t a) s) (φ a)) (volume.restrict (Cyl.cell c)) :=
    hF'_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂(volume.restrict (Cyl.cell c)), ∀ x ∈ Icc (s - δ) (s + δ),
      ‖inner ℝ (deriv (fun t : ℝ => w t a) x) (φ a)‖ ≤ C * ‖φ a‖ := by
    rw [ae_restrict_iff' hcellm]
    refine ae_of_all _ (fun a ha x hx => ?_)
    have hxI : x ∈ Ioo (0 : ℝ) T := hIsub hx
    rw [hderiv_eq x hxI a]
    by_cases hRa : R < |a.2|
    · simp [hR a hRa]
    · have hab : |a.2| ≤ R := not_lt.1 hRa
      have ha2 : a.2 ∈ Icc (-R) R := abs_le.1 hab
      have ha1 : a.1 ∈ Icc (-c / 2) (c / 2) := Ico_subset_Icc_self ha.1
      have hmem : (x, a) ∈ (Icc (s - δ) (s + δ) ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) : Set (ℝ × Plane)) :=
        ⟨hx, ha1, ha2⟩
      have hCb : ‖fderiv ℝ G (x, a) (1, 0)‖ ≤ C := hC (x, a) hmem
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hCb (norm_nonneg _))
  have h_diff : ∀ᵐ a ∂(volume.restrict (Cyl.cell c)), ∀ x ∈ Icc (s - δ) (s + δ),
      HasDerivAt (fun t : ℝ => inner ℝ (w t a) (φ a))
        (inner ℝ (deriv (fun t : ℝ => w t a) x) (φ a)) x := by
    refine ae_of_all _ (fun a x hx => ?_)
    have hxI : x ∈ Ioo (0 : ℝ) T := hIsub hx
    rw [hderiv_eq x hxI a]
    have h1 := HasDerivAt.inner ℝ (hderiv_of x hxI a) (hasDerivAt_const x (φ a))
    rw [inner_zero_right, zero_add] at h1
    exact h1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Cyl.cell c))
    (F := fun t a => inner ℝ (w t a) (φ a))
    (F' := fun x a => inner ℝ (deriv (fun t : ℝ => w t a) x) (φ a))
    (x₀ := s) (s := Icc (s - δ) (s + δ)) (bound := fun a => C * ‖φ a‖)
    hI_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact key.2

end UnforcedLeray.Short.PartI
