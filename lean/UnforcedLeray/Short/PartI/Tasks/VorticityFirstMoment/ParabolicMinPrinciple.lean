import UnforcedLeray.Short.PartI.Sub.T02_4
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Part I, task `PartI:T02/4`: the parabolic minimum principle on the cylinder

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
Phragmen-Lindelof comparison for the scalar vorticity equation with bounded drift).

The target `parabolicMinPrinciple : ParabolicMinPrinciple` is proved by contradiction.  If
`D s0 z0 < 0` with `s0 ∈ [0, T)`, periodicity moves `z0` to `q0 ∈ [-c/2, c/2]`.  On the compact box
`K = [0, T'] × [-c/2, c/2] × [-R, R]` (with `s0 < T' < T`) `D` has a minimiser `(s1, z1)` with
`m = D s1 z1 < 0`.  Then `s1 ∈ (0, T)`; `z1` is a global spatial minimiser of `D s1` (periodicity,
and `D ≥ 0` for `|η| ≥ R`); and `s ↦ D s z1` is minimal on `[0, s1]` at `s1`.  At `(s1, z1)` the
first derivatives in `q` and `η` vanish, the second derivatives are `≥ 0`, and `∂_s D ≤ 0`, so
`vorticityOp ν b D s1 z1 ≤ 0`, contradicting the hypothesis on `(0,T) × ℝ²`.

Helpers are prefixed `pm`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- A `c`-periodic function on the plane can be read with `q` in `[-c/2, c/2]`. -/
theorem pm_reduce {f : Plane → ℝ} {c : ℝ} (hc : 0 < c) (hper : Cyl.IsPeriodic c f) (z : Plane) :
    ∃ q : ℝ, -c / 2 ≤ q ∧ q ≤ c / 2 ∧ f (q, z.2) = f z := by
  have hg : Function.Periodic (fun x : ℝ => f (x, z.2)) c := fun x => hper (x, z.2)
  obtain ⟨n, h1, h2⟩ : ∃ n : ℤ, (n : ℝ) ≤ (z.1 + c / 2) / c ∧ (z.1 + c / 2) / c < (n : ℝ) + 1 :=
    ⟨⌊(z.1 + c / 2) / c⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  refine ⟨z.1 - n * c, by linarith, by linarith, ?_⟩
  have key : (fun x : ℝ => f (x, z.2)) (z.1 - n * c) = (fun x : ℝ => f (x, z.2)) z.1 :=
    hg.sub_int_mul_eq _
  exact key

/-- A function with a global minimum at `q0` has nonnegative second derivative there. -/
theorem pm_second_nonneg {g : ℝ → ℝ} {q0 : ℝ} (hg : ContinuousAt g q0)
    (hmin : ∀ q, g q0 ≤ g q) : 0 ≤ deriv (deriv g) q0 := by
  by_contra hneg
  push_neg at hneg
  have hlmin : IsLocalMin g q0 := Filter.Eventually.of_forall hmin
  have hd : deriv g q0 = 0 := hlmin.deriv_eq_zero
  have hlmax : IsLocalMax g q0 := isLocalMax_of_deriv_deriv_neg hneg hd hg
  have hmin' : ∀ᶠ q in nhds q0, g q0 ≤ g q := hlmin
  have hmax' : ∀ᶠ q in nhds q0, g q ≤ g q0 := hlmax
  have hev : g =ᶠ[nhds q0] fun _ => g q0 := by
    filter_upwards [hmin', hmax'] with q h1 h2
    exact le_antisymm h2 h1
  have h3 : deriv (deriv g) q0 = 0 := by
    rw [hev.deriv.deriv_eq]
    simp [deriv_const']
  linarith

/-- The parabolic minimum principle on the cylinder (target `PartI:T02/4`). -/
theorem parabolicMinPrinciple : ParabolicMinPrinciple := by
  intro ν c T R b D hν hc hT hDc hDs hper hD0 hDR hop s0 hs0 z0
  obtain ⟨hs0a, hs0T⟩ := Set.mem_Ico.mp hs0
  have hs0I : s0 ∈ Icc 0 T := Set.mem_Icc.mpr ⟨hs0a, hs0T.le⟩
  by_contra hcon
  push_neg at hcon
  -- `D s0 z0 < 0` forces `|z0.2| < R`
  have hR : |z0.2| < R := by
    by_contra h
    push_neg at h
    have := hDR s0 hs0I z0 h
    linarith
  obtain ⟨q0, hq0a, hq0b, hDq0⟩ := pm_reduce hc (hper s0 hs0I) z0
  obtain ⟨T', hT'1, hT'2⟩ := exists_between hs0T
  obtain ⟨K, hKdef⟩ : ∃ K : Set (ℝ × Plane),
      K = Icc 0 T' ×ˢ (Icc (-c / 2) (c / 2) ×ˢ Icc (-R) R) := ⟨_, rfl⟩
  have hKiff : ∀ x : ℝ × Plane, x ∈ K ↔
      (0 ≤ x.1 ∧ x.1 ≤ T') ∧ ((-c / 2 ≤ x.2.1 ∧ x.2.1 ≤ c / 2) ∧ (-R ≤ x.2.2 ∧ x.2.2 ≤ R)) := by
    intro x
    rw [hKdef]
    simp only [Set.mem_prod, Set.mem_Icc]
  have hKcpt : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : K ⊆ Icc 0 T ×ˢ (univ : Set Plane) := by
    intro x hx
    obtain ⟨h1, _⟩ := (hKiff x).mp hx
    exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨h1.1, h1.2.trans hT'2.le⟩, Set.mem_univ _⟩
  have hFc : ContinuousOn (fun x : ℝ × Plane => D x.1 x.2) K := hDc.mono hKsub
  have habs := abs_lt.mp hR
  have hpt0 : (s0, (q0, z0.2)) ∈ K :=
    (hKiff _).mpr ⟨⟨hs0a, hT'1.le⟩, ⟨⟨hq0a, hq0b⟩, ⟨habs.1.le, habs.2.le⟩⟩⟩
  obtain ⟨⟨s1, z1⟩, hx1K, hx1min⟩ := hKcpt.exists_isMinOn ⟨(s0, (q0, z0.2)), hpt0⟩ hFc
  have hs1K : 0 ≤ s1 ∧ s1 ≤ T' := ((hKiff (s1, z1)).mp hx1K).1
  have hz1q : -c / 2 ≤ z1.1 ∧ z1.1 ≤ c / 2 := ((hKiff (s1, z1)).mp hx1K).2.1
  have hz1η : -R ≤ z1.2 ∧ z1.2 ≤ R := ((hKiff (s1, z1)).mp hx1K).2.2
  have hmin_K : ∀ x ∈ K, D s1 z1 ≤ D x.1 x.2 := fun x hx => isMinOn_iff.mp hx1min x hx
  have hle0 : D s1 z1 ≤ D s0 (q0, z0.2) := hmin_K (s0, (q0, z0.2)) hpt0
  have hm_neg : D s1 z1 < 0 := by linarith
  -- `s1 ≠ 0` because `D 0 ≥ 0`
  have hs1pos : 0 < s1 := by
    rcases hs1K.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hm_neg
      have := hD0 z1
      linarith
  have hs1Ioo : s1 ∈ Ioo 0 T := Set.mem_Ioo.mpr ⟨hs1pos, lt_of_le_of_lt hs1K.2 hT'2⟩
  have hs1Icc : s1 ∈ Icc 0 T := Set.mem_Icc.mpr ⟨hs1K.1, hs1K.2.trans hT'2.le⟩
  -- `z1` is a global spatial minimiser of `D s1`
  have hglob : ∀ z : Plane, D s1 z1 ≤ D s1 z := by
    intro z
    by_cases hz : |z.2| < R
    · obtain ⟨q, hqa, hqb, hDq⟩ := pm_reduce hc (hper s1 hs1Icc) z
      have habz := abs_lt.mp hz
      have hpt : (s1, (q, z.2)) ∈ K :=
        (hKiff _).mpr ⟨⟨hs1K.1, hs1K.2⟩, ⟨⟨hqa, hqb⟩, ⟨habz.1.le, habz.2.le⟩⟩⟩
      have h1 : D s1 z1 ≤ D s1 (q, z.2) := hmin_K (s1, (q, z.2)) hpt
      linarith
    · push_neg at hz
      have h0 := hDR s1 hs1Icc z hz
      linarith
  -- `s ↦ D s z1` is minimal on `[0, s1]` at `s1`
  have htime : ∀ t ∈ Icc 0 s1, D s1 z1 ≤ D t z1 := by
    intro t ht
    have hpt : (t, z1) ∈ K :=
      (hKiff _).mpr ⟨⟨ht.1, ht.2.trans hs1K.2⟩, ⟨hz1q, hz1η⟩⟩
    exact hmin_K (t, z1) hpt
  -- smoothness at `(s1, z1)`
  have hFs : ContDiffAt ℝ 2 (fun x : ℝ × Plane => D x.1 x.2) (s1, z1) :=
    hDs.contDiffAt (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ)
      (Set.mem_prod.mpr ⟨hs1Ioo, Set.mem_univ _⟩))
  have hpathQ : ContDiffAt ℝ 2 (fun q : ℝ => ((s1, (q, z1.2)) : ℝ × Plane)) z1.1 := by
    fun_prop
  have hgQ : ContDiffAt ℝ 2 (fun q : ℝ => D s1 (q, z1.2)) z1.1 :=
    ContDiffAt.comp (f := fun q : ℝ => ((s1, (q, z1.2)) : ℝ × Plane))
      (g := fun x : ℝ × Plane => D x.1 x.2) z1.1 hFs hpathQ
  have hpathE : ContDiffAt ℝ 2 (fun η : ℝ => ((s1, (z1.1, η)) : ℝ × Plane)) z1.2 := by
    fun_prop
  have hgE : ContDiffAt ℝ 2 (fun η : ℝ => D s1 (z1.1, η)) z1.2 :=
    ContDiffAt.comp (f := fun η : ℝ => ((s1, (z1.1, η)) : ℝ × Plane))
      (g := fun x : ℝ × Plane => D x.1 x.2) z1.2 hFs hpathE
  have hpathT : ContDiffAt ℝ 2 (fun t : ℝ => ((t, z1) : ℝ × Plane)) s1 := by
    fun_prop
  have hgT : ContDiffAt ℝ 2 (fun t : ℝ => D t z1) s1 :=
    ContDiffAt.comp (f := fun t : ℝ => ((t, z1) : ℝ × Plane))
      (g := fun x : ℝ × Plane => D x.1 x.2) s1 hFs hpathT
  have hdiffT : DifferentiableAt ℝ (fun t : ℝ => D t z1) s1 := hgT.differentiableAt (by norm_num)
  -- (i) first derivatives in `q` and `η` vanish
  have hq1 : Cyl.partialQ (D s1) z1 = 0 := by
    have hlm : IsLocalMin (fun q : ℝ => D s1 (q, z1.2)) z1.1 :=
      Filter.Eventually.of_forall (fun q => hglob (q, z1.2))
    exact hlm.deriv_eq_zero
  have hPE : Cyl.partialEta (D s1) z1 = 0 := by
    have hlm : IsLocalMin (fun η : ℝ => D s1 (z1.1, η)) z1.2 :=
      Filter.Eventually.of_forall (fun η => hglob (z1.1, η))
    exact hlm.deriv_eq_zero
  -- (ii) second derivatives in `q` and `η` are nonnegative
  have hPQQ : 0 ≤ Cyl.partialQ (Cyl.partialQ (D s1)) z1 :=
    pm_second_nonneg hgQ.continuousAt (fun q => hglob (q, z1.2))
  have hPEE : 0 ≤ Cyl.partialEta (Cyl.partialEta (D s1)) z1 :=
    pm_second_nonneg hgE.continuousAt (fun η => hglob (z1.1, η))
  -- (iii) the time derivative at `(s1, z1)` is nonpositive
  have hT1 : deriv (fun t : ℝ => D t z1) s1 ≤ 0 := by
    have hseg : segment ℝ s1 (s1 + -s1) = Icc 0 s1 := by
      have h0 : s1 + -s1 = 0 := by ring
      rw [h0, segment_symm, segment_eq_Icc hs1K.1]
    have hcone : -s1 ∈ posTangentConeAt (Icc 0 s1) s1 :=
      mem_posTangentConeAt_of_segment_subset hseg.subset
    have hloc : IsLocalMinOn (fun t : ℝ => D t z1) (Icc 0 s1) s1 :=
      (isMinOn_iff.mpr (fun t ht => htime t ht)).localize
    have hf' : HasFDerivWithinAt (fun t : ℝ => D t z1)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv (fun t : ℝ => D t z1) s1))
        (Icc 0 s1) s1 :=
      (hdiffT.hasDerivAt.hasDerivWithinAt).hasFDerivWithinAt
    have hnn := hloc.hasFDerivWithinAt_nonneg hf' hcone
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul] at hnn
    by_contra hpos
    push_neg at hpos
    nlinarith [mul_pos hs1pos hpos]
  -- the operator at `(s1, z1)` is `≤ 0`, contradicting the hypothesis
  have hvort : vorticityOp ν b D s1 z1 ≤ 0 := by
    unfold vorticityOp
    rw [hq1, hPE]
    have hL : 0 ≤ Train.lapS (D s1) z1 := add_nonneg hPQQ hPEE
    linarith [mul_nonneg hν.le hL]
  have hpos := hop s1 hs1Ioo z1 hm_neg
  linarith

end UnforcedLeray.Short.PartI
