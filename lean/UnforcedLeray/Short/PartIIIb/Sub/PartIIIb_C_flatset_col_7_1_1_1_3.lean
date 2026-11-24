import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_1_of
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# `SFDPeriodize` (decomposition of `PartIII-b:C/flatset/col/7/1/1/1/3`)

Source of record `the November 2 reference manuscript` 1684-1689.
A smooth `F` supported in a compact box inside the open `q`-cell is periodized,
`W(s,q,η) = ∑_k F(s, q + k c, η)` (locally a finite sum, so smooth), and packaged as an element of
`Hsp c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The `q`-periodization of the `i`-th component of `F`: `∑_k F(s, q + k c, η)_i`. -/
def perCoord (c : ℝ) (F : Chart → Fin 2 → ℝ) (p : Chart) (i : Fin 2) : ℝ :=
  ∑' k : ℤ, F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) i

theorem perCoord_far {c a b s0 s1 L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (p : Chart) (R : ℝ) (hp : |p.2.1| < R) (N : ℕ)
    (hN : |a| + |b| + R ≤ (N : ℝ) * c) (k : ℤ) (hk : k ∉ Finset.Icc (-(N : ℤ)) N) :
    F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) = 0 := by
  by_contra hne
  have hm : p.2.1 + (k : ℝ) * c ∈ Icc a b := (hsupp _ hne).2.1
  obtain ⟨hm1, hm2⟩ := hm
  have hkN : (N : ℤ) < k ∨ k < -(N : ℤ) := by
    rw [Finset.mem_Icc] at hk
    omega
  have hcase : (N : ℝ) * c < (k : ℝ) * c ∨ (k : ℝ) * c < -((N : ℝ) * c) := by
    rcases hkN with h | h
    · left
      have h' : (N : ℝ) < k := by exact_mod_cast h
      exact mul_lt_mul_of_pos_right h' hc
    · right
      have h' : (k : ℝ) < -(N : ℝ) := by exact_mod_cast h
      have := mul_lt_mul_of_pos_right h' hc
      linarith
  have hp' := abs_lt.1 hp
  rcases hcase with h | h
  · linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b]
  · linarith [abs_nonneg a, abs_nonneg b, neg_abs_le a, le_abs_self b]

theorem perCoord_eventually_sum {c a b s0 s1 L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (x0 : Chart) (i : Fin 2) :
    ∃ N : ℕ, ∀ᶠ p in 𝓝 x0, perCoord c F p i =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) i := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |a| + |b| + (|x0.2.1| + 1) ≤ (N : ℝ) * c := by
    refine ⟨⌈(|a| + |b| + (|x0.2.1| + 1)) / c⌉₊, ?_⟩
    have := Nat.le_ceil ((|a| + |b| + (|x0.2.1| + 1)) / c)
    rwa [div_le_iff₀ hc] at this
  refine ⟨N, ?_⟩
  have hev : ∀ᶠ p in 𝓝 x0, |p.2.1| < |x0.2.1| + 1 := by
    have hcont : Continuous fun p : Chart => |p.2.1| := by fun_prop
    exact hcont.continuousAt.eventually_lt continuousAt_const (by
      show |x0.2.1| < |x0.2.1| + 1
      linarith)
  filter_upwards [hev] with p hp
  unfold perCoord
  apply tsum_eq_sum
  intro k hk
  simp [perCoord_far hsupp hc p _ hp N hN k hk]

theorem perCoord_contDiff {c a b s0 s1 L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ fun p => F p i)
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (i : Fin 2) : ContDiff ℝ ∞ fun p => perCoord c F p i := by
  rw [contDiff_iff_contDiffAt]
  intro x0
  obtain ⟨N, hN⟩ := perCoord_eventually_sum hsupp hc x0 i
  have hsum : ContDiff ℝ ∞ fun p : Chart =>
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) i := by
    apply ContDiff.sum
    intro k _
    have hφ : ContDiff ℝ ∞ fun p : Chart => ((p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) : Chart) := by
      fun_prop
    exact (hF i).comp hφ
  exact hsum.contDiffAt.congr_of_eventuallyEq hN

theorem perCoord_shift (c : ℝ) (F : Chart → Fin 2 → ℝ) (p : Chart) (i : Fin 2) :
    perCoord c F (p.1, (p.2.1 + c, p.2.2)) i = perCoord c F p i := by
  unfold perCoord
  have h2 := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k : ℤ => F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) i)
  simp only [Equiv.coe_addRight] at h2
  rw [← h2]
  refine tsum_congr fun k => ?_
  dsimp only
  congr 3
  push_cast
  ring

theorem perCoord_supp {c s0 s1 a b L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (p : Chart) (hp : ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)) (i : Fin 2) :
    perCoord c F p i = 0 := by
  have hz : ∀ k : ℤ, F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) = 0 := by
    intro k
    by_contra hne
    have h := hsupp _ hne
    exact hp ⟨h.1, h.2.2⟩
  simp [perCoord, hz]

theorem perCoord_cell {c s0 s1 a b L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (hcell : -(c / 2) < a) (hcell' : b < c / 2)
    (s q η : ℝ) (hq : q ∈ Ico (-(c / 2)) (c / 2)) (i : Fin 2) :
    perCoord c F (s, (q, η)) i = F (s, (q, η)) i := by
  unfold perCoord
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    by_contra hne
    have hm := (hsupp _ (fun h => hne (congrFun h i))).2.1
    obtain ⟨hm1, hm2⟩ := hm
    have hk1 : (1 : ℝ) ≤ k ∨ (k : ℝ) ≤ -1 := by
      rcases lt_trichotomy k 0 with h | h | h
      · right
        have : k ≤ -1 := by omega
        exact_mod_cast this
      · exact absurd h hk
      · left
        have : 1 ≤ k := by omega
        exact_mod_cast this
    rcases hk1 with h | h
    · nlinarith [hq.1, hq.2]
    · nlinarith [hq.1, hq.2]

theorem perCoord_unique {c a b s0 s1 L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (hcell : -(c / 2) < a) (hcell' : b < c / 2) (p : Chart) (i : Fin 2)
    (k k' : ℤ) (hk : F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) ≠ 0)
    (hk' : F (p.1, (p.2.1 + (k' : ℝ) * c, p.2.2)) ≠ 0) : k = k' := by
  have m1 := (hsupp _ hk).2.1
  have m2 := (hsupp _ hk').2.1
  obtain ⟨m1a, m1b⟩ := m1
  obtain ⟨m2a, m2b⟩ := m2
  have e1 : ((k : ℝ) - k') * c < 1 * c := by
    rw [sub_mul, one_mul]
    linarith
  have e2 : ((k' : ℝ) - k) * c < 1 * c := by
    rw [sub_mul, one_mul]
    linarith
  have f1 := lt_of_mul_lt_mul_right e1 hc.le
  have f2 := lt_of_mul_lt_mul_right e2 hc.le
  have g1 : k - k' < 1 := by exact_mod_cast f1
  have g2 : k' - k < 1 := by exact_mod_cast f2
  omega

theorem perCoord_bound {c s0 s1 a b L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ fun p => F p i)
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (hcell : -(c / 2) < a) (hcell' : b < c / 2) :
    ∃ C : ℝ, ∀ p i, |perCoord c F p i| ≤ C := by
  have hFc : Continuous F := continuous_pi fun i => (hF i).continuous
  obtain ⟨C0, hC0⟩ := (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc (a := -L) (b := L))) :
    IsCompact (Icc s0 s1 ×ˢ (Icc a b ×ˢ Icc (-L) L))).exists_bound_of_continuousOn hFc.continuousOn
  have hFb : ∀ x, ‖F x‖ ≤ max C0 0 := by
    intro x
    by_cases hx : F x = 0
    · simp [hx]
    · have hxK := hsupp x hx
      exact (hC0 x ⟨hxK.1, hxK.2.1, abs_le.1 hxK.2.2⟩).trans (le_max_left _ _)
  refine ⟨max C0 0, fun p i => ?_⟩
  by_cases hex : ∃ k : ℤ, F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) ≠ 0
  · obtain ⟨k0, hk0⟩ := hex
    unfold perCoord
    rw [tsum_eq_single k0]
    · calc |F (p.1, (p.2.1 + (k0 : ℝ) * c, p.2.2)) i|
          = ‖F (p.1, (p.2.1 + (k0 : ℝ) * c, p.2.2)) i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖F (p.1, (p.2.1 + (k0 : ℝ) * c, p.2.2))‖ := norm_le_pi_norm _ i
        _ ≤ max C0 0 := hFb _
    · intro k hk
      by_contra hne
      have hk1 : F (p.1, (p.2.1 + (k : ℝ) * c, p.2.2)) ≠ 0 := fun h => hne (by simp [h])
      exact hk (perCoord_unique hsupp hc hcell hcell' p i k k0 hk1 hk0)
  · push_neg at hex
    have h0 : perCoord c F p i = 0 := by
      unfold perCoord
      simp [hex]
    rw [h0, abs_zero]
    exact le_max_right _ _

theorem perCoord_cell_eq {c s0 s1 a b L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (hcell : -(c / 2) < a) (hcell' : b < c / 2) (p : Chart) (i : Fin 2)
    (hq : p.2.1 ∈ Ico (-(c / 2)) (c / 2)) :
    perCoord c F p i = F p i := by
  rcases p with ⟨s, q, η⟩
  exact perCoord_cell hsupp hc hcell hcell' s q η hq i

theorem perCoord_memLp {c s0 s1 a b L : ℝ} {F : Chart → Fin 2 → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ fun p => F p i)
    (hsupp : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L)
    (hc : 0 < c) (hcell : -(c / 2) < a) (hcell' : b < c / 2) (hs0 : 0 < s0) :
    MemLp (fun p : Chart => (WithLp.toLp 2 (fun i => perCoord c F p i) :
      EuclideanSpace ℝ (Fin 2))) 2 (ageμ c (-3 / 2)) := by
  set S : Set Chart := Icc s0 s1 ×ˢ (univ ×ˢ Icc (-L) L) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)
  have hind : (fun p : Chart => (WithLp.toLp 2 (fun i => perCoord c F p i) :
      EuclideanSpace ℝ (Fin 2))) = S.indicator (fun p : Chart => (WithLp.toLp 2
        (fun i => perCoord c F p i) : EuclideanSpace ℝ (Fin 2))) := by
    funext p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp]
      have hn : ¬ (p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) := fun h =>
        hp ⟨h.1, trivial, abs_le.1 h.2⟩
      ext i
      simp [perCoord_supp hsupp p hn i]
  have hfin : ageμ c (-3 / 2) S < ⊤ := by
    have h1 : (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun s : ℝ => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))) (Icc s0 s1) < ⊤ := by
      rw [withDensity_apply _ measurableSet_Icc]
      calc ∫⁻ x in Icc s0 s1, ENNReal.ofReal (x ^ (-3 / 2 : ℝ))
            ∂(volume.restrict (Ioi (0 : ℝ)))
          ≤ ∫⁻ x in Icc s0 s1, ENNReal.ofReal (s0 ^ (-3 / 2 : ℝ))
            ∂(volume.restrict (Ioi (0 : ℝ))) := by
            refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
            exact ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow_of_nonpos hs0 hx.1 (by norm_num))
        _ = ENNReal.ofReal (s0 ^ (-3 / 2 : ℝ)) * (volume.restrict (Ioi (0 : ℝ))) (Icc s0 s1) :=
            setLIntegral_const _ _
        _ < ⊤ := by
            refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
            rw [Measure.restrict_apply measurableSet_Icc]
            exact (measure_mono inter_subset_left).trans_lt measure_Icc_lt_top
    have hbox : volume (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L) < ⊤ :=
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (-L) L)).measure_lt_top
    have h2 : UnforcedLeray.Cyl.avgμ c (univ ×ˢ Icc (-L) L) < ⊤ := by
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc)]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine lt_of_le_of_lt (measure_mono ?_) hbox
      rintro x ⟨hx1, hx2⟩
      have hx := Set.mem_prod.1 hx2
      exact ⟨⟨hx.1.1, hx.1.2.le⟩, hx1.2⟩
    haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
      unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
      infer_instance
    unfold ageμ
    rw [hS, Measure.prod_prod]
    exact ENNReal.mul_lt_top h1 h2
  haveI : IsFiniteMeasure ((ageμ c (-3 / 2)).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := perCoord_bound hF hsupp hc hcell hcell'
  rw [hind, memLp_indicator_iff_restrict hSm]
  refine MemLp.of_bound ?_ (2 * C) (Filter.Eventually.of_forall fun p => ?_)
  · have hcont : Continuous fun p : Chart =>
        (WithLp.toLp 2 (fun i => perCoord c F p i) : EuclideanSpace ℝ (Fin 2)) :=
      (PiLp.continuous_toLp 2 fun _ : Fin 2 => ℝ).comp
        (continuous_pi fun i => (perCoord_contDiff hF hsupp hc i).continuous)
    exact hcont.aestronglyMeasurable
  · show ‖(WithLp.toLp 2 (fun i => perCoord c F p i) : EuclideanSpace ℝ (Fin 2))‖ ≤ 2 * C
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_iff.2 ⟨by linarith [abs_nonneg (perCoord c F p 0), hC p 0], ?_⟩
    simp only [Fin.sum_univ_two, PiLp.toLp_apply, Real.norm_eq_abs]
    have h0 := hC p 0
    have h1 := hC p 1
    have a0 := sq_abs (perCoord c F p 0)
    have a1 := sq_abs (perCoord c F p 1)
    nlinarith [abs_nonneg (perCoord c F p 0), abs_nonneg (perCoord c F p 1)]

/-- **P** Periodization and `Lp` packaging (source 1684-1689): a smooth `F` supported in a compact
box inside the open cell is a.e. the representative of a smooth force. -/
theorem sfdPeriodize : SFDPeriodize := by
  intro c hc F hF hsup
  obtain ⟨s0', s1', a', b', L', hs0, ha, hb, hsupp⟩ := hsup
  have hW := perCoord_memLp hF hsupp hc ha hb hs0
  refine ⟨MemLp.toLp _ hW,
    ⟨fun p i => perCoord c F p i, fun i => perCoord_contDiff hF hsupp hc i, ?_,
      ⟨s0', s1', L', hs0, ?_⟩, ?_⟩, ?_⟩
  · intro s q η
    funext i
    exact perCoord_shift c F (s, (q, η)) i
  · intro p hp
    by_contra h
    apply hp
    show (fun i => perCoord c F p i) = 0
    funext i
    exact perCoord_supp hsupp p h i
  · filter_upwards [MemLp.coeFn_toLp hW] with p hp
    intro i
    simp only [NearInst.velC, hp, PiLp.toLp_apply]
  · filter_upwards [MemLp.coeFn_toLp hW, ae_ageμ_mem hc (-3 / 2)] with p hp hpq
    have hq : p.2.1 ∈ Ico (-(c / 2)) (c / 2) := by
      have h1 : p.2 ∈ Cyl.cell c := (Set.mem_prod.1 hpq).2
      have h2 := Set.mem_prod.1 h1
      exact ⟨by linarith [h2.1.1], h2.1.2⟩
    funext i
    simp only [NearInst.velC, hp, PiLp.toLp_apply, perCoord_cell_eq hsupp hc ha hb p i hq]


end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
