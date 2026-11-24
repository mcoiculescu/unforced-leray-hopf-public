import UnforcedLeray.Lib.CZCore.Dyadic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The Calderón–Zygmund decomposition of a continuous compactly supported function (INF01 T9)


target T9; §4.9 and decision D4 of `scoping/README.md` §3 ("dyadic decomposition on anisotropic
integer-weight boxes for continuous compactly supported functions … no maximal function").
Used for the weak `(1,1)` bound behind blueprint units B0414 (`paper/main.tex` lines
7336–7344) and B0423 (lines 7447–7477).

For `f` continuous with compact support and a height `t > 0`:

* a box `Q` is *heavy* if `t |Q| < ∫_Q |f|`;
* boxes of generation `≤ -n` are light, for `n` large (`exists_light_generation`), because
  `|Q| → ∞` there while `∫ |f| < ∞`;
* a generation `K ≥ 0` is fixed so that `f` oscillates by at most `t` on each box of generation
  `K` (uniform continuity);
* the selected boxes (`czSel`) are the heavy boxes of generation `≤ K` none of whose
  ancestors is heavy. They are finitely many and pairwise disjoint; each satisfies
  `∫_Q |f| ≤ 2^{|a|} t |Q|` (its parent is light); off them `|f| ≤ 2t`, because the
  generation-`K` box of such a point is light and `f` oscillates by at most `t` on it. This is
  the step where continuity replaces Lebesgue differentiation (critic §4.9).

The good part is `f` off the boxes and the average of `f` on each box; the bad parts are
`b_Q = (f - ⨍_Q f) 1_Q`. The structure `CZDecomp` records the properties used by the weak
`(1,1)` argument (T10); `exists_czDecomp` constructs it. Because the number of boxes is finite,
the bad part is a finite sum, so no `L²`-convergence of an infinite series is needed later.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {N : ℕ} (a : Fin N → ℕ+)

/-- **T9 (INF01 §5, Level 1).** A Calderón–Zygmund decomposition of `f` at height `t` on the
anisotropic dyadic boxes of weight `a`, with finitely many boxes. -/
structure CZDecomp (f : (Fin N → ℝ) → ℝ) (t : ℝ) where
  /-- The selected boxes, as (generation, index). -/
  boxes : Finset (ℤ × (Fin N → ℤ))
  /-- The good part. -/
  good : (Fin N → ℝ) → ℝ
  /-- The bad parts, one per box. -/
  bad : ℤ × (Fin N → ℤ) → (Fin N → ℝ) → ℝ
  disjoint : (boxes : Set (ℤ × (Fin N → ℤ))).PairwiseDisjoint fun Q => dyadicBox a Q.1 Q.2
  decomp : ∀ x, f x = good x + ∑ Q ∈ boxes, bad Q x
  abs_good_le : ∀ x, |good x| ≤ 2 ^ homDim a * t
  eLpNorm_good_le : eLpNorm good 1 volume ≤ eLpNorm f 1 volume
  bad_eq_zero : ∀ Q, ∀ x ∉ dyadicBox a Q.1 Q.2, bad Q x = 0
  memLp_bad : ∀ Q, ∀ p : ℝ≥0∞, MemLp (bad Q) p volume
  integral_bad : ∀ Q, ∫ x, bad Q x = 0
  sum_eLpNorm_bad_le : ∑ Q ∈ boxes, eLpNorm (bad Q) 1 volume ≤ 2 * eLpNorm f 1 volume
  measure_le : ENNReal.ofReal t * ∑ Q ∈ boxes, volume (dyadicBox a Q.1 Q.2) ≤ eLpNorm f 1 volume

section Selection

variable (f : (Fin N → ℝ) → ℝ) (t : ℝ)

/-- The mass `∫_Q |f|` of a box, in `ℝ≥0∞`. -/
def boxMass (k : ℤ) (m : Fin N → ℤ) : ℝ≥0∞ := ∫⁻ x in dyadicBox a k m, ‖f x‖ₑ

/-- A box is heavy if `t |Q| < ∫_Q |f|`. -/
def IsHeavy (k : ℤ) (m : Fin N → ℤ) : Prop :=
  ENNReal.ofReal t * volume (dyadicBox a k m) < boxMass a f k m

/-- The selected boxes up to generation `K`: heavy, with no heavy ancestor. -/
def czSel (K : ℤ) : Set (ℤ × (Fin N → ℤ)) :=
  {Q | Q.1 ≤ K ∧ IsHeavy a f t Q.1 Q.2 ∧
    ∀ j < Q.1, ∀ m', (dyadicBox a Q.1 Q.2 ∩ dyadicBox a j m').Nonempty → ¬ IsHeavy a f t j m'}

/-- The average of `f` on a box. -/
def czAvg (k : ℤ) (m : Fin N → ℤ) : ℝ :=
  (volume (dyadicBox a k m)).toReal⁻¹ * ∫ x in dyadicBox a k m, f x

/-- The bad part `(f - ⨍_Q f) 1_Q`. -/
def czBad (Q : ℤ × (Fin N → ℤ)) (x : Fin N → ℝ) : ℝ :=
  (dyadicBox a Q.1 Q.2).indicator (fun y => f y - czAvg a f Q.1 Q.2) x

theorem boxMass_le_lintegral (k : ℤ) (m : Fin N → ℤ) :
    boxMass a f k m ≤ ∫⁻ x, ‖f x‖ₑ := setLIntegral_le_lintegral _ _

theorem czSel_pairwiseDisjoint (K : ℤ) :
    (czSel a f t K).PairwiseDisjoint fun Q => dyadicBox a Q.1 Q.2 := by
  intro Q hQ Q' hQ' hne
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  rcases lt_trichotomy Q.1 Q'.1 with h | h | h
  · exact hQ'.2.2 Q.1 h Q.2 ⟨x, hx', hx⟩ hQ.2.1
  · apply hne
    have h2 : Q.2 = Q'.2 := by
      rw [mem_dyadicBox_iff] at hx hx'
      rw [← hx, ← hx', h]
    exact Prod.ext h h2
  · exact hQ.2.2 Q'.1 h Q'.2 ⟨x, hx, hx'⟩ hQ'.2.1

/-- `‖⨍_Q f‖ |Q| = |∫_Q f|`. -/
theorem enorm_czAvg_mul (k : ℤ) (m : Fin N → ℤ) :
    ‖czAvg a f k m‖ₑ * volume (dyadicBox a k m) = ‖∫ x in dyadicBox a k m, f x‖ₑ := by
  have hv0 := volume_dyadicBox_pos a k m
  have hvt := volume_dyadicBox_ne_top a k m
  have hvr : 0 < (volume (dyadicBox a k m)).toReal := ENNReal.toReal_pos hv0 hvt
  rw [czAvg, enorm_mul, Real.enorm_of_nonneg (inv_nonneg.2 hvr.le), ENNReal.ofReal_inv_of_pos hvr,
    ENNReal.ofReal_toReal hvt, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hv0 hvt, one_mul]

theorem enorm_czAvg_mul_le (k : ℤ) (m : Fin N → ℤ) :
    ‖czAvg a f k m‖ₑ * volume (dyadicBox a k m) ≤ boxMass a f k m := by
  rw [enorm_czAvg_mul]
  exact enorm_integral_le_lintegral_enorm _

theorem czBad_eq_zero (Q : ℤ × (Fin N → ℤ)) {x : Fin N → ℝ} (hx : x ∉ dyadicBox a Q.1 Q.2) :
    czBad a f Q x = 0 :=
  indicator_of_notMem hx _

theorem czBad_of_mem (Q : ℤ × (Fin N → ℤ)) {x : Fin N → ℝ} (hx : x ∈ dyadicBox a Q.1 Q.2) :
    czBad a f Q x = f x - czAvg a f Q.1 Q.2 :=
  indicator_of_mem hx _

theorem eLpNorm_czBad_le (Q : ℤ × (Fin N → ℤ)) :
    eLpNorm (czBad a f Q) 1 volume ≤ 2 * boxMass a f Q.1 Q.2 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp_rw [czBad, enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator (measurableSet_dyadicBox a _ _)]
  calc ∫⁻ x in dyadicBox a Q.1 Q.2, ‖f x - czAvg a f Q.1 Q.2‖ₑ
      ≤ ∫⁻ x in dyadicBox a Q.1 Q.2, (‖f x‖ₑ + ‖czAvg a f Q.1 Q.2‖ₑ) :=
        lintegral_mono fun x => enorm_sub_le
    _ = boxMass a f Q.1 Q.2 + ‖czAvg a f Q.1 Q.2‖ₑ * volume (dyadicBox a Q.1 Q.2) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, boxMass]
    _ ≤ boxMass a f Q.1 Q.2 + boxMass a f Q.1 Q.2 := by
        gcongr; exact enorm_czAvg_mul_le a f _ _
    _ = 2 * boxMass a f Q.1 Q.2 := (two_mul _).symm

variable {f}

theorem stronglyMeasurable_czBad (hf : Continuous f) (Q : ℤ × (Fin N → ℤ)) :
    StronglyMeasurable (czBad a f Q) :=
  ((hf.measurable.sub measurable_const).indicator (measurableSet_dyadicBox a _ _)).stronglyMeasurable

theorem memLp_czBad (hf : Continuous f) (hfc : HasCompactSupport f) (Q : ℤ × (Fin N → ℤ))
    (p : ℝ≥0∞) : MemLp (czBad a f Q) p volume := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  unfold czBad
  rw [memLp_indicator_iff_restrict (measurableSet_dyadicBox a _ _)]
  have : IsFiniteMeasure (volume.restrict (dyadicBox a Q.1 Q.2)) :=
    isFiniteMeasure_restrict.2 (volume_dyadicBox_ne_top a _ _)
  refine MemLp.of_bound (hf.sub continuous_const).aestronglyMeasurable
    (C + |czAvg a f Q.1 Q.2|) (Eventually.of_forall fun x => ?_)
  calc ‖f x - czAvg a f Q.1 Q.2‖ ≤ ‖f x‖ + ‖czAvg a f Q.1 Q.2‖ := norm_sub_le _ _
    _ ≤ C + |czAvg a f Q.1 Q.2| := by rw [Real.norm_eq_abs (czAvg a f _ _)]; linarith [hC x]

theorem integral_czBad (hf : Continuous f) (hfc : HasCompactSupport f) (Q : ℤ × (Fin N → ℤ)) :
    ∫ x, czBad a f Q x = 0 := by
  have hfi : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
  have hvt := volume_dyadicBox_ne_top a Q.1 Q.2
  have hvr : (volume (dyadicBox a Q.1 Q.2)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (volume_dyadicBox_pos a _ _) hvt).ne'
  unfold czBad
  rw [integral_indicator (measurableSet_dyadicBox a _ _),
    integral_sub hfi.integrableOn (integrableOn_const hvt), setIntegral_const, czAvg,
    smul_eq_mul, measureReal_def]
  field_simp
  ring

variable (f)

/-- **Coarse boxes are light.** -/
theorem exists_light_generation [NeZero N] (hfi : ∫⁻ x, ‖f x‖ₑ ≠ ⊤) (ht : 0 < t) :
    ∃ n : ℕ, ∀ k : ℤ, k ≤ -(n : ℤ) → ∀ m, ¬ IsHeavy a f t k m := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∫⁻ x, ‖f x‖ₑ).toReal / t)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun k hk m hheavy => ?_⟩
  have hdl : (2 : ℝ) ^ n ≤ dyLen k := by
    rw [← dyLen_neg_natCast]
    unfold dyLen
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpow : dyLen k ≤ dyLen k ^ homDim a :=
    le_self_pow₀ (le_trans (one_le_pow₀ (by norm_num)) hdl) (by have := one_le_homDim a; omega)
  have hbig : (∫⁻ x, ‖f x‖ₑ).toReal ≤ t * dyLen k ^ homDim a := by
    rw [div_lt_iff₀ ht] at hn
    nlinarith
  have h1 : ∫⁻ x, ‖f x‖ₑ ≤ ENNReal.ofReal t * volume (dyadicBox a k m) := by
    rw [volume_dyadicBox, ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_toReal hfi]
    exact ENNReal.ofReal_le_ofReal hbig
  exact absurd (hheavy.trans_le (boxMass_le_lintegral a f k m)) (not_lt.2 h1)

/-- A heavy box meets the support of `f`. -/
theorem exists_mem_tsupport_of_isHeavy {k : ℤ} {m : Fin N → ℤ} (h : IsHeavy a f t k m) :
    ∃ x ∈ dyadicBox a k m, x ∈ tsupport f := by
  by_contra hc
  push Not at hc
  have h0 : boxMass a f k m = 0 := by
    rw [boxMass, setLIntegral_congr_fun (measurableSet_dyadicBox a k m)
      (g := fun _ => 0) fun x hx => by simp [image_eq_zero_of_notMem_tsupport (hc x hx)]]
    simp
  rw [IsHeavy, h0] at h
  exact not_lt_zero h

theorem czSel_finite [NeZero N] (hfc : HasCompactSupport f) (hfi : ∫⁻ x, ‖f x‖ₑ ≠ ⊤)
    (ht : 0 < t) (K : ℤ) : (czSel a f t K).Finite := by
  obtain ⟨n, hn⟩ := exists_light_generation a f t hfi ht
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ((Set.finite_Icc (-(n : ℤ)) K).biUnion fun k _ =>
    ((finite_dyIdx_image a k hR).image fun m => (k, m))).subset ?_
  rintro ⟨k, m⟩ hQ
  obtain ⟨x, hxQ, hxs⟩ := exists_mem_tsupport_of_isHeavy a f t hQ.2.1
  have hk : -(n : ℤ) ≤ k := by
    by_contra h
    exact hn k (by omega) m hQ.2.1
  refine mem_iUnion₂.2 ⟨k, ⟨hk, hQ.1⟩, ⟨m, ⟨x, hxs, ((mem_dyadicBox_iff a).1 hxQ)⟩, rfl⟩⟩

/-- A selected box has `∫_Q |f| ≤ 2^{|a|} t |Q|` (its parent is light). -/
theorem boxMass_le_of_mem_czSel {K : ℤ} {Q : ℤ × (Fin N → ℤ)} (hQ : Q ∈ czSel a f t K) :
    boxMass a f Q.1 Q.2 ≤ 2 ^ homDim a * (ENNReal.ofReal t * volume (dyadicBox a Q.1 Q.2)) := by
  obtain ⟨k, m⟩ := Q
  set y := fun i => (m i : ℝ) * dyLen k ^ (a i : ℕ)
  have hy : y ∈ dyadicBox a k m := corner_mem_dyadicBox a k m
  have hne : (dyadicBox a k m ∩ dyadicBox a (k - 1) (dyIdx a (k - 1) y)).Nonempty :=
    ⟨y, hy, mem_dyadicBox_self a _ y⟩
  have hsub := dyadicBox_subset_of_le a (by omega : k - 1 ≤ k) hne
  have hlight := hQ.2.2 (k - 1) (by omega) _ hne
  simp only [IsHeavy, not_lt] at hlight
  calc boxMass a f k m ≤ boxMass a f (k - 1) (dyIdx a (k - 1) y) := lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal t * volume (dyadicBox a (k - 1) (dyIdx a (k - 1) y)) := hlight
    _ = 2 ^ homDim a * (ENNReal.ofReal t * volume (dyadicBox a k m)) := by
        rw [volume_dyadicBox_pred a k m]; ring

/-- **Off the selected boxes, `|f| ≤ 2t`.** -/
theorem abs_le_of_forall_notMem_czSel {n : ℕ} (hn : ∀ k : ℤ, k ≤ -(n : ℤ) → ∀ m, ¬ IsHeavy a f t k m)
    {K : ℤ} (hosc : ∀ x y, dyIdx a K x = dyIdx a K y → |f x - f y| ≤ t) (ht : 0 < t)
    {x : Fin N → ℝ} (hx : ∀ Q ∈ czSel a f t K, x ∉ dyadicBox a Q.1 Q.2) : |f x| ≤ 2 * t := by
  have hlightK : ¬ IsHeavy a f t K (dyIdx a K x) := by
    intro hheavy
    classical
    obtain ⟨j, ⟨hjK, hj⟩, hmin⟩ := Int.exists_least_of_bdd
      (P := fun j => j ≤ K ∧ IsHeavy a f t j (dyIdx a j x))
      ⟨-(n : ℤ), fun z hz => by
        by_contra h
        exact hn z (by omega) _ hz.2⟩ ⟨K, le_rfl, hheavy⟩
    refine hx (j, dyIdx a j x) ⟨hjK, hj, ?_⟩ (mem_dyadicBox_self a j x)
    intro i hi m' hne hheavy'
    have hsub := dyadicBox_subset_of_le a hi.le hne
    have hxm : dyIdx a i x = m' := (mem_dyadicBox_iff a).1 (hsub (mem_dyadicBox_self a j x))
    have := hmin i ⟨by omega, hxm ▸ hheavy'⟩
    omega
  simp only [IsHeavy, not_lt] at hlightK
  set Q := dyadicBox a K (dyIdx a K x) with hQdef
  have hbound : ∀ y ∈ Q, ‖f x‖ₑ ≤ ‖f y‖ₑ + ENNReal.ofReal t := by
    intro y hy
    have hxy := hosc x y ((mem_dyadicBox_iff a).1 hy).symm
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_add (abs_nonneg _) ht.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := abs_sub_abs_le_abs_sub (f x) (f y)
    linarith
  have h1 : ‖f x‖ₑ * volume Q ≤ (2 * ENNReal.ofReal t) * volume Q := by
    calc ‖f x‖ₑ * volume Q = ∫⁻ _ in Q, ‖f x‖ₑ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in Q, (‖f y‖ₑ + ENNReal.ofReal t) :=
          setLIntegral_mono' (measurableSet_dyadicBox a _ _) hbound
      _ = boxMass a f K (dyIdx a K x) + ENNReal.ofReal t * volume Q := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, boxMass, mul_comm]
      _ ≤ ENNReal.ofReal t * volume Q + ENNReal.ofReal t * volume Q := by gcongr
      _ = (2 * ENNReal.ofReal t) * volume Q := by ring
  have h2 := (ENNReal.mul_le_mul_iff_left (volume_dyadicBox_pos a _ _)
    (volume_dyadicBox_ne_top a _ _)).1 h1
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end Selection

section Exists

variable {f : (Fin N → ℝ) → ℝ}

theorem sum_czBad_of_mem {S : Finset (ℤ × (Fin N → ℤ))}
    (hS : (S : Set (ℤ × (Fin N → ℤ))).PairwiseDisjoint fun Q => dyadicBox a Q.1 Q.2)
    {Q : ℤ × (Fin N → ℤ)} (hQ : Q ∈ S) {x : Fin N → ℝ} (hx : x ∈ dyadicBox a Q.1 Q.2) :
    ∑ Q' ∈ S, czBad a f Q' x = f x - czAvg a f Q.1 Q.2 := by
  rw [Finset.sum_eq_single_of_mem Q hQ fun Q' hQ' hne => czBad_eq_zero a f Q' fun hx' =>
    Set.disjoint_left.1 (hS hQ' hQ hne) hx' hx]
  exact czBad_of_mem a f Q hx

theorem sum_czBad_of_notMem {S : Finset (ℤ × (Fin N → ℤ))} {x : Fin N → ℝ}
    (hx : ∀ Q ∈ S, x ∉ dyadicBox a Q.1 Q.2) : ∑ Q' ∈ S, czBad a f Q' x = 0 :=
  Finset.sum_eq_zero fun Q hQ => czBad_eq_zero a f Q (hx Q hQ)

/-- **T9 (INF01 §5, Level 1): existence of the Calderón–Zygmund decomposition** for a continuous
compactly supported `f` at height `t > 0`, on the dyadic boxes of weight `a` (`N ≥ 1`). -/
theorem exists_czDecomp [NeZero N] (hf : Continuous f) (hfc : HasCompactSupport f) {t : ℝ}
    (ht : 0 < t) : Nonempty (CZDecomp a f t) := by
  have hfint : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
  have hfi : ∫⁻ x, ‖f x‖ₑ ≠ ⊤ := hfint.hasFiniteIntegral.ne
  obtain ⟨n, hn⟩ := exists_light_generation a f t hfi ht
  -- the finest generation `K`
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf) t ht
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  have hosc : ∀ x y, dyIdx a (K : ℤ) x = dyIdx a K y → |f x - f y| ≤ t := by
    intro x y hxy
    have hd := dist_le_of_dyIdx_eq a (Nat.cast_nonneg K) hxy
    have hKeq : dyLen (K : ℤ) = (1 / 2 : ℝ) ^ K := by
      rw [dyLen, zpow_neg, zpow_natCast, one_div, inv_pow]
    have h := hδf (hd.trans_lt (hKeq ▸ hK))
    rw [Real.dist_eq] at h
    exact h.le
  have hfin := czSel_finite a f t hfc hfi ht K
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ Q, Q ∈ S ↔ Q ∈ czSel a f t K := fun Q => Set.Finite.mem_toFinset _
  have hdisj : (S : Set (ℤ × (Fin N → ℤ))).PairwiseDisjoint fun Q => dyadicBox a Q.1 Q.2 := by
    rw [hSdef, Set.Finite.coe_toFinset]; exact czSel_pairwiseDisjoint a f t K
  set good : (Fin N → ℝ) → ℝ := fun x => f x - ∑ Q ∈ S, czBad a f Q x with hgood
  have hgood_in : ∀ Q ∈ S, ∀ x ∈ dyadicBox a Q.1 Q.2, good x = czAvg a f Q.1 Q.2 := by
    intro Q hQ x hx
    simp only [hgood]
    rw [sum_czBad_of_mem a hdisj hQ hx]
    ring
  have hgood_out : ∀ x, (∀ Q ∈ S, x ∉ dyadicBox a Q.1 Q.2) → good x = f x := by
    intro x hx
    simp only [hgood]
    rw [sum_czBad_of_notMem a hx, sub_zero]
  have havg : ∀ Q ∈ S, |czAvg a f Q.1 Q.2| ≤ 2 ^ homDim a * t := by
    intro Q hQ
    have h1 := (enorm_czAvg_mul_le a f Q.1 Q.2).trans
      (boxMass_le_of_mem_czSel a f t ((hSmem Q).1 hQ))
    rw [← mul_assoc] at h1
    have h2 := (ENNReal.mul_le_mul_iff_left (volume_dyadicBox_pos a _ _)
      (volume_dyadicBox_ne_top a _ _)).1 h1
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  set Ω := ⋃ Q ∈ S, dyadicBox a Q.1 Q.2 with hΩdef
  have hΩ : MeasurableSet Ω := S.measurableSet_biUnion fun Q _ => measurableSet_dyadicBox a _ _
  have hbm : ∀ Q ∈ S, MeasurableSet (dyadicBox a Q.1 Q.2) := fun Q _ => measurableSet_dyadicBox a _ _
  have hmass_le : ∑ Q ∈ S, boxMass a f Q.1 Q.2 ≤ eLpNorm f 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [boxMass]
    rw [← lintegral_biUnion_finset hdisj hbm]
    exact setLIntegral_le_lintegral _ _
  refine ⟨⟨S, good, czBad a f, hdisj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x; simp only [hgood]; ring
  · intro x
    by_cases hx : ∃ Q ∈ S, x ∈ dyadicBox a Q.1 Q.2
    · obtain ⟨Q, hQ, hxQ⟩ := hx
      rw [hgood_in Q hQ x hxQ]
      exact havg Q hQ
    · push Not at hx
      rw [hgood_out x hx]
      have h2t := abs_le_of_forall_notMem_czSel a f t hn hosc ht
        (fun Q hQ => hx Q ((hSmem Q).2 hQ))
      have h2 : (2 : ℝ) ≤ 2 ^ homDim a :=
        le_self_pow₀ (by norm_num) (by have := one_le_homDim a; omega)
      nlinarith
  · rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
      ← lintegral_add_compl _ hΩ, ← lintegral_add_compl (fun x => ‖f x‖ₑ) hΩ]
    refine add_le_add ?_ (le_of_eq (setLIntegral_congr_fun hΩ.compl fun x hx => ?_))
    · rw [hΩdef, lintegral_biUnion_finset hdisj hbm, lintegral_biUnion_finset hdisj hbm]
      refine Finset.sum_le_sum fun Q hQ => ?_
      rw [setLIntegral_congr_fun (g := fun _ => ‖czAvg a f Q.1 Q.2‖ₑ)
        (measurableSet_dyadicBox a _ _) fun x hx => by simp only [hgood_in Q hQ x hx],
        setLIntegral_const]
      exact enorm_czAvg_mul_le a f _ _
    · have hx' : ∀ Q ∈ S, x ∉ dyadicBox a Q.1 Q.2 := fun Q hQ hxQ =>
        hx (mem_biUnion hQ hxQ)
      simp only [hgood_out x hx']
  · intro Q x hx; exact czBad_eq_zero a f Q hx
  · intro Q p; exact memLp_czBad a hf hfc Q p
  · intro Q; exact integral_czBad a hf hfc Q
  · calc ∑ Q ∈ S, eLpNorm (czBad a f Q) 1 volume ≤ ∑ Q ∈ S, 2 * boxMass a f Q.1 Q.2 :=
          Finset.sum_le_sum fun Q _ => eLpNorm_czBad_le a f Q
      _ = 2 * ∑ Q ∈ S, boxMass a f Q.1 Q.2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * eLpNorm f 1 volume := by gcongr
  · calc ENNReal.ofReal t * ∑ Q ∈ S, volume (dyadicBox a Q.1 Q.2)
        = ∑ Q ∈ S, ENNReal.ofReal t * volume (dyadicBox a Q.1 Q.2) := Finset.mul_sum _ _ _
      _ ≤ ∑ Q ∈ S, boxMass a f Q.1 Q.2 :=
          Finset.sum_le_sum fun Q hQ => ((hSmem Q).1 hQ).2.1.le
      _ ≤ eLpNorm f 1 volume := hmass_le

end Exists

end UnforcedLeray.CZ
