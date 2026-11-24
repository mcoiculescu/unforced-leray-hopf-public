import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.PouProps

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- Summand of the age interpolation at node `k`: the local linear interpolant at `r`. -/
def i1L (t₀ t₁ : ℝ) (K : ℕ) (g : ℝ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  g (gridPt t₀ t₁ K k) + (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K *
    (g (gridPt t₀ t₁ K (k + 1)) - g (gridPt t₀ t₁ K k))

/-- Slope of the local linear interpolant at node `k`. -/
def i1S (t₀ t₁ : ℝ) (K : ℕ) (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  1 / gridH t₀ t₁ K * (g (gridPt t₀ t₁ K (k + 1)) - g (gridPt t₀ t₁ K k))

theorem i1_interp (t₀ t₁ : ℝ) (K : ℕ) (g : ℝ → ℝ) (r : ℝ) :
    interp1 t₀ t₁ K g r = ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * i1L t₀ t₁ K g r k := rfl

theorem i1_hasDerivAt (t₀ t₁ : ℝ) (K : ℕ) (g : ℝ → ℝ) (r : ℝ) (k : ℕ)
    (hp : HasDerivAt (pou t₀ t₁ K k) (deriv (pou t₀ t₁ K k) r) r) :
    HasDerivAt (fun y => pou t₀ t₁ K k y * i1L t₀ t₁ K g y k)
      (deriv (pou t₀ t₁ K k) r * i1L t₀ t₁ K g r k + pou t₀ t₁ K k r * i1S t₀ t₁ K g k) r := by
  have h1 : HasDerivAt (fun y => (y - gridPt t₀ t₁ K k) / gridH t₀ t₁ K)
      (1 / gridH t₀ t₁ K) r :=
    ((hasDerivAt_id' r).sub_const _).div_const _
  have hl : HasDerivAt (fun y => i1L t₀ t₁ K g y k) (i1S t₀ t₁ K g k) r :=
    (h1.mul_const _).const_add _
  exact hp.mul hl

theorem sum_split_aux (K : ℕ) (Q P L σ : ℕ → ℝ) (c G : ℝ)
    (hQ : ∑ k ∈ Finset.range K, Q k = 0) (hP : ∑ k ∈ Finset.range K, P k = 1) :
    (∑ k ∈ Finset.range K, (Q k * L k + P k * σ k)) - G =
      ∑ k ∈ Finset.range K, (Q k * (L k - c) + P k * (σ k - G)) := by
  have h2 : ∀ k, Q k * (L k - c) + P k * (σ k - G) =
      (Q k * L k + P k * σ k) - (c * Q k + G * P k) := fun k => by ring
  have e3 : ∑ k ∈ Finset.range K, (c * Q k + G * P k) = c * ∑ k ∈ Finset.range K, Q k +
      G * ∑ k ∈ Finset.range K, P k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k _ => h2 k), Finset.sum_sub_distrib, e3, hQ, hP]
  ring

/-- Linearization of `g` at an interior point `r`, using the oscillation of `g'`. -/
theorem interp1D_lin {t₀ t₁ h w : ℝ} {g g' : ℝ → ℝ} (hg : ContinuousOn g (Icc t₀ t₁))
    (hd : ∀ r ∈ Ioo t₀ t₁, HasDerivAt g (g' r) r)
    (hw : ∀ r ∈ Ioo t₀ t₁, ∀ r' ∈ Ioo t₀ t₁, |r - r'| ≤ 2 * h → |g' r - g' r'| ≤ w)
    {r : ℝ} (hr : r ∈ Ioo t₀ t₁) {a : ℝ} (ha : a ∈ Icc t₀ t₁) (har : |a - r| ≤ 2 * h) :
    |g a - g r - g' r * (a - r)| ≤ w * |a - r| := by
  rcases lt_trichotomy a r with h1 | h1 | h1
  · obtain ⟨ζ, hζ, hslope⟩ := exists_hasDerivAt_eq_slope g g' h1
      (hg.mono (Icc_subset_Icc ha.1 hr.2.le))
      (fun x hx => hd x ⟨lt_of_le_of_lt ha.1 hx.1, lt_trans hx.2 hr.2⟩)
    have hne : r - a ≠ 0 := (sub_pos.2 h1).ne'
    have hG : g r - g a = g' ζ * (r - a) := (div_eq_iff hne).1 hslope.symm
    have hζI : ζ ∈ Ioo t₀ t₁ := ⟨lt_of_le_of_lt ha.1 hζ.1, lt_trans hζ.2 hr.2⟩
    have e1 : |a - r| = r - a := by rw [abs_sub_comm, abs_of_pos (sub_pos.2 h1)]
    have hζr : |r - ζ| ≤ 2 * h := by
      rw [abs_of_pos (sub_pos.2 hζ.2)]
      linarith [hζ.1, e1, har]
    have hb := hw r hr ζ hζI hζr
    have key : g a - g r - g' r * (a - r) = (g' r - g' ζ) * (r - a) := by
      linear_combination (-1 : ℝ) * hG
    rw [key, abs_mul, abs_sub_comm a r]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  · rw [h1]; simp
  · obtain ⟨ζ, hζ, hslope⟩ := exists_hasDerivAt_eq_slope g g' h1
      (hg.mono (Icc_subset_Icc hr.1.le ha.2))
      (fun x hx => hd x ⟨lt_trans hr.1 hx.1, lt_of_lt_of_le hx.2 ha.2⟩)
    have hne : a - r ≠ 0 := (sub_pos.2 h1).ne'
    have hG : g a - g r = g' ζ * (a - r) := (div_eq_iff hne).1 hslope.symm
    have hζI : ζ ∈ Ioo t₀ t₁ := ⟨lt_trans hr.1 hζ.1, lt_of_lt_of_le hζ.2 ha.2⟩
    have e1 : |a - r| = a - r := abs_of_pos (sub_pos.2 h1)
    have hζr : |r - ζ| ≤ 2 * h := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.2 hζ.1)]
      linarith [hζ.2, e1, har]
    have hb := hw r hr ζ hζI hζr
    have key : g a - g r - g' r * (a - r) = -((g' r - g' ζ) * (a - r)) := by
      linear_combination hG
    rw [key, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-- Chord estimate with derivative oscillation (the second-order part of the value error). -/
theorem interp1D_chord {ga gb gr D w a r h s : ℝ} (hh : 0 < h) (hw : 0 ≤ w)
    (hsh : r - a = s * h) (hs2 : -1 / 2 ≤ s) (hs3 : s ≤ 3 / 2)
    (ea : |ga - gr - D * (a - r)| ≤ w * |a - r|)
    (eb : |gb - gr - D * (a + h - r)| ≤ w * |a + h - r|) :
    |ga + s * (gb - ga) - gr| ≤ 3 / 2 * w * h := by
  have hid : ga + s * (gb - ga) - gr =
      (1 - s) * (ga - gr - D * (a - r)) + s * (gb - gr - D * (a + h - r)) := by
    linear_combination (-D) * hsh
  have e1 : |a - r| = |s| * h := by
    rw [abs_sub_comm, hsh, abs_mul, abs_of_pos hh]
  have e2 : |a + h - r| = |1 - s| * h := by
    rw [show a + h - r = (1 - s) * h by linear_combination (-1 : ℝ) * hsh, abs_mul,
      abs_of_pos hh]
  have hA : |1 - s| * |ga - gr - D * (a - r)| ≤ |1 - s| * (w * (|s| * h)) :=
    mul_le_mul_of_nonneg_left (by rw [← e1]; exact ea) (abs_nonneg _)
  have hB : |s| * |gb - gr - D * (a + h - r)| ≤ |s| * (w * (|1 - s| * h)) :=
    mul_le_mul_of_nonneg_left (by rw [← e2]; exact eb) (abs_nonneg _)
  have hsplit : |(1 - s) * (ga - gr - D * (a - r)) + s * (gb - gr - D * (a + h - r))| ≤
      |1 - s| * |ga - gr - D * (a - r)| + |s| * |gb - gr - D * (a + h - r)| := by
    calc |(1 - s) * (ga - gr - D * (a - r)) + s * (gb - gr - D * (a + h - r))|
        ≤ |(1 - s) * (ga - gr - D * (a - r))| + |s * (gb - gr - D * (a + h - r))| :=
          abs_add_le _ _
      _ = |1 - s| * |ga - gr - D * (a - r)| + |s| * |gb - gr - D * (a + h - r)| := by
          rw [abs_mul, abs_mul]
  have hq : |s| * |1 - s| ≤ 3 / 4 := by
    rw [← abs_mul, abs_le]
    constructor
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ s + 1 / 2 by linarith)
        (show (0 : ℝ) ≤ 3 / 2 - s by linarith)]
    · nlinarith [sq_nonneg (s - 1 / 2)]
  have hfin : |ga + s * (gb - ga) - gr| ≤
      |1 - s| * (w * (|s| * h)) + |s| * (w * (|1 - s| * h)) := by
    rw [hid]
    exact le_trans hsplit (add_le_add hA hB)
  have hsum : |1 - s| * (w * (|s| * h)) + |s| * (w * (|1 - s| * h)) =
      2 * w * h * (|s| * |1 - s|) := by ring
  have hbound : 2 * w * h * (|s| * |1 - s|) ≤ 3 / 2 * w * h := by
    have h0 : 2 * w * h * (|s| * |1 - s|) ≤ 2 * w * h * (3 / 4) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg (by norm_num) hw) hh.le)
    have h1 : 2 * w * h * (3 / 4) = 3 / 2 * w * h := by ring
    linarith
  linarith [hfin, hsum, hbound]

/-- Chord estimate for the value error. -/
theorem interp1D_chordVal {ga gb gr w s : ℝ} (hw : 0 ≤ w) (hs2 : -1 / 2 ≤ s) (hs3 : s ≤ 3 / 2)
    (ea : |ga - gr| ≤ w) (eb : |gb - gr| ≤ w) :
    |ga + s * (gb - ga) - gr| ≤ 2 * w := by
  have hid : ga + s * (gb - ga) - gr = (1 - s) * (ga - gr) + s * (gb - gr) := by ring
  have h1 : |(1 - s) * (ga - gr) + s * (gb - gr)| ≤ |1 - s| * w + |s| * w := by
    calc |(1 - s) * (ga - gr) + s * (gb - gr)|
        ≤ |(1 - s) * (ga - gr)| + |s * (gb - gr)| := abs_add_le _ _
      _ = |1 - s| * |ga - gr| + |s| * |gb - gr| := by rw [abs_mul, abs_mul]
      _ ≤ |1 - s| * w + |s| * w :=
          add_le_add (mul_le_mul_of_nonneg_left ea (abs_nonneg _))
            (mul_le_mul_of_nonneg_left eb (abs_nonneg _))
  have h2 : |1 - s| + |s| ≤ 2 := by
    rcases abs_cases (1 - s) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
      rcases abs_cases s with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;> linarith
  have h5 : (|1 - s| + |s|) * w ≤ 2 * w := mul_le_mul_of_nonneg_right h2 hw
  rw [hid]
  exact le_trans h1 (by linarith [h5, show |1 - s| * w + |s| * w = (|1 - s| + |s|) * w by ring])

theorem interp1D_s_bounds {x h s : ℝ} (hh : 0 < h) (hsh : x = s * h)
    (h1 : -(h / 2) ≤ x) (h2 : x ≤ 3 * h / 2) : -1 / 2 ≤ s ∧ s ≤ 3 / 2 := by
  constructor <;> nlinarith

theorem interp1D : UnforcedLeray.Short.IIb.TdSums.Interp1D := by
  obtain ⟨hCD, hSum, D, hD0, hPou⟩ := (pouProps : UnforcedLeray.Short.IIb.TdSums.PouProps)
  refine ⟨2 + 2 * D, by linarith, fun t₀ t₁ K ht hK => ?_⟩
  have hsumK : ∀ r : ℝ, ∑ k ∈ Finset.range K, pou t₀ t₁ K k r = 1 :=
    fun r => hSum t₀ t₁ K hK r
  rcases eq_or_lt_of_le ht with htt | htt
  · -- degenerate interval: `Ioo` is empty and the value error is zero
    have hh0 : gridH t₀ t₁ K = 0 := by unfold gridH; rw [← htt, sub_self, zero_div]
    have hgp : ∀ k, gridPt t₀ t₁ K k = t₀ := fun k => by
      unfold gridPt; rw [hh0, mul_zero, add_zero]
    refine ⟨fun g w hw r hr => ?_, fun g g' w _ _ _ r hr => ?_⟩
    · have hr' : r = t₀ := le_antisymm (by linarith [hr.2]) hr.1
      have hw0 : 0 ≤ w := by
        have := hw r hr r hr (by simp [hh0])
        linarith [abs_nonneg (g r - g r)]
      have key : interp1 t₀ t₁ K g t₀ = g t₀ := by
        rw [i1_interp]
        have e : ∀ k, pou t₀ t₁ K k t₀ * i1L t₀ t₁ K g t₀ k = pou t₀ t₁ K k t₀ * g t₀ := by
          intro k
          unfold i1L
          rw [hgp k, hgp (k + 1), hh0]
          simp
        rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_mul, hsumK t₀, one_mul]
      rw [hr', key, sub_self, abs_zero]
      exact mul_nonneg (by linarith) hw0
    · exfalso
      linarith [hr.1, hr.2]
  · have hpos : 0 < gridH t₀ t₁ K := pouT_gridH_pos htt hK
    obtain ⟨hPnn, hDsum, hsupp⟩ := hPou t₀ t₁ K htt hK
    have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hgmem : ∀ j : ℕ, j ≤ K → gridPt t₀ t₁ K j ∈ Icc t₀ t₁ := by
      intro j hj
      have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj
      have hKh : (K : ℝ) * gridH t₀ t₁ K = t₁ - t₀ := by
        unfold gridH; field_simp
      constructor
      · unfold gridPt
        have := mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) hpos.le
        linarith
      · unfold gridPt
        have := mul_le_mul_of_nonneg_right hjK hpos.le
        linarith
    have hsup : ∀ k ∈ Finset.range K, ∀ r ∈ Icc t₀ t₁,
        (pou t₀ t₁ K k r ≠ 0 ∨ deriv (pou t₀ t₁ K k) r ≠ 0) →
        gridPt t₀ t₁ K k - gridH t₀ t₁ K / 2 ≤ r ∧
          r ≤ gridPt t₀ t₁ K k + gridH t₀ t₁ K + gridH t₀ t₁ K / 2 := by
      intro k _ r hr hne
      have := hsupp k r hr hne
      rw [pouT_gridPt_succ] at this
      exact this
    refine ⟨fun g w hw r hr => ?_, fun g g' w hg hd hw r hr => ?_⟩
    · -- value estimate
      have hw0 : 0 ≤ w := by
        have := hw r hr r hr (by rw [sub_self, abs_zero]; linarith)
        linarith [abs_nonneg (g r - g r)]
      have hV : ∀ k ∈ Finset.range K,
          pou t₀ t₁ K k r * |i1L t₀ t₁ K g r k - g r| ≤ pou t₀ t₁ K k r * (2 * w) := by
        intro k hk
        by_cases hP : pou t₀ t₁ K k r = 0
        · simp [hP]
        · obtain ⟨hs1, hs2⟩ := hsup k hk r hr (Or.inl hP)
          have hak := hgmem k (Nat.le_of_lt (Finset.mem_range.1 hk))
          have hak1 := hgmem (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.1 hk))
          have hsucc := pouT_gridPt_succ t₀ t₁ K k
          rw [hsucc] at hak1
          have hdist0 : |gridPt t₀ t₁ K k - r| ≤ 2 * gridH t₀ t₁ K := by
            rw [abs_le]; constructor <;> linarith
          have hdist1 : |gridPt t₀ t₁ K k + gridH t₀ t₁ K - r| ≤ 2 * gridH t₀ t₁ K := by
            rw [abs_le]; constructor <;> linarith
          have ea : |g (gridPt t₀ t₁ K k) - g r| ≤ w :=
            hw _ hak r hr hdist0
          have eb : |g (gridPt t₀ t₁ K k + gridH t₀ t₁ K) - g r| ≤ w :=
            hw _ hak1 r hr hdist1
          have hsh : r - gridPt t₀ t₁ K k =
              (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K * gridH t₀ t₁ K :=
            (div_mul_cancel₀ _ hpos.ne').symm
          obtain ⟨hb1, hb2⟩ := interp1D_s_bounds hpos hsh (by linarith) (by linarith)
          have hL := interp1D_chordVal hw0 hb1 hb2 ea eb
          unfold i1L
          rw [hsucc]
          exact mul_le_mul_of_nonneg_left hL (hPnn k r)
      have hdecomp : interp1 t₀ t₁ K g r - g r =
          ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * (i1L t₀ t₁ K g r k - g r) := by
        rw [i1_interp]
        have e : ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * (i1L t₀ t₁ K g r k - g r) =
            ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * i1L t₀ t₁ K g r k -
              (∑ k ∈ Finset.range K, pou t₀ t₁ K k r) * g r := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [e, hsumK r, one_mul]
      have hval : |∑ k ∈ Finset.range K, pou t₀ t₁ K k r * (i1L t₀ t₁ K g r k - g r)| ≤ 2 * w := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        calc ∑ k ∈ Finset.range K, |pou t₀ t₁ K k r * (i1L t₀ t₁ K g r k - g r)|
            = ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * |i1L t₀ t₁ K g r k - g r| :=
              Finset.sum_congr rfl (fun k _ => by rw [abs_mul, abs_of_nonneg (hPnn k r)])
          _ ≤ ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * (2 * w) := Finset.sum_le_sum hV
          _ = (∑ k ∈ Finset.range K, pou t₀ t₁ K k r) * (2 * w) := by rw [Finset.sum_mul]
          _ = 2 * w := by rw [hsumK r, one_mul]
      rw [hdecomp]
      nlinarith [mul_nonneg hD0 hw0, hval]
    · -- derivative estimate
      have hw0 : 0 ≤ w := by
        have := hw r hr r hr
          (by rw [sub_self, abs_zero]; linarith)
        linarith [abs_nonneg (g' r - g' r)]
      have hQ0 : ∑ k ∈ Finset.range K, deriv (pou t₀ t₁ K k) r = 0 := by
        have h1 : HasDerivAt (fun y => ∑ k ∈ Finset.range K, pou t₀ t₁ K k y)
            (∑ k ∈ Finset.range K, deriv (pou t₀ t₁ K k) r) r :=
          HasDerivAt.fun_sum (fun k _ => ((hCD t₀ t₁ K k).differentiable (by simp) r).hasDerivAt)
        have h2 : (fun y => ∑ k ∈ Finset.range K, pou t₀ t₁ K k y) = fun _ => (1 : ℝ) :=
          funext (fun y => hsumK y)
        rw [h2] at h1
        exact h1.unique (hasDerivAt_const r (1 : ℝ))
      have hI : HasDerivAt (interp1 t₀ t₁ K g)
          (∑ k ∈ Finset.range K, (deriv (pou t₀ t₁ K k) r * i1L t₀ t₁ K g r k +
            pou t₀ t₁ K k r * i1S t₀ t₁ K g k)) r := by
        have hfun : interp1 t₀ t₁ K g =
            fun y => ∑ k ∈ Finset.range K, pou t₀ t₁ K k y * i1L t₀ t₁ K g y k := by
          funext y; rfl
        rw [hfun]
        exact HasDerivAt.fun_sum (fun k _ => i1_hasDerivAt t₀ t₁ K g r k
          ((hCD t₀ t₁ K k).differentiable (by simp) r).hasDerivAt)
      rw [hI.deriv]
      have hsplit : (∑ k ∈ Finset.range K, (deriv (pou t₀ t₁ K k) r * i1L t₀ t₁ K g r k +
            pou t₀ t₁ K k r * i1S t₀ t₁ K g k)) - g' r =
          ∑ k ∈ Finset.range K, (deriv (pou t₀ t₁ K k) r * (i1L t₀ t₁ K g r k - g r) +
            pou t₀ t₁ K k r * (i1S t₀ t₁ K g k - g' r)) :=
        sum_split_aux K (fun k => deriv (pou t₀ t₁ K k) r) (fun k => pou t₀ t₁ K k r)
          (fun k => i1L t₀ t₁ K g r k) (fun k => i1S t₀ t₁ K g k) (g r) (g' r) hQ0 (hsumK r)
      rw [hsplit, Finset.sum_add_distrib]
      have hA : |∑ k ∈ Finset.range K,
          deriv (pou t₀ t₁ K k) r * (i1L t₀ t₁ K g r k - g r)| ≤ 3 / 2 * D * w := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hk : ∀ k ∈ Finset.range K,
            |deriv (pou t₀ t₁ K k) r * (i1L t₀ t₁ K g r k - g r)| ≤
              |deriv (pou t₀ t₁ K k) r| * (3 / 2 * w * gridH t₀ t₁ K) := by
          intro k hk
          rw [abs_mul]
          by_cases hQ : deriv (pou t₀ t₁ K k) r = 0
          · simp [hQ]
          · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            obtain ⟨hs1, hs2⟩ := hsup k hk r (Ioo_subset_Icc_self hr) (Or.inr hQ)
            have hsucc := pouT_gridPt_succ t₀ t₁ K k
            have hak := hgmem k (Nat.le_of_lt (Finset.mem_range.1 hk))
            have hak1 := hgmem (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.1 hk))
            rw [hsucc] at hak1
            have hdist0 : |gridPt t₀ t₁ K k - r| ≤ 2 * gridH t₀ t₁ K := by
              rw [abs_le]; constructor <;> linarith
            have hdist1 : |gridPt t₀ t₁ K k + gridH t₀ t₁ K - r| ≤ 2 * gridH t₀ t₁ K := by
              rw [abs_le]; constructor <;> linarith
            have ea := interp1D_lin hg hd hw hr hak hdist0
            have eb := interp1D_lin hg hd hw hr hak1 hdist1
            have hsh : r - gridPt t₀ t₁ K k =
                (r - gridPt t₀ t₁ K k) / gridH t₀ t₁ K * gridH t₀ t₁ K :=
              (div_mul_cancel₀ _ hpos.ne').symm
            obtain ⟨hb1, hb2⟩ := interp1D_s_bounds hpos hsh (by linarith) (by linarith)
            have hc := interp1D_chord hpos hw0 hsh hb1 hb2 ea eb
            unfold i1L
            rw [hsucc]
            exact hc
        calc ∑ k ∈ Finset.range K,
              |deriv (pou t₀ t₁ K k) r * (i1L t₀ t₁ K g r k - g r)|
            ≤ ∑ k ∈ Finset.range K,
              |deriv (pou t₀ t₁ K k) r| * (3 / 2 * w * gridH t₀ t₁ K) :=
              Finset.sum_le_sum hk
          _ = (∑ k ∈ Finset.range K, |deriv (pou t₀ t₁ K k) r|) *
              (3 / 2 * w * gridH t₀ t₁ K) := by rw [Finset.sum_mul]
          _ ≤ (D / gridH t₀ t₁ K) * (3 / 2 * w * gridH t₀ t₁ K) :=
              mul_le_mul_of_nonneg_right (hDsum r)
                (mul_nonneg (mul_nonneg (by norm_num) hw0) hpos.le)
          _ = 3 / 2 * D * w := by
              rw [div_mul_eq_mul_div, div_eq_iff hpos.ne']; ring
      have hB : |∑ k ∈ Finset.range K,
          pou t₀ t₁ K k r * (i1S t₀ t₁ K g k - g' r)| ≤ w := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hk : ∀ k ∈ Finset.range K,
            |pou t₀ t₁ K k r * (i1S t₀ t₁ K g k - g' r)| ≤ pou t₀ t₁ K k r * w := by
          intro k hk
          rw [abs_mul, abs_of_nonneg (hPnn k r)]
          by_cases hP : pou t₀ t₁ K k r = 0
          · simp [hP]
          · refine mul_le_mul_of_nonneg_left ?_ (hPnn k r)
            obtain ⟨hs1, hs2⟩ := hsup k hk r (Ioo_subset_Icc_self hr) (Or.inl hP)
            have hsucc := pouT_gridPt_succ t₀ t₁ K k
            have hak := hgmem k (Nat.le_of_lt (Finset.mem_range.1 hk))
            have hak1 := hgmem (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.1 hk))
            rw [hsucc] at hak1
            have hlt : gridPt t₀ t₁ K k < gridPt t₀ t₁ K k + gridH t₀ t₁ K := by linarith
            have hcont : ContinuousOn g (Icc (gridPt t₀ t₁ K k)
                (gridPt t₀ t₁ K k + gridH t₀ t₁ K)) :=
              hg.mono (Icc_subset_Icc hak.1 hak1.2)
            obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hlt hcont
              (fun x hx => hd x ⟨lt_of_le_of_lt hak.1 hx.1, lt_of_lt_of_le hx.2 hak1.2⟩)
            have hS : i1S t₀ t₁ K g k = g' ξ := by
              unfold i1S
              rw [hsucc, hξeq, add_sub_cancel_left]
              ring
            have hdist : |ξ - r| ≤ 2 * gridH t₀ t₁ K := by
              rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2]
            have hξI : ξ ∈ Ioo t₀ t₁ :=
              ⟨lt_of_le_of_lt hak.1 hξ.1, lt_of_lt_of_le hξ.2 hak1.2⟩
            rw [hS]
            exact hw ξ hξI r hr hdist
        calc ∑ k ∈ Finset.range K, |pou t₀ t₁ K k r * (i1S t₀ t₁ K g k - g' r)|
            ≤ ∑ k ∈ Finset.range K, pou t₀ t₁ K k r * w := Finset.sum_le_sum hk
          _ = (∑ k ∈ Finset.range K, pou t₀ t₁ K k r) * w := by rw [Finset.sum_mul]
          _ = w := by rw [hsumK r, one_mul]
      refine le_trans (abs_add_le _ _) ?_
      nlinarith [hA, hB, mul_nonneg hD0 hw0]

end TdSums

end UnforcedLeray.Short.IIb
