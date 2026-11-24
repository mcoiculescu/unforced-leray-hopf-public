import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4

/-!
# Part II-b, task `PartII-b:T09/4/1` (`ChartWindowTest`): window tests pull back to phase tests

Source of record: `the November 2 reference manuscript`, SP 1639-1668, 1912-1916.
Target `chartWindowTest_proof : UnforcedLeray.Short.IIb.ChartWindowTest`.

Proof. Put `R = ε⁻¹` and `φ(τ,y) = winPer c χ (chart R τ y)`.
* `winPer` is `c`-periodic in `q`, so `φ` is `2εc`-periodic in `τ` (`Axi.chart_add_period`).
* `winPer c χ` is smooth on `ℝ³`: near a point where `x_q/c + 1/2` is not an integer the floor is
  locally constant; near a point where it is an integer, `winPer` vanishes (`|q - cm| ≥ c/2 - |q - q₀|`
  and the support of `χ` lies in `|q| ≤ c/2 - μ`).
* `χ` vanishes unless `s ∈ [a, b]` with `a > 0` (compact support in `s > 0`), so `φ = 0` near the axis
  (`s` large) and on `{s < a}`; off the axis the chart is smooth, so `φ` is smooth.
* `|η| ≤ M` on the support and `s ≥ a` bound `‖y‖`, so `φ` vanishes for `‖y‖` large.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace ChartWinHelp

/-- A compact subset of `(0, ∞)` has a positive lower and a finite upper bound. -/
theorem compact_bounds {K : Set ℝ} (hK : IsCompact K) (hpos : K ⊆ Ioi 0) :
    ∃ a > 0, ∃ b > 0, ∀ t ∈ K, a ≤ t ∧ t ≤ b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, 1, one_pos, fun t ht => by simp at ht⟩
  · exact ⟨sInf K, hpos (hK.sInf_mem hne), sSup K, hpos (hK.sSup_mem hne),
      fun t ht => ⟨csInf_le hK.bddBelow ht, le_csSup hK.bddAbove ht⟩⟩

/-- Support bounds of a window test: `s ∈ [a, b]` with `a > 0`, `|η| ≤ M` on the support. -/
theorem supp_bounds {c : ℝ} {χ : Coord → ℝ} (hχ : IsWinTest c χ) :
    ∃ a > 0, ∃ b > 0, ∃ M : ℝ, ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b ∧ |y.2.2| ≤ M := by
  have hK : IsCompact (tsupport χ) := hχ.1.compact
  have hsub : (fun x : Coord => x.1) '' tsupport χ ⊆ Ioi 0 := by
    rintro t ⟨x, hx, rfl⟩
    exact (hχ.1.supp hx).1
  obtain ⟨a, ha, b, hb, hab⟩ := compact_bounds (hK.image continuous_fst) hsub
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1 hK.isBounded
  refine ⟨a, ha, b, hb, M, fun y hy => ?_⟩
  have hyK : y ∈ tsupport χ := subset_tsupport χ (Function.mem_support.2 hy)
  have h1 := hab y.1 ⟨y, hyK, rfl⟩
  have hn : ‖y‖ ≤ M := by
    have := hM hyK
    rwa [mem_closedBall_zero_iff] at this
  have h2 : ‖y.2.2‖ ≤ M := ((norm_snd_le y.2).trans (norm_snd_le y)).trans hn
  exact ⟨h1.1, h1.2, by rwa [Real.norm_eq_abs] at h2⟩

/-- A margin: `χ` vanishes where `|q| ≥ c/2 - μ`. -/
theorem margin_of {c : ℝ} (hc : 0 < c) {χ : Coord → ℝ} (hχ : IsWinTest c χ) :
    ∃ μ > 0, ∀ x : Coord, c / 2 - μ ≤ |x.2.1| → χ x = 0 := by
  have hK : IsCompact (tsupport χ) := hχ.1.compact
  have hI : IsCompact ((fun x : Coord => |x.2.1|) '' tsupport χ) :=
    hK.image (continuous_abs.comp (continuous_fst.comp continuous_snd))
  obtain ⟨b', hb'lt, hb'⟩ : ∃ b' < c / 2, ∀ x ∈ tsupport χ, |x.2.1| ≤ b' := by
    rcases (tsupport χ).eq_empty_or_nonempty with he | hne
    · exact ⟨0, by linarith, fun x hx => by rw [he] at hx; simp at hx⟩
    · obtain ⟨x1, hx1, hx1e⟩ := hI.sSup_mem (hne.image _)
      refine ⟨sSup _, ?_, fun x hx => le_csSup hI.bddAbove ⟨x, hx, rfl⟩⟩
      rw [← hx1e]
      show |x1.2.1| < c / 2
      obtain ⟨h1a, h1b⟩ := hχ.2 hx1
      rw [abs_lt]
      exact ⟨by linarith, h1b⟩
  refine ⟨(c / 2 - b') / 2, by linarith, fun x hx => ?_⟩
  by_contra hne
  have hxK : x ∈ tsupport χ := subset_tsupport χ (Function.mem_support.2 hne)
  have := hb' x hxK
  linarith

/-- The `c`-periodization of a window function, as used in `ChartWindowTest`. -/
theorem winPer_zero_of_s {c : ℝ} {χ : Coord → ℝ} {a b : ℝ}
    (hab : ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b) (x : Coord) (hx : x.1 < a ∨ b < x.1) :
    winPer c χ x = 0 := by
  by_contra h
  have h' : χ (x.1, (x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2)) ≠ 0 := h
  obtain ⟨h1, h2⟩ := hab _ h'
  have h1' : a ≤ x.1 := h1
  have h2' : x.1 ≤ b := h2
  rcases hx with hx | hx <;> linarith

/-- `winPer` is `c`-periodic in `q`. -/
theorem winPer_add_c {c : ℝ} (hc : 0 < c) (χ : Coord → ℝ) (x : Coord) :
    winPer c χ (x.1, (x.2.1 + c, x.2.2)) = winPer c χ x := by
  unfold winPer
  have h : (x.2.1 + c) / c + 1 / 2 = x.2.1 / c + 1 / 2 + 1 := by
    field_simp
    ring
  rw [h, Int.floor_add_one]
  have e : x.2.1 + c - c * ((((⌊x.2.1 / c + 1 / 2⌋ + 1 : ℤ)) : ℤ) : ℝ) =
      x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) := by
    push_cast
    ring
  rw [e]

/-- `winPer` is smooth on `ℝ³`. -/
theorem winPer_contDiff {c : ℝ} (hc : 0 < c) {χ : Coord → ℝ} (hχ : IsWinTest c χ) :
    ContDiff ℝ ∞ (winPer c χ) := by
  rw [contDiff_iff_contDiffAt]
  intro x0
  by_cases hint : ∃ k : ℤ, x0.2.1 / c + 1 / 2 = k
  · obtain ⟨k, hk⟩ := hint
    obtain ⟨μ, hμ, hmar⟩ := margin_of hc hχ
    have hx0 : x0.2.1 = c * ((k : ℝ) - 1 / 2) := by
      have h1 : x0.2.1 / c = (k : ℝ) - 1 / 2 := by linarith
      rw [div_eq_iff hc.ne'] at h1
      linarith
    have hev : ∀ᶠ x in 𝓝 x0, |x.2.1 - x0.2.1| < μ := by
      have hc1 : Continuous fun x : Coord => |x.2.1 - x0.2.1| := by fun_prop
      exact hc1.continuousAt.eventually_lt continuousAt_const (by simpa using hμ)
    have hzero : winPer c χ =ᶠ[𝓝 x0] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with x hx
      show χ (x.1, (x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2)) = 0
      apply hmar
      show c / 2 - μ ≤ |x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ)|
      have hj : (1 : ℝ) / 2 ≤ |((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2| := by
        rcases le_or_gt (k - ⌊x.2.1 / c + 1 / 2⌋) 0 with h | h
        · have h' : ((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have h' : (1 : ℝ) ≤ ((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) := by
            exact_mod_cast (show (1 : ℤ) ≤ k - ⌊x.2.1 / c + 1 / 2⌋ by omega)
          rw [abs_of_nonneg (by linarith)]
          linarith
      have hdec : x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) =
          (x.2.1 - x0.2.1) + c * (((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2) := by
        push_cast
        rw [hx0]
        ring
      have habs : c / 2 ≤ |c * (((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2)| := by
        rw [abs_mul, abs_of_pos hc]
        nlinarith
      have htri : |c * (((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2)| ≤
          |x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ)| + |x.2.1 - x0.2.1| := by
        have e2 : c * (((k - ⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2) =
            (x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ)) - (x.2.1 - x0.2.1) := by
          rw [hdec]
          ring
        rw [e2]
        exact abs_sub _ _
      linarith
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hzero
  · push Not at hint
    have hlo : ((⌊x0.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) < x0.2.1 / c + 1 / 2 :=
      lt_of_le_of_ne (Int.floor_le _) (fun h => hint _ h.symm)
    have hhi : x0.2.1 / c + 1 / 2 < ((⌊x0.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hcont : Continuous fun x : Coord => x.2.1 / c + 1 / 2 := by fun_prop
    have hc1 : ∀ᶠ x in 𝓝 x0, ((⌊x0.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) < x.2.1 / c + 1 / 2 :=
      continuousAt_const.eventually_lt hcont.continuousAt hlo
    have hc2 : ∀ᶠ x in 𝓝 x0, x.2.1 / c + 1 / 2 < ((⌊x0.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
      hcont.continuousAt.eventually_lt continuousAt_const hhi
    have hfl : ∀ᶠ x in 𝓝 x0, ⌊x.2.1 / c + 1 / 2⌋ = ⌊x0.2.1 / c + 1 / 2⌋ := by
      filter_upwards [hc1, hc2] with x h1 h2
      rw [Int.floor_eq_iff]
      exact ⟨by exact_mod_cast h1.le, h2⟩
    have hshift : ContDiff ℝ ∞
        (fun x : Coord => χ (x.1, (x.2.1 - c * ((⌊x0.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2))) := by
      apply hχ.1.smooth.comp
      fun_prop
    have heq : winPer c χ =ᶠ[𝓝 x0]
        fun x : Coord => χ (x.1, (x.2.1 - c * ((⌊x0.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2)) := by
      filter_upwards [hfl] with x hx
      unfold winPer
      rw [hx]
    exact hshift.contDiffAt.congr_of_eventuallyEq heq

/-- The ring chart is smooth off the axis. -/
theorem chart_contDiffAt {R : ℝ} (hR : R ≠ 0) {x0 : ℝ × Space} (hx0 : x0.2 ∉ Axi.axis) :
    ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.chart R x.1 x.2) x0 := by
  have hϱ : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.ϱ x.2) x0 := by
    have h1 : ContDiffAt ℝ ∞ Axi.ϱ x0.2 :=
      Axi.contDiffOn_ϱ.contDiffAt (Axi.isClosed_axis.isOpen_compl.mem_nhds hx0)
    exact h1.comp x0 contDiffAt_snd
  have hpos : 0 < Axi.ϱ x0.2 := Axi.ϱ_pos hx0
  have hage : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.age R x.2) x0 := by
    unfold Axi.age
    exact contDiffAt_const.div (hϱ.pow 2) (pow_ne_zero _ hpos.ne')
  have hagepos : Axi.age R x0.2 ≠ 0 := by
    unfold Axi.age
    exact div_ne_zero (pow_ne_zero _ hR) (pow_ne_zero _ hpos.ne')
  have hphase : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.phase R x.1 x.2) x0 := by
    unfold Axi.phase
    exact ((contDiffAt_const.mul contDiffAt_fst).div_const 2).sub
      (contDiffAt_const.mul (hage.log hagepos))
  have hy2 : ContDiffAt ℝ ∞ (fun x : ℝ × Space => x.2 2) x0 :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffAt).comp x0 contDiffAt_snd
  have htrans : ContDiffAt ℝ ∞ (fun x : ℝ × Space => Axi.trans R x.2) x0 := by
    unfold Axi.trans
    exact (contDiffAt_const.mul hy2).div hϱ hpos.ne'
  unfold Axi.chart
  exact hage.prodMk (hphase.prodMk htrans)

end ChartWinHelp

namespace ChartWinHelp2

open ChartWinHelp

/-- The support bound on the chart: `a ≤ s` and `|η| ≤ M` give `a‖y‖² ≤ R² + M²`. -/
theorem supp_norm_bound {R a M : ℝ} (hR : 0 < R) (ha : 0 < a) {y : Space}
    (h1 : a ≤ Axi.age R y) (h2 : |Axi.trans R y| ≤ M) : a * ‖y‖ ^ 2 ≤ R ^ 2 + M ^ 2 := by
  have hϱ : 0 < Axi.ϱ y := by
    by_contra h0
    have h0' : Axi.ϱ y = 0 := le_antisymm (not_lt.1 h0) (Real.sqrt_nonneg _)
    have h3 : Axi.age R y = 0 := by
      unfold Axi.age
      rw [h0']
      simp
    linarith
  have hϱsq : Axi.ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hn2 : ‖y‖ ^ 2 = Axi.ϱ y ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hϱsq]
    simp [Real.norm_eq_abs, sq_abs]
  have hA : a * Axi.ϱ y ^ 2 ≤ R ^ 2 := by
    have h1' : a ≤ R ^ 2 / Axi.ϱ y ^ 2 := h1
    rwa [le_div_iff₀ (pow_pos hϱ 2)] at h1'
  have hB : (R * y 2) ^ 2 ≤ (M * Axi.ϱ y) ^ 2 := by
    have h2' : |R * y 2 / Axi.ϱ y| ≤ M := h2
    rw [abs_div, abs_of_pos hϱ, div_le_iff₀ hϱ] at h2'
    nlinarith [abs_nonneg (R * y 2), sq_abs (R * y 2)]
  have hC : a * (y 2) ^ 2 * R ^ 2 ≤ M ^ 2 * R ^ 2 := by
    have e1 : a * (y 2) ^ 2 * R ^ 2 = a * (R * y 2) ^ 2 := by ring
    have hm1 : a * (R * y 2) ^ 2 ≤ a * (M * Axi.ϱ y) ^ 2 := mul_le_mul_of_nonneg_left hB ha.le
    have hm2 : M ^ 2 * (a * Axi.ϱ y ^ 2) ≤ M ^ 2 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hA (sq_nonneg M)
    have e2 : a * (M * Axi.ϱ y) ^ 2 = M ^ 2 * (a * Axi.ϱ y ^ 2) := by ring
    linarith
  have hD : a * (y 2) ^ 2 ≤ M ^ 2 := le_of_mul_le_mul_right hC (pow_pos hR 2)
  have hE : a * ‖y‖ ^ 2 = a * Axi.ϱ y ^ 2 + a * (y 2) ^ 2 := by
    rw [hn2]
    ring
  linarith

/-- The support of a window test bounds `winPer` values. -/
theorem winPer_bounds {c a b M : ℝ} {χ : Coord → ℝ}
    (hab : ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b ∧ |y.2.2| ≤ M) (x : Coord)
    (h : winPer c χ x ≠ 0) : a ≤ x.1 ∧ x.1 ≤ b ∧ |x.2.2| ≤ M :=
  hab (x.1, (x.2.1 - c * ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ), x.2.2)) h

/-- The chart pullback of `winPer` is smooth on `ℝ × ℝ³`. -/
theorem G_contDiff {c R : ℝ} (hc : 0 < c) (hR : 0 < R) {χ : Coord → ℝ} (hχ : IsWinTest c χ) :
    ContDiff ℝ ∞ (fun x : ℝ × Space => winPer c χ (Axi.chart R x.1 x.2)) := by
  obtain ⟨a, ha, b, hb, M, hab⟩ := supp_bounds hχ
  have hab' : ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b :=
    fun y hy => ⟨(hab y hy).1, (hab y hy).2.1⟩
  rw [contDiff_iff_contDiffAt]
  intro x0
  by_cases hax : x0.2 ∈ Axi.axis
  · have hϱ0 : Axi.ϱ x0.2 = 0 := by
      obtain ⟨h0, h1⟩ := hax
      unfold Axi.ϱ
      rw [h0, h1]
      simp
    have hcont : Continuous fun x : ℝ × Space => Axi.ϱ x.2 :=
      Axi.continuous_ϱ.comp continuous_snd
    have hev : ∀ᶠ x in 𝓝 x0, Axi.ϱ x.2 < R / (b + 1) := by
      refine hcont.continuousAt.eventually_lt continuousAt_const ?_
      rw [hϱ0]
      exact div_pos hR (by linarith)
    have hzero : (fun x : ℝ × Space => winPer c χ (Axi.chart R x.1 x.2)) =ᶠ[𝓝 x0]
        fun _ => (0 : ℝ) := by
      filter_upwards [hev] with x hx
      apply winPer_zero_of_s hab'
      show Axi.age R x.2 < a ∨ b < Axi.age R x.2
      by_cases h0 : Axi.ϱ x.2 = 0
      · left
        have h3 : Axi.age R x.2 = 0 := by
          unfold Axi.age
          rw [h0]
          simp
        rw [h3]
        exact ha
      · right
        have hnn : 0 ≤ Axi.ϱ x.2 := Real.sqrt_nonneg _
        have hp : 0 < Axi.ϱ x.2 := lt_of_le_of_ne hnn (Ne.symm h0)
        have h2 : Axi.ϱ x.2 * (b + 1) < R := (lt_div_iff₀ (by linarith : (0 : ℝ) < b + 1)).1 hx
        unfold Axi.age
        rw [lt_div_iff₀ (pow_pos hp 2)]
        have h3 : 0 < R + Axi.ϱ x.2 * (b + 1) := by
          have := mul_pos hp (show (0 : ℝ) < b + 1 by linarith)
          linarith
        have h4 := mul_pos (sub_pos.2 h2) h3
        nlinarith [h4, mul_nonneg (sq_nonneg (Axi.ϱ x.2))
          (show (0 : ℝ) ≤ b ^ 2 + b + 1 by nlinarith [sq_nonneg b])]
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · exact (winPer_contDiff hc hχ).contDiffAt.comp x0 (chart_contDiffAt hR.ne' hax)

end ChartWinHelp2

open ChartWinHelp ChartWinHelp2 in
/-- **Leaf `T09/4/1`** (SP 1912-1918): a window test pulls back through the ring chart to a phase
test (smooth and periodic in `τ`, vanishing near the axis and at spatial infinity). -/
theorem chartWindowTest_proof : UnforcedLeray.Short.IIb.ChartWindowTest := by
  intro c ε χ hc hε hχ
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hR : ε⁻¹ ≠ 0 := hRpos.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  have hG := G_contDiff hc hRpos hχ
  obtain ⟨a, ha, b, hb, M, hab⟩ := supp_bounds hχ
  refine ⟨fun x => ((winPer c χ (Axi.chart ε⁻¹ x.1 x.2) : ℝ) : ℂ),
    ⟨⟨?_, ?_, ?_⟩, fun τ y _ => rfl⟩⟩
  · exact Complex.ofRealCLM.contDiff.comp hG
  · intro τ y
    have hper : winPer c χ (Axi.chart ε⁻¹ (τ + 2 * ε * c) y) =
        winPer c χ (Axi.chart ε⁻¹ τ y) := by
      rw [Axi.chart_add_period hR hP τ y]
      exact winPer_add_c hc χ (Axi.chart ε⁻¹ τ y)
    show ((winPer c χ (Axi.chart ε⁻¹ (τ + 2 * ε * c) y) : ℝ) : ℂ) =
      ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ)
    rw [hper]
  · refine ⟨(((ε⁻¹) ^ 2 + M ^ 2) / a) + 1, fun τ y hy => ?_⟩
    show ((winPer c χ (Axi.chart ε⁻¹ τ y) : ℝ) : ℂ) = 0
    rw [Complex.ofReal_eq_zero]
    by_contra hne
    obtain ⟨h1, _, h3⟩ := winPer_bounds hab _ hne
    have hbound := supp_norm_bound hRpos ha h1 h3
    set T := ((ε⁻¹) ^ 2 + M ^ 2) / a + 1 with hT
    have hTa : a * T = (ε⁻¹) ^ 2 + M ^ 2 + a := by
      rw [hT]
      field_simp
    have hT1 : 1 ≤ T := by
      have : 0 ≤ ((ε⁻¹) ^ 2 + M ^ 2) / a := div_nonneg (by positivity) ha.le
      rw [hT]
      linarith
    have hTpos : 0 ≤ T := by linarith
    have h4 : T ^ 2 < ‖y‖ ^ 2 := by nlinarith
    have h5 : a * T ^ 2 ≤ a * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_left h4.le ha.le
    have h6 : a * T ≤ a * T ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ha.le hTpos) (sub_nonneg.2 hT1)]
    nlinarith
