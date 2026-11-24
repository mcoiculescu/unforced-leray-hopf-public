import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_3

/-!
# `PartII-b:T10/7/1/1/3` piece: `gl_profPeriodic` (periodic representative of profiles)

Source of record: `the November 2 reference manuscript` 1912-1921 (chart 1639-1668).

Route (no pushforward measure needed, all on `volume` of `ℝ × Space`):
* `σ t (τ, y) = (τ + t, y)` preserves volume, so the a.e. identities transfer along shifts.
* From `W(σ_P x) = W x` a.e. and the a.e. representation `W = A e_r + B e_3`, the inner products with
  `eR` and `e3` (orthonormal off the axis) give `A(τ+P, mer y) = A(τ, mer y)` and the same for `B`,
  a.e. in `x`.
* Induction over `ℕ` and `ℤ` gives `F(τ + kP, mer y) = F(τ, mer y)` a.e. for each `k : ℤ`
  (countable intersection over `k`, `ae_all_iff`).
* Put `A'(τ, p) = A(τ - P ⌊τ/P⌋, p)`: measurable, everywhere `P`-periodic, and equal to `A` a.e.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

theorem gl_profPeriodic : UnforcedLeray.Short.IIb.GLProfPeriodic := by
  intro P W A B hP hA hB hrep hper
  -- shift `(τ, y) ↦ (τ + t, y)` preserves volume
  have hσ : ∀ t : ℝ, MeasurePreserving (fun x : ℝ × UnforcedLeray.Space =>
      (x.1 + t, x.2)) volume volume := by
    intro t
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume t).prod (MeasurePreserving.id volume)
  have hae : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume, x.2 ∉ UnforcedLeray.Axi.axis := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae UnforcedLeray.Axi.ae_not_mem_axis
  -- one-period step for both profiles
  have hstep : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
      A (x.1 + P, UnforcedLeray.Axi.mer x.2) = A (x.1, UnforcedLeray.Axi.mer x.2) ∧
      B (x.1 + P, UnforcedLeray.Axi.mer x.2) = B (x.1, UnforcedLeray.Axi.mer x.2) := by
    have h1 : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
        W (x.1 + P, x.2) = A (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3 :=
      (hσ P).quasiMeasurePreserving.ae hrep
    filter_upwards [h1, hper, hrep, hae] with x h1x hperx hrepx hx2
    have key : A (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3 =
        A (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3 := by
      rw [← h1x, hperx, hrepx]
    have h0e3 : inner ℝ UnforcedLeray.Axi.e3 (UnforcedLeray.Axi.eR x.2) = 0 := by
      rw [real_inner_comm]
      exact UnforcedLeray.Axi.inner_eR_e3 x.2
    have h0eR : inner ℝ (UnforcedLeray.Axi.eR x.2) UnforcedLeray.Axi.e3 = 0 :=
      UnforcedLeray.Axi.inner_eR_e3 x.2
    have hA2 : inner ℝ (A (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3) (UnforcedLeray.Axi.eR x.2) =
        inner ℝ (A (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3) (UnforcedLeray.Axi.eR x.2) := by
      rw [key]
    have hB2 : inner ℝ (A (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1 + P, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3) UnforcedLeray.Axi.e3 =
        inner ℝ (A (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.eR x.2 +
          B (x.1, UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3) UnforcedLeray.Axi.e3 := by
      rw [key]
    have heR : inner ℝ (UnforcedLeray.Axi.eR x.2) (UnforcedLeray.Axi.eR x.2) = 1 := by
      rw [real_inner_self_eq_norm_sq, UnforcedLeray.Axi.norm_eR hx2]
      norm_num
    have he3 : inner ℝ UnforcedLeray.Axi.e3 UnforcedLeray.Axi.e3 = 1 := by
      rw [UnforcedLeray.Axi.inner_e3_left, UnforcedLeray.Axi.e3_apply]
      simp
    simp only [inner_add_left, real_inner_smul_left, heR, he3, h0e3, h0eR, mul_one, mul_zero,
      add_zero] at hA2 hB2
    constructor <;> linarith
  -- general integer-shift lemma for a function of `(τ, mer y)`
  have gen : ∀ F : ℝ × (ℝ × ℝ) → ℝ,
      (∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
        F (x.1 + P, UnforcedLeray.Axi.mer x.2) = F (x.1, UnforcedLeray.Axi.mer x.2)) →
      ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume, ∀ k : ℤ,
        F (x.1 + (k:ℝ) * P, UnforcedLeray.Axi.mer x.2) = F (x.1, UnforcedLeray.Axi.mer x.2) := by
    intro F hF
    have hnat : ∀ n : ℕ, ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
        F (x.1 + (n:ℝ) * P, UnforcedLeray.Axi.mer x.2) = F (x.1, UnforcedLeray.Axi.mer x.2) := by
      intro n
      induction n with
      | zero => filter_upwards with x; simp
      | succ n ih =>
        have h1 : ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
            F (x.1 + (n:ℝ) * P + P, UnforcedLeray.Axi.mer x.2) =
              F (x.1 + (n:ℝ) * P, UnforcedLeray.Axi.mer x.2) :=
          (hσ ((n:ℝ) * P)).quasiMeasurePreserving.ae hF
        filter_upwards [h1, ih] with x h1x ihx
        have e : x.1 + ((n + 1 : ℕ) : ℝ) * P = x.1 + (n:ℝ) * P + P := by push_cast; ring
        rw [e, h1x, ihx]
    have hint : ∀ k : ℤ, ∀ᵐ x : ℝ × UnforcedLeray.Space ∂volume,
        F (x.1 + (k:ℝ) * P, UnforcedLeray.Axi.mer x.2) = F (x.1, UnforcedLeray.Axi.mer x.2) := by
      intro k
      rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
      · have := hnat n
        push_cast
        exact this
      · have h := (hσ (-(n:ℝ) * P)).quasiMeasurePreserving.ae (hnat n)
        filter_upwards [h] with x hx
        have e : x.1 + -(n:ℝ) * P + (n:ℝ) * P = x.1 := by ring
        rw [e] at hx
        push_cast
        exact hx.symm
    exact ae_all_iff.2 hint
  have hallA := gen A (hstep.mono fun x hx => hx.1)
  have hallB := gen B (hstep.mono fun x hx => hx.2)
  -- the reduced profiles
  have hred : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      (p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ), p.2)) :=
    ((measurable_fst.sub (measurable_const.mul ((measurable_of_countable
      (fun k : ℤ => (k:ℝ))).comp (Int.measurable_floor.comp (measurable_fst.div_const P)))))).prodMk
      measurable_snd
  refine ⟨fun p => A (p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ), p.2),
    fun p => B (p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ), p.2), ?_, ?_, ?_, ?_, ?_⟩
  · exact hA.comp hred
  · exact hB.comp hred
  · intro p
    show A (p.1 + P - P * ((⌊(p.1 + P) / P⌋ : ℤ) : ℝ), p.2) =
      A (p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ), p.2)
    have h : (p.1 + P) / P = p.1 / P + 1 := by rw [add_div, div_self hP.ne']
    have e : p.1 + P - P * ((⌊p.1 / P⌋ + 1 : ℤ) : ℝ) = p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ) := by
      push_cast; ring
    rw [h, Int.floor_add_one, e]
  · intro p
    show B (p.1 + P - P * ((⌊(p.1 + P) / P⌋ : ℤ) : ℝ), p.2) =
      B (p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ), p.2)
    have h : (p.1 + P) / P = p.1 / P + 1 := by rw [add_div, div_self hP.ne']
    have e : p.1 + P - P * ((⌊p.1 / P⌋ + 1 : ℤ) : ℝ) = p.1 - P * ((⌊p.1 / P⌋ : ℤ) : ℝ) := by
      push_cast; ring
    rw [h, Int.floor_add_one, e]
  · filter_upwards [hrep, hallA, hallB] with x h1 h2A h2B
    have e : x.1 - P * ((⌊x.1 / P⌋ : ℤ) : ℝ) = x.1 + (((-⌊x.1 / P⌋ : ℤ)) : ℝ) * P := by
      push_cast; ring
    show W x = A (x.1 - P * ((⌊x.1 / P⌋ : ℤ) : ℝ), UnforcedLeray.Axi.mer x.2) •
        UnforcedLeray.Axi.eR x.2 +
      B (x.1 - P * ((⌊x.1 / P⌋ : ℤ) : ℝ), UnforcedLeray.Axi.mer x.2) • UnforcedLeray.Axi.e3
    rw [e, h2A (-⌊x.1 / P⌋), h2B (-⌊x.1 / P⌋)]
    exact h1

#print axioms gl_profPeriodic
