import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_2

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.

At the terminal age `t` we have `φ t = ψ` (`BwdSol.terminal`), so the localized quantity is
`ζ_{η₀}(Δψ)² + μ|∇ψ|² + κψ²` with `0 ≤ ζ_{η₀} ≤ 1`.  The first and second partials and `ψ` of a
cylinder test function are bounded on the plane, and they vanish for `|η| > R` together with the
partials that occur.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- A cylinder test function is bounded on the whole plane. -/
theorem lztCylBounded {c : ℝ} {f : B0579.Plane → ℝ} (hc : 0 < c) (hf : B0579.IsCylTest c f) :
    ∃ M : ℝ, ∀ x : B0579.Plane, |f x| ≤ M := by
  obtain ⟨R, hR⟩ := hf.band
  have hK : IsCompact (Icc 0 c ×ˢ Icc (-|R|) |R| : Set B0579.Plane) :=
    isCompact_Icc.prod isCompact_Icc
  have hfK : ContinuousOn f (Icc 0 c ×ˢ Icc (-|R|) |R|) := hf.continuous.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfK
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : R < |x.2|
  · rw [hR x hx, abs_zero]
    exact le_max_right _ _
  · push_neg at hx
    set k : ℤ := ⌊x.1 / c⌋ with hk
    have hfl1 : (k : ℝ) ≤ x.1 / c := Int.floor_le _
    have hfl2 : x.1 / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hA : (k : ℝ) * c ≤ x.1 := (le_div_iff₀ hc).1 hfl1
    have hB : x.1 < ((k : ℝ) + 1) * c := (div_lt_iff₀ hc).1 hfl2
    have hB' : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
    have hy0 : 0 ≤ x.1 - (k : ℝ) * c := by linarith
    have hyc : x.1 - (k : ℝ) * c ≤ c := by linarith
    have hp : Function.Periodic (fun u : ℝ => f (u, x.2)) c :=
      fun u => hf.periodic (u, x.2)
    have hshift : f (x.1 - (k : ℝ) * c, x.2) = f x := by
      have h := hp.sub_int_mul_eq (x := x.1) k
      simpa using h
    have hband : -|R| ≤ x.2 ∧ x.2 ≤ |R| := abs_le.1 (hx.trans (le_abs_self R))
    have hmem : (x.1 - (k : ℝ) * c, x.2) ∈ Icc 0 c ×ˢ Icc (-|R|) |R| :=
      ⟨⟨hy0, hyc⟩, hband⟩
    have hbound := hC (x.1 - (k : ℝ) * c, x.2) hmem
    rw [hshift, Real.norm_eq_abs] at hbound
    exact le_trans hbound (le_max_left _ _)

/-- Squares are bounded by squares of bounds. -/
theorem lztSq (a B : ℝ) (h : |a| ≤ B) : a * a ≤ B * B := by
  rw [← abs_mul_abs_self a]
  exact mul_self_le_mul_self (abs_nonneg a) h

theorem lapZTerminal : UnforcedLeray.Short.IIb.LapZTerminal := by
  intro ν c s t v ψ φ hc hψ hφ mu kap
  -- boundedness of `ψ`, its first and second partials
  obtain ⟨B0, hB0⟩ := lztCylBounded hc hψ
  obtain ⟨B1, hB1⟩ := lztCylBounded hc (hψ.pd 0)
  obtain ⟨B2, hB2⟩ := lztCylBounded hc (hψ.pd 1)
  obtain ⟨B3, hB3⟩ := lztCylBounded hc ((hψ.pd 0).pd 0)
  obtain ⟨B4, hB4⟩ := lztCylBounded hc ((hψ.pd 1).pd 1)
  -- vanishing bands
  obtain ⟨R0, hR0⟩ := B0579.IsCylTest.exists_band_pd hψ 0
  obtain ⟨R1, hR1⟩ := B0579.IsCylTest.exists_band_pd hψ 1
  obtain ⟨R2, hR2⟩ := B0579.IsCylTest.exists_band_pd (hψ.pd 0) 0
  obtain ⟨R3, hR3⟩ := B0579.IsCylTest.exists_band_pd (hψ.pd 1) 1
  -- the terminal value of the family
  have hLZ : ∀ η0 : ℝ, ∀ x : B0579.Plane, lapZ mu kap η0 φ t x =
      cutζ η0 x * (lapP ψ x * lapP ψ x) +
        (mu * (B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x) +
          kap * (ψ x * ψ x)) := by
    intro η0 x
    simp only [lapZ, lapSq, gradSq, hφ.terminal]
  have hcut : ∀ η0 : ℝ, ∀ x : B0579.Plane, 0 ≤ cutζ η0 x ∧ cutζ η0 x ≤ 1 := by
    intro η0 x
    have h0 : 0 ≤ cutBump (x.2 - η0) := cutBump.nonneg' (x.2 - η0)
    have h1 : cutBump (x.2 - η0) ≤ 1 := cutBump.le_one
    have e : cutζ η0 x = cutBump (x.2 - η0) * cutBump (x.2 - η0) := by
      unfold cutζ cutθ; ring
    rw [e]
    exact ⟨mul_nonneg h0 h0, by nlinarith⟩
  have hlap : ∀ x : B0579.Plane, lapP ψ x * lapP ψ x ≤ (|B3| + |B4|) * (|B3| + |B4|) := by
    intro x
    apply lztSq
    unfold lapP
    calc |B0579.pd 0 (B0579.pd 0 ψ) x + B0579.pd 1 (B0579.pd 1 ψ) x|
        ≤ |B0579.pd 0 (B0579.pd 0 ψ) x| + |B0579.pd 1 (B0579.pd 1 ψ) x| := abs_add_le _ _
      _ ≤ |B3| + |B4| :=
          add_le_add ((hB3 x).trans (le_abs_self B3)) ((hB4 x).trans (le_abs_self B4))
  have hgr : ∀ x : B0579.Plane, B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x
      ≤ B1 * B1 + B2 * B2 :=
    fun x => add_le_add (lztSq _ _ (hB1 x)) (lztSq _ _ (hB2 x))
  have hgr0 : ∀ x : B0579.Plane, 0 ≤ B0579.pd 0 ψ x * B0579.pd 0 ψ x +
      B0579.pd 1 ψ x * B0579.pd 1 ψ x :=
    fun x => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hψψ : ∀ x : B0579.Plane, ψ x * ψ x ≤ B0 * B0 := fun x => lztSq _ _ (hB0 x)
  have hBound : ∀ η0 : ℝ, ∀ x : B0579.Plane, lapZ mu kap η0 φ t x ≤
      (|B3| + |B4|) * (|B3| + |B4|) + |mu| * (B1 * B1 + B2 * B2) + |kap| * (B0 * B0) := by
    intro η0 x
    rw [hLZ η0 x]
    obtain ⟨h0, h1⟩ := hcut η0 x
    have hL0 : 0 ≤ lapP ψ x * lapP ψ x := mul_self_nonneg _
    have t1 : cutζ η0 x * (lapP ψ x * lapP ψ x) ≤ (|B3| + |B4|) * (|B3| + |B4|) :=
      le_trans (mul_le_of_le_one_left hL0 h1) (hlap x)
    have t2 : mu * (B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x) ≤
        |mu| * (B1 * B1 + B2 * B2) :=
      calc mu * (B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x)
          ≤ |mu| * (B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x) :=
            mul_le_mul_of_nonneg_right (le_abs_self mu) (hgr0 x)
        _ ≤ |mu| * (B1 * B1 + B2 * B2) := mul_le_mul_of_nonneg_left (hgr x) (abs_nonneg mu)
    have t3 : kap * (ψ x * ψ x) ≤ |kap| * (B0 * B0) :=
      calc kap * (ψ x * ψ x) ≤ |kap| * (ψ x * ψ x) :=
            mul_le_mul_of_nonneg_right (le_abs_self kap) (mul_self_nonneg _)
        _ ≤ |kap| * (B0 * B0) := mul_le_mul_of_nonneg_left (hψψ x) (abs_nonneg kap)
    linarith
  refine ⟨(|B3| + |B4|) * (|B3| + |B4|) + |mu| * (B1 * B1 + B2 * B2) + |kap| * (B0 * B0),
    max (max R0 R1) (max R2 R3), fun η0 x => ⟨hBound η0 x, fun hx => ?_⟩⟩
  have hx0 : R0 < |x.2| := lt_of_le_of_lt (le_trans (le_max_left R0 R1) (le_max_left _ _)) hx
  have hx1 : R1 < |x.2| := lt_of_le_of_lt (le_trans (le_max_right R0 R1) (le_max_left _ _)) hx
  have hx2 : R2 < |x.2| := lt_of_le_of_lt (le_trans (le_max_left R2 R3) (le_max_right _ _)) hx
  have hx3 : R3 < |x.2| := lt_of_le_of_lt (le_trans (le_max_right R2 R3) (le_max_right _ _)) hx
  obtain ⟨hψx, hp0⟩ := hR0 x hx0
  obtain ⟨-, hp1⟩ := hR1 x hx1
  obtain ⟨-, hq00⟩ := hR2 x hx2
  obtain ⟨-, hq11⟩ := hR3 x hx3
  have hLP : lapP ψ x = 0 := by
    unfold lapP
    simp [hq00, hq11]
  rw [hLZ η0 x, hLP, hψx, hp0, hp1]
  simp
