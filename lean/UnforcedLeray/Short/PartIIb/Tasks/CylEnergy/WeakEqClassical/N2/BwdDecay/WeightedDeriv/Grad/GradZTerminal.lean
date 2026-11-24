import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.

At the terminal age `t` we have `φ t = ψ` (`BwdSol.terminal`), so the localized Bernstein
quantity is `ζ_{η₀}|∇ψ|² + λψ²` with `0 ≤ ζ_{η₀} ≤ 1`.  The partials and `ψ` of a cylinder test
function are bounded on the plane (periodicity and compactness of the cell), and they vanish for
`|η| > R` together with their first partials.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- A cylinder test function is bounded on the whole plane. -/
theorem gztCylBounded {c : ℝ} {f : B0579.Plane → ℝ} (hc : 0 < c) (hf : B0579.IsCylTest c f) :
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
theorem gztSq (a B : ℝ) (h : |a| ≤ B) : a * a ≤ B * B := by
  rw [← abs_mul_abs_self a]
  exact mul_self_le_mul_self (abs_nonneg a) h

theorem gradZTerminal : UnforcedLeray.Short.IIb.GradZTerminal := by
  intro ν c s t v ψ φ hc hψ hφ lam
  obtain ⟨B0, hB0⟩ := gztCylBounded hc hψ
  obtain ⟨B1, hB1⟩ := gztCylBounded hc (hψ.pd 0)
  obtain ⟨B2, hB2⟩ := gztCylBounded hc (hψ.pd 1)
  obtain ⟨R0, hR0⟩ := B0579.IsCylTest.exists_band_pd hψ 0
  obtain ⟨R1, hR1⟩ := B0579.IsCylTest.exists_band_pd hψ 1
  have hgZ : ∀ η0 : ℝ, ∀ x : B0579.Plane, gradZ lam η0 φ t x =
      cutζ η0 x * (B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x) +
        lam * (ψ x * ψ x) := by
    intro η0 x
    simp only [gradZ, gradSq, hφ.terminal]
  have hcut : ∀ η0 : ℝ, ∀ x : B0579.Plane, 0 ≤ cutζ η0 x ∧ cutζ η0 x ≤ 1 := by
    intro η0 x
    have h0 : 0 ≤ cutBump (x.2 - η0) := cutBump.nonneg' (x.2 - η0)
    have h1 : cutBump (x.2 - η0) ≤ 1 := cutBump.le_one
    have e : cutζ η0 x = cutBump (x.2 - η0) * cutBump (x.2 - η0) := by
      unfold cutζ cutθ; ring
    rw [e]
    exact ⟨mul_nonneg h0 h0, by nlinarith⟩
  have hbd : ∀ η0 : ℝ, ∀ x : B0579.Plane,
      gradZ lam η0 φ t x ≤ (B1 * B1 + B2 * B2) + |lam| * (B0 * B0) := by
    intro η0 x
    rw [hgZ η0 x]
    obtain ⟨h0, h1⟩ := hcut η0 x
    have hP0 : 0 ≤ B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x :=
      add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have hP : B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x ≤
        B1 * B1 + B2 * B2 :=
      add_le_add (gztSq _ _ (hB1 x)) (gztSq _ _ (hB2 x))
    have hT1 : cutζ η0 x * (B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x) ≤
        B0579.pd 0 ψ x * B0579.pd 0 ψ x + B0579.pd 1 ψ x * B0579.pd 1 ψ x :=
      mul_le_of_le_one_left hP0 h1
    have hψψ : ψ x * ψ x ≤ B0 * B0 := gztSq _ _ (hB0 x)
    have hT2 : lam * (ψ x * ψ x) ≤ |lam| * (B0 * B0) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self lam) (mul_self_nonneg _))
        (mul_le_mul_of_nonneg_left hψψ (abs_nonneg lam))
    linarith
  refine ⟨(B1 * B1 + B2 * B2) + |lam| * (B0 * B0), max R0 R1, fun η0 x => ⟨hbd η0 x, fun hx => ?_⟩⟩
  have hx0 : R0 < |x.2| := lt_of_le_of_lt (le_max_left _ _) hx
  have hx1 : R1 < |x.2| := lt_of_le_of_lt (le_max_right _ _) hx
  obtain ⟨hψx, hp0⟩ := hR0 x hx0
  obtain ⟨-, hp1⟩ := hR1 x hx1
  rw [hgZ η0 x, hψx, hp0, hp1]
  simp

end UnforcedLeray.Short.IIb
