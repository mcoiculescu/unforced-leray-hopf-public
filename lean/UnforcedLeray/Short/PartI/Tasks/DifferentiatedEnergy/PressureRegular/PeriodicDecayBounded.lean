import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# Part I, task `PartI:T08/3/2` (`periodicDecayBounded_proof`): periodic, continuous, decaying
functions are bounded.

Pure analysis. A continuous `c`-periodic `f` on `ℝ²` tending to `0` as `|η| → ∞` is bounded:
`|f| ≤ 1` on `|η| ≥ R` by the decay, the compact box `[0, c] × [-|R|, |R|]` gives a bound on the
rest, and periodicity moves any point into `[0, c] × ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace UnforcedLeray.Short.PartI

theorem periodicDecayBounded_proof : UnforcedLeray.Short.PartI.PeriodicDecayBounded := by
  intro c hc f hcont hper hdec
  have hev : ∀ᶠ z in comap (fun z : ℝ × ℝ => |z.2|) atTop, f z ∈ Metric.ball (0 : ℝ) 1 :=
    hdec.eventually (Metric.ball_mem_nhds 0 one_pos)
  rw [Filter.eventually_comap] at hev
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hev
  have key : ∀ a : ℝ × ℝ, R ≤ |a.2| → |f a| < 1 := fun a ha => by
    have := hR |a.2| ha a rfl
    simpa [Metric.mem_ball, Real.dist_eq] using this
  have hK : IsCompact (Icc (0 : ℝ) c ×ˢ Icc (-|R|) |R|) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 1, fun z => ?_⟩
  have hfz : f (z.1 + ((-⌊z.1 / c⌋ : ℤ) : ℝ) * c, z.2) = f z := hper.add_int_mul _ z
  have h1 : ((⌊z.1 / c⌋ : ℤ) : ℝ) ≤ z.1 / c := Int.floor_le _
  have h1' : ((⌊z.1 / c⌋ : ℤ) : ℝ) * c ≤ z.1 := (le_div_iff₀ hc).1 h1
  have h2 : z.1 / c < ((⌊z.1 / c⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h2' : z.1 < (((⌊z.1 / c⌋ : ℤ) : ℝ) + 1) * c := (div_lt_iff₀ hc).1 h2
  have main : ∀ t : ℝ, 0 ≤ t → t ≤ c → |f (t, z.2)| ≤ max C 1 := by
    intro t ht0 ht1
    by_cases h : R ≤ |z.2|
    · exact le_trans (key (t, z.2) h).le (le_max_right _ _)
    · have h2 : |z.2| ≤ |R| := le_trans (le_of_lt (not_le.1 h)) (le_abs_self R)
      have hmem : (t, z.2) ∈ Icc (0 : ℝ) c ×ˢ Icc (-|R|) |R| :=
        ⟨⟨ht0, ht1⟩, abs_le.1 h2⟩
      have := hC (t, z.2) hmem
      rw [Real.norm_eq_abs] at this
      exact le_trans this (le_max_left _ _)
  rw [← hfz]
  have ha : (0 : ℝ) ≤ z.1 + ((-⌊z.1 / c⌋ : ℤ) : ℝ) * c := by
    push_cast; nlinarith
  have hb : z.1 + ((-⌊z.1 / c⌋ : ℤ) : ℝ) * c ≤ c := by
    push_cast; nlinarith
  exact main _ ha hb

end UnforcedLeray.Short.PartI
