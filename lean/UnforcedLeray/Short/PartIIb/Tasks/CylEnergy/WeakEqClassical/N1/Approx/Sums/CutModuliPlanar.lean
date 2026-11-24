import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.EtaCutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.UnifContBand
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.PdPeriodic

/-!

planar derivatives.

Source: `the November 2 reference manuscript`, lines 2074-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace TdSums

/-- A function vanishing on an open set has vanishing planar partials there. -/
theorem cutZeroPd (O : Set B0579.Plane) (hO : IsOpen O) (j : Fin 2) (f : B0579.Plane → ℝ)
    (hf : ∀ y ∈ O, f y = 0) : ∀ y ∈ O, B0579.pd j f y = 0 := by
  intro y hy
  have hev : f =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hO.mem_nhds hy) (fun z hz => hf z hz)
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

theorem cutModuliPlanar : UnforcedLeray.Short.IIb.TdSums.CutModuliPlanar := by
  intro c t₀ t₁ R φ hc hR hφ ε hε
  obtain ⟨C, -, hEc⟩ := (etaCutProps : EtaCutProps)
  obtain ⟨hEsm, hEx⟩ := hEc R hR
  set O : Set B0579.Plane := {y | 2 * R < |y.2|} with hO_def
  have hOopen : IsOpen O := isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  -- the cut test vanishes on the open set `O`
  have hzero : ∀ r : ℝ, ∀ y ∈ O, cutTest R φ r y = 0 := by
    intro r y hy
    have hy' : 2 * R < |y.2| := hy
    unfold cutTest
    rw [(hEx y).2.2.2.1 hy'.le, zero_mul]
  -- joint smoothness of the cut test and of its planar partials
  have hUjoint : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × B0579.Plane => cutTest R φ z.1 z.2) (Icc t₀ t₁ ×ˢ univ) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℝ × B0579.Plane => etaCut R z.2) (Icc t₀ t₁ ×ˢ univ) :=
      (hEsm.comp contDiff_snd).contDiffOn
    exact h1.mul hφ.smooth
  have hD0 := pdJointSmooth t₀ t₁ (cutTest R φ) 0 hUjoint
  have hD1 := pdJointSmooth t₀ t₁ (cutTest R φ) 1 hUjoint
  have hDD00 := pdJointSmooth t₀ t₁ (fun r => B0579.pd 0 (cutTest R φ r)) 0 hD0
  have hDD11 := pdJointSmooth t₀ t₁ (fun r => B0579.pd 1 (cutTest R φ r)) 1 hD1
  -- continuity on the band
  have hcont0 : ContinuousOn (fun z : ℝ × B0579.Plane => cutTest R φ z.1 z.2)
      (Icc t₀ t₁ ×ˢ univ) := hUjoint.continuousOn
  have hcont1 : ContinuousOn (fun z : ℝ × B0579.Plane => B0579.pd 0 (cutTest R φ z.1) z.2)
      (Icc t₀ t₁ ×ˢ univ) := hD0.continuousOn
  have hcont2 : ContinuousOn (fun z : ℝ × B0579.Plane => B0579.pd 1 (cutTest R φ z.1) z.2)
      (Icc t₀ t₁ ×ˢ univ) := hD1.continuousOn
  have hcont3 : ContinuousOn (fun z : ℝ × B0579.Plane => lapP (cutTest R φ z.1) z.2)
      (Icc t₀ t₁ ×ˢ univ) := hDD00.continuousOn.add hDD11.continuousOn
  -- periodicity in `q`
  have hper0 : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
      cutTest R φ r (x.1 + c, x.2) = cutTest R φ r x := by
    intro r hr x
    unfold cutTest
    rw [(hEx x).2.2.2.2.1 (x.1 + c), hφ.periodic r hr x]
  have hpd : ∀ j : Fin 2, ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
      B0579.pd j (cutTest R φ r) (x.1 + c, x.2) = B0579.pd j (cutTest R φ r) x :=
    fun j r hr x => pdPeriodic c (cutTest R φ r) j (hper0 r hr) x
  have hperL : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
      lapP (cutTest R φ r) (x.1 + c, x.2) = lapP (cutTest R φ r) x := by
    intro r hr x
    unfold lapP
    rw [pdPeriodic c (B0579.pd 0 (cutTest R φ r)) 0 (hpd 0 r hr) x,
      pdPeriodic c (B0579.pd 1 (cutTest R φ r)) 1 (hpd 1 r hr) x]
  have hper1 : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
      B0579.pd 0 (cutTest R φ r) (x.1 + c, x.2) = B0579.pd 0 (cutTest R φ r) x :=
    fun r hr x => hpd 0 r hr x
  have hper2 : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane,
      B0579.pd 1 (cutTest R φ r) (x.1 + c, x.2) = B0579.pd 1 (cutTest R φ r) x :=
    fun r hr x => hpd 1 r hr x
  -- vanishing for `|η| ≥ 3R`
  have hband : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, 3 * R ≤ |x.2| → cutTest R φ r x = 0 := by
    intro r _ x hx
    exact hzero r x (show 2 * R < |x.2| by linarith)
  have hbandD0 : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, 3 * R ≤ |x.2| →
      B0579.pd 0 (cutTest R φ r) x = 0 := by
    intro r _ x hx
    exact cutZeroPd O hOopen 0 (cutTest R φ r) (hzero r) x (show 2 * R < |x.2| by linarith)
  have hbandD1 : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, 3 * R ≤ |x.2| →
      B0579.pd 1 (cutTest R φ r) x = 0 := by
    intro r _ x hx
    exact cutZeroPd O hOopen 1 (cutTest R φ r) (hzero r) x (show 2 * R < |x.2| by linarith)
  have hbandL : ∀ r ∈ Icc t₀ t₁, ∀ x : B0579.Plane, 3 * R ≤ |x.2| →
      lapP (cutTest R φ r) x = 0 := by
    intro r _ x hx
    unfold lapP
    have h0 : ∀ y ∈ O, B0579.pd 0 (cutTest R φ r) y = 0 :=
      cutZeroPd O hOopen 0 (cutTest R φ r) (hzero r)
    have h1 : ∀ y ∈ O, B0579.pd 1 (cutTest R φ r) y = 0 :=
      cutZeroPd O hOopen 1 (cutTest R φ r) (hzero r)
    rw [cutZeroPd O hOopen 0 _ h0 x (show 2 * R < |x.2| by linarith),
      cutZeroPd O hOopen 1 _ h1 x (show 2 * R < |x.2| by linarith), add_zero]
  -- uniform continuity in age for each of the four quantities
  obtain ⟨δ0, hδ0, h0⟩ := unifContBand c t₀ t₁ (3 * R) (Icc t₀ t₁)
    (fun r x => cutTest R φ r x) hc subset_rfl hcont0 hper0 hband ε hε
  obtain ⟨δ1, hδ1, h1⟩ := unifContBand c t₀ t₁ (3 * R) (Icc t₀ t₁)
    (fun r x => B0579.pd 0 (cutTest R φ r) x) hc subset_rfl hcont1 hper1 hbandD0 ε hε
  obtain ⟨δ2, hδ2, h2⟩ := unifContBand c t₀ t₁ (3 * R) (Icc t₀ t₁)
    (fun r x => B0579.pd 1 (cutTest R φ r) x) hc subset_rfl hcont2 hper2 hbandD1 ε hε
  obtain ⟨δ3, hδ3, h3⟩ := unifContBand c t₀ t₁ (3 * R) (Icc t₀ t₁)
    (fun r x => lapP (cutTest R φ r) x) hc subset_rfl hcont3 hperL hbandL ε hε
  refine ⟨min (min δ0 δ1) (min δ2 δ3), lt_min (lt_min hδ0 hδ1) (lt_min hδ2 hδ3),
    fun r hr r' hr' hd x => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact h0 r hr r' hr' (le_trans hd (le_trans (min_le_left _ _) (min_le_left _ _))) x
  · exact h1 r hr r' hr' (le_trans hd (le_trans (min_le_left _ _) (min_le_right _ _))) x
  · exact h2 r hr r' hr' (le_trans hd (le_trans (min_le_right _ _) (min_le_left _ _))) x
  · exact h3 r hr r' hr' (le_trans hd (le_trans (min_le_right _ _) (min_le_right _ _))) x

end TdSums

end UnforcedLeray.Short.IIb
