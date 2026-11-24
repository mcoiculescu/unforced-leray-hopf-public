import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.CrossPhaseTest
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_2

/-!
# `PhiDriftPair`: the `χₙ Φ` part of the weak drift of the truncated field

Source: `the November 2 reference manuscript` lines 1351-1362, 1470-1480.

For a phase test `Θ` and `c = χₙ`, `driftT (cΘ) = c driftT Θ + ½ (y·∇c) Θ` (`driftT_mulT_apply`).
Applying the weak drift identity `dom.drift` of `Φ` to the phase test `cΘ` gives
`⟪cΘ, bΦ⟫ = ⟪driftT(cΘ), Φ⟫ = ⟪c driftT Θ, Φ⟫ + ⟪½(y·∇c)Θ, Φ⟫`, and rearranging yields
`⟪driftT Θ, cΦ⟫ = ⟪Θ, c bΦ - ½(y·∇c)Φ⟫`.  All pairings are integrals over the phase measure
`muP P`, and each integrand is integrable since every factor lies in `Y_2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Real scalar on the right of `dotL`. -/
theorem pdp_dotL_real_right (a b : CVec3) (r : ℝ) :
    dotL a (r • b) = (r : ℂ) * dotL a b := by
  simp only [dotL_apply, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Real scalar on the left of `dotL`. -/
theorem pdp_dotL_real_left (a b : CVec3) (r : ℝ) :
    dotL (r • a) b = (r : ℂ) * dotL a b := by
  simp only [dotL_apply, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Additivity of `dotL` in its left argument. -/
theorem pdp_dotL_add_left (a b c : CVec3) : dotL (a + b) c = dotL a c + dotL b c := by
  simp only [dotL_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

/-- Subtractivity of `dotL` in its right argument. -/
theorem pdp_dotL_sub_right (a u v : CVec3) : dotL a (u - v) = dotL a u - dotL a v := by
  simp only [dotL_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The cutoff `χₙ` is bounded (it is continuous with compact support). -/
theorem pdp_cut_bound (n : ℕ) : ∃ C : ℝ, ∀ y : Space, |cutχ n y| ≤ C := by
  have hcpt : HasCompactSupport (cutχ n) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * ((n : ℝ) + 1)))
      fun y hy => cutχ_eq_zero n (by
        simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le)
  obtain ⟨C, hC⟩ := (contDiff_cutχ n).continuous.bounded_above_of_compact_support hcpt
  exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y⟩

theorem phiDriftPair : PhiDriftPair := by
  intro P ν μ hP hP1 hν hμ D hD n bΦ hbΦ hbd Θ hΘ
  obtain ⟨Cc, hCc⟩ := pdp_cut_bound n
  obtain ⟨L, hL⟩ := goodMult_radS_cutχ.bound
  have hcc : Continuous (cutχ n) := (contDiff_cutχ n).continuous
  have hrc : Continuous (fun y : Space => (1 / 2 : ℝ) * radS (cutχ n) y) :=
    goodMult_radS_cutχ.cont n
  -- multiplication by the cutoff and by `½ y·∇χₙ` preserves `Y_2`
  have hcY : ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
      UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • g x) :=
    fun g hg => isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => cutχ n x.2) (M := Cc)
      (hcc.comp continuous_snd).aestronglyMeasurable (fun x => hCc x.2)
      (ae_of_all _ fun x => rfl) hg
  have hrY : ∀ g : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 g →
      UnforcedLeray.Short.IIb.IsInYr P 2
        (fun x : ℝ × Space => ((1 / 2 : ℝ) * radS (cutχ n) x.2) • g x) :=
    fun g hg => isInYr_smul_of_bdd hP
      (a := fun x : ℝ × Space => (1 / 2 : ℝ) * radS (cutχ n) x.2) (M := L)
      (hrc.comp continuous_snd).aestronglyMeasurable (fun x => hL n x.2)
      (ae_of_all _ fun x => rfl) hg
  -- phase test and Y_2 memberships
  have hΘY : UnforcedLeray.Short.IIb.IsInYr P 2 Θ := isInYr_of_phaseTest hP hΘ
  have hDΘ : IsPhaseTest P (driftT Θ) := hΘ.driftT
  have hDΘY : UnforcedLeray.Short.IIb.IsInYr P 2 (driftT Θ) := isInYr_of_phaseTest hP hDΘ
  have hΦY : UnforcedLeray.Short.IIb.IsInYr P 2 D.Φ := hD.dom.mem
  have hcΘ : IsPhaseTest P (fun q : ℝ × Space => cutχ n q.2 • Θ q) :=
    (crossPhaseTest P (cutχ n) (contDiff_cutχ n) Θ hΘ).2
  -- weak drift identity of Φ applied to the phase test cΘ
  have hA := hbd _ hcΘ
  -- product rule for driftT (cΘ)
  have hdec : ∀ p : ℝ × Space, driftT (fun q : ℝ × Space => cutχ n q.2 • Θ q) p =
      cutχ n p.2 • driftT Θ p + ((1 / 2 : ℝ) * radS (cutχ n) p.2) • Θ p :=
    fun p => driftT_mulT_apply (contDiff_cutχ n) hΘ.smooth p
  have hdecInt : ∀ z : ℝ × Space,
      dotL (driftT (fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (D.Φ z) =
        (cutχ n z.2 : ℂ) * dotL (driftT Θ z) (D.Φ z)
          + (((1 / 2 : ℝ) * radS (cutχ n) z.2 : ℝ) : ℂ) * dotL (Θ z) (D.Φ z) := by
    intro z
    rw [hdec z, pdp_dotL_add_left, pdp_dotL_real_left, pdp_dotL_real_left]
  -- integrability of the scalar integrands on the phase measure
  have hAi : Integrable
      (fun z : ℝ × Space => (cutχ n z.2 : ℂ) * dotL (driftT Θ z) (D.Φ z)) (muP P) :=
    (dot_integrable hP hDΘY (hcY _ hΦY)).congr
      (ae_of_all _ fun z => pdp_dotL_real_right _ _ _)
  have hCi : Integrable
      (fun z : ℝ × Space => (((1 / 2 : ℝ) * radS (cutχ n) z.2 : ℝ) : ℂ) * dotL (Θ z) (D.Φ z))
      (muP P) :=
    (dot_integrable hP hΘY (hrY _ hΦY)).congr
      (ae_of_all _ fun z => pdp_dotL_real_right _ _ _)
  have hBi : Integrable
      (fun z : ℝ × Space => (cutχ n z.2 : ℂ) * dotL (Θ z) (bΦ z)) (muP P) :=
    (dot_integrable hP hΘY (hcY _ hbΦ)).congr
      (ae_of_all _ fun z => pdp_dotL_real_right _ _ _)
  have hLi : Integrable
      (fun z : ℝ × Space => dotL (driftT (fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (D.Φ z))
      (muP P) :=
    (hAi.add hCi).congr (ae_of_all _ fun z => (hdecInt z).symm)
  have hBi' : Integrable
      (fun z : ℝ × Space => dotL ((fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (bΦ z)) (muP P) :=
    hBi.congr (ae_of_all _ fun z => (pdp_dotL_real_left _ _ _).symm)
  -- the pairing identity for cΘ, in integral form
  have hA2 := hA
  rw [pair_eq_integral P _ _ hLi, pair_eq_integral P _ _ hBi'] at hA2
  have hA3 : ∫ z, dotL (driftT (fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (D.Φ z) ∂(muP P)
      = ∫ z, dotL ((fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (bΦ z) ∂(muP P) := by
    have h := congrArg (fun w : ℂ => (P : ℝ) • w) hA2
    simpa only [smul_smul, mul_inv_cancel₀ hP.ne', one_smul] using h
  have hsplitA : ∫ z, dotL (driftT (fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (D.Φ z) ∂(muP P)
      = ∫ z, (cutχ n z.2 : ℂ) * dotL (driftT Θ z) (D.Φ z) ∂(muP P)
        + ∫ z, (((1 / 2 : ℝ) * radS (cutχ n) z.2 : ℝ) : ℂ) * dotL (Θ z) (D.Φ z) ∂(muP P) := by
    calc ∫ z, dotL (driftT (fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (D.Φ z) ∂(muP P)
        = ∫ z, ((cutχ n z.2 : ℂ) * dotL (driftT Θ z) (D.Φ z)
            + (((1 / 2 : ℝ) * radS (cutχ n) z.2 : ℝ) : ℂ) * dotL (Θ z) (D.Φ z)) ∂(muP P) :=
          integral_congr_ae (ae_of_all _ hdecInt)
      _ = _ := integral_add hAi hCi
  have hsplitB : ∫ z, dotL ((fun q : ℝ × Space => cutχ n q.2 • Θ q) z) (bΦ z) ∂(muP P)
      = ∫ z, (cutχ n z.2 : ℂ) * dotL (Θ z) (bΦ z) ∂(muP P) :=
    integral_congr_ae (ae_of_all _ fun z => pdp_dotL_real_left (Θ z) (bΦ z) (cutχ n z.2))
  have hkey := hA3
  rw [hsplitA, hsplitB] at hkey
  -- the target pairing, in integral form
  have hIntL : Integrable
      (fun z : ℝ × Space => dotL (driftT Θ z) (cutχ n z.2 • D.Φ z)) (muP P) :=
    dot_integrable hP hDΘY (hcY _ hΦY)
  have hIntR : Integrable
      (fun z : ℝ × Space =>
        dotL (Θ z) (cutχ n z.2 • bΦ z - ((1 / 2 : ℝ) * radS (cutχ n) z.2) • D.Φ z))
      (muP P) :=
    (hBi.sub hCi).congr (ae_of_all _ fun z => by
      simp only [Pi.sub_apply, pdp_dotL_sub_right, pdp_dotL_real_right])
  rw [pair_eq_integral P _ _ hIntL, pair_eq_integral P _ _ hIntR]
  congr 1
  have hL : ∫ z, dotL (driftT Θ z) (cutχ n z.2 • D.Φ z) ∂(muP P)
      = ∫ z, (cutχ n z.2 : ℂ) * dotL (driftT Θ z) (D.Φ z) ∂(muP P) :=
    integral_congr_ae (ae_of_all _ fun z => pdp_dotL_real_right _ _ _)
  have hR : ∫ z, dotL (Θ z) (cutχ n z.2 • bΦ z - ((1 / 2 : ℝ) * radS (cutχ n) z.2) • D.Φ z)
      ∂(muP P)
      = ∫ z, ((cutχ n z.2 : ℂ) * dotL (Θ z) (bΦ z)
          - (((1 / 2 : ℝ) * radS (cutχ n) z.2 : ℝ) : ℂ) * dotL (Θ z) (D.Φ z)) ∂(muP P) :=
    integral_congr_ae (ae_of_all _ fun z => by
      simp only [pdp_dotL_sub_right, pdp_dotL_real_right])
  rw [hL, hR, integral_sub hBi hCi]
  linear_combination hkey

end UnforcedLeray.Short.PartIIIb.Concrete
