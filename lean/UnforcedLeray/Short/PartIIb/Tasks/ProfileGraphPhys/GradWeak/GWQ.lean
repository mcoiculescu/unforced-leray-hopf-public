import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Pair
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Pt
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Norm
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Box
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.CTPair
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`): the radial weak identity `Q_ε b = Qb`

Source of record: `the November 2 reference manuscript` lines 1912-1921.
Test fields `Φ_j = (y_j/ϱ) Ψ e_i`, `Ψ = ctLift c ε (3/2) φ`, `j = 0, 1, 2` (`Φ_2 = 0`):
`Σ_j -∂_j Φ_j = ctLift (2) (Q_ε^T φ) e_i` (`GWQ.sum_neg_dy_tst`), paired with `N_v b` by `ct_pair` (`a = 2`);
`Σ_j Φ_j · g_j` is `Ψ e_i · N_v(√s Q b)`, paired by `ct_pair` (`a = 3/2`, `√s Q b ∈ H_r` by `GWQ.inHr_sqrtS`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.GWQ

theorem gwQ : UnforcedLeray.Short.IIb.GWQ := by
  intro c ε r b g Qb Eb hc hε hr1 hr3 hb hgY hgp hQp hQm hQe
  have hr0 : 0 < r := by linarith
  have hP : 0 < 2 * ε * c := by positivity
  have hQHr : InHr c r (sqrtS Qb) := inHr_sqrtS hc hε hr1 (hgY 0) (hgY 1) hQp hQm hQe
  have hwY : IsInYr (2 * ε * c) r (NvC ε⁻¹ b) := nvCInYr_proof c ε r b hc hε hr0 hb
  have hbBox := hrBoxIntegrable c r b hc hr1 hb
  have hQBox := hrBoxIntegrable c r (sqrtS Qb) hc hr1 hQHr
  have hax : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), x.2 ∉ Axi.axis := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae Axi.ae_not_mem_axis
  intro i
  have hIntB : ∀ φ, IsCoordTest φ →
      Integrable (fun x : Coord => b x i * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ)) := by
    intro φ hφ
    have hT := coordT_isCoordTest hφ ε
    obtain ⟨a0, Q, ha0, hz⟩ := coord_box hT
    exact integrable_box_mul (fun σ H R L hσ => hbBox σ H R L hσ i) ha0
      hT.smooth.continuous.continuousOn hz
  have hIntQ : ∀ φ, IsCoordTest φ → Integrable (fun x : Coord => Qb x i * (φ x : ℂ)) := by
    intro φ hφ
    obtain ⟨a0, Q, ha0, hz⟩ := coord_box hφ
    have hψ : ContinuousOn (fun x : Coord => x.1 ^ (-(1 / 2 : ℝ)) * φ x)
        (Icc a0 Q ×ˢ (Icc (-Q) Q ×ˢ Icc (-Q) Q)) := by
      refine ContinuousOn.mul ?_ hφ.smooth.continuous.continuousOn
      exact (continuous_fst.continuousOn).rpow_const
        (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha0 hx.1.1)))
    have h := integrable_box_mul (fun σ H R L hσ => hQBox σ H R L hσ i) ha0 hψ
      (fun x hx => hz x (by intro h; apply hx; simp [h]))
    refine h.congr (Eventually.of_forall fun x => ?_)
    by_cases hφx : φ x = 0
    · simp [hφx]
    · have hpos : 0 < x.1 := lt_of_lt_of_le ha0 (hz x hφx).1.1
      have h1 : Real.sqrt x.1 * x.1 ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]; norm_num
      have hc2 : ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
        exact_mod_cast h1
      simp only [sqrtS, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
      linear_combination (Qb x i * (φ x : ℂ)) * hc2
  have hMain : ∀ φ, IsCoordTest φ →
      ∫ x : Coord, Qb x i * (φ x : ℂ) =
        ∫ x : Coord, b x i * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ) := by
    intro φ hφ
    have hT := coordT_isCoordTest hφ ε
    set T := coordTranspose (vQ ε) (dQ ε) φ with hTdef
    have hΦ : ∀ j, IsPhaseTest (2 * ε * c) (tst c ε (3 / 2) φ i j) := tst_isPhaseTest hc hε hφ i
    have hF : ∀ j, IsPhaseTest (2 * ε * c) (-(dy j (tst c ε (3 / 2) φ i j))) :=
      fun j => ((hΦ j).dy j).neg
    have hgp' : ∀ j, pairF (2 * ε * c) (-(dy j (tst c ε (3 / 2) φ i j))) (NvC ε⁻¹ b) =
        pairF (2 * ε * c) (tst c ε (3 / 2) φ i j) (g j) := fun j => hgp j _ (hΦ j)
    have hS1 := pairF_add3 hP hr1 (hF 0) (hF 1) (hF 2) hwY.meas hwY.finite.ne
    have hLHS : pairF (2 * ε * c) (fun x => (-(dy 0 (tst c ε (3 / 2) φ i 0))) x +
        (-(dy 1 (tst c ε (3 / 2) φ i 1))) x + (-(dy 2 (tst c ε (3 / 2) φ i 2))) x) (NvC ε⁻¹ b) =
        ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((2 : ℝ) - 2) : ℝ)) : ℂ) * b x i * (T x : ℂ) := by
      have h1 : pairF (2 * ε * c) (fun x => (-(dy 0 (tst c ε (3 / 2) φ i 0))) x +
          (-(dy 1 (tst c ε (3 / 2) φ i 1))) x + (-(dy 2 (tst c ε (3 / 2) φ i 2))) x) (NvC ε⁻¹ b) =
          pairF (2 * ε * c) (fun x => ((ctLift c ε 2 T x : ℝ) : ℂ) • frameC i x.2)
            (NvC ε⁻¹ b) := by
        unfold pairF
        refine phaseInt_congr_ae ?_
        filter_upwards [hax] with x hx
        have e := sum_neg_dy_tst hc hε hφ i hx
        rw [Fin.sum_univ_three] at e
        simp only [Pi.neg_apply]
        rw [e, frameC_eq, Complex.coe_smul]
      rw [h1]
      exact ct_pair c ε r 2 T b i hc hε hr1 hr3 hT hb
    have hRHS : pairF (2 * ε * c) (tst c ε (3 / 2) φ i 0) (g 0) +
        pairF (2 * ε * c) (tst c ε (3 / 2) φ i 1) (g 1) +
        pairF (2 * ε * c) (tst c ε (3 / 2) φ i 2) (g 2) =
        ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * sqrtS Qb x i * (φ x : ℂ) := by
      have ints : ∀ j, Integrable (fun z => dotL (tst c ε (3 / 2) φ i j z) (g j z))
          (hSlab (2 * ε * c)) := fun j =>
        integrable_pair hP hr1 (hΦ j) (hgY j).meas (hgY j).finite.ne
      unfold pairF
      rw [← phaseInt_add3 (ints 0) (ints 1) (ints 2)]
      have e : (fun x : ℝ × Space => dotL (tst c ε (3 / 2) φ i 0 x) (g 0 x) +
          dotL (tst c ε (3 / 2) φ i 1 x) (g 1 x) + dotL (tst c ε (3 / 2) φ i 2 x) (g 2 x)) =
          fun x => dotL ((((ctLift c ε (3 / 2) φ x : ℝ)) : ℂ) • frameC i x.2)
            ((((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x +
              (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x) := by
        funext x
        have := rhs_pt c ε (3 / 2) φ i g x
        rwa [Fin.sum_univ_three] at this
      rw [e]
      have h2 : phaseInt (2 * ε * c) (fun x : ℝ × Space =>
          dotL ((((ctLift c ε (3 / 2) φ x : ℝ)) : ℂ) • frameC i x.2)
            ((((x.2 0 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 0 x +
              (((x.2 1 / Real.sqrt (x.2 0 ^ 2 + x.2 1 ^ 2) : ℝ) : ℂ)) • g 1 x)) =
          pairF (2 * ε * c) (fun x => ((ctLift c ε (3 / 2) φ x : ℝ) : ℂ) • frameC i x.2)
            (NvC ε⁻¹ (sqrtS Qb)) := by
        unfold pairF
        refine phaseInt_congr_ae ?_
        filter_upwards [hQe] with x hx
        rw [hx]
      rw [h2]
      exact ct_pair c ε r (3 / 2) φ (sqrtS Qb) i hc hε hr1 hr3 hφ hQHr
    have hkey : ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((2 : ℝ) - 2) : ℝ)) : ℂ) * b x i * (T x : ℂ) =
        ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) *
          ∫ x : Coord, (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * sqrtS Qb x i * (φ x : ℂ) := by
      rw [← hLHS, ← hRHS, hS1, hgp' 0, hgp' 1, hgp' 2]
    have hk : ((Real.pi * ε⁻¹ ^ 2 / c : ℝ) : ℂ) ≠ 0 := by
      have : (Real.pi * ε⁻¹ ^ 2 / c : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hkey' := mul_left_cancel₀ hk hkey
    have eL : ∫ x : Coord, Qb x i * (φ x : ℂ) =
        ∫ x : Coord, (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * sqrtS Qb x i * (φ x : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hφx : φ x = 0
      · simp [hφx]
      · obtain ⟨a0, Q, ha0, hz⟩ := coord_box hφ
        have hpos : 0 < x.1 := lt_of_lt_of_le ha0 (hz x hφx).1.1
        have h1 : x.1 ^ ((3 / 2 : ℝ) - 2) * Real.sqrt x.1 = 1 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]; norm_num
        have hc2 : (((x.1 ^ ((3 / 2 : ℝ) - 2) : ℝ)) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = 1 := by
          exact_mod_cast h1
        simp only [sqrtS, PiLp.smul_apply, smul_eq_mul]
        linear_combination (-(Qb x i * (φ x : ℂ))) * hc2
    have eR' : ∫ x : Coord, (((x.1 ^ ((2 : ℝ) - 2) : ℝ)) : ℂ) * b x i * (T x : ℂ) =
        ∫ x : Coord, b x i * (T x : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp
    rw [eL, ← hkey', eR']
  exact ⟨fun φ hφ => ⟨hIntB φ hφ, hIntQ φ hφ⟩, fun φ hφ => hMain φ hφ⟩

#print axioms gwQ
