import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.WeakFromSmooth

/-!
# Part III-a: the local part of the cut adjoint rate (`adjWRateCont`, local leaf)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058.

The pairing `∫_cell adjIntegrand tr (φ r) r ψ uψ` splits as the local part (the velocity and the
Laplacian of `ψ`, supported in the band `|η| ≤ R`) minus the global part `∫ φ(r) uψ·∇E(r)`. This
file proves that the local part is continuous in the age `r ∈ (t, s)`: the integrand is jointly
continuous on the compact set `[ρ-ε, ρ+ε] × C_c ∩ {|η| ≤ R}`, and vanishes outside the band.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Local part of `adjWRateCont`** (SP 3052-3058): the band part
`∫_cell φ(r) (ν Δψ - v(r)·∇ψ)` is continuous on `(t, s)`. -/
theorem adjLocContinuous (m : ℝ) :
    ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
      (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
      ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
        ContinuousOn (fun r => ∫ x in B0579.cell c, φ r x *
          ((ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ))
          (Ioo t s) := by
  intro ν c tr t s g φ hctx ψ hψ
  obtain ⟨_, hc, ht, _, _, _, hj⟩ := hctx
  obtain ⟨R, hR⟩ := hψ.band
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  -- the derivatives of `ψ` vanish outside the band
  have hpdz : ∀ j : Fin 2, ∀ x : ℝ × ℝ, R < |x.2| → B0579.pd j ψ x = 0 := by
    intro j x hx
    show fderiv ℝ ψ x (B0579.dir j) = 0
    exact mpVanishFderiv hR (B0579.dir j) x hx
  have hlapz : ∀ x : ℝ × ℝ, R < |x.2| → lapP ψ x = 0 := by
    intro x hx
    unfold lapP
    have h1 : B0579.pd 0 (B0579.pd 0 ψ) x = 0 := by
      show fderiv ℝ (B0579.pd 0 ψ) x (B0579.dir 0) = 0
      exact mpVanishFderiv (fun y hy => hpdz 0 y hy) (B0579.dir 0) x hx
    have h2 : B0579.pd 1 (B0579.pd 1 ψ) x = 0 := by
      show fderiv ℝ (B0579.pd 1 ψ) x (B0579.dir 1) = 0
      exact mpVanishFderiv (fun y hy => hpdz 1 y hy) (B0579.dir 1) x hx
    rw [h1, h2, add_zero]
  -- the joint continuity of the data
  have hjc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ) :=
    hj.continuousOn
  have hvS : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) (Ici 0 ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hcoord : ∀ j : Fin 2, Continuous fun v : EuclideanSpace ℝ (Fin 2) => v j := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous
  have hAc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) =>
      ν * lapP ψ p.2 - (tr.v p.1 p.2 0 * B0579.pd 0 ψ p.2 + tr.v p.1 p.2 1 * B0579.pd 1 ψ p.2))
      (Ici 0 ×ˢ univ) := by
    have hlapC : Continuous (lapP ψ) := by
      unfold lapP
      exact ((hψ.pd 0).pd 0).continuous.add ((hψ.pd 1).pd 1).continuous
    have hv0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 0) (Ici 0 ×ˢ univ) :=
      (hcoord 0).comp_continuousOn hvS
    have hv1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2 1) (Ici 0 ×ˢ univ) :=
      (hcoord 1).comp_continuousOn hvS
    have hd0 : Continuous (B0579.pd 0 ψ) := (hψ.pd 0).continuous
    have hd1 : Continuous (B0579.pd 1 ψ) := (hψ.pd 1).continuous
    have hL : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => lapP ψ p.2) (Ici 0 ×ˢ univ) :=
      hlapC.comp_continuousOn continuousOn_snd |>.congr fun _ _ => rfl
    have hD0 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd 0 ψ p.2) (Ici 0 ×ˢ univ) :=
      hd0.comp_continuousOn continuousOn_snd
    have hD1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => B0579.pd 1 ψ p.2) (Ici 0 ×ˢ univ) :=
      hd1.comp_continuousOn continuousOn_snd
    exact (continuousOn_const.mul hL).sub ((hv0.mul hD0).add (hv1.mul hD1))
  -- the compact set and the bounds
  have hcontAt : ∀ ρ ∈ Ioo t s, ContinuousAt (fun r => ∫ x in B0579.cell c, φ r x *
      ((ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ))
      ρ := by
    intro ρ hρ
    have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Ioo_mem_nhds hρ.1 hρ.2)
    have hIcc : ∀ r ∈ Icc (ρ - ε / 2) (ρ + ε / 2), r ∈ Ioo t s := by
      intro r hr
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hr.1, hr.2]
    have hball2 : ∀ r ∈ Metric.ball ρ (ε / 2), r ∈ Icc (ρ - ε / 2) (ρ + ε / 2) := by
      intro r hr
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
      constructor <;> linarith [hr.1, hr.2]
    set Kc : Set (ℝ × (ℝ × ℝ)) := Icc (ρ - ε / 2) (ρ + ε / 2) ×ˢ
      (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) with hKc_def
    have hKc : IsCompact Kc := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hKsub : Kc ⊆ Ico t s ×ˢ univ := by
      intro p hp
      exact ⟨Ioo_subset_Ico_self (hIcc p.1 hp.1), mem_univ _⟩
    have hKsub' : Kc ⊆ Ici 0 ×ˢ univ := by
      intro p hp
      exact ⟨le_trans ht (Ioo_subset_Ico_self (hIcc p.1 hp.1)).1, mem_univ _⟩
    obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn (hjc.mono hKsub)
    obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn (hAc.mono hKsub')
    set Kx : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R with hKx_def
    have hKxc : IsCompact Kx := isCompact_Icc.prod isCompact_Icc
    have hbound_int : Integrable (Kx.indicator fun _ => M1 * M2)
        (volume.restrict (B0579.cell c)) := by
      rw [integrable_indicator_iff hKxc.isClosed.measurableSet]
      apply integrableOn_const <;>
        first
        | exact enorm_ne_top
        | exact ne_top_of_le_ne_top hKxc.measure_lt_top.ne (Measure.restrict_apply_le _ _)
    have hF_meas : ∀ᶠ r in 𝓝 ρ, AEStronglyMeasurable (fun x => φ r x *
        ((ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ))
        (volume.restrict (B0579.cell c)) := by
      refine Filter.eventually_of_mem (Ioo_mem_nhds hρ.1 hρ.2) fun r hr => ?_
      have hr0 : 0 ≤ r := le_trans ht (Ioo_subset_Ico_self hr).1
      have hAr : Continuous fun x : ℝ × ℝ => ν * lapP ψ x -
          (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) :=
        hAc.comp_continuous (continuous_const.prodMk continuous_id)
          (fun x => ⟨hr0, mem_univ _⟩)
      have hφr : Continuous fun x => φ r x :=
        (adjContDiff_slice hj (Ioo_subset_Ico_self hr)).continuous
      exact ((hφr.mul (Complex.continuous_ofReal.comp hAr))).aestronglyMeasurable
    have h_bound : ∀ᶠ r in 𝓝 ρ, ∀ᵐ a ∂(volume.restrict (B0579.cell c)),
        ‖φ r a * ((ν * lapP ψ a - (tr.v r a 0 * B0579.pd 0 ψ a + tr.v r a 1 * B0579.pd 1 ψ a) : ℝ)
          : ℂ)‖ ≤ Kx.indicator (fun _ => M1 * M2) a := by
      refine Filter.eventually_of_mem (Metric.ball_mem_nhds ρ (half_pos hε)) fun r hr => ?_
      refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (Filter.Eventually.of_forall fun a ha => ?_)
      by_cases haK : a ∈ Kx
      · rw [Set.indicator_of_mem haK]
        have hp : ((r, a) : ℝ × (ℝ × ℝ)) ∈ Kc := ⟨hball2 r hr, haK⟩
        have h1 := hM1 (r, a) hp
        have h2 := hM2 (r, a) hp
        simp only at h1 h2
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      · rw [Set.indicator_of_notMem haK]
        have hR' : R < |a.2| := by
          by_contra hcon
          push_neg at hcon
          exact haK ⟨Ico_subset_Icc_self (Set.mem_prod.1 ha).1, abs_le.1 hcon⟩
        simp [hlapz a hR', hpdz 0 a hR', hpdz 1 a hR']
    have h_cont : ∀ᵐ a ∂(volume.restrict (B0579.cell c)),
        ContinuousAt (fun r => φ r a * ((ν * lapP ψ a -
          (tr.v r a 0 * B0579.pd 0 ψ a + tr.v r a 1 * B0579.pd 1 ψ a) : ℝ) : ℂ)) ρ := by
      refine Filter.Eventually.of_forall fun a => ?_
      have h1 : ContinuousAt (fun r : ℝ => φ r a) ρ :=
        (hjc.continuousAt (show Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 ((ρ, a) : ℝ × (ℝ × ℝ)) from
          prod_mem_nhds (Ico_mem_nhds hρ.1 hρ.2) univ_mem)).comp
          (f := fun r : ℝ => ((r, a) : ℝ × (ℝ × ℝ))) (continuous_id.prodMk continuous_const).continuousAt
      have h2 : ContinuousAt (fun r : ℝ => ν * lapP ψ a -
          (tr.v r a 0 * B0579.pd 0 ψ a + tr.v r a 1 * B0579.pd 1 ψ a)) ρ :=
        (hAc.continuousAt (show Ici 0 ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 ((ρ, a) : ℝ × (ℝ × ℝ)) from
          prod_mem_nhds (Ici_mem_nhds hρ0) univ_mem)).comp
          (f := fun r : ℝ => ((r, a) : ℝ × (ℝ × ℝ))) (continuous_id.prodMk continuous_const).continuousAt
      exact h1.mul (Complex.continuous_ofReal.continuousAt.comp h2)
    exact continuousAt_of_dominated hF_meas h_bound hbound_int h_cont
  exact fun ρ hρ => (hcontAt ρ hρ).continuousWithinAt

/-- The band part is integrable on the cell at each age (the continuous band integrand). -/
theorem adjLocIntegrable (m : ℝ) :
    ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
      (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
      ∀ ρ ∈ Ioo t s, ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
        IntegrableOn (fun x => φ ρ x * ((ν * lapP ψ x -
          (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ))
          (B0579.cell c) := by
  intro ν c tr t s g φ hctx ρ hρ ψ hψ
  obtain ⟨_, hc, ht, _, _, _, hj⟩ := hctx
  obtain ⟨R, hR⟩ := hψ.band
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  have hφs : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hpdz : ∀ j : Fin 2, ∀ x : ℝ × ℝ, R < |x.2| → B0579.pd j ψ x = 0 := by
    intro j x hx
    show fderiv ℝ ψ x (B0579.dir j) = 0
    exact mpVanishFderiv hR (B0579.dir j) x hx
  have hlapz : ∀ x : ℝ × ℝ, R < |x.2| → lapP ψ x = 0 := by
    intro x hx
    unfold lapP
    have h1 : B0579.pd 0 (B0579.pd 0 ψ) x = 0 := by
      show fderiv ℝ (B0579.pd 0 ψ) x (B0579.dir 0) = 0
      exact mpVanishFderiv (fun y hy => hpdz 0 y hy) (B0579.dir 0) x hx
    have h2 : B0579.pd 1 (B0579.pd 1 ψ) x = 0 := by
      show fderiv ℝ (B0579.pd 1 ψ) x (B0579.dir 1) = 0
      exact mpVanishFderiv (fun y hy => hpdz 1 y hy) (B0579.dir 1) x hx
    rw [h1, h2, add_zero]
  have hvR : ∀ j : Fin 2, Continuous fun x : ℝ × ℝ => tr.v ρ x j := by
    intro j
    have h : ContDiff ℝ ∞ (fun w : ℝ × ℝ => tr.v ρ w j) :=
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (UnforcedLeray.B0238.contDiff_Vc tr hρ0.le)
    exact h.continuous
  have hGc : Continuous (fun x : ℝ × ℝ => φ ρ x * ((ν * lapP ψ x -
      (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) := by
    have hlapC : Continuous (lapP ψ) := by
      unfold lapP
      exact ((hψ.pd 0).pd 0).continuous.add ((hψ.pd 1).pd 1).continuous
    have hreal : Continuous (fun x : ℝ × ℝ => ν * lapP ψ x -
        (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x)) :=
      (continuous_const.mul hlapC).sub
        (((hvR 0).mul (hψ.pd 0).continuous).add ((hvR 1).mul (hψ.pd 1).continuous))
    exact hφs.continuous.mul (Complex.continuous_ofReal.comp hreal)
  have hGv : UnforcedLeray.Cyl.VanishesOutside R (fun x : ℝ × ℝ => φ ρ x * ((ν * lapP ψ x -
      (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) := by
    intro x hx
    simp [hlapz x hx, hpdz 0 x hx, hpdz 1 x hx]
  rw [hcell]
  exact hGv.integrableOn_cell hGc c

/-- **Reduction of `adjWRateCont`** to its global leaf: the pairing equals the band part minus the
global part `∫ φ(r) uψ·∇E(r)`, and the band part is continuous (`adjLocContinuous`). -/
theorem adjWRateCont_of_glob (m : ℝ)
    (hGlob : ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
      (φ : ℝ → ℝ × ℝ → ℂ), AdjWCtx m ν c tr t s g φ →
      ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ),
        B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
          ContinuousOn (fun r => ∫ x in B0579.cell c, φ r x *
            ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
              uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) (Ioo t s)) :
    AdjWRateCont m := by
  intro ν c tr t s g φ hctx ψ uψ hψ hu
  have hA := hctx.2.2.2.2.2.1
  have hL := adjLocContinuous m ν c tr t s g φ hctx ψ hψ
  have hG := hGlob ν c tr t s g φ hctx ψ uψ hψ hu
  refine (hL.sub hG).congr (fun r hr => ?_)
  have hI := adjLocIntegrable m ν c tr t s g φ hctx r hr ψ hψ
  have hadj := hA.integrable ψ uψ hψ hu r (Ioo_subset_Icc_self hr)
  have hpt : ∀ x : ℝ × ℝ,
      φ r x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
        uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) =
      φ r x * ((ν * lapP ψ x - (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ) -
        adjIntegrand tr (φ r) r ψ uψ x := by
    intro x
    simp only [adjIntegrand]
    push_cast
    ring
  have hGlobEq : ∫ x in B0579.cell c, φ r x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
        uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) =
      (∫ x in B0579.cell c, φ r x * ((ν * lapP ψ x -
        (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) -
        ∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x := by
    rw [← integral_sub hI hadj]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  show (∫ x in B0579.cell c, adjIntegrand tr (φ r) r ψ uψ x) =
    (∫ x in B0579.cell c, φ r x * ((ν * lapP ψ x -
        (tr.v r x 0 * B0579.pd 0 ψ x + tr.v r x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) -
      ∫ x in B0579.cell c, φ r x * ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
        uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)
  linear_combination hGlobEq

end UnforcedLeray.Short.IIIa
