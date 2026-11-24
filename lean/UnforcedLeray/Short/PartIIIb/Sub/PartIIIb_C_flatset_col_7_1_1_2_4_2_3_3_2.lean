import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_of
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.LerayClassCont
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.JointRepVecC

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The norm of the partial derivative in the last `ℝ²`-variable is bounded by the full
derivative. -/
theorem p0jr_partial_norm_le {f : ℝ × (ℝ × ℝ) → ℂ} (hf : Differentiable ℝ f) (s : ℝ)
    (x : ℝ × ℝ) :
    ‖fderiv ℝ (fun y => f (s, y)) x‖ ≤ ‖fderiv ℝ f (s, x)‖ := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => (s, y)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right s x
  have h2 : HasFDerivAt f (fderiv ℝ f (s, x)) (s, x) := (hf (s, x)).hasFDerivAt
  have h3 : HasFDerivAt (fun y => f (s, y))
      ((fderiv ℝ f (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
    h2.comp x h1
  rw [h3.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_inr, mul_one]

/-- Gaussian decay in `η` for a smooth, `c`-periodic in `q`, band-supported complex function
(the decay of one component of a nice family). -/
theorem p0jr_decay_of_band {c s0 s1 L : ℝ} (hc : 0 < c) (f : ℝ × (ℝ × ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s q η, f (s, (q + c, η)) = f (s, (q, η)))
    (hsupp : ∀ p, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (x : ℝ × ℝ),
      ‖f (s, x)‖ + ‖fderiv ℝ (fun y => f (s, y)) x‖ ≤ C * Real.exp (-1 * x.2 ^ 2) := by
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ × (ℝ × ℝ) → ℝ, Φ = fun p => ‖f p‖ + ‖fderiv ℝ f p‖ :=
    ⟨_, rfl⟩
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hΦc : Continuous Φ := by
    rw [hΦdef]
    exact (hf.continuous.norm).add (hf.continuous_fderiv (by simp)).norm
  obtain ⟨v, hv⟩ : ∃ v : ℝ × (ℝ × ℝ), v = (0, (c, 0)) := ⟨_, rfl⟩
  have hshift : ∀ p, f (p + v) = f p := by
    intro p
    obtain ⟨s, q, η⟩ := p
    have := hper s q η
    subst hv
    simpa using this
  have hfd : ∀ p, fderiv ℝ f (p + v) = fderiv ℝ f p := by
    intro p
    rw [← fderiv_comp_add_right v]
    have hfun : (fun x => f (x + v)) = f := funext hshift
    rw [hfun]
  have hΦper : ∀ s q η, Φ (s, (q + c, η)) = Φ (s, (q, η)) := by
    intro s q η
    have h1 : (s, (q + c, η)) = (s, (q, η)) + v := by
      subst hv; simp
    rw [hΦdef]
    dsimp only
    rw [h1, hshift, hfd]
  have hK : IsCompact (Icc s0 s1 ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hΦc.continuousOn
  have hbox : ∀ s q η, s ∈ Icc s0 s1 → |η| ≤ L → Φ (s, (q, η)) ≤ max C0 0 := by
    intro s q η hs hη
    obtain ⟨y, hy, hyeq⟩ := (Function.Periodic.exists_mem_Ico₀
      (f := fun q => Φ (s, (q, η))) (fun q => hΦper s q η) hc q)
    have hmem : (s, (y, η)) ∈ Icc s0 s1 ×ˢ (Icc (0 : ℝ) c ×ˢ Icc (-L) L) :=
      ⟨hs, ⟨hy.1, hy.2.le⟩, abs_le.mp hη⟩
    have hb := hC0 _ hmem
    have h2 : Φ (s, (y, η)) ≤ C0 :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hb)
    have h3 : Φ (s, (q, η)) = Φ (s, (y, η)) := hyeq
    rw [h3]
    exact h2.trans (le_max_left _ _)
  refine ⟨max C0 0 * Real.exp (L ^ 2), mul_nonneg (le_max_right _ _) (Real.exp_nonneg _),
    fun s x => ?_⟩
  obtain ⟨q, η⟩ := x
  dsimp only
  by_cases hcase : s ∈ Icc s0 s1 ∧ |η| ≤ L
  · have hpart : ‖f (s, (q, η))‖ + ‖fderiv ℝ (fun y => f (s, y)) (q, η)‖ ≤ Φ (s, (q, η)) := by
      rw [hΦdef]
      dsimp only
      exact add_le_add le_rfl (p0jr_partial_norm_le hdiff s (q, η))
    have hΦ0 : Φ (s, (q, η)) ≤ max C0 0 := hbox s q η hcase.1 hcase.2
    have hexp : 1 ≤ Real.exp (L ^ 2) * Real.exp (-1 * η ^ 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [sq_abs η, abs_nonneg η]
    calc ‖f (s, (q, η))‖ + ‖fderiv ℝ (fun y => f (s, y)) (q, η)‖
        ≤ max C0 0 := hpart.trans hΦ0
      _ ≤ max C0 0 * (Real.exp (L ^ 2) * Real.exp (-1 * η ^ 2)) :=
          le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = max C0 0 * Real.exp (L ^ 2) * Real.exp (-1 * η ^ 2) := by ring
  · have hzero : f (s, (q, η)) = 0 ∧ fderiv ℝ (fun y => f (s, y)) (q, η) = 0 := by
      by_cases hs : s ∈ Icc s0 s1
      · have hη : L < |η| := by
          by_contra hle
          exact hcase ⟨hs, not_lt.mp hle⟩
        have hev : ∀ᶠ y : ℝ × ℝ in 𝓝 (q, η), L < |y.2| :=
          (continuous_const.continuousAt).eventually_lt
            (continuous_snd.abs.continuousAt) hη
        have hev2 : (fun y => f (s, y)) =ᶠ[𝓝 (q, η)] fun _ => (0 : ℂ) := by
          filter_upwards [hev] with y hy
          by_contra hne
          exact absurd (hsupp (s, y) hne).2 (not_le.mpr hy)
        refine ⟨?_, ?_⟩
        · by_contra hne
          exact absurd (hsupp (s, (q, η)) hne).2 (not_le.mpr hη)
        · rw [hev2.fderiv_eq]
          simp
      · have hz : ∀ y, f (s, y) = 0 := fun y => by
          by_contra hne
          exact hs (hsupp (s, y) hne).1
        have hfun : (fun y => f (s, y)) = fun _ => (0 : ℂ) := funext hz
        refine ⟨hz _, ?_⟩
        rw [hfun]
        simp
    rw [hzero.1, hzero.2]
    simp only [norm_zero, add_zero, zero_add]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _)) (Real.exp_nonneg _)

/-- **(2) A jointly measurable representative of the projected slices** (source 3427-3440 /
1684-1689). Proof: `IIIa.lerayClassCont` gives the `L²(cell)`-continuity of the projected slices
of the nice family `(s, y) ↦ F(s, y)` (complexified), and `IIIa.jointRepVecC` gives the jointly
measurable representative `J`. Gaussian decay of the slices comes from the band support of `F`
(`p0jr_decay_of_band`). -/
theorem p0JointRep : P0JointRep := by
  intro c hc F hFs hFp hband
  obtain ⟨s0, s1, L, hs0, hb⟩ := hband
  have hcomp : ∀ i : Fin 2, ContDiff ℝ ∞ fun p : ℝ × (ℝ × ℝ) => ((F p i : ℝ) : ℂ) := fun i =>
    Complex.ofRealCLM.contDiff.comp (hFs i)
  have hsupp : ∀ i : Fin 2, ∀ p : ℝ × (ℝ × ℝ), ((F p i : ℝ) : ℂ) ≠ 0 →
      p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    intro i p hp
    apply hb p
    intro h0
    apply hp
    simp [h0]
  have hperi : ∀ i : Fin 2, ∀ s q η,
      ((F (s, (q + c, η)) i : ℝ) : ℂ) = ((F (s, (q, η)) i : ℝ) : ℂ) := fun i s q η => by
    rw [hFp s q η]
  have hnice : UnforcedLeray.Short.IIIa.NiceSlices c (fun p i => ((F p i : ℝ) : ℂ)) := by
    refine ⟨fun i => hcomp i, fun s x i => ?_, ?_⟩
    · obtain ⟨q, η⟩ := x
      exact hperi i s q η
    · intro s₂
      obtain ⟨C0, hC0, hd0⟩ := p0jr_decay_of_band hc (fun p => ((F p 0 : ℝ) : ℂ)) (hcomp 0)
        (fun s q η => hperi 0 s q η) (hsupp 0)
      obtain ⟨C1, hC1, hd1⟩ := p0jr_decay_of_band hc (fun p => ((F p 1 : ℝ) : ℂ)) (hcomp 1)
        (fun s q η => hperi 1 s q η) (hsupp 1)
      refine ⟨C0 + C1, 1, one_pos, fun s x i _ => ?_⟩
      have hE : (0 : ℝ) ≤ Real.exp (-1 * x.2 ^ 2) := Real.exp_nonneg _
      fin_cases i
      · exact (hd0 s x).trans (mul_le_mul_of_nonneg_right (by linarith) hE)
      · exact (hd1 s x).trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  obtain ⟨h1, h2, -⟩ := UnforcedLeray.Short.IIIa.lerayClassCont c hc _ hnice
  obtain ⟨J, hJm, hJ⟩ := UnforcedLeray.Short.IIIa.jointRepVecC c hc
    (fun s => UnforcedLeray.Short.IIIa.P0re c
      (UnforcedLeray.Short.IIIa.uSl (fun p i => ((F p i : ℝ) : ℂ)) s))
    (fun s => UnforcedLeray.Short.IIIa.P0im c
      (UnforcedLeray.Short.IIIa.uSl (fun p i => ((F p i : ℝ) : ℂ)) s)) h1 h2
  refine ⟨J, hJm, fun σ hσ => ?_⟩
  have hcell : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold UnforcedLeray.B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  have hmeas : (volume.restrict (UnforcedLeray.B0579.cell c)) = UnforcedLeray.Cyl.cellμ c := by
    rw [hcell]
    rfl
  have hae := hJ σ hσ
  rw [hmeas] at hae
  filter_upwards [hae] with x hx
  funext i
  exact hx i

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
